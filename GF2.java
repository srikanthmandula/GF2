import java.io.*;
import java.util.Scanner;

public class GF2 
{
    public static void main(String[] arr)
	{  
	    GF2 gf2=new GF2(); 
	    gf2.inputValues();
   }

public int[] EEA_code(int x, int y)
 { 

       if (y == 0) {
           return new int[]{ 1, 0 };
       } else {
           int quotient1 = x / y;
           int remainder = x % y;
           int[] remainderArray = EEA_code(y, remainder);
           return new int[] { remainderArray[1], remainderArray[0] - quotient1 * remainderArray[1] };
       }
   }

   public Polynmal poly_subtract(Polynmal ax, Polynmal bx) {

       int[] sum_reslt;

       if (ax.coefnts.length > bx.coefnts.length) {
           sum_reslt = ax.coefnts.clone();
           int j = sum_reslt.length - 1;
           for (int i = 0; i < bx.coefnts.length; i++) {
               sum_reslt[j] -= bx.coefnts[i];
               j--;
           }
       } else {
           sum_reslt = bx.coefnts.clone();
           for (int i = 0; i < sum_reslt.length; i++)
               sum_reslt[i] = sum_reslt[i] * -1;

           int j = sum_reslt.length - 1;

           for (int i = ax.coefnts.length - 1; i >= 0; i--) {
               sum_reslt[j] = sum_reslt[j] + ax.coefnts[i];
               j--;
           }
       }
       return PLDA_Code(new Polynmal(sum_reslt), m_x_coeff)[1];
   }

   public Polynmal sub_Ops_Work(Polynmal fx, Polynmal gx) {

       int[] sum_reslt;

       if (fx.coefnts.length > gx.coefnts.length) {
           sum_reslt = fx.coefnts.clone();
           int j = sum_reslt.length - 1;
           for (int i = 0; i < gx.coefnts.length; i++) {
               sum_reslt[j] -= gx.coefnts[i];
               j--;
           }
       } else {
           sum_reslt = gx.coefnts.clone();
           for (int i = 0; i < sum_reslt.length; i++)
               sum_reslt[i] = sum_reslt[i] * -1;
           int j = sum_reslt.length - 1;

           for (int i = fx.coefnts.length - 1; i >= 0; i--) {
               sum_reslt[j] = sum_reslt[j] + fx.coefnts[i];
               j--;
           }
       }
       return new Polynmal(sum_reslt).purgeZero();
   }

   public Polynmal multpl_Wkgs(Polynmal ax, Polynmal bx) {
       if (ax.havingZero() || bx.havingZero()) {
           return new Polynmal(new int[] { 0 });
       }

       else {
           int[] sum_reslt = new int[(ax.coefnts.length + bx.coefnts.length) - 1];
           for (int i = 0; i < ax.coefnts.length; i++)
               for (int j = 0; j < bx.coefnts.length; j++)
                   sum_reslt[i + j] += ax.coefnts[i] * bx.coefnts[j];
           return PLDA_Code(new Polynmal(sum_reslt), m_x_coeff)[1];
       }
   }

   public Polynmal mul_Ops_Final(Polynmal fx, Polynmal gx) {
       if (fx.havingZero() || gx.havingZero()) {
           {
               int[] z = {0};
               return new Polynmal ( z );
           }
       }

       else {
           int[] sum_reslt = new int[(fx.coefnts.length + gx.coefnts.length) - 1];
           for (int i = 0; i < fx.coefnts.length; i++)
               for (int j = 0; j < gx.coefnts.length; j++)
                   sum_reslt[i + j] += fx.coefnts[i] * gx.coefnts[j];
           return new Polynmal(sum_reslt).purgeZero();
       }
   }

   public Polynmal addition(Polynmal fx, Polynmal gx) {
       int[] sum_reslt;

       if (fx.coefnts.length > gx.coefnts.length) {
           sum_reslt = fx.coefnts.clone();
           int j = sum_reslt.length - 1;
           for (int i = 0; i < gx.coefnts.length; i++) {
               sum_reslt[j] += gx.coefnts[i];
               j--;
           }
       } else { 
           sum_reslt = gx.coefnts.clone();
           int j = sum_reslt.length - 1;
           for (int i = 0; i < fx.coefnts.length; i++) {
               sum_reslt[j] += fx.coefnts[i];
               j--;
           }
       }
       return new Polynmal(sum_reslt).purgeZero();
   }

   public Polynmal[] PLDA_Code(Polynmal res, Polynmal mx_coff) {
       res = res.moduarOf(prime);
       mx_coff = mx_coff.moduarOf(prime);
       int[] aquire={0};
       Polynmal qut = new Polynmal(aquire);
       Polynmal plda_result_1 = res;

       while (!plda_result_1.havingZero() && (plda_result_1.coefnts.length - 1 >= mx_coff.coefnts.length - 1)) {

           int temp_Coeff = (((plda_result_1.coefnts[0] * (EEA_code(mx_coff.coefnts[0], prime)[0]) % prime) + prime) % prime);
        
           int temp_deg = (((plda_result_1.coefnts.length - 1) - (mx_coff.coefnts.length - 1)) + 1);
           int[] temp_arr = new int[temp_deg];
           temp_arr[0] = temp_Coeff;
           Polynmal temp = new Polynmal(temp_arr);
           Polynmal mul = mul_Ops_Final(temp, mx_coff);
           plda_result_1 = sub_Ops_Work(plda_result_1, mul);
           qut = addition(qut, temp);
           plda_result_1 = plda_result_1.moduarOf(prime);
           plda_result_1 = plda_result_1.purgeZero();
           qut = qut.moduarOf(prime);
           qut = qut.purgeZero();
       }
       Polynmal[] result_2 = new Polynmal[2];
       result_2[0] =qut;
       result_2[1] = plda_result_1;
       return result_2;
   }

   public Polynmal[] EEA_logic(Polynmal fx, Polynmal gx) {
       Polynmal[] y_arr = new Polynmal[2];
       fx = fx.moduarOf(prime);
       gx = gx.moduarOf(prime);

       if (gx.havingZero()) {
           fx = fx.purgeZero();
           int [] temp=null;
           if (prime == 0) {
        	   temp= new int[]{ 1, 0 };
           } else {
               int qut = fx.coefnts[0] / prime;
               int rem = fx.coefnts[0] % prime;
               int[] remArr = EEA_code(prime, rem);
               temp= new int[] { remArr[1], remArr[0] - qut * remArr[1] };
           }
           int[] qut_1 = { ((((temp[0]) % prime) + prime) % prime) };
           int[] prime = { 0 };
           y_arr[0] = new Polynmal(qut_1);
           y_arr[1] = new Polynmal(prime);
           return y_arr;
       } 
	   
	   else 	   
	   {
           Polynmal[] q_arr = PLDA_Code(fx, gx);
           Polynmal q_arr_0 = q_arr[0];
           Polynmal q_arr_1 = q_arr[1];
           Polynmal[] remain_arr = EEA_logic(gx, q_arr_1);
           Polynmal px_arr =remain_arr[1].moduarOf(prime);
           Polynmal mul_first = multpl_Wkgs(q_arr_0, remain_arr[1]);
           Polynmal sub_first = poly_subtract(remain_arr[0], mul_first);
           Polynmal p_first = sub_first.moduarOf(prime);
           remain_arr[0] = px_arr;
           remain_arr[1] = p_first;
           return (remain_arr);
       }
   }

		private class Polynmal{


	        int[] coefnts;

	        public Polynmal(int[] a)
	        {
	            this.coefnts = new int[a.length];

	            for(int i = 0;i<a.length;i++)
	            {				
	                this.coefnts[i] = a[i]; 
	            }
	        }

	        public String toString()
	        {
	            StringBuilder strbdr=new StringBuilder();
	            for (int i = 0; i < coefnts.length; i++) {
	            	strbdr.append(coefnts[i]+" ");
	            }
	            return strbdr.toString();
	        }

	        public boolean havingZero()
	        {
	            for (int i = 0; i < coefnts.length; i++) {
	                if (coefnts[i] != 0) {
	                    return false;
	                }
	            }
	            return true;
	        }

	        public Polynmal purgeZero()
	        {
				int[] temp_poly=null;
				
	            if (!havingZero()) {
	                int x = 0;
	               
	                    if (coefnts[0] == 0)
	                        x++;
	                    
	                
	                temp_poly = new int[coefnts.length - x];
	                for (int i = 0; i < coefnts.length - x; i++)
	                {
	                	temp_poly[i] = coefnts[i + x];
	                }
	                return new Polynmal(temp_poly);
	            }
				else {
	               int[] temp2_poly = { 0 };
	               return new Polynmal(temp2_poly);
	            }
				
	        }

	        public Polynmal moduarOf(int p)
	        {		
	            int[] temp1 = new int[coefnts.length];
	            for (int i = 0; i < coefnts.length; i++) {
	                temp1[i] = coefnts[i];
	                temp1[i] = (temp1[i] % p + p) % p;
	            }

	            return (new Polynmal(temp1)).purgeZero();
	        }

	    
		}
		
		 public void print_opFile()
		    {
          try {
				File file = new File("output.txt");
				 
					 file.createNewFile();
					 BufferedWriter writerF = new BufferedWriter(new FileWriter("output.txt"));					 
					    try {
			             	 int[] sum_reslt;
			                  if (fx.coefnts.length > gx.coefnts.length) { 
			                      sum_reslt = fx.coefnts.clone();
			                      int j = sum_reslt.length - 1;
			                      int tr=fx.coefnts.length-gx.coefnts.length;
			                      for (int i = tr; i < fx.coefnts.length; i++) {
			                          sum_reslt[i] += gx.coefnts[i-tr];
			                          
			                      }
			                  } else { 
			                      sum_reslt = gx.coefnts.clone();
			                      int j = sum_reslt.length - 1;
								  int tr=gx.coefnts.length-fx.coefnts.length ;
			                      for (int i = tr; i < gx.coefnts.length; i++) {
			                          sum_reslt[i] +=  fx.coefnts[i-tr];
			                          
			                      }
			                  }
							  int cntr1=0;
							 for(int i=0;i<sum_reslt.length;i++)
							 {
							  sum_reslt[i]=sum_reslt[i] % prime;
							  if(sum_reslt[i] !=0)
							  {
								  cntr1++;
							  }
								if(cntr1 !=0)
			                 writerF.write(sum_reslt[i]+" ");
							 }
			                  writerF.newLine();
			    				
								int[] result2;
			    		        if (fx.coefnts.length > gx.coefnts.length) {
			    		            result2 = fx.coefnts.clone();
			    		            int j = result2.length - 1;
									int tr=fx.coefnts.length-gx.coefnts.length;
			    		            for (int i = tr; i < fx.coefnts.length; i++) {
			    		                result2[i] -= gx.coefnts[i-tr];
			    		                if(result2[i]<0) result2[i]=result2[i]+prime;
										if(result2[i]>=prime) result2[i]=result2[i] % prime;
			    		            }
			    		        } else {
			    		            result2 = gx.coefnts.clone();
			    		            for (int i = 0; i < result2.length; i++)
			    		                result2[i] = result2[i] * -1;
			    		            int j = result2.length - 1;
									int tr=gx.coefnts.length-fx.coefnts.length ;
			    		            for (int i =tr;i< gx.coefnts.length;i++) {
			    		                result2[i] = result2[i] + fx.coefnts[i-tr];
			    		                if(result2[i]<0) result2[i]=result2[i]+prime;
										if(result2[i]>=prime) result2[i]=result2[i] % prime;
			    		            }
			    		        }
			    			
							
							  int cntr2=0;
							 for(int i=0;i<result2.length;i++)
							 {
							  result2[i]=result2[i] % prime;
							  if(result2[i] !=0)
							  {
								  cntr2++;
							  }
								if(cntr2 !=0)
			                 writerF.write(result2[i]+" ");
							 }
							
							
			    			writerF.newLine();
			   				if (fx.havingZero() || gx.havingZero()){
			   					writerF.write(new Polynmal(new int[]{0})+"");
			   				    writerF.newLine();
			   				}else {
			   		            int[] result_t = new int[(fx.coefnts.length + gx.coefnts.length) - 1];
			   		            for (int i = 0; i < fx.coefnts.length; i++)
			   		                for (int j = 0; j < gx.coefnts.length; j++)
			   		                	result_t[i + j] += fx.coefnts[i] * gx.coefnts[j];
			   		         writerF.write(PLDA_Code(new Polynmal(result_t), m_x_coeff)[1]+"");
			   		      writerF.newLine();
			   		        }
			   				 if (fx.havingZero() || EEA_logic(gx, m_x_coeff)[0].havingZero())
			   					writerF.write(new Polynmal(new int[]{0})+"");
			   		        else{
			   		            int[] result4 = new int[(fx.coefnts.length + EEA_logic(gx, m_x_coeff)[0].coefnts.length) - 1];
			   		            for (int i = 0; i < fx.coefnts.length; i++)
			   		                for (int j = 0; j < EEA_logic(gx, m_x_coeff)[0].coefnts.length; j++)
			   		                	result4[i + j] += fx.coefnts[i] * EEA_logic(gx, m_x_coeff)[0].coefnts[j];
			   		         writerF.write(PLDA_Code(new Polynmal(result4), m_x_coeff)[1]+"");
			   		        }
			   			} finally {
			   				writerF.close();
			   			
				 }
		          
		  	} 
			
			catch (Exception e)
			{
		  		System.out.println(e);
		  	}
		 }


		int prime;
		int m_x_degree,f_x_degree,g_x_degree;
        int[] f_x_array,g_x_array,m_x_array;
	    Polynmal m_x_coeff,fx,gx;
	    
	    
	    private void inputValues() {
	      
	       try {
	  	   FileReader fileread = new FileReader("input.txt");
	       Scanner scnr=new Scanner(fileread);
	       int line=0;
	       while (scnr.hasNext())
			   {
	    	   if(line==0) 
	    		   prime=scnr.nextInt();
	    	   if(line==1) 
	    		   m_x_degree=scnr.nextInt();
	    	   if(line==2)
			   {
	    		   m_x_array = new int[m_x_degree+1];
	               for(int i = 0;i<m_x_array.length;i++)
	                m_x_array[i] = scnr.nextInt();
	       	    } 
	    	   if(line==3) 
	    		   f_x_degree=scnr.nextInt();
	    	   if(line==4){
	    		   f_x_array = new int[f_x_degree+1];
	               for(int i = 0;i<f_x_array.length;i++)
	               {
	            	   f_x_array[i] = scnr.nextInt();
	               }
	    	    } 
	    	   if(line==5) 
	    		   g_x_degree=scnr.nextInt();
	    	   if(line==6){
	    		   g_x_array = new int[g_x_degree+1];
	               for(int i = 0;i<g_x_array.length;i++)
	               {
	            	   g_x_array[i] = scnr.nextInt();
	               }
	    	    } 
	    	    
	    	    line++;
	       }
	       m_x_coeff = new Polynmal(m_x_array);
           fx = new Polynmal(f_x_array);
           gx = new Polynmal(g_x_array);
	        print_opFile();			
			} 
			
			catch(Exception e)
			{
				
				System.out.println(e);
			}
						
}
}
