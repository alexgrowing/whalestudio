import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.CentralCharacterHolds
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.LibFresh
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ChartEisIntDifferentiableAt

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.eisensteinLowWeight

open Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def fac (x y : ℝ) : ℂ :=
  ((x : ℂ) + Complex.I * (y : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))

def facX (x y : ℝ) : ℂ :=
  (1 - 2 * (Real.pi : ℂ) * (x : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ))) *
    Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))

def facY (x y : ℝ) : ℂ :=
  (Complex.I - 2 * (Real.pi : ℂ) * (y : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ))) *
    Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))

theorem hasDerivAt_fac {X Y : ℝ → ℝ} {X' Y' s : ℝ} (hX : HasDerivAt X X' s) (hY : HasDerivAt Y Y' s) :
    HasDerivAt (fun s => fac (X s) (Y s)) (X' * facX (X s) (Y s) + Y' * facY (X s) (Y s)) s := by
  have hXc := hX.ofReal_comp
  have hYc := hY.ofReal_comp
  have h1 := hXc.add (hYc.const_mul Complex.I)
  have h2 := ((hXc.pow 2).add (hYc.pow 2)).const_mul (-(Real.pi : ℂ))
  unfold fac facX facY
  refine (h1.mul h2.cexp).congr_deriv ?_
  simp only [Pi.add_apply, Pi.pow_apply]
  norm_num
  ring

theorem low_identity (x y : ℝ) :
    (x * facX x y + (-y) * facY x y) - Complex.I * (y * facX x y + x * facY x y) =
      (x * facX x (-y) + (-y) * facY x (-y)) + fac x (-y) := by
  unfold fac facX facY
  push_cast
  simp only [neg_sq]
  set E := Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))
  linear_combination (-(x : ℂ) * E + 4 * (Real.pi : ℂ) * (x : ℂ) * (y : ℂ) ^ 2 * E) * Complex.I_sq

def atv (v : InfinitePlace F) (x d : ℝ) : UpperTheory.V.TR.Rinf F := fun w => if w = v then x else d

def kA (v : InfinitePlace F) (s : ℝ) : GL (Fin 2) (UpperTheory.V.TR.Rinf F) where
  val := !![atv v (Real.exp s) 1, 0; 0, atv v (Real.exp (-s)) 1]
  inv := !![atv v (Real.exp (-s)) 1, 0; 0, atv v (Real.exp s) 1]
  val_inv := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j w
    fin_cases i <;> fin_cases j <;> simp [atv] <;> split_ifs <;> simp [← Real.exp_add]
  inv_val := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j w
    fin_cases i <;> fin_cases j <;> simp [atv] <;> split_ifs <;> simp [← Real.exp_add]

def kB (v : InfinitePlace F) (s : ℝ) : GL (Fin 2) (UpperTheory.V.TR.Rinf F) where
  val := !![atv v (Real.cosh s) 1, atv v (Real.sinh s) 0; atv v (Real.sinh s) 0, atv v (Real.cosh s) 1]
  inv := !![atv v (Real.cosh s) 1, -atv v (Real.sinh s) 0; -atv v (Real.sinh s) 0, atv v (Real.cosh s) 1]
  val_inv := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j w
    fin_cases i <;> fin_cases j <;> simp [atv] <;> split_ifs <;> (try simp) <;>
      nlinarith [Real.cosh_sq_sub_sinh_sq s]
  inv_val := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j w
    fin_cases i <;> fin_cases j <;> simp [atv] <;> split_ifs <;> (try simp) <;>
      nlinarith [Real.cosh_sq_sub_sinh_sq s]

def kZ (v : InfinitePlace F) (s : ℝ) : GL (Fin 2) (UpperTheory.V.TR.Rinf F) where
  val := !![atv v (Real.exp s) 1, 0; 0, atv v (Real.exp s) 1]
  inv := !![atv v (Real.exp (-s)) 1, 0; 0, atv v (Real.exp (-s)) 1]
  val_inv := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j w
    fin_cases i <;> fin_cases j <;> simp [atv] <;> split_ifs <;> simp [← Real.exp_add]
  inv_val := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j w
    fin_cases i <;> fin_cases j <;> simp [atv] <;> split_ifs <;> simp [← Real.exp_add]

def eps (v : InfinitePlace F) : GL (Fin 2) (UpperTheory.V.TR.Rinf F) where
  val := !![1, 0; 0, atv v (-1) 1]
  inv := !![1, 0; 0, atv v (-1) 1]
  val_inv := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j w
    fin_cases i <;> fin_cases j <;> simp [atv] <;> split_ifs <;> simp
  inv_val := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j w
    fin_cases i <;> fin_cases j <;> simp [atv] <;> split_ifs <;> simp

def XA (v : InfinitePlace F) : UpperTheory.V.TR.Lie F 2 :=
  UpperTheory.V.TR.toL (Matrix.single 0 0 (Pi.single v 1)) - UpperTheory.V.TR.toL (Matrix.single 1 1 (Pi.single v 1))

def XB (v : InfinitePlace F) : UpperTheory.V.TR.Lie F 2 :=
  UpperTheory.V.TR.toL (Matrix.single 0 1 (Pi.single v 1)) + UpperTheory.V.TR.toL (Matrix.single 1 0 (Pi.single v 1))

def XZ (v : InfinitePlace F) : UpperTheory.V.TR.Lie F 2 :=
  UpperTheory.V.TR.toL (Matrix.single 0 0 (Pi.single v 1)) + UpperTheory.V.TR.toL (Matrix.single 1 1 (Pi.single v 1))

theorem kA_zero (v : InfinitePlace F) : kA v 0 = 1 := by
  refine Units.ext ?_
  ext i j w
  fin_cases i <;> fin_cases j <;> simp [kA, atv]

theorem kB_zero (v : InfinitePlace F) : kB v 0 = 1 := by
  refine Units.ext ?_
  ext i j w
  fin_cases i <;> fin_cases j <;> simp [kB, atv]

theorem kZ_zero (v : InfinitePlace F) : kZ v 0 = 1 := by
  refine Units.ext ?_
  ext i j w
  fin_cases i <;> fin_cases j <;> simp [kZ, atv]

theorem kA_deriv (v : InfinitePlace F) :
    HasDerivAt (fun s : ℝ => UpperTheory.V.TR.toL (kA v s).val) (XA v) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun u => ?_
  by_cases hu : u = v
  · subst hu
    fin_cases i <;> fin_cases j
    · simpa [XA, kA, atv] using Real.hasDerivAt_exp 0
    · simp [XA, kA, atv, hasDerivAt_const]
    · simp [XA, kA, atv, hasDerivAt_const]
    · simpa [XA, kA, atv] using (hasDerivAt_neg (0 : ℝ)).exp
  · fin_cases i <;> fin_cases j <;> simp [XA, kA, atv, hu, hasDerivAt_const]

theorem kB_deriv (v : InfinitePlace F) :
    HasDerivAt (fun s : ℝ => UpperTheory.V.TR.toL (kB v s).val) (XB v) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun u => ?_
  by_cases hu : u = v
  · subst hu
    fin_cases i <;> fin_cases j
    · simpa [XB, kB, atv] using Real.hasDerivAt_cosh 0
    · simpa [XB, kB, atv] using Real.hasDerivAt_sinh 0
    · simpa [XB, kB, atv] using Real.hasDerivAt_sinh 0
    · simpa [XB, kB, atv] using Real.hasDerivAt_cosh 0
  · fin_cases i <;> fin_cases j <;> simp [XB, kB, atv, hu, hasDerivAt_const]

theorem kZ_deriv (v : InfinitePlace F) :
    HasDerivAt (fun s : ℝ => UpperTheory.V.TR.toL (kZ v s).val) (XZ v) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun u => ?_
  by_cases hu : u = v
  · subst hu
    fin_cases i <;> fin_cases j
    · simpa [XZ, kZ, atv] using Real.hasDerivAt_exp 0
    · simp [XZ, kZ, atv, hasDerivAt_const]
    · simp [XZ, kZ, atv, hasDerivAt_const]
    · simpa [XZ, kZ, atv] using Real.hasDerivAt_exp 0
  · fin_cases i <;> fin_cases j <;> simp [XZ, kZ, atv, hu, hasDerivAt_const]

def finInd (c : HeightOneSpectrum (𝓞 F) → ℕ) (a b : Af F) : ℂ :=
  if ∀ w, Valued.v (pLoc F w a) ≤ WithZero.exp (-(c w : ℤ)) ∧ Valued.v (pLoc F w b - 1) ≤ WithZero.exp (-(c w : ℤ))
  then 1 else 0

def pI (η : Fin 2 → Ad F) : Fin 2 → UpperTheory.V.TR.Rinf F := fun j => UpperTheory.V.TR.pInf F (η j)

theorem phi_eq (c : HeightOneSpectrum (𝓞 F) → ℕ) (η : Fin 2 → Ad F) :
    Phi c η = arch (pI η 0) (pI η 1) * finInd c (pFin F (η 0)) (pFin F (η 1)) := rfl

theorem phi_infGL (c : HeightOneSpectrum (𝓞 F) → ℕ) (η : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    Phi c (η ᵥ* ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      arch ((pI η ᵥ* (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) 0)
          ((pI η ᵥ* (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) 1) *
        finInd c (pFin F (η 0)) (pFin F (η 1)) := by
  set M := ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))
  have hI : M.map (UpperTheory.V.TR.pInf F) = (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) :=
    congrArg Units.val (UpperTheory.V.TR.pInf_infGL y)
  have hF : M.map (pFin F) = 1 := congrArg Units.val (UpperTheory.V.TR.pFin_infGL y)
  have eI : ∀ i, UpperTheory.V.TR.pInf F ((η ᵥ* M) i) = (pI η ᵥ* (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) i :=
    fun i => by rw [RingHom.map_vecMul, hI]; rfl
  have eF : ∀ i, pFin F ((η ᵥ* M) i) = pFin F (η i) := fun i => by
    rw [RingHom.map_vecMul, hF, Matrix.vecMul_one]; rfl
  rw [phi_eq, eF 0, eF 1]
  simp only [pI] at eI ⊢
  rw [eI 0, eI 1]

theorem arch_split (v : InfinitePlace F) (x y : UpperTheory.V.TR.Rinf F) :
    arch x y = fac (x v) (y v) * ∏ w ∈ Finset.univ.erase v, fac (x w) (y w) := by
  unfold arch
  exact (Finset.mul_prod_erase Finset.univ (fun w => fac (x w) (y w)) (Finset.mem_univ v)).symm

def rest (v : InfinitePlace F) (p : Fin 2 → UpperTheory.V.TR.Rinf F) : ℂ := ∏ w ∈ Finset.univ.erase v, fac (p 0 w) (p 1 w)

theorem vecMul_apply2 (p : Fin 2 → UpperTheory.V.TR.Rinf F) (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) (i : Fin 2)
    (w : InfinitePlace F) : (p ᵥ* y) i w = p 0 w * y 0 i w + p 1 w * y 1 i w := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem phi_curve (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (η : Fin 2 → Ad F)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F))
    (hy : ∀ w, w ≠ v → ∀ i j, (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j w =
      (1 : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j w) :
    Phi c (η ᵥ* ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      fac ((pI η ᵥ* (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) 0 v)
          ((pI η ᵥ* (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) 1 v) *
        (rest v (pI η) * finInd c (pFin F (η 0)) (pFin F (η 1))) := by
  rw [phi_infGL, arch_split v, mul_assoc]
  congr 2
  unfold rest
  refine Finset.prod_congr rfl fun w hw => ?_
  have hw' := Finset.ne_of_mem_erase hw
  have h : ∀ i, (pI η ᵥ* (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) i w = pI η i w := fun i => by
    rw [vecMul_apply2, hy w hw' 0 i, hy w hw' 1 i]
    fin_cases i <;> simp [Matrix.one_apply]
  rw [h 0, h 1]

def DA (x y : ℝ) : ℂ := (x : ℂ) * facX x y + (-(y : ℂ)) * facY x y

def DB (x y : ℝ) : ℂ := (y : ℂ) * facX x y + (x : ℂ) * facY x y

def DZ (x y : ℝ) : ℂ := (x : ℂ) * facX x (-y) + (-(y : ℂ)) * facY x (-y)

theorem low_identity' (x y : ℝ) : DA x y - Complex.I * DB x y = DZ x y + fac x (-y) := by
  have h := low_identity x y
  unfold DA DB DZ
  push_cast
  linear_combination h

theorem hyA (v : InfinitePlace F) (s : ℝ) : ∀ w, w ≠ v → ∀ i j,
    ((kA v s : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j w =
      (1 : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j w := by
  intro w hw i j
  fin_cases i <;> fin_cases j <;> simp [kA, atv, hw]

theorem hyB (v : InfinitePlace F) (s : ℝ) : ∀ w, w ≠ v → ∀ i j,
    ((kB v s : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j w =
      (1 : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j w := by
  intro w hw i j
  fin_cases i <;> fin_cases j <;> simp [kB, atv, hw]

theorem hyEZ (v : InfinitePlace F) (s : ℝ) : ∀ w, w ≠ v → ∀ i j,
    ((eps v * kZ v s : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j w =
      (1 : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j w := by
  intro w hw i j
  rw [Units.val_mul]
  fin_cases i <;> fin_cases j <;> simp [eps, kZ, atv, hw, Matrix.mul_apply, Fin.sum_univ_two]

theorem hyE (v : InfinitePlace F) : ∀ w, w ≠ v → ∀ i j,
    ((eps v : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j w =
      (1 : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j w := by
  intro w hw i j
  fin_cases i <;> fin_cases j <;> simp [eps, atv, hw]

def Rt (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (η : Fin 2 → Ad F) : ℂ :=
  rest v (pI η) * finInd c (pFin F (η 0)) (pFin F (η 1))

theorem term_A (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (η : Fin 2 → Ad F) :
    HasDerivAt (fun s => Phi c (η ᵥ* ((UpperTheory.V.TR.infGL F 2 (kA v s) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))))
      (DA (pI η 0 v) (pI η 1 v) * Rt c v η) 0 := by
  set x := pI η 0 v
  set y := pI η 1 v
  have e : (fun s => Phi c (η ᵥ* ((UpperTheory.V.TR.infGL F 2 (kA v s) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)))) =
      fun s => fac (x * Real.exp s) (y * Real.exp (-s)) * Rt c v η := by
    funext s
    rw [phi_curve c v η (kA v s) (hyA v s), vecMul_apply2, vecMul_apply2]
    simp [kA, atv, x, y, Rt]
  rw [e]
  have hX : HasDerivAt (fun s => x * Real.exp s) x 0 := by simpa using (Real.hasDerivAt_exp 0).const_mul x
  have hY : HasDerivAt (fun s => y * Real.exp (-s)) (-y) 0 := by
    simpa using ((hasDerivAt_neg (0 : ℝ)).exp).const_mul y
  have h := (hasDerivAt_fac hX hY).mul_const (Rt c v η)
  refine h.congr_deriv ?_
  simp only [Real.exp_zero, mul_one, neg_zero, DA]
  push_cast
  ring

theorem term_B (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (η : Fin 2 → Ad F) :
    HasDerivAt (fun s => Phi c (η ᵥ* ((UpperTheory.V.TR.infGL F 2 (kB v s) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))))
      (DB (pI η 0 v) (pI η 1 v) * Rt c v η) 0 := by
  set x := pI η 0 v
  set y := pI η 1 v
  have e : (fun s => Phi c (η ᵥ* ((UpperTheory.V.TR.infGL F 2 (kB v s) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)))) =
      fun s => fac (x * Real.cosh s + y * Real.sinh s) (x * Real.sinh s + y * Real.cosh s) * Rt c v η := by
    funext s
    rw [phi_curve c v η (kB v s) (hyB v s), vecMul_apply2, vecMul_apply2]
    simp [kB, atv, x, y, Rt]
  rw [e]
  have hX : HasDerivAt (fun s => x * Real.cosh s + y * Real.sinh s) y 0 := by
    refine (((Real.hasDerivAt_cosh 0).const_mul x).add ((Real.hasDerivAt_sinh 0).const_mul y)).congr_deriv ?_
    simp
  have hY : HasDerivAt (fun s => x * Real.sinh s + y * Real.cosh s) x 0 := by
    refine (((Real.hasDerivAt_sinh 0).const_mul x).add ((Real.hasDerivAt_cosh 0).const_mul y)).congr_deriv ?_
    simp
  have h := (hasDerivAt_fac hX hY).mul_const (Rt c v η)
  refine h.congr_deriv ?_
  simp only [Real.cosh_zero, Real.sinh_zero, mul_one, mul_zero, add_zero, zero_add, DB]
  all_goals (push_cast; ring)

theorem term_Z (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (η : Fin 2 → Ad F) :
    HasDerivAt (fun s => Phi c (η ᵥ* ((UpperTheory.V.TR.infGL F 2 (eps v * kZ v s) : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F))))
      (DZ (pI η 0 v) (pI η 1 v) * Rt c v η) 0 := by
  set x := pI η 0 v
  set y := pI η 1 v
  have e : (fun s => Phi c (η ᵥ* ((UpperTheory.V.TR.infGL F 2 (eps v * kZ v s) : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)))) =
      fun s => fac (x * Real.exp s) (-y * Real.exp s) * Rt c v η := by
    funext s
    rw [phi_curve c v η (eps v * kZ v s) (hyEZ v s), vecMul_apply2, vecMul_apply2, Units.val_mul]
    simp [eps, kZ, atv, x, y, Rt, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e]
  have hX : HasDerivAt (fun s => x * Real.exp s) x 0 := by simpa using (Real.hasDerivAt_exp 0).const_mul x
  have hY : HasDerivAt (fun s => -y * Real.exp s) (-y) 0 := by simpa using (Real.hasDerivAt_exp 0).const_mul (-y)
  have h := (hasDerivAt_fac hX hY).mul_const (Rt c v η)
  refine h.congr_deriv ?_
  simp only [Real.exp_zero, mul_one, DZ]
  push_cast
  ring

theorem term_eps (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (η : Fin 2 → Ad F) :
    Phi c (η ᵥ* ((UpperTheory.V.TR.infGL F 2 (eps v) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      fac (pI η 0 v) (-(pI η 1 v)) * Rt c v η := by
  rw [phi_curve c v η (eps v) (hyE v), vecMul_apply2, vecMul_apply2]
  simp [eps, atv, Rt]

theorem term_low (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (η : Fin 2 → Ad F) :
    DA (pI η 0 v) (pI η 1 v) * Rt c v η - Complex.I * (DB (pI η 0 v) (pI η 1 v) * Rt c v η) =
      DZ (pI η 0 v) (pI η 1 v) * Rt c v η +
        Phi c (η ᵥ* ((UpperTheory.V.TR.infGL F 2 (eps v) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) := by
  rw [term_eps]
  linear_combination Rt c v η * low_identity' (pI η 0 v) (pI η 1 v)

theorem norm_infEq (w : InfinitePlace F) (r : ℝ) :
    ‖((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm r : w.Completion)‖ = |r| := by
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.dist_eq r 0
  have h0 : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm 0 : w.Completion) = 0 :=
    map_zero _
  rw [← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right, ← h0]
  exact h

theorem ideleModule_infId (u : (UpperTheory.V.TR.Rinf F)ˣ) :
    (IdeleGroup.ideleModule F (UpperTheory.V.TR.infId F u) : ℝ) = ∏ w, |u.val w| := by
  rw [ideleModule_eq]
  have h1 : ((UpperTheory.V.TR.infId F u : Ideles F) : Ad F).1 = UpperTheory.V.TR.infEq F u.val := by
    show (1 : InfiniteAdeleRing F) - UpperTheory.V.TR.infEq F 1 + UpperTheory.V.TR.infEq F u.val = _
    simp
  have h2 : ((UpperTheory.V.TR.infId F u : Ideles F) : Ad F).2 = 1 := by
    show (1 : Af F) - 0 + 0 = 1
    simp
  rw [h1, h2]
  have h3 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(1 : Af F) v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by simp
  rw [h3, mul_one]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one]
  exact norm_infEq w (u.val w)

theorem absD_mul_infGL (g : GA F 2) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    absD (g * UpperTheory.V.TR.infGL F 2 y) = absD g * ∏ w, |(Matrix.GeneralLinearGroup.det y).val w| := by
  unfold absD
  rw [map_mul, UpperTheory.V.TR.det_infGL, map_mul, Positive.val_mul, ideleModule_infId]

theorem det_kA (v : InfinitePlace F) (s : ℝ) : ∏ w, |(Matrix.GeneralLinearGroup.det (kA v s)).val w| = 1 := by
  refine Finset.prod_eq_one fun w _ => ?_
  simp [kA, Matrix.det_fin_two, atv]
  split_ifs <;> simp [← Real.exp_add]

theorem det_kB (v : InfinitePlace F) (s : ℝ) : ∏ w, |(Matrix.GeneralLinearGroup.det (kB v s)).val w| = 1 := by
  refine Finset.prod_eq_one fun w _ => ?_
  simp [kB, Matrix.det_fin_two, atv]
  split_ifs
  · rw [← sq, ← sq, Real.cosh_sq_sub_sinh_sq, abs_one]
  · simp

theorem det_eps (v : InfinitePlace F) : ∏ w, |(Matrix.GeneralLinearGroup.det (eps v)).val w| = 1 := by
  refine Finset.prod_eq_one fun w _ => ?_
  simp [eps, Matrix.det_fin_two, atv]
  split_ifs <;> simp

theorem det_kZ (v : InfinitePlace F) (s : ℝ) :
    ∏ w, |(Matrix.GeneralLinearGroup.det (kZ v s)).val w| = Real.exp s * Real.exp s := by
  rw [Fintype.prod_eq_single v (fun w hw => by simp [kZ, Matrix.det_fin_two, atv, hw])]
  simp [kZ, Matrix.det_fin_two, atv]

def eu (v : InfinitePlace F) (s : ℝ) : (UpperTheory.V.TR.Rinf F)ˣ where
  val := atv v (Real.exp s) 1
  inv := atv v (Real.exp (-s)) 1
  val_inv := by funext w; simp only [atv, Pi.mul_apply, Pi.one_apply]; split_ifs <;> simp [← Real.exp_add]
  inv_val := by funext w; simp only [atv, Pi.mul_apply, Pi.one_apply]; split_ifs <;> simp [← Real.exp_add]

theorem infGL_kZ (v : InfinitePlace F) (s : ℝ) :
    UpperTheory.V.TR.infGL F 2 (kZ v s) = Matrix.GeneralLinearGroup.scalar (Fin 2) (UpperTheory.V.TR.infId F (eu v s)) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) (Ad F)) i j - UpperTheory.V.TR.sInf F ((1 : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j) +
      UpperTheory.V.TR.sInf F (((kZ v s : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j) =
    Matrix.scalar (Fin 2) (1 - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F (atv v (Real.exp s) 1)) i j
  fin_cases i <;> fin_cases j <;> simp [kZ]

theorem omega_eu (ω : HChar F) (hω : IsOfFinOrder ω) (v : InfinitePlace F) (s : ℝ) :
    ((ω.1 (UpperTheory.V.TR.infId F (eu v s)) : ℂˣ) : ℂ) = 1 := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).1 hω
  have e : eu v s = (eu v (s / n)) ^ n := by
    refine Units.ext (funext fun w => ?_)
    rw [Units.val_pow_eq_pow_val, Pi.pow_apply]
    simp only [eu, atv]
    split_ifs
    · rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    · simp
  have h := congrArg (fun χ : HChar F => χ.1 (UpperTheory.V.TR.infId F (eu v (s / n)))) hpow
  rw [e, map_pow, map_pow]
  have h' : (ω ^ n).1 (UpperTheory.V.TR.infId F (eu v (s / n))) = (ω.1 (UpperTheory.V.TR.infId F (eu v (s / n)))) ^ n := rfl
  rw [← h', h]
  rfl

theorem mul_scalar_comm (h : GA F 2) (z : Ideles F) :
    h * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * h := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  exact ((Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq).symm

theorem lieD_XZ_eq_zero (hP : SPois) (hI : SInt) (hS : SSmooth) {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ}
    (H : Hyp ω c) (hs : Eis ω (Phi c) ∈ UpperTheory.V.TR.Sm F 2) (v : InfinitePlace F) (h : GA F 2) :
    UpperTheory.V.TR.lieD (XZ v) (Eis ω (Phi c)) h = 0 := by
  have h1 := UpperTheory.V.TR.hasDerivAt_curve ⟨Eis ω (Phi c), hs⟩ h (kZ v) (XZ v) (kZ_zero v) (kZ_deriv v)
  have e : (fun t => (⟨Eis ω (Phi c), hs⟩ : UpperTheory.V.TR.Sm F 2).1 (h * UpperTheory.V.TR.infGL F 2 (kZ v t))) =
      fun _ => Eis ω (Phi c) h := by
    funext t
    show Eis ω (Phi c) (h * UpperTheory.V.TR.infGL F 2 (kZ v t)) = Eis ω (Phi c) h
    rw [infGL_kZ, mul_scalar_comm, central_character_holds hP hI hS F ω c H, omega_eu ω H.fin, one_mul]
  rw [e] at h1
  exact h1.unique (hasDerivAt_const 0 _)

theorem eisInt_curve (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (g : GA F 2) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F))
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    eisInt ω Ψ (g * UpperTheory.V.TR.infGL F 2 y) t u =
      thetaS Ψ ((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * g) *
          UpperTheory.V.TR.infGL F 2 y) *
        ((ω.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ) *
        (((absD g * ∏ w, |(Matrix.GeneralLinearGroup.det y).val w|) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
  unfold eisInt
  rw [absD_mul_infGL, ← mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)))]

theorem absD_nonneg' (g : GA F 2) : 0 ≤ absD g := (IdeleGroup.ideleModule F _).2.le

theorem sqrt_exp (a s : ℝ) (ha : 0 ≤ a) :
    (a * (Real.exp s * Real.exp s)) ^ ((1 : ℝ) / 2) = a ^ ((1 : ℝ) / 2) * Real.exp s := by
  rw [Real.mul_rpow ha (by positivity), ← Real.exp_add, ← Real.exp_mul]
  congr 2
  ring

theorem rowA_vecMul_mul (ξ : Fin 2 → F) (M N : GA F 2) :
    rowA ξ ᵥ* ((M * N : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) =
      (rowA ξ ᵥ* (M : Matrix (Fin 2) (Fin 2) (Ad F))) ᵥ* (N : Matrix (Fin 2) (Fin 2) (Ad F)) := by
  rw [Units.val_mul, Matrix.vecMul_vecMul]

theorem pointwise (c : HeightOneSpectrum (𝓞 F) → ℕ) (ω : HChar F) (v : InfinitePlace F) (g : GA F 2)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F)
    (hsum : ∀ h : GA F 2, Summable (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} =>
      Phi c (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F))))) :
    UpperTheory.V.TR.lieD (XA v) (fun g' => eisInt ω (Phi c) g' t u) g -
        Complex.I * UpperTheory.V.TR.lieD (XB v) (fun g' => eisInt ω (Phi c) g' t u) g =
      UpperTheory.V.TR.lieD (XZ v) (fun g' => eisInt ω (Phi c) g' t u) (g * UpperTheory.V.TR.infGL F 2 (eps v)) := by
  set f : GA F 2 → ℂ := fun g' => eisInt ω (Phi c) g' t u with hf
  set A := moduleSection (w0 F) t * (u : Ideles F)
  set M := Matrix.GeneralLinearGroup.scalar (Fin 2) A * g with hM
  set K : ℂ := ((ω.1 A : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ) * ((absD g ^ ((1 : ℝ) / 2) : ℝ) : ℂ) with hK

  obtain ⟨DAf, hDA, sA, hθA⟩ := UpperTheory.HilbertEisensteinWeightOne.SLowLib.thetaS_curve c g A (kA v) (XA v) (kA_zero v) (kA_deriv v)
  simp only [← hM] at hDA hθA
  have dA := UpperTheory.HilbertEisensteinWeightOne.Fresh.hasDerivAt_chart_curve f g (UpperTheory.HilbertEisensteinWeightOne.SLowLib.chart_eisInt_differentiableAt ω c g t u) (kA v) (XA v) (kA_zero v) (kA_deriv v)
  have eA : (fun s => f (g * UpperTheory.V.TR.infGL F 2 (kA v s))) =
      fun s => thetaS (Phi c) (M * UpperTheory.V.TR.infGL F 2 (kA v s)) * K := by
    funext s
    simp only [hf]
    rw [eisInt_curve, det_kA, mul_one, hK]
    ring
  rw [eA] at dA
  have vA := dA.unique (hθA.mul_const K)

  obtain ⟨DBf, hDB, sB, hθB⟩ := UpperTheory.HilbertEisensteinWeightOne.SLowLib.thetaS_curve c g A (kB v) (XB v) (kB_zero v) (kB_deriv v)
  simp only [← hM] at hDB hθB
  have dB := UpperTheory.HilbertEisensteinWeightOne.Fresh.hasDerivAt_chart_curve f g (UpperTheory.HilbertEisensteinWeightOne.SLowLib.chart_eisInt_differentiableAt ω c g t u) (kB v) (XB v) (kB_zero v) (kB_deriv v)
  have eB : (fun s => f (g * UpperTheory.V.TR.infGL F 2 (kB v s))) =
      fun s => thetaS (Phi c) (M * UpperTheory.V.TR.infGL F 2 (kB v s)) * K := by
    funext s
    simp only [hf]
    rw [eisInt_curve, det_kB, mul_one, hK]
    ring
  rw [eB] at dB
  have vB := dB.unique (hθB.mul_const K)

  set M' := M * UpperTheory.V.TR.infGL F 2 (eps v) with hM'
  obtain ⟨DZf, hDZ, sZ, hθZ⟩ := UpperTheory.HilbertEisensteinWeightOne.SLowLib.thetaS_curve c (g * UpperTheory.V.TR.infGL F 2 (eps v)) A (kZ v)
    (XZ v) (kZ_zero v) (kZ_deriv v)
  have hMM : Matrix.GeneralLinearGroup.scalar (Fin 2) A * (g * UpperTheory.V.TR.infGL F 2 (eps v)) = M' := by
    rw [hM', hM, mul_assoc]
  simp only [hMM] at hDZ hθZ
  have dZ := UpperTheory.HilbertEisensteinWeightOne.Fresh.hasDerivAt_chart_curve f (g * UpperTheory.V.TR.infGL F 2 (eps v)) (UpperTheory.HilbertEisensteinWeightOne.SLowLib.chart_eisInt_differentiableAt ω c _ t u) (kZ v) (XZ v) (kZ_zero v)
    (kZ_deriv v)
  have eZ : (fun s => f (g * UpperTheory.V.TR.infGL F 2 (eps v) * UpperTheory.V.TR.infGL F 2 (kZ v s))) =
      fun s => thetaS (Phi c) (M' * UpperTheory.V.TR.infGL F 2 (kZ v s)) * (K * ((Real.exp s : ℝ) : ℂ)) := by
    funext s
    simp only [hf]
    rw [eisInt_curve, det_kZ, absD_mul_infGL, det_eps, mul_one, sqrt_exp _ _ (absD_nonneg' g), hK,
      ← mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) A) g]
    push_cast
    ring
  rw [eZ] at dZ
  have hE : HasDerivAt (fun s : ℝ => K * ((Real.exp s : ℝ) : ℂ)) K 0 := by
    refine ((Real.hasDerivAt_exp 0).ofReal_comp.const_mul K).congr_deriv ?_
    simp
  have vZ := dZ.unique (hθZ.mul hE)
  rw [kZ_zero, map_one, mul_one, Real.exp_zero, Complex.ofReal_one, mul_one] at vZ

  have tA : ∀ ξ, DAf ξ = DA (pI (rowA ξ.1 ᵥ* (M : Matrix (Fin 2) (Fin 2) (Ad F))) 0 v)
      (pI (rowA ξ.1 ᵥ* (M : Matrix (Fin 2) (Fin 2) (Ad F))) 1 v) * Rt c v (rowA ξ.1 ᵥ* (M : Matrix (Fin 2) (Fin 2) (Ad F))) := by
    intro ξ
    have h := hDA ξ
    simp only [rowA_vecMul_mul] at h
    exact h.unique (term_A c v _)
  have tB : ∀ ξ, DBf ξ = DB (pI (rowA ξ.1 ᵥ* (M : Matrix (Fin 2) (Fin 2) (Ad F))) 0 v)
      (pI (rowA ξ.1 ᵥ* (M : Matrix (Fin 2) (Fin 2) (Ad F))) 1 v) * Rt c v (rowA ξ.1 ᵥ* (M : Matrix (Fin 2) (Fin 2) (Ad F))) := by
    intro ξ
    have h := hDB ξ
    simp only [rowA_vecMul_mul] at h
    exact h.unique (term_B c v _)
  have tZ : ∀ ξ, DZf ξ = DZ (pI (rowA ξ.1 ᵥ* (M : Matrix (Fin 2) (Fin 2) (Ad F))) 0 v)
      (pI (rowA ξ.1 ᵥ* (M : Matrix (Fin 2) (Fin 2) (Ad F))) 1 v) * Rt c v (rowA ξ.1 ᵥ* (M : Matrix (Fin 2) (Fin 2) (Ad F))) := by
    intro ξ
    have h := hDZ ξ
    simp only [hM', mul_assoc, ← map_mul, rowA_vecMul_mul] at h
    exact h.unique (term_Z c v _)
  have tE : ∀ ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Phi c (rowA ξ.1 ᵥ* (M' : Matrix (Fin 2) (Fin 2) (Ad F))) =
      Phi c ((rowA ξ.1 ᵥ* (M : Matrix (Fin 2) (Fin 2) (Ad F))) ᵥ*
        ((UpperTheory.V.TR.infGL F 2 (eps v) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) := fun ξ => by
    rw [hM', rowA_vecMul_mul]

  have h1 := sA.hasSum.sub (sB.hasSum.mul_left Complex.I)
  have h2 := sZ.hasSum.add (hsum M').hasSum
  have h3 : (fun ξ => DAf ξ - Complex.I * DBf ξ) =
      fun ξ => DZf ξ + Phi c (rowA ξ.1 ᵥ* (M' : Matrix (Fin 2) (Fin 2) (Ad F))) := by
    funext ξ
    rw [tA, tB, tZ, tE]
    exact term_low c v _
  rw [h3] at h1
  have key := h1.unique h2
  rw [vA, vB, vZ]
  have hθ : thetaS (Phi c) M' = ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Phi c (rowA ξ.1 ᵥ* (M' : Matrix (Fin 2) (Fin 2) (Ad F))) :=
    rfl
  rw [hθ]
  linear_combination K * key

end UpperTheory.HilbertEisensteinWeightOne.eisensteinLowWeight

open UpperTheory.HilbertEisensteinWeightOne.eisensteinLowWeight in
theorem UpperTheory.HilbertEisensteinWeightOne.low_weight_holds : SPois → SInt → SSmooth → SLow := by
  intro hP hI hS F _ _ _ ω c H hs v
  set φ : UpperTheory.V.TR.Sm F 2 := ⟨Eis ω (Phi c), hs⟩
  have hA : UpperTheory.V.TR.Eop v 0 0 φ - UpperTheory.V.TR.Eop v 1 1 φ = UpperTheory.V.TR.lie F 2 (XA v) φ := by
    unfold UpperTheory.V.TR.Eop
    rw [← LinearMap.sub_apply, ← map_sub]
    rfl
  have hB : UpperTheory.V.TR.Eop v 0 1 φ + UpperTheory.V.TR.Eop v 1 0 φ = UpperTheory.V.TR.lie F 2 (XB v) φ := by
    unfold UpperTheory.V.TR.Eop
    rw [← LinearMap.add_apply, ← map_add]
    rfl
  rw [hA, hB]
  apply Subtype.ext
  funext g
  show UpperTheory.V.TR.lieD (XA v) (Eis ω (Phi c)) g = Complex.I * UpperTheory.V.TR.lieD (XB v) (Eis ω (Phi c)) g
  obtain ⟨iA, eA⟩ := UpperTheory.HilbertEisensteinWeightOne.lieD_Eis_eq_integral hP hI H g (XA v)
  obtain ⟨iB, eB⟩ := UpperTheory.HilbertEisensteinWeightOne.lieD_Eis_eq_integral hP hI H g (XB v)
  obtain ⟨-, eZ⟩ := UpperTheory.HilbertEisensteinWeightOne.lieD_Eis_eq_integral hP hI H (g * UpperTheory.V.TR.infGL F 2 (eps v)) (XZ v)
  have hZ0 := lieD_XZ_eq_zero hP hI hS H hs v (g * UpperTheory.V.TR.infGL F 2 (eps v))
  have hsum : ∀ h : GA F 2, Summable (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} =>
      Phi c (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))) := fun h =>
    ((hP F ω c H).choose_spec h).1.of_norm
  have hint := integral_sub iA (iB.const_mul Complex.I)
  rw [integral_const_mul] at hint
  have hpt : (fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      UpperTheory.V.TR.lieD (XA v) (fun g' => eisInt ω (Phi c) g' p.1 p.2) g -
        Complex.I * UpperTheory.V.TR.lieD (XB v) (fun g' => eisInt ω (Phi c) g' p.1 p.2) g) =
      fun p => UpperTheory.V.TR.lieD (XZ v) (fun g' => eisInt ω (Phi c) g' p.1 p.2) (g * UpperTheory.V.TR.infGL F 2 (eps v)) :=
    funext fun p => pointwise c ω v g p.1 p.2 hsum
  rw [hpt, ← eZ, hZ0, ← eA, ← eB] at hint
  linear_combination -hint
