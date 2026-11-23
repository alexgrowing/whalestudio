import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.ArchimedeanWeightRotation

open Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def ca (v : InfinitePlace F) (θ : ℝ) : UpperTheory.V.TR.Rinf F := fun u => if u = v then Real.cos θ else 1

def sa (v : InfinitePlace F) (θ : ℝ) : UpperTheory.V.TR.Rinf F := fun u => if u = v then Real.sin θ else 0

omit [NumberField F] [IsTotallyReal F] in
theorem ca_sq (v : InfinitePlace F) (θ : ℝ) (u : InfinitePlace F) : ca v θ u ^ 2 + sa v θ u ^ 2 = 1 := by
  unfold ca sa
  split_ifs <;> simp [Real.cos_sq_add_sin_sq]

def rotv (v : InfinitePlace F) (θ : ℝ) : UpperTheory.V.TR.Kinf F 2 :=
  ⟨!![ca v θ, sa v θ; -sa v θ, ca v θ], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j u
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [ca_sq v θ u]⟩

theorem rotv_zero (v : InfinitePlace F) : rotv v 0 = (1 : UpperTheory.V.TR.Kinf F 2) := by
  ext i j u
  fin_cases i <;> fin_cases j <;> simp [rotv, ca, sa]

def Xv (v : InfinitePlace F) : UpperTheory.V.TR.Lie F 2 :=
  UpperTheory.V.TR.toL (Matrix.single 0 1 (Pi.single v 1)) - UpperTheory.V.TR.toL (Matrix.single 1 0 (Pi.single v 1))

theorem rot_deriv (v : InfinitePlace F) :
    HasDerivAt (fun t : ℝ => UpperTheory.V.TR.toL (Unitary.toUnits (rotv v t)).val) (Xv v) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun u => ?_
  by_cases hu : u = v
  · subst hu
    fin_cases i <;> fin_cases j
    · simpa [Xv, rotv, ca, sa] using Real.hasDerivAt_cos 0
    · simpa [Xv, rotv, ca, sa] using Real.hasDerivAt_sin 0
    · simpa [Xv, rotv, ca, sa] using (Real.hasDerivAt_sin 0).fun_neg
    · simpa [Xv, rotv, ca, sa] using Real.hasDerivAt_cos 0
  · fin_cases i <;> fin_cases j <;> simp [Xv, rotv, ca, sa, hu, hasDerivAt_const]

theorem det_rotv (v : InfinitePlace F) (θ : ℝ) :
    Matrix.GeneralLinearGroup.det (Unitary.toUnits (rotv v θ)) = 1 := by
  refine Units.ext ?_
  ext u
  simp [rotv, Matrix.det_fin_two]
  nlinarith [ca_sq v θ u]

theorem factor (x y a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    (((x * a + y * -b : ℝ) : ℂ) + Complex.I * ((x * b + y * a : ℝ) : ℂ)) *
        Complex.exp (-(Real.pi : ℂ) * (((x * a + y * -b : ℝ) : ℂ) ^ 2 + ((x * b + y * a : ℝ) : ℂ) ^ 2)) =
      ((a : ℂ) + Complex.I * (b : ℂ)) *
        (((x : ℂ) + Complex.I * (y : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))) := by
  have hr : (x * a + y * -b) ^ 2 + (x * b + y * a) ^ 2 = x ^ 2 + y ^ 2 := by
    linear_combination (x ^ 2 + y ^ 2) * h
  have hc : (((x * a + y * -b : ℝ) : ℂ) ^ 2 + ((x * b + y * a : ℝ) : ℂ) ^ 2) = (x : ℂ) ^ 2 + (y : ℂ) ^ 2 := by
    exact_mod_cast hr
  rw [hc]
  push_cast
  linear_combination (-(b : ℂ) * y * Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))) * Complex.I_sq

omit [IsTotallyReal F] in
theorem prod_rot (v : InfinitePlace F) (θ : ℝ) :
    ∏ u, (((ca v θ u : ℝ) : ℂ) + Complex.I * ((sa v θ u : ℝ) : ℂ)) = Complex.exp (θ * Complex.I) := by
  rw [Fintype.prod_eq_single v (fun u hu => by simp [ca, sa, hu])]
  simp [ca, sa, Complex.exp_mul_I]
  ring

theorem phi_rot (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (θ : ℝ) (η : Fin 2 → Ad F) :
    Phi c (η ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ)) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      Complex.exp (θ * Complex.I) * Phi c η := by
  set M := ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ)) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))
  have hI : M.map (UpperTheory.V.TR.pInf F) = ((Unitary.toUnits (rotv v θ) : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
      Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) :=
    congrArg Units.val (UpperTheory.V.TR.pInf_infGL (Unitary.toUnits (rotv v θ)))
  have hF : M.map (pFin F) = 1 := congrArg Units.val (UpperTheory.V.TR.pFin_infGL (Unitary.toUnits (rotv v θ)))
  have eI : ∀ i, UpperTheory.V.TR.pInf F ((η ᵥ* M) i) = ((fun j => UpperTheory.V.TR.pInf F (η j)) ᵥ*
      ((Unitary.toUnits (rotv v θ) : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))) i :=
    fun i => by rw [RingHom.map_vecMul, hI]; rfl
  have eF : ∀ i, pFin F ((η ᵥ* M) i) = pFin F (η i) := fun i => by
    rw [RingHom.map_vecMul, hF, Matrix.vecMul_one]; rfl
  unfold Phi
  rw [eF 0, eF 1, eI 0, eI 1, ← mul_assoc]
  congr 1
  unfold arch
  rw [← prod_rot v θ, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun u _ => ?_
  have h := factor (UpperTheory.V.TR.pInf F (η 0) u) (UpperTheory.V.TR.pInf F (η 1) u) (ca v θ u) (sa v θ u) (ca_sq v θ u)
  simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two, rotv] using h

theorem thetaS_rot (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (θ : ℝ) (h : GA F 2) :
    thetaS (Phi c) (h * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) =
      Complex.exp (θ * Complex.I) * thetaS (Phi c) h := by
  unfold thetaS
  rw [← tsum_mul_left]
  congr 1
  funext ξ
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, phi_rot]

theorem eis_rot (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : InfinitePlace F) (θ : ℝ) (g : GA F 2) :
    Eis ω (Phi c) (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) =
      Complex.exp (θ * Complex.I) * Eis ω (Phi c) g := by
  have hd : absD (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) = absD g := by
    unfold absD
    rw [map_mul, UpperTheory.V.TR.det_infGL, det_rotv, map_one, mul_one]
  have he : ∀ t u, eisInt ω (Phi c) (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v θ))) t u =
      Complex.exp (θ * Complex.I) * eisInt ω (Phi c) g t u := by
    intro t u
    unfold eisInt
    rw [← mul_assoc, thetaS_rot, hd]
    ring
  simp only [Eis, he, integral_const_mul]

end UpperTheory.HilbertEisensteinWeightOne.ArchimedeanWeightRotation

open UpperTheory.HilbertEisensteinWeightOne.ArchimedeanWeightRotation in
theorem UpperTheory.HilbertEisensteinWeightOne.weight_holds : SPois → SInt → SSmooth → SWt := by
  intro _ _ _ F _ _ _ ω c _ hs v
  set φ : UpperTheory.V.TR.Sm F 2 := ⟨Eis ω (Phi c), hs⟩
  have hX : UpperTheory.V.TR.Eop v 0 1 φ - UpperTheory.V.TR.Eop v 1 0 φ = UpperTheory.V.TR.lie F 2 (Xv v) φ := by
    unfold UpperTheory.V.TR.Eop
    rw [← LinearMap.sub_apply, ← map_sub]
    rfl
  rw [hX]
  apply Subtype.ext
  funext g
  have h1 := UpperTheory.V.TR.hasDerivAt_curve φ g (fun t => Unitary.toUnits (rotv v t)) (Xv v)
    (by rw [rotv_zero, map_one]) (rot_deriv v)
  have h2 : HasDerivAt (fun t : ℝ => φ.1 (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v t))))
      (Complex.I * φ.1 g) 0 := by
    have e : (fun t : ℝ => φ.1 (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits (rotv v t)))) =
        fun t : ℝ => Complex.exp (t * Complex.I) * φ.1 g := funext fun t => eis_rot ω c v t g
    rw [e]
    have h3 := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).cexp.mul_const (φ.1 g)
    simpa using h3
  rw [UpperTheory.V.TR.lie_apply, h1.unique h2]
  simp [φ]
