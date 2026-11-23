import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.KFinitenessEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def sgn (b : Bool) : ℝ := if b then 1 else -1

def archE (ε : InfinitePlace F → Bool) (x y : UpperTheory.V.TR.Rinf F) : ℂ :=
  ∏ v, (((x v : ℂ) + (sgn (ε v) : ℂ) * Complex.I * (y v : ℂ)) *
    Complex.exp (-(Real.pi : ℂ) * ((x v : ℂ) ^ 2 + (y v : ℂ) ^ 2)))

open Classical in

def PhiE (c : HeightOneSpectrum (𝓞 F) → ℕ) (ε : InfinitePlace F → Bool) (ξ : Fin 2 → Ad F) : ℂ :=
  archE ε (UpperTheory.V.TR.pInf F (ξ 0)) (UpperTheory.V.TR.pInf F (ξ 1)) *
    if ∀ w, Valued.v (pLoc F w (pFin F (ξ 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F (ξ 1)) - 1) ≤ WithZero.exp (-(c w : ℤ)) then 1 else 0

def lam (k : UpperTheory.V.TR.Kinf F 2) : ℂ := ∏ w, ((k.1 0 0 w : ℂ) + Complex.I * (k.1 0 1 w : ℂ))

def eps (k : UpperTheory.V.TR.Kinf F 2) (w : InfinitePlace F) : Bool :=
  decide (0 < k.1 0 0 w * k.1 1 1 w - k.1 0 1 w * k.1 1 0 w)

theorem place (a b c d x y : ℝ) (h1 : a * a + c * c = 1) (h2 : b * b + d * d = 1) (h3 : a * b + c * d = 0)
    (h4 : a * a + b * b = 1) (h5 : c * c + d * d = 1) (h6 : a * c + b * d = 0) :
    (((x * a + y * c : ℝ) : ℂ) + Complex.I * ((x * b + y * d : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (((x * a + y * c : ℝ) : ℂ) ^ 2 + ((x * b + y * d : ℝ) : ℂ) ^ 2)) =
    ((a : ℂ) + Complex.I * (b : ℂ)) * (((x : ℂ) + (sgn (decide (0 < a * d - b * c)) : ℂ) * Complex.I * (y : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2))) := by
  have hsq : (x * a + y * c) ^ 2 + (x * b + y * d) ^ 2 = x ^ 2 + y ^ 2 := by
    linear_combination x ^ 2 * h4 + y ^ 2 * h5 + 2 * x * y * h6
  have hC : (((x * a + y * c : ℝ) : ℂ) ^ 2 + ((x * b + y * d : ℝ) : ℂ) ^ 2) = (x : ℂ) ^ 2 + (y : ℂ) ^ 2 := by
    exact_mod_cast hsq
  rw [hC]
  generalize Complex.exp (-(Real.pi : ℂ) * ((x : ℂ) ^ 2 + (y : ℂ) ^ 2)) = E
  have hs2 : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h4 + h5 - (a * c + b * d) * h6
  have hsg : ((sgn true : ℝ) : ℂ) = 1 := by simp [sgn]
  have hsg' : ((sgn false : ℝ) : ℂ) = -1 := by simp [sgn]
  rcases mul_self_eq_one_iff.mp hs2 with hs | hs
  · have hc : c = -b := by linear_combination (-c) * h4 + a * h6 - b * hs
    have hd : d = a := by linear_combination (-d) * h4 + b * h6 + a * hs
    have hpos : 0 < a * d - b * c := by
      rw [hs]
      norm_num
    rw [decide_eq_true hpos, hsg]
    subst hc hd
    push_cast
    linear_combination (-((b : ℂ) * (y : ℂ) * E)) * Complex.I_sq
  · have hc : c = b := by linear_combination (-c) * h4 + a * h6 - b * hs
    have hd : d = -a := by linear_combination (-d) * h4 + b * h6 + a * hs
    have hneg : ¬ 0 < a * d - b * c := by
      rw [hs]
      norm_num
    rw [decide_eq_false hneg, hsg']
    subst hc hd
    push_cast
    linear_combination ((c : ℂ) * (y : ℂ) * E) * Complex.I_sq

theorem rels (k : UpperTheory.V.TR.Kinf F 2) (w : InfinitePlace F) :
    k.1 0 0 w * k.1 0 0 w + k.1 1 0 w * k.1 1 0 w = 1 ∧ k.1 0 1 w * k.1 0 1 w + k.1 1 1 w * k.1 1 1 w = 1 ∧
    k.1 0 0 w * k.1 0 1 w + k.1 1 0 w * k.1 1 1 w = 0 ∧ k.1 0 0 w * k.1 0 0 w + k.1 0 1 w * k.1 0 1 w = 1 ∧
    k.1 1 0 w * k.1 1 0 w + k.1 1 1 w * k.1 1 1 w = 1 ∧ k.1 0 0 w * k.1 1 0 w + k.1 0 1 w * k.1 1 1 w = 0 := by
  have hA := Unitary.coe_star_mul_self k
  have hB := Unitary.coe_mul_star_self k
  have e : ∀ (M N : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)), M = N → ∀ i j, M i j w = N i j w :=
    fun M N h i j => by rw [h]
  have a1 := e _ _ hA 0 0
  have a2 := e _ _ hA 1 1
  have a3 := e _ _ hA 0 1
  have b1 := e _ _ hB 0 0
  have b2 := e _ _ hB 1 1
  have b3 := e _ _ hB 0 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at a1 a2 a3 b1 b2 b3
  exact ⟨a1, a2, a3, b1, b2, b3⟩

theorem arch_rot (k : UpperTheory.V.TR.Kinf F 2) (X Y : UpperTheory.V.TR.Rinf F) :
    arch (fun w => X w * k.1 0 0 w + Y w * k.1 1 0 w) (fun w => X w * k.1 0 1 w + Y w * k.1 1 1 w) =
      lam k * archE (eps k) X Y := by
  unfold arch archE lam
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rels k w
  exact place (k.1 0 0 w) (k.1 0 1 w) (k.1 1 0 w) (k.1 1 1 w) (X w) (Y w) h1 h2 h3 h4 h5 h6

theorem phi_rot (c : HeightOneSpectrum (𝓞 F) → ℕ) (k : UpperTheory.V.TR.Kinf F 2) (v : Fin 2 → Ad F) :
    Phi c (v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      lam k * PhiE c (eps k) v := by
  have hK : ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map
      (UpperTheory.V.TR.pInf F) = k.1 := by
    have h := congrArg Units.val (UpperTheory.V.TR.pInf_infGL (E := F) (Unitary.toUnits k))
    exact h
  have hKf : ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map
      (pFin F) = 1 := by
    have h := congrArg Units.val (UpperTheory.V.TR.pFin_infGL (E := F) (Unitary.toUnits k))
    exact h
  have ef : ∀ i, pFin F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F))) i) = pFin F (v i) := by
    intro i
    rw [RingHom.map_vecMul, hKf, Matrix.vecMul_one]
    rfl
  have e0 : UpperTheory.V.TR.pInf F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F))) 0) =
      fun w => UpperTheory.V.TR.pInf F (v 0) w * k.1 0 0 w + UpperTheory.V.TR.pInf F (v 1) w * k.1 1 0 w := by
    rw [RingHom.map_vecMul, hK]
    funext w
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have e1 : UpperTheory.V.TR.pInf F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F))) 1) =
      fun w => UpperTheory.V.TR.pInf F (v 0) w * k.1 0 1 w + UpperTheory.V.TR.pInf F (v 1) w * k.1 1 1 w := by
    rw [RingHom.map_vecMul, hK]
    funext w
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  unfold Phi PhiE
  rw [ef 0, ef 1, e0, e1, arch_rot k, mul_assoc]

theorem absD_mul (g h : GA F 2) : absD (g * h) = absD g * absD h := by
  unfold absD
  rw [map_mul, map_mul]
  rfl

theorem absD_nonneg (g : GA F 2) : 0 ≤ absD g := by
  unfold absD
  exact ((IdeleGroup.ideleModule F) (Matrix.GeneralLinearGroup.det g)).2.le

theorem eis_smul (ω : HChar F) (a : ℂ) (Ψ : (Fin 2 → Ad F) → ℂ) (g : GA F 2) :
    Eis ω (fun v => a * Ψ v) g = a * Eis ω Ψ g := by
  unfold Eis
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  try dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  try dsimp only
  unfold eisInt thetaS
  simp only [tsum_mul_left]
  ring

theorem eis_mul_right (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (g K : GA F 2) :
    Eis ω Ψ (g * K) = ((absD K ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
      Eis ω (fun v => Ψ (v ᵥ* (K : Matrix (Fin 2) (Fin 2) (Ad F)))) g := by
  unfold Eis
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  try dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  try dsimp only
  unfold eisInt thetaS
  rw [absD_mul, Real.mul_rpow (absD_nonneg g) (absD_nonneg K)]
  simp only [← mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 2) _) g K, Units.val_mul, ← Matrix.vecMul_vecMul]
  push_cast
  ring

theorem cpt_eq (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (hs : Eis ω (Phi c) ∈ UpperTheory.V.TR.Sm F 2)
    (k : UpperTheory.V.TR.Kinf F 2) (g : GA F 2) :
    (UpperTheory.V.TR.cptRep F 2 k ⟨Eis ω (Phi c), hs⟩).1 g =
      ((((absD (UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2)) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * lam k) *
        Eis ω (PhiE c (eps k)) g := by
  change Eis ω (Phi c) (g * UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k)) = _
  rw [eis_mul_right, show (fun v => Phi c (v ᵥ* ((UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)))) = fun v => lam k * PhiE c (eps k) v from funext (phi_rot c k), eis_smul]
  ring

end UpperTheory.HilbertEisensteinWeightOne.KFinitenessEisenstein

open UpperTheory.HilbertEisensteinWeightOne.KFinitenessEisenstein in
theorem UpperTheory.HilbertEisensteinWeightOne.K_finiteness_holds : SPois → SInt → SSmooth → SKfin := by
  intro _ _ _ F _ _ _ ω c _ hs
  haveI : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun ε : InfinitePlace F → Bool => Eis ω (PhiE c ε))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hle : (Submodule.span ℂ (Set.range fun k => UpperTheory.V.TR.cptRep F 2 k ⟨Eis ω (Phi c), hs⟩)).map
      (UpperTheory.V.TR.Sm F 2).subtype ≤
      Submodule.span ℂ (Set.range fun ε : InfinitePlace F → Bool => Eis ω (PhiE c ε)) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    have e : (UpperTheory.V.TR.Sm F 2).subtype (UpperTheory.V.TR.cptRep F 2 k ⟨Eis ω (Phi c), hs⟩) =
        ((((absD (UpperTheory.V.TR.infGL F 2 (Unitary.toUnits k) : GA F 2)) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * lam k) •
          Eis ω (PhiE c (eps k)) :=
      funext fun g => by rw [Pi.smul_apply, smul_eq_mul]; exact cpt_eq ω c hs k g
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨eps k, rfl⟩)
  haveI := Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).symm
