import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeSIsBridge
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DopEqSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PolarConjTranspose
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSmoothLogNearOneOfIsUnitaryLieExpData
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKind
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CommuteGelfandInvariantMatrixUnitsOfGlRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmMulRightOfIsCMExt

noncomputable section

namespace GlobalTheory.HCFinU.Central

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothForms GlobalTheory.Dec
open scoped ContDiff

section Group

variable {n : ℕ} {ε : Fin n → Bool} {G : Type} [Group G]

def toUJ (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) : UJ ε :=
  ⟨⟨g, Jm ε * gᴴ * Jm ε, mul_eq_one_comm.1 (GelfAd.inv_mul_of_UJ hg), GelfAd.inv_mul_of_UJ hg⟩, hg⟩

open Classical in

def sec (ι : UJ ε →* G) (u : Matrix (Fin n) (Fin n) ℂ) : G := if h : inUJ ε u then ι (toUJ u h) else 1

theorem sec_uMat (ι : UJ ε →* G) (h : UJ ε) : sec ι (uMat h) = ι h := by
  have : inUJ ε (uMat h) := h.2
  rw [sec, dif_pos this]
  congr 1
  exact Subtype.ext (Units.ext rfl)

def expU {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) : UJ ε := toUJ _ (exp_indefinite_unitary_holds n ε X hX t)

def line (ι : UJ ε →* G) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : G := sec ι (NormedSpace.exp ((t : ℂ) • X))

theorem line_eq (ι : UJ ε →* G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    line ι X t = ι (expU hX t) := sec_uMat ι (expU hX t)

def der (ι : UJ ε →* G) (X : Matrix (Fin n) (Fin n) ℂ) (ψ : G → ℂ) : G → ℂ :=
  fun g => deriv (fun t => ψ (g * line ι X t)) 0

def derC (ι : UJ ε →* G) (Z : Matrix (Fin n) (Fin n) ℂ) (ψ : G → ℂ) : G → ℂ :=
  der ι (cpart1 ε Z) ψ + Complex.I • der ι (cpart2 ε Z) ψ

def gelfG (ι : UJ ε →* G) (m : ℕ) (ψ : G → ℂ) : G → ℂ :=
  ∑ a : Fin (m + 1) → Fin n,
    (List.ofFn fun i => derC ι (Matrix.single (a i) (a (i + 1)) 1)).foldr (fun T acc => T acc) ψ

theorem Rd_eq (ι : UJ ε →* G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {ψ : G → ℂ} {x : G} (hF : ∀ h : UJ ε, F (uMat h) = ψ (x * ι h)) (h : UJ ε) :
    Rd X F (uMat h) = der ι X ψ (x * ι h) := by
  unfold Rd der
  congr 1
  funext t
  rw [line_eq ι hX, mul_assoc, ← map_mul, ← hF]
  rfl

theorem Eword_eq (ι : UJ ε →* G) {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {ψ : G → ℂ} {x : G}
    (hF : ∀ h : UJ ε, F (uMat h) = ψ (x * ι h)) (w : List (Fin n × Fin n)) : ∀ h : UJ ε,
    Eword ε w F (uMat h) =
      (w.map fun p => derC ι (Matrix.single p.1 p.2 1)).foldr (fun T acc => T acc) ψ (x * ι h) := by
  induction w with
  | nil => exact hF
  | cons p w ih =>
    intro h
    have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    simp only [Eword, Eab, Ec, List.map_cons, List.foldr_cons, derC, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Rd_eq ι hc.1 ih, Rd_eq ι hc.2.1 ih]

theorem gelf_eq (ι : UJ ε →* G) {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {ψ : G → ℂ} {x : G}
    (hF : ∀ h : UJ ε, F (uMat h) = ψ (x * ι h)) (m : ℕ) : gelf ε m F 1 = gelfG ι m ψ x := by
  unfold gelf gelfG
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have := Eword_eq ι hF (cycWord a) 1
  rw [map_one, mul_one] at this
  refine this.trans ?_
  simp only [cycWord, List.map_ofFn, Function.comp_def, finRotate_succ_apply]

theorem der_right (ι : UJ ε →* G) {a : G} {k : UJ ε} (hk : ∀ h, ι h * a = a * ι (k⁻¹ * h * k))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    line ι X t * a = a * line ι (uMat k⁻¹ * X * uMat k) t := by
  rw [line_eq ι hX, hk, ← sec_uMat, line]
  congr 2
  have hu : IsUnit (uMat k) := Units.isUnit _
  have hi : uMat k⁻¹ = (uMat k)⁻¹ := Matrix.coe_units_inv _
  have e : (t : ℂ) • (uMat k⁻¹ * X * uMat k) = (uMat k)⁻¹ * ((t : ℂ) • X) * uMat k := by simp [hi]
  rw [e, Matrix.exp_conj' _ _ hu, ← hi]
  rfl

theorem conj_bar (k : UJ ε) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (uMat k⁻¹ * Z * uMat k)ᴴ * Jm ε = uMat k⁻¹ * (Jm ε * Zᴴ * Jm ε) * uMat k := by
  have hi : uMat k⁻¹ = Jm ε * (uMat k)ᴴ * Jm ε :=
    (Matrix.coe_units_inv _).trans (Matrix.inv_eq_left_inv (GelfAd.inv_mul_of_UJ k.2))
  rw [hi]
  simp only [Matrix.conjTranspose_mul, Jm_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, signature_mul_signature_mul, Jm_mul_self, Matrix.mul_one]

theorem derC_right (ι : UJ ε →* G) {a : G} {k : UJ ε} (hk : ∀ h, ι h * a = a * ι (k⁻¹ * h * k))
    (Z : Matrix (Fin n) (Fin n) ℂ) (ψ : G → ℂ) :
    derC ι Z (fun x => ψ (x * a)) = fun x => derC ι (uMat k⁻¹ * Z * uMat k) ψ (x * a) := by
  have hc := complex_parts_mem_lie_algebra_holds n ε Z
  have e1 : cpart1 ε (uMat k⁻¹ * Z * uMat k) = uMat k⁻¹ * cpart1 ε Z * uMat k := by
    rw [cpart1, cpart1, conj_bar, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
  have e2 : cpart2 ε (uMat k⁻¹ * Z * uMat k) = uMat k⁻¹ * cpart2 ε Z * uMat k := by
    rw [cpart2, cpart2, conj_bar, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
  funext x
  simp only [derC, der, e1, e2, Pi.add_apply, Pi.smul_apply, mul_assoc x, der_right ι hk hc.1,
    der_right ι hk hc.2.1]

variable (ε) in

def lieJ : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | inG ε X}
  zero_mem' := by simp [inG]
  add_mem' := fun {X Y} hX hY => by
    have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
    have h2 : Yᴴ * Jm ε + Jm ε * Y = 0 := hY
    change (X + Y)ᴴ * Jm ε + Jm ε * (X + Y) = 0
    rw [conjTranspose_add, add_mul, mul_add, add_add_add_comm, h1, h2, add_zero]
  smul_mem' := fun c X hX => by
    have h1 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
    change (c • X)ᴴ * Jm ε + Jm ε * (c • X) = 0
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, h1, smul_zero]

variable (ε) in

def barJ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := Jm ε * Xᴴ * Jm ε
  map_add' X Y := by rw [conjTranspose_add, mul_add, add_mul]
  map_smul' c X := by rw [conjTranspose_smul, star_trivial, mul_smul_comm, smul_mul_assoc]; rfl

theorem barJ_apply (X : Matrix (Fin n) (Fin n) ℂ) : barJ ε X = Jm ε * Xᴴ * Jm ε := rfl

theorem inG_iff (X : Matrix (Fin n) (Fin n) ℂ) : inG ε X ↔ barJ ε X = -X := by
  rw [barJ_apply, inG]
  constructor
  · intro h
    rw [mul_assoc, eq_neg_of_add_eq_zero_left h, mul_neg, signature_mul_signature_mul]
  · intro h
    have := congrArg (Jm ε * ·) h
    simp only [mul_assoc, signature_mul_signature_mul] at this
    rw [this, mul_neg, neg_add_cancel]

theorem inUJ_of {u : Matrix (Fin n) (Fin n) ℂ} (h : barJ ε u * u = 1) : inUJ ε u := by
  have := congrArg (Jm ε * ·) h
  simp only [barJ_apply, mul_assoc, signature_mul_signature_mul, mul_one] at this
  rw [inUJ, mul_assoc, this]

def c1 (Z : Matrix (Fin n) (Fin n) ℂ) : lieJ ε := ⟨cpart1 ε Z, (complex_parts_mem_lie_algebra_holds n ε Z).1⟩

def c2 (Z : Matrix (Fin n) (Fin n) ℂ) : lieJ ε := ⟨cpart2 ε Z, (complex_parts_mem_lie_algebra_holds n ε Z).2.1⟩

theorem c_add (Z Z' : Matrix (Fin n) (Fin n) ℂ) :
    (c1 (Z + Z') : lieJ ε) = c1 Z + c1 Z' ∧ (c2 (Z + Z') : lieJ ε) = c2 Z + c2 Z' := by
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · change cpart1 ε _ = cpart1 ε _ + cpart1 ε _
    simp only [cpart1, conjTranspose_add, mul_add, add_mul]
    module
  · change cpart2 ε _ = cpart2 ε _ + cpart2 ε _
    simp only [cpart2, conjTranspose_add, mul_add, add_mul]
    module

theorem c_smul (c : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (c1 (c • Z) : lieJ ε) = c.re • c1 Z + (-c.im) • c2 Z ∧ (c2 (c • Z) : lieJ ε) = c.im • c1 Z + c.re • c2 Z := by
  have hI : (1 / (2 * Complex.I) : ℂ) = -Complex.I / 2 := by
    field_simp
    simp
  have hc : c = c.re + c.im * Complex.I := (Complex.re_add_im c).symm
  have hs : star c = c.re - c.im * Complex.I := by
    apply Complex.ext <;> simp
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · change cpart1 ε _ = c.re • cpart1 ε _ + (-c.im) • cpart2 ε _
    simp only [cpart1, cpart2, conjTranspose_smul, mul_smul_comm, smul_mul_assoc]
    rw [hs, hI]
    generalize c.re = x at *
    generalize c.im = y at *
    subst hc
    simp only [← Complex.coe_smul]
    push_cast
    match_scalars
    · ring
    · ring
  · change cpart2 ε _ = c.im • cpart1 ε _ + c.re • cpart2 ε _
    simp only [cpart1, cpart2, conjTranspose_smul, mul_smul_comm, smul_mul_assoc]
    rw [hs, hI]
    generalize c.re = x at *
    generalize c.im = y at *
    subst hc
    simp only [← Complex.coe_smul]
    match_scalars
    · linear_combination (-(y : ℂ) / 2) * Complex.I_mul_I
    · linear_combination ((y : ℂ) / 2) * Complex.I_mul_I

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem isLieData (ι : UJ ε →* G) : IsLieData (barJ ε) (lieJ ε).subtype (sec ι) where
  anti a b := by simp only [barJ_apply, conjTranspose_mul, mul_assoc, signature_mul_signature_mul]
  one := by simp [barJ_apply, Jm_mul_self]
  invol a := by
    simp only [barJ_apply, conjTranspose_mul, Jm_conjTranspose, conjTranspose_conjTranspose, mul_assoc, signature_mul_signature_mul,
      Jm_mul_self, mul_one]
  inj := Subtype.val_injective
  skew X := ⟨fun h => ⟨⟨X, (inG_iff X).2 h⟩, rfl⟩, fun ⟨Y, h⟩ => h ▸ (inG_iff _).1 Y.2⟩
  mul a b ha hb := by
    have := sec_uMat ι (toUJ a (inUJ_of ha) * toUJ b (inUJ_of hb))
    rw [map_mul, ← sec_uMat, ← sec_uMat] at this
    exact this

theorem expMap_eq (ι : UJ ε →* G) (X : lieJ ε) (t : ℝ) :
    expMap (lieJ ε).subtype (sec ι) (t • X) = line ι X.1 t := by
  rw [expMap, line, Complex.coe_smul]
  rfl

def derEnd (ι : UJ ε →* G) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smSub (expMap (lieJ ε).subtype (sec ι))) where
  toFun Z := derOp (isLieData ι) (hasLog_of_isLieData _ _ _ _ _ _ (isLieData ι)) (c1 Z) +
    Complex.I • derOp (isLieData ι) (hasLog_of_isLieData _ _ _ _ _ _ (isLieData ι)) (c2 Z)
  map_add' Z Z' := by
    rw [(c_add Z Z').1, (c_add Z Z').2, derOp_add, derOp_add]
    module
  map_smul' c Z := by
    rw [(c_smul c Z).1, (c_smul c Z).2, derOp_add, derOp_add, derOp_smul, derOp_smul, derOp_smul, derOp_smul,
      RingHom.id_apply]
    have hc : c = c.re + c.im * Complex.I := (Complex.re_add_im c).symm
    generalize c.re = x at *
    generalize c.im = y at *
    subst hc
    push_cast
    match_scalars
    · ring
    · linear_combination (-(y : ℂ)) * Complex.I_mul_I

theorem derEnd_coe (ι : UJ ε →* G) (Z : Matrix (Fin n) (Fin n) ℂ) (ψ : smSub (expMap (lieJ ε).subtype (sec ι))) :
    (derEnd ι Z ψ).1 = derC ι Z ψ.1 := by
  funext g
  change Der _ (c1 Z) ψ.1 g + Complex.I • Der _ (c2 Z) ψ.1 g = _
  simp only [Der, expMap_eq]
  rfl

theorem foldr_ofFn {M : Type} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (k : ℕ) :
    ∀ (f : Fin k → M → M) (a : Fin k → Module.End ℂ S), (∀ i (x : S), f i x.1 = (a i x).1) → ∀ x : S,
      (List.ofFn f).foldr (fun f acc => f acc) x.1 = ((List.ofFn a).prod x).1 := by
  induction k with
  | zero => intro f a _ x; simp
  | succ k ih =>
    intro f a h x
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.prod_cons, Module.End.mul_apply,
      ih _ _ (fun i => h i.succ), h]

theorem gelfG_eq (ι : UJ ε →* G) (m : ℕ) (ψ : smSub (expMap (lieJ ε).subtype (sec ι))) :
    gelfG ι m ψ.1 = (gelfA (fun a b => derEnd ι (Matrix.single a b 1)) m ψ).1 := by
  rw [gelfG, gelfA, LinearMap.sum_apply, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun idx _ => foldr_ofFn _ _ _ _ (fun _ _ => (derEnd_coe ι _ _).symm) ψ

theorem sm_right (ι : UJ ε →* G) {a : G} {k : UJ ε} (hk : ∀ h, ι h * a = a * ι (k⁻¹ * h * k)) {ψ : G → ℂ}
    (hψ : Sm (expMap (lieJ ε).subtype (sec ι)) ψ) : Sm (expMap (lieJ ε).subtype (sec ι)) fun x => ψ (x * a) := by
  intro g
  let A : lieJ ε →ₗ[ℝ] lieJ ε :=
    ((LinearMap.mulRight ℝ (uMat k)) ∘ₗ (LinearMap.mulLeft ℝ (uMat k⁻¹))).restrict fun X hX =>
      (inG_iff (uMat k⁻¹ * X * uMat k)).2 (by
        rw [barJ_apply, conj_bar, ← barJ_apply, (inG_iff X).1 hX, mul_neg, neg_mul])
  have := (hψ (g * a)).comp (LinearMap.toContinuousLinearMap A).contDiff
  convert this using 2 with X
  have h1 := expMap_eq ι X 1
  have h2 := expMap_eq ι (A X) 1
  rw [one_smul] at h1 h2
  change ψ (g * expMap (lieJ ε).subtype (sec ι) X * a) = ψ (g * a * expMap (lieJ ε).subtype (sec ι) (A X))
  rw [h1, h2, mul_assoc, mul_assoc, der_right ι hk X.2]
  rfl

theorem gelfG_right (ι : UJ ε →* G) {a : G} {k : UJ ε} (hk : ∀ h, ι h * a = a * ι (k⁻¹ * h * k)) (m : ℕ) {ψ : G → ℂ}
    (hψ : ∀ (r : ℕ) (Y : Fin r → Matrix (Fin n) (Fin n) ℂ), (∀ i, inG ε (Y i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin r → ℝ => ψ (g * (List.ofFn fun i => line ι (Y i) (t i)).prod)) :
    gelfG ι m (fun x => ψ (x * a)) = fun x => gelfG ι m ψ (x * a) := by
  have hs : Sm (expMap (lieJ ε).subtype (sec ι)) ψ :=
    (SecondKind.main _ _ _ _ _ _ (isLieData ι) (hasLog_of_isLieData _ _ _ _ _ _ (isLieData ι)) Set.univ
      Submodule.span_univ ψ).2 fun r Y _ g => by
        simp only [expMap_eq]
        exact hψ r (fun i => (Y i).1) (fun i => (Y i).2) g
  let T : Module.End ℂ (smSub (expMap (lieJ ε).subtype (sec ι))) :=
    (LinearMap.funLeft ℂ ℂ (fun x => x * a)).restrict fun _ hx => sm_right ι hk hx
  have hQP : (uMat k)ᵀ * (uMat k⁻¹)ᵀ = 1 := by
    rw [← transpose_mul, show uMat k⁻¹ * uMat k = 1 from Units.inv_mul _, transpose_one]
  have key := GelfAd.trace_pow_comm (fun a b => derEnd ι (Matrix.single a b 1)) T _ _ hQP
    (fun a b => by
      simp only [← map_smul, ← map_sum]
      have e : ∑ c, ∑ d, ((uMat k⁻¹)ᵀ a c * (uMat k)ᵀ d b) •
          (Matrix.single c d 1 : Matrix (Fin n) (Fin n) ℂ) = uMat k⁻¹ * Matrix.single a b 1 * uMat k := by
        rw [matrix_eq_sum_single (uMat k⁻¹ * Matrix.single a b 1 * uMat k)]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
        congr 1
        simp [Matrix.mul_apply, Matrix.single, ite_and]
      rw [e]
      refine LinearMap.ext fun φ => Subtype.ext ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, derEnd_coe]
      refine (derC_right ι hk _ φ.1).trans ?_
      rw [← derEnd_coe]
      rfl) (m + 1)
  rw [← gelfA_eq_sum_pow] at key
  have := congrArg (fun S : Module.End ℂ (smSub (expMap (lieJ ε).subtype (sec ι))) => (S ⟨ψ, hs⟩).1) key
  rw [gelfG_eq ι m ⟨ψ, hs⟩, gelfG_eq ι m ⟨_, sm_right ι hk hs⟩]
  exact this

end Group

section Words

open GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut NumberField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def ByWords (T : (GAd σ J → ℂ) → GAd σ J → ℂ) : Prop :=
  ∃ w : List (ℝ → GAd σ J) →₀ ℂ, (∀ l ∈ w.support, ∀ γ ∈ l, IsRealLine σ J γ) ∧ ∀ f, IsSm σ J f → T f = dop w f

variable {σ J}

theorem byWords_id : ByWords σ J fun f => f :=
  ⟨Finsupp.single [] 1, by simp, fun f _ => by rw [dop_single]; simp⟩

theorem ByWords.comp {S T : (GAd σ J → ℂ) → GAd σ J → ℂ} (hS : ByWords σ J S) (hT : ByWords σ J T) :
    ByWords σ J fun f => S (T f) := by
  obtain ⟨w, hw, eS⟩ := hS
  obtain ⟨z, hz, eT⟩ := hT
  refine ⟨wordMul w z, fun m hm γ hγ => ?_, fun f hf => ?_⟩
  · obtain ⟨l, hl, l', hl', rfl⟩ := mem_support_wordMul hm
    rcases List.mem_append.1 hγ with h | h
    exacts [hw l hl γ h, hz l' hl' γ h]
  · obtain ⟨h1, h2⟩ := GlobalTheory.UAut.DopComp.dop_dop σ J f hf w z hw hz
    beta_reduce
    rw [eT f hf, eS _ h1, h2]

theorem byWords_foldr (L : List ((GAd σ J → ℂ) → GAd σ J → ℂ)) (h : ∀ T ∈ L, ByWords σ J T) :
    ByWords σ J fun f => L.foldr (fun T acc => T acc) f := by
  induction L with
  | nil => exact byWords_id
  | cons T L ih =>
    exact (h T List.mem_cons_self).comp (ih fun S hS => h S (List.mem_cons_of_mem _ hS))

theorem byWords_sum {ι : Type} (s : Finset ι) (T : ι → (GAd σ J → ℂ) → GAd σ J → ℂ) (h : ∀ i, ByWords σ J (T i)) :
    ByWords σ J fun f => ∑ i ∈ s, T i f := by
  classical
  choose w hw e using h
  refine ⟨∑ i ∈ s, w i, fun l hl => ?_, fun f hf => ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hl)
    exact hw i l hi
  · rw [dop_sum_comb]
    exact Finset.sum_congr rfl fun i _ => e i f hf

theorem byWords_two {γ δ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (hδ : IsRealLine σ J δ) (c : ℂ) :
    ByWords σ J fun f => lineDer γ f + c • lineDer δ f := by
  classical
  refine ⟨Finsupp.single [γ] 1 + Finsupp.single [δ] c, fun l hl ε hε => ?_, fun f _ => ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_add hl) with hl | hl <;>
      obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hl) <;>
      obtain rfl := List.mem_singleton.1 hε
    exacts [hγ, hδ]
  · rw [dop_add_comb, dop_single, dop_single]
    funext g
    simp

theorem byWords_gelfG {d : ℕ} {ε : Fin d → Bool} (ι : UJ ε →* GAd σ J)
    (h : ∀ X, inG ε X → IsRealLine σ J (line ι X)) (m : ℕ) : ByWords σ J (gelfG ι m) :=
  byWords_sum Finset.univ _ fun _ => byWords_foldr _ fun T hT => by
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hT
    exact byWords_two (h _ (complex_parts_mem_lie_algebra_holds d ε _).1) (h _ (complex_parts_mem_lie_algebra_holds d ε _).2.1) Complex.I

end Words

section Bridge

open GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.AdBridge
open GlobalTheory.Orb (archMat)
open scoped TensorProduct

variable (I : AutInst)

def embAtPlace (v : InfinitePlace I.F) : EmbOver I.E v := ⟨I.φ v, RingHom.ext (I.φ_over v)⟩

theorem infEmb_compInf (v : InfinitePlace I.F) (y : AF I.F ⊗[I.F] I.E) :
    infEmb (embAtPlace I v) (compInf I.F I.E v y) = thetaV I v y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [thetaV_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem archMat_bridge (x : I.GA) (v : InfinitePlace I.F) :
    archMat I.cm.sig I.J (embAtPlace I v) (projArch I.cm.sig I.J v (bridgeS I I.cm.sig rfl x)) =
      I.P v * uMat (x.1 v) * (I.P v)⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  rw [(bridgeS_isBridge I x).1 v, ofHAInf, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  ext i j
  exact infEmb_compInf I v _

theorem tauF_eq (z : AF I.F ⊗[I.F] I.E) :
    tauF I z = Algebra.TensorProduct.comm I.F _ _ (Algebra.TensorProduct.map (sndA I.F) (AlgHom.id I.F I.E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem bridge_mem_infPts (y : I.Ginf) : bridgeS I I.cm.sig rfl (y, 1) ∈ infPts I.cm.sig I.J := by
  have h := (bridgeS_isBridge I (y, 1)).2
  refine Units.ext (Matrix.ext fun i j => ?_)
  apply (Algebra.TensorProduct.comm I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af I.F) I.E).injective
  refine (tauF_eq I _).symm.trans ((congrFun (congrFun h i) j).symm.trans ?_)
  change (1 : Matrix (Fin I.n) (Fin I.n) _) i j = Algebra.TensorProduct.comm I.F _ _ ((1 : Matrix (Fin I.n) (Fin I.n) _) i j)
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

open Classical in

def iota (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) (v : InfinitePlace I.F) : UJ (I.ε v) →* GAd s I.J :=
  (bridgeS I s hs : I.GA →* GAd s I.J).comp
    ((MonoidHom.inl I.Ginf I.Gf).comp (MonoidHom.mulSingle (fun u => UJ (I.ε u)) v))

open Classical in
theorem iota_apply (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) (v : InfinitePlace I.F) (h : UJ (I.ε v)) :
    iota I s hs v h = bridgeS I s hs (Pi.mulSingle v h, 1) := rfl

theorem iota_conj (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) (v : InfinitePlace I.F) (b : I.GA) (h : UJ (I.ε v)) :
    iota I s hs v h * bridgeS I s hs b = bridgeS I s hs b * iota I s hs v ((b.1 v)⁻¹ * h * b.1 v) := by
  classical
  rw [iota_apply, iota_apply, ← map_mul, ← map_mul]
  congr 1
  refine Prod.ext (funext fun u => ?_) (by simp)
  by_cases e : u = v
  · subst e
    simp [mul_assoc]
  · simp [Pi.mulSingle_eq_of_ne e]

theorem isRealLine_line (v : InfinitePlace I.F) {X : Matrix (Fin I.n) (Fin I.n) ℂ} (hX : inG (I.ε v) X) :
    IsRealLine I.cm.sig I.J (line (iota I I.cm.sig rfl v) X) := by
  classical
  have hcm : IsCMExt I.F I.E I.cm.sig := ⟨I.cm.totReal, I.cm.cmUnram.1, I.cm.deg2, I.cm.cmUnram.2.1⟩
  have hd := fun u => (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit u)
  refine ⟨v, embAtPlace I v, I.P v * X * (I.P v)⁻¹, ?_, fun t => ⟨projArch _ _ v (line (iota I I.cm.sig rfl v) X t), ?_, ?_⟩⟩
  · have hP := I.P_spec v
    have hX' : Xᴴ * Jm (I.ε v) + Jm (I.ε v) * X = 0 := hX
    have h1 := Matrix.mul_nonsing_inv _ (hd v)
    change _ * I.J.map (I.φ v) + I.J.map (I.φ v) * _ = 0
    rw [← hP] at hX'
    generalize I.J.map (I.φ v) = Q at *
    generalize (I.P v)⁻¹ = P' at *
    generalize I.P v = P at *
    have h2 : P'ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
    have := congrArg (fun M => P'ᴴ * M * P') hX'
    simp only [mul_add, add_mul, mul_assoc, h1, mul_one, mul_zero, zero_mul] at this
    simp only [← mul_assoc, h2, one_mul] at this
    simpa only [conjTranspose_mul, mul_assoc] using this
  · rw [line_eq _ hX, iota_apply]
    refine GAd_ext _ _ (fun u => ?_) fun w => ?_
    · by_cases e : u = v
      · subst e
        rw [projArch_embArch_self]
      · rw [projArch_embArch_ne _ _ e]
        apply (GlobalTheory.Orb.isEmbedding_archMat I.J hcm (embAtPlace I u)).injective
        change archMat _ _ _ _ = archMat _ _ _ _
        rw [archMat_bridge, map_one]
        dsimp only
        rw [Pi.mulSingle_eq_of_ne e]
        exact (congrArg (· * (I.P u)⁻¹) (mul_one _)).trans (Matrix.mul_nonsing_inv _ (hd u))
    · rw [proj_embArch]
      exact mem_infPts_iff_forall.1 (bridge_mem_infPts I _) w
  · rw [line_eq _ hX, iota_apply, archMat_bridge]
    dsimp only
    rw [Pi.mulSingle_eq_same, ← Matrix.smul_mul, ← Matrix.mul_smul,
      Matrix.exp_conj _ _ (I.P_unit v), ← Complex.coe_smul]
    rfl

theorem zOp_eq_dop : ∀ (I : Formalism.MainNotions.S.AutInst) (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) (v : InfinitePlace I.F) (m : ℕ),
    ∃ z : List (ℝ → GlobalTheory.AdelicU.GAd s I.J) →₀ ℂ, GlobalTheory.UAut.IsCentral s I.J z ∧
      ∀ (N : ℕ) (φ : GlobalTheory.AdelicU.GAd s I.J → ℂ), GlobalTheory.UAut.IsSm s I.J φ →
        (GlobalTheory.Dec.zOp I v m)^[N] (fun x => φ (GlobalTheory.HCFinU.bridgeS I s hs x)) =
          fun x => (GlobalTheory.UAut.dop z)^[N] φ (GlobalTheory.HCFinU.bridgeS I s hs x) := by
  intro I s hs v m
  subst hs
  obtain ⟨z, hz, e⟩ := byWords_gelfG (iota I I.cm.sig rfl v) (fun X hX => isRealLine_line I v hX) m
  have hcm : IsCMExt I.F I.E I.cm.sig := ⟨I.cm.totReal, I.cm.cmUnram.1, I.cm.deg2, I.cm.cmUnram.2.1⟩
  refine ⟨z, ⟨hz, fun f hf a _ g => ?_⟩, fun N => ?_⟩
  · obtain ⟨b, rfl⟩ := (bridgeS I I.cm.sig rfl).surjective a
    rw [← e f hf, ← e _ (GlobalTheory.UAut.isSm_mul_right_of_isCMExt _ _ hcm f _ hf)]
    exact congrFun (gelfG_right _ (iota_conj I _ rfl v b) m fun r Y hY g =>
      hf r (fun i => line _ (Y i)) (fun i => isRealLine_line I v (hY i)) g) g
  · induction N with
    | zero => exact fun _ _ => rfl
    | succ N ih =>
      intro φ hφ
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        ← ih _ (GlobalTheory.UAut.DopComp.dop_dop _ _ φ hφ z z hz hz).1]
      congr 1
      funext x
      rw [← e φ hφ]
      exact gelf_eq _ (fun h => by rw [slice_apply, map_mul, iota_apply]) m

end Bridge

end GlobalTheory.HCFinU.Central

end
