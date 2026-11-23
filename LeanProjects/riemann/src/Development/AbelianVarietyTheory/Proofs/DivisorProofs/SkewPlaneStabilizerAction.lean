import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneConstantTermGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviOfUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementTorusPart
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

abbrev gm {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (p : GAd σ J) : Matrix (Fin n) (Fin n) (AE F E) := (matHom _ σ J p).1

theorem gm_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : gm (1 : GAd σ J) = 1 := by
  simp only [gm, map_one, Units.val_one]

theorem gm_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (p q : GAd σ J) : gm (p * q) = gm p * gm q := by
  simp only [gm, map_mul, Units.val_mul]

theorem gm_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (p : GAd σ J) : gm p⁻¹ * gm p = 1 := by
  simp only [gm, map_inv]; exact Units.inv_mul _

theorem fR_gm (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0)
    (p : GAd σ (c • J.map σ)) (u v : Fin n → AE F E) :
    fR (cA σ).toRingHom (incM F J) (gm p *ᵥ u) (gm p *ᵥ v) = fR (cA σ).toRingHom (incM F J) u v := by
  have hU : (gm p)ᵀ * incM F J * (gm p).map (cA σ).toRingHom = incM F J :=
    ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ J hc).symm p).2
  rw [fR_mulVec, hU]; rfl

theorem mul_fR_eq_one (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {c : E} (hc : c ≠ 0)
    {x y : Fin n → E} (hxy : form σ J x y = 1) (p : GAd σ (c • J.map σ)) {t : AE F E}
    (ht : gm p *ᵥ incV F x = t • incV F x) : t * fR (cA σ).toRingHom (incM F J) (incV F x) (gm p *ᵥ incV F y) = 1 := by
  have h := fR_gm hσ J hc p (incV F x) (incV F y)
  rw [ht, fR_smul_left, fR_inc, hxy, map_one] at h
  exact h

def stab (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0)
    (x y : Fin n → E) (hxy : form σ J x y = 1) : Subgroup (GAd σ (c • J.map σ)) where
  carrier := {p | ∃ t : AE F E, gm p *ᵥ incV F x = t • incV F x}
  one_mem' := ⟨1, by rw [gm_one, Matrix.one_mulVec, one_smul]⟩
  mul_mem' := by
    rintro p q ⟨t, ht⟩ ⟨s, hs⟩
    refine ⟨s * t, ?_⟩
    rw [gm_mul, ← Matrix.mulVec_mulVec, hs, Matrix.mulVec_smul, ht, smul_smul]
  inv_mem' := by
    rintro p ⟨t, ht⟩
    refine ⟨fR (cA σ).toRingHom (incM F J) (incV F x) (gm p *ᵥ incV F y), ?_⟩
    have e := mul_fR_eq_one hσ hc hxy p ht
    have h1 : incV F x = t • (gm p⁻¹ *ᵥ incV F x) := by
      rw [← Matrix.mulVec_smul, ← ht, Matrix.mulVec_mulVec, gm_inv_mul, Matrix.one_mulVec]
    generalize fR (cA σ).toRingHom (incM F J) (incV F x) (gm p *ᵥ incV F y) = s at e ⊢
    calc gm p⁻¹ *ᵥ incV F x = (t * s) • (gm p⁻¹ *ᵥ incV F x) := by rw [e, one_smul]
      _ = s • (t • (gm p⁻¹ *ᵥ incV F x)) := by rw [smul_smul, mul_comm]
      _ = s • incV F x := by rw [← h1]

theorem mem_stab {hσ : ∀ x, σ (σ x) = x} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {c : E} {hc : c ≠ 0}
    {x y : Fin n → E} {hxy : form σ J x y = 1} {p : GAd σ (c • J.map σ)} :
    p ∈ stab hσ J hc x y hxy ↔ ∃ t : AE F E, gm p *ᵥ incV F x = t • incV F x := Iff.rfl

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

local instance topRingAE : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem continuous_gm {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Continuous (gm : GAd σ J → Matrix (Fin n) (Fin n) (AE F E)) :=
  Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous

def tv {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) {J' : Matrix (Fin n) (Fin n) E} (p : GAd σ J') : AE F E :=
  fR (cA σ).toRingHom (incM F J) (gm p *ᵥ incV F x) (incV F y)

theorem continuous_tv {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (J' : Matrix (Fin n) (Fin n) E) :
    Continuous (tv (σ := σ) J x y (J' := J')) :=
  ((continuous_gm J').matrix_mulVec continuous_const).dotProduct continuous_const

variable {hσ : ∀ x, σ (σ x) = x} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {c : E} {hc : c ≠ 0}
    {x y : Fin n → E} {hxy : form σ J x y = 1}

theorem gm_x {p : GAd σ (c • J.map σ)} (hp : p ∈ stab hσ J hc x y hxy) : gm p *ᵥ incV F x = tv J x y p • incV F x := by
  obtain ⟨t, ht⟩ := hp
  rw [tv, ht, fR_smul_left, fR_inc, hxy, map_one, mul_one]

theorem isUnit_tv {p : GAd σ (c • J.map σ)} (hp : p ∈ stab hσ J hc x y hxy) : IsUnit (tv (σ := σ) J x y p) :=
  ⟨⟨_, _, mul_fR_eq_one hσ hc hxy p (gm_x hp), by rw [mul_comm]; exact mul_fR_eq_one hσ hc hxy p (gm_x hp)⟩, rfl⟩

variable (hσ J hc x y hxy) in

def tHom : stab hσ J hc x y hxy →* AE F E where
  toFun p := tv J x y p.1
  map_one' := by
    show fR _ _ (gm (1 : GAd σ (c • J.map σ)) *ᵥ _) _ = 1
    rw [gm_one, Matrix.one_mulVec, fR_inc, hxy, map_one]
  map_mul' p q := by
    show fR _ _ (gm (p.1 * q.1) *ᵥ _) _ = tv J x y p.1 * tv J x y q.1
    rw [gm_mul, ← Matrix.mulVec_mulVec, gm_x q.2, Matrix.mulVec_smul, gm_x p.2, smul_smul, fR_smul_left, fR_inc, hxy,
      map_one, mul_one, mul_comm]

variable (hσ J hc x y hxy) in

def tUnits : stab hσ J hc x y hxy →* (AE F E)ˣ := IsUnit.liftRight (tHom hσ J hc x y hxy) fun p => isUnit_tv p.2

theorem gm_x_units (p : stab hσ J hc x y hxy) : gm p.1 *ᵥ incV F x = (tUnits hσ J hc x y hxy p : AE F E) • incV F x := gm_x p.2

theorem continuous_tUnits : Continuous (tUnits hσ J hc x y hxy) := by
  refine Units.continuous_iff.2 ⟨(continuous_tv J x y _).comp continuous_subtype_val, ?_⟩
  have e : (fun p => ((tUnits hσ J hc x y hxy p)⁻¹ : (AE F E)ˣ).1) = fun p => tv J x y (p⁻¹ : stab hσ J hc x y hxy).1 := by
    funext p; rw [← map_inv]; rfl
  rw [e]
  exact (continuous_tv J x y _).comp (continuous_subtype_val.comp continuous_inv)

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem fR_mulVec_rect {R : Type} [CommRing R] (cc : R →+* R) {a b : ℕ} (J : Matrix (Fin a) (Fin a) R)
    (X : Matrix (Fin a) (Fin b) R) (u v : Fin b → R) :
    fR cc J (X *ᵥ u) (X *ᵥ v) = fR cc (Xᵀ * J * X.map cc) u v := by
  have h : (fun i => cc ((X *ᵥ v) i)) = X.map cc *ᵥ fun i => cc (v i) := by
    funext i; exact RingHom.map_mulVec cc X v i
  simp only [fR, h]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Xᵀ, Matrix.vecMul_transpose]

theorem fR_mulVec_left {R : Type} [CommRing R] (cc : R →+* R) {a b : ℕ} (J : Matrix (Fin a) (Fin a) R)
    (X : Matrix (Fin a) (Fin b) R) (z : Fin b → R) (v : Fin a → R) :
    fR cc J (X *ᵥ z) v = z ⬝ᵥ (Xᵀ * J) *ᵥ (fun i => cc (v i)) := by
  simp only [fR]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z Xᵀ, Matrix.vecMul_transpose]

theorem tr_mul_mulVec_eq_zero {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {ι : Matrix (Fin n) (Fin n₁) E} {v : Fin n → E}
    (h : ∀ u, form σ J (ι *ᵥ u) v = 0) : (ιᵀ * J) *ᵥ (fun i => σ (v i)) = 0 := by
  funext i
  have := h (Pi.single i 1)
  rw [Matrix.mulVec_single_one] at this
  rw [← Matrix.mulVec_mulVec]
  exact this

theorem cA_incV {n : ℕ} (v : Fin n → E) : (fun i => (cA σ).toRingHom (incV F v i)) = incV F (fun i => σ (v i)) := by
  funext i; exact cA_incl σ (v i)

theorem fR_incM_left {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {ι : Matrix (Fin n) (Fin n₁) E} {v : Fin n → E}
    (h : ∀ u, form σ J (ι *ᵥ u) v = 0) (z : Fin n₁ → AE F E) :
    fR (cA σ).toRingHom (incM F J) (incM F ι *ᵥ z) (incV F v) = 0 := by
  rw [fR_mulVec_left, cA_incV]
  have e : (incM F ι)ᵀ * incM F J = incM F (ιᵀ * J) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [e, ← GlobalTheory.UnipCocptForm.incV_mulVec, tr_mul_mulVec_eq_zero h]
  simp [incV, dotProduct]

theorem mulVec_eq_zero_of_tr {n n₁ : ℕ} (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E}
    {J₁ : Matrix (Fin n₁) (Fin n₁) E} {ι : Matrix (Fin n) (Fin n₁) E} {A : Matrix (Fin n₁) (Fin n) E} (hd : J₁.det ≠ 0)
    (hA : ιᵀ * J = J₁ * A.map σ) {v : Fin n → E} (h : ∀ u, form σ J (ι *ᵥ u) v = 0) : A *ᵥ v = 0 := by
  have e := tr_mul_mulVec_eq_zero h
  rw [hA, ← Matrix.mulVec_mulVec] at e
  have e2 : A.map σ *ᵥ (fun i => σ (v i)) = fun i => σ ((A *ᵥ v) i) := by
    funext i; exact (RingHom.map_mulVec (σ : E →+* E) A v i).symm
  rw [e2] at e
  have e3 := Matrix.eq_zero_of_mulVec_eq_zero hd e
  funext i
  have := congrFun e3 i
  simp only [Pi.zero_apply] at this ⊢
  rw [← hσ ((A *ᵥ v) i), this, map_zero]

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def hm {n n₁ : ℕ} (A : Matrix (Fin n₁) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E) {J' : Matrix (Fin n) (Fin n) E}
    (p : GAd σ J') : Matrix (Fin n₁) (Fin n₁) (AE F E) :=
  incM F A * gm p * incM F ι

theorem incM_one' {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  simp only [incM, Matrix.map_one _ (map_zero _) (map_one _)]

theorem incM_mul'' {a b d : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin b) (Fin d) E) :
    incM F (X * Y) = incM F X * incM F Y := by
  simp only [incM, Matrix.map_mul]

variable {hσ : ∀ x, σ (σ x) = x} {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {c : E} {hc : c ≠ 0}
  {hxy : form σ W.J H.x H.y = 1}

theorem fR_basic (hσ' : ∀ x, σ (σ x) = x) (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) :
    fR (cA σ).toRingHom (incM F W.J) (incV F H.x) (incV F H.x) = 0 ∧
    fR (cA σ).toRingHom (incM F W.J) (incV F H.y) (incV F H.x) = -1 ∧
    (∀ r, (cA σ).toRingHom ((cA σ).toRingHom r) = r) ∧
    ∀ i j, (cA σ).toRingHom (incM F W.J j i) = -incM F W.J i j := by
  have hcc : ∀ r, (cA σ).toRingHom ((cA σ).toRingHom r) = r := cA_cA σ hσ'
  have hJ : ∀ i j, (cA σ).toRingHom (incM F W.J j i) = -incM F W.J i j := fun i j => by
    change cA σ (inclR (F := F) (AF F) (W.J j i)) = -inclR (F := F) (AF F) (W.J i j)
    rw [cA_incl, hsk, map_neg]
  refine ⟨by rw [fR_inc, hH.2.1, map_zero], ?_, hcc, hJ⟩
  have := fR_skew (cA σ).toRingHom (incM F W.J) hcc hJ (incV F H.x) (incV F H.y)
  rw [fR_inc, hH.2.2.2.1, map_one, map_one] at this
  linear_combination this

theorem decomp (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0)
    {A : Matrix (Fin n₁) (Fin n) E} (hA1 : A * H.ι = 1) (hA2 : H.ιᵀ * W.J = W₁.J * A.map σ)
    {p : GAd σ (c • W.J.map σ)} (hp : p ∈ stab hσ W.J hc H.x H.y hxy) (z : Fin n₁ → AE F E) :
    fR (cA σ).toRingHom (incM F W.J) (gm p *ᵥ (incM F H.ι *ᵥ z)) (incV F H.x) = 0 ∧
      ∃ a : AE F E, gm p *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (hm A H.ι p *ᵥ z) + a • incV F H.x := by
  obtain ⟨hxx, hyx, -, -⟩ := fR_basic hσ hH hsk
  have hox : ∀ w, fR (cA σ).toRingHom (incM F W.J) (incM F H.ι *ᵥ w) (incV F H.x) = 0 :=
    fR_incM_left fun u => (hH.2.2.2.2.1 u).1
  have h0 : fR (cA σ).toRingHom (incM F W.J) (gm p *ᵥ (incM F H.ι *ᵥ z)) (incV F H.x) = 0 := by
    have e1 := fR_gm hσ W.J hc p (incM F H.ι *ᵥ z) (incV F H.x)
    rw [gm_x hp, fR_smul_right, hox] at e1
    exact (((isUnit_tv hp).map (cA σ).toRingHom).mul_right_eq_zero).1 e1
  refine ⟨h0, ?_⟩
  obtain ⟨α, β, w, hv⟩ := hH.decompA hσ hsk hd (gm p *ᵥ (incM F H.ι *ᵥ z))
  have hβ : β = 0 := by
    rw [hv, fR_add_left, fR_add_left, fR_smul_left, fR_smul_left, hxx, hyx, hox] at h0
    linear_combination -h0
  have hAx : incM F A *ᵥ incV F H.x = 0 := by
    rw [← GlobalTheory.UnipCocptForm.incV_mulVec, mulVec_eq_zero_of_tr hσ hd hA2 fun u => (hH.2.2.2.2.1 u).1]
    funext i; simp [incV]
  have hAι : incM F A * incM F H.ι = 1 := by rw [← incM_mul'', hA1, incM_one']
  have hw : hm A H.ι p *ᵥ z = w := by
    rw [hm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, hβ, zero_smul, add_zero, Matrix.mulVec_add,
      Matrix.mulVec_smul, hAx, smul_zero, zero_add, Matrix.mulVec_mulVec, hAι, Matrix.one_mulVec]
  refine ⟨α, ?_⟩
  rw [hw, hv, hβ, zero_smul, add_zero, add_comm]

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {hσ : ∀ x, σ (σ x) = x} {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {c : E} {hc : c ≠ 0}
  {hxy : form σ W.J H.x H.y = 1}

theorem A_facts (hσ' : ∀ x, σ (σ x) = x) (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hd : W₁.J.det ≠ 0)
    {A : Matrix (Fin n₁) (Fin n) E} (hA1 : A * H.ι = 1) (hA2 : H.ιᵀ * W.J = W₁.J * A.map σ) :
    incM F A *ᵥ incV F H.x = 0 ∧ incM F A * incM F H.ι = 1 := by
  refine ⟨?_, by rw [← incM_mul'', hA1, incM_one']⟩
  rw [← GlobalTheory.UnipCocptForm.incV_mulVec, mulVec_eq_zero_of_tr hσ' hd hA2 fun u => (hH.2.2.2.2.1 u).1]
  funext i; simp [incV]

theorem hm_one {A : Matrix (Fin n₁) (Fin n) E} (hA1 : A * H.ι = 1) {J' : Matrix (Fin n) (Fin n) E} :
    hm A H.ι (1 : GAd σ J') = 1 := by
  rw [hm, gm_one, Matrix.mul_one, ← incM_mul'', hA1, incM_one']

theorem hm_mul (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0)
    {A : Matrix (Fin n₁) (Fin n) E} (hA1 : A * H.ι = 1) (hA2 : H.ιᵀ * W.J = W₁.J * A.map σ)
    {p q : GAd σ (c • W.J.map σ)} (hp : p ∈ stab hσ W.J hc H.x H.y hxy) (hq : q ∈ stab hσ W.J hc H.x H.y hxy) :
    hm A H.ι (p * q) = hm A H.ι p * hm A H.ι q := by
  obtain ⟨hAx, hAι⟩ := A_facts hσ hH hd hA1 hA2
  refine eq_of_mulVec _ _ fun z => ?_
  obtain ⟨a, ha⟩ := (decomp hH hsk hd hA1 hA2 hq z).2
  obtain ⟨b, hb⟩ := (decomp hH hsk hd hA1 hA2 hp (hm A H.ι q *ᵥ z)).2
  rw [← Matrix.mulVec_mulVec, hm, gm_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha,
    Matrix.mulVec_add, hb, Matrix.mulVec_smul, gm_x hp, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, hAx, Matrix.mulVec_smul, hAx, Matrix.mulVec_mulVec, hAι, Matrix.one_mulVec]
  simp

theorem gram_inc (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) :
    (incM F H.ι)ᵀ * incM F W.J * (incM F H.ι).map (cA σ).toRingHom = incM F W₁.J := by
  have e : (incM F H.ι).map (cA σ).toRingHom = incM F (H.ι.map σ) := by
    ext i j; exact cA_incl σ (H.ι i j)
  have e2 : (incM F H.ι)ᵀ = incM F H.ιᵀ := rfl
  rw [e, e2, ← incM_mul'', ← incM_mul'', hH.2.2.2.2.2]

theorem hm_unitary (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0)
    {A : Matrix (Fin n₁) (Fin n) E} (hA1 : A * H.ι = 1) (hA2 : H.ιᵀ * W.J = W₁.J * A.map σ)
    {p : GAd σ (c • W.J.map σ)} (hp : p ∈ stab hσ W.J hc H.x H.y hxy) :
    (hm A H.ι p)ᵀ * incM F W₁.J * (hm A H.ι p).map (cA σ).toRingHom = incM F W₁.J := by
  obtain ⟨hxx, -, hcc, hJ⟩ := fR_basic hσ hH hsk
  refine eq_of_form (cA σ).toRingHom _ _ fun u v => ?_
  rw [← fR_mulVec]
  change _ = fR (cA σ).toRingHom (incM F W₁.J) u v
  rw [← gram_inc hH, ← fR_mulVec_rect, ← fR_mulVec_rect]
  obtain ⟨hu0, a, ha⟩ := decomp hH hsk hd hA1 hA2 hp u
  obtain ⟨hv0, b, hb⟩ := decomp hH hsk hd hA1 hA2 hp v
  have hu : incM F H.ι *ᵥ (hm A H.ι p *ᵥ u) = gm p *ᵥ (incM F H.ι *ᵥ u) - a • incV F H.x := by rw [ha]; abel
  have hv : incM F H.ι *ᵥ (hm A H.ι p *ᵥ v) = gm p *ᵥ (incM F H.ι *ᵥ v) - b • incV F H.x := by rw [hb]; abel
  have hxv : fR (cA σ).toRingHom (incM F W.J) (incV F H.x) (gm p *ᵥ (incM F H.ι *ᵥ v)) = 0 := by
    have := fR_skew (cA σ).toRingHom (incM F W.J) hcc hJ (gm p *ᵥ (incM F H.ι *ᵥ v)) (incV F H.x)
    rw [hv0, map_zero] at this
    linear_combination this
  rw [hu, hv, fR_sub_left, fR_sub_right, fR_sub_right, fR_smul_left, fR_smul_right, fR_smul_left, fR_smul_right, hu0,
    hxv, hxx, fR_gm hσ W.J hc p]
  ring

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

local instance topRingAE' : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _

variable (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) {c : E} (hc : c ≠ 0)
  (hxy : form σ W.J H.x H.y = 1)

def piU (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0)
    (A : Matrix (Fin n₁) (Fin n) E) (hA1 : A * H.ι = 1) (hA2 : H.ιᵀ * W.J = W₁.J * A.map σ) :
    stab hσ W.J hc H.x H.y hxy →* UA σ W₁.J where
  toFun p := ⟨⟨hm A H.ι p.1, hm A H.ι (p⁻¹).1,
    by rw [← hm_mul hH hsk hd hA1 hA2 p.2 (p⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, hm_one hA1],
    by rw [← hm_mul hH hsk hd hA1 hA2 (p⁻¹).2 p.2, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, hm_one hA1]⟩,
    hm_unitary hH hsk hd hA1 hA2 p.2⟩
  map_one' := Subtype.ext (Units.ext (hm_one hA1))
  map_mul' p q := Subtype.ext (Units.ext (hm_mul hH hsk hd hA1 hA2 p.2 q.2))

theorem continuous_piU (hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0)
    (A : Matrix (Fin n₁) (Fin n) E) (hA1 : A * H.ι = 1) (hA2 : H.ιᵀ * W.J = W₁.J * A.map σ) :
    Continuous (piU hσ W W₁ H hc hxy hH hsk hd A hA1 hA2) := by
  have hg : Continuous fun p : stab hσ W.J hc H.x H.y hxy => hm A H.ι p.1 :=
    (continuous_const.matrix_mul ((continuous_gm _).comp continuous_subtype_val)).matrix_mul continuous_const
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨hg, ?_⟩) _
  exact hg.comp continuous_inv

end GlobalTheory.StabLine

noncomputable section

namespace GlobalTheory.StabLine

open GlobalTheory.AdelicPlaneLevi

theorem exists_stab_decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      ∀ (r : ℕ) (X' Y' : Matrix (Fin n) (Fin (r + 1)) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) →
      ∃ (P : Subgroup (GAd σ (c₀ • W.J.map σ))) (π : P →* GAd σ (c₀ • W₁.J.map σ)) (T : P →* (AE F E)ˣ),
        (∀ p, p ∈ P ↔ ∃ t : AF F ⊗[F] E, (matHom _ σ _ p).1 *ᵥ (fun i => inclR (F := F) (AF F) (H.x i)) = t • fun i => inclR (F := F) (AF F) (H.x i)) ∧
        (∀ p : P, ∃ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}, ∃ m, IsLevi (W₁ := W₁) H (T p) 1 m ∧
          (p : GAd σ (c₀ • W.J.map σ)) = u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M (π p)) ∧
        (∀ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}, ∀ t m y, IsLevi (W₁ := W₁) H t 1 m →
          u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M y ∈ P) ∧
        Continuous π ∧ Continuous T ∧
        ∃ A : Matrix (Fin n₁) (Fin n) E, A * H.ι = 1 ∧ ∀ p : P, (matHom _ σ _ (π p)).1 =
          GlobalTheory.SiegelSet.adMat F A * (matHom _ σ _ (p : GAd σ (c₀ • W.J.map σ))).1 * GlobalTheory.SiegelSet.adMat F H.ι := by
  intro F E _ _ _ _ _ σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hW₁ hW M hM r X' Y' hwitt hX0
  have hH : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁ := ⟨hn, hxx, hyy, hxy, horth, hgram⟩
  have hd : W₁.J.det ≠ 0 := fun h0 => hW₁.2 (by
    have e : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero])
  obtain ⟨A, hA1, hA2, -⟩ := GlobalTheory.ThK.DescB.GenGrowth.exists_proj hσ hH hsk hd
  let πU := piU hσ W W₁ H hc₀ hxy hH hsk hd A hA1 hA2
  let π : stab hσ W.J hc₀ H.x H.y hxy →* GAd σ (c₀ • W₁.J.map σ) :=
    (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).toMonoidHom.comp πU
  let T := tUnits hσ W.J hc₀ H.x H.y hxy
  have h0 : 0 < r + 1 := Nat.succ_pos r
  have hX : ∀ k, X' k ⟨0, h0⟩ = H.x k := hX0
  have hfix : ∀ g : UA σ W.J, g ∈ GlobalTheory.ThK.unip σ W H → mat g *ᵥ incV F H.x = incV F H.x := by
    intro g hg
    refine Subgroup.closure_induction (fun g hg => hg.1) (Matrix.one_mulVec _) (fun a b _ _ ha hb => ?_)
      (fun a _ ha => ?_) hg
    · change (mat a * mat b) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec, hb, ha]
    · have e : mat a⁻¹ * mat a = 1 := by change mat (a⁻¹ * a) = 1; rw [inv_mul_cancel]; rfl
      conv_lhs => rw [← ha, Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
  refine ⟨stab hσ W.J hc₀ H.x H.y hxy, π, T, fun p => Iff.rfl, fun p => ?_, fun u hu t m y hml => ?_, ?_,
    continuous_tUnits, A, hA1, fun p => rfl⟩
  · obtain ⟨m, hml⟩ := GlobalTheory.ThK.DescB.CentreTwoExists.exists_levi_of_unit hcm W W₁ H hsk hxx hyy hxy horth (T p)
    let h := πU p
    let q : UA σ W.J := m * M h
    let g0 : UA σ W.J := (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀).symm p.1
    have hmq : mat q *ᵥ incV F H.x = (T p : AE F E) • incV F H.x := by
      change (mat m * mat (M h)) *ᵥ _ = _
      have e1 := (hM h).1
      simp only [Units.val_one, one_smul] at e1
      rw [← Matrix.mulVec_mulVec, e1, hml.1]
    have hqι : mat q * incM F H.ι = incM F H.ι * mat h := by
      change (mat m * mat (M h)) * incM F H.ι = incM F H.ι * mat h
      have e2 := hml.2.2
      rw [show mat (1 : UA σ W₁.J) = 1 from rfl, Matrix.mul_one] at e2
      rw [Matrix.mul_assoc, (hM h).2.2, ← Matrix.mul_assoc, e2]
    have hqq : mat q⁻¹ * mat q = 1 := by change mat (q⁻¹ * q) = 1; rw [inv_mul_cancel]; rfl
    have hhh : mat h * mat h⁻¹ = 1 := by change mat (h * h⁻¹) = 1; rw [mul_inv_cancel]; rfl
    have hmem : g0 * q⁻¹ ∈ GlobalTheory.ThK.unip σ W H := by
      refine Subgroup.subset_closure ⟨?_, fun z => ?_⟩
      · have e : mat (g0 * q⁻¹) *ᵥ (mat q *ᵥ incV F H.x) = (T p : AE F E) • incV F H.x := by
          change (gm p.1 * mat q⁻¹) *ᵥ _ = _
          rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hqq, Matrix.mul_one]
          exact gm_x_units p
        rw [hmq, Matrix.mulVec_smul] at e
        have := congrArg (fun w => ((T p)⁻¹ : (AE F E)ˣ).1 • w) e
        simpa only [smul_smul, Units.inv_mul, one_smul] using this
      · obtain ⟨a, ha⟩ := (decomp hH hsk hd hA1 hA2 p.2 (mat h⁻¹ *ᵥ z)).2
        refine ⟨a, ?_⟩
        have e : incM F H.ι *ᵥ z = mat q *ᵥ (incM F H.ι *ᵥ (mat h⁻¹ *ᵥ z)) := by
          symm
          rw [Matrix.mulVec_mulVec, hqι, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ (mat h), hhh, Matrix.one_mulVec]
        conv_lhs => rw [e]
        change (gm p.1 * mat q⁻¹) *ᵥ _ = _
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hqq, Matrix.mul_one, ha,
          show hm A H.ι p.1 = mat h from rfl, Matrix.mulVec_mulVec _ (mat h), hhh, Matrix.one_mulVec]
    refine ⟨GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (g0 * q⁻¹),
      (GlobalTheory.ThK.GLTwo.IsHypPlane.mem_unip_iff hσ hH hsk hd hc₀ hwitt h0 hX _).1 hmem, m, hml, ?_⟩
    have e1 : GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M (π p) = GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (M h) := by
      simp only [GlobalTheory.ThK.CuspTransfer.emb, π, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulEquiv.symm_apply_apply]
      rfl
    have e2 : g0 * q⁻¹ * m * M h = g0 := by
      rw [mul_assoc, show m * M h = q from rfl, inv_mul_cancel_right]
    rw [e1, ← map_mul, ← map_mul, e2]
    exact (MulEquiv.apply_symm_apply _ _).symm
  · have hu' : (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀).symm u ∈ GlobalTheory.ThK.unip σ W H :=
      (GlobalTheory.ThK.GLTwo.IsHypPlane.mem_unip_iff hσ hH hsk hd hc₀ hwitt h0 hX _).2 (by rwa [MulEquiv.apply_symm_apply])
    have ux := hfix _ hu'
    refine (mem_stab).2 ⟨t.1, ?_⟩
    rw [gm_mul, gm_mul]
    have e1 := (hM ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm y)).1
    simp only [Units.val_one, one_smul] at e1
    change (gm u * mat m * mat (M ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm y))) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec, hml.1, Matrix.mulVec_smul]
    exact congrArg _ ux
  · exact (GlobalTheory.ThK.GLTwo.continuous_toGAd hσ W₁.J hc₀).1.comp (continuous_piU hσ W W₁ H hc₀ hxy hH hsk hd A hA1 hA2)

end GlobalTheory.StabLine
