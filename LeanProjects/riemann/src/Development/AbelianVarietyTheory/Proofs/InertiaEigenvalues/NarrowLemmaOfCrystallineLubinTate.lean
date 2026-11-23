import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.LTCrys
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.EqNegOneOfJumpAt
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ConradLocalTied
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLubinTateChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCharIsCrystallineHodgeTateZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineTwistCrystallineCharacterJumpsShift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInvAndHodgeTateJumpsNeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumOfIsCrys
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingsRegularPhiSurjectiveFil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsAlgebraicVectorSpanningSubspace
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AinfActionTiltFixedOfFrobeniusRelation

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne TensorProduct CompanionTheory.PRW.ACWD

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PY.LocAlgCrys

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l}

variable (L) in

def gal (g : GQ l) : ↥L.1 ⊗[ℚ_[l]] P.R.B →ₐ[↥L.1] ↥L.1 ⊗[ℚ_[l]] P.R.B :=
  Algebra.TensorProduct.map (AlgHom.id ↥L.1 ↥L.1) (P.actQ g : P.R.B →ₐ[ℚ_[l]] P.R.B)

variable (L) in

def phi (f : ℕ) : ↥L.1 ⊗[ℚ_[l]] P.R.B →ₐ[↥L.1] ↥L.1 ⊗[ℚ_[l]] P.R.B :=
  Algebra.TensorProduct.map (AlgHom.id ↥L.1 ↥L.1) (P.φB ^ f)

theorem mem_D (χ : ↥(GK K) →* (↥L.1)ˣ) (x : ↥L.1 ⊗[ℚ_[l]] P.R.B) :
    x ∈ Dcris (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ) ↔ ∀ g : ↥(GK K), ((χ g : (↥L.1)ˣ) : ↥L.1) • gal P L g x = x := by
  have h : ∀ (g : ↥(GK K)) y, actVB (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ) g y = ((χ g : (↥L.1)ˣ) : ↥L.1) • gal P L g y := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    | tmul v b =>
      change (((χ g : (↥L.1)ˣ) : ↥L.1) • v) ⊗ₜ[ℚ_[l]] (P.PD K).actB g b = _
      rw [P.PD_actB]
      rfl
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero, h]

theorem mul_mem_D {χ χ' : ↥(GK K) →* (↥L.1)ˣ} {x y : ↥L.1 ⊗[ℚ_[l]] P.R.B}
    (hx : x ∈ Dcris (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ)) (hy : y ∈ Dcris (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ')) :
    x * y ∈ Dcris (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep (χ * χ')) := by
  rw [mem_D] at hx hy ⊢
  intro g
  rw [map_mul, MonoidHom.mul_apply, Units.val_mul, ← smul_mul_smul_comm, hx, hy]

def Gen (f : ℕ) (χ : ↥(GK K) →* (↥L.1)ˣ) (c : (↥L.1)ˣ) : Prop :=
  Ideal.span {x | x ∈ Dcris (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ) ∧ phi P L f x = (c : ↥L.1) • x} = ⊤

def Eig (f : ℕ) (χ : ↥(GK K) →* (↥L.1)ˣ) (c : (↥L.1)ˣ) : Prop :=
  ∀ x ∈ Dcris (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ), phi P L f x = (c : ↥L.1) • x

variable {P} {f : ℕ} {χ χ' : ↥(GK K) →* (↥L.1)ˣ} {c c' : (↥L.1)ˣ}

theorem Gen.eig_inv (h1 : Eig P f (1 : ↥(GK K) →* (↥L.1)ˣ) 1) (h : Gen P f χ c) : Eig P f χ⁻¹ c⁻¹ := by
  intro y hy
  have key : ∀ x ∈ Ideal.span {x | x ∈ Dcris (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ) ∧ phi P L f x = (c : ↥L.1) • x},
      x * ((c : ↥L.1) • phi P L f y - y) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have h2 := mul_mem_D P hx.1 hy
      rw [mul_inv_cancel] at h2
      have h3 := h1 _ h2
      rw [map_mul, hx.2, Units.val_one, one_smul] at h3
      rw [mul_sub, mul_smul_comm, ← smul_mul_assoc, h3, sub_self]
    | zero => rw [zero_mul]
    | add a b _ _ ha hb => rw [add_mul, ha, hb, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, mul_assoc, hx, mul_zero]
  have h4 := key 1 (by rw [h]; trivial)
  rw [one_mul, sub_eq_zero] at h4
  conv_rhs => rw [← h4, smul_smul, Units.inv_mul, one_smul]

theorem Eig.gen {AI : LocAinf l P} (T : LocTied l P AI) (hc : IsCrys (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ))
    (h : Eig P f χ c) : Gen P f χ c := by
  obtain ⟨m, b, d, hd, h1⟩ := GlobalTheory.Per.TiedSpan.tied_crisSpan l P AI T (GlobalTheory.MemLoc.tied_regular_and_onto l P AI T).1
    K L ↥L.1 _ hc 1
  rw [Gen, Ideal.eq_top_iff_one, h1]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [GlobalTheory.TwistJump.map_mulLeft]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨hd i, h _ (hd i)⟩)

theorem phi_ιA (AI : LocAinf l P) (k : ℕ) (x : Ainf l) :
    (P.φB ^ k) (AI.ιA x) = AI.ιA (WittVector.map (iterateFrobenius _ l k) x) := by
  induction k with
  | zero =>
    change AI.ιA x = _
    congr 1
    ext i
    simp
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, ← AI.ιA_φ, WittVector.frobenius_eq_map_frobenius]
    congr 1
    ext i
    simp [iterateFrobenius_def, frobenius_def, pow_succ, pow_mul]

variable (P) in

def Good (f : ℕ) (χ : ↥(GK K) →* (↥L.1)ˣ) (a : (↥K.1 →ₐ[ℚ_[l]] ↥L.1) → ℤ) (c : (↥L.1)ˣ) : Prop :=
  IsCrys (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ) ∧
    (∀ τ b, multV (P.PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep χ) τ b = if b = a τ then 1 else 0) ∧ Eig P f χ c

variable {AI : LocAinf l P} (T : LocTied l P AI) (h1 : Eig P f (1 : ↥(GK K) →* (↥L.1)ˣ) 1)
  {a a' : (↥K.1 →ₐ[ℚ_[l]] ↥L.1) → ℤ}
include T h1

theorem Good.inv (h : Good P f χ a c) : Good P f χ⁻¹ (-a) c⁻¹ :=
  ⟨(GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg l P AI T K L χ a h.1 h.2.1).1, (GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg l P AI T K L χ a h.1 h.2.1).2,
    (h.2.2.gen T h.1).eig_inv h1⟩

end Local

section Bridge

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
  (P : LocPrime l) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
  {L L' : FinExt l} (hL : L.1 ≤ L'.1)

def tr : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] P.R.B →ₗ[ℚ_[l]] ↥L'.1 ⊗[ℚ_[l]] P.R.B :=
  LinearMap.rTensor P.R.B ((IntermediateField.inclusion hL).toLinearMap ∘ₗ LinearMap.proj 0)

variable (ψ : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L.1) (χ : ↥(GK Bw.Kw) →* (↥L'.1)ˣ)
  (hχ : ∀ g, (((χ g : (↥L'.1)ˣ) : ↥L'.1) : Qbar l) = ent ψ (Bw.e.symm g))
include hχ

end Bridge

end GlobalTheory.PY.LocAlgCrys

end
