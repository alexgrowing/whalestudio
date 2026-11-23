import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Formalism.AdmissibleDesigns.InvariantsEqBotIff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
  GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf
open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

namespace GlobalTheory.ConjLocal

section DdR

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

theorem finrank_DdR_congr : finrank LL ↥(DdR PD ρ) = finrank LL ↥(DdR PD ρ') := by
  let E : V ⊗[Qp] BdR ≃ₗ[LL] V' ⊗[Qp] BdR := AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)
  have hE : ∀ g x, E (actVdR PD ρ g x) = actVdR PD ρ' g (E x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, actVdR, he]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hD : DdR PD ρ = (DdR PD ρ').comap (E : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR) := by
    ext x
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, Submodule.mem_comap, sub_eq_zero]
    constructor
    · intro hx g
      rw [LinearEquiv.coe_coe, ← hE, hx g]
    · intro hx g
      apply E.injective
      rw [hE]
      exact hx g
  rw [hD]
  exact (E.ofSubmodule' (DdR PD ρ')).finrank_eq

end DdR

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {a : ℕ}

theorem exists_ext_entries (L₁ : FinExt l) (A : GL (Fin a) (Om l)) :
    ∃ L₂ : FinExt l, L₁.1 ≤ L₂.1 ∧ (∀ i j, (A : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L₂.1) ∧
      ∀ i j, ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L₂.1 := by
  let f : Bool × Fin a × Fin a → Om l := fun p => if p.1 then (A : Matrix (Fin a) (Fin a) (Om l)) p.2.1 p.2.2
    else ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) p.2.1 p.2.2
  have hfin : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨supExt L₁ ⟨_, hfin⟩, le_sup_left, fun i j => ?_, fun i j => ?_⟩
  · exact (le_sup_right : IntermediateField.adjoin ℚ_[l] (Set.range f) ≤ L₁.1 ⊔ _)
      (IntermediateField.subset_adjoin _ _ ⟨(true, i, j), rfl⟩)
  · exact (le_sup_right : IntermediateField.adjoin ℚ_[l] (Set.range f) ≤ L₁.1 ⊔ _)
      (IntermediateField.subset_adjoin _ _ ⟨(false, i, j), rfl⟩)

theorem repE_apply (L : FinExt l) (r : ↥Gw →* GL (Fin a) ↥L.1) (g : ↥(GK Bw.Kw)) (x : Fin a → ↥L.1) :
    Bw.repE L r g x = ((r (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1).mulVec x := by
  simp [LocBridge.repE, Matrix.toLinAlgEquiv'_apply]

variable {Bw} in

theorem exists_conj_model {r r' : ↥Gw →* GL (Fin a) (Om l)} (A : GL (Fin a) (Om l))
    (hc : ∀ g, r' g = A * r g * A⁻¹) {L₁ : FinExt l} {r₁ : ↥Gw →* GL (Fin a) ↥L₁.1}
    (h₁ : IsModel Bw r L₁ r₁) :
    ∃ (L₂ : FinExt l) (hL : L₁.1 ≤ L₂.1) (r₂ : ↥Gw →* GL (Fin a) ↥L₂.1), IsModel Bw r' L₂ r₂ ∧
      ∃ e : (Fin a → ↥L₂.1) ≃ₗ[↥L₂.1] (Fin a → ↥L₂.1), ∀ g x,
        e (Bw.repE L₂ (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x) =
          Bw.repE L₂ r₂ g (e x) := by
  obtain ⟨L₂, hL, hA, hB⟩ := exists_ext_entries L₁ A
  let A₂ : Matrix (Fin a) (Fin a) ↥L₂.1 := fun i j => ⟨_, hA i j⟩
  let B₂ : Matrix (Fin a) (Fin a) ↥L₂.1 := fun i j => ⟨_, hB i j⟩
  let f : ↥L₂.1 →+* Om l := algebraMap ↥L₂.1 (Om l)
  have fA : f.mapMatrix A₂ = (A : Matrix (Fin a) (Fin a) (Om l)) := rfl
  have fB : f.mapMatrix B₂ = ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) := rfl
  have inj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L₂.1 → Matrix (Fin a) (Fin a) (Om l)) :=
    Matrix.map_injective Subtype.val_injective
  have h1 : A₂ * B₂ = 1 := inj (by rw [map_mul, map_one, fA, fB, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have h2 : B₂ * A₂ = 1 := inj (by rw [map_mul, map_one, fA, fB, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  let U : GL (Fin a) ↥L₂.1 := ⟨A₂, B₂, h1, h2⟩
  refine ⟨L₂, hL, (MulAut.conj U).toMonoidHom.comp
    (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁), ?_, ?_⟩
  · refine ⟨h₁.1.trans hL, ?_⟩
    ext g i j
    rw [hc g, ← h₁.2]
    change (f.mapMatrix (A₂ * ((IntermediateField.inclusion hL).toRingHom.mapMatrix
        ((r₁ g : GL (Fin a) ↥L₁.1) : Matrix (Fin a) (Fin a) ↥L₁.1)) * B₂)) i j =
      ((A : Matrix (Fin a) (Fin a) (Om l)) * (algebraMap ↥L₁.1 (Om l)).mapMatrix
        ((r₁ g : GL (Fin a) ↥L₁.1) : Matrix (Fin a) (Fin a) ↥L₁.1) *
        ((A⁻¹ : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) i j
    rw [map_mul, map_mul, fA, fB]
    rfl
  · refine ⟨Formalism.MainNotions.N.K.Norm.matEquiv A₂ B₂ h1 h2, fun g x => ?_⟩
    rw [Formalism.MainNotions.N.K.Norm.matEquiv_apply, Formalism.MainNotions.N.K.Norm.matEquiv_apply, repE_apply, repE_apply]
    change A₂.mulVec (Matrix.mulVec _ x) = Matrix.mulVec (A₂ * _ * B₂) (A₂.mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem local_conj : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Gw : Subgroup (Ω ≃ₐ[E] Ω))
    (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r r' : ↥Gw →* GL (Fin a) (Om l)) (A : GL (Fin a) (Om l)),
    (∀ g, r' g = A * r g * A⁻¹) → (IsdRAt P Bw r → IsdRAt P Bw r') ∧ (IsCrysAt P Bw r → IsCrysAt P Bw r') ∧
      (IsPotCrysAt P Bw r → IsPotCrysAt P Bw r') ∧
      ∀ (τ : E →+* Om l) (J : Multiset ℤ), IsJumpsAt P Bw r τ J → IsJumpsAt P Bw r' τ J := by
  intro l _ P E Ω _ _ _ _ O _ _ _ Gw Bw a r r' A hc
  have dR : ∀ {L₁ L₂ : FinExt l} {r₁ : ↥Gw →* GL (Fin a) ↥L₁.1} (hL : L₁.1 ≤ L₂.1)
      (r₂ : ↥Gw →* GL (Fin a) ↥L₂.1) (e : (Fin a → ↥L₂.1) ≃ₗ[↥L₂.1] (Fin a → ↥L₂.1)),
      (∀ g x, e (Bw.repE L₂ (Formalism.MainNotions.N.mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x) =
          Bw.repE L₂ r₂ g (e x)) → Bw.IsdRE P L₁ r₁ → Bw.IsdRE P L₂ r₂ := by
    intro L₁ L₂ r₁ hL r₂ e he hd
    have h := (local_ext P Bw hL r₁).2.1.2 hd
    unfold LocBridge.IsdRE at h ⊢
    rw [← finrank_DdR_congr (P.PD Bw.Kw) e he, h]
  refine ⟨fun ⟨L₁, r₁, h₁, hd⟩ => ?_, fun ⟨L₁, r₁, h₁, hd⟩ => ?_, fun ⟨L₁, r₁, h₁, hd⟩ => ?_,
    fun τ J ⟨L₁, r₁, h₁, hd, τ₁, hτ, hJ⟩ => ?_⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    exact ⟨L₂, r₂, hm, dR hL r₂ e he hd⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    exact ⟨L₂, r₂, hm, Formalism.MainNotions.N.K.Norm.isCrys_congr (P.PD Bw.Kw) e he ((local_ext P Bw hL r₁).1.2 hd)⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    obtain ⟨K', hK, hcr⟩ := (local_ext P Bw hL r₁).2.2.1.2 hd
    exact ⟨L₂, r₂, hm, K', hK, Formalism.MainNotions.N.K.Norm.isCrys_congr (P.PD K') e (fun g x => he _ x) hcr⟩
  · obtain ⟨L₂, hL, r₂, hm, e, he⟩ := exists_conj_model A hc h₁
    refine ⟨L₂, r₂, hm, dR hL r₂ e he hd, (IntermediateField.inclusion hL).comp τ₁, fun x => hτ x, fun n => ?_⟩
    rw [hJ n, ← (local_ext P Bw hL r₁).2.2.2 τ₁ n]
    exact Formalism.MainNotions.N.K.Norm.multV_congr (P.PD Bw.Kw) e he _ n

end GlobalTheory.ConjLocal
