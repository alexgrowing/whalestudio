import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoEquivariant

noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem unitFor_of_tie (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W RA RW inclR φR gR πA)
    (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitFor E := by
  intro e₀ h₀
  obtain ⟨e₁, f₀, hf₀, hj, hN⟩ := E.one_e
  obtain ⟨u, hu, hT⟩ := W.one_line
  have huT : u ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self u
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hf₀ ▸ Submodule.mem_top : e₀ ∈ Submodule.span O {f₀})
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 (h₀ ▸ Submodule.mem_top : f₀ ∈ Submodule.span O {e₀})
  have hje : E.jD W.one (c • e₁) = (1 : RW) ⊗ₜ[O] e₀ := by
    rw [map_smul, hj, ← hc, TensorProduct.tmul_smul]
  have hde : d • (c • e₁) = e₁ := by
    apply E.jD_inj
    rw [map_smul, hje, hj, ← hd, TensorProduct.tmul_smul]
  refine ⟨c • e₁, hje, ⟨fun x y hxy => ?_, ?_⟩, ?_, fun g => ?_, ?_⟩
  · have h1 := congrArg (E.jD W.one) hxy
    simp only at h1
    rw [E.jD_smul, E.jD_smul, hje, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h1
    exact GlobalTheory.EtaleExact.ioE_injective E
      (GlobalTheory.Cyc.Decomp.tmul_gen_cancel hO W.one u hu huT e₀ h₀ _ _ h1)
  · have htop : Submodule.span W.EE {c • e₁} = ⊤ := by
      refine GlobalTheory.EtaleExact.eq_top_DD E hm W.one _ ?_
      rw [eq_top_iff]
      rintro z -
      have h1 : ((1 : RW) ⊗ₜ[O] e₀ : TW RW W.one) ∈ Submodule.span RW
          (E.jD W.one '' (Submodule.span W.EE {c • e₁} : Submodule W.EE (W.DD W.one))) :=
        Submodule.subset_span ⟨c • e₁, Submodule.mem_span_singleton_self _, hje⟩
      induction z using TensorProduct.induction_on with
      | zero => exact Submodule.zero_mem _
      | add a b ha hb => exact Submodule.add_mem _ ha hb
      | tmul r t =>
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1
          (h₀ ▸ Submodule.mem_top : t ∈ Submodule.span O {e₀})
        have h2 : (r ⊗ₜ[O] (a • e₀) : TW RW W.one) = (a • r) • ((1 : RW) ⊗ₜ[O] e₀) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
        rw [h2]
        exact Submodule.smul_mem _ _ h1
    intro z
    exact Submodule.mem_span_singleton.1 (htop ▸ Submodule.mem_top : z ∈ Submodule.span W.EE {c • e₁})
  · apply E.jD_inj
    rw [E.jD_φ, hje]
    simp [TWmap]
  · obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    have hact : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g e₀)
    rw [E.jD_act, hje]
    simp [TWact, hact]
  · rw [hN]
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨algebraMap O (LetA O n) d, by rw [algebraMap_smul, hde]⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨algebraMap O (LetA O n) c, by rw [algebraMap_smul]⟩

end Generic

theorem unitPart : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H), GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitPart l P AI H F := by
  intro l _ P AI H F K s LL h
  haveI := GlobalTheory.EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  have hp : (P.PD K).p = l := P.PD_p K
  refine unitFor_of_tie Subtype.val_injective _
    (GlobalTheory.EtaleExact.map_ne_top_of_tie (F.E K s LL h).tie ?_ ?_)
  · rw [hp]
    exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL
  · rw [hp]
    exact GlobalTheory.EtaleExact.sep_RW LL

end GlobalTheory.WachUnit
