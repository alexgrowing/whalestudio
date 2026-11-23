import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDstOfIsSstStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisPhiFixedAddFinrankMonLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableCocycleOfFrobeniusMonodromyPairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAddLeFinrankRangeAddOfComapLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonVEqZeroIffExistsCrisInclStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryDeRhamOfCoboundarySemistableStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

noncomputable def stPairs {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {V : Type} [AddCommGroup V]
    [Module ℚ_[l] V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) : Submodule ℚ_[l] ((↥(GK K) → V) × (V ⊗[ℚ_[l]] Bst P)) where
  carrier := {p | p.1 ∈ continuousCocycles ρ ∧ ∀ g, p.1 g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g p.2 - p.2}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, hx⟩ ⟨hb, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, fun g => ?_⟩
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_tmul, hx, hy, map_add]
    abel
  smul_mem' := by
    rintro c a ⟨ha, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, fun g => ?_⟩
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

theorem exists_stCocycles_lower : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v : V, Continuous fun g => ρ g v) → IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → Module.Finite ℚ_[l] ↥(continuousCocycles ρ) → ∃ S : Submodule ℚ_[l] (↥(GK K) → V), finiteCocycles (P.PD K) ρ ≤ S ∧ S ≤ continuousCocycles ρ ∧ (∀ c ∈ S, ∃ z : V ⊗[ℚ_[l]] Bst P, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ (∀ c ∈ S, ∃ b : V ⊗[ℚ_[l]] P.R.BdR, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) ρ g b - b) ∧ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) ≤ finrank ℚ_[l] ↥S := by
  intro l _ P AI T K V _ _ _ _ _ _ _ V' _ _ _ ρ ρ' m hc hd hs hfin
  let π : ↥(stPairs P ρ) →ₗ[ℚ_[l]] (↥(GK K) → V) := (LinearMap.fst _ _ _).comp (stPairs P ρ).subtype
  let ν : ↥(stPairs P ρ) →ₗ[ℚ_[l]] (V ⊗[ℚ_[l]] Bst P) :=
    (monV P ℚ_[l] V).comp ((LinearMap.snd _ _ _).comp (stPairs P ρ).subtype)
  have hcris : ∀ (c : ↥(GK K) → V) (x : V ⊗[ℚ_[l]] P.R.B),
      (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) ρ g x - x) →
      ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g (crisIncl P ℚ_[l] V x) - crisIncl P ℚ_[l] V x := by
    intro c x hx g
    rw [stRep_crisIncl, ← map_sub, ← hx, crisIncl_tmul, map_one]
  have h1 : finiteCocycles (P.PD K) ρ ≤ LinearMap.range π := by
    rintro c ⟨hc1, x, hx⟩
    exact ⟨⟨(c, crisIncl P ℚ_[l] V x), hc1, hcris c x hx⟩, rfl⟩
  have h2 : LinearMap.range π ≤ continuousCocycles ρ := by
    rintro _ ⟨e, rfl⟩
    exact e.2.1
  have h3 : ∀ c ∈ LinearMap.range π, ∃ z : V ⊗[ℚ_[l]] Bst P,
      ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z := by
    rintro _ ⟨e, rfl⟩
    exact ⟨e.1.2, e.2.2⟩
  refine ⟨LinearMap.range π, h1, h2, h3, fun c hc => ?_, ?_⟩
  · obtain ⟨z, hz⟩ := h3 c hc
    exact GlobalTheory.T.coboundary_deRham_of_coboundary_semistable l P AI T K V ρ c z hz
  have hφ : ∀ y ∈ Dst P ρ, phiV P ℚ_[l] V y ∈ Dst P ρ := fun y hy =>
    (mem_Dst P ρ).mpr fun g => by
      rw [← End.mul_apply, ← phiV_stRep, End.mul_apply, (mem_Dst P ρ).mp hy g]
  have hN : ∀ y ∈ Dst P ρ, monV P ℚ_[l] V y ∈ Dst P ρ := fun y hy =>
    (mem_Dst P ρ).mpr fun g => by
      rw [← End.mul_apply, ← monV_stRep, End.mul_apply, (mem_Dst P ρ).mp hy g]
  haveI := GlobalTheory.T.finiteDimensional_Dst_of_isSst' l P K V ρ hs
  haveI : FiniteDimensional ℚ_[l] ↥(LinearMap.range π) := Submodule.finiteDimensional_of_le h2
  haveI : FiniteDimensional ℚ_[l] ↥(Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap
      ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) := Submodule.finiteDimensional_of_le inf_le_left
  have h4 := GlobalTheory.T.finrank_add_finrank_le_finrank_range_add_finrank ℚ_[l] _ _ _ π ν (finiteCocycles (P.PD K) ρ) ((Dst P ρ).map (monV P ℚ_[l] V))
    (Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) h1
    (by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨hN y hy, phiV P ℚ_[l] V y - y, Submodule.sub_mem _ (hφ y hy) hy, ?_⟩
      rw [map_sub, ← End.mul_apply, monV_phiV]
      rfl)
    (by
      rintro x ⟨hx, y, hy, hxy⟩
      obtain ⟨z, c, hc1, hc2, hz⟩ := GlobalTheory.T.semistable_cocycle_of_frobenius_monodromy_pair l P AI T K V ρ hc x hx y hy hxy.symm
      exact ⟨⟨(c, z), hc1, hc2⟩, hz⟩)
    (by
      rintro e ⟨-, x, hx⟩
      refine ⟨e.1.2 - crisIncl P ℚ_[l] V x, (mem_Dst P ρ).mpr fun g => ?_, ?_⟩
      · have := (e.2.2 g).symm.trans (hcris _ x hx g)
        rw [map_sub, sub_eq_sub_iff_sub_eq_sub]
        exact this
      · rw [map_sub, (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V _).mpr ⟨x, rfl⟩, sub_zero]
        rfl)
  have h5 := GlobalTheory.T.finrank_dcris_phi_fixed_add_finrank_mon_le_alt l P AI T K V V' ρ ρ' m hd hs
  omega

end GlobalTheory.PMon
