import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiltrationAdaptedBasisOfSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisOfIsDeRhamLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilteredComparisonCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFiltrationBoundsInvariantCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeStructureOfAdaptedInvariantFamilyStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.HodgeEx

theorem exists_hodge : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) → ∃ H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K, ∀ N : ℕ, (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) → ∀ i, |(H.p i : ℤ) - H.q| ≤ N := by
  intro l _ K P AI T C hC ξ hξ d ρ hDR
  set M : ↥(GK K) → Matrix (Fin d) (Fin d) P.R.BdR :=
    fun g => (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) with hM
  have hKact : ∀ (g : ↥(GK K)) (k : ↥K.1) (v : P.R.BdR),
      P.actQdR (g : GQ l) (algebraMap ↥K.1 P.R.BdR k * v) = algebraMap ↥K.1 P.R.BdR k * P.actQdR (g : GQ l) v := by
    intro g k v
    rw [← P.PD_actdR, ← P.PD_actdR, map_mul, AlgEquiv.commutes]
  let Iv : Submodule ↥K.1 (Fin d → P.R.BdR) :=
    { carrier := {c | ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c}
      add_mem' := by
        intro u v hu hv g
        simp only [Set.mem_setOf_eq] at hu hv ⊢
        have : (fun i => P.actQdR (g : GQ l) ((u + v) i)) =
            (fun i => P.actQdR (g : GQ l) (u i)) + (fun i => P.actQdR (g : GQ l) (v i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add, hu g, hv g]
      zero_mem' := by
        intro g
        simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      smul_mem' := by
        intro k u hu g
        simp only [Set.mem_setOf_eq] at hu ⊢
        have : (fun i => P.actQdR (g : GQ l) ((k • u) i)) = k • (fun i => P.actQdR (g : GQ l) (u i)) := by
          funext i; simp only [Pi.smul_apply, Algebra.smul_def, hKact]
        rw [this, Matrix.mulVec_smul, hu g] }
  have hmemIv : ∀ c, c ∈ Iv ↔ ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c := fun c => Iff.rfl
  obtain ⟨x, hxli, hxinv, hxspan⟩ := GlobalTheory.T.exists_invariant_basis_of_isDeRham_lattice l P AI T K d ρ hDR
  set D : Submodule ↥K.1 (Fin d → P.R.BdR) := Submodule.span ↥K.1 (Set.range x) with hD
  have hDIv : D ≤ Iv := Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (hmemIv _).2 (hxinv j))
  have hIvD : ∀ c, c ∈ Iv → c ∈ D := fun c hc => hxspan c hc
  haveI : FiniteDimensional ↥K.1 D := FiniteDimensional.span_of_finite ↥K.1 (Set.finite_range x)
  have hfr : Module.finrank ↥K.1 D = d := by
    rw [hD, finrank_span_eq_card hxli, Fintype.card_fin]
  let F : ℤ → Submodule ↥K.1 (Fin d → P.R.BdR) := fun a => Submodule.pi Set.univ (fun _ => (P.PD K).Fil a)
  have hmemF : ∀ a v, v ∈ F a ↔ ∀ i, v i ∈ (P.PD K).Fil a := fun a v => by
    simp [F, Submodule.mem_pi]
  have hFil : Antitone (P.PD K).Fil := antitone_int_of_succ_le (P.PD K).Fil_anti
  have hF : Antitone F := fun a b hab v hv => (hmemF _ _).2 fun i => hFil hab ((hmemF _ _).1 hv i)
  have hex : ∀ v ∈ D, ∃ a, v ∈ F a := by
    intro v _
    choose a ha using fun i => (P.PD K).Fil_exh (v i)
    refine ⟨-∑ i, |a i|, (hmemF _ _).2 fun i => hFil ?_ (ha i)⟩
    have h1 : |a i| ≤ ∑ j, |a j| := Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := neg_abs_le (a i)
    linarith
  have hsep : ∀ v ∈ D, (∀ a, v ∈ F a) → v = 0 := fun v _ hv =>
    funext fun i => (P.PD K).Fil_sep (v i) fun a => (hmemF a v).1 (hv a) i
  obtain ⟨b0, h0, hbF0, hbrep0⟩ := GlobalTheory.T.exists_filtration_adapted_basis_of_subspace D F hF hex hsep
  set e := finCongr hfr
  set b := b0.reindex e with hb
  set h : Fin d → ℤ := fun j => h0 (e.symm j) with hh
  have hbF : ∀ j, (b j : Fin d → P.R.BdR) ∈ F (h j) ∧ (b j : Fin d → P.R.BdR) ∉ F (h j + 1) := fun j => by
    rw [hb, Module.Basis.reindex_apply]; exact hbF0 _
  have hbrep : ∀ (a : ℤ) (v : D), (v : Fin d → P.R.BdR) ∈ F a → ∀ j, b.repr v j ≠ 0 → a ≤ h j := by
    intro a v hv j hj
    rw [hb, Module.Basis.repr_reindex_apply] at hj
    exact hbrep0 a v hv _ hj
  have hbinv : ∀ j (g : ↥(GK K)), M g *ᵥ (fun i => P.actQdR (g : GQ l) ((b j : Fin d → P.R.BdR) i)) = (b j : Fin d → P.R.BdR) :=
    fun j => (hmemIv _).1 (hDIv (b j).2)
  have hspan : ∀ y : Fin d → P.R.BdR, (∀ i, y i ∈ (P.PD K).Fil 0) →
      ∃ c : Fin d → P.R.BdR, (∀ j, c j ∈ (P.PD K).Fil (-h j)) ∧ y = ∑ j, c j • (b j : Fin d → P.R.BdR) := by
    intro y hy
    obtain ⟨m, k, bb, z, hz, rfl⟩ := GlobalTheory.T.deRham_filtered_comparison_coordinates l P AI T K d ρ hDR 0 y hy
    have hzD : ∀ r, z r ∈ D := fun r => hIvD _ ((hmemIv _).2 (hz r).1)
    let cf : Fin m → Fin d → ↥K.1 := fun r j => b.repr ⟨z r, hzD r⟩ j
    refine ⟨fun j => ∑ r, cf r j • bb r, fun j => ?_, ?_⟩
    · refine Submodule.sum_mem _ fun r _ => ?_
      by_cases hc : cf r j = 0
      · rw [hc, zero_smul]; exact zero_mem _
      · have hkr := hbrep (k r) ⟨z r, hzD r⟩ ((hmemF _ _).2 (hz r).2.1) j hc
        refine Submodule.smul_mem _ _ (hFil ?_ (hz r).2.2)
        linarith
    · have hexp : ∀ r, z r = ∑ j, cf r j • (b j : Fin d → P.R.BdR) := fun r => by
        have := congrArg Subtype.val (b.sum_repr ⟨z r, hzD r⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      conv_lhs => enter [2, r]; rw [hexp r]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => ?_
      simp only [Algebra.smul_def]
      ring
  obtain ⟨H, hH⟩ := GlobalTheory.T.hodge_structure_of_adapted_invariant_family l K P AI T C hC ξ hξ d ρ (fun j => (b j : Fin d → P.R.BdR)) h hbinv
    (fun j i => (hmemF _ _).1 (hbF j).1 i) hspan
  refine ⟨H, fun N ⟨h1, h2⟩ i => ?_⟩
  rw [hH i]
  have hne : (b i : Fin d → P.R.BdR) ≠ 0 := fun h0' => b.ne_zero i (Subtype.ext h0')
  obtain ⟨hlo, hhi⟩ := GlobalTheory.T.deRham_filtration_bounds_invariant_coordinates l P K d ρ N h1 h2 _ (hbinv i) hne
  rw [abs_le]
  constructor
  · by_contra hlt
    push_neg at hlt
    exact (hbF i).2 (hF (show h i + 1 ≤ -(N : ℤ) by omega) ((hmemF _ _).2 hlo))
  · by_contra hlt
    push_neg at hlt
    exact hhi ((hmemF _ _).1 (hF (show (N : ℤ) + 1 ≤ h i by omega) (hbF i).1))

end GlobalTheory.HodgeEx
