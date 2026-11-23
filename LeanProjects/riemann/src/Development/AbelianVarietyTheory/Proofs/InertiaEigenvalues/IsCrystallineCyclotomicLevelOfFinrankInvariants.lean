import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem finrank_maxUnramified_eq_cyclotomicLevel (K E : FinExt l) (s : ℕ) (hs : 1 ≤ s) (hE : E.1 = Ks K s)
    (hle : K.1 ≤ E.1) : Module.finrank ℚ_[l] ↥(K0 E) = Module.finrank ℚ_[l] ↥(K0 K) := by
  have h0 : K0 K ≤ K0 E := inf_le_inf_right _ hle
  have h1 : Ks E s = Ks K s := by
    apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rw [← hE]
      exact inf_le_left
    · exact sup_le_sup_right h0 _
  have h2 := finrank_Ks E s hs
  rw [h1, finrank_Ks K s hs] at h2
  have hlp : l.Prime := Fact.out
  have hpos : 0 < (l - 1) * l ^ (s - 1) :=
    Nat.mul_pos (Nat.sub_pos_of_lt hlp.one_lt) (pow_pos hlp.pos _)
  exact (Nat.eq_of_mul_eq_mul_right hpos h2).symm

theorem mem_GKs_iff_mem_Gj (P : LocPrime l) (K : FinExt l) (LL : FinExt l) (n : ℕ)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (x : ↥(GK K)) :
    x ∈ W.GKs ↔ (x : GQ l) ∈ Gj K W.s := by
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have hcb := (cyc_basic l P.χQ hχ).2.2 K
  have hK0 : (x : GQ l) ∈ (K0 K).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (inf_le_left : K0 K ≤ K.1) x.2
  rw [W.GKs_def, (hcb x hK0).1 W.s, P.PD_χ, ← DictKs.le_v_iff P LL,
    (algebraMap ℚ_[l] ↥LL.1).map_sub, (algebraMap ℚ_[l] ↥LL.1).map_one]

theorem actVB_inclusion (P : LocPrime l) (K E LL : FinExt l) (hle : K.1 ≤ E.1)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (g : ↥(GK E)) :
    actVB (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) g =
      actVB (P.PD K) T.ρ (Subgroup.inclusion (GK_le hle) g) := by
  unfold actVB
  congr 1
  ext b
  change (P.PD E).actB g b = (P.PD K).actB _ b
  rw [P.PD_actB, P.PD_actB]
  rfl

theorem iInf_ker_eq {R M ι κ : Type} [Ring R] [AddCommGroup M] [Module R M]
    (f : ι → M →ₗ[R] M) (g : κ → M →ₗ[R] M) (h1 : ∀ i, ∃ k, f i = g k) (h2 : ∀ k, ∃ i, f i = g k) :
    ⨅ i, LinearMap.ker (f i) = ⨅ k, LinearMap.ker (g k) := by
  apply le_antisymm
  · refine le_iInf fun k => ?_
    obtain ⟨i, hi⟩ := h2 k
    exact hi ▸ iInf_le _ i
  · refine le_iInf fun i => ?_
    obtain ⟨k, hk⟩ := h1 i
    exact hk ▸ iInf_le _ k

theorem Dcris_eq_iInf (P : LocPrime l) (K E LL : FinExt l) (hle : K.1 ≤ E.1)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (H : Subgroup ↥(GK K))
    (hH : ∀ x : ↥(GK K), x ∈ H ↔ (x : GQ l) ∈ GK E) :
    Dcris (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) =
      ⨅ g : ↥H, LinearMap.ker (actVB (P.PD K) T.ρ (g : ↥(GK K)) -
        (LinearMap.id : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.B)) := by
  unfold Dcris
  apply iInf_ker_eq
  · intro g
    refine ⟨⟨Subgroup.inclusion (GK_le hle) g, (hH _).2 g.2⟩, ?_⟩
    exact congrArg (fun f => f - LinearMap.id) (actVB_inclusion P K E LL hle T g)
  · intro g
    refine ⟨⟨(g : ↥(GK K)), (hH _).1 g.2⟩, ?_⟩
    exact congrArg (fun f => f - LinearMap.id) (actVB_inclusion P K E LL hle T _)

set_option maxHeartbeats 1600000 in

theorem isCrys_Ks_of_finrank : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (n : ℕ) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), W.s = s → ∀ (E : FinExt l), E.1 = Ks K s → ∀ (hle : K.1 ≤ E.1) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), Module.finrank ↥LL.1 ↥(⨅ g : ↥W.GKs, LinearMap.ker (actVB (P.PD K) T.ρ (g : ↥(GK K)) - (LinearMap.id : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.B))) = Module.finrank ℚ_[l] ↥(K0 K) * Module.finrank ↥LL.1 T.V → IsCrys (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) := by
  intro l _ P K s LL n W hs E hE hle T h
  have hG : Gj K W.s = GK E := by
    rw [Gj, hs, ← hE]
    rfl
  have hD := Dcris_eq_iInf P K E LL hle T W.GKs (fun x => by
    rw [mem_GKs_iff_mem_Gj, hG])
  have h1 := finrank_maxUnramified_eq_cyclotomicLevel K E s (hs ▸ W.s_pos) hE hle
  have h2 := congrArg
    (fun D : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.B) => Module.finrank ↥LL.1 ↥D) hD
  rw [← h1] at h
  exact h2.trans h

end GlobalTheory.Cyc
