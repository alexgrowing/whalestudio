import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedRankEqFinrank
import Formalism.LocalToGlobal.GlobalTheory.GL6.RamifiedMaxSlopeLe
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClearDenominatorsLattice

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions NumberField Matrix

theorem exists_integer_smul_mem_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (x : V) :
    ∃ r : 𝓞 K, r ≠ 0 ∧ r • x ∈ L :=
  _root_.UpperTheory.Reformulated.B.ClearDenominatorsLattice.exists_integer_smul_mem_of_span_top L hL x

variable (D : D7) (u : D.what₂.Word)

theorem norm_preserves_rational_form (v : (D.mem u).A.vT) (x : ((D.fm u).lat 0).V) :
    ∃ y, (D.fm u).emb 0 y = (D.mem u).A.Nm v ((D.fm u).emb 0 x) := by
  have hL : ∀ x ∈ ((D.fm u).lat 0).L, ∃ y, (D.fm u).emb 0 y = (D.mem u).A.Nm v ((D.fm u).emb 0 x) := by
    intro x hx
    choose ys _ hys using fun a => (D.fm u).rhoT_lat v a x hx
    refine ⟨∑ a, ys a, ?_⟩
    rw [map_sum]
    unfold ColumnsAtT.Nm
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun a _ => hys a
  obtain ⟨r, hr, hrx⟩ := exists_integer_smul_mem_of_span_top ((D.fm u).lat 0).L ((D.fm u).lat_good 0).2.2 x
  obtain ⟨y, hy⟩ := hL _ hrx
  have hrK : (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.what₂.LL) D.what₂.LL)]; exact hr
  refine ⟨(algebraMap (𝓞 D.what₂.LL) D.what₂.LL r)⁻¹ • y, ?_⟩
  rw [LinearMap.map_smulₛₗ, hy, ← algebraMap_smul D.what₂.LL r x, LinearMap.map_smulₛₗ, map_smul, smul_smul,
    ← map_mul, inv_mul_cancel₀ hrK, map_one, one_smul]

theorem ramified_rational_ne_bot (h : (D.mem u).A.Mram ≠ ⊥) : (D.fm u).ramSub ≠ ⊥ := by
  classical
  choose yv hyv using fun v j => norm_preserves_rational_form D u v (((D.fm u).lat 0).b j)
  let A : Matrix ((D.mem u).A.vT × ((D.fm u).lat 0).ι) ((D.fm u).lat 0).ι D.what₂.LL :=
    fun p j => ((D.fm u).lat 0).b.repr (yv p.1 j) p.2
  have hE : ∀ x : ((D.fm u).lat 0).V, (D.fm u).emb 0 x =
      ∑ i, D.what₂.embLL (((D.fm u).lat 0).b.repr x i) • (D.fm u).emb 0 (((D.fm u).lat 0).b i) := by
    intro x
    conv_lhs => rw [← ((D.fm u).lat 0).b.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ _ _ _
  have key : ∀ (v : (D.mem u).A.vT) (c : ((D.fm u).lat 0).ι → ℂ),
      (D.mem u).A.Nm v (∑ j, c j • (D.fm u).emb 0 (((D.fm u).lat 0).b j)) =
        ∑ i, ((A.map D.what₂.embLL) *ᵥ c) (v, i) • (D.fm u).emb 0 (((D.fm u).lat 0).b i) := by
    intro v c
    rw [map_sum]
    have hj : ∀ j, (D.mem u).A.Nm v (c j • (D.fm u).emb 0 (((D.fm u).lat 0).b j)) =
        c j • ∑ i, D.what₂.embLL (((D.fm u).lat 0).b.repr (yv v j) i) • (D.fm u).emb 0 (((D.fm u).lat 0).b i) := by
      intro j; rw [map_smul, ← hyv, ← hE (yv v j)]
    rw [Finset.sum_congr rfl fun j _ => hj j]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hli := ((D.fm u).emb_basis 0).1
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hzMu : z ∈ (D.mem u).A.Mu0 := hz.1
  rw [← (D.fm u).Fi_zero, ← ((D.fm u).emb_basis 0).2] at hzMu
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hzMu
  have hc0 : c ≠ 0 := by
    rintro rfl; apply hz0; rw [← hc]; simp
  have hAc : (A.map D.what₂.embLL) *ᵥ c = 0 := by
    funext p
    obtain ⟨v, i⟩ := p
    have hv : (D.mem u).A.Nm v z = 0 := by
      have : z ∈ ⨅ v, LinearMap.ker ((D.mem u).A.Nm v) := hz.2
      rw [Submodule.mem_iInf] at this; exact this v
    rw [← hc, key] at hv
    exact (Fintype.linearIndependent_iff.1 hli) _ hv i
  have hx : ∃ x : ((D.fm u).lat 0).ι → D.what₂.LL, x ≠ 0 ∧ A *ᵥ x = 0 := by
    by_contra hne
    push Not at hne
    have hker : LinearMap.ker A.mulVecLin = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx; by_contra hx0; exact hne x hx0 hx
    obtain ⟨g, hg⟩ := A.mulVecLin.exists_leftInverse_of_injective hker
    have hBA : LinearMap.toMatrix' g * A = 1 := by
      have h1 := congrArg LinearMap.toMatrix' hg
      rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h1
    have hBA' : (LinearMap.toMatrix' g).map D.what₂.embLL * A.map D.what₂.embLL = 1 := by
      rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero _) (map_one _)]
    apply hc0
    rw [← Matrix.one_mulVec c, ← hBA', ← Matrix.mulVec_mulVec, hAc, Matrix.mulVec_zero]
  obtain ⟨x, hx0, hAx⟩ := hx
  have hX0 : ∑ j, x j • ((D.fm u).lat 0).b j ≠ 0 := by
    intro h0
    exact hx0 (funext fun j => (Fintype.linearIndependent_iff.1 ((D.fm u).lat 0).b.linearIndependent) x h0 j)
  have hEX : (D.fm u).emb 0 (∑ j, x j • ((D.fm u).lat 0).b j) =
      ∑ j, (D.what₂.embLL ∘ x) j • (D.fm u).emb 0 (((D.fm u).lat 0).b j) := by
    rw [map_sum]; exact Finset.sum_congr rfl fun j _ => LinearMap.map_smulₛₗ _ _ _
  refine Submodule.ne_bot_iff _ |>.2 ⟨_, ?_, hX0⟩
  show (D.fm u).emb 0 (∑ j, x j • ((D.fm u).lat 0).b j) ∈ (D.mem u).A.Mram
  rw [hEX]
  refine ⟨?_, ?_⟩
  · rw [← (D.fm u).Fi_zero, ← ((D.fm u).emb_basis 0).2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · show _ ∈ ⨅ v, LinearMap.ker ((D.mem u).A.Nm v)
    rw [Submodule.mem_iInf]
    intro v
    rw [LinearMap.mem_ker, key]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ((A.map D.what₂.embLL) *ᵥ (D.what₂.embLL ∘ x)) (v, i) = 0 := by
      rw [← RingHom.map_mulVec, hAx, Pi.zero_apply, map_zero]
    rw [this, zero_smul]

theorem ramified_lattice_ne_bot (h : (D.mem u).A.Mram ≠ ⊥) : (D.fm u).ramL ≠ ⊥ := by
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (ramified_rational_ne_bot D u h)
  obtain ⟨r, hr, hrX⟩ := exists_integer_smul_mem_of_span_top ((D.fm u).lat 0).L ((D.fm u).lat_good 0).2.2 X
  have hrK : (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.what₂.LL) D.what₂.LL)]; exact hr
  refine Submodule.ne_bot_iff _ |>.2 ⟨r • X, ⟨hrX, ?_⟩, ?_⟩
  · show r • X ∈ (D.fm u).ramSub
    rw [← algebraMap_smul D.what₂.LL r X]
    exact (D.fm u).ramSub.smul_mem _ hX
  · rw [← algebraMap_smul D.what₂.LL r X]
    exact smul_ne_zero hrK hX0

theorem ramified_forms_ne_bot (M : FreeRankModel (D.mem u).A) (hT : 3 ≤ (D.mem u).A.T) (hd : 0 < D.duS u) :
    (D.mem u).A.Mram ≠ ⊥ := by
  intro h0
  have hdu : (D.mem u).A.du = 0 := by
    unfold ColumnsAtT.du; rw [h0, finrank_bot]
  have h := ramified_rank_mul (D.mem u).A M
  rw [hdu, zero_mul] at h
  have hpos : 0 < (D.duS u) * ((D.mem u).A.T - 2) ^ D.R.f := Nat.mul_pos hd (Nat.pow_pos (by omega))
  unfold D7.duS at hpos
  omega

theorem ramified_max_slope_le_of_model (M : FreeRankModel (D.mem u).A) (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (hd : 0 < D.duS u) :
    (D.fm u).ramLat.muMax ≤ ((D.fm u).lat 0).muMax := by
  have hT : 3 ≤ (D.mem u).A.T := by
    have h1 : 1 ≤ D.R.f := by
      have h0 : 0 < D.R.n := D.R.toFrame.ord_pos
      have hf : D.R.f = 2 * D.R.n := rfl
      omega
    have h2 : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := D.R.m_add_three_le_k; omega
    have h3 : 1 ≤ D.R.f * D.R.N D.R.m := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    have := hS.1
    have h4 : 2 * D.R.f * D.R.N D.R.m = 2 * (D.R.f * D.R.N D.R.m) := by ring
    omega
  exact ramified_max_slope_le D u (ramified_lattice_ne_bot D u (ramified_forms_ne_bot D u M hT hd))

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
