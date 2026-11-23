import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariablePreservesSqNormOrthogonal
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc.MeanBlocks

variable {D : D7} {n ρ p : ℕ}

abbrev ix (hn : ρ + p = n) : Fin ρ ⊕ Fin p ≃ Fin n := finSumFinEquiv.trans (finCongr hn)

theorem bT_apply (hn : ρ + p = n) (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) (i j : Fin ρ ⊕ Fin p) :
    (bT hn z x y).1 (ix hn i) (ix hn j) = Matrix.fromBlocks z.1 x (adj x) y.1 i j := by
  simp only [bT, bl, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem herm_apply (b : hermA D n) (i j : Fin n) : cA D (b.1 j i) = b.1 i j :=
  congrFun (congrFun (show adj b.1 = b.1 from b.2) i) j

def sub {r : ℕ} (f : Fin r → Fin n) (b : hermA D n) : hermA D r :=
  ⟨b.1.submatrix f f, by
    show adj (b.1.submatrix f f : Mx D r r) = _
    ext i j
    exact herm_apply b (f i) (f j)⟩

def blk (hn : ρ + p = n) : (hermA D p × (Mx D ρ p × hermA D ρ)) ≃ₜ+ hermA D n where
  toFun u := bT hn u.2.2 u.2.1 u.1
  invFun b := (sub (fun i => ix hn (Sum.inr i)) b,
    b.1.submatrix (fun i => ix hn (Sum.inl i)) (fun i => ix hn (Sum.inr i)), sub (fun i => ix hn (Sum.inl i)) b)
  left_inv u := by
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ (Subtype.ext ?_))
    · ext i j
      exact bT_apply hn _ _ _ (Sum.inr i) (Sum.inr j)
    · ext i j
      exact bT_apply hn _ _ _ (Sum.inl i) (Sum.inr j)
    · ext i j
      exact bT_apply hn _ _ _ (Sum.inl i) (Sum.inl j)
  right_inv b := by
    apply Subtype.ext
    ext i j
    obtain ⟨i, rfl⟩ := (ix hn).surjective i
    obtain ⟨j, rfl⟩ := (ix hn).surjective j
    rw [bT_apply]
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · exact herm_apply b _ _
    · rfl
  map_add' u v := by
    apply Subtype.ext
    ext i j
    obtain ⟨i, rfl⟩ := (ix hn).surjective i
    obtain ⟨j, rfl⟩ := (ix hn).surjective j
    rw [AddSubgroup.coe_add, Matrix.add_apply, bT_apply, bT_apply, bT_apply]
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · exact map_add (cA D) _ _
    · rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.matrix_submatrix ?_ _ _
    exact Continuous.matrix_fromBlocks (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
      (continuous_fst.comp continuous_snd)
      (by
        open GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf in
        exact continuous_adj.comp (continuous_fst.comp continuous_snd))
      (continuous_subtype_val.comp continuous_fst)
  continuous_invFun := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
    · exact (continuous_subtype_val.matrix_submatrix _ _).subtype_mk _
    · exact continuous_subtype_val.matrix_submatrix _ _
    · exact (continuous_subtype_val.matrix_submatrix _ _).subtype_mk _

theorem mem_rat_iff {a b : ℕ} (x : Mx D a b) : x ∈ ratMx D a b ↔ ∀ i j, ∃ c, incA D c = x i j := by
  constructor
  · rintro ⟨η, rfl⟩ i j
    exact ⟨η i j, rfl⟩
  · intro h
    choose η hη using h
    exact ⟨Matrix.of η, by ext i j; exact hη i j⟩

theorem blk_rat (hn : ρ + p = n) (u : hermA D p × (Mx D ρ p × hermA D ρ)) :
    blk hn u ∈ ratHerm D n ↔ u ∈ (ratHerm D p).prod ((ratMx D ρ p).prod (ratHerm D ρ)) := by
  show (bT hn u.2.2 u.2.1 u.1).1 ∈ ratMx D n n ↔ u.1.1 ∈ ratMx D p p ∧ u.2.1 ∈ ratMx D ρ p ∧ u.2.2.1 ∈ ratMx D ρ ρ
  simp only [mem_rat_iff]
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · have := h (ix hn (Sum.inr i)) (ix hn (Sum.inr j))
      rwa [bT_apply] at this
    · have := h (ix hn (Sum.inl i)) (ix hn (Sum.inr j))
      rwa [bT_apply] at this
    · have := h (ix hn (Sum.inl i)) (ix hn (Sum.inl j))
      rwa [bT_apply] at this
  · rintro ⟨h1, h2, h3⟩ i j
    obtain ⟨i, rfl⟩ := (ix hn).surjective i
    obtain ⟨j, rfl⟩ := (ix hn).surjective j
    rw [bT_apply]
    rcases i with i | i <;> rcases j with j | j
    · exact h3 i j
    · exact h2 i j
    · obtain ⟨c, hc⟩ := h2 j i
      refine ⟨D.sp.cm.sig c, ?_⟩
      show _ = cA D (u.2.1 j i)
      rw [← hc]
      rfl
    · exact h1 i j

theorem setIntegral_box {A B : Type} [TopologicalSpace A] [TopologicalSpace B] [MeasurableSpace A] [MeasurableSpace B]
    [BorelSpace A] [BorelSpace B] [SecondCountableTopology A] [SecondCountableTopology B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] {s : Set A} {t : Set B} (hs : μ s = 1) (ht : ν t = 1)
    (f : A × B → ℂ) (hf : Continuous f) {C : ℝ} (hC : ∀ u, ‖f u‖ ≤ C) :
    ∫ u in s ×ˢ t, f u ∂(μ.prod ν) = ∫ a in s, ∫ b in t, f (a, b) ∂ν ∂μ := by
  refine setIntegral_prod f (Measure.integrableOn_of_bounded (M := C) ?_ hf.aestronglyMeasurable (.of_forall hC))
  rw [Measure.prod_prod, hs, ht, one_mul]
  exact ENNReal.one_ne_top

end GlobalTheory.CompanionTheory.PcFc.MeanBlocks

open GlobalTheory.CompanionTheory.PcFc.MeanBlocks in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.CompanionTheory.PcFc.mean_blocks : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (m : Meas D ρ p) {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}, IsCovolOneH lam 𝓖 → ∀ {lp : Measure (hermA D p)} {𝓖p : Set (hermA D p)}, IsCovolOneH lp 𝓖p → ∀ Φ : hermA D n → ℂ, Continuous Φ → IsPer Φ → ∫ b in 𝓖, Φ b ∂lam = ∫ y in 𝓖p, ∫ x in m.𝓕, ∫ z in m.𝓖, Φ (bT hn z x y) ∂m.lz ∂m.μ ∂lp := by
  intro D n ρ p hn m lam 𝓖 hl lp 𝓖p hp Φ hΦ hper
  obtain ⟨hl1, hl2, hl3⟩ := hl
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hz1, hz2, hz3⟩ := m.hz
  obtain ⟨hx1, hx2, hx3⟩ := m.hμ
  have lat := fun a b => (open GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf in lattice_Mx D a b)
  haveI : ∀ a b, IsTopologicalAddGroup (Mx D a b) := fun a b => (lat a b).1
  haveI : ∀ a b, LocallyCompactSpace (Mx D a b) := fun a b => (lat a b).2.1
  haveI : ∀ a b, SecondCountableTopology (Mx D a b) := fun a b => (lat a b).2.2.1
  haveI : ∀ a b, T2Space (Mx D a b) := fun a b => (lat a b).2.2.2.1
  haveI : ∀ a b, BorelSpace (Mx D a b) := fun a b => ⟨rfl⟩
  haveI : ∀ r, IsTopologicalAddGroup (hermA D r) := fun r => inferInstance
  haveI : ∀ r, BorelSpace (hermA D r) := fun r => Subtype.borelSpace _
  haveI : ∀ r, SecondCountableTopology (hermA D r) := fun r => Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : ∀ r, T2Space (hermA D r) := fun r => Topology.IsEmbedding.subtypeVal.t2Space
  haveI : ∀ r, LocallyCompactSpace (hermA D r) := fun r => (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := r)).locallyCompactSpace
  have cH : ∀ r, Countable (ratHerm D r) := fun r => by
    haveI : DiscreteTopology (ratHerm D r) := (GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := r)).1
    haveI : SecondCountableTopology (ratHerm D r) := Topology.IsInducing.subtypeVal.secondCountableTopology
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := cH n
  haveI : Countable ((ratHerm D p).prod ((ratMx D ρ p).prod (ratHerm D ρ))) :=
    Function.Injective.countable (f := fun u => (⟨blk hn u.1, (blk_rat hn u.1).2 u.2⟩ : ratHerm D n))
      fun u v h => Subtype.ext ((blk hn).injective (congrArg Subtype.val h))
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := n)).2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.continuousOn
  have hb : ∀ b, ‖Φ b‖ ≤ C := fun b => by
    obtain ⟨γ, hγ, hk⟩ := hcov b
    rw [← hper γ hγ b]
    exact hC _ hk
  haveI : (m.μ.prod m.lz).IsAddHaarMeasure := inferInstance
  haveI : (lp.prod (m.μ.prod m.lz)).IsAddHaarMeasure := inferInstance
  have hin : m.μ.prod m.lz (m.𝓕 ×ˢ m.𝓖) = 1 := by rw [Measure.prod_prod, hx3, hz3, one_mul]
  have hc : Continuous fun u => Φ (blk hn u) := hΦ.comp (blk hn).continuous
  have key := mean_transport _ (ratHerm D n) (blk hn) (blk_rat hn) (lp.prod (m.μ.prod m.lz)) lam
    (GlobalTheory.WeilSliceUnit.isAddFundamentalDomain_prod hp2 (GlobalTheory.WeilSliceUnit.isAddFundamentalDomain_prod hx2 hz2)) hl2
    (by rw [Measure.prod_prod, hp3, hin, one_mul]) hl3 Φ hper
  rw [← key, setIntegral_box lp _ hp3 hin _ hc fun u => hb _]
  refine integral_congr_ae (.of_forall fun y => ?_)
  exact setIntegral_box m.μ m.lz hx3 hz3 (fun v => Φ (blk hn (y, v))) (hc.comp (continuous_const.prodMk continuous_id))
    fun u => hb _
