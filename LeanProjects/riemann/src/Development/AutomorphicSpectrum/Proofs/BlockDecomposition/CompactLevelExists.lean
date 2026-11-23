import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBallSubset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSat2InvTConj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsNormalisedOfDualIsConj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIntegralIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockInverseIntegralIff

noncomputable section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open GlobalTheory.PrincCong (congSub mem_congSub_iff isOpen_congSub exists_mat_subset)
open GlobalTheory.LFun.ConjPlace (invT invT_val mem_iff_invT map_mem_Ov_iff)
open GlobalTheory.ThetaSatake (cw cloc)
open GlobalTheory.CompanionTheory.ThetaSatPair (embT_cw invT_symm)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.KExLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_le_KGL (w : Pl E) (n k : ℕ) : congSub w n k ≤ KGL w n :=
  fun g hg => ((mem_congSub_iff w n k g).1 hg).1

theorem eventually_congSub_le (w : Pl E) (a : ℕ) (U : Subgroup (GLw a w)) (hU : IsOpen (U : Set (GLw a w))) :
    ∀ᶠ k in atTop, congSub w a k ≤ U := by
  have hVn : (U : Set (GLw a w)) ∈ 𝓝 (1 : GLw a w) := hU.mem_nhds U.one_mem
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap] at hVn
  obtain ⟨t, htn, htV⟩ := Filter.mem_comap.1 hVn
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 htn
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨N₀, hN₀⟩ := exists_mat_subset w a (Filter.inter_mem hA hB')
  filter_upwards [eventually_ge_atTop N₀] with m hm γ hγ
  have a1 := hN₀ m hm _ ((mem_congSub_iff w a _ _).1 hγ).2
  have a2 := hN₀ m hm _ ((mem_congSub_iff w a _ _).1 (inv_mem hγ)).2
  exact htV (hAB ⟨a1.1, a2.2⟩)

theorem continuous_detGL (w : Pl E) (a : ℕ) :
    Continuous (GeneralLinearGroup.det : GLw a w → (w.adicCompletion E)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_det Units.continuous_val
  · have e : (fun g : GLw a w => (((GeneralLinearGroup.det g)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E)) =
        fun g => ((g⁻¹ : GLw a w) : Matrix (Fin a) (Fin a) _).det := by
      funext g
      rw [← map_inv]
      rfl
    exact e ▸ Continuous.matrix_det (Units.continuous_val.comp continuous_inv)

theorem eventually_det (w : Pl E) (a : ℕ) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : IsOpen (μ.ker : Set (w.adicCompletion E)ˣ)) :
    ∀ᶠ k in atTop, ∀ g ∈ congSub w a k, μ (GeneralLinearGroup.det g) = 1 := by
  have hU : IsOpen ((μ.ker.comap GeneralLinearGroup.det : Subgroup (GLw a w)) : Set (GLw a w)) :=
    hμ.preimage (continuous_detGL w a)
  filter_upwards [eventually_congSub_le w a _ hU] with k hk g hg
  exact hk hg

theorem isCompact_congSub (w : Pl E) (n k : ℕ) : IsCompact (congSub w n k : Set (GLw n w)) :=
  (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_congSub w n k)) (congSub_le_KGL w n k)

theorem blocks_mem_congSub {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) {k : ℕ} (hg : blk h w m X ∈ congSub w n k) :
    m.1 ∈ congSub w a k ∧ m.2 ∈ congSub w b k := by
  obtain ⟨hK, hc⟩ := (mem_congSub_iff w n k _).1 hg
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hK
  have v := GlobalTheory.CompanionTheory.CtS.blk_val_eq h w m X
  have iv := GlobalTheory.CompanionTheory.CtS.blk_inv_val h w m X
  let e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h)
  have v11 : ∀ i j, (blk h w m X).val (e (Sum.inl i)) (e (Sum.inl j)) = m.1.val i j := fun i j => by
    rw [v]; simp [e, reindex_apply, submatrix_apply]
  have v22 : ∀ i j, (blk h w m X).val (e (Sum.inr i)) (e (Sum.inr j)) = m.2.val i j := fun i j => by
    rw [v]; simp [e, reindex_apply, submatrix_apply]
  have i11 : ∀ i j, ((blk h w m X)⁻¹).val (e (Sum.inl i)) (e (Sum.inl j)) = (m.1⁻¹).val i j := fun i j => by
    rw [iv]; simp [e, reindex_apply, submatrix_apply]
  have i22 : ∀ i j, ((blk h w m X)⁻¹).val (e (Sum.inr i)) (e (Sum.inr j)) = (m.2⁻¹).val i j := fun i j => by
    rw [iv]; simp [e, reindex_apply, submatrix_apply]
  have o11 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (e (Sum.inl i)) (e (Sum.inl j)) =
      (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := fun i j => by
    simp [Matrix.one_apply, e.injective.eq_iff]
  have o22 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (e (Sum.inr i)) (e (Sum.inr j)) =
      (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j := fun i j => by
    simp [Matrix.one_apply, e.injective.eq_iff]
  refine ⟨(mem_congSub_iff w a k _).2 ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩,
    (mem_congSub_iff w b k _).2 ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩⟩
  · rw [← v11]; exact h1 _ _
  · rw [← i11]; exact h2 _ _
  · rw [← v11, ← o11]; exact hc _ _
  · rw [← v22]; exact h1 _ _
  · rw [← i22]; exact h2 _ _
  · rw [← v22, ← o22]; exact hc _ _

theorem conj_mem_congSub (w : Pl E) (n k : ℕ) {x g : GLw n w} (hx : x ∈ KGL w n) (hg : g ∈ congSub w n k) :
    x * g * x⁻¹ ∈ congSub w n k := by
  obtain ⟨y, hy, rfl⟩ := hg
  obtain ⟨z, rfl⟩ := hx
  exact ⟨z * y * z⁻¹, (MonoidHom.normal_ker _).conj_mem y hy z, by simp only [map_mul, map_inv]⟩

theorem invT_mem_congSub {u w : Pl E} (c : u.adicCompletion E ≃+* w.adicCompletion E)
    (hc : ∀ x, Valued.v (c x) = Valued.v x) (a k : ℕ) {g : GLw a u} (hg : g ∈ congSub u a k) :
    invT c a g ∈ congSub w a k := by
  have h1 := (mem_congSub_iff u a k _).1 hg
  have h2 := (mem_congSub_iff u a k _).1 (inv_mem hg)
  refine (mem_congSub_iff w a k _).2 ⟨(mem_iff_invT c (map_mem_Ov_iff c hc) g).1 h1.1, fun i j => ?_⟩
  have e : (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j =
      c ((1 : Matrix (Fin a) (Fin a) (u.adicCompletion E)) j i) := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  rw [invT_val, e, ← map_sub, hc]
  exact h2.2 j i

theorem under_cw (w : Pl E) :
    (cw w).under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) :=
  ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) (cw w) w).2
    (Or.inr (conjPl_conjSrc _ w))).symm

end GlobalTheory.CompanionTheory.KExLevel

namespace GlobalTheory.CompanionTheory.KExLevel

theorem kEx : KEx := by
  intro E _ _ _ n Sec _ R _ μ hμ L hL
  let T : Finset (Pl E) := R ∪ R.image cw
  have A : ∀ a ∈ Finset.range (n + 1), ∀ w ∈ R, ∀ᶠ k in atTop, ∀ m : GLw a w × GLw (n - a) w,
      m.1 ∈ congSub w a k → m.2 ∈ congSub w (n - a) k → m ∈ L a w := by
    intro a ha w hw
    obtain ⟨L₁, L₂, e, l1, l2⟩ := hL a (Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)) w hw
    filter_upwards [eventually_congSub_le w a L₁ l1.1, eventually_congSub_le w (n - a) L₂ l2.1] with k h1 h2 m m1 m2
    rw [e]
    exact ⟨h1 m1, h2 m2⟩
  have B : ∀ a ∈ Finset.range (n + 1), ∀ w ∈ T, ∀ᶠ k in atTop, ∀ m : GLw a w × GLw (n - a) w,
      m.1 ∈ congSub w a k → m.2 ∈ congSub w (n - a) k →
        μ w (GeneralLinearGroup.det m.1 ^ (n - a) * GeneralLinearGroup.det m.2 ^ a) = 1 := by
    intro a _ w _
    filter_upwards [eventually_det w a (μ w) (hμ w), eventually_det w (n - a) (μ w) (hμ w)] with k h1 h2 m m1 m2
    rw [map_mul, map_pow, map_pow, h1 _ m1, h2 _ m2, one_pow, one_pow, one_mul]
  obtain ⟨M, hA, hB⟩ := (((Filter.eventually_all_finset _).2 fun a ha =>
    (Filter.eventually_all_finset _).2 (A a ha)).and ((Filter.eventually_all_finset _).2 fun a ha =>
    (Filter.eventually_all_finset _).2 (B a ha))).exists
  have hT : ∀ w, w ∈ T → (if w ∈ T then congSub w n M else KGL w n) = congSub w n M := fun w hw => if_pos hw
  refine ⟨fun w => if w ∈ T then congSub w n M else KGL w n, ⟨fun w => ?_, ?_⟩, fun w => ?_, fun w hw => ?_,
    fun a ha w hw m X hm => ?_, fun a ha w hw hs u hc m X hm => ?_⟩
  · by_cases h : w ∈ T
    · simp only [if_pos h]; exact isOpen_congSub w n M
    · simp only [if_neg h]; exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1
  · refine Filter.eventually_cofinite.2 (T.finite_toSet.subset fun w hw => ?_)
    by_contra h
    refine hw ?_
    have h' : w ∉ T := h
    simp only [if_neg h']
    exact le_rfl
  · by_cases h : w ∈ T
    · simp only [if_pos h]; exact isCompact_congSub w n M
    · simp only [if_neg h]; exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  · refine if_neg fun h => ?_
    rcases Finset.mem_union.1 h with h | h
    · exact hw w h rfl
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 h
      exact hw r hr (under_cw r).symm
  · have hwT : w ∈ T := Finset.mem_union_left _ hw
    have ha' : a ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_iff.2 ha)
    simp only [if_pos hwT] at hm
    obtain ⟨b1, b2⟩ := blocks_mem_congSub _ w m X hm
    exact ⟨hA a ha' w hw m b1 b2, hB a ha' w hwT m b1 b2⟩
  · have hu : u = cw w := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hc
    have huT : u ∈ T := Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, hw, hu.symm⟩)
    have hw' : w = cw u := by rw [hu]; exact (GlobalTheory.ThetaPull.conjSrc_conjSrc w).symm
    have ha' : a ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_iff.2 ha)
    simp only [if_pos huT] at hm
    obtain ⟨b1, b2⟩ := blocks_mem_congSub _ u m X hm
    clear hu hc
    subst hw'
    have hv : ∀ x, Valued.v ((cloc u).symm x) = Valued.v x := fun x => by
      have := (GlobalTheory.CuspRep.conjLoc_spec (IsCMField.complexConj E).toRingEquiv u).2.2 ((cloc u).symm x)
      have e : GlobalTheory.CuspRep.conjLoc (IsCMField.complexConj E).toRingEquiv u ((cloc u).symm x) = x :=
        (cloc u).apply_symm_apply x
      rw [e] at this
      exact this.symm
    let p : ∀ c : ℕ, GLw c u → GLw c (cw u) := fun c g =>
      (invT (cloc u) c).symm ((PhiU c (u.adicCompletion E))⁻¹ * g * PhiU c (u.adicCompletion E))
    have hp : ∀ c (g : GLw c u), g ∈ congSub u c M → p c g ∈ congSub (cw u) c M := fun c g hg => by
      have hk : (PhiU c (u.adicCompletion E))⁻¹ ∈ KGL u c := inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ c)
      have h1 := conj_mem_congSub u c M hk hg
      rw [inv_inv] at h1
      change (invT (cloc u) c).symm _ ∈ _
      rw [invT_symm]
      exact invT_mem_congSub (cloc u).symm hv c M h1
    have he : ∀ c (g : GLw c u), embW c u g = embT c (cw u) (p c g) := fun c g => by
      rw [embT_cw]
      simp only [p, MulEquiv.apply_symm_apply]
      congr 1
      group
    exact ⟨hB a ha' u huT m b1 b2, (p a m.1, p (n - a) m.2), hA a ha' (cw u) hw _ (hp _ _ b1) (hp _ _ b2),
      he _ _, he _ _⟩

end GlobalTheory.CompanionTheory.KExLevel

end
