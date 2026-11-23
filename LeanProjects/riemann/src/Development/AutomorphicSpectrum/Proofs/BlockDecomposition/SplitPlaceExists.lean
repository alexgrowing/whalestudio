import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.IsPairLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBallSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelsEqIntegralGLOfUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLocallyConstant

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.Ex0 PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitLevel

theorem exists_reps {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K K' : Subgroup G)
    (hc : IsCompact (K : Set G)) (ho : IsOpen (K' : Set G)) :
    ∃ X : Finset G, (∀ x ∈ X, x ∈ K) ∧ ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K' := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  have hop : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact ho.preimage continuous_subtype_val
  haveI : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hop
  haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  refine ⟨Finset.univ.image fun q : K ⧸ K'.subgroupOf K => ((q.out : K) : G), ?_, ?_⟩
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    exact q.out.2
  · intro k hk
    let q₀ : K ⧸ K'.subgroupOf K := QuotientGroup.mk ⟨k, hk⟩
    refine ⟨((q₀.out : K) : G), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have h : (q₀.out)⁻¹ * ⟨k, hk⟩ ∈ K'.subgroupOf K := QuotientGroup.eq.1 (QuotientGroup.out_eq' q₀)
      exact Subgroup.mem_subgroupOf.1 h
    · rintro x ⟨hx, hxk⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
      have h : q = q₀ := by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hxk)
      rw [h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_conj (w : Pl E) (n m : ℕ) : ∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ GlobalTheory.PrincCong.congSub w n m,
    k * k' * k⁻¹ ∈ GlobalTheory.PrincCong.congSub w n m := by
  rintro _ ⟨h, rfl⟩ _ ⟨h', hh', rfl⟩
  refine ⟨h * h' * h⁻¹, ?_, by simp⟩
  exact Subgroup.Normal.conj_mem inferInstance h' hh' h

def lev (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (m b : ℕ) : Subgroup (GLw b w) :=
  GlobalTheory.PrincCong.congSub w b m ⊓ μ.ker.comap GeneralLinearGroup.det

theorem continuous_det (w : Pl E) (b : ℕ) :
    Continuous (GeneralLinearGroup.det : GLw b w → (w.adicCompletion E)ˣ) :=
  Units.continuous_iff.2 ⟨Continuous.matrix_det Units.continuous_val,
    Continuous.matrix_det (Units.continuous_val.comp continuous_inv)⟩

theorem isLevel_lev (w : Pl E) (hw : IsSplitAt w) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : IsOpen (μ.ker : Set (w.adicCompletion E)ˣ)) (m b : ℕ) :
    GlobalTheory.BCT.IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) (lev w μ m b) := by
  refine ⟨?_, fun g hg => ((GlobalTheory.PrincCong.mem_congSub_iff w b m g).1 hg.1).1, fun k hk => ?_⟩
  · exact (GlobalTheory.PrincCong.isOpen_congSub w b m).inter (hμ.preimage (continuous_det w b))
  · have ht : thL b w = MonoidHom.id _ := by unfold thL; rw [if_pos hw]
    rw [ht]
    exact hk

theorem blk_mem {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : ℕ) (y : GLw a w × GLw b w)
    (h1 : y.1 ∈ GlobalTheory.PrincCong.congSub w a m) (h2 : y.2 ∈ GlobalTheory.PrincCong.congSub w b m) :
    blk h w y 0 ∈ GlobalTheory.PrincCong.congSub w n m := by
  rw [GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.blk_zero_eq, GlobalTheory.PrincCong.mem_congSub_iff]
  obtain ⟨k1, e1⟩ := (GlobalTheory.PrincCong.mem_congSub_iff w a m _).1 h1
  obtain ⟨k2, e2⟩ := (GlobalTheory.PrincCong.mem_congSub_iff w b m _).1 h2
  have hI1 := GlobalTheory.AdelicU.mem_GLint_iff.1 k1
  have hI2 := GlobalTheory.AdelicU.mem_GLint_iff.1 k2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [CtLevel.dgM_val]
    exact CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ hI1.1 hI2.1 i j
  · rw [← map_inv, CtLevel.dgM_val]
    exact CtLevel.blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ hI1.2 hI2.2 i j
  · obtain ⟨i', rfl⟩ := (CtLevel.blkEq h).surjective i
    obtain ⟨j', rfl⟩ := (CtLevel.blkEq h).surjective j
    have hone : ∀ p q, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (CtLevel.blkEq h p) (CtLevel.blkEq h q) =
        (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) (w.adicCompletion E)) p q := by
      intro p q
      simp [Matrix.one_apply, (CtLevel.blkEq h).injective.eq_iff]
    rw [hone]
    rcases i' with i' | i' <;> rcases j' with j' | j'
    · rw [(GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.dgM_entries h w y).1]
      simpa [Matrix.one_apply] using e1 i' j'
    · rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]
      simp
    · rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]
      simp
    · rw [(GlobalTheory.CompanionTheory.GL3BlockMatrixLocal.dgM_entries h w y).2]
      simpa [Matrix.one_apply] using e2 i' j'

theorem splitEx : SplitEx := by
  intro E _ _ _ n w hw μ hμ m hm KB hKB
  have hKc := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2
  have ho := GlobalTheory.PrincCong.isOpen_congSub w n m
  have hle : GlobalTheory.PrincCong.congSub w n m ≤ GlobalTheory.LFun.KGL w n :=
    fun g hg => ((GlobalTheory.PrincCong.mem_congSub_iff w n m g).1 hg).1
  have hcl : IsClosed (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) := Subgroup.isClosed_of_isOpen _ ho
  have hc : IsCompact (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) := hKc.of_isClosed_subset hcl hle
  obtain ⟨X, hX, hXu⟩ := exists_reps (GlobalTheory.LFun.KGL w n) (GlobalTheory.PrincCong.congSub w n m) hKc ho
  refine ⟨GlobalTheory.PrincCong.congSub w n m, X, (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)).indicator 1,
    fun a => (lev w μ m a).prod (lev w μ m (n - a)), ?_, ho, hle, congSub_conj w n m, hX, hXu, ?_, ?_⟩
  · ext k
    rw [Subgroup.mem_subgroupOf, GlobalTheory.PrincCong.mem_congSub_iff, hKB k]
    exact Iff.rfl
  · refine ⟨ho, hc, ?_, fun k₁ hk₁ k₂ hk₂ g => ?_⟩
    · refine HasCompactSupport.of_support_subset_isCompact hc ?_
      intro g hg
      by_contra h
      exact hg (Set.indicator_of_notMem h _)
    · have hiff : k₁ * g * k₂ ∈ GlobalTheory.PrincCong.congSub w n m ↔ g ∈ GlobalTheory.PrincCong.congSub w n m := by
        rw [Subgroup.mul_mem_cancel_right _ hk₂, Subgroup.mul_mem_cancel_left _ hk₁]
      by_cases hg : g ∈ GlobalTheory.PrincCong.congSub w n m
      · rw [Set.indicator_of_mem (show _ ∈ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hiff.2 hg),
          Set.indicator_of_mem (show _ ∈ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hg)]
        rfl
      · rw [Set.indicator_of_notMem (show _ ∉ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from fun h => hg (hiff.1 h)),
          Set.indicator_of_notMem (show _ ∉ (GlobalTheory.PrincCong.congSub w n m : Set (GLw n w)) from hg)]
  · intro a ha
    refine ⟨⟨_, _, rfl, isLevel_lev w hw μ hμ m a, isLevel_lev w hw μ hμ m (n - a)⟩, fun y hy => ⟨?_, ?_⟩⟩
    · exact blk_mem (Nat.add_sub_of_le ha) w m y hy.1.1 hy.2.1
    · have d1 : μ (GeneralLinearGroup.det y.1) = 1 := hy.1.2
      have d2 : μ (GeneralLinearGroup.det y.2) = 1 := hy.2.2
      rw [map_mul, map_pow, map_pow, d1, d2, one_pow, one_pow, one_mul]

end GlobalTheory.CompanionTheory.SplitLevel

end
