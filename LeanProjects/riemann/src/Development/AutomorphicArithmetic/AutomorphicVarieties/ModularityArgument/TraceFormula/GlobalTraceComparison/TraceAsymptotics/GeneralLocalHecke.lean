import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfNotFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportOutFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedOpenSubgroupGLw

noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section Gen
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem exists_normal (K K₀ : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hK₀ : IsOpen (K₀ : Set G)) :
    ∃ N : Subgroup G, IsOpen (N : Set G) ∧ N ≤ K₀ ∧ N ≤ K ∧ (N.subgroupOf K).Normal := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  set U := K₀.subgroupOf K with hU
  have hUo : IsOpen (U : Set K) := hK₀.preimage continuous_subtype_val
  haveI : Finite (K ⧸ U) := Subgroup.quotient_finite_of_isOpen _ hUo
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hUc : IsClosed (U : Set K) := U.isClosed_of_isOpen hUo
  have hcl : IsClosed (U.normalCore : Set K) := by
    have e : (U.normalCore : Set K) = ⋂ b : K, (fun a => b * a * b⁻¹) ⁻¹' (U : Set K) := by
      ext a
      simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      rfl
    rw [e]
    exact isClosed_iInter fun b => hUc.preimage (by fun_prop)
  have hco : IsOpen (U.normalCore : Set K) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  refine ⟨U.normalCore.map K.subtype, ?_, ?_, Subgroup.map_subtype_le _, ?_⟩
  · rw [Subgroup.coe_map]
    exact hKo.isOpenMap_subtype_val _ hco
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le U hx)
  · have e : (U.normalCore.map K.subtype).subgroupOf K = U.normalCore :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [e]
    exact Subgroup.normalCore_normal U

private theorem trc_eq {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K N : Subgroup G)
    (hKc : IsCompact (K : Set G)) (hNo : IsOpen (N : Set G)) (hNK : N ≤ K)
    (hfd : FiniteDimensional ℂ (fixed ρ N)) (F : G → ℂ) (hF : IsHecke N F) :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.trc ρ K F = twTr ρ K N F LinearMap.id := by
  unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.trc
  refine (GlobalTheory.TraceLevel.twTr_level ρ K _ N F hNo hKc ?_ ?_ ⟨hF.1, ?_⟩ hfd).symm
  · intro k hk
    refine ⟨⟨hNK hk, fun x => (hF.2 k hk x).2⟩, fun x => ?_⟩
    show F (x * k)⁻¹ = F x⁻¹
    rw [_root_.mul_inv_rev, (hF.2 _ (N.inv_mem hk) _).1]
  · exact inf_le_left.trans inf_le_left
  · intro k hk x
    refine ⟨?_, hk.1.2 x⟩
    have h := hk.2 (x⁻¹ * k⁻¹)
    simp only [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right] at h
    simpa using h.symm

end Gen

private theorem hint_sub {H : Type} [Group H] [Subsingleton H] (K : Subgroup H) (u : H → ℂ) : hint K u = u 1 := by
  unfold hint
  have h1 : (rStab u ⊓ K).relIndex K = 1 :=
    Subgroup.relIndex_eq_one.2 fun x _ => by
      rw [Subsingleton.elim x 1]
      exact one_mem _
  haveI : Unique (H ⧸ (rStab u ⊓ K)) :=
    { default := QuotientGroup.mk 1
      uniq := fun q => by
        induction q using QuotientGroup.induction_on with
        | H x => rw [Subsingleton.elim x 1] }
  have hu : ∀ x : H, u x = u 1 := fun x => by rw [Subsingleton.elim x 1]
  rw [h1, finsum_unique, hu]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem blk_zero {n : ℕ} (w : Pl E) (g : GLw n w) (m : GLw 0 w) (X : Matrix (Fin n) (Fin 0) (w.adicCompletion E)) :
    blk (Nat.add_zero n) w (g, m) X = g := by
  have e : ∀ i : Fin n, (finSumFinEquiv.trans (finCongr (Nat.add_zero n))).symm i = Sum.inl i := by
    intro i
    rw [Equiv.symm_apply_eq]
    ext
    simp
    rfl
  have hM : Matrix.reindex (finSumFinEquiv.trans (finCongr (Nat.add_zero n))) (finSumFinEquiv.trans (finCongr (Nat.add_zero n)))
      (Matrix.fromBlocks g.val (g.val * X) 0 m.val) = g.val := by
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, e, Matrix.fromBlocks_apply₁₁]
  have key : ∀ (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)), M = g.val →
      (if hM : IsUnit M then hM.unit else (1 : GLw n w)) = g := by
    rintro _ rfl
    rw [dif_pos g.isUnit]
    exact Units.ext rfl
  exact key _ hM

private theorem constant_term_parabolic_average {n : ℕ} (w : Pl E) (hw : IsSplitAt w) (μ : HChar E) (f : ∀ w : Pl E, GLw n w → ℂ) (g : GLw n w) :
    ct0 μ (Nat.add_zero n) f w (g, 1) = avg fun k : KGL w n => f w ((k : GLw n w)⁻¹ * g * k) := by
  haveI : Subsingleton (Multiplicative (Matrix (Fin n) (Fin 0) (w.adicCompletion E))) :=
    ⟨fun a b => Multiplicative.toAdd.injective (by ext i j; exact j.elim0)⟩
  have hU : ∀ y : GLw n w, y ∈ UL n w := fun y => by
    unfold UL
    rw [if_pos hw]
    trivial
  have hs : ∀ y : GLw n w, (toSub (UL n w) y : GLw n w) = y := fun y => by
    unfold toSub
    rw [dif_pos (hU y)]
  unfold ct0 ctMu ct
  rw [hint_sub]
  simp only [blk_zero, hs]
  have h0 : absHalf w ((g, (1 : GLw 0 w)).1.val.det ^ 0 / (g, (1 : GLw 0 w)).2.val.det ^ n) = 1 := by
    simp [absHalf, ordL]
    exact zpow_zero _
  rw [h0]
  simp

theorem trAvg : TrAvg := by
  intro E _ _ _ n w hw μ τ f hf
  obtain ⟨K₀, hK₀o, -, hH⟩ := hf
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  obtain ⟨N, hNo, hNK₀, hNK, hNn⟩ := exists_normal _ K₀ hKo hKc hK₀o
  have hfd := finiteDimensional_fixed_openSubgroup_GLw E n w τ N hNo
  have hfN : IsHecke N (f w) := ⟨hH.1, fun k hk x => hH.2 k (hNK₀ hk) x⟩
  obtain ⟨hFN, -, -, htr⟩ := GlobalTheory.ConjAvg.conjAvg E n w τ.V τ.ρ N hNo hNK hNn (f w) hfN
  have hct : (fun g => ct0 μ (Nat.add_zero n) f w (g, 1)) =
      fun g => avg fun k : KGL w n => f w ((k : GLw n w)⁻¹ * g * k) :=
    funext fun g => constant_term_parabolic_average w hw μ f g
  rw [hct, trc_eq τ.ρ _ N hKc hNo hNK hfd _ hFN, trc_eq τ.ρ _ N hKc hNo hNK hfd _ hfN, htr]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
