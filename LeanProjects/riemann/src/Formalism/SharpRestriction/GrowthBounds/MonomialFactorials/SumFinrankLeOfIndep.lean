import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestSumSpan
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestDimBCProved
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationOverZpHolds
import Formalism.MahlerMeasure.MahlerMeasureProofs.SSDirect

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem sum_finrank_le_of_indep {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq ι]
    (f : ι → Submodule K V) (hf : iSupIndep f) (T : Submodule K V) [FiniteDimensional K T] (s : Finset ι)
    (hle : ∀ i ∈ s, f i ≤ T) : ∑ i ∈ s, Module.finrank K (f i) ≤ Module.finrank K T := by
  have key : ∀ s : Finset ι, (∀ i ∈ s, f i ≤ T) →
      (⨆ i ∈ s, f i) ≤ T ∧ ∑ i ∈ s, Module.finrank K (f i) = Module.finrank K (⨆ i ∈ s, f i : Submodule K V) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      have h0 : (⨆ i ∈ (∅ : Finset ι), f i) = ⊥ := le_bot_iff.1 (iSup₂_le fun i hi => by simp at hi)
      rw [h0, finrank_bot, Finset.sum_empty]
      exact ⟨bot_le, rfl⟩
    | insert a s ha ih =>
      intro h
      obtain ⟨h1, h2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hfa : f a ≤ T := h a (Finset.mem_insert_self a s)
      have e : (⨆ i ∈ insert a s, f i) = f a ⊔ ⨆ i ∈ s, f i := by
        rw [Finset.iSup_insert]
      haveI : FiniteDimensional K (f a) := Submodule.finiteDimensional_of_le hfa
      haveI : FiniteDimensional K (⨆ i ∈ s, f i : Submodule K V) := Submodule.finiteDimensional_of_le h1
      have hd : Disjoint (f a) (⨆ i ∈ s, f i) := hf.disjoint_biSup ha
      refine ⟨by rw [e]; exact sup_le hfa h1, ?_⟩
      rw [Finset.sum_insert ha, h2, e]
      have := Submodule.finrank_sup_add_finrank_inf_eq (f a) (⨆ i ∈ s, f i)
      rw [hd.eq_bot, finrank_bot, add_zero] at this
      omega
  obtain ⟨h1, h2⟩ := key s hle
  rw [h2]
  exact Submodule.finrank_mono h1

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem span_SSZ_fin (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) :
    FiniteDimensional ℚ_[X.p] (Submodule.span ℚ_[X.p]
      (((gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) :
        Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :
          Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p]))) := by
  set Dd := blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b with hDd
  set V0 := Submodule.span ℚ_[X.p]
    (((gmB Dd).SSZ X.p (r := X.r) : Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) :
      Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) with hV0
  set W := Submodule.span (KK X.O) ((Dd.SSZ X.O (r := X.r) : Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r Dd.T.t) (KK X.O))) :
      Set (MvPolynomial (BVar (2 * X.s + 1) X.r Dd.T.t) (KK X.O))) with hW
  show FiniteDimensional ℚ_[X.p] V0
  haveI : FiniteDimensional (KK X.O) W := span_SSZ_finite Dd
  have hmemW : ∀ x ∈ V0, MvPolynomial.map (iotaX X) x ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact map_SSZ (ι := iotaX X) (iotaX_int X) Dd x hx
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul a x _ hx => rw [map_smul_Q]; exact W.smul_mem _ hx
  refine Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt (rank_le (n := Module.finrank (KK X.O) W) fun s hs => ?_)
    (Cardinal.natCast_lt_aleph0))
  have hli : LinearIndependent ℚ_[X.p] (fun i : s => ((i : V0) : MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) :=
    hs.map' V0.subtype (Submodule.ker_subtype V0)
  have hli2 := li_map (iotaX X) _ hli
  let w : s → W := fun i => ⟨MvPolynomial.map (iotaX X) (i : V0).1, hmemW _ (i : V0).2⟩
  have hli3 : LinearIndependent (KK X.O) w := LinearIndependent.of_comp W.subtype hli2
  have h := hli3.fintype_card_le_finrank
  simpa using h

theorem sum_gens_le (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N) (hB : G.BlockOK)
    (hr : 1 ≤ r) (s : Finset ((Fin G.T.t → ℕ) × ℕ)) (hs : ∀ x ∈ s, G.LevelOK x.1 x.2)
    [FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] ((G.SSZ p (r := r) :
      Submodule ℤ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])) : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])))] :
    ∑ x ∈ s, Module.finrank ℚ_[p] (Submodule.span ℚ_[p] (G.gens p (r := r) x.1 x.2)) ≤
      Module.finrank ℚ_[p] (Submodule.span ℚ_[p] ((G.SSZ p (r := r) :
        Submodule ℤ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])) : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]))) := by
  classical
  have hind := (Formalism.GM.semisimple_direct_sum p N r G hB hr).1
  let g : {x // x ∈ s} → {ij : (Fin G.T.t → ℕ) × ℕ // G.LevelOK ij.1 ij.2} := fun y => ⟨y.1, hs y.1 y.2⟩
  have hg : Function.Injective g := fun y y' h => by
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  have hind' := iSupIndep.comp hind hg
  rw [← Finset.sum_attach]
  refine sum_finrank_le_of_indep _ hind' _ s.attach fun y _ => ?_
  apply Submodule.span_le.2
  intro z hz
  apply Submodule.subset_span
  show z ∈ ((G.SSZ p (r := r) : Submodule ℤ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])) :
    Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]))
  unfold Formalism.GM.M.BlockData.SSZ
  exact Submodule.subset_span (Set.mem_iUnion.2 ⟨y.1.1, Set.mem_iUnion.2 ⟨y.1.2, Set.mem_iUnion.2 ⟨hs y.1 y.2, hz⟩⟩⟩)

theorem restSumSpan_proved : RestSumSpan C0 CE1 CE2 X := by
  classical
  intro aTop _ aPlus _ b _
  haveI := span_SSZ_fin C0 CE1 CE2 X aTop aPlus b
  have hr : 1 ≤ X.r := Nat.pos_of_ne_zero X.hm
  refine sum_gens_le X.p (gB C0 CE1 CE2 X aTop aPlus b) (gB_blockOK C0 CE1 CE2 X aTop aPlus b) hr
    (lv C0 CE1 CE2 X aTop b) (fun x hx => ?_)
  rw [lv_eq C0 CE1 CE2 X aTop aPlus b] at hx
  unfold levels at hx
  exact (Finset.mem_filter.1 hx).2

end Formalism.MainNotions.G.SymmetricFormBlocks

end
