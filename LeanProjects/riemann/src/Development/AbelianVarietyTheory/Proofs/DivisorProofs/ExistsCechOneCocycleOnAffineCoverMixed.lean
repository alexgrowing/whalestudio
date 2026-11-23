import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsCobOfIsAffineOpen

open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)

namespace GlobalTheory.CechMixed
open GlobalTheory.KS

theorem coc_on {X : Scheme.{0}} {J : Type} {V : J → X.Opens} {z : C1 V} (hz : IsCoc V z) (i j l : J)
    {W : X.Opens} (hi : W ≤ V i) (hj : W ≤ V j) (hl : W ≤ V l) :
    rsT (z i j) W + rsT (z j l) W = rsT (z i l) W := by
  have e : W ≤ V i ⊓ V j ⊓ V l := le_inf (le_inf hi hj) hl
  have h := congrArg (fun s => rsT s W) (hz i j l)
  simp only [rsT_add] at h
  rwa [rsT_rsT inf_le_left e, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) e,
    rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) e] at h

theorem le_iSup_inf {X : Scheme.{0}} {J : Type} {V : J → X.Opens} (hV : ⨆ i, V i = ⊤) (O : X.Opens) :
    O ≤ ⨆ i, V i ⊓ O := by
  rw [← iSup_inf_eq, hV, top_inf_eq]

theorem exists_split {X : Scheme.{0}} {J : Type} {V : J → X.Opens} (hV : ⨆ i, V i = ⊤) {O : X.Opens}
    (hO : IsAffineOpen O) {z : C1 V} (hz : IsCoc V z) :
    ∃ b : ∀ i, Γ(X, V i ⊓ O), ∀ i i' (W : X.Opens), W ≤ V i → W ≤ V i' → W ≤ O →
      rsT (z i i') W = rsT (b i) W - rsT (b i') W := by
  have hs : ⨆ i, V i ⊓ O = O := by rw [← iSup_inf_eq, hV, top_inf_eq]
  have hle : ∀ i j, V i ⊓ O ⊓ (V j ⊓ O) ≤ V i ⊓ V j := fun i j => inf_le_inf inf_le_left inf_le_left
  obtain ⟨y, hy⟩ := isCob_of_isAffineOpen X J (fun i => V i ⊓ O)
    (fun i j => rsT (z i j) (V i ⊓ O ⊓ (V j ⊓ O))) (hs.symm ▸ hO) (by
      intro i j l
      dsimp only
      rw [rsT_rsT (hle i j) inf_le_left,
        rsT_rsT (hle j l) (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
        rsT_rsT (hle i l) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)]
      exact coc_on hz i j l ((inf_le_left.trans inf_le_left).trans inf_le_left)
        ((inf_le_left.trans inf_le_right).trans inf_le_left) (inf_le_right.trans inf_le_left))
  refine ⟨fun i => - y i, fun i i' W h h' hW => ?_⟩
  have e : W ≤ V i ⊓ O ⊓ (V i' ⊓ O) := le_inf (le_inf h hW) (le_inf h' hW)
  have k := congrArg (fun s => rsT s W) (hy i i')
  simp only [rsT_sub] at k
  rw [rsT_rsT (hle i i') e, rsT_rsT inf_le_right e, rsT_rsT inf_le_left e] at k
  simp only [rsT_neg]
  rw [k]; ring

theorem exists_cocycle_on_affine : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ i, V i = ⊤ → (∀ k, IsAffineOpen (U k)) → ∀ z : C1 V, IsCoc V z → ∃ (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), IsCoc U z' ∧ (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) ∧ ∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k') := by
  intro X J K V U hV hU z hz
  choose b hb using fun k => exists_split hV (hU k) hz
  have glue : ∀ k k', ∃ t : Γ(X, U k ⊓ U k'), ∀ i, rsT t (V i ⊓ (U k ⊓ U k')) =
      rsT (b k' i) (V i ⊓ (U k ⊓ U k')) - rsT (b k i) (V i ⊓ (U k ⊓ U k')) := by
    intro k k'
    refine exists_rsT_eq (fun i => V i ⊓ (U k ⊓ U k')) (fun i => inf_le_right)
      (le_iSup_inf hV _) _ fun i j => ?_
    simp only [rsT_sub]
    rw [rsT_rsT (inf_le_inf_left _ inf_le_right) inf_le_left,
      rsT_rsT (inf_le_inf_left _ inf_le_left) inf_le_left,
      rsT_rsT (inf_le_inf_left _ inf_le_right) inf_le_right,
      rsT_rsT (inf_le_inf_left _ inf_le_left) inf_le_right]
    have hi : V i ⊓ (U k ⊓ U k') ⊓ (V j ⊓ (U k ⊓ U k')) ≤ V i := inf_le_left.trans inf_le_left
    have hj : V i ⊓ (U k ⊓ U k') ⊓ (V j ⊓ (U k ⊓ U k')) ≤ V j := inf_le_right.trans inf_le_left
    have hk : V i ⊓ (U k ⊓ U k') ⊓ (V j ⊓ (U k ⊓ U k')) ≤ U k ⊓ U k' := inf_le_right.trans inf_le_right
    have h1 := hb k i j _ hi hj (hk.trans inf_le_left)
    have h2 := hb k' i j _ hi hj (hk.trans inf_le_right)
    linear_combination h1 - h2
  choose t ht using glue
  have ht' : ∀ k k' i (W : X.Opens), W ≤ V i → W ≤ U k → W ≤ U k' →
      rsT (t k k') W = rsT (b k' i) W - rsT (b k i) W := by
    intro k k' i W hi hk hk'
    have e : W ≤ V i ⊓ (U k ⊓ U k') := le_inf hi (le_inf hk hk')
    have h := congrArg (fun s => rsT s W) (ht k k' i)
    simp only [rsT_sub] at h
    rwa [rsT_rsT inf_le_right e, rsT_rsT (inf_le_inf_left _ inf_le_right) e,
      rsT_rsT (inf_le_inf_left _ inf_le_left) e] at h
  refine ⟨t, fun i k => b k i, fun k k' k'' => ?_, fun i i' k => hb k i i' _
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right,
    fun i k k' => ht' k k' i _ (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
      inf_le_right⟩
  refine eq_of_rsT_eq (fun i => V i ⊓ (U k ⊓ U k' ⊓ U k'')) (fun i => inf_le_right)
    (le_iSup_inf hV _) _ _ fun i => ?_
  have e : V i ⊓ (U k ⊓ U k' ⊓ U k'') ≤ U k ⊓ U k' ⊓ U k'' := inf_le_right
  have e1 := (e.trans inf_le_left).trans inf_le_left
  have e2 := (e.trans inf_le_left).trans inf_le_right
  have e3 := e.trans inf_le_right
  simp only [rsT_add]
  rw [rsT_rsT inf_le_left e, rsT_rsT (le_inf (inf_le_left.trans inf_le_right) inf_le_right) e,
    rsT_rsT (le_inf (inf_le_left.trans inf_le_left) inf_le_right) e,
    ht' k k' i _ inf_le_left e1 e2, ht' k' k'' i _ inf_le_left e2 e3, ht' k k'' i _ inf_le_left e1 e3]
  ring

end GlobalTheory.CechMixed
