import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeOfIsHeckeWit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

open GlobalTheory.DrinLev.HT.HeckePt GlobalTheory.CechPic

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

private theorem cls_lbPow_eq_nsmul {X : Scheme} {L : LB X} (hL : L.IsLB) (c : ℕ) (h : (Hecke.lbPow L c).IsLB) :
    cls (Hecke.lbPow L c) h = c • cls L hL := by
  refine (cls_linComb hL _ _ h).trans ?_
  simp [pull_id]

theorem isPIsog_pullMor {S S' : Scheme.{0}} {s : S ⟶ Sp R} {f : S' ⟶ S} {o o' : Obj b N s}
    {o₁ o₁' : Obj b N (f ≫ s)} (n : ObjMap o₁ o f) (n' : ObjMap o₁' o' f) {c : ℕ} {ψ : o.A ⟶ o'.A}
    (hψ : IsPIsog c o o' ψ) : IsPIsog c o₁ o₁' (pullMor n.cart n'.cart ψ) := by
  obtain ⟨hc, hmon, hact, heta, ⟨hpol⟩, ψ', hmon', h1, h2⟩ := hψ
  haveI := hmon
  haveI := hmon'
  have hl := pullMor_left n.cart n'.cart ψ
  set pm := pullMor n.cart n'.cart ψ with hpm
  refine ⟨hc, isMonHom_pullMor _ _ _, ?_, ?_, ?_, pullMor n'.cart n.cart ψ', isMonHom_pullMor _ _ _,
    pullMor_comp_eq_pow _ _ _ _ _ h1, pullMor_comp_eq_pow _ _ _ _ _ h2⟩
  · intro c'
    apply ext_of_left n'.cart
    have e := congrArg Over.Hom.left (hact c')
    simp only [Over.comp_left] at e
    simp only [Over.comp_left, Category.assoc, hl, reassoc_of% hl, reassoc_of% (n.act c'), n'.act, e]
  · intro x
    apply ext_of_left n'.cart
    have e := congrArg Over.Hom.left (heta x)
    simp only [Over.comp_left] at e
    simp only [Over.comp_left, Category.assoc, hl, n'.eta, reassoc_of% (n.eta x), e]
  · have hsq : n.φ₂ ≫ sq2 ψ = sq2 pm ≫ n'.φ₂ := PIsogExt.isSquare_square_compatible_homs n.sq n'.sq hl.symm
    have hA : (Hecke.lbPow o₁.P c).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hB : (o₁'.P.pull (sq2 pm)).IsLB := pull_isLB o₁'.isLB _
    have hX : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
    refine ⟨(cls_eq_iff hA hB).1 ?_⟩
    have e1 := (cls_eq_iff o₁.isLB (pull_isLB o.isLB n.φ₂)).2 n.pol
    have e1' := (cls_eq_iff o₁'.isLB (pull_isLB o'.isLB n'.φ₂)).2 n'.pol
    have e0 : c • cls o.P o.isLB = pull (sq2 ψ) (cls o'.P o'.isLB) := by
      rw [← cls_lbPow_eq_nsmul o.isLB c hX, ← cls_pull o'.isLB (sq2 ψ) (pull_isLB o'.isLB _)]
      exact (cls_eq_iff hX _).2 hpol
    rw [cls_pull o.isLB] at e1
    rw [cls_pull o'.isLB] at e1'
    rw [cls_lbPow_eq_nsmul o₁.isLB c hA, cls_pull o₁'.isLB, e1, e1', ← pull_comp, ← hsq, pull_comp, ← e0,
      map_nsmul]

theorem isogTarget_spMap : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (M : Model b N) (c : ℕ) (k L : Type) [Field k] [Field L] (j : k →+* L) (ξ ζ : Sp k ⟶ M.X),
    CorrQF.IsogTarget M c ξ ζ → CorrQF.IsogTarget M c (spMap j ≫ ξ) (spMap j ≫ ζ) := by
  intro p _ D R _ b N M c k L _ _ j ξ ζ h
  obtain ⟨hs, o, o', ψ, ⟨m⟩, ⟨m'⟩, hψ⟩ := h
  obtain ⟨o₁, ⟨n⟩⟩ := HTPull.exists_objMap_pull p D R b N (Sp k) (Sp L) (ξ ≫ M.s) (spMap j) o
  obtain ⟨o₁', ⟨n'⟩⟩ := HTPull.exists_objMap_pull p D R b N (Sp k) (Sp L) (ξ ≫ M.s) (spMap j) o'
  have key : ∀ (w : Sp L ⟶ Sp R), spMap j ≫ ξ ≫ M.s = w →
      ∃ (a a' : Obj b N w) (φ : a.A ⟶ a'.A), Nonempty (ObjMap a M.univ (spMap j ≫ ξ)) ∧
        Nonempty (ObjMap a' M.univ (spMap j ≫ ζ)) ∧ IsPIsog c a a' φ := by
    intro w hw
    subst hw
    exact ⟨o₁, o₁', _, ⟨n.comp m⟩, ⟨n'.comp m'⟩, isPIsog_pullMor n n' hψ⟩
  obtain ⟨a, a', φ, ha, ha', hφ⟩ := key _ (Category.assoc _ _ _).symm
  exact ⟨by simp only [Category.assoc, hs], a, a', φ, ha, ha', hφ⟩

end GlobalTheory.UPel.HT.ES.CorrQF
