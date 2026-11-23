import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem weight_app {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G]
    (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V)
    (h : V ≤ E.chart j) (χ : E.X) (a : Γ(E.B.left, V)) :
    D.weight j V hV h χ ((D.q.left.app V).hom a) = (Finsupp.single (0 : E.X) a) χ := by
  have e : (Equiv.ofBijective _ (D.coord j V hV h)).symm ((D.q.left.app V).hom a) =
      AddMonoidAlgebra.single 0 a := by
    rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply]
    simp [AddMonoidAlgebra.liftNCRingHom]
  unfold SplitExt.GtDatum.weight
  rw [e, AddMonoidAlgebra.coeff_single]

theorem eq_of_weight_eq {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G]
    (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V)
    (h : V ≤ E.chart j) {s s' : Γ(G.left, D.q.left ⁻¹ᵁ V)}
    (e : ∀ χ, D.weight j V hV h χ s = D.weight j V hV h χ s') : s = s' := by
  apply (Equiv.ofBijective _ (D.coord j V hV h)).symm.injective
  apply AddMonoidAlgebra.ext
  ext χ
  exact e χ

theorem app_res {X Y : Scheme.{0}} (q : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : q ⁻¹ᵁ V ≤ q ⁻¹ᵁ U)
    (a : Γ(X, U)) :
    (q.app V).hom ((X.presheaf.map (homOfLE h).op).hom a) =
      (Y.presheaf.map (homOfLE h').op).hom ((q.app U).hom a) := by
  have := q.naturality (homOfLE h).op
  exact congrArg (fun f => f.hom a) this

theorem FibPre.compat_iff {k : Type} [Field k] (Φ : FibPre k) (t : ∀ l, Γ(Φ.E.B.left, Φ.N₀.U l))
    (i j : Φ.N₀.ι) :
    ((Φ.G.left.presheaf.map (homOfLE (inf_le_left : (Φ.H 1).U i ⊓ (Φ.H 1).U j ≤ (Φ.H 1).U i)).op).hom
        ((Φ.D.q.left.app (Φ.N₀.U i)).hom (t i)) =
      ((Φ.H 1).g i j : Γ(Φ.G.left, (Φ.H 1).U i ⊓ (Φ.H 1).U j)) *
        (Φ.G.left.presheaf.map (homOfLE (inf_le_right : (Φ.H 1).U i ⊓ (Φ.H 1).U j ≤ (Φ.H 1).U j)).op).hom
          ((Φ.D.q.left.app (Φ.N₀.U j)).hom (t j))) ↔
    (Φ.E.B.left.presheaf.map (homOfLE (inf_le_left : Φ.N₀.U i ⊓ Φ.N₀.U j ≤ Φ.N₀.U i)).op).hom (t i) =
      (Φ.N₀.g i j : Γ(Φ.E.B.left, Φ.N₀.U i ⊓ Φ.N₀.U j)) *
        (Φ.E.B.left.presheaf.map (homOfLE (inf_le_right : Φ.N₀.U i ⊓ Φ.N₀.U j ≤ Φ.N₀.U j)).op).hom (t j) := by
  have := Φ.D.q_flat
  have := Φ.D.q_surjective
  rw [← (GlobalTheory.FunDescent.app_injective Φ.D.q.left (Φ.N₀.U i ⊓ Φ.N₀.U j)).eq_iff, map_mul,
    app_res _ _ (Φ.D.q.left.preimage_mono inf_le_left), app_res _ _ (Φ.D.q.left.preimage_mono inf_le_right)]
  have hg : ((Φ.H 1).g i j : Γ(Φ.G.left, (Φ.H 1).U i ⊓ (Φ.H 1).U j)) =
      (Φ.D.q.left.app (Φ.N₀.U i ⊓ Φ.N₀.U j)).hom (Φ.N₀.g i j) :=
    congrArg Units.val (pow_one (pullU Φ.D.q.left (Φ.N₀.U i ⊓ Φ.N₀.U j) (Φ.N₀.g i j)))
  rw [hg]
  exact Iff.rfl

theorem FibPre.pure_zero : (∀ (k : Type) [Field k] (Φ : FibPre k), (∀ t : Φ.N₀.Sec, ∃ φ : (Φ.H 1).Sec, Φ.Pure 0 φ ∧ ∀ l, Φ.wt φ 0 l = t.f l) ∧ ∀ φ : (Φ.H 1).Sec, Φ.Pure 0 φ → ∃ t : Φ.N₀.Sec, (∀ l, Φ.wt φ 0 l = t.f l) ∧ (∀ l, φ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (t.f l)) ∧ Out.nonzeroLocus φ = Φ.D.q.left ⁻¹ᵁ Out.nonzeroLocus t) := by
  intro k _ Φ
  refine ⟨fun t => ?_, fun φ hφ => ?_⟩
  · refine ⟨⟨fun l => (Φ.D.q.left.app (Φ.N₀.U l)).hom (t.f l),
      fun i j => (Φ.compat_iff t.f i j).2 (t.compat i j)⟩, ?_, fun l => ?_⟩
    · rintro α ⟨l, hl⟩
      by_contra hα
      exact hl ((weight_app Φ.D _ _ _ _ α (t.f l)).trans (Finsupp.single_eq_of_ne hα))
    · exact (weight_app Φ.D _ _ _ _ 0 (t.f l)).trans Finsupp.single_eq_same
  · have hf : ∀ l, φ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (Φ.wt φ 0 l) := fun l => by
      refine eq_of_weight_eq Φ.D (Φ.ch l) _ (Φ.aff l) (Φ.le l) fun χ => ?_
      rw [weight_app]
      by_cases hχ : χ = 0
      · subst hχ
        exact Finsupp.single_eq_same.symm
      · rw [Finsupp.single_eq_of_ne hχ]
        by_contra hne
        exact hχ (hφ ⟨l, hne⟩)
    refine ⟨⟨fun l => Φ.wt φ 0 l, fun i j => (Φ.compat_iff _ i j).1 ?_⟩, fun _ => rfl, hf, ?_⟩
    · have c := φ.compat i j
      rw [hf i, hf j] at c
      exact c
    · unfold Out.nonzeroLocus
      rw [Scheme.Hom.preimage_iSup]
      refine iSup_congr fun l => ?_
      rw [Scheme.preimage_basicOpen, hf]
      rfl

end GlobalTheory.ZH
