import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecScalIffPullAb
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValRConstHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.AdaptedSep

theorem basis_separates : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 4 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → (∀ (a : u.PtC) w, Crd (u.H k) σ (u.toG a) w → w ≠ 0) ∧ (∀ (a a' : u.PtC) w, Crd (u.H k) σ (u.toG a) w → Crd (u.H k) σ (u.toG a') w → a = a') ∧ ∀ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j → ∃ a' : u.PtC, u.toG a' = a := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l k hk J _ σ cls f ⟨_, h₂, h₃, h₄, h₅, h₆, h₇⟩
  obtain ⟨m, t, ht⟩ := CrdMove.immBy_lbPow hL.1.ample _ u.A k hk
  obtain ⟨s, hs⟩ := CrdMove.exists_transport u.A.isLB u.U.LG.isLB u.U.gen.hom.left u.U.gen.inv.left
    (congrArg (fun q => q.left) u.U.gen.inv_hom_id) (congrArg (fun q => q.left) u.U.gen.hom_inv_id) _ u.U.ext k t
  choose b hb using fun i => AdaptedSpan.exists_comb hL.1.globalFns u.U (by omega : 1 ≤ k) σ cls f h₂ h₃ h₄ h₅ h₆ h₇ (s i)
  have key : ∀ (a : u.PtC) w, Crd (u.H k) σ (u.toG a) w → Crd (lbPow u.A.L k) t (a.left ≫ u.U.gen.hom.left)
      (fun i => ∑ j, algebraMap (FractionRing u.V) (PadicAlgCl p) (b i j) * w j) := fun a w h =>
    hs _ a.left _ (CrdMove.crd_comb (pullback.condition : pullback.fst u.G.hom (jK u.V) ≫ u.G.hom = _)
      (fun _ => (Category.comp_id _).symm) σ s b hb a.left _ (Over.w a) h)
  refine ⟨fun a w h hw => ?_, fun a a' w h h' => ?_, fun a ha => ?_⟩
  · have hm : (a.left ≫ u.U.gen.hom.left : Sp (PadicAlgCl p) ⟶ u.A.A.left) (IsLocalRing.closedPoint _) ∈
        ⨆ i ∈ Set.univ, nonzeroLocus (t i) := by rw [ht.1]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    obtain ⟨_, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    have hu := (CrdCalc.crd_isUnit_iff i (key a w h)).2 ((CrdCalc.top_le_iff _ _).2 hi)
    simp [hw] at hu
  · have e := ImmSep.eq_of_crd_eq _ _ _ _ _ t _ (DVR.linComb_isLB _ u.A.isLB _ _) ht _ _ _ _
      ((Over.w (a ≫ u.U.gen.hom)).trans (Over.w (a' ≫ u.U.gen.hom)).symm) (key a w h) (key a' w h')
    exact (cancel_mono u.U.gen.hom).1 (Over.OverMorphism.ext e)
  · have e : gPt p ≫ spMap u.j = jFK (R := u.V) (PadicAlgCl p) ≫ jK u.V :=
      (Spec.map_comp _ _).symm.trans (Eq.trans rfl (Spec.map_comp
        (CommRingCat.ofHom (algebraMap u.V (FractionRing u.V)))
        (CommRingCat.ofHom (algebraMap (FractionRing u.V) (PadicAlgCl p)))))
    exact ⟨Over.homMk (pullback.lift a (jFK (R := u.V) (PadicAlgCl p)) (ha.trans e)) (pullback.lift_snd _ _ _),
      pullback.lift_fst _ _ _⟩

end GlobalTheory.ZH.AdaptedSep
