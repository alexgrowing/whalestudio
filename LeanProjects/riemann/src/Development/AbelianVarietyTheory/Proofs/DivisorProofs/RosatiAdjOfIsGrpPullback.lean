import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

namespace GlobalTheory.TorusPart

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR TopologicalSpace in

theorem rosatiAdj_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} (P : Out.PolAV S) (P' : Out.PolAV S')
    {g : P'.A.left ⟶ P.A.left} (hg : IsGrpPullback P'.A P.A f g) (hw : LBIso (P.L.pull g) P'.L)
    {a b : P.A ⟶ P.A} {a' b' : P'.A ⟶ P'.A} (ha : a'.left ≫ g = g ≫ a.left) (hb : b'.left ≫ g = g ≫ b.left)
    (h : RosatiAdj P.A P.L a b) : RosatiAdj P'.A P'.L a' b' := by
  have pa : ∀ {c : P.A ⟶ P.A} {c' : P'.A ⟶ P'.A}, c'.left ≫ g = g ≫ c.left → ∀ {T : Over S'} (x : T ⟶ P'.A),
      pushPt hg.1.w (x ≫ c') = pushPt hg.1.w x ≫ c := fun hc _ x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hc, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ P'.A), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  obtain ⟨w, gw'⟩ := LBIso.symm hw
  intro s
  obtain ⟨U, hU, t, ht⟩ := h (f s)
  let V : (P'.A ⊗ P'.A).left.Opens := (P'.A ⊗ P'.A).hom ⁻¹ᵁ (f ⁻¹ᵁ U)
  let T' : Over S' := Over.mk (V.ι ≫ (P'.A ⊗ P'.A).hom)
  let j : T' ⟶ P'.A ⊗ P'.A := Over.homMk V.ι rfl
  let m := lift (pushPt hg.1.w (j ≫ fst _ _)) (pushPt hg.1.w (j ≫ snd _ _))
  obtain ⟨n, hn⟩ : ∃ n : V.toScheme ⟶ ((P.A ⊗ P.A).hom ⁻¹ᵁ U).toScheme, n ≫ ((P.A ⊗ P.A).hom ⁻¹ᵁ U).ι = m.left :=
    ⟨IsOpenImmersion.lift _ m.left (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y ∈ U) (Over.w m)).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨t', ht', -⟩ := exists_gen P.isLB (φ' := fun i => (V.ι ≫ rosatiφ P'.A a' b' i) ≫ g)
    (ε' := rosatiε) (fun W _ k => by
      have p₁ := prod_ros a b (pushPt hg.1.w (j ≫ fst _ _)) (pushPt hg.1.w (j ≫ snd _ _)) k
      have p₂ := prod_ros a' b' (j ≫ fst _ _) (j ≫ snd _ _) (fun q => k (q ≫ g))
      rw [← comp_lift, lift_fst_snd, Category.comp_id] at p₂
      rw [← pa ha, ← pa hb, ← pm, ← pm] at p₁
      exact ((Finset.prod_congr rfl fun i _ => by
        show k (n ≫ _ ≫ _) ^ _ = k (m.left ≫ _) ^ _
        rw [← Category.assoc, hn]).trans p₁).trans p₂.symm) (LB.pullGen P.L _ _ t n) (pullGen_isGen _ _ _ _ ht n)
  exact ⟨f ⁻¹ᵁ U, hU, exists_down ((isGen_iff w).1 gw') P.isLB P'.isLB t' ht'⟩

theorem exists_isActPull_isRosati : ∀ (O : Type) [CommRing O] (c : O →+* O) (S S' : Scheme.{0}) (f : S' ⟶ S)
    (P : Out.PolAV S) (j : OAct O P.A),
    IsRosati c P j → ∃ (P' : Out.PolAV S') (j' : OAct O P'.A) (ψ : P'.A.left ⟶ P.A.left),
      IsActPull j' j f ψ ∧ IsRosati c P' j' := by
  intro O _ c S S' f P j h
  have hp := exists_isActPull f j
  exact ⟨StrictPull.polPull P f, OAct.pullback f P.A j, pullback.fst P.A.hom f, hp, fun a =>
    rosatiAdj_of_isGrpPullback P (StrictPull.polPull P f) hp.1
      (PolBaseChange.lbIso_refl (StrictPull.polPull P f).isLB) (hp.2 a) (hp.2 (c a)) (h a)⟩

end GlobalTheory.TorusPart
