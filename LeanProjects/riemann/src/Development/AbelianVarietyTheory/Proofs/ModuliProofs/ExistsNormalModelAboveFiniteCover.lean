import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalFiniteModelOfFiniteOverOpen
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem Cpt.exists_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (C : Cpt c t β) (b : O →+* O') (k : F →+* F') (r : U' ⟶ U) (hr : r ≫ c = c' ≫ spMap k) (ν : SABMap t' t r), IsDedFrac β → IsDedFrac β' → β'.comp b = k.comp β → Geo.Tor.IsNormalScheme U' → IsFinite (pullback.lift r c' hr) → ∃ C' : Cpt c' t' β', Nonempty (C'.Above C b r ν) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' C b k r hr ν _ hD hβ hN hfin
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hD
  let _ := β'.toAlgebra
  have hsq : spMap β' ≫ spMap b = spMap k ≫ spMap β := by rw [← spMap_comp, ← spMap_comp, hβ]
  have hjs : C.j ≫ C.s = c ≫ spMap β := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  have hopen := C.jQ_open
  let s₁ := pullback.snd C.s (spMap b)
  let q : pullback s₁ (spMap β') ⟶ pullback C.s (spMap β) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ spMap k) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hsq,
        Category.assoc])
  have q₁ : q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
  have q₂ : q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap k := pullback.lift_snd _ _ _
  have hq : IsPullback q (pullback.snd s₁ (spMap β')) (pullback.snd C.s (spMap β)) (spMap k) := by
    refine IsPullback.of_right ?_ q₂ (IsPullback.of_hasPullback C.s (spMap β))
    rw [q₁, ← hsq]
    exact (IsPullback.of_hasPullback s₁ (spMap β')).paste_horiz (IsPullback.of_hasPullback C.s (spMap b))
  let f : U' ⟶ pullback C.s (spMap b) := pullback.lift (r ≫ C.j) (c' ≫ spMap β') (by
    rw [Category.assoc, hjs, ← Category.assoc, hr, Category.assoc, Category.assoc, hsq])
  have f₁ : f ≫ pullback.fst _ _ = r ≫ C.j := pullback.lift_fst _ _ _
  let u : U' ⟶ pullback s₁ (spMap β') := pullback.lift f c' (pullback.lift_snd _ _ _)
  have u₁ : u ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have u₂ : u ≫ pullback.snd _ _ = c' := pullback.lift_snd _ _ _
  have hu : r ≫ C.jQ = u ≫ q := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, q₁, ← Category.assoc u, u₁, f₁, Cpt.j]
    · rw [Category.assoc, Category.assoc, q₂, ← Category.assoc u, u₂, C.jQ_over, hr]
  let g := pullback.snd C.jQ q
  let v : U' ⟶ pullback C.jQ q := pullback.lift r u hu
  have v₁ : v ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  have v₂ : v ≫ g = u := pullback.lift_snd _ _ _
  have hp : IsPullback (pullback.fst C.jQ q) (g ≫ pullback.snd _ _) c (spMap k) := by
    have := (IsPullback.of_hasPullback C.jQ q).paste_vert hq
    rwa [C.jQ_over] at this
  have hv : IsFinite v := by
    have e : v = pullback.lift r c' hr ≫ hp.isoPullback.inv := by
      rw [Iso.eq_comp_inv]
      apply pullback.hom_ext
      · rw [Category.assoc, hp.isoPullback_hom_fst, v₁, pullback.lift_fst]
      · rw [Category.assoc, hp.isoPullback_hom_snd, ← Category.assoc, v₂, u₂, pullback.lift_snd]
    rw [e]; infer_instance
  have hW : (v ≫ g.isoOpensRange.hom) ≫ g.opensRange.ι = u := by
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, v₂]
  obtain ⟨Y, π, jQ, hπ, hY, hproj, hflat, j₂, j₁, jo, jd, jr⟩ :=
    GlobalTheory.exists_normal_finite_model_of_finite_over_open O' F' _ U' s₁ c' f g.opensRange (v ≫ g.isoOpensRange.hom)
      (GlobalTheory.ProjSpace.isProjOver_pullback_snd b C.proj) hN inferInstance
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans u₁)
      (by rw [← Category.assoc]; exact (congrArg (· ≫ _) hW).trans u₂)
  obtain ⟨_, _, _, _, _, mu, -⟩ := sabPull Out.CubePf.cubePull (π ≫ pullback.fst C.s (spMap b)) C.t
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m ν
  have hj : (jQ ≫ pullback.fst (π ≫ s₁) (spMap β')) ≫ π ≫ pullback.fst C.s (spMap b) =
      r ≫ C.jQ ≫ pullback.fst _ _ := by
    refine Eq.trans ?_ f₁
    rw [← j₁]
    simp only [Category.assoc]
  obtain ⟨n', hn'⟩ : ∃ n' : SABMap t' C.t ((jQ ≫ pullback.fst (π ≫ s₁) (spMap β')) ≫ π ≫ pullback.fst C.s (spMap b)),
      n'.φ = ν.φ ≫ C.m.φ := by
    rw [hj]; exact ⟨n, hn⟩
  obtain ⟨m, hm⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mu n'
  have hg : ∀ p, p ∈ g.opensRange ↔ pullback.fst C.s (spMap b) (pullback.fst s₁ (spMap β') p) ∈ abLocus C.t.G := by
    intro p
    have e : pullback.fst C.s (spMap b) (pullback.fst s₁ (spMap β') p) = pullback.fst C.s (spMap β) (q p) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, q₁]
    rw [e]
    change p ∈ Set.range (pullback.snd C.jQ q) ↔ q p ∈ pullback.fst C.s (spMap β) ⁻¹' abLocus C.t.G
    rw [C.ab_gen, Scheme.Pullback.range_snd]
    rfl
  refine ⟨⟨Y, π ≫ s₁, hY, hproj, hflat, jQ, j₂, jo, jd, _, m, ?_⟩,
    ⟨⟨π ≫ pullback.fst _ _, ?_, ?_, mu, hj, hm.symm.trans hn'⟩⟩⟩
  · ext y
    refine Iff.trans ?_ (jr y).symm
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne C.t.semi mu.cart.1, Scheme.Hom.comp_apply]
    constructor
    · intro h
      let w : pullback (π ≫ s₁) (spMap β') ⟶ pullback s₁ (spMap β') :=
        pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
      have hw : pullback.fst s₁ (spMap β') (w y) = π (pullback.fst (π ≫ s₁) (spMap β') y) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
      refine ⟨⟨w y, (hg _).2 (by rw [hw]; exact h)⟩, ?_⟩
      exact (Scheme.Hom.comp_apply _ _ _).trans hw
    · rintro ⟨p, hp⟩
      replace hp := (Scheme.Hom.comp_apply _ _ _).symm.trans hp
      have := (hg p.1).1 p.2
      exact (congrArg (fun z => pullback.fst C.s (spMap b) z ∈ abLocus C.t.G) hp).mp this
  · simp only [Category.assoc, s₁, pullback.condition]
  · have key : ∀ h, IsFinite (pullback.lift (π ≫ pullback.fst C.s (spMap b)) (π ≫ s₁) h) := fun h => by
      have e : pullback.lift (π ≫ pullback.fst C.s (spMap b)) (π ≫ s₁) h = π := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
        · rw [pullback.lift_snd]
      rw [e]; exact hπ
    exact key _

end GlobalTheory.Models
