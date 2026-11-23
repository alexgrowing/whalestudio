import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem isPullback_of_open_part_eq_preimage :
    ∀ (S S₁ P G : Scheme.{0}) (p : P ⟶ S) (s : S₁ ⟶ S) (e : G ⟶ P) (c : G ⟶ S₁) (hw : e ≫ p = c ≫ s), IsOpenImmersion (Limits.pullback.lift e c hw) → ∀ V : P.Opens, (∀ w : ↥(Limits.pullback p s), Limits.pullback.fst p s w ∈ V ↔ w ∈ Set.range (Limits.pullback.lift e c hw)) → ∃ e' : G ⟶ V.toScheme, e' ≫ V.ι = e ∧ IsPullback e' c (V.ι ≫ p) s := by
  intro S S₁ P G p s e c hw hl V hV
  have hlf : Limits.pullback.lift e c hw ≫ Limits.pullback.fst p s = e :=
    Limits.pullback.lift_fst _ _ _
  have hls : Limits.pullback.lift e c hw ≫ Limits.pullback.snd p s = c :=
    Limits.pullback.lift_snd _ _ _
  generalize Limits.pullback.lift e c hw = l at hl hV hlf hls
  have hr : Set.range e ⊆ Set.range V.ι := by
    rintro _ ⟨g, rfl⟩
    rw [Scheme.Opens.range_ι]
    have h := (hV (l g)).mpr ⟨g, rfl⟩
    rw [← Scheme.Hom.comp_apply, hlf] at h
    exact h
  have he' : IsOpenImmersion.lift V.ι e hr ≫ V.ι = e := IsOpenImmersion.lift_fac _ _ _
  generalize IsOpenImmersion.lift V.ι e hr = e' at he'
  have hcomm : e' ≫ V.ι ≫ p = c ≫ s := by rw [← Category.assoc, he', hw]
  have hk : ∀ t : PullbackCone (V.ι ≫ p) s, ∃ q : t.pt ⟶ G,
      q ≫ l = Limits.pullback.lift (t.fst ≫ V.ι) t.snd
        ((Category.assoc _ _ _).trans t.condition) := by
    intro t
    refine ⟨IsOpenImmersion.lift l _ ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨x, rfl⟩
    refine (hV _).mp ?_
    rw [← Scheme.Hom.comp_apply, Limits.pullback.lift_fst, Scheme.Hom.comp_apply]
    exact (t.fst x).2
  choose q hq using hk
  refine ⟨e', he', ⟨hcomm⟩, ⟨PullbackCone.IsLimit.mk hcomm q ?_ ?_ ?_⟩⟩
  · intro t
    rw [← cancel_mono V.ι, Category.assoc, he', ← hlf, ← Category.assoc, hq,
      Limits.pullback.lift_fst]
  · intro t
    conv_lhs => rw [← hls]
    rw [← Category.assoc, hq, Limits.pullback.lift_snd]
  · intro t m h₁ h₂
    rw [← cancel_mono l, hq]
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hlf, Limits.pullback.lift_fst, ← h₁, Category.assoc, he']
    · rw [Category.assoc, hls, Limits.pullback.lift_snd, h₂]

end GlobalTheory.Desc
