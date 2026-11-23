import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RingHomFlatCodescendsAlongFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpObjOfDenseOpen

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ExtDescent

variable {S S₀ : Scheme.{0}} {f : S ⟶ S₀}

theorem hom_ext_of_points [Flat f] [Surjective f] {X Y : Over S₀} {a b : X ⟶ Y}
    (h : ∀ (T : Over S) (t : Over.mk (T.hom ≫ f) ⟶ X), t ≫ a = t ≫ b) : a = b := by
  apply Over.OverMorphism.ext
  haveI := Flat.epi_of_flat_of_surjective (pullback.fst X.hom f)
  rw [← cancel_epi (pullback.fst X.hom f)]
  exact congrArg (fun z => z.left) (h (Over.mk (pullback.snd X.hom f))
    (Over.homMk (pullback.fst X.hom f) (by simpa using pullback.condition)))

theorem isMonHom_of_grpPullback [Flat f] [Surjective f] {X Y : Over S} {X₀ Y₀ : Over S₀}
    [GrpObj X] [GrpObj Y] [GrpObj X₀] [GrpObj Y₀] {φ : X.left ⟶ X₀.left} {ψ : Y.left ⟶ Y₀.left}
    (hX : IsGrpPullback X X₀ f φ) (hY : IsGrpPullback Y Y₀ f ψ) (g : X ⟶ Y) (g₀ : X₀ ⟶ Y₀)
    (w : φ ≫ g₀.left = g.left ≫ ψ) [IsMonHom g] : IsMonHom g₀ := by
  have pa : ∀ {T : Over S} (x : T ⟶ X), pushHom hX T x ≫ g₀ = pushHom hY T (x ≫ g) := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, w, Category.assoc])
  have hm : μ[X₀] ≫ g₀ = (g₀ ⊗ₘ g₀) ≫ μ := by
    refine hom_ext_of_points (f := f) fun T t => ?_
    obtain ⟨x, hx⟩ := GrpDense.pushPt_surjective hX.1 T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := GrpDense.pushPt_surjective hX.1 T (t ≫ snd _ _)
    obtain rfl : t = lift (pushHom hX T x) (pushHom hX T y) :=
      CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst]; exact hx.symm)
        (by rw [lift_snd]; exact hy.symm)
    rw [← Category.assoc, ← Hom.mul_def, ← map_mul, pa, lift_map_assoc, ← Hom.mul_def, pa, pa,
      ← map_mul, MonObj.mul_comp]
  refine ⟨?_, hm⟩
  have e : (η[X₀] ≫ g₀) * (η[X₀] ≫ g₀) = η[X₀] ≫ g₀ := by
    rw [Hom.mul_def, ← lift_map, Category.assoc, ← hm, ← Category.assoc]
    congr 1
    simpa [Hom.mul_def, Hom.one_def] using _root_.mul_one (1 : 𝟙_ (Over S₀) ⟶ X₀)
  have e' : η[X₀] ≫ g₀ = 1 := by simpa using e
  rw [e', Hom.one_def]; simp

theorem unit_comm {X : Over S} {X₀ : Over S₀} [GrpObj X] [GrpObj X₀] {φ : X.left ⟶ X₀.left}
    (h : IsGrpPullback X X₀ f φ) : f ≫ (η[X₀]).left = (η[X]).left ≫ φ := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S))))
  have e₁ : (1 : 𝟙_ (Over S) ⟶ X) = η[X] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine Eq.symm (e.trans ?_)
  show (toUnit _ ≫ η[X₀]).left = _
  simp

theorem fpqc_of_isPullback [Flat f] [Surjective f] [QuasiCompact f] {X X₀ : Scheme.{0}} {p : X ⟶ X₀}
    {s : X ⟶ S} {s₀ : X₀ ⟶ S₀} (h : IsPullback p s s₀ f) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) p :=
  ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›,
    MorphismProperty.of_isPullback (P := @Flat) h.flip ‹_›⟩,
    MorphismProperty.of_isPullback (P := @QuasiCompact) h.flip ‹_›⟩

theorem isPullback_of_baseChange [Flat f] [Surjective f] [QuasiCompact f] {T G B T₀ G₀ B₀ : Scheme.{0}}
    {i : T ⟶ G} {t : T ⟶ S} {q : G ⟶ B} {e : S ⟶ B} (H : IsPullback i t q e)
    {i₀ : T₀ ⟶ G₀} {t₀ : T₀ ⟶ S₀} {q₀ : G₀ ⟶ B₀} {e₀ : S₀ ⟶ B₀}
    {τ : T ⟶ T₀} {g : G ⟶ G₀} {φ : B ⟶ B₀} (hτ : IsPullback τ t t₀ f) (hγ : IsPullback g q q₀ φ)
    (hi : τ ≫ i₀ = i ≫ g) (he : f ≫ e₀ = e ≫ φ) : IsPullback i₀ t₀ q₀ e₀ := by
  haveI : Flat τ := (fpqc_of_isPullback hτ).1.2
  haveI : Surjective τ := (fpqc_of_isPullback hτ).1.1
  haveI := Flat.epi_of_flat_of_surjective τ
  have w : i₀ ≫ q₀ = t₀ ≫ e₀ := by
    rw [← cancel_epi τ, reassoc_of% hi, hγ.w, reassoc_of% H.w, reassoc_of% hτ.w, he]
  let c : T₀ ⟶ pullback q₀ e₀ := pullback.lift i₀ t₀ w
  have c₁ : c ≫ pullback.fst q₀ e₀ = i₀ := pullback.lift_fst _ _ _
  have c₂ : c ≫ pullback.snd q₀ e₀ = t₀ := pullback.lift_snd _ _ _
  have hp : IsPullback (τ ≫ c) t (pullback.snd q₀ e₀) f := by
    refine IsPullback.of_right ?_ (by rw [Category.assoc, c₂, hτ.w]) (IsPullback.of_hasPullback q₀ e₀)
    rw [Category.assoc, c₁, hi, he]
    exact H.paste_horiz hγ
  have hc : IsPullback τ (𝟙 T) c (τ ≫ c) := by
    refine IsPullback.of_bot ?_ (by simp) hp
    rw [c₂, Category.id_comp]
    exact hτ
  haveI : IsIso c := MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{0})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hc.flip
    (fpqc_of_isPullback hp) (inferInstanceAs (IsIso (𝟙 T)))
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) c₁ c₂

end GlobalTheory.ExtDescent

namespace GlobalTheory

open ExtDescent

theorem splitTorus_extension_descends :
    ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [GrpObj B₀] (X : Type) [AddCommGroup X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap β) φG → IsGrpPullback B B₀ (spMap β) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G) (q₀ : G₀ ⟶ B₀) (i₀ : splitTorus (Sp k) X ⟶ G₀), φG ≫ q₀.left = q.left ≫ φ → GlobalTheory.SplitTorus.bcMap (spMap β) X ≫ i₀.left = i.left ≫ φG → IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → IsMonHom q₀ ∧ Flat q₀.left ∧ Surjective q₀.left ∧ QuasiCompact q₀.left ∧ IsMonHom i₀ ∧ IsPullback i₀ (toUnit _) q₀ (η[B₀] : 𝟙_ _ ⟶ B₀) := by
  intro k K _ _ β G B _ _ G₀ B₀ _ _ X _ φG φ hG hB q i q₀ i₀ wq wi hq hfl hsu hqc hi H
  haveI h₁ : Flat (spMap β) := inferInstance
  haveI h₂ : Surjective (spMap β) := inferInstance
  haveI h₃ : QuasiCompact (spMap β) := inferInstance
  have hγ : IsPullback φG q.left q₀.left φ := by
    refine IsPullback.of_bot ?_ wq hB.1
    rw [Over.w, Over.w]
    exact hG.1
  have hφ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) φ :=
    fpqc_of_isPullback hB.1
  haveI := flat_descendsAlong_fpqc
  haveI := quasiCompact_descendsAlong_fpqc.{0}
  have hT := SplitTorus.isGrpPullback_bcMap (spMap β) X
  refine ⟨isMonHom_of_grpPullback hG hB q q₀ wq,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat) hγ.flip hφ hfl,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective) hγ.flip hφ hsu,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @QuasiCompact) hγ.flip hφ hqc,
    isMonHom_of_grpPullback hT hG i i₀ wi, ?_⟩
  have H' : IsPullback i.left (splitTorus (Sp K) X).hom q.left (η[B]).left :=
    H.map (Over.forget _)
  have H₀ := isPullback_of_baseChange H' hT.1 hγ wi (unit_comm hB)
  exact IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext H₀.w) H₀

end GlobalTheory
