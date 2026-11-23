import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueComapEqVanishingIdeal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.InvariantMorDescent

theorem exists_equalizer_ideal {Z Y S : Scheme.{0}} (z : Y ⟶ S) [IsSeparated z] (a b : Z ⟶ Y)
    (h : a ≫ z = b ≫ z) :
    ∃ I : Z.IdealSheafData, ∀ (T : Scheme.{0}) (t : T ⟶ Z), I ≤ t.ker ↔ t ≫ a = t ≫ b := by
  let i := pullback.fst (pullback.lift a b h) (pullback.diagonal z)
  have hi : i ≫ a = i ≫ b := by
    have c : i ≫ _ = _ := pullback.condition (f := pullback.lift a b h) (g := pullback.diagonal z)
    have c₁ := congrArg (· ≫ pullback.fst z z) c
    have c₂ := congrArg (· ≫ pullback.snd z z) c
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd] at c₁ c₂
    exact c₁.trans c₂.symm
  refine ⟨i.ker, fun T t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · rw [← IsClosedImmersion.lift_fac i t ht, Category.assoc, Category.assoc, hi]
  · have e : t ≫ pullback.lift a b h = (t ≫ a) ≫ pullback.diagonal z := by
      apply pullback.hom_ext
      · simp [pullback.lift_fst]
      · simp [pullback.lift_snd, ht]
    rw [← pullback.lift_fst t (t ≫ a) e]
    exact Scheme.Hom.le_ker_comp _ _

theorem fst_comp_eq_snd_comp {K L : Type} [Field K] [Field L] [Algebra K L] {G : Type*}
    (s : G → L →ₐ[K] L) (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    {X X' Y S : Scheme.{0}} {p : X ⟶ Spec (.of K)} {q : X' ⟶ Spec (.of L)} {π : X' ⟶ X}
    (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (z : Y ⟶ S) [IsSeparated z] (f : X' ⟶ Y) (u : X ⟶ S) (hu : f ≫ z = π ≫ u)
    (hf : ∀ g, GaloisDescent.twist H (s g) ≫ f = f) :
    pullback.fst π π ≫ f = pullback.snd π π ≫ f := by
  have hp : IsPullback (pullback.fst π π) (pullback.snd π π ≫ q) (π ≫ p)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    (IsPullback.of_hasPullback π π).paste_vert H
  obtain ⟨I, hI⟩ := exists_equalizer_ideal z (pullback.fst π π ≫ f) (pullback.snd π π ≫ f) (by
    rw [Category.assoc, Category.assoc, hu, pullback.condition_assoc])
  have h₂ : ∀ g, GaloisDescent.twist hp (s g) ≫ pullback.snd π π =
      pullback.snd π π ≫ GaloisDescent.twist H (s g) := fun g => by
    apply H.hom_ext
    · rw [Category.assoc, Category.assoc, GaloisDescent.twist_fst, ← pullback.condition,
        GaloisDescent.twist_fst_assoc]
    · rw [Category.assoc, Category.assoc, GaloisDescent.twist_snd, GaloisDescent.twist_snd,
        Category.assoc]
  obtain ⟨J, hJ, -⟩ := (GaloisDescent.idealSheaf_stable_iff_exists_comap hp s hs I).1 fun g => by
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
    refine (hI _ _).2 ?_
    rw [Category.assoc, Category.assoc, GaloisDescent.twist_fst_assoc, reassoc_of% (h₂ g), hf]
    exact (hI _ _).1 I.ker_subschemeι.ge
  have h₃ : I ≤ (pullback.diagonal π).ker := (hI _ _).2 (by simp)
  rw [← Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.le_map_iff_comap_le, ← hJ,
    ← Scheme.IdealSheafData.comap_comp, pullback.diagonal_fst,
    Scheme.IdealSheafData.comap_id, le_bot_iff] at h₃
  rw [h₃, Scheme.IdealSheafData.comap_bot] at hJ
  simpa using (hI _ (𝟙 _)).1 (hJ ▸ bot_le)

theorem existsUnique_desc : ∀ (K C : Type) [Field K] [CharZero K] [Field C] [IsAlgClosed C] [Algebra K C] (S : Scheme.{0}) (b : Sp K ⟶ S) (X Y : Over S), IsSeparated Y.hom → ∀ κ : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk b, κ.left = spMap (algebraMap K C) → ∀ f : Over.mk (spMap (algebraMap K C) ≫ b) ⊗ X ⟶ Y, (∀ (σ : C ≃ₐ[K] C) (s : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk (spMap (algebraMap K C) ≫ b)), s.left = spMap (σ : C →+* C) → s ▷ X ≫ f = f) → ∃! g : Over.mk b ⊗ X ⟶ Y, κ ▷ X ≫ g = f := by
  intro K C _ _ _ _ _ S b X Y hY κ hκ f hf
  have f₁ : Flat κ.left := by
    rw [hκ]
    change Flat (spMap (algebraMap K C))
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField K) _
  have f₂ : Surjective κ.left := ⟨fun y =>
    ⟨(default : PrimeSpectrum C), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have f₃ : QuasiCompact κ.left := by
    rw [hκ]
    exact inferInstanceAs (QuasiCompact (spMap (algebraMap K C)))
  have H : IsPullback (κ ▷ X).left (fst _ X).left (fst (Over.mk b) X).left
      (Spec.map (CommRingCat.ofHom (algebraMap K C))) := by
    have := (SemiRigid.isPullback_whiskerRight κ X).flip
    rw [hκ] at this
    exact this
  have key := fst_comp_eq_snd_comp (fun σ : C ≃ₐ[K] C => σ.toAlgHom)
    GaloisDescent.mem_range_algebraMap_of_forall_algEquiv H Y.hom f.left (Over.mk b ⊗ X).hom
    ((Over.w f).trans (Over.w (κ ▷ X)).symm) fun σ => by
      have hσ : spMap (σ : C →+* C) ≫ spMap (algebraMap K C) = spMap (algebraMap K C) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact σ.toAlgHom.comp_algebraMap
      let s : Over.mk (spMap (algebraMap K C) ≫ b) ⟶ Over.mk (spMap (algebraMap K C) ≫ b) :=
        Over.homMk (spMap (σ : C →+* C)) (by
          change spMap (σ : C →+* C) ≫ spMap (algebraMap K C) ≫ b = spMap (algebraMap K C) ≫ b
          rw [reassoc_of% hσ])
      have hsκ : s ≫ κ = κ := Over.OverMorphism.ext (by
        rw [Over.comp_left, hκ]; exact hσ)
      have e : GaloisDescent.twist H σ.toAlgHom = (s ▷ X).left := by
        apply H.hom_ext
        · rw [GaloisDescent.twist_fst, ← Over.comp_left, ← comp_whiskerRight, hsκ]
        · rw [GaloisDescent.twist_snd]
          exact congrArg (·.left) (whiskerRight_fst s X).symm
      rw [e]
      exact congrArg (·.left) (hf σ s rfl)
  obtain ⟨g, hg⟩ := SemiRigid.exists_desc (κ ▷ X) f fun Z a c h => by
    have h' : a.left ≫ (κ ▷ X).left = c.left ≫ (κ ▷ X).left := congrArg (·.left) h
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, ← pullback.lift_fst a.left c.left h', Category.assoc, key,
      pullback.lift_snd_assoc]
  have := SemiRigid.epi_of_fpqc (κ ▷ X)
  exact ⟨g, hg, fun g' hg' => (cancel_epi (κ ▷ X)).1 (hg'.trans hg.symm)⟩

end GlobalTheory.InvariantMorDescent
