import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace

noncomputable section

universe u

theorem nonempty_pullback_iso_iff {W X : Scheme.{u}} (q : W ⟶ X) (U : X.Opens)
    (a : W ⟶ U.toScheme) (ha : a ≫ U.ι = q) (E' : U.toScheme.Modules) (E : W.Modules) :
    Nonempty ((Scheme.Modules.pullback a).obj E' ≅ E) ↔
      Nonempty ((Scheme.Modules.pullback (q ∣_ U)).obj E' ≅
        (Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj E) := by
  have h1 : (q ⁻¹ᵁ U).ι ≫ a = q ∣_ U := by
    rw [← cancel_mono U.ι, Category.assoc, ha, morphismRestrict_ι]
  have hrange : Set.range (𝟙 W : W ⟶ W) ⊆ Set.range (q ⁻¹ᵁ U).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hw : U.ι (a w) ∈ Set.range U.ι := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.comp_apply, ha] at hw
    exact hw
  let s : W ⟶ (q ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (q ⁻¹ᵁ U).ι (𝟙 W) hrange
  have hs : s ≫ (q ⁻¹ᵁ U).ι = 𝟙 W := IsOpenImmersion.lift_fac _ _ _
  have h2 : s ≫ q ∣_ U = a := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hs,
      Category.id_comp, ha]
  constructor
  · rintro ⟨γ⟩
    exact ⟨GroundTheory.Heights₂.Heights.Model.pullbackCompIso h1 γ⟩
  · rintro ⟨δ⟩
    exact ⟨GroundTheory.Heights₂.Heights.Model.pullbackCompIso h2 δ ≪≫
      (GroundTheory.Heights₂.Heights.Model.pullbackCompIso hs (Iso.refl _)).symm ≪≫
        (Scheme.Modules.pullbackId W).app E⟩

def SpreadBundle.Along (X : Scheme.{0}) (p : Nat.Primes)
    (g : Spec (.of (ZLoc p)) ⟶ Spec (.of ℤ)) : Prop :=
  ∀ E : (pullback (toSpecZ X) g).Modules, IsVectorBundle E →
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ m' : ℕ, m ∣ m' → ¬ (p : ℕ) ∣ m' →
      ∃ E' : (invOpen X m').toScheme.Modules, IsVectorBundle E' ∧
        Nonempty ((Scheme.Modules.pullback (pullback.fst (toSpecZ X) g ∣_ invOpen X m')).obj E' ≅
          (Scheme.Modules.pullback (pullback.fst (toSpecZ X) g ⁻¹ᵁ invOpen X m').ι).obj E)

theorem SpreadBundle.along_congr (X : Scheme.{0}) (p : Nat.Primes)
    {g g' : Spec (.of (ZLoc p)) ⟶ Spec (.of ℤ)} (h : g = g') :
    SpreadBundle.Along X p g ↔ SpreadBundle.Along X p g' := by
  subst h
  rfl

theorem SpreadBundle.model_iff_along (X : Scheme.{0}) (p : Nat.Primes) :
    (∀ E : (GroundTheory.Heights₂.Heights.Model.baseChange (toSpecZ X) (ZLoc p)).Modules,
      GroundTheory.Heights₂.Heights.Model.IsVectorBundle E →
      ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, m ∣ n → ∀ hn : ¬ ((p : ℕ) : ℤ) ∣ (n : ℤ),
        ∃ E' : (GroundTheory.Heights₂.Heights.Model.invOpen (toSpecZ X) n : Scheme.{0}).Modules,
          GroundTheory.Heights₂.Heights.Model.IsVectorBundle E' ∧
          Nonempty ((Scheme.Modules.pullback (GroundTheory.Heights₂.Heights.Model.toInvOpen (toSpecZ X)
            (ZLoc p) n (GroundTheory.Heights₂.Heights.Model.isUnit_intCast_zLoc p n hn))).obj E' ≅ E)) ↔
      SpreadBundle.Along X p (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZLoc p)))) := by
  refine forall_congr' fun E => imp_congr_right fun _ => exists_congr fun m =>
    and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun n =>
      imp_congr_right fun _ => ?_
  have hdvd : ¬ ((p : ℕ) : ℤ) ∣ (n : ℤ) ↔ ¬ (p : ℕ) ∣ n := by
    rw [Int.natCast_dvd_natCast]
  constructor
  · intro h hn
    obtain ⟨E', hE', hiso⟩ := h (hdvd.2 hn)
    exact ⟨E', hE', (nonempty_pullback_iso_iff _ _ _
      (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι _ _ _ _) E' E).1 hiso⟩
  · intro h hn
    obtain ⟨E', hE', hiso⟩ := h (hdvd.1 hn)
    exact ⟨E', hE', (nonempty_pullback_iso_iff _ _ _
      (GroundTheory.Heights₂.Heights.Model.toInvOpen_ι _ _ _ _) E' E).2 hiso⟩

theorem SpreadBundle.equiv :
    GroundTheory.Heights₂.Heights.Model.SpreadBundle.Statement ↔ SpreadBundle.Statement := by
  constructor
  · intro h X hX p
    obtain ⟨h1, h2⟩ := hX
    exact (SpreadBundle.along_congr X p (specZ_hom_ext _ _)).1
      ((SpreadBundle.model_iff_along X p).1 (h X (toSpecZ X) p))
  · intro h X f _ _ p
    obtain rfl := specZ_hom_ext f (toSpecZ X)
    exact (SpreadBundle.model_iff_along X p).2
      ((SpreadBundle.along_congr X p (specZ_hom_ext _ _)).2 (h X ⟨‹_›, ‹_›⟩ p))

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
