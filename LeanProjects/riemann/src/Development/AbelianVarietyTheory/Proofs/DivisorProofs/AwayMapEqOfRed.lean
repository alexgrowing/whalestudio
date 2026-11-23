import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SecGlue.Red

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]; exact Spec.map_id _

theorem away_ext {R T : Type} [CommRing R] [CommRing T] (a : R) (φ ψ : Localization.Away a →+* T)
    (h : φ.comp (algebraMap R _) = ψ.comp (algebraMap R _)) : φ = ψ :=
  IsLocalization.ringHom_ext (Submonoid.powers a) h

theorem isUnit_of_away {R T : Type} [CommRing R] [CommRing T] [Algebra R T] (a : R)
    (ρ : Localization.Away a →+* T) (hρ : ρ.comp (algebraMap R _) = algebraMap R T) :
    IsUnit (algebraMap R T a) := by
  rw [← hρ]; exact (IsLocalization.Away.algebraMap_isUnit a).map ρ

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

abbrev redI (π : R →+* R₀) (S : Type) [CommRing S] [Algebra R S] : Ideal S :=
  (RingHom.ker π).map (algebraMap R S)

def redPsi (π : R →+* R₀) (hπ : Function.Surjective π) (S : Type) [CommRing S] [Algebra R S] :
    R₀ →+* S ⧸ redI π S :=
  π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
    ⟨(Ideal.Quotient.mk (redI π S)).comp (algebraMap R S), fun x hx => by
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hx⟩

theorem redPsi_comp (π : R →+* R₀) (hπ : Function.Surjective π) (S : Type) [CommRing S]
    [Algebra R S] : (redPsi π hπ S).comp π = (Ideal.Quotient.mk (redI π S)).comp (algebraMap R S) :=
  RingHom.liftOfRightInverse_comp _ _ _ _

theorem ker_mk_sq (π : R →+* R₀) (h : RingHom.ker π ^ 2 = ⊥) (S : Type) [CommRing S]
    [Algebra R S] : RingHom.ker (Ideal.Quotient.mk (redI π S)) ^ 2 = ⊥ := by
  rw [Ideal.mk_ker, ← Ideal.map_pow, h, Ideal.map_bot]

def IsRed (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}} (g₀ : Sp R₀ ⟶ Y)
    (S : Type) [CommRing S] [Algebra R S] (u : Sp S ⟶ Y) : Prop :=
  spMap (Ideal.Quotient.mk (redI π S)) ≫ u = spMap (redPsi π hπ S) ≫ g₀

theorem IsRed.eq {π : R →+* R₀} {hπ : Function.Surjective π} {Y : Scheme.{0}} {g₀ : Sp R₀ ⟶ Y}
    {S : Type} [CommRing S] [Algebra R S] {u v : Sp S ⟶ Y} (hu : IsRed π hπ g₀ S u)
    (hv : IsRed π hπ g₀ S v) :
    spMap (Ideal.Quotient.mk (redI π S)) ≫ u = spMap (Ideal.Quotient.mk (redI π S)) ≫ v :=
  hu.trans hv.symm

theorem isRed_of_away (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}}
    (g₀ : Sp R₀ ⟶ Y) (a : R) (u : Sp (Localization.Away a) ⟶ Y)
    (hu : spMap (Localization.awayMap π a) ≫ u =
      spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀)
    (S : Type) [CommRing S] [Algebra R S] (ρ : Localization.Away a →+* S)
    (hρ : ρ.comp (algebraMap R _) = algebraMap R S) : IsRed π hπ g₀ S (spMap ρ ≫ u) := by
  have hunit : IsUnit (redPsi π hπ S (π a)) := by
    have e : redPsi π hπ S (π a) = Ideal.Quotient.mk (redI π S) (algebraMap R S a) := by
      rw [← RingHom.comp_apply (redPsi π hπ S) π, redPsi_comp, RingHom.comp_apply]
    rw [e]; exact (isUnit_of_away a ρ hρ).map _
  let lam := IsLocalization.Away.lift (S := Localization.Away (π a)) (π a) hunit
  have key : (Ideal.Quotient.mk (redI π S)).comp ρ = lam.comp (Localization.awayMap π a) := by
    apply away_ext a
    rw [RingHom.comp_assoc, hρ, RingHom.comp_assoc]
    have e1 : (Localization.awayMap π a).comp (algebraMap R (Localization.Away a)) =
        (algebraMap R₀ (Localization.Away (π a))).comp π := IsLocalization.map_comp _
    rw [e1, ← RingHom.comp_assoc, IsLocalization.Away.lift_comp, redPsi_comp]
  unfold IsRed
  rw [← Category.assoc, ← spMap_comp, key, spMap_comp, Category.assoc, hu, ← Category.assoc,
    ← spMap_comp, IsLocalization.Away.lift_comp]

theorem isRed_self (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}}
    (g₀ : Sp R₀ ⟶ Y) (a : R) (u : Sp (Localization.Away a) ⟶ Y)
    (hu : spMap (Localization.awayMap π a) ≫ u =
      spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀) :
    IsRed π hπ g₀ (Localization.Away a) u := by
  have := isRed_of_away π hπ g₀ a u hu (Localization.Away a) (RingHom.id _) rfl
  rwa [spMap_id, Category.id_comp] at this

theorem isRed_comp (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}}
    (g₀ : Sp R₀ ⟶ Y) {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
    (σ : S →+* S') (hσ : σ.comp (algebraMap R S) = algebraMap R S') {u : Sp S ⟶ Y}
    (hu : IsRed π hπ g₀ S u) : IsRed π hπ g₀ S' (spMap σ ≫ u) := by
  have hle : redI π S ≤ (redI π S').comap σ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap, ← RingHom.comp_apply σ, hσ]
    exact Ideal.mem_map_of_mem _ hx
  have h1 : (Ideal.Quotient.mk (redI π S')).comp σ =
      (Ideal.quotientMap (redI π S') σ hle).comp (Ideal.Quotient.mk (redI π S)) :=
    (Ideal.quotientMap_comp_mk hle).symm
  have h2 : (Ideal.quotientMap (redI π S') σ hle).comp (redPsi π hπ S) = redPsi π hπ S' := by
    apply RingHom.ext; intro y; obtain ⟨x, rfl⟩ := hπ y
    rw [RingHom.comp_apply, ← RingHom.comp_apply (redPsi π hπ S), redPsi_comp,
      ← RingHom.comp_apply (redPsi π hπ S'), redPsi_comp, RingHom.comp_apply, RingHom.comp_apply,
      Ideal.quotientMap_mk, ← RingHom.comp_apply σ, hσ]
  unfold IsRed at *
  rw [← Category.assoc, ← spMap_comp, h1, spMap_comp, Category.assoc, hu, ← Category.assoc,
    ← spMap_comp, h2]

theorem awayMap_eq_of_red (π : R →+* R₀) {Y : Scheme.{0}} (a : R)
    (u v : Sp (Localization.Away a) ⟶ Y)
    (h : spMap (Ideal.Quotient.mk (redI π (Localization.Away a))) ≫ u =
      spMap (Ideal.Quotient.mk (redI π (Localization.Away a))) ≫ v) :
    spMap (Localization.awayMap π a) ≫ u = spMap (Localization.awayMap π a) ≫ v := by
  have H : ∀ x ∈ redI π (Localization.Away a), Localization.awayMap π a x = 0 := by
    intro x hx
    have hle : redI π (Localization.Away a) ≤ RingHom.ker (Localization.awayMap π a) := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply,
        show (Localization.awayMap π a).comp (algebraMap R (Localization.Away a)) =
          (algebraMap R₀ (Localization.Away (π a))).comp π from IsLocalization.map_comp _,
        RingHom.comp_apply, RingHom.mem_ker.1 hy, map_zero]
    exact hle hx
  have e : Localization.awayMap π a =
      (Ideal.Quotient.lift _ (Localization.awayMap π a) H).comp (Ideal.Quotient.mk _) := by
    ext x; simp
  rw [e, spMap_comp, Category.assoc, Category.assoc, h]

end GlobalTheory.SecGlue.Red
