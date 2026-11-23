import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.RegDenom

theorem exists_denom_of_injective {R K B S : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Finite S]
    (ρ : R →+* B) (v : S → B →+* K) (hv : Function.Injective v)
    (hρ : ∀ i r, v i (ρ r) = algebraMap R K r) (f : S → K) :
    ∃ d : R, d ≠ 0 ∧ ∃ b : B, ∀ i, v i b = algebraMap R K d * f i := by
  classical
  cases nonempty_fintype S
  have inj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  let W : Submodule K (S → K) := Submodule.span K (Set.range fun b : B => fun i => v i b)
  have hW : W = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr hne)
    have hm : Function.Injective (fun i : S => ((v i : B →+* K) : B →* K)) := by
      intro i j hij
      apply hv
      ext b
      exact DFunLike.congr_fun hij b
    have hli : LinearIndependent K (fun i : S => (fun b => v i b : B → K)) :=
      (linearIndependent_monoidHom B K).comp _ hm
    have hc : ∀ i, φ (Pi.single i 1) = 0 := by
      have h0 := Fintype.linearIndependent_iff.mp hli (fun i => φ (Pi.single i 1)) (by
        funext b
        have hb : φ (fun i => v i b) = 0 := hle (Submodule.subset_span ⟨b, rfl⟩)
        have hx : (fun i => v i b) = ∑ i, (v i b) • (Pi.single i (1 : K) : S → K) := by
          funext j
          simp [Finset.sum_apply, Pi.single_apply]
        rw [hx, map_sum] at hb
        simp only [map_smul, smul_eq_mul] at hb
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← hb]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
      exact h0
    apply hφ
    ext i
    simpa using hc i

  have key : ∀ x ∈ W, ∃ d : R, d ≠ 0 ∧ ∃ b : B, ∀ i, v i b = algebraMap R K d * x i := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨b, rfl⟩ := h
      exact ⟨1, one_ne_zero, b, fun i => by simp⟩
    | zero => exact ⟨1, one_ne_zero, 0, fun i => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨d, hd, b, hb⟩ := hx
      obtain ⟨e, he, c, hc⟩ := hy
      refine ⟨d * e, mul_ne_zero hd he, ρ e * b + ρ d * c, fun i => ?_⟩
      simp only [map_add, map_mul, hρ, hb, hc, Pi.add_apply]
      ring
    | smul k x _ hx =>
      obtain ⟨d, hd, b, hb⟩ := hx
      obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) k
      have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
      have hcK : algebraMap R K c ≠ 0 := fun h => hc0 (inj (by simpa using h))
      refine ⟨c * d, mul_ne_zero hc0 hd, ρ a * b, fun i => ?_⟩
      simp only [map_mul, hρ, hb, Pi.smul_apply, smul_eq_mul]
      field_simp
  exact key f (hW ▸ Submodule.mem_top)

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

def valHom {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valHom_apply {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) : valHom x U h s = valAt x U h s := rfl

theorem eq_of_valHom_eq {B : Type} [CommRing B] {X : Scheme.{0}} {x y : Spec (CommRingCat.of B) ⟶ X} {U : X.Opens}
    (hU : IsAffineOpen U) (hx : ⊤ ≤ x ⁻¹ᵁ U) (hy : ⊤ ≤ y ⁻¹ᵁ U) (e : valHom x U hx = valHom y U hy) : x = y := by
  have ha : x.appLE U ⊤ hx = y.appLE U ⊤ hy := by
    ext s
    have := DFunLike.congr_fun e s
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).hom).1 this
  have htop : IsAffineOpen (⊤ : (Spec (CommRingCat.of B)).Opens) := isAffineOpen_top _
  have h1 := hU.SpecMap_appLE_fromSpec x htop hx
  have h2 := hU.SpecMap_appLE_fromSpec y htop hy
  rw [ha, h2] at h1
  have : IsIso htop.fromSpec := by
    rw [show htop = isAffineOpen_top _ from rfl, IsAffineOpen.fromSpec_top]
    infer_instance
  exact (cancel_epi htop.fromSpec).mp h1.symm

theorem le_preimage_top {X Y : Scheme.{0}} (p : X ⟶ Y) (U : X.Opens) : U ≤ p ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial

def structHom {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (le_preimage_top p U)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem valHom_structHom {B : Type} [CommRing B] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R))
    (i : R →+* B) (x : Spec (CommRingCat.of B) ⟶ X) (hx : x ≫ p = Spec.map (CommRingCat.ofHom i))
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (r : R) : valHom x U h (structHom p U r) = i r := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U (le_preimage_top p U) ≫ x.appLE U ⊤ h ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom = CommRingCat.ofHom i := by
    have e1 : p.appLE ⊤ U (le_preimage_top p U) ≫ x.appLE U ⊤ h = (x ≫ p).appTop := by
      rw [Scheme.Hom.appLE_comp_appLE]
      simp only [Scheme.Hom.appLE, Scheme.Hom.comp_appTop, Scheme.Hom.appTop]
      refine Eq.trans (congrArg _ ?_) (Category.comp_id _)
      exact (Spec (CommRingCat.of B)).presheaf.map_id _
    rw [reassoc_of% e1, hx, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congr($(e).hom r)

theorem exists_denom_regularAt : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
    (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left),
    ∃ d : R, d ≠ 0 ∧ Γ.RegularAt (fun t => algebraMap R _ d * f t) g := by
  intro R _ _ T _ _ Γ f g
  obtain ⟨U, hU, hg, -⟩ := exists_isAffineOpen_mem_and_subset (x := g) (U := ⊤) trivial
  let S := {t : T // ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U}
  let v : S → Γ(Γ.G.left, U) →+* FractionRing R := fun t => valHom (Γ.pt t.1).left U t.2
  have hv : Function.Injective v := by
    intro s t e
    have hst := eq_of_valHom_eq hU s.2 t.2 e
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := inferInstance
    exact Subtype.ext (Γ.pt_inj s.1 t.1 x x (by rw [hst]))
  have hρ : ∀ t r, v t (structHom Γ.G.hom U r) = algebraMap R _ r := fun t r =>
    valHom_structHom Γ.G.hom _ _ (Over.w (Γ.pt t.1)) U t.2 r
  obtain ⟨d, hd, b, hb⟩ := exists_denom_of_injective (structHom Γ.G.hom U) v hv hρ (fun t => f t.1)
  exact ⟨d, hd, U, hg, b, fun t h => hb ⟨t, h⟩⟩

end GlobalTheory.CompanionTheory.Ar.BT.RegDenom
