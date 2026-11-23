import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompRedIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitCoboundaryOfMulCocycleStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.UU.RingPoint

noncomputable section
namespace GlobalTheory.UU.UnitCob

section Alg
variable {B C : Type} [CommRing B] [CommRing C] {M N : Type} [AddCommGroup M] [AddCommGroup N]

def ev (κ : B →+* C) (c : Multiplicative M →* Cˣ) : AddMonoidAlgebra B M →+* C :=
  AddMonoidAlgebra.liftNCRingHom κ ((Units.coeHom C).comp c) fun _ _ => Commute.all _ _

theorem ev_single (κ : B →+* C) (c : Multiplicative M →* Cˣ) (m : M) (b : B) :
    ev κ c (AddMonoidAlgebra.single m b) = κ b * (c (Multiplicative.ofAdd m)).val := by
  simp [ev, AddMonoidAlgebra.liftNCRingHom]

def pair (c : Multiplicative M →* Cˣ) (c' : Multiplicative N →* Cˣ) : Multiplicative (M × N) →* Cˣ :=
  MonoidHom.mk' (fun p => c (Multiplicative.ofAdd p.toAdd.1) * c' (Multiplicative.ofAdd p.toAdd.2)) fun p q => by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ofAdd_add, map_mul]
    exact _root_.mul_mul_mul_comm _ _ _ _

theorem map_mapDomain (s : M → N) (F : AddMonoidAlgebra B N →+* C) (G : AddMonoidAlgebra B M →+* C)
    (h : ∀ m b, F (AddMonoidAlgebra.single (s m) b) = G (AddMonoidAlgebra.single m b)) (a : AddMonoidAlgebra B M) :
    F (AddMonoidAlgebra.mapDomain s a) = G a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [AddMonoidAlgebra.mapDomain_add, map_add, map_add, ha, hb]
  | single m b => rw [AddMonoidAlgebra.mapDomain_single, h]

theorem hom_eq (F G : AddMonoidAlgebra B M →+* C)
    (h : ∀ m b, F (AddMonoidAlgebra.single m b) = G (AddMonoidAlgebra.single m b)) (a : AddMonoidAlgebra B M) :
    F a = G a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | single m b => exact h m b

theorem ev_eq_zero (κ : B →+* C) (c : Multiplicative M →* Cˣ) (a : AddMonoidAlgebra B M)
    (h : ∀ m, κ (a.coeff m) = 0) : ev κ c a = 0 := by
  rw [← AddMonoidAlgebra.sum_coeff_single a, Finsupp.sum, map_sum]
  exact Finset.sum_eq_zero fun m _ => by rw [ev_single, h, zero_mul]

theorem coeff_mem (I : Ideal B) (G : AddMonoidAlgebra B M →+* AddMonoidAlgebra (B ⧸ I) M)
    (hG : ∀ m b, G (AddMonoidAlgebra.single m b) = AddMonoidAlgebra.single m (Ideal.Quotient.mk I b))
    (a : AddMonoidAlgebra B M) (h : G a = 1) (p : M) : (a - 1).coeff p ∈ I := by
  have k : AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk I) a = G a :=
    hom_eq _ G (fun m b => by rw [hG]; simp) a
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← AddMonoidAlgebra.coeff_mapRingHom, map_sub, k, h, map_one, sub_self]
  rfl

def mon (B : Type) [CommRing B] (s : M →+ N) : Multiplicative M →* (AddMonoidAlgebra B N)ˣ :=
  ((AddMonoidAlgebra.of B N).comp (AddMonoidHom.toMultiplicative s)).toHomUnits

theorem mon_val (s : M →+ N) (m : M) :
    (mon B s (Multiplicative.ofAdd m)).val = AddMonoidAlgebra.single (s m) 1 := rfl

end Alg

section Geo
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Y : Over S}

def ev₁ {Z : Over S} (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) : AddMonoidAlgebra Γ(Y.left, ⊤) X →+* Γ(Z.left, ⊤) :=
  ev y.left.appTop.hom (splitTorusPointsEquiv S X Z t)

def ev₂ {Z : Over S} (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y) :
    AddMonoidAlgebra Γ(Y.left, ⊤) (X × X) →+* Γ(Z.left, ⊤) :=
  ev y.left.appTop.hom (pair (splitTorusPointsEquiv S X Z t) (splitTorusPointsEquiv S X Z t'))

theorem ev₁_single {Z : Over S} (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (m : X) (b) :
    ev₁ t y (AddMonoidAlgebra.single m b) = y.left.appTop.hom b * (chV t m).val := ev_single _ _ _ _

theorem ev₂_single {Z : Over S} (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (m : X × X) (b) :
    ev₂ t t' y (AddMonoidAlgebra.single m b) = y.left.appTop.hom b * ((chV t m.1).val * (chV t' m.2).val) :=
  ev_single _ _ _ _

theorem chV_comp {Z Z' : Over S} (σ : Z' ⟶ Z) (t : Z ⟶ splitTorus S X) (χ : X) :
    (chV (σ ≫ t) χ).val = σ.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]

theorem chV_ext {Z : Over S} {t t' : Z ⟶ splitTorus S X} (h : ∀ χ, (chV t χ).val = (chV t' χ).val) : t = t' :=
  (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun a => Units.ext (h a.toAdd))

theorem exists_point {U : Over S} {D : Type} [CommRing D] (e : Γ(U.left, ⊤) ≃+* D) (c : Multiplicative X →* Dˣ) :
    ∃ t : U ⟶ splitTorus S X, ∀ χ, e (chV t χ).val = (c (Multiplicative.ofAdd χ)).val :=
  ⟨(splitTorusPointsEquiv S X U).symm ((Units.map e.symm.toMonoidHom).comp c), fun χ => by
    rw [chV, MulEquiv.apply_symm_apply]; exact e.apply_symm_apply _⟩

theorem exists_coeffs [IsAffine Y.left] (f : Γ((splitTorus S X ⊗ splitTorus S X ⊗ Y).left, ⊤)) :
    ∃ φ : AddMonoidAlgebra Γ(Y.left, ⊤) (X × X), ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift t (lift t' y)).left.appTop.hom f = ev₂ t t' y φ := by
  obtain ⟨U, y₀, e, -, he, hU⟩ := exists_ringPoint Y (AddMonoidAlgebra Γ(Y.left, ⊤) (X × X))
    AddMonoidAlgebra.singleZeroRingHom
  obtain ⟨t₀, h₀⟩ := exists_point (S := S) e (mon _ (AddMonoidHom.inl X X))
  obtain ⟨t₁, h₁⟩ := exists_point (S := S) e (mon _ (AddMonoidHom.inr X X))
  refine ⟨e ((lift t₀ (lift t₁ y₀)).left.appTop.hom f), fun Z t t' y => ?_⟩
  obtain ⟨σ, hσ, Hσ⟩ := hU Z y (ev₂ t t' y) fun b => (ev₂_single t t' y 0 b).trans (by simp [chV_zero])
  have a₀ : σ ≫ t₀ = t := chV_ext fun χ => by
    rw [chV_comp, Hσ, h₀, mon_val, ev₂_single]; simp [chV_zero]
  have a₁ : σ ≫ t₁ = t' := chV_ext fun χ => by
    rw [chV_comp, Hσ, h₁, mon_val, ev₂_single]; simp [chV_zero]
  rw [← Hσ, Rosenlicht.over_appTop_comp, comp_lift, comp_lift, a₀, a₁, hσ]

theorem appTop_ev₁ {Z : Over S} (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (a : AddMonoidAlgebra Γ(Y.left, ⊤) X) :
    (lift t y).left.appTop.hom (ev₁ (fst (splitTorus S X) Y) (snd _ _) a) = ev₁ t y a :=
  hom_eq ((lift t y).left.appTop.hom.comp (ev₁ (fst (splitTorus S X) Y) (snd _ _))) _ (fun m b => by
    rw [RingHom.comp_apply, ev₁_single, ev₁_single, map_mul, ← chV_comp, Rosenlicht.over_appTop_comp, lift_fst,
      lift_snd]) a

abbrev pl {Z W : Scheme.{0}} (r : Z ⟶ W) (u : Γ(W, ⊤)ˣ) : Γ(Z, ⊤)ˣ := Units.map r.appTop.hom.toMonoidHom u

theorem gm_mul_iff {Z W W' W'' : Scheme.{0}} (r₁ : Z ⟶ W) (r₂ : Z ⟶ W') (r₃ : Z ⟶ W'') (r₄ : Z ⟶ W'')
    (u : Γ(W, ⊤)ˣ) (v : Γ(W', ⊤)ˣ) (w : Γ(W'', ⊤)ˣ) :
    (∀ z, gm r₁ z ⊤ u * gm r₂ z ⊤ v = gm r₃ z ⊤ w * gm r₄ z ⊤ w) ↔
      r₁.appTop.hom u.val * r₂.appTop.hom v.val = r₃.appTop.hom w.val * r₄.appTop.hom w.val := by
  have e : ∀ z, (gm r₁ z ⊤ u * gm r₂ z ⊤ v = gm r₃ z ⊤ w * gm r₄ z ⊤ w) =
      (gm (𝟙 Z) z ⊤ (pl r₁ u * pl r₂ v) = gm (𝟙 Z) z ⊤ (pl r₃ w * pl r₄ w)) := fun z => by
    rw [map_mul, map_mul, gm_top r₁, gm_top r₂, gm_top r₃, gm_top r₄]
  simp only [e]
  exact ⟨fun h => congrArg Units.val (unit_ext fun z _ => h z), fun h z => congrArg _ (Units.ext h)⟩

theorem gm_one_iff {Z W : Scheme.{0}} (r : Z ⟶ W) (u : Γ(W, ⊤)ˣ) :
    (∀ z, gm r z ⊤ u = 1) ↔ r.appTop.hom u.val = 1 := by
  have e : ∀ z, (gm r z ⊤ u = 1) = (gm (𝟙 Z) z ⊤ (pl r u) = gm (𝟙 Z) z ⊤ 1) := fun z => by
    rw [map_one, gm_top r]
  simp only [e]
  exact ⟨fun h => congrArg Units.val (unit_ext fun z _ => h z), fun h z => congrArg _ (Units.ext h)⟩

theorem cocycle_of_points [IsAffine Y.left] (φ : AddMonoidAlgebra Γ(Y.left, ⊤) (X × X))
    (h : ∀ (Z : Over S) (t t' t'' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      ev₂ (t * t') t'' y φ * ev₂ t t' y φ = ev₂ t (t' * t'') y φ * ev₂ t' t'' y φ) :
    AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.1, p.2)) φ *
        AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, (0 : X))) φ =
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, p.2)) φ *
        AddMonoidAlgebra.mapDomain (fun p : X × X => ((0 : X), p.1, p.2)) φ := by
  obtain ⟨U, y₀, e, -, he, -⟩ := exists_ringPoint Y (AddMonoidAlgebra Γ(Y.left, ⊤) (X × X × X))
    AddMonoidAlgebra.singleZeroRingHom
  obtain ⟨t₀, h₀⟩ := exists_point (S := S) e (mon _ (AddMonoidHom.inl X (X × X)))
  obtain ⟨t₁, h₁⟩ := exists_point (S := S) e (mon _ ((AddMonoidHom.inr X (X × X)).comp (AddMonoidHom.inl X X)))
  obtain ⟨t₂, h₂⟩ := exists_point (S := S) e (mon _ ((AddMonoidHom.inr X (X × X)).comp (AddMonoidHom.inr X X)))
  have key : ∀ (s : X × X → X × X × X) (t t' : U ⟶ splitTorus S X),
      (∀ m : X × X, e (chV t m.1).val * e (chV t' m.2).val = AddMonoidAlgebra.single (s m) 1) →
      AddMonoidAlgebra.mapDomain s φ = e (ev₂ t t' y₀ φ) := fun s t t' H =>
    map_mapDomain s (RingHom.id _) (e.toRingHom.comp (ev₂ t t' y₀)) (fun m b => by
      change _ = e (ev₂ t t' y₀ _)
      rw [ev₂_single, map_mul, map_mul, H, he]
      simp [AddMonoidAlgebra.single_mul_single]) φ
  rw [key _ (t₀ * t₁) t₂, key _ t₀ t₁, key _ t₀ (t₁ * t₂), key _ t₁ t₂, ← map_mul, ← map_mul, h]
  all_goals
    intro m
    simp [chV_mul, h₀, h₁, h₂, mon_val, AddMonoidAlgebra.single_mul_single]

end Geo

section Red
variable {A : Type} [CommRing A] (J : Ideal A) {X : Type} [AddCommGroup X] {Y : Over (Spec (CommRingCat.of A))}

theorem coeff_mem_of_points [IsAffine Y.left] (φ : AddMonoidAlgebra Γ(Y.left, ⊤) (X × X))
    (h : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) →
      ∀ (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y), ev₂ t t' y φ = 1) (p : X × X) :
    (φ - 1).coeff p ∈ J.map (strMap Y) := by
  obtain ⟨I, hI⟩ : ∃ I, I = J.map (strMap Y) := ⟨_, rfl⟩
  rw [← hI]
  obtain ⟨U, y₀, e, -, he, -⟩ := exists_ringPoint Y (AddMonoidAlgebra (Γ(Y.left, ⊤) ⧸ I) (X × X))
    (AddMonoidAlgebra.singleZeroRingHom.comp (Ideal.Quotient.mk I))
  obtain ⟨t₀, h₀⟩ := exists_point e (mon _ (AddMonoidHom.inl X X))
  obtain ⟨t₁, h₁⟩ := exists_point e (mon _ (AddMonoidHom.inr X X))
  have hU : ∃ s, s ≫ red J = U.hom := (exists_comp_red_iff J U).2 fun a ha => e.injective (by
    have : Ideal.Quotient.mk I (strMap Y a) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hI ▸ Ideal.mem_map_of_mem _ ha)
    rw [← appTop_strMap y₀, he, RingHom.comp_apply, this, map_zero, map_zero])
  refine coeff_mem I (e.toRingHom.comp (ev₂ t₀ t₁ y₀)) (fun m b => ?_) φ
    ((congrArg e (h U hU t₀ t₁ y₀)).trans (map_one e)) p
  change e (ev₂ t₀ t₁ y₀ _) = _
  rw [ev₂_single, map_mul, map_mul, he, h₀, h₁, mon_val, mon_val]
  simp [AddMonoidAlgebra.single_mul_single]

end Red

theorem exists_coboundary : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (Y : Over (Spec (CommRingCat.of A))) [IsAffine Y.left] (f : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤)ˣ), (∀ (Z : Over (Spec (CommRingCat.of A))) (t t' t'' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift (t * t') (lift t'' y)).left z ⊤ f * gm (lift t (lift t' y)).left z ⊤ f = gm (lift t (lift (t' * t'') y)).left z ⊤ f * gm (lift t' (lift t'' y)).left z ⊤ f) → (∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift t (lift t' y)).left z ⊤ f = 1) → ∃ g : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤)ˣ, (∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift t (lift t' y)).left z ⊤ f * gm (lift (t * t') y).left z ⊤ g = gm (lift t y).left z ⊤ g * gm (lift t' y).left z ⊤ g) ∧ (∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift t y).left z ⊤ g = 1) := by
  intro A _ J hJ X _ Y _ f hc h1
  obtain ⟨φ, hφ⟩ := exists_coeffs f.val
  have hI : IsNilpotent (J.map (strMap Y)) := by
    obtain ⟨n, hn⟩ := hJ
    exact ⟨n, by rw [← Ideal.map_pow, hn]; exact Ideal.map_bot⟩
  obtain ⟨u, hu, Hu⟩ := GlobalTheory.T.exists_unit_coboundary_of_cocycle_addMonoidAlgebra _ _ hI X φ
    (coeff_mem_of_points J φ fun Z hZ t t' y => (hφ Z t t' y).symm.trans ((gm_one_iff _ _).1 (h1 Z hZ t t' y)))
    (cocycle_of_points φ fun Z t t' t'' y => by
      rw [← hφ, ← hφ, ← hφ, ← hφ]
      exact (gm_mul_iff _ _ _ _ _ _ _).1 (hc Z t t' t'' y))
  refine ⟨Units.map (ev₁ (fst _ Y) (snd _ _)).toMonoidHom u, fun Z t t' y => (gm_mul_iff _ _ _ _ _ _ _).2 ?_,
    fun Z hZ t y => (gm_one_iff _ _).2 ?_⟩
  · have e := congrArg (ev₂ t t' y) Hu
    rw [map_mul, map_mul, map_mapDomain _ _ (ev₁ (t * t') y), map_mapDomain _ _ (ev₁ t y),
      map_mapDomain _ _ (ev₁ t' y), ← hφ, ← appTop_ev₁ (t * t'), ← appTop_ev₁ t, ← appTop_ev₁ t'] at e
    · exact e
    all_goals
      intro m b
      simp [ev₁_single, ev₂_single, chV_mul, chV_zero]
  · refine (appTop_ev₁ t y u.val).trans ?_
    have hle : J.map (strMap Y) ≤ RingHom.ker y.left.appTop.hom := Ideal.map_le_iff_le_comap.2 fun a ha =>
      (appTop_strMap y a).trans ((exists_comp_red_iff J Z).1 hZ a ha)
    have e : ev₁ t y (u.val - 1) = 0 := ev_eq_zero _ _ _ fun m => hle (hu m)
    rwa [map_sub, map_one, sub_eq_zero] at e

end GlobalTheory.UU.UnitCob
end
