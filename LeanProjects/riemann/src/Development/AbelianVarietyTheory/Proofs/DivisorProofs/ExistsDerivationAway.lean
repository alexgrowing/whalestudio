import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocReg

theorem exists_derivation_away {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (f : A)
    (hloc : letI := φ.toAlgebra; IsLocalization.Away f B) (d : A → A)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = x * d y + y * d x) :
    ∃ D : Derivation ℤ B B, ∀ a, D (φ a) = φ (d a) := by
  letI := φ.toAlgebra
  have h0 : d 0 = 0 := by
    have e := hadd 0 0
    rw [add_zero] at e
    linear_combination -e
  have h1 : d 1 = 0 := by
    have e := hmul 1 1
    rw [_root_.mul_one, _root_.one_mul] at e
    linear_combination -e
  let ψ : A →+* TrivSqZeroExt B B :=
    { toFun := fun a => TrivSqZeroExt.inl (φ a) + TrivSqZeroExt.inr (φ (d a))
      map_one' := by ext <;> simp [h1]
      map_mul' := fun x y => by
        ext
        · simp
        · simp [hmul]
          ring
      map_zero' := by ext <;> simp [h0]
      map_add' := fun x y => by ext <;> simp [hadd] }
  have hu : IsUnit (ψ f) := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    simpa [ψ, RingHom.algebraMap_toAlgebra] using IsLocalization.Away.algebraMap_isUnit (S := B) f)
  let Λ : B →+* TrivSqZeroExt B B := IsLocalization.Away.lift f hu
  have hΛ : ∀ a, Λ (φ a) = ψ a := fun a => IsLocalization.lift_eq (M := Submonoid.powers f) (S := B) _ a
  have hfst : ∀ x, (Λ x).fst = x := by
    have : (TrivSqZeroExt.fstHom ℤ B B).toRingHom.comp Λ = RingHom.id B := by
      refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun r => ?_)
      simp [RingHom.algebraMap_toAlgebra, hΛ, ψ]
    intro x
    exact congr($this x)
  let L : B →+ B :=
    { toFun := fun x => (Λ x).snd
      map_zero' := by simp
      map_add' := fun x y => by simp }
  refine ⟨Derivation.mk' L.toIntLinearMap (fun x y => ?_), fun a => ?_⟩
  · show (Λ (x * y)).snd = x • (Λ y).snd + y • (Λ x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [mul_comm]
  · show (Λ (φ a)).snd = φ (d a)
    rw [hΛ]
    simp [ψ]

theorem deriv_ext_basicOpen : ∀ (X : Scheme.{0}) (U W : X.affineOpens) (hWU : W.1 ≤ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1)), (∀ r, DW ((X.presheaf.map (homOfLE hWU).op).hom r) = (X.presheaf.map (homOfLE hWU).op).hom (D r)) → ∀ (h : Γ(X, U.1)), X.basicOpen h ≤ W.1 → ∀ (R : Type) [CommRing R] [Algebra ℤ R] (g : Sp R ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U.1) (D' : Derivation ℤ R R), (∀ r, D' ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.appLE U.1 ⊤ hg).hom r)) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.appLE U.1 ⊤ hg).hom (D r))) → ∃ (hUW : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ g ⁻¹ᵁ W.1) (D'' : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1)), (∀ r, D'' (((Sp R).presheaf.map (homOfLE (le_top : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ ⊤)).op).hom r) = ((Sp R).presheaf.map (homOfLE (le_top : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ ⊤)).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D' ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)))) ∧ (∀ θ, D'' ((g.appLE W.1 _ hUW).hom θ) = (g.appLE W.1 _ hUW).hom (DW θ)) := by

  intro X U W hWU D DW hDW h hhW R _ _ g hg D' hD'
  set e := Scheme.ΓSpecIso (CommRingCat.of R) with he
  set f := (g.appLE U.1 ⊤ hg).hom h with hf
  have hUW : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) f).1 ≤ g ⁻¹ᵁ W.1 := by
    show (Sp R).basicOpen f ≤ _
    rw [hf, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact fun x hx => hhW hx.2
  refine ⟨hUW, ?_⟩
  set U' := ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) f) with hU'
  let φ := ((Sp R).presheaf.map (homOfLE (le_top : U'.1 ≤ ⊤)).op).hom
  have hloc : letI := φ.toAlgebra; IsLocalization.Away f Γ(Sp R, U'.1) :=
    (isAffineOpen_top (Sp R)).isLocalization_basicOpen f
  obtain ⟨D'', hD''⟩ := exists_derivation_away φ f hloc (fun r => e.inv.hom (D' (e.hom.hom r)))
    (fun x y => by simp only [map_add]) (fun x y => by
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add]
      simp)
  refine ⟨D'', hD'', ?_⟩

  set resUW := (X.presheaf.map (homOfLE hWU).op).hom with hresUW
  set ψW := (g.appLE W.1 U'.1 hUW).hom with hψW
  have hUU : U'.1 ≤ g ⁻¹ᵁ U.1 := hUW.trans (fun x hx => hWU hx)
  set ψU := (g.appLE U.1 U'.1 hUU).hom with hψU
  have hψ : ∀ y, ψW (resUW y) = ψU y := fun y => by
    rw [hψW, hresUW, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have hψU' : ∀ y, ψU y = φ ((g.appLE U.1 ⊤ hg).hom y) := fun y => by
    rw [hψU, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hDU : ∀ y, D'' (ψU y) = ψU (D y) := fun y => by
    rw [hψU', hD'', hψU', hD']
    simp
  have hres : ∀ y, D'' (ψW (resUW y)) = ψW (DW (resUW y)) := fun y => by
    rw [hψ, hDU, hDW, hψ]
  have hunit : IsUnit (ψU h) := by
    rw [hψU']
    letI := φ.toAlgebra
    exact IsLocalization.Away.algebraMap_isUnit (S := Γ(Sp R, U'.1)) f
  have key : ∀ θ : Γ(X, W.1), ∃ (a : Γ(X, U.1)) (M : ℕ), resUW (h ^ M) * θ = resUW a := by
    intro θ
    set V := X.basicOpen (resUW h) with hVdef
    have hV : V = X.basicOpen h := by
      rw [hVdef, hresUW, Scheme.basicOpen_res]
      exact inf_eq_right.2 hhW
    have hVW : V ≤ W.1 := X.basicOpen_le _
    have hVU : V ≤ U.1 := hVW.trans hWU
    let resUV := (X.presheaf.map (homOfLE hVU).op).hom
    let resWV := (X.presheaf.map (homOfLE hVW).op).hom
    have hcomp : ∀ y, resWV (resUW y) = resUV y := fun y => by
      rw [hresUW, ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    have hlocU : letI := resUV.toAlgebra; IsLocalization.Away h Γ(X, V) :=
      U.2.isLocalization_of_eq_basicOpen h (homOfLE hVU) hV
    have hlocW : letI := resWV.toAlgebra; IsLocalization.Away (resUW h) Γ(X, V) :=
      W.2.isLocalization_basicOpen (resUW h)
    obtain ⟨⟨a, _, N, rfl⟩, hN⟩ := (letI := resUV.toAlgebra; IsLocalization.surj (Submonoid.powers h) (resWV θ))
    simp only [RingHom.algebraMap_toAlgebra] at hN
    rw [← hcomp, ← hcomp, ← map_mul] at hN
    letI := resWV.toAlgebra
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (resUW h)) (S := Γ(X, V))
      (x := θ * resUW (h ^ N)) (y := resUW a) (by simpa only [RingHom.algebraMap_toAlgebra] using hN)
    refine ⟨h ^ k * a, k + N, ?_⟩
    simp only [map_mul, map_pow] at hc ⊢
    linear_combination hc
  intro θ
  obtain ⟨a, M, hM⟩ := key θ
  have e2 := congrArg (fun x => D'' (ψW x)) hM
  have e3 := congrArg (fun x => ψW (DW x)) hM
  simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add] at e2 e3
  rw [hres, hres] at e2
  have hu : IsUnit (ψW (resUW (h ^ M))) := by rw [hψ, map_pow]; exact hunit.pow M
  exact hu.mul_left_cancel (by linear_combination e2 - e3)

end GlobalTheory.LocReg
end
