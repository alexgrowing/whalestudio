import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

section Ring

variable (B : Type) [CommRing B] (p : ℕ)

theorem X_pow_dvd_of_mem {P : MvPolynomial Unit B} (hP : P ∈ orig B Unit ^ (p + 1)) :
    (Polynomial.X : Polynomial B) ^ (p + 1) ∣ MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) P := by
  have h₁ : MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) P ∈
      Ideal.map ((MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) :
        MvPolynomial Unit B →ₐ[B] Polynomial B) : MvPolynomial Unit B →+* Polynomial B) (orig B Unit ^ (p + 1)) :=
    Ideal.mem_map_of_mem _ hP
  rw [map_orig_pow] at h₁
  have h₂ : Ideal.span (Set.range fun i : Unit => ((MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) :
      MvPolynomial Unit B →ₐ[B] Polynomial B) : MvPolynomial Unit B →+* Polynomial B) (MvPolynomial.X i)) =
      Ideal.span {(Polynomial.X : Polynomial B)} := by
    congr 1
    ext a
    simp
  rw [h₂, Ideal.span_singleton_pow] at h₁
  exact Ideal.mem_span_singleton.1 h₁

variable {B p}

theorem top_coeff_eq (hp : 1 ≤ p) (b : Fin (p + 1) → B) (v : B)
    (h : ∑ i : Fin (p + 1), algebraMap B (Jet B Unit p) (b i) * dQ B p ^ (i : ℕ) =
      1 + dQ B p ^ p * algebraMap B (Jet B Unit p) v) : b (Fin.last p) = v := by
  set P : MvPolynomial Unit B := ∑ i : Fin (p + 1), MvPolynomial.C (b i) * MvPolynomial.X () ^ (i : ℕ) -
    (1 + MvPolynomial.X () ^ p * MvPolynomial.C v) with hPdef
  have hP : P ∈ orig B Unit ^ (p + 1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hPdef, map_sub, map_add, map_sum, map_one, map_mul, map_pow, sub_eq_zero]
    simp only [map_mul, map_pow]
    exact h
  have hd := X_pow_dvd_of_mem B p hP
  have hc := Polynomial.X_pow_dvd_iff.1 hd p (Nat.lt_succ_self p)
  have hp0 : p ≠ 0 := by omega
  have e₁ : MvPolynomial.aeval (fun _ : Unit => (Polynomial.X : Polynomial B)) P =
      ∑ i : Fin (p + 1), Polynomial.C (b i) * Polynomial.X ^ (i : ℕ) -
        (1 + Polynomial.C v * Polynomial.X ^ p) := by
    simp only [hPdef, map_sub, map_add, map_sum, map_mul, map_pow, map_one, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Polynomial.algebraMap_eq]
    ring
  have e₂ : ∑ i : Fin (p + 1), (if p = (i : ℕ) then b i else 0) = b (Fin.last p) := by
    rw [Finset.sum_eq_single (Fin.last p)]
    · simp
    · intro i _ hi
      rw [if_neg]
      intro h'
      exact hi (Fin.ext (by simpa using h'.symm))
    · simp
  rw [e₁] at hc
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_one, if_neg hp0, e₂, if_true, zero_add] at hc
  exact sub_eq_zero.1 hc

end Ring

theorem appLE_top_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (W : Y.Opens) (h₁ : ⊤ ≤ f ⁻¹ᵁ W)
    (h₂ : ⊤ ≤ g ⁻¹ᵁ W) : f.appLE W ⊤ h₁ = g.appLE W ⊤ h₂ := by
  subst e
  rfl

theorem appTop_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appTop = f.appLE ⊤ ⊤ h := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

section Test

variable {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] {k : Type} [Field k] (x : Sp k ⟶ X0)
variable {B : Type} [CommRing B] [Algebra k B]

theorem rQ_appLE_prZ (p : ℕ) (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens) (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W)
    (hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W)) (a : Γ(pullback G.hom x, W)) :
    ((rQ G x p z).appLE _ ⊤ hr).hom (((prZ G x p).app W).hom a) =
      ((spMap ((inR (k := k) B p : B →ₐ[k] Jet B Unit p) : B →+* Jet B Unit p)).appTop).hom
        (((xkZ G x z).appLE W ⊤ hW).hom a) := by
  have h₁ : (prZ G x p).app W ≫ (rQ G x p z).appLE _ ⊤ hr = (rQ G x p z ≫ prZ G x p).appLE W ⊤ hr := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  have h₂ : (xkZ G x z).appLE W ⊤ hW ≫
      (spMap ((inR (k := k) B p : B →ₐ[k] Jet B Unit p) : B →+* Jet B Unit p)).appTop =
      (spMap ((inR (k := k) B p : B →ₐ[k] Jet B Unit p) : B →+* Jet B Unit p) ≫ xkZ G x z).appLE W ⊤ (by
        rw [Scheme.Hom.comp_preimage]
        exact fun y _ => hW (show _ from trivial)) := by
    rw [← Scheme.Hom.appLE_comp_appLE _ _ W ⊤ ⊤ hW (by simp), appTop_eq_appLE _ (by simp)]
  have h₃ := h₁.trans ((appLE_top_congr (rQ_prZ G x p z) W _ _).trans h₂.symm)
  exact congrArg (fun q => q.hom a) h₃

theorem rQ_appLE_dltOn (p : ℕ) (z : overAt x B ⟶ G) (V : (Ym G x p).Opens) (hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ V) :
    ((rQ G x p z).appLE V ⊤ hr).hom (dltOn G x p V) = toΓ _ (dQ B p) := by
  have h₁ : (Ym G x p).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ (rQ G x p z).appLE V ⊤ hr =
      (rQ G x p z).appTop := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have h₂ : ((rQ G x p z).appLE V ⊤ hr).hom (dltOn G x p V) = ((rQ G x p z).appTop).hom (dlt G x p) :=
    congrArg (fun q => q.hom (dlt G x p)) h₁
  have h₃ := congrArg (fun q => (q.appTop).hom (toΓ (Jet k Unit p) (Ideal.Quotient.mk _ (MvPolynomial.X ()))))
    (rQ_fst G x p z)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h₃
  rw [h₂, dlt, h₃, spMap_toΓ]
  congr 1
  exact MvPolynomial.aeval_X (R := k) (fun _ : Unit => dQ B p) ()

theorem coef_at_test (p : ℕ) (hp : 1 ≤ p) (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens)
    (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W) (c : Fin (p + 1) → Γ(pullback G.hom x, W)) (f : Γ(Ym G x p, prZ G x p ⁻¹ᵁ W)) (v : B)
    (hf : f = ∑ i, ((prZ G x p).app W).hom (c i) * dltOn G x p _ ^ (i : ℕ))
    (hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W))
    (hv : ((rQ G x p z).appLE _ ⊤ hr).hom f = toΓ _ (1 + dQ B p ^ p * algebraMap B _ v)) :
    ((xkZ G x z).appLE W ⊤ hW).hom (c (Fin.last p)) = toΓ B v := by
  have hs : ∀ i, ∃ b : B, toΓ B b = ((xkZ G x z).appLE W ⊤ hW).hom (c i) := fun i =>
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv).2 _
  choose b hb using hs
  have key : ∑ i : Fin (p + 1), algebraMap B (Jet B Unit p) (b i) * dQ B p ^ (i : ℕ) =
      1 + dQ B p ^ p * algebraMap B (Jet B Unit p) v := by
    apply toΓ_inj
    rw [← hv, hf, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, rQ_appLE_prZ G x p z W hW hr, rQ_appLE_dltOn, ← hb, spMap_toΓ]
    rfl
  rw [← hb, top_coeff_eq hp b v key]

end Test

theorem coef_pull : ∀ (X0 : Scheme.{0}) (G : Over X0) [GrpObj G] (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (hp : 1 ≤ p) (B : Type) [CommRing B] [Algebra k B] (z : overAt x B ⟶ G) (W : (pullback G.hom x).Opens) (hW : ⊤ ≤ xkZ G x z ⁻¹ᵁ W) (c : Fin (p + 1) → Γ(pullback G.hom x, W)) (f : Γ(Ym G x p, prZ G x p ⁻¹ᵁ W)) (v : B), f = ∑ i, ((prZ G x p).app W).hom (c i) * dltOn G x p _ ^ (i : ℕ) → ∀ hr : ⊤ ≤ rQ G x p z ⁻¹ᵁ (prZ G x p ⁻¹ᵁ W), ((rQ G x p z).appLE _ ⊤ hr).hom f = toΓ _ (1 + dQ B p ^ p * algebraMap B _ v) → ((xkZ G x z).appLE W ⊤ hW).hom (c (Fin.last p)) = toΓ B v := by
  intro X0 G _ k _ x p hp B _ _ z W hW c f v hf hr hv
  exact coef_at_test G x p hp z W hW c f v hf hr hv

end GlobalTheory.CompanionTheory.Ar.Coc
