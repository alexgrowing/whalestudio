import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

private theorem dualNumber_base_change_comp {X : Scheme.{0}} {t : SAB H X} {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (ρ : A →+* B) (χ : B →+* C) (u : Vecs Dw t A) (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) :
    u.bc (χ.comp ρ) σ j = spMap (dualMap χ) ≫ u.bc ρ σ j := by
  rw [Vecs.bc, Vecs.bc, ← Category.assoc, ModelRelProbe.spMap_comp]
  congr 2
  ext z <;> simp [dualMap]

private theorem pull_ind_base_change {R K : Type} [CommRing R] [Field K] {f : c.F →+* R} {x : Sp R ⟶ T.X} (g : EigFrame T f x)
    (ψ : R →+* K) {P : Sp K ⟶ T.X} (hP : P = spMap ψ ≫ x) (σ : E →+* ℂ) :
    Pull.Ind T.t P (Vecs.bc (Dw := Dw) ψ g.v σ) := by
  subst hP
  exact Pull.frame_ind (GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw l c T.X T.t _ K _ ψ _ g.v
    ⟨fun τ i => ⟨g.tan τ i, g.eig τ i⟩, g.basis⟩) σ

private theorem triangular_base_change {R R' K : Type} [CommRing R] [CommRing R'] [Field K] {f : c.F →+* R} {x : Sp R ⟶ T.X}
    {f' : c.F →+* R'} {x' : Sp R' ⟶ T.X} {g : EigFrame T f x} {g' : EigFrame T f' x'} {ρ : R →+* R'}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ} (h : g.Tri ρ g' t) (ψ : R' →+* K) {P : Sp K ⟶ T.X}
    (hP : P = spMap ψ ≫ x') (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    ∃ cf : Fin (Dw.mult σ) → K, cf i = ψ (t σ i) ∧ (∀ k, i < k → cf k = 0) ∧
      IsCombAtG T.t P (Vecs.bc (Dw := Dw) (ψ.comp ρ) g.v σ) cf (Vecs.bc (Dw := Dw) ψ g'.v σ i) := by
  obtain ⟨cf, c1, c2, c3⟩ := h.2.2 σ i
  refine ⟨fun k => ψ (cf k), congrArg ψ c1, fun k hk => by simp only [c2 k hk, map_zero], ?_⟩
  rw [funext (dualNumber_base_change_comp ρ ψ g.v σ), hP]
  exact GlobalTheory.LatDRFree.comb_map _ ψ c3

private theorem add_one_pow_eq_ringHom_image_add_prime_mul_zero (Y : GlobalTheory.ProjVar.Var F) (y : Y.X) :
    spMap (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) ≫ stalkPt Y y = genericPt Y :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)

end SlopeTestRemainingChoices

theorem UpperTheory.exists_unit_tri_and_diag_coeff_mul_eq_of_carries :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Φ : FlagCpt T e) (K : Type) [Field K] (φ : Φ.Y.Fn →+* K) (q : Sp K ⟶ Φ.Y.X) (f : c.F →+* K) (g : EigFrame T f (q ≫ Φ.π ≫ genι T)) (x : Pad.Letter Dw), q = spMap φ ≫ genericPt Φ.Y → Φ.Carries q g → ∃ c₀ : Kˣ, ∀ y₀ : Φ.Y.X, (∀ σ, Pull.Tri T.t (q ≫ Φ.π ≫ genι T) (Vecs.bc (φ.comp (algebraMap (Φ.Y.X.presheaf.stalk y₀) Φ.Y.X.functionField)) (GlobalTheory.LineNorm.fr Φ y₀).v σ) (g.v σ)) ∧ ∀ cf : Fin (Dw.mult x.1) → K, IsCombAtG T.t (q ≫ Φ.π ≫ genι T) (Vecs.bc (φ.comp (algebraMap (Φ.Y.X.presheaf.stalk y₀) Φ.Y.X.functionField)) (GlobalTheory.LineNorm.fr Φ y₀).v x.1) cf (g.v x.1 x.2) → cf x.2 * (c₀ : K) = φ (GlobalTheory.LineNorm.dg Φ y₀ x.1 x.2 : Φ.Y.Fn) := by
  intro E _ _ _ H Dw l Xo c O _ β T F _ _ e Φ K _ φ q f g x hq hc
  obtain ⟨y', ψ, φ₁, f', t, t', h1, h2, h3⟩ := hc
  have hy : ∀ y : Φ.Y.X,
      q = spMap (φ.comp (algebraMap (Φ.Y.X.presheaf.stalk y) Φ.Y.X.functionField)) ≫ stalkPt Φ.Y y := fun y => by
    rw [hq, ← add_one_pow_eq_ringHom_image_add_prime_mul_zero Φ.Y y, ← Category.assoc]
    exact congrArg (· ≫ stalkPt Φ.Y y) (ModelRelProbe.spMap_comp _ _)
  have hm : Mono (stalkPt Φ.Y y') := inferInstanceAs (Mono (Φ.Y.X.fromSpecStalk y'))
  obtain rfl : ψ = φ.comp (algebraMap (Φ.Y.X.presheaf.stalk y') Φ.Y.X.functionField) :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _)
      (a₂ := CommRingCat.ofHom _) ((cancel_mono (stalkPt Φ.Y y')).1 (h1.symm.trans (hy y'))))
  have hP : q ≫ Φ.π ≫ genι T = spMap φ ≫ genericPt Φ.Y ≫ Φ.π ≫ genι T := by rw [hq, Category.assoc]
  have hPy : ∀ y : Φ.Y.X, q ≫ Φ.π ≫ genι T =
      spMap (φ.comp (algebraMap (Φ.Y.X.presheaf.stalk y) Φ.Y.X.functionField)) ≫ stalkPt Φ.Y y ≫ Φ.π ≫ genι T :=
    fun y => (congrArg (· ≫ Φ.π ≫ genι T) (hy y)).trans (Category.assoc _ _ _)
  have I0 := pull_ind_base_change Φ.f0 φ hP
  have I' := pull_ind_base_change f' _ (hPy y')
  have Ig : ∀ σ, Pull.Ind T.t (q ≫ Φ.π ≫ genι T) (g.v σ) :=
    Pull.frame_ind (f := f) (u := g.v) ⟨fun τ i => ⟨g.tan τ i, g.eig τ i⟩, g.basis⟩
  have T1 : ∀ σ, Pull.Tri T.t (q ≫ Φ.π ≫ genι T) (Vecs.bc (Dw := Dw) _ f'.v σ) (Vecs.bc (Dw := Dw) φ Φ.f0.v σ) :=
    fun σ j => by
      obtain ⟨cf, -, c2, c3⟩ := triangular_base_change h2 φ hP σ j
      exact ⟨cf, c2, c3⟩
  have T2 : ∀ σ, Pull.Tri T.t (q ≫ Φ.π ≫ genι T) (Vecs.bc (Dw := Dw) _ f'.v σ) (g.v σ) :=
    fun σ j => by
      obtain ⟨cf, -, c2, c3⟩ := h3.2.2 σ j
      exact ⟨cf, c2, c3⟩
  have T3 : ∀ σ, Pull.Tri T.t (q ≫ Φ.π ≫ genι T) (g.v σ) (Vecs.bc (Dw := Dw) φ Φ.f0.v σ) := fun σ =>
    ((T2 σ).symm (I' σ) (Ig σ)).1.trans (Ig σ).1 (I' σ).1 (T1 σ)
  obtain ⟨d, d1, d2⟩ := T3 x.1 x.2
  refine ⟨Units.mk0 (d x.2) ((T3 x.1).diag (Ig _) (I0 _) d2).1, fun y₀ => ?_⟩
  have IF := pull_ind_base_change (GlobalTheory.LineNorm.fr Φ y₀) _ (hPy y₀)
  have A := triangular_base_change (GlobalTheory.LineNorm.fr_spec Φ y₀).1 φ hP
  have T4 : ∀ σ, Pull.Tri T.t (q ≫ Φ.π ≫ genι T)
      (Vecs.bc (φ.comp (algebraMap (Φ.Y.X.presheaf.stalk y₀) Φ.Y.X.functionField)) (GlobalTheory.LineNorm.fr Φ y₀).v σ)
      (g.v σ) := fun σ =>
    Pull.Tri.trans (IF σ).1 (I0 σ).1 (fun j => by
      obtain ⟨cf, -, c2, c3⟩ := A σ j
      exact ⟨cf, c2, c3⟩) ((T3 σ).symm (Ig σ) (I0 σ)).1
  refine ⟨T4, fun cf hcf => ?_⟩
  obtain ⟨a, a1, -, a3⟩ := A x.1 x.2
  have := (T4 x.1).diag_mul (IF _) (Ig _).1 d1 d2 hcf a3
  rw [Units.val_mk0, mul_comm, ← this]
  exact a1
