import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.ModelValBaseChange

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMapR_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Chart.dualMapR (g.comp f) = (Chart.dualMapR g).comp (Chart.dualMapR f) :=
  RingHom.ext fun x ↦ TrivSqZeroExt.ext (by simp [Chart.dualMapR]) (by simp [Chart.dualMapR])

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem lieCorr_comp {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {X'' : Obj F 𝔠 (Sp R'')} {σ : R →+* R'}
    {τ : R' →+* R''} {φ : X'.A.left ⟶ X.A.left} {φ' : X''.A.left ⟶ X'.A.left} {v : X.Lie} {v' : X'.Lie}
    {v'' : X''.Lie} (h : Obj.LieCorr σ φ v v') (h' : Obj.LieCorr τ φ' v' v'') :
    Obj.LieCorr (τ.comp σ) (φ' ≫ φ) v v'' := by
  unfold Obj.LieCorr at *
  rw [← Category.assoc, h', Category.assoc, h, ← Category.assoc, ← spMap_comp_ringHom, ← dualMapR_comp_ringHom]

theorem exists_lieCorr {σ : R →+* R'} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {φ : X'.A.left ⟶ X.A.left}
    (hp : X'.IsPullBy X (spMap σ) φ) (v : X.Lie) : ∃ w : X'.Lie, Obj.LieCorr σ φ v w := by
  letI := σ.toAlgebra
  obtain ⟨e, he, -⟩ := Obj.exists_lieEquiv (R' := R') hp
  exact ⟨e (1 ⊗ₜ v), (he _ _).2 rfl⟩

theorem lieCorr_unique {σ : R →+* R'} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {φ : X'.A.left ⟶ X.A.left}
    (hp : X'.IsPullBy X (spMap σ) φ) {v : X.Lie} {w₁ w₂ : X'.Lie} (h₁ : Obj.LieCorr σ φ v w₁)
    (h₂ : Obj.LieCorr σ φ v w₂) : w₁ = w₂ := by
  letI := σ.toAlgebra
  obtain ⟨e, he, -⟩ := Obj.exists_lieEquiv (R' := R') hp
  exact ((he _ _).1 h₁).trans ((he _ _).1 h₂).symm

theorem isPullBy_comp {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {φ' : X''.A.left ⟶ X'.A.left}
    (hp : X'.IsPullBy X (spMap σ) φ) (hp' : X''.IsPullBy X' (spMap τ) φ') :
    X''.IsPullBy X (spMap (τ.comp σ)) (φ' ≫ φ) := by
  rw [spMap_comp_ringHom]
  exact hp'.comp hp

theorem detCorr_comp {σ : R →+* R'} {τ : R' →+* R''} {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {X'' : Obj F 𝔠 (Sp R'')} {φ : X'.A.left ⟶ X.A.left} {φ' : X''.A.left ⟶ X'.A.left}
    (hp : X'.IsPullBy X (spMap σ) φ) (hp' : X''.IsPullBy X' (spMap τ) φ') {δ : X.DetOmega} {δ' : X'.DetOmega}
    {δ'' : X''.DetOmega} (hd : Obj.DetCorr σ φ δ δ') (hd' : Obj.DetCorr τ φ' δ' δ'') :
    Obj.DetCorr (τ.comp σ) (φ' ≫ φ) δ δ'' := by
  intro v v'' hv
  choose v' hv' using fun i ↦ exists_lieCorr hp (v i)
  choose w hw using fun i ↦ exists_lieCorr hp' (v' i)
  have hwv : w = v'' := funext fun i ↦
    lieCorr_unique (isPullBy_comp hp hp') (lieCorr_comp (hv' i) (hw i)) (hv i)
  subst hwv
  rw [hd' v' w hw, hd v v' hv', RingHom.comp_apply]

end GlobalTheory.RealMult.ModelValBaseChange

namespace GlobalTheory.RealMult

open ModelValBaseChange in

theorem isModelVal_baseChange : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
  (r₀ : Rule (rapObj 𝔠) R₀ k) (M : Scheme.{0}) (U : Obj F 𝔠 M) (R R' : Type) [CommRing R] [Algebra R₀ R]
  [CommRing R'] [Algebra R₀ R'] (σ : R →ₐ[R₀] R') (X : Obj F 𝔠 (Sp R)) (X' : Obj F 𝔠 (Sp R'))
  (φ : X'.A.left ⟶ X.A.left) (δ : X.DetGen) (δ' : X'.DetGen) (v : R), X'.IsPullBy X (spMap (σ : R →+* R')) φ →
  Obj.DetCorr (σ : R →+* R') φ δ.1 δ'.1 → IsModelVal r₀ U X δ v → IsModelVal r₀ U X' δ' (σ v) := by
  intro F _ _ 𝔠 R₀ _ k r₀ M U R R' _ _ _ _ σ X X' φ δ δ' v hp hd hv
  intro R'' _ _ τ X'' φ'' δ'' hp'' hd'' W hW Y φY hY δY h hh ψ χ hχ
  have hc : ((τ.comp σ : R →ₐ[R₀] R'') : R →+* R'') = (τ : R' →+* R'').comp (σ : R →+* R') := rfl
  have := hv R'' (τ.comp σ) X'' (φ'' ≫ φ) δ'' (by rw [hc]; exact isPullBy_comp hp hp'')
    (by rw [hc]; exact detCorr_comp hp hp'' hd hd'') W hW Y φY hY δY h hh ψ χ hχ
  exact this

end GlobalTheory.RealMult
