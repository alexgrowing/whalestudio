import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DwComapLinear

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.ChartMap

variable {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁}
  {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂}

def Φc (b : (I₁ → ℂ) → I₂ → ℂ) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) (k : K₁.K) :
    Hol (K₂.W (κ k)) →+* Hol (K₁.W k) :=
  (Hol.comap _ (hΦ k) (hW k)).toRingHom

theorem Φc_cst (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) (k : K₁.K) (f : Hol F₂.V) :
    Φc b M κ hΦ hW k (K₂.cst (κ k) f) = K₁.cst k (Hol.comap b hb hbV f) :=
  Hol.ext_fn fun p hp ↦ by
    change (Hol.comap _ (hΦ k) (hW k) (K₂.cst (κ k) f)).fn p = _
    rw [Hol.fn_comap _ _ _ _ hp, Charts.fn_cst _ _ _ (hW k p hp), Charts.fn_cst _ _ _ hp,
      Hol.fn_comap _ _ _ _ (K₁.base k p hp)]

theorem Φc_sh (b : (I₁ → ℂ) → I₂ → ℂ) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) {l : Λ₁} {k k' : K₁.K}
    (h : K₁.le l k' k) (h₂ : K₂.le (A l) (κ k') (κ k)) (f : Hol (K₂.W (κ k))) :
    Φc b M κ hΦ hW k' (Charts.sh h₂ f) = Charts.sh h (Φc b M κ hΦ hW k f) :=
  Hol.ext_fn fun p hp ↦ by
    change (Hol.comap _ (hΦ k') (hW k') (Charts.sh h₂ f)).fn p =
      (Charts.sh h (Hol.comap _ (hΦ k) (hW k) f)).fn p
    rw [Hol.fn_comap _ _ _ _ hp, Charts.fn_sh _ _ (hW k' p hp), Charts.fn_sh _ _ hp,
      Hol.fn_comap _ _ _ _ (K₁.maps h p hp)]
    congr 1
    simp [Fam.shift, map_add, hτ l p.1 (K₁.base k' p hp)]

theorem dw_Φc (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) (k : K₁.K) (a : Fin g₁)
    (f : Hol (K₂.W (κ k))) :
    dw a (Φc b M κ hΦ hW k f) = ∑ c, M (Pi.single a 1) c • Φc b M κ hΦ hW k (dw c f) :=
  dw_comap_linear b M (fun p hp ↦ hb _ (K₁.base k p hp)) (hΦ k) (hW k) a f

end GlobalTheory.AnPer.ChartMap

namespace GlobalTheory.AnPer.ChartMap

variable {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁}
  {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂}

@[reducible] def objMap (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) (T : K₁.Obj) : K₂.Obj where
  k := κ T.k
  C := T.C
  ring := T.ring
  alg := ((algebraMap (Hol F₁.V) T.C).comp (Hol.comap b hb hbV).toRingHom).toAlgebra
  J := T.J
  nil := T.nil
  ρ := T.ρ.comp (Φc b M κ hΦ hW T.k)
  ρ_cst f := by
    change T.ρ (Φc b M κ hΦ hW T.k (K₂.cst (κ T.k) f)) = algebraMap (Hol F₁.V) T.C (Hol.comap b hb hbV f)
    rw [Φc_cst b hb hbV M κ hΦ hW, T.ρ_cst]

def homMap (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) {K₁ : Charts F₁} {K₂ : Charts F₂}
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k))
    (hle : ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) {T T' : K₁.Obj} (f : T ⟶ T') :
    Charts.Hom (objMap b hb hbV M κ hΦ hW T) (objMap b hb hbV M κ hΦ hW T') where
  φ := { (f.φ : T.C →+* T'.C) with commutes' := fun r ↦ f.φ.commutes (Hol.comap b hb hbV r) }
  deg := A f.deg
  le := hle _ _ _ (Charts.Hom.le f)
  mem := f.mem
  close := by
    have h := Close.comap_linear T'.J _ _ (Φc b M κ hΦ hW T.k) (fun c a ↦ M (Pi.single a 1) c)
      (dw_Φc b hb M κ hΦ hW T.k) f.close
    convert h using 1
    · exact RingHom.ext fun x ↦ congrArg T'.ρ (Φc_sh b M A hτ κ hΦ hW (Charts.Hom.le f) (hle _ _ _ (Charts.Hom.le f)) x)
    · rfl

def functor (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) (K₁ : Charts F₁) (K₂ : Charts F₂)
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k))
    (hle : ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) : K₁.Obj ⥤ K₂.Obj where
  obj := objMap b hb hbV M κ hΦ hW
  map f := homMap b hb hbV M A hτ κ hΦ hW hle f
  map_id T := Charts.hom_ext (fun _ ↦ rfl) (map_zero A)
  map_comp f f' := Charts.hom_ext (fun _ ↦ rfl) (map_add A _ _)

def coef (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V)
    (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂)
    (hτ : ∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) (K₁ : Charts F₁) (K₂ : Charts F₂)
    (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k))
    (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k))
    (hle : ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) :
    CoefMap (Hol.comap b hb hbV).toRingHom K₂.Oc K₁.Oc where
  G := functor b hb hbV M A hτ K₁ K₂ κ hΦ hW hle
  α T := RingHom.id T.C
  naturality _ _ := rfl
  smul T r c := (Algebra.smul_def (A := T.C) (Hol.comap b hb hbV r) c).symm

end GlobalTheory.AnPer.ChartMap

namespace GlobalTheory.AnPer

theorem period_pullback_eq_of_chartMap : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∀ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k)) (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)), (∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) → ∀ (r₁ : Real K₁ s₁ σ₁) (r₂ : Real K₂ s₂ σ₂) (β : B₂ →+* B₁) (φ : X₁ ⟶ X₂) (m : IsMor (dp0 B₂) s₂ (dp0 B₁) s₁ β φ), (∀ x, σ₁ (β x) = Hol.comap b hb hbV (σ₂ x)) → (∀ k, spMap (Hol.comap _ (hΦ k) (hW k)).toRingHom ≫ r₂.x (κ k) = r₁.x k ≫ φ) → ∀ (c : FirstDeRham s₂) (per₂ : Λ₂ →+ Hol F₂.V) (per₁ : Λ₁ →+ Hol F₁.V), (∀ l, per₁ l = Hol.comap b hb hbV (per₂ (A l))) → r₂.coef.pull1 c = K₂.perCl per₂ → r₁.coef.pull1 (m.pull1 c) = K₁.perCl per₁ := by
  intro I₁ _ g₁ Λ₁ _ F₁ B₁ _ X₁ s₁ σ₁ I₂ _ g₂ Λ₂ _ F₂ B₂ _ X₂ s₂ σ₂ b hb hbV M A hτ K₁ K₂ κ hΦ hW hle r₁ r₂ β φ m
    hσ hx c per₂ per₁ hper hc
  let n := ChartMap.coef b hb hbV M A hτ K₁ K₂ κ hΦ hW hle
  let θ : (m.coef.comp r₁.coef).G ⟶ (r₂.coef.comp n).G :=
    { app := fun T ↦
        { φ := { RingHom.id T.C with
            commutes' := fun r ↦ congrArg (algebraMap (Hol F₁.V) T.C) (hσ r) }
          φ₀ := RingHom.id (T.C ⧸ T.J)
          comm := fun _ ↦ rfl
          dp := letI := T.ratAlg
            isDPMorphism_of_rat T.δ (ChartMap.objMap b hb hbV M κ hΦ hW T).δ (RingHom.id T.C) fun _ h ↦ h
          pt := by
            change spMap (RingHom.id (T.C ⧸ T.J)) ≫ (spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ r₁.x T.k) ≫ φ =
              spMap (((Ideal.Quotient.mk T.J).comp T.ρ).comp (Hol.comap _ (hΦ T.k) (hW T.k)).toRingHom) ≫
                r₂.x (κ T.k)
            rw [Cris.spMap_id, Category.id_comp, Category.assoc, ← hx T.k,
              Cris.spMap_comp (Hol.comap _ (hΦ T.k) (hW T.k)).toRingHom, Category.assoc] }
      naturality := fun _ _ _ ↦ Thick.hom_ext fun _ ↦ rfl }
  have e₁ : r₁.coef.pull1 (m.pull1 c) = (m.coef.comp r₁.coef).pull1 c := (m.coef.pullCohomologyOne_comp r₁.coef c).symm
  have e₂ : (m.coef.comp r₁.coef).pull1 c = (r₂.coef.comp n).pull1 c :=
    CoefMap.pullCohomologyOne_eq_of_natTrans _ _ θ (fun _ _ ↦ rfl) c
  have e₃ : n.pullbackOneCocycle (K₂.perZ per₂) = K₁.perZ per₁ := by
    refine Subtype.ext ?_
    funext T T' f
    exact (congrArg (algebraMap (Hol F₁.V) T'.C) (hper f.deg)).symm
  rw [e₁, e₂, r₂.coef.pullCohomologyOne_comp n c, hc, Charts.perCl, CoefMap.pullCohomologyOne_class, e₃, Charts.perCl]

end GlobalTheory.AnPer

namespace GlobalTheory.AnPer.CmpCore

theorem period_pullback_eq_of_chartMap_class_alt : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∀ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K) (hΦ : ∀ k, AnalyticOnNhd ℂ (fun p : Tot I₁ g₁ ↦ ((b p.1, M p.2) : Tot I₂ g₂)) (K₁.W k)) (hW : ∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)), (∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k)) → ∀ (r₁ : Real K₁ s₁ σ₁) (r₂ : Real K₂ s₂ σ₂) (β : B₂ →+* B₁) (φ : X₁ ⟶ X₂) (m : IsMor (dp0 B₂) s₂ (dp0 B₁) s₁ β φ), (∀ x, σ₁ (β x) = Hol.comap b hb hbV (σ₂ x)) → (∀ k, spMap (Hol.comap _ (hΦ k) (hW k)).toRingHom ≫ r₂.x (κ k) = r₁.x k ≫ φ) → ∀ (c : FirstDeRham s₂) (per₂ : Λ₂ →+ Hol F₂.V) (per₁ : Λ₁ →+ Hol F₁.V), (∀ l, per₁ l = Hol.comap b hb hbV (per₂ (A l))) → r₂.coef.pull1 c = K₂.perCl per₂ → r₁.coef.pull1 (m.pull1 c) = K₁.perCl per₁ :=
  @GlobalTheory.AnPer.period_pullback_eq_of_chartMap

end GlobalTheory.AnPer.CmpCore
