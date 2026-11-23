import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Definitions.Divisors.SubRedMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorComp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Charts.Obj.cAlg

namespace GlobalTheory.AnPer.TenFam

open GlobalTheory.CatCoh

variable {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀}
  {D : Type} [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) (hπ : IsNilpotent (RingHom.ker π))
  {I : Type} [Fintype I] {F : Fam I g Λ} (K : Charts F) (ν : K₀.K → K.K)
  (Ta : ∀ k, Hol (K.W (ν k)) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k)) (τV : Hol F.V →+* D)
  (hc : ∀ k f, Ta k (K.cst (ν k) f) = τV f ⊗ₜ[ℂ] 1)

def obj (T : K₀.Obj) : K.Obj where
  k := ν T.k
  C := T.ten D
  alg := ((algebraMap D (T.ten D)).comp τV).toAlgebra
  J := T.tenJ π
  nil := T.tenJ_nil π hπ
  ρ := ((Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc).comp (Ta T.k)).toRingHom
  ρ_cst f := by
    change Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc (Ta T.k (K.cst (ν T.k) f)) = τV f ⊗ₜ[ℂ] (1 : T.C)
    rw [hc, Algebra.TensorProduct.map_tmul, map_one]
    rfl

variable (hν : ∀ l k' k, K₀.le l k' k → K.le l (ν k') (ν k))
  (hd : ∀ k a h, Ta k (dw a h) = LinearMap.lTensor D (dw a).toLinearMap (Ta k h))
  (hcl : ∀ l k' k (h₀ : K₀.le l k' k), Close ((RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k'))) ((Ta k').toRingHom.comp (Charts.sh (hν l k' k h₀))) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k')) (K₀.maps h₀))).comp (Ta k)).toRingHom))

include hd hcl in

theorem close {T T' : K₀.Obj} (f : T ⟶ T') :
    Close (T'.tenJ π) ((obj π hπ K ν Ta τV hc T').ρ.comp (Charts.sh (hν _ _ _ (Charts.Hom.le f))))
      ((Charts.Hom.ten D f : T.ten D →+* T'.ten D).comp (obj π hπ K ν Ta τV hc T).ρ) := by
  have h1 := (hcl _ _ _ (Charts.Hom.le f)).map (J' := T'.tenJ π)
    (Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc).toRingHom (fun c hc' ↦ by
      have : (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W T'.k)) ≤
          (T'.tenJ π).comap (Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc).toRingHom :=
        Ideal.map_le_iff_le_comap.2 fun d hd' ↦ by
          change T'.red π (d ⊗ₜ T'.ρc 1) ∈ T'.J
          rw [Charts.Obj.red_tmul, (RingHom.mem_ker).1 hd', map_zero, zero_mul]
          exact T'.J.zero_mem
      exact this hc')
  have h2 := GlobalTheory.AnPer.Close.tensor_comp (Ta T.k) (hd T.k) T'.J (T'.tenJ π) (fun c hc' ↦ by
      change T'.red π (1 ⊗ₜ c) ∈ T'.J
      rw [Charts.Obj.red_tmul]
      exact T'.J.mul_mem_left _ hc')
    (T'.ρc.comp (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k)) (K₀.maps (Charts.Hom.le f))))
    ((Charts.Hom.φc f).comp T.ρc) f.close
  have e1 : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc
      (Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k))
        (K₀.maps (Charts.Hom.le f))) x) = Algebra.TensorProduct.map (AlgHom.id ℂ D)
        (T'.ρc.comp (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k))
        (K₀.maps (Charts.Hom.le f)))) x := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul d c => rfl
  have e2 : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), Algebra.TensorProduct.map (AlgHom.id ℂ D) ((Charts.Hom.φc f).comp T.ρc) x =
      Charts.Hom.ten D f (Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc x) := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul d c => rfl
  have tr : ∀ {W : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C} {a b b' c c' : Hol W →+* C},
      Close J a b → Close J b' c → (∀ h, b h = b' h) → (∀ h, c h = c' h) → Close J a c' := by
    intro W C _ J a b b' c c' p q e e'
    obtain rfl : b = b' := RingHom.ext e
    obtain rfl : c = c' := RingHom.ext e'
    exact Relation.ReflTransGen.trans p q
  exact tr h1 h2 (fun h ↦ e1 (Ta T.k h)) (fun h ↦ e2 (Ta T.k h))

def functor : K₀.Obj ⥤ K.Obj where
  obj := obj π hπ K ν Ta τV hc
  map {T T'} f :=
    { φ := { (Charts.Hom.ten D f : T.ten D →+* T'.ten D) with commutes' := fun d ↦ (Charts.Hom.ten D f).commutes (τV d) }
      deg := f.deg
      le := hν _ _ _ (Charts.Hom.le f)
      mem := fun _ h ↦ Charts.Hom.ten_mem π f h
      close := close π hπ K ν Ta τV hc hν hd hcl f }
  map_id T := Charts.hom_ext (fun b ↦ mp_id (K₀.Ten D) T b) rfl
  map_comp f f' := Charts.hom_ext (fun b ↦ mp_comp (K₀.Ten D) f f' b) rfl

def coef : CoefMap τV K.Oc (K₀.Ten D) where
  G := functor π hπ K ν Ta τV hc hν hd hcl
  α T := RingHom.id (T.ten D)
  naturality _ _ := rfl
  smul T b c := (Algebra.smul_def (A := T.ten D) (τV b) c).symm

theorem main : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀} {D : Type} [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp ℂ} {σ₀ : ℂ →+* Hol F₀.V} (r₀ : Real K₀ s₀ σ₀) (hσ : σ₀ = algebraMap ℂ (Hol F₀.V)) {D₀ : Type} [CommRing D₀] {π₀ : D₀ →+* ℂ} (κ : DividedPowers (RingHom.ker π₀)) {s' : X₀ ⟶ Sp D₀} (hs : s' = s₀ ≫ spMap π₀) (io : D₀ →+* D) (hio : ∀ d, π (io d) = π₀ d) (hπ : IsNilpotent (RingHom.ker π)) {I : Type} [Fintype I] {F : Fam I g Λ} (K : Charts F) {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (r : Real K s σ) (ν : K₀.K → K.K) (hν : ∀ l k' k, K₀.le l k' k → K.le l (ν k') (ν k)) (Ta : ∀ k, Hol (K.W (ν k)) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k)) (τV : Hol F.V →+* D), (∀ k f, Ta k (K.cst (ν k) f) = τV f ⊗ₜ[ℂ] 1) → (∀ k a h, Ta k (dw a h) = LinearMap.lTensor D (dw a).toLinearMap (Ta k h)) → (∀ l k' k (h₀ : K₀.le l k' k), Close ((RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k'))) ((Ta k').toRingHom.comp (Charts.sh (hν l k' k h₀))) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k')) (K₀.maps h₀))).comp (Ta k)).toRingHom)) → ∀ (φ₀ : X₀ ⟶ X), (∀ k, spMap ((Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol (K₀.W k))).comp π) (AlgHom.id ℂ (Hol (K₀.W k))) (fun _ _ ↦ Commute.all _ _)).comp (Ta k)).toRingHom ≫ r.x (ν k) = r₀.x k ≫ φ₀) → ∀ (j : B →+* D₀) (n : IsMor (dp0 B) s κ s' j φ₀), (∀ b, io (j b) = τV (σ b)) → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V) (q : Λ →+ D), (∀ l, q l = τV (per l)) → r.coef.pull1 c = K.perCl per → (r₀.tenCoef π hσ κ hs io hio hπ).pull1 (n.pull1 c) = GlobalTheory.CatCoh.H1.mk _ (K₀.tenZ q) := by
  intro I₀ _ g Λ _ F₀ K₀ D _ _ π X₀ s₀ σ₀ r₀ hσ D₀ _ π₀ κ s' hs io hio hπ I _ F K B _ X s σ r ν hν Ta τV hc hd hcl φ₀ hpt
    j n hj c per q hq hper
  let β := coef π hπ K ν Ta τV hc hν hd hcl
  let θ : (r.coef.comp β).G ⟶ (n.coef.comp (r₀.tenCoef π hσ κ hs io hio hπ)).G :=
    { app := fun T ↦
        { φ := { RingHom.id (T.ten D) with commutes' := fun b ↦ congrArg (algebraMap D (T.ten D)) (hj b).symm }
          φ₀ := Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl
          comm := fun _ ↦ rfl
          dp := letI := T.tenRat (D := D); isDPMorphism_of_rat _ (T.tenδ π) (RingHom.id (T.ten D)) fun _ h ↦ h
          pt := by
            have e : (Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl).comp
                ((Ideal.Quotient.mk (T.tenJ π)).comp (obj π hπ K ν Ta τV hc T).ρ) =
                ((Ideal.Quotient.mk T.J).comp T.ρ).comp ((Algebra.TensorProduct.lift
                  ((Algebra.ofId ℂ (Hol (K₀.W T.k))).comp π) (AlgHom.id ℂ (Hol (K₀.W T.k)))
                  (fun _ _ ↦ Commute.all _ _)).comp (Ta T.k)).toRingHom := by
              have e' : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), T.red π (Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc x) =
                  T.ρc (Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol (K₀.W T.k))).comp π)
                    (AlgHom.id ℂ (Hol (K₀.W T.k))) (fun _ _ ↦ Commute.all _ _) x) := fun x ↦ by
                induction x using TensorProduct.induction_on with
                | zero => simp only [map_zero]
                | add x y hx hy => simp only [map_add, hx, hy]
                | tmul d c =>
                  rw [Algebra.TensorProduct.lift_tmul, map_mul]
                  exact congrArg (· * T.ρc c) (T.ρc.commutes (π d)).symm
              exact RingHom.ext fun h ↦ congrArg (Ideal.Quotient.mk T.J) (e' (Ta T.k h))
            change spMap (Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl) ≫
              spMap ((Ideal.Quotient.mk (T.tenJ π)).comp (obj π hπ K ν Ta τV hc T).ρ) ≫ r.x (ν T.k) =
              (spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ r₀.x T.k) ≫ φ₀
            rw [Category.assoc, ← hpt]
            exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ r.x (ν T.k)) ((Cris.spMap_comp _ _).symm.trans
              ((congrArg spMap e).trans (Cris.spMap_comp _ _)))).trans (Category.assoc _ _ _)) }
      naturality := fun _ _ _ ↦ Thick.hom_ext fun _ ↦ rfl }
  have h1 := (r.coef.comp β).pullCohomologyOne_eq_of_natTrans (n.coef.comp (r₀.tenCoef π hσ κ hs io hio hπ)) θ (fun _ _ ↦ rfl) c
  rw [CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_comp, hper] at h1
  refine h1.symm.trans (congrArg (GlobalTheory.CatCoh.H1.mk _) (Subtype.ext ?_))
  funext T T' f
  change algebraMap D (T'.ten D) (τV (per f.deg)) = algebraMap D (T'.ten D) (q f.deg)
  rw [hq]

end GlobalTheory.AnPer.TenFam
