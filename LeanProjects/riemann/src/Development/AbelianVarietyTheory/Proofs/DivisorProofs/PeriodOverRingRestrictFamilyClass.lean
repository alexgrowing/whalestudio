import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer

variable {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam I₀ g Λ}
  (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) (θ : Hol F.V →+* R)
  (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k))
  (ρ' : ∀ S : K₀.DObj et M, Hol (K.W (ka S.T.k)) →+* S.T.C)
  (h1 : ∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f))
  (h3 : ∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1))))
    ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S)))

def famObj (S : K₀.DObj et M) : K.Obj where
  k := ka S.T.k
  C := S.T.C
  alg := ((algebraMap R S.T.C).comp θ).toAlgebra
  J := S.T.J
  nil := S.T.nil
  ρ := ρ' S
  ρ_cst := h1 S

def famCoef : CoefMap θ K.Oc (K₀.OD et M) where
  G :=
    { obj := famObj K K₀ et M θ ka ρ' h1
      map {S S'} f :=
        { φ := { (f.1.φ : S.T.C →+* S'.T.C) with commutes' := fun x ↦ f.2 (θ x) }
          deg := f.1.deg
          le := hka (Charts.Hom.le f.1)
          mem := f.1.mem
          close := h3 S S' f }
      map_id _ := Charts.hom_ext (fun _ ↦ rfl) rfl
      map_comp _ _ := Charts.hom_ext (fun _ ↦ rfl) rfl }
  α S := RingHom.id S.T.C
  naturality _ _ := rfl
  smul S d c := (Algebra.smul_def (A := S.T.C) (θ d) c).symm

theorem famCoef_perCl (per : Λ →+ Hol F.V) :
    (famCoef K K₀ et M θ ka hka ρ' h1 h3).pull1 (K.perCl per) = K₀.perClD et M (θ.toAddMonoidHom.comp per) :=
  congrArg (H1.mk _) (Subtype.ext (funext fun _ ↦ funext fun _ ↦ funext fun _ ↦ rfl))

theorem coefD_pull1_of_family (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k))
    (h2 : ∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J)
    {B B₀ D : Type} [CommRing B] [CommRing B₀] [CommRing D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp B₀}
    {σ : B →+* Hol F.V} {σ₀ : B₀ →+* Hol F₀.V} (r : Real K s σ) (r₀ : Real K₀ s₀ σ₀) {J : Ideal D}
    (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io)
    (j : B →+* D) (φ₀ : X₀ ⟶ X) (n : IsMor (dp0 B) s dl s' j φ₀) (h4 : ∀ b, θ (σ b) = io (j b))
    (h5 : ∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀) (c : FirstDeRham s) (per : Λ →+ Hol F.V)
    (hc : r.coef.pull1 c = K.perCl per) (h1 : ∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f))
    (h3 : ∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1))))
      ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S))) :
    (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (θ.toAddMonoidHom.comp per) := by
  let t : (r.coef.comp (famCoef K K₀ et M θ ka hka ρ' h1 h3)).G ⟶ (n.coef.comp (r₀.coefD dl H)).G :=
    { app S :=
        { φ := { RingHom.id S.T.C with commutes' := fun b ↦ congrArg (algebraMap R S.T.C) (h4 b) }
          φ₀ := RingHom.id (S.T.C ⧸ S.T.J)
          comm := fun _ ↦ rfl
          dp := letI := S.T.ratAlg; isDPMorphism_of_rat (C := S.T.C) (C' := S.T.C) _ _ (RingHom.id S.T.C) fun _ h ↦ h
          pt := by
            have e : (Ideal.Quotient.mk S.T.J).comp (ρ' S) = ((Ideal.Quotient.mk S.T.J).comp S.T.ρ).comp (res _) :=
              RingHom.ext fun h ↦ Ideal.Quotient.eq.2 (h2 S h)
            change spMap (RingHom.id (S.T.C ⧸ S.T.J)) ≫ spMap ((Ideal.Quotient.mk S.T.J).comp (ρ' S)) ≫ r.x (ka S.T.k) =
              (spMap ((Ideal.Quotient.mk S.T.J).comp S.T.ρ) ≫ r₀.x S.T.k) ≫ φ₀
            rw [Cris.spMap_id, Category.id_comp, Category.assoc, ← h5, e, Cris.spMap_comp (res _), Category.assoc] }
      naturality _ _ _ := Thick.hom_ext fun _ ↦ rfl }
  refine (n.coef.pullCohomologyOne_comp (r₀.coefD dl H) c).symm.trans ?_
  refine (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ t (fun _ _ ↦ rfl) c).symm.trans ?_
  rw [CoefMap.pullCohomologyOne_comp, hc, famCoef_perCl]

end GlobalTheory.AnPer

open GlobalTheory.AnPer in

theorem GlobalTheory.AnPer.period_restrict_family : ∀ {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam I₀ g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)) (ρ' : ∀ S : K₀.DObj et M, Hol (K.W (ka S.T.k)) →+* S.T.C), (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) → (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) → (∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S))) → ∀ {B B₀ D : Type} [CommRing B] [CommRing B₀] [CommRing D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp B₀} {σ : B →+* Hol F.V} {σ₀ : B₀ →+* Hol F₀.V} (r : GlobalTheory.AnPer.Real K s σ) (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B →+* D) (φ₀ : X₀ ⟶ X) (n : IsMor (dp0 B) s dl s' j φ₀), (∀ b, θ (σ b) = io (j b)) → (∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀) → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), r.coef.pull1 c = K.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (θ.toAddMonoidHom.comp per) :=
  fun K K₀ _ _ et M θ ka hka res ρ' h1 h2 h3 _ _ _ _ _ _ _ _ _ _ _ _ r r₀ _ dl _ _ _ H j φ₀ n h4 h5 c per hc ↦
    coefD_pull1_of_family K K₀ et M θ ka hka ρ' res h2 r r₀ dl H j φ₀ n h4 h5 c per hc h1 h3
