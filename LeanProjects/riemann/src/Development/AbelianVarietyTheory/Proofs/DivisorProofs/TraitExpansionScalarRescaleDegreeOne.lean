import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SecMoveK
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointFlatOfModificationOfDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Rescale

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (g z) ∈ U)
    (a : Γ(X, U)) : gs (g ≫ f) z U a = (g.stalkMap z).hom (gs f (g z) U a) := by
  rw [gs_stalkMap (g ≫ f) z U h, gs_stalkMap f (g z) U h, Scheme.Hom.stalkMap_comp]
  rfl

theorem cst_zero' {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) : cst q z 0 = 0 := by
  simp only [cst, gs_eq q z ⊤ trivial, map_zero]

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem gs_scal {V : Type} [CommRing V] {Y Z : Scheme.{0}} (q : Y ⟶ Sp V) (r : Z ⟶ Y) (z : Z) (a : V) :
    gs r z ⊤ (scal q a) = cst (r ≫ q) z a :=
  gs_pull r q z ⊤ trivial _

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

theorem cancel (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
    (hα : Flat C.α) (b : W) (hb : b ≠ 0) (s₁ : SecK C.P.L.L T.β 1) (s₂ : SecK C.P.L.L C.α 1)
    (h : ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J,
      Good C.P.L.L z J → cst (p ≫ T.G.hom) z b * sval s₁ p z J = cst (p ≫ T.G.hom) z b * sval s₂ p' z J)
    (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left) (hp : p ≫ T.β = p' ≫ C.α) (z : Z)
    (J : (Z ⟶ C.G.left) → C.P.L.L.ι) (hJ : Good C.P.L.L z J) : sval s₁ p z J = sval s₂ p' z J := by
  haveI := T.U.smooth
  haveI : Flat (pullback.fst T.β C.α ≫ T.G.hom) := inferInstance
  obtain ⟨g, rfl, rfl⟩ : ∃ g, g ≫ pullback.fst T.β C.α = p ∧ g ≫ pullback.snd T.β C.α = p' :=
    ⟨pullback.lift p p' hp, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨J₀, hJ₀, e₀⟩ := exists_good C.P.L.L C.P.L.isLB (g z) (K := Unit)
    (fun _ => pullback.fst T.β C.α ≫ T.β) (fun _ => J ((g ≫ pullback.fst T.β C.α) ≫ T.β)) (fun _ _ _ => rfl)
    (fun _ => hJ ((g ≫ pullback.fst T.β C.α) ≫ T.β))
  have key := h _ (pullback.fst T.β C.α) (pullback.snd T.β C.α) pullback.condition (g z) J₀ hJ₀
  have eJ : J₀ (pullback.snd T.β C.α ≫ C.α) = J₀ (pullback.fst T.β C.α ≫ T.β) :=
    congrArg J₀ pullback.condition.symm
  have A₁ : sval s₁ (g ≫ pullback.fst T.β C.α) z J = (g.stalkMap z).hom (sval s₁ (pullback.fst T.β C.α) (g z) J₀) := by
    rw [sval_of s₁ _ z J (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => (e₀ ()).symm),
      sval_of s₁ _ (g z) J₀ (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => rfl)]
    exact gs_comp_stalk g _ z _ (hJ₀.mem _ _) _
  have A₂ : sval s₂ (g ≫ pullback.snd T.β C.α) z J = (g.stalkMap z).hom (sval s₂ (pullback.snd T.β C.α) (g z) J₀) := by
    have e₁ : J ((g ≫ pullback.snd T.β C.α) ≫ C.α) = J₀ (pullback.fst T.β C.α ≫ T.β) := by
      rw [e₀ (), Category.assoc, Category.assoc, pullback.condition]
    rw [sval_of s₂ _ z J (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => e₁),
      sval_of s₂ _ (g z) J₀ (fun _ => J₀ (pullback.fst T.β C.α ≫ T.β)) (fun _ => eJ)]
    refine gs_comp_stalk g _ z _ ?_ _
    exact Set.mem_iInter.2 fun _ => by rw [← eJ]; exact hJ₀ (pullback.snd T.β C.α ≫ C.α)
  have hz : sval s₁ (pullback.fst T.β C.α) (g z) J₀ = sval s₂ (pullback.snd T.β C.α) (g z) J₀ := by
    have h0 : cst (pullback.fst T.β C.α ≫ T.G.hom) (g z) b *
        (sval s₁ (pullback.fst T.β C.α) (g z) J₀ - sval s₂ (pullback.snd T.β C.α) (g z) J₀) = 0 := by
      rw [mul_sub, key, sub_self]
    have := GlobalTheory.cst_dvd_of_cst_mul_eq_zero (pullback.fst T.β C.α ≫ T.G.hom) (g z) (a := b) (b := 0)
      (fun c hc => zero_dvd_iff.2 ((mul_eq_zero.1 hc).resolve_left hb)) h0
    rw [cst_zero', zero_dvd_iff, sub_eq_zero] at this
    exact this
  rw [A₁, A₂, hz]

end GlobalTheory.Mum.Rescale

namespace GlobalTheory.Mum.Rescale

theorem cst_unit {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (z : Z) {u : V} (hu : IsUnit u) :
    IsUnit (cst q z u) := by
  obtain ⟨w, rfl⟩ := hu
  refine ⟨⟨cst q z w, cst q z ↑w⁻¹, ?_, ?_⟩, rfl⟩
  · rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, Units.mul_inv, ReciprocityTheory.ChartRestriction.G.H1.cst_one]
  · rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, Units.inv_mul, ReciprocityTheory.ChartRestriction.G.H1.cst_one]

theorem rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (F₁ : IntFam (maximalIdeal R) D.toPre 1) (θ₀ : SecK C.P.L.L C.α 1) (r t : R) (x : FractionRing R), r ≠ 0 → x * algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) t → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a b : W) (v : Wˣ), a ≠ 0 → b ≠ 0 → T.Exp a b θ₀ F₁ → b * T.φ t = a * T.φ r * v → T.Exp 1 (v : W) (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal C.A.A.hom x) θ₀) F₁ := by
  intro R _ _ _ _ D C F₁ θ₀ r t x hr hx W _ _ _ T a b v ha hb hE hbt
  obtain ⟨σ, ⟨σ', f', hC, hP, hX⟩, hσ⟩ := hE
  have hw : PGen T.ℓ := (isGen_iff T.ℓ).1 T.ℓ_gen
  obtain ⟨s, hs⟩ := sec_upK hw C.P.L.isLB T.U.LG.isLB (φ' := fun _ : Fin 1 => 𝟙 T.G.left)
    (ε := fun _ => ((1 : ℕ) : ℤ)) σ'
  have gen : ∀ ψ : Fin 1 → (T.G.left ⟶ C.G.left), ψ = (fun _ => T.β) →
      ∀ s : LB.Sec (LB.LinComb C.P.L.L ψ (fun _ => ((1 : ℕ) : ℤ))), ∃ s' : SecK C.P.L.L T.β 1,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) z J, sval s' r z J = sval s r z J := by
    rintro ψ rfl s
    exact ⟨s, fun _ _ _ _ => rfl⟩
  obtain ⟨s', hs'⟩ := gen _ (funext fun _ => Category.id_comp _) s
  have hs₁ : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) (z : Z) J J', Good C.P.L.L z J → Good T.U.LG.L z J' →
      sval s' r z J = (gw T.ℓ r z (J (r ≫ T.β)) (J' r)).val * sval σ' r z J' := by
    intro Z r z J J' hJ hJ'
    rw [hs', hs Z r z J J' hJ hJ']
    simp [pw, Fin.prod_univ_one]
  let σ₁ : SecK C.P.L.L T.β 1 := ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal T.G.hom (v : W)) s'
  have hC₁ : T.Carries (v : W) σ' σ₁ := by
    intro Z r z J J' hJ hJ'
    rw [sval_secScale _ _ _ _ hJ, hs₁ Z r z J J' hJ hJ', pow_one, _root_.mul_assoc]
  have hα : Flat C.α := MorphismProperty.of_isPullback (P := @Flat) C.α_cart.1.flip (GlobalTheory.T.genericPoint_flat_of_modification_of_domain R C.toModif)
  refine ⟨σ₁, ⟨σ', f', hC₁, hP, hX⟩, fun Z p p' hpp z J hJ => ?_⟩
  rw [gs_scal, ReciprocityTheory.ChartRestriction.G.H1.cst_one, _root_.one_mul]
  refine cancel C T hα b hb σ₁ _ (fun Z p p' hpp z J hJ => ?_) Z p p' hpp z J hJ
  choose I hI using fun χ : Z ⟶ T.G.left => exists_chart T.U.LG.isLB (χ z)
  have hI' : Good T.U.LG.L z I := hI
  have e1 := hC Z p z J I hJ hI'
  have e2 := hσ Z p p' hpp z J hJ
  rw [e1, gs_scal, gs_scal, pow_one] at e2
  rw [sval_secScale _ _ _ _ hJ, sval_secScale _ _ _ _ hJ, hs₁ Z p z J I hJ hI', gs_scal, gs_scal]

  have hρ : ∀ c : R, cst (p ≫ T.G.hom) z (T.φ c) = cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) c) := by
    intro c
    have hm : (p ≫ T.G.hom) ≫ spMap T.φ = (p' ≫ C.A.A.hom) ≫ spMap (algebraMap R (FractionRing R)) := by
      have h1 : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
      have h2 : C.α ≫ C.G.hom = C.A.A.hom ≫ C.gp := C.α_cart.1.w
      calc (p ≫ T.G.hom) ≫ spMap T.φ = p ≫ T.G.hom ≫ T.ξ ≫ C.π := by rw [T.ξ_π, Category.assoc]
        _ = (p ≫ T.β) ≫ C.G.hom ≫ C.π := by rw [← Category.assoc T.G.hom, ← h1]; simp only [Category.assoc]
        _ = (p' ≫ C.α) ≫ C.G.hom ≫ C.π := by rw [hpp]
        _ = p' ≫ C.A.A.hom ≫ C.gp ≫ C.π := by rw [Category.assoc, ← Category.assoc C.α, h2]; simp only [Category.assoc]
        _ = (p' ≫ C.A.A.hom) ≫ spMap (algebraMap R (FractionRing R)) := by rw [C.gp_π, Category.assoc]
    rw [← cst_comp, hm, cst_comp]
  have hrU : IsUnit (cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) r)) :=
    cst_unit _ _ (isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr))
  have hx' : cst (p' ≫ C.A.A.hom) z x * cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) r) =
      cst (p' ≫ C.A.A.hom) z (algebraMap R (FractionRing R) t) := by
    rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, hx]
  have hbt' : cst (p ≫ T.G.hom) z b * cst (p ≫ T.G.hom) z (T.φ t) =
      cst (p ≫ T.G.hom) z a * cst (p ≫ T.G.hom) z (T.φ r) * cst (p ≫ T.G.hom) z (v : W) := by
    rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, ← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, ← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, hbt]
  rw [hρ, hρ, ← hx'] at hbt'
  have hsc : cst (p ≫ T.G.hom) z b * cst (p' ≫ C.A.A.hom) z x =
      cst (p ≫ T.G.hom) z a * cst (p ≫ T.G.hom) z (v : W) := by
    apply hrU.mul_right_cancel
    linear_combination hbt'
  linear_combination (cst (p ≫ T.G.hom) z (v : W)) * e2 - sval θ₀ p' z J * hsc

end GlobalTheory.Mum.Rescale
