import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriesTransportUniformisingIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTraitScalarGenericFibreNonfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitScalarCancelOfIsFieldStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TraitRescale

variable {X Z : Scheme.{0}}

noncomputable def gsTop (f : Z ⟶ X) (z : Z) : Γ(X, ⊤) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (f ⁻¹ᵁ ⊤) z trivial).hom.comp (f.app ⊤).hom

theorem gs_top (f : Z ⟶ X) (z : Z) (a : Γ(X, ⊤)) : gs f z ⊤ a = gsTop f z a := gs_eq f z ⊤ trivial a

theorem scal_comp {A B : Type} [CommRing A] [CommRing B] {Y : Scheme.{0}} (q : Y ⟶ Sp B) (φ : A →+* B) (r : A) :
    scal q (φ r) = scal (q ≫ spMap φ) r := by
  have e := congrArg (fun h => h.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [e]

theorem scal_mul {A : Type} [CommRing A] {Y : Scheme.{0}} (q : Y ⟶ Sp A) (x y : A) :
    scal q (x * y) = scal q x * scal q y := by simp only [scal, map_mul]

theorem scal_one {A : Type} [CommRing A] {Y : Scheme.{0}} (q : Y ⟶ Sp A) : scal q 1 = 1 := by
  simp only [scal, map_one]

theorem gs_top_mul (f : Z ⟶ X) (z : Z) (a b : Γ(X, ⊤)) : gs f z ⊤ (a * b) = gs f z ⊤ a * gs f z ⊤ b :=
  gs_mul f z ⊤ trivial a b

theorem gs_top_one (f : Z ⟶ X) (z : Z) : gs f z ⊤ 1 = 1 := by rw [gs_top, map_one]

theorem gs_scal {A : Type} [CommRing A] {Y : Scheme.{0}} (p : Z ⟶ Y) (q : Y ⟶ Sp A) (z : Z) (r : A) :
    gs p z ⊤ (scal q r) = gs (p ≫ q) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) :=
  gs_pull p q z ⊤ trivial _

theorem gs_scal_compat {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
    (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left) (h : p ≫ T.β = p' ≫ C.α) (z : Z) (c : R) :
    gs p z ⊤ (scal T.G.hom (T.φ c)) = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c)) := by
  rw [scal_comp, scal_comp, gs_scal, gs_scal]
  have e : p ≫ T.G.hom ≫ spMap T.φ = p' ≫ C.A.A.hom ≫ spMap (algebraMap R (FractionRing R)) := by
    have h1 : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
    have h2 : C.α ≫ C.G.hom = C.A.A.hom ≫ C.gp := C.α_cart.1.w
    have h3 : C.gp ≫ C.π = spMap (algebraMap R (FractionRing R)) := C.gp_π
    rw [← T.ξ_π, ← h3, ← Category.assoc T.G.hom, ← h1, ← Category.assoc C.A.A.hom, ← h2]
    simp only [← Category.assoc, h]
  rw [e]

theorem sval_smul {Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (a • s) r z J = gs r z ⊤ a * sval s r z J := by
  have hm := hJ.mem φ r
  unfold sval
  rw [show (a • s).f (fun k => J (r ≫ φ k)) = resG Y le_top a * s.f (fun k => J (r ≫ φ k)) from GlobalTheory.LB.smul_f a s _,
]
  exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a))

end GlobalTheory.Mum.TraitRescale

open GlobalTheory.Mum.TraitRescale in

theorem GlobalTheory.Mum.Trait.exp_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (s : SecK C.P.L.L C.α k) (F : IntFam (maximalIdeal R) D.toPre k) (a b : W) (u : Wˣ) (c₁ c₂ : R), a ≠ 0 → c₂ ≠ 0 → T.φ c₂ * (u : W) * a = T.φ c₁ * b → T.Exp a b s F → T.Exp 1 u (scal C.A.A.hom (algebraMap R (FractionRing R) c₁ / algebraMap R (FractionRing R) c₂) • s) F := by
  intro R _ _ _ hB D C W _ _ _ T k s F a b u c₁ c₂ ha hc₂ hrel hExp
  obtain ⟨σ, ⟨σ', f', hcar, hpull, hexp⟩, hagree⟩ := hExp
  obtain ⟨σ'', hcar''⟩ := GlobalTheory.T.exists_carries_transport_uniformising_iso R D C W T k (u : W) σ'
  refine ⟨σ'', ⟨σ', f', hcar'', hpull, hexp⟩, ?_⟩
  have hφ2 : T.φ c₂ ≠ 0 := fun h0 => hc₂ (T.inj (h0.trans (map_zero T.φ).symm))
  have hb : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hrel
    exact (mul_ne_zero (mul_ne_zero hφ2 u.ne_zero) ha) hrel
  set c : FractionRing R := algebraMap R (FractionRing R) c₁ / algebraMap R (FractionRing R) c₂ with hc
  have hc₂K : algebraMap R (FractionRing R) c₂ ≠ 0 :=
    fun h0 => hc₂ (IsFractionRing.injective R (FractionRing R) (h0.trans (map_zero _).symm))
  have hcc : c * algebraMap R (FractionRing R) c₂ = algebraMap R (FractionRing R) c₁ := div_mul_cancel₀ _ hc₂K
  have key : ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J,
      Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom b) * sval σ'' p z J =
        gs p z ⊤ (scal T.G.hom b) * (gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J) := by
    intro Z p p' h z J hJ
    choose J' hJ' using fun χ : Z ⟶ T.G.left => exists_chart T.U.LG.isLB (χ z)
    have e1 := hcar Z p z J J' hJ hJ'
    have e2 := hcar'' Z p z J J' hJ hJ'
    have e3 := hagree Z p p' h z J hJ

    have m : gs p z ⊤ (scal T.G.hom (T.φ c₂)) * gs p z ⊤ (scal T.G.hom (u : W)) * gs p z ⊤ (scal T.G.hom a) =
        gs p z ⊤ (scal T.G.hom (T.φ c₁)) * gs p z ⊤ (scal T.G.hom b) := by
      have := congrArg (fun w => gs p z ⊤ (scal T.G.hom w)) hrel
      simpa only [scal_mul, gs_top_mul] using this
    rw [gs_scal_compat T p p' h z c₁, gs_scal_compat T p p' h z c₂] at m
    have hC : gs p' z ⊤ (scal C.A.A.hom c) * gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₂)) =
        gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₁)) := by
      rw [← hcc, scal_mul, gs_top_mul]
    have hU : IsUnit (gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₂))) := by
      obtain ⟨v, hv⟩ := Ne.isUnit hc₂K
      have : IsUnit (scal C.A.A.hom (algebraMap R (FractionRing R) c₂)) :=
        IsUnit.of_mul_eq_one (scal C.A.A.hom ((v⁻¹ : (FractionRing R)ˣ) : FractionRing R))
          (by rw [← scal_mul, ← hv, Units.mul_inv, scal_one])
      rw [gs_top]
      exact this.map _
    have e13 := e1.symm.trans e3
    rw [e2]
    apply hU.mul_right_cancel
    linear_combination (gs p z ⊤ (scal T.G.hom (u : W)) *
      gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c₂))) * e13 + sval s p' z J * m -
      (gs p z ⊤ (scal T.G.hom b) * sval s p' z J) * hC
  intro Z p p' h z J hJ
  rw [scal_one, gs_top_one, _root_.one_mul, sval_smul C.P.L.L _ s p' z hJ]
  by_cases hF : IsField R
  · exact GlobalTheory.T.trait_scalar_cancel_of_isField R hB D C W T k σ'' s b c hF hb key Z p p' h z J hJ
  · exact (GlobalTheory.T.isUnit_trait_scalar_genericFibre_nonfield R D C W T Z p p' h hF b hb z).mul_left_cancel (key Z p p' h z J hJ)

end
