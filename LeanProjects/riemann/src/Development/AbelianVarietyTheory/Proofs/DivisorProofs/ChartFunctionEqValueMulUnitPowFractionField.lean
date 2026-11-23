import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV

set_option autoImplicit false

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FracPt

theorem stalkIso_gs {K : Type} [CommRing K] [IsLocalRing K] {X : Scheme.{0}} (f : Sp K ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (stalkClosedPointIso (CommRingCat.of K)).hom.hom (gs f (closedPoint K) U a) = valR f U a := by
  have e1 : gs f (closedPoint K) U a = (Sp K).presheaf.germ ⊤ (closedPoint K) trivial ((f.appLE U ⊤ h).hom a) := by
    erw [gs_eq f _ U (h trivial)]
    rw [← TopCat.Presheaf.germ_res_apply (Sp K).presheaf (homOfLE h) (closedPoint K) trivial]
    rfl
  erw [e1]
  rw [valR, dif_pos h]
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of K)]
  simp only [CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.FracPt

namespace GlobalTheory.FracPt

theorem valR_spMap_const {Ω K : Type} [CommRing Ω] [CommRing K] (f : Ω →+* K) (ω : Ω) :
    valR (spMap f) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) = f ω := by
  have h : ⊤ ≤ spMap f ⁻¹ᵁ ⊤ := le_rfl
  rw [valR, dif_pos h]
  calc _ = ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ CommRingCat.ofHom f).hom
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) := by
          rw [← Scheme.ΓSpecIso_naturality]; rfl
    _ = f ω := by
          have e : (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) = ω := by
            rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
          rw [CommRingCat.hom_comp, RingHom.comp_apply, e, CommRingCat.hom_ofHom]

theorem chart_eq_value_mul_pow : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω]
    (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)) (j : L.ι) (O : X.Opens), O ≤ L.U j →
    ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → ∃ e₀ : (FractionRing Ω)ˣ,
      ∀ (k : ℕ) (σ : SecM (𝟙 X) L k) (ω : Ω), IsValue (𝟙 _) L x g k σ ω →
        valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (rsT (σ.f fun _ => j) O) =
          algebraMap Ω (FractionRing Ω) ω * (e₀ : FractionRing Ω) ^ k := by
  intro X L hL Ω _ _ x g j O hO hxO
  let ηF := spMap (algebraMap Ω (FractionRing Ω))
  let z : Sp (FractionRing Ω) := closedPoint (FractionRing Ω)
  have hz : ((ηF ≫ x) ≫ 𝟙 X) z ∈ L.U j := by
    rw [Category.comp_id]; exact hO (hxO trivial)
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL z (K := PUnit) (fun _ => (ηF ≫ x) ≫ 𝟙 X) (fun _ => j)
    (fun _ _ _ => rfl) (fun _ => hz)
  let φ := (stalkClosedPointIso (CommRingCat.of (FractionRing Ω))).hom.hom
  refine ⟨Units.map φ.toMonoidHom (val g ηF z J), fun k σ ω hv => ?_⟩
  have e := congrArg φ (hv _ ηF z J hJ)
  have hOW : O ≤ (LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ))).U (fun _ => j) :=
    fun y hy => Set.mem_iInter.2 fun _ => hO hy
  rw [sval_of σ (ηF ≫ x) z J (fun _ => j) (fun _ => hJj PUnit.unit)] at e
  erw [← gs_res (ηF ≫ x) z hOW (hxO trivial) (σ.f fun _ => j)] at e
  rw [map_mul, Units.val_pow_eq_pow_val, map_pow] at e
  have e1 := stalkIso_gs (ηF ≫ x) O hxO ((X.presheaf.map (homOfLE hOW).op).hom (σ.f fun _ => j))
  have e2 := stalkIso_gs ηF ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω)
  rw [valR_spMap_const] at e2
  erw [e1, e2] at e
  rw [GlobalTheory.KS.rsT, dif_pos hOW]
  exact e

end GlobalTheory.FracPt
