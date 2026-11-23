import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatV

theorem val_pow_mul_eq {R : Type} [CommRing R] (t b : Rˣ) (a : R) (k : ℕ) :
    ((t ^ k : Rˣ) : R) * a = a * ((b⁻¹ ^ k : Rˣ) : R) * (((t * b) ^ k : Rˣ) : R) := by
  have e : ((b⁻¹ ^ k : Rˣ) : R) * ((b ^ k : Rˣ) : R) = 1 := by
    rw [← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
  rw [mul_pow, Units.val_mul]
  linear_combination (-(((t ^ k : Rˣ) : R) * a)) * e

theorem exists_isValue : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)), g.IsGen → ∀ (k : ℕ) (σ : SecM (𝟙 X) L k), ∃ ω : Ω, IsValue (𝟙 _) L x g k σ ω := by
  intro X L hL Ω _ _ x g hg k σ
  obtain ⟨j₀, hj₀⟩ : ∃ i, ∀ p : Sp Ω, x.base p ∈ L.U i := by
    have hc : x.base (IsLocalRing.closedPoint Ω) ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact ⟨i, fun p => ((IsLocalRing.specializes_closedPoint p).map x.continuous).mem_open (L.U i).isOpen hi⟩
  have hW : (⊤ : (Sp Ω).Opens) ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀) :=
    fun p _ => Set.mem_iInter.2 fun _ => hj₀ p
  have hG : (⊤ : (Sp Ω).Opens) ≤ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => j₀) :=
    fun p _ => Set.mem_iInter.2 fun _ => hj₀ p
  let ωs : Γ(Sp Ω, ⊤) := ((Sp Ω).presheaf.map (homOfLE hW).op).hom
      ((x.app (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀))).hom (σ.f fun _ => j₀)) *
    ((ReciprocityTheory.ChartRestriction.G.Semi.res hG (g.s fun _ => j₀))⁻¹ ^ k).val
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ωs, fun Z r z J hJ => ?_⟩
  have hinv : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ωs) = ωs := by
    simp
  rw [hinv]
  have hj : (r ≫ x) z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => J ((r ≫ x) ≫ 𝟙 X)) := hJ.mem _ (r ≫ x)
  have hj0 : (r ≫ x) z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀) := hW (show r z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  have hgj : r z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => J (r ≫ x ≫ 𝟙 X)) := hJ.mem _ r
  have hg0 : r z ∈ LB.wchart L (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => j₀) := hG (show r z ∈ (⊤ : (Sp Ω).Opens) from trivial)
  rw [sval_of σ (r ≫ x) z J _ (fun _ => rfl), sec_trans σ (r ≫ x) z hj hj0, val_of g r z J _ (fun _ => rfl),
    gen_trans hg r z hgj hg0]
  have hT : trF (L := L) (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) (r ≫ x) z (fun _ => J ((r ≫ x) ≫ 𝟙 X)) (fun _ => j₀) =
      trF (L := L) (fun _ : PUnit => x ≫ 𝟙 X) (fun _ => 1) r z (fun _ => J (r ≫ x ≫ 𝟙 X)) (fun _ => j₀) ^ k := by
    simp only [trF]
    rw [Category.assoc]
    simp
  have hp := (gs_pull r x z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀)) hj0 (σ.f fun _ => j₀)).symm
  have hm : r z ∈ (⊤ : (Sp Ω).Opens) := trivial
  have h1 := gs_mul r z ⊤ hm (((Sp Ω).presheaf.map (homOfLE hW).op).hom
      ((x.app (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j₀))).hom (σ.f fun _ => j₀)))
    ((ReciprocityTheory.ChartRestriction.G.Semi.res hG (g.s fun _ => j₀))⁻¹ ^ k).val
  have h2 := gm_res r z hG hm (g.s fun _ => j₀)
  rw [gs_res r z hW hm, gs_unit r z ⊤ hm, map_pow, map_inv] at h1
  erw [h2] at h1
  rw [hT, hp, h1]
  exact val_pow_mul_eq _ _ _ _

end GlobalTheory.HeatV
