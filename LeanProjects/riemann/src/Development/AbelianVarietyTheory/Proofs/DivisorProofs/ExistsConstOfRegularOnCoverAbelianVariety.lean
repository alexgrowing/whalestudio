import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.HeatConst

theorem const_of_regular_on_cover : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (I : Type) (W : I → P₀.A.left.Opens), ⨆ i, W i = ⊤ → (∀ i, ⊤ ≤ ξ ⁻¹ᵁ W i) → ∀ y : F, (∀ i, ∃ h : Γ(P₀.A.left, W i), valR ξ (W i) h = y) → ∃ r : K, ψ r = y := by
  intro K _ P₀ F _ ψ ξ hξ hinj I W hW hWξ y hy
  choose h hh using hy
  have hagree : ∀ i j, rsT (h i) (W i ⊓ W j) = rsT (h j) (W i ⊓ W j) := by
    intro i j
    have hij : ⊤ ≤ ξ ⁻¹ᵁ (W i ⊓ W j) := fun p hp => ⟨hWξ i hp, hWξ j hp⟩
    refine sub_eq_zero.1 (hinj _ _ hij ?_)
    rw [GlobalTheory.LogKSBal.valR_eq ξ hij, map_sub, ← GlobalTheory.LogKSBal.valR_eq ξ hij, ← GlobalTheory.LogKSBal.valR_eq ξ hij,
      GlobalTheory.LogKSBal.valR_rsT ξ inf_le_left hij, GlobalTheory.LogKSBal.valR_rsT ξ inf_le_right hij, hh, hh, sub_self]
  obtain ⟨t, ht⟩ := GlobalTheory.KS.exists_rsT_eq W (O := ⊤) (fun _ => le_top) hW.ge h hagree
  obtain ⟨u, hu⟩ := (GlobalTheory.globalFns_holds (Sp K) P₀.A P₀.isAb).2 t
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom u, ?_⟩
  obtain ⟨i, -⟩ : ∃ i, ξ.base (IsLocalRing.closedPoint F) ∈ W i := by
    have : ξ.base (IsLocalRing.closedPoint F) ∈ (⨆ i, W i) := by rw [hW]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have htop : ⊤ ≤ ξ ⁻¹ᵁ (⊤ : P₀.A.left.Opens) := fun _ _ => trivial
  have hc : t = constFn P₀.A.hom ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom u) := by
    rw [← hu]
    simp [constFn, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rw [← hh i, ← ht i, GlobalTheory.LogKSBal.valR_rsT ξ le_top (hWξ i), hc, GlobalTheory.LogKSBal.valR_constFn P₀.A.hom ξ htop hξ]

end GlobalTheory.HeatConst
