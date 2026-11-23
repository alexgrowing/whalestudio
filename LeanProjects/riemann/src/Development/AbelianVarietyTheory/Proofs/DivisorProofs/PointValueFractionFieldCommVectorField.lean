import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
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

namespace GlobalTheory.GenericVal

theorem exists_affine_le_preimage {X : Scheme.{0}} {Ω : Type} [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ x ⁻¹ᵁ U := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := x.base (IsLocalRing.closedPoint Ω)) (U := ⊤) trivial
  refine ⟨U, hU, fun p _ => ?_⟩
  have hsp : (p : PrimeSpectrum Ω) ⤳ IsLocalRing.closedPoint Ω :=
    (PrimeSpectrum.le_iff_specializes (R := Ω) p (IsLocalRing.closedPoint Ω)).1
      (show p.asIdeal ≤ IsLocalRing.maximalIdeal Ω from IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
  exact hsp.mem_open (x ⁻¹ᵁ U).isOpen hyU

theorem valR_generic : ∀ (X : Scheme.{0}) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (dd : Fld X) (δ : Derivation ℤ Ω Ω) (δL : Derivation ℤ (FractionRing Ω) (FractionRing Ω)), IsField ⊤ dd → (∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd O f) = δ (valR x O f)) → (∀ ω, δL (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ ω)) → ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (dd O f) = δL (valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f) := by
  intro X Ω _ _ _ x dd δ δL hF hx hδL O f hO
  obtain ⟨U, hU, hxU⟩ := exists_affine_le_preimage x
  set ξ := spMap (algebraMap Ω (FractionRing Ω)) ≫ x with hξ
  have hξU : ⊤ ≤ ξ ⁻¹ᵁ U := fun q _ => hxU (show (spMap (algebraMap Ω (FractionRing Ω))).base q ∈ (⊤ : (Sp Ω).Opens) from trivial)
  let q₀ : Sp (FractionRing Ω) := default
  have hq : ξ.base q₀ ∈ O ⊓ U := ⟨hO trivial, hξU trivial⟩
  obtain ⟨s, hsle, hsmem⟩ := hU.exists_basicOpen_le (V := O ⊓ U) ⟨ξ.base q₀, hq⟩ hq.2
  set W := X.basicOpen s with hWdef
  have hWO : W ≤ O := hsle.trans inf_le_left
  have hWU : W ≤ U := X.basicOpen_le s
  have hW : ⊤ ≤ ξ ⁻¹ᵁ W := fun q _ => by
    rw [Subsingleton.elim q q₀]; exact hsmem
  letI : Algebra Γ(X, U) Γ(X, W) := (resG X hWU).toAlgebra
  haveI : IsLocalization.Away s Γ(X, W) := hU.isLocalization_basicOpen s
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) (resG X hWO f)
  have hmu : IsUnit (resG X hWU (m : Γ(X, U))) := IsLocalization.map_units Γ(X, W) m
  change resG X hWO f * resG X hWU (m : Γ(X, U)) = resG X hWU a at hm
  have vres : ∀ {V' : X.Opens} (e : W ≤ V') (g : Γ(X, V')), valR ξ W (resG X e g) = valR ξ V' g :=
    fun e g => GlobalTheory.Points.valR_res ξ e hW g
  have vU : ∀ g : Γ(X, U), valR ξ U g = algebraMap Ω (FractionRing Ω) (valR x U g) := fun g =>
    GlobalTheory.Points.valR_spMap_comp _ x U hxU g
  have hdd : ∀ g : Γ(X, U), dd W (resG X hWU g) = resG X hWU (dd U g) := fun g => hF.2.2 U W hWU le_top g
  have hddO : dd W (resG X hWO f) = resG X hWO (dd O f) := hF.2.2 O W hWO le_top f
  have hL := hF.2.1 W le_top (resG X hWO f) (resG X hWU (m : Γ(X, U)))
  rw [hm, hdd, hdd, hddO] at hL
  have e1 := congrArg (valR ξ W) hL
  have e2 := congrArg (valR ξ W) hm
  simp only [GlobalTheory.Points.valR_add ξ W hW, GlobalTheory.Points.valR_mul ξ W hW, vres, vU, hx U _ hxU] at e1 e2
  have hM : IsUnit (algebraMap Ω (FractionRing Ω) (valR x U (m : Γ(X, U)))) := by
    have h1 := hmu.map (GlobalTheory.Points.valMap ξ W hW).hom
    rwa [← GlobalTheory.Points.valR_eq, vres, vU] at h1
  have e3 := congrArg δL e2
  rw [Derivation.leibniz, hδL, hδL, smul_eq_mul, smul_eq_mul] at e3
  apply hM.mul_left_cancel
  linear_combination -e1 - e3

end GlobalTheory.GenericVal
