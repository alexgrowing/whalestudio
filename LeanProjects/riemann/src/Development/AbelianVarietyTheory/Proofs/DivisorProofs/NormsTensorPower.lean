import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverNorm

theorem isRatSec_pull_pow {X Z : Scheme.{0}} [IsIntegral Z] (B : LB X) (j : Z ⟶ X) (m : ℕ)
    {r : (B.pull j).ι → Z.functionFieldˣ} (hr : IsRatSec (B.pull j) r) :
    IsRatSec ((lbPow B m).pull j) fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ m := by
  intro i i' h
  have l₀ : ((lbPow B m).pull j).U i ⊓ ((lbPow B m).pull j).U i' ≤
      (B.pull j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (B.pull j).U fun _ => i' PUnit.unit PUnit.unit :=
    fun _ hx => ⟨InducedPow.mem_chart B j m hx.1, InducedPow.mem_chart B j m hx.2⟩
  have l₁ : ((lbPow B m).pull j).U i ⊓ ((lbPow B m).pull j).U i' ≤
      j ⁻¹ᵁ ((lbPow B m).U (i PUnit.unit) ⊓ (lbPow B m).U (i' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have l₂ : (lbPow B m).U (i PUnit.unit) ⊓ (lbPow B m).U (i' PUnit.unit) ≤
      B.U (i PUnit.unit PUnit.unit) ⊓ B.U (i' PUnit.unit PUnit.unit) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have l₃ : (B.pull j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (B.pull j).U (fun _ => i' PUnit.unit PUnit.unit) ≤
      j ⁻¹ᵁ (B.U (i PUnit.unit PUnit.unit) ⊓ B.U (i' PUnit.unit PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hr _ _ (l₀ h), mul_pow,
    InducedPow.pull_g _ j i i' l₁, InducedPow.pow_g B m _ _ l₂, map_pow, map_pow,
    InducedPow.pull_g B j _ _ l₃, ← fnOf_resG l₀ h]
  congr 3
  have e : j.appLE _ _ l₃ ≫ Z.presheaf.map (homOfLE l₀).op =
      X.presheaf.map (homOfLE l₂).op ≫ j.appLE _ _ l₁ := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  exact congrArg (fun ψ => ψ.hom (B.g (i PUnit.unit PUnit.unit) (i' PUnit.unit PUnit.unit)).val) e

theorem norms_pow : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (m : ℕ), Norms V L f a l → Norms V (L.pow m) (fun x => f x ^ m) (fun σ y => m * a σ y) (fun v e y => m * l v e y) := by
  rintro F _ _ Y V L f a l m ⟨r, hr, hu, hc, hf⟩
  have key : ∀ (g : Y.Fn) (i : ((lbPow L.B m).pull V.j).ι),
      V.φ (g ^ m) * ((r (fun _ => i PUnit.unit PUnit.unit) ^ m : V.G.functionFieldˣ) : V.G.functionField) =
        (V.φ g * (r (fun _ => i PUnit.unit PUnit.unit) : V.G.functionField)) ^ m := by
    intro g i
    rw [map_pow, Units.val_pow_eq_pow_val, mul_pow]
  refine ⟨fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ m, isRatSec_pull_pow L.B V.j m hr, ?_, ?_, ?_⟩
  · intro i x hx
    show UnitAt x (V.φ (f (V.π x) ^ m) * _)
    erw [key]
    exact InducedPow.unitAt_pow (hu _ x (InducedPow.mem_chart L.B V.j m hx)) m
  · intro σ z y y' i e₁ e₂ hi
    have hi' := InducedPow.mem_chart L.B V.j m hi
    have H := hc σ z y y' (fun _ => i PUnit.unit PUnit.unit) e₁ e₂ hi'
    have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e₁]
      rfl
    have hU := hu _ _ hi'
    rw [hπ] at hU
    have h₄ : ((L.pow m).φ _).φ (i PUnit.unit) y' = (m : ℝ) * (L.φ _).φ (i PUnit.unit PUnit.unit) y' :=
      ((L.φ _).zpow_φ _ _ y').trans (by simp)
    show (m : ℝ) * a σ y = Real.log ‖ratVal (V.φ (f (under y) ^ m) * _) z‖ - _
    erw [key, InducedPow.ratVal_pow z hU, norm_pow, Real.log_pow, h₄, H]
    ring
  · intro v e y z yt i e₁ e₂ hi
    have hi' : ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit PUnit.unit) := fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit
    have H := hf v e y z yt (fun _ => i PUnit.unit PUnit.unit) e₁ e₂ hi'
    have hmem : below z ∈ (L.B.pull V.j).U (fun _ => i PUnit.unit PUnit.unit) := by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit PUnit.unit) := by
        rw [← e₂]
        exact hi' (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hπ : V.π (below z) = below y.1 := by
      rw [← e₁]
      rfl
    have hU := hu _ _ hmem
    rw [hπ] at hU
    show (m : ℝ) * l v e y = Real.log (e.w (valAt z (V.φ (f (below y.1) ^ m) * _)))
    erw [key, InducedPow.valAt_pow _ hU.regAt, map_pow, Real.log_pow, H]

end GlobalTheory.CoverNorm
