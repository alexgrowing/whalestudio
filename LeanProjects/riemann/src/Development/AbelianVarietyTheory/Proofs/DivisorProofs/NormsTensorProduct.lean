import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CoverNorm

theorem isRatSec_pull_tens {X Z : Scheme.{0}} [IsIntegral Z] (A B : LB X) (j : Z ⟶ X)
    {r : (A.pull j).ι → Z.functionFieldˣ} {s : (B.pull j).ι → Z.functionFieldˣ}
    (hr : IsRatSec (A.pull j) r) (hs : IsRatSec (B.pull j) s) :
    IsRatSec ((CechPic.tens A B).pull j)
      fun i => r (fun _ => (i PUnit.unit).1) * s fun _ => (i PUnit.unit).2 := by
  have cA {i : ((CechPic.tens A B).pull j).ι} :
      ((CechPic.tens A B).pull j).U i ≤ (A.pull j).U fun _ => (i PUnit.unit).1 :=
    fun _ hx => Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).1
  have cB {i : ((CechPic.tens A B).pull j).ι} :
      ((CechPic.tens A B).pull j).U i ≤ (B.pull j).U fun _ => (i PUnit.unit).2 :=
    fun _ hx => Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).2
  intro i i' h
  have lA := inf_le_inf (cA (i := i)) (cA (i := i'))
  have lB := inf_le_inf (cB (i := i)) (cB (i := i'))
  rw [Units.val_mul, Units.val_mul, hr _ _ (lA h), hs _ _ (lB h), mul_mul_mul_comm,
    ← fnOf_resG lA h, ← fnOf_resG lB h, ← map_mul,
    InducedPull.val_pull_g _ j i i' (InducedPull.inf_le _ j i i')]
  congr 2
  refine Eq.trans ?_ (map_mul _ _ _).symm
  refine congrArg₂ (· * ·) ?_ ?_
  · refine (congrArg _ (InducedPull.val_pull_g A j _ _ (InducedPull.inf_le A j _ _))).trans ?_
    have e := (Scheme.Hom.appLE_map j (InducedPull.inf_le A j (fun _ => (i PUnit.unit).1)
      fun _ => (i' PUnit.unit).1) (homOfLE lA).op).trans
      (Scheme.Hom.map_appLE j (InducedPull.inf_le _ j i i') (homOfLE (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left))).op).symm
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom e) (A.g (i PUnit.unit).1 (i' PUnit.unit).1).val
  · refine (congrArg _ (InducedPull.val_pull_g B j _ _ (InducedPull.inf_le B j _ _))).trans ?_
    have e := (Scheme.Hom.appLE_map j (InducedPull.inf_le B j (fun _ => (i PUnit.unit).2)
      fun _ => (i' PUnit.unit).2) (homOfLE lB).op).trans
      (Scheme.Hom.map_appLE j (InducedPull.inf_le _ j i i') (homOfLE (le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right))).op).symm
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom e) (B.g (i PUnit.unit).2 (i' PUnit.unit).2).val

theorem norms_tens : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L₁ L₂ : HermLB V.p) (f₁ : Y.X → Y.Fn) (a₁ : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l₁ : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (f₂ : Y.X → Y.Fn) (a₂ : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l₂ : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ), Norms V L₁ f₁ a₁ l₁ → Norms V L₂ f₂ a₂ l₂ → Norms V (L₁.tens L₂) (fun x => f₁ x * f₂ x) (fun σ y => a₁ σ y + a₂ σ y) (fun v e y => l₁ v e y + l₂ v e y) := by
  intro F _ _ Y V L₁ L₂ f₁ a₁ l₁ f₂ a₂ l₂ h₁ h₂
  obtain ⟨r₁, hr₁, hu₁, hc₁, hv₁⟩ := h₁
  obtain ⟨r₂, hr₂, hu₂, hc₂, hv₂⟩ := h₂
  have cA {i : ((L₁.tens L₂).B.pull V.j).ι} {x : V.G} (hx : x ∈ ((L₁.tens L₂).B.pull V.j).U i) :
      x ∈ (L₁.B.pull V.j).U fun _ => (i PUnit.unit).1 :=
    Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).1
  have cB {i : ((L₁.tens L₂).B.pull V.j).ι} {x : V.G} (hx : x ∈ ((L₁.tens L₂).B.pull V.j).U i) :
      x ∈ (L₂.B.pull V.j).U fun _ => (i PUnit.unit).2 :=
    Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).2
  have split : ∀ (i : ((L₁.tens L₂).B.pull V.j).ι) (g₁ g₂ : Y.Fn),
      V.φ (g₁ * g₂) * (((r₁ (fun _ => (i PUnit.unit).1) * r₂ (fun _ => (i PUnit.unit).2) : V.G.functionFieldˣ)) :
        V.G.functionField) =
      (V.φ g₁ * (r₁ (fun _ => (i PUnit.unit).1) : V.G.functionField)) *
        (V.φ g₂ * (r₂ (fun _ => (i PUnit.unit).2) : V.G.functionField)) := by
    intro i g₁ g₂
    rw [map_mul, Units.val_mul]
    ring
  refine ⟨fun i => r₁ (fun _ => (i PUnit.unit).1) * r₂ (fun _ => (i PUnit.unit).2),
    isRatSec_pull_tens L₁.B L₂.B V.j hr₁ hr₂, fun i x hx => ?_, fun σ z y y' i e₁ e₂ hi => ?_,
    fun v e y z yt i e₁ e₂ hi => ?_⟩
  · rw [split]
    exact (hu₁ _ x (cA hx)).mul (hu₂ _ x (cB hx))
  · have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e₁]
      rfl
    have H₁ := hc₁ σ z y y' _ e₁ e₂ (cA hi)
    have H₂ := hc₂ σ z y y' _ e₁ e₂ (cB hi)
    have U₁ := hu₁ _ _ (cA hi)
    have U₂ := hu₂ _ _ (cB hi)
    rw [hπ] at U₁ U₂
    have n₁ := norm_ne_zero_iff.2 (ratVal_ne_zero (y := z) U₁)
    have n₂ := norm_ne_zero_iff.2 (ratVal_ne_zero (y := z) U₂)
    beta_reduce
    rw [split, ratVal_mul U₁.regAt U₂.regAt, norm_mul, Real.log_mul n₁ n₂, H₁, H₂]
    change _ = _ - ((L₁.φ _).φ (i PUnit.unit).1 y' + (L₂.φ _).φ (i PUnit.unit).2 y') / 2
    ring
  · have H₁ := hv₁ v e y z yt (fun _ => (i PUnit.unit).1) e₁ e₂ (fun x hx => (hi hx).1)
    have H₂ := hv₂ v e y z yt (fun _ => (i PUnit.unit).2) e₁ e₂ (fun x hx => (hi hx).2)
    have hmem : below z ∈ ((L₁.tens L₂).B.pull V.j).U i := by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ (L₁.tens L₂).B.U (i PUnit.unit) := by
        rw [← e₂]
        exact hi (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hπ : V.π (below z) = below y.1 := by
      rw [← e₁]
      rfl
    have U₁ := hu₁ _ _ (cA hmem)
    have U₂ := hu₂ _ _ (cB hmem)
    rw [hπ] at U₁ U₂
    rw [split, SmallSec.valAt_mul U₁.regAt U₂.regAt, map_mul,
      Real.log_mul (e.w.pos (SmallSec.valAt_ne_zero U₁)).ne' (e.w.pos (SmallSec.valAt_ne_zero U₂)).ne', ← H₁, ← H₂]

end GlobalTheory.CoverNorm
