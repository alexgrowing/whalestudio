import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedAdelicMetricIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedOfPositiveNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLineBundleInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MSmoothAndSemiPosIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetWeightIsCInfOfPotential
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmoothHermitianMetricProjectiveVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSmoothAtGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinationMetricLocalExpansionStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ModelTwistLift

open GlobalTheory.Mean4O.HermCover in

theorem exists_smooth_lift : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (Mb : Adl (cxSt F) Y) (ι : Type) [Fintype ι] (ρ : ι → Adl (cxSt F) Y) (t : ι → ℝ) (g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), IsComb Mb ρ t g → (∀ σ, (cxSt F).mSmooth Y σ Mb.D (Mb.m σ)) → ∀ (M : TrueGeo.Model Y) (L : ι → HermLB M.p) (m : ℕ+), (∀ i, (ρ i).Induced M (L i) m 0) → ∃ w : ∀ σ : 𝓞 F →+* ℂ, CxPts M.p σ → ℝ, (∀ σ y, CInfAt (w σ) y) ∧ ∀ (σ : F →+* ℂ) (y : Pts Y σ) (y' : CxPts M.p (σ.comp (algebraMap (𝓞 F) F))), y'.1 = y.1 ≫ M.j → w _ y' = 2 * g σ y := by
  intro F _ _ Y Mb ι _ ρ t g hC hMb M L m hL
  have hρ : ∀ i σ, (cxSt F).mSmooth Y σ (ρ i).D ((ρ i).m σ) := fun i =>
    (InducedSemiPos.mSmooth_and_semiPos_iff F _ Y (ρ i) M (L i) m 0 (hL i)).1
  have hY : ∀ σ (z : Pts Y σ), CInfAt (g σ) z := by
    intro σ z0
    obtain ⟨c, K, aM, a, U, fM, f, hc, hU, hfM, hf, hev⟩ := GlobalTheory.T.combination_metric_local_expansion F Y Mb ι ρ t g hC hρ σ z0
    have h1 : CInfAt (fun z => Real.log (‖ratVal U z‖ ^ 2) + ∑ i, a i * lnN ((ρ i).m σ) (f i) z +
        aM * lnN (Mb.m σ) fM z + K) z0 :=
      (((MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.cInfAt_log_normSq_ratVal hU).add
        (GoodMetric.SmoothMetric.cInfAt_sum Finset.univ _ fun i _ =>
          (GlobalTheory.T.log_norm_smooth_at_generator F Y σ _ _ (hρ i σ) (f i) z0 (hf i)).const_mul (a i))).add
        ((GlobalTheory.T.log_norm_smooth_at_generator F Y σ _ _ (hMb σ) fM z0 hfM).const_mul aM)).add (cInfAt_const K z0)
    refine (h1.const_mul c⁻¹).congr ?_
    filter_upwards [hev] with z hz
    rw [← hz, inv_mul_cancel_left₀ hc]
  let lift : ∀ σ : 𝓞 F →+* ℂ, CxPts M.p σ → Pts Y (extEmb σ) := fun σ y' =>
    ⟨M.pb.lift y'.1 (spMap (extEmb σ)) (y'.2.trans (spMap_extEmb σ)), M.pb.lift_snd _ _ _⟩
  have hlift : ∀ σ (y' : CxPts M.p σ), (lift σ y').1 ≫ M.j = y'.1 := fun σ y' => M.pb.lift_fst _ _ _
  have hg : ∀ (τ τ' : F →+* ℂ) (z : Pts Y τ) (z' : Pts Y τ'), τ = τ' → z.1 = z'.1 → g τ z = g τ' z' := by
    intro τ τ' z z' h hz
    subst h
    obtain rfl : z = z' := Subtype.ext hz
    rfl
  refine ⟨fun σ y' => 2 * g (extEmb σ) (lift σ y'), fun σ y' => ?_, fun τ y y' hy => ?_⟩
  · let mp : Pts Y (extEmb σ) → CxPts M.p σ := fun z =>
      ⟨z.1 ≫ M.j, by rw [Category.assoc, M.pb.w, ← Category.assoc, z.2, ← spMap_extEmb]⟩
    have hlm : ∀ z, lift σ (mp z) = z := fun z =>
      Subtype.ext (M.pb.hom_ext (hlift σ (mp z)) (by rw [(lift σ (mp z)).2, z.2]))
    have hmz : mp (lift σ y') = y' := Subtype.ext (hlift σ y')
    rw [← hmz]
    refine OnModelCInf.baseChange_cInfAt F M.X Y.X M.p Y.str M.j M.pb (extEmb σ) σ mp (fun _ => rfl) _ _ ?_
    refine ((hY _ (lift σ y')).const_mul 2).congr (Filter.Eventually.of_forall fun z => ?_)
    show 2 * g (extEmb σ) (lift σ (mp z)) = 2 * g (extEmb σ) z
    rw [hlm]
  · show 2 * g _ (lift _ y') = 2 * g τ y
    congr 1
    refine hg _ _ _ _ (extEmb_restrict τ) ?_
    refine M.pb.hom_ext ((hlift _ y').trans hy) ?_
    rw [(lift _ y').2, y.2, extEmb_restrict τ]

end GlobalTheory.ModelTwistLift
