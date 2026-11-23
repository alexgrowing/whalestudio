import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagComponentDeep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeBundleIsNefIsBigOfWeight
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GeneratedWeightsMulStableAndBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagComponentDeepStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.HSApp.geometric_hypothesis_of_components : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif) (h : Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict) (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ Λ₀ : ℝ, WtBig P → RatGen TF.X Z Y.U P.u₁ → RatGen TF.X Z Y.U P.u₂ → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ k.beta → 1 ≤ k.abelian₂ → (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ k.abelian₂) → 1 ≤ Λ₀ → (h.data f₁ f₂ th k).ShortFamily 0 Λ₀ → (h.data f₁ f₂ th k).ShortFamily (dimFlag (T.Q.Dw j)) k.LamD → (h.data f₁ f₂ th k).ShortFamily P.T k.LamT → GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ := by
  intro hPr hGD hQ hNad hPrin hSi hFa hLie D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k Λ₀ hW hR₁ hR₂ hB hL hLe h1 hS0 hSD hST
  have hNN := hQ.nef
  have hF := hG.geo
  have hA : IsNef Y.d.c₂.F (h.geo f₁ f₂ th k).LA ∧ IsBig Y.d.c₂.F (h.geo f₁ f₂ th k).LA := by
    apply _root_.GlobalTheory.T.hodge_bundle_isNef_isBig_of_weight <;> assumption
  obtain ⟨hnef, hbig⟩ := hA
  have hbir := GlobalTheory.HSApp.birational_of_ratGen TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k hR₁
  have hbir₂ := GlobalTheory.HSApp.geo_second_birational TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k hR₂
  obtain ⟨hms, hmb⟩ := _root_.GlobalTheory.HSApp.generated_weights_mul_stable_and_bounded hPr D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k hB
  have hnb₂ : IsNef Y.d.c₂.F (h.data f₁ f₂ th k).L₂ ∧ IsBig Y.d.c₂.F (h.data f₁ f₂ th k).L₂ :=
    GlobalTheory.BirationalBig.isNef_and_isBig hQ _ (h.geo f₁ f₂ th k).second.toLinSys
    (h.geo f₁ f₂ th k).alg₂.variety (h.geo f₁ f₂ th k).alg₂.bpf hbir₂
  have hTC : IsTotallyComplex Y.d.c₂.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := Y.d.c₂) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  obtain ⟨hD, hT, -, -, hLam, -, hLD, hLT, -⟩ := Ready.data_numbers h f₁ f₂ th k
  refine ⟨hTC, ?_, ?_, ?_, ?_, ?_, hms, hmb, ?_, ?_, h1, hS0, ?_, ?_⟩
  · exact hbir
  · exact hnef
  · exact hbig
  · exact hnb₂.1
  · exact hnb₂.2
  · intro q σ
    rw [hLam]
    exact hLe q σ
  · rw [hLam]; exact hL
  · rw [hD, hLD]; exact hSD
  · rw [hT, hLT]; exact hST
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_geometric_hypothesis_holds : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif) (h : Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict) (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ Λ₀ : ℝ, WtBig P → RatGen TF.X Z Y.U P.u₁ → RatGen TF.X Z Y.U P.u₂ → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ k.beta → 1 ≤ k.abelian₂ → (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ k.abelian₂) → 1 ≤ Λ₀ → (h.data f₁ f₂ th k).ShortFamily 0 Λ₀ → (h.data f₁ f₂ th k).ShortFamily (dimFlag (T.Q.Dw j)) k.LamD → (h.data f₁ f₂ th k).ShortFamily P.T k.LamT → GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ := by
  first | exact @_root_.GlobalTheory.HSApp.geometric_hypothesis_of_components | exact _root_.GlobalTheory.HSApp.geometric_hypothesis_of_components | (intros; apply _root_.GlobalTheory.HSApp.geometric_hypothesis_of_components <;> assumption)
end
