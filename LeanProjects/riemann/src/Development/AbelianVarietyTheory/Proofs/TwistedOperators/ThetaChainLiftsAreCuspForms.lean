import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermLiftIsotropicSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftLowerTowerVanishingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowerWittTowerIsotropicSplitEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharactersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftCuspObj

variable {D : D7}

theorem multT_induction {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S)
    (J : Set (GA D W)) (χ : GA D W → ℂ) (P : (GA D W → ℂ) → Prop) (h0 : P 0)
    (hadd : ∀ φ φ', P φ → P φ' → P (φ + φ')) (hsmul : ∀ (c : ℂ) φ, P φ → P (c • φ))
    (hcusp : ∀ φ, IsAutFunSm θ W φ → IsCuspFun W φ → P φ)
    (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) : P (F v) := by
  obtain ⟨T, hT, rfl⟩ := Submodule.mem_map.1 hF
  have key : ∀ m, P (T m) := by
    intro m
    have hT' : T ∈ Submodule.span ℂ {T | IsMultMap θ M J χ T} := hT
    clear hF hT
    induction hT' using Submodule.span_induction with
    | mem x hx => exact hcusp _ ((show IsMultMap θ M J χ x from hx).aut m) ((show IsMultMap θ M J χ x from hx).cusp m)
    | zero => simpa using h0
    | add x y _ _ hx hy => simpa using hadd _ _ hx hy
    | smul a x _ hx => simpa using hsmul a _ hx
  induction v using PiTensorProduct.induction_on with
  | smul_tprod a m => simpa using hsmul a _ (key m)
  | add x y hx hy => simpa using hadd _ _ hx hy

theorem liftInt_add {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    {φ φ' : H → ℂ} {g : G} (h : IntegrableOn (fun x => th g x s * φ x) 𝓕 ν)
    (h' : IntegrableOn (fun x => th g x s * φ' x) 𝓕 ν) :
    Lift.liftInt ν 𝓕 th s (φ + φ') g = Lift.liftInt ν 𝓕 th s φ g + Lift.liftInt ν 𝓕 th s φ' g := by
  simp only [Lift.liftInt, Pi.add_apply, mul_add]
  exact integral_add h h'

theorem liftInt_smul {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    (c : ℂ) (φ : H → ℂ) (g : G) :
    Lift.liftInt ν 𝓕 th s (c • φ) g = c * Lift.liftInt ν 𝓕 th s φ g := by
  simp only [Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  ext x
  ring

theorem liftInt_zero {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    (g : G) : Lift.liftInt ν 𝓕 th s (0 : H → ℂ) g = 0 := by
  simp [Lift.liftInt]

structure Good {V V' W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ))
    (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (κ : Measure (NI V C)) (𝓝 : Set (NI V C))
    (f : WO V W → ℂ) (f' : WO V' W → ℂ) (g : GA D V) (c : ℂ) (φ : GA D W → ℂ) : Prop where
  integ : ∀ g₁, IntegrableOn (fun h => thetaKO ω g₁ h f * φ h) 𝓕 ν
  integ' : IntegrableOn (fun h => thetaKO ω' 1 h f' * φ h) 𝓕 ν
  mean : IntegrableOn (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g)) 𝓝 κ
  eq : ∫ n in 𝓝, Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g) ∂κ =
    c * Lift.liftInt ν 𝓕 (thetaKO ω') f' φ 1

section Good

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)}
  {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {κ : Measure (NI V C)} {𝓝 : Set (NI V C)}
  {f : WO V W → ℂ} {f' : WO V' W → ℂ} {g : GA D V} {c : ℂ}

theorem Good.zero : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c 0 where
  integ g₁ := by simp
  integ' := by simp
  mean := by
    simp only [liftInt_zero]
    exact integrableOn_zero
  eq := by simp [liftInt_zero]

theorem Good.add {φ φ' : GA D W → ℂ} (h : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c φ)
    (h' : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c φ') : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c (φ + φ') := by
  have e : ∀ x : GA D V, Lift.liftInt ν 𝓕 (thetaKO ω) f (φ + φ') x =
      Lift.liftInt ν 𝓕 (thetaKO ω) f φ x + Lift.liftInt ν 𝓕 (thetaKO ω) f φ' x :=
    fun x => liftInt_add (h.integ x) (h'.integ x)
  refine ⟨fun g₁ => ?_, ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, mul_add]
    exact Integrable.add (h.integ g₁) (h'.integ g₁)
  · simp only [Pi.add_apply, mul_add]
    exact Integrable.add h.integ' h'.integ'
  · simp only [e]
    exact Integrable.add h.mean h'.mean
  · simp only [e]
    rw [integral_add h.mean h'.mean, h.eq, h'.eq, liftInt_add h.integ' h'.integ', mul_add]

theorem Good.smul {φ : GA D W → ℂ} (a : ℂ) (h : Good C ω ω' ν 𝓕 κ 𝓝 f f' g c φ) :
    Good C ω ω' ν 𝓕 κ 𝓝 f f' g c (a • φ) := by
  refine ⟨fun g₁ => ?_, ?_, ?_, ?_⟩
  · have e : (fun x => thetaKO ω g₁ x f * (a • φ) x) = fun x => a * (thetaKO ω g₁ x f * φ x) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact Integrable.const_mul (h.integ g₁) a
  · have e : (fun x => thetaKO ω' 1 x f' * (a • φ) x) = fun x => a * (thetaKO ω' 1 x f' * φ x) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact Integrable.const_mul h.integ' a
  · simp only [liftInt_smul]
    exact Integrable.const_mul h.mean a
  · simp only [liftInt_smul]
    rw [integral_const_mul, h.eq]
    ring

end Good

theorem constTerm_multT (hct : TowerConstTerm D) (hP : GlobalTheory.Published.CuspRapidDecay)
    {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {χS χT χT' : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)}
    (hω : IsWeilDatumO ψ V W χS χT ω) (hω' : IsWeilDatumO ψ V' W χS χT' ω')
    {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν)
    {S : D.what₂.Tau → SPar} (M : DSModel W S) (J : Set (GA D W)) (χ : GA D W → ℂ)
    (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hlow : ∀ f', IsThetaFunO ψ V' W f' → Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) 1 = 0)
    (κ : Measure (NI V C)) (𝓝 : Set (NI V C)) (hκ : κ.IsHaarMeasure) (h𝓝 : IsFundamentalDomain (NIQ V C) 𝓝 κ)
    (g : GA D V) : ∫ n in 𝓝, Lift.liftInt ν 𝓕 (thetaKO ω) f (F v) ((n : GA D V) * g) ∂κ = 0 := by
  obtain ⟨μ, 𝓨, h𝓨⟩ : ∃ μ 𝓨, IsCovolOne (ratMx D W.rank r) μ 𝓨 := GlobalTheory.MixModel.exists_isCovolOne D W.rank r
  have hfor := hct V V' W r C B hs ψ χS χT χT' ω ω' hω hω' μ 𝓨 h𝓨 ν 𝓕 hν h𝓕 κ 𝓝 hκ h𝓝
  have hgood : Good C ω ω' ν 𝓕 κ 𝓝 f (res V V' W C B μ 𝓨 (ω (g, 1) f)) g ((κ 𝓝).toReal : ℂ) (F v) :=
    multT_induction θ M J χ
      (fun φ => Good C ω ω' ν 𝓕 κ 𝓝 f (res V V' W C B μ 𝓨 (ω (g, 1) f)) g ((κ 𝓝).toReal : ℂ) φ)
      Good.zero (fun _ _ h h' => Good.add h h') (fun a _ h => Good.smul a h)
      (fun φ hφ hc => by
        obtain ⟨-, -, -, h1, h2, h3, h4⟩ := hfor φ (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc) hc f hf g
        exact ⟨h1, h2, h3, h4⟩) F hF v
  obtain ⟨-, -, hres, -⟩ := hfor 0 GlobalTheory.Grow.RapidDec.zero (by intro _ _ _ _ _ _ _ _; simp) f hf g
  rw [hgood.eq, hlow _ hres, mul_zero]

theorem liftCusp : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    ∀ D : D7, GlobalTheory.Chain.LiftCusp D := by
  intro hDS hHC hP D k V W M M' θ ψ hθ hch ω hω ν 𝓕 hν h𝓕 J χ F hF v f hf r C hC κ 𝓝 hκ h𝓝 g
  obtain ⟨V', B, hs, hsig⟩ := GlobalTheory.T.exists_lowerWittTower_isotropicSplitEmbedding D V _ M r C hC
  have hr : 1 ≤ r := by
    obtain ⟨h0, -⟩ := hC
    exact h0
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  obtain ⟨η, h1, h2, h3, h4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  obtain ⟨ω', hW'⟩ := GlobalTheory.T.exists_weilDatum_of_splittingCharacters D ψ hW.std V' W χS χT (Exists.intro η (And.intro h1 (And.intro h4 (And.intro h3 h2))))
    hW.hecS hW.hecT (resEta_parity hW.resS (by have := hs.rank; omega)) hW.resT
  have hst : GlobalTheory.Chain.IsStepWeil k ψ V' W ω' := Exists.intro χS (Exists.intro χT (And.intro hW' hexp))
  exact constTerm_multT (GlobalTheory.T.constantTermLift_isotropicSubspace D) hP hs hθ hW hW' hν h𝓕 M' J χ F hF v hf
    (fun f' hf' => congrFun (GlobalTheory.T.thetaLift_lowerTower_vanishing hDS hHC hP D k r V' W M' θ ψ hθ hch hr hsig ω' hst ν 𝓕 hν h𝓕 J χ F hF v f'
      hf') 1) κ 𝓝 hκ h𝓝 g

end GlobalTheory.LiftCuspObj

end
