import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfIsVacO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKIntMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilTwistSeries

theorem twist_val_mem {D : D7} {pd : ℕ} {k : Type} [Field k] {σ : k →+* ℂ} {δ : Formalism.L2.Host.HChar D.host.E}
    {δc : (AE D)ˣ →* Circle} (h : IsTwist pd σ δ δc) (x : (AE D)ˣ) : ((δc x : Circle) : ℂ) ∈ σ.fieldRange := by
  obtain ⟨hE, ⟨n, hn, ho⟩, -, ht, -, hv⟩ := h
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  have hfin := (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ δ).1
  have hu : ∀ v, v ∉ hfin.toFinset → δ.UnrAt v := fun v hv' => by
    by_contra hc
    exact hv' (hfin.mem_toFinset.2 hc)
  refine GlobalTheory.TwistValues.char_mem δc δ hE hn ho σ.fieldRange (fun P k => ?_) x
  exact GlobalTheory.TwistValues.locK_mem δ (GlobalTheory.RationalValues.unitsIn σ.fieldRange) hfin.toFinset ht
    (GlobalTheory.TypeValues.inf_eq_one δ hn ho) hu
    (fun v hv' => by
      obtain ⟨y, hy⟩ := hv v (hu v hv')
      show ((δ.val v : ℂˣ) : ℂ) ∈ σ.fieldRange
      refine ⟨y, ?_⟩
      rw [hy, Formalism.L2.Host.HChar.valTw]
      simp) P k

theorem theta_weil_twist : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
      ∀ (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsTwist C.d.pd C.σ₂ δ δc →
      ∀ om : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ),
        IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).1
          (Lift.chrTh (Lift.tup R.mu0 δc) R.eta ((i : ℕ) + 1)).2 om →
      ∀ s ∈ GfC (Vc D i), ∀ f : WO (Vc D i) (Wc D i) → ℂ,
        IsLevDatum R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (T.Q.l.M * C.d.pd) C.σ₂.fieldRange (R.vacP i) f →
      ∀ w ∈ ratVec R i (c0L i) C.σ₂.fieldRange,
        ∃ c ∈ C.σ₂.fieldRange, ∃ dd : GA D (Wc D i) → ℂ, (MuVal (Wc D i) δc dd ∨ MuVal (Wc D i) δc⁻¹ dd) ∧
          ∀ g, thetaKO om s g (harmVec R i u w f) = c * (dd g * thetaKO (R.ωP i A.μ0) s g (harmVec R i u w f)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hJ hL hG hFam hMod hP hT i hV hpin gramR c0R c0L hB u hu C hC δ δc hδ om hom s hs
    f hf w hw
  have hψ : IsStdChar D R.ψ (-1) := (hP.ωP i A.μ0).std
  have hvac := (hP.vP i A.μ0).1
  have hθ : IsInfFam R.θ := hvac.2.inf
  have hf0 : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := GlobalTheory.OneMapRef.isThetaFunO_of_isVacO hvac
  obtain ⟨P, e, Φ, -, -, -, -, -, hTh⟩ := hf
  have hft : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hθ hTh hf0
  have hH : IsThetaFunO R.ψ (Vc D i) (Wc D i) (harmVec R i u w f) :=
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hft _
  have hxi : R.xi A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0))
  have hmu : R.toLevCh.mu A.μ0 = Lift.tup R.mu0 (1 : (AE D)ˣ →* Circle) := by
    unfold LevCh.mu
    rw [hxi]
  have hω : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh R.mu0 R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh R.mu0 R.eta ((i : ℕ) + 1)).2 (R.ωP i A.μ0) := by
    have h := hP.ωP i A.μ0
    rw [hmu, GlobalTheory.SplitChange.chrTh_tup] at h
    simpa only [mul_one] using h
  rw [GlobalTheory.SplitChange.chrTh_tup] at hom
  have hδH : IsHeckeChar D δc := hδ.1.1
  have hδF : ∀ a, δc (idF D a) = 1 := GlobalTheory.GridWeil.triv_base hδ.1 hδ.2.2.1
  obtain ⟨nV, hnV, -⟩ := GlobalTheory.Member.exists_muVal D (Vc D i) δc hδH hδF
  obtain ⟨nW, hnW, -⟩ := GlobalTheory.Member.exists_muVal D (Wc D i) δc hδH hδF
  obtain ⟨x, hx⟩ := hnV.1 s
  refine ⟨(nV s)⁻¹, ?_, nW, Or.inl hnW, fun g => ?_⟩
  · rw [hnV.2 s x hx]
    exact inv_mem (twist_val_mem hδ x)
  · rw [GlobalTheory.SplitChange.thetaKO_twist hω hδH hδF hom hnV hnW s g hH]
    ring

end GlobalTheory.WeilTwistSeries
