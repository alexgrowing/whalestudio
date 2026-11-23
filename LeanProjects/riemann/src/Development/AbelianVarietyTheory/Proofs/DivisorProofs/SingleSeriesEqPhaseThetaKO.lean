import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseRatAtOfPhaseOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicLiftEqGeometricClassSumAllTuples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstUpToCenter
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordEqOfPerConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
noncomputable section

namespace GlobalTheory.AdTh.VecSeries
open GlobalTheory.AdTh GlobalTheory.AdTh.PhaseMap

set_option maxHeartbeats 2000000 in

theorem singleSeries_eq_phase_thetaKO : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → IoExt R → ∀ (χ : (AE D)ˣ →* Circle) (ω : WeilRep D i), IsWeilTw R i χ ω → ∀ (Q : Finset (Pl D.host.E)) (Ω : DatFn D i) (φ' : WO (Vc D i) (Wc D i) → ℂ), VecOf R i Q Ω φ' → ∀ (ka : ℂ), GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → ∀ (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g' : ℕ) (Dc : GlobalTheory.Dict.Dic (T.Q.Dw ((i : ℕ) + 1)) T.Q.c (O i).s0 X g' (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))) (vr : GlobalTheory.Harm.Var X.Ψ (T.Q.Dw ((i : ℕ) + 1)).p X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.AdTh.IsVarOf (Vc D i) (Wc D i) X (T.Q.Dw ((i : ℕ) + 1)).p vr → ∀ (h : GA D (Vc D i)) (w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ (g γ : GA D (Wc D i)), γ ∈ GQ (Wc D i) → singleSeries R i ω φ' h ((O i).c0' y) w g = ka * thetaKO ω h (γ * g) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) φ' (MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)))) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hR i hOP hE χ ω hω Q Ω φ' hφ ka hka P y hy X g' Dc vr hM hp hv h w hw g γ hγ
  have hθ : IsInfFam R.θ := hR.models.inf
  have hstd := hOP.2.lift.std
  have hPr := (GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A _ R F hR i A.μ0 hstd).1
  have hψ := hPr.weil.std
  obtain ⟨f1, f2, f3, f4, f5⟩ := GlobalTheory.AdTh.VecFockCore.vec_fock_core D G Pl0 T0 A _ R F hR i A.μ0 hstd
  have hBV : ∀ τ, (R.BV i τ)ᴴ * R.BV i τ = 1 := fun τ => by
    obtain ⟨ε, hε, h1, -⟩ := hR.models.BV i τ
    rw [gramAt_one hPr.std, Matrix.mul_one] at h1
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with h | h
    · rw [h.1]; rfl
    · exact absurd a.2 (not_lt.2 h.2)
  have hon : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ =>
    ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [gramAt_one hPr.std], by simp⟩

  have hthφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ' := by
    obtain ⟨⟨hψ', h0⟩, e, -, hth⟩ := hφ
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ' hθ hth h0.theta

  have hsub : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ P',
      pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f P' =
        pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) f
          (MvPolynomial.aeval (fun k => ∑ b, MvPolynomial.C
              (if (k.2.1 : ℕ) < ((Wc D i).sig (tauE D k.1)).1 then (R.BV i k.1)⁻¹ k.2.2 b
                else (starRingEnd ℂ) ((R.BV i k.1)⁻¹ k.2.2 b)) * MvPolynomial.X (k.1, k.2.1, b)) P') := by
    intro f hf P'
    have h := GlobalTheory.AdTh.SourceBasis.pureTensorO_mul_source D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ (fun _ => 1) (R.BV i) _ _ _ f5
      (fun τ => (trace_parity (f5 τ)).1) (fun τ => by simp) (fun τ => det_ne_zero (hBV τ)) f hf P'
    simp only [Matrix.one_mul] at h
    exact h
  have hinj : Function.Injective (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i A.μ0)) :=
    GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ _ _ _ _ _ _ f4 f3 hon f5 hPr.sigV hPr.sigW _ f1 f2
      (GlobalTheory.AdTh.VecNeCore.thetaVector_ne_zero_core D G Pl0 T0 A _ R F hR i hstd)

  have hlt : ∀ ℓ : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank, (vr (Dc.eL ℓ)).2.2 = ℓ.2.2 ∧
      ((ℓ.1 = tauE D (vr (Dc.eL ℓ)).1 ∧ ((vr (Dc.eL ℓ)).2.1 : ℕ) = ℓ.2.1) ∨
        (ℓ.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (tauE D (vr (Dc.eL ℓ)).1) ∧
          ((vr (Dc.eL ℓ)).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1)) := by
    intro ℓ
    have hP := hT.j.pins
    have hm : ∀ τ, τ ∉ X.Ψ → (T.Q.Dw ((i : ℕ) + 1)).mult τ ≤ X.p0 := fun τ hτ => by
      unfold Datum.mult
      rw [if_neg fun h : τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 => hτ ((hM.psi τ).2
        (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ h)), hp]
    obtain ⟨h1, h2⟩ := GlobalTheory.AdTh.Dic.letter Dc (fun τ => RingHom.ext fun _ => rfl) hm ℓ
    obtain ⟨g1, g2, g3⟩ := hv (Dc.eL ℓ)
    refine ⟨g2.trans h1, ?_⟩
    rcases h2 with ⟨k, e1, e2, e3⟩ | ⟨k, e1, e2, e3⟩
    · rw [e1, Sum.elim_inl] at g3
      exact Or.inl ⟨e2.trans g1, g3.trans e3⟩
    · rw [e1, Sum.elim_inr] at g3
      exact Or.inr ⟨by rw [← g1]; exact e2, by rw [g3, e3]⟩

  have hio := hka (fun ℓ => vr (Dc.eL ℓ)) hlt w hw A.μ0 y
  have hpol : MvPolynomial.rename (fun ℓ => vr (Dc.eL ℓ)) (MvPolynomial.map (inC (O i).c') ((O i).io y)) =
      MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)) := by
    rw [hy, MvPolynomial.rename_rename]
    exact congrArg (MvPolynomial.rename _) (MvPolynomial.map_map _ _ _)

  have hS : (MvPolynomial.aeval (fun k => ∑ b, MvPolynomial.C
              (if (k.2.1 : ℕ) < ((Wc D i).sig (tauE D k.1)).1 then (R.BV i k.1)⁻¹ k.2.2 b
                else (starRingEnd ℂ) ((R.BV i k.1)⁻¹ k.2.2 b)) * MvPolynomial.X (k.1, k.2.1, b))) (R.ioP i (PiTensorProduct.tprod ℂ w) ((O i).c0' y)) =
      ka • MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)) := by
    apply hinj
    rw [map_smul, ← hsub _ f1, ← hpol]
    exact hio

  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i)
      (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) φ' (MvPolynomial.rename vr (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)))) :=
    GlobalTheory.FockTheta.ptStable D R.ψ R.θ hψ hθ _ _ _ _ _ _ φ' _ hthφ
  have hmove : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → thetaKO ω h g f = thetaKO ω h (γ * g) f := fun f hf => by
    have e1 : ((h, γ * g) : GA D (Vc D i) × GA D (Wc D i)) = (1, γ) * (h, g) := by simp
    rw [thetaKO, thetaKO, e1, map_mul]
    exact (hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ f hf)).symm
  have hsm : ∀ k f, thetaKO ω h k (ka • f) = ka * thetaKO ω h k f := fun k f => by
    rw [thetaKO, thetaKO, map_smul]
    rfl
  show thetaKO ω h g (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
    (onb (R.MW i (sg0 D A))) φ' (R.ioP i (PiTensorProduct.tprod ℂ w) ((O i).c0' y))) = _
  rw [hsub _ hthφ, hS, map_smul, hsm, hmove _ hth]

end GlobalTheory.AdTh.VecSeries
