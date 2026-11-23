import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSdLatTwOExpS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinRatMemLatOOfPerO
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqOfTwoOver
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentVacuumHyperspecialDictionary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateStandardLatticeIsSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfBInt

variable {D : D7}

theorem selfDualC_of (V : HSp D) (hV : V.gram = 1) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : Formalism.L2.Col.IsSdLat N) : IsSelfDualC V N := by
  refine ⟨h.1, fun y => ?_⟩
  have h2 : Formalism.HermitianLatticesTheory.dual (Formalism.L2.Col.hStd D.host.E V.rank) N = N := h.2
  conv_lhs => rw [← h2]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  have e : Formalism.L2.Col.hStd D.host.E V.rank x y = ∑ i, ∑ j, star (x i) * V.gram i j * y j := by
    rw [hV]
    simp [Formalism.L2.Col.hStd, Matrix.one_apply]
  rw [e]

theorem noConj {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hE : IsIdemSum e SS) :
    ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  obtain ⟨⟨es, hes, he⟩, hc⟩ := hE
  intro P hP hP'
  have hv : Formalism.IndefR.Fin.belowPl P = Formalism.IndefR.Fin.belowPl (Formalism.L2.Col.conjPrime₂ P) :=
    HeightOneSpectrum.ext (congrArg HeightOneSpectrum.asIdeal (GlobalTheory.GridPlaces.under_conjP P)).symm
  have h := Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_below_inj hes he hc hP hP' hv
  exact GlobalTheory.ModulusNorm.conjPl_ne_of_isIdemAt (hes P hP) ((GlobalTheory.PlaceDict.conjP_eq_conjPl D P).symm.trans h.symm)

end GlobalTheory.HalfBInt

open GlobalTheory.HalfBInt in

theorem GlobalTheory.HalfBInt.trace_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T ((LinearMap.toMatrix' (y)).reindex (finCongr hT.symm) (finCongr hS.symm)) ((LinearMap.toMatrix' (y)).reindex (finCongr hT.symm) (finCongr hS.symm))) := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc _ _ ΛS ΛT dS dT eS eT y hy
  subst hS hT
  obtain rfl : ΛS = N := SetLike.coe_injective eS
  obtain rfl : ΛT = N' := SetLike.coe_injective eT
  have hnc := noConj hE
  have hyT : y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ΛS (twist₂ ΛT c (expS SS)) := by
    rw [← Formalism.L2.Ker.twist_homomorphism _ _ _ _ ΛS ΛT c _ dS.1.fg hc]
    exact hy
  have hsdT := (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS _ _ ΛT c SS hnc (GlobalTheory.StdMove.isSdLat_of T hP.gT ΛT dT) hc).1
  have dT' : IsSelfDualC T (twist₂ ΛT c (expS SS)) := selfDualC_of T hP.gT _ hsdT
  have hrat := GlobalTheory.AdForm.RatLatPer.finRat_mem_latO_of_perO D ψ θ S T _ _ rfl rfl δ sc hP ΛS (twist₂ ΛT c (expS SS)) ΛS (twist₂ ΛT c (expS SS)) dS dT' rfl rfl y hyT
  have hneg : GlobalTheory.VacUnique.finRat S T (-((LinearMap.toMatrix' y).reindex (finCongr (rfl : T.rank = T.rank).symm) (finCongr (rfl : S.rank = S.rank).symm))) ∈
      latO S T ((ΛS : Set (Fin S.rank → D.host.E))) ((twist₂ ΛT c (expS SS) : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    rw [map_neg]
    exact neg_mem hrat
  have h0 : IsLatVac (heisO ψ S T) (latO S T ((ΛS : Set (Fin S.rank → D.host.E))) ((twist₂ ΛT c (expS SS) : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Set (Fin T.rank → D.host.E)) (fun _ => True)) (0 : WO S T → ℂ) :=
    ⟨fun _ _ => by funext w; simp [heisO], fun _ _ _ _ _ => by funext w; simp [heisO]⟩
  obtain ⟨k, hk, -⟩ := GlobalTheory.LatVacSign.heisO_finRat_sign ψ S T ΛS (twist₂ ΛT c (expS SS)) hP.std dS dT' 0 h0 _ hneg
  exact ⟨k, hk⟩
