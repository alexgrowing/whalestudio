import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameAut

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame

section Op

variable (K : Type) [CommRing K] (n : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ)

def wtOp (g : ι → GL (Fin n) K) : Module.End K (NablaT K n mu) :=
  ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : Kˣ) : K) • grp K n mu g

theorem wtOp_apply (g : ι → GL (Fin n) K) (u : NablaT K n mu) :
    wtOp K n mu sh g u = ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : Kˣ) : K) • grp K n mu g u := rfl

theorem wtOp_one : wtOp K n mu sh 1 = 1 := by
  simp [wtOp, grp]

theorem wtOp_mul (g h : ι → GL (Fin n) K) : wtOp K n mu sh (g * h) = wtOp K n mu sh g * wtOp K n mu sh h := by
  simp only [wtOp, grp, map_mul, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, smul_mul_smul_comm]

def wtHom : (ι → GL (Fin n) K) →* Module.End K (NablaT K n mu) where
  toFun := wtOp K n mu sh
  map_one' := wtOp_one K n mu sh
  map_mul' := wtOp_mul K n mu sh

end Op

end GlobalTheory.FrameAut

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL

namespace GlobalTheory.FrameAut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

def labOf (j : Fin D.R.m) (t : p.P.T) (Q : (blk p j t).Pl) : HeightOneSpectrum (𝓞 D.host.E) := Formalism.DivisionValues.conjPl (plOf p j t Q)

def IsSystemOf (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} {F : Frame l D.what₂.Tau N} {e0 : D.what₂.LL →+* PadicAlgCl l}
    {ix : F.I → (blk p j t).Pl × ℕ} {inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)} (T : Tied p j t F e0 ix inc)
    (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl l) (π : Submodule ℂ (UA D.host.E N → ℂ)) : Prop :=
  IsAutRepU π ∧
  (∀ τ, ∃ lam : DomWeight N, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
    HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
  (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → IsUnramU π v) ∧
  ∀ Q : (blk p j t).Pl, IsUnramU π (labOf p j t Q) ∧
    ∃ (σ : SmIrr (GL (Fin N) ((labOf p j t Q).adicCompletion D.host.E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU N (labOf p j t Q)) ((cLoc (labOf p j t Q)).comp (locU N (labOf p j t Q)).subtype) σ.ρ ∧
      GlobalTheory.LFun.HasSatGL (labOf p j t Q) σ.ρ S ∧
      ∀ i, (ix i).1 = Q → T.io (θ i) = GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E (labOf p j t Q)) N S (ix i).2

def PlacesOk (j : Fin D.R.m) (t : p.P.T) (l : ℕ) : Prop :=
  (∀ Q : (blk p j t).Pl, IsSplitAt (labOf p j t Q) ∧
    (labOf p j t Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j t Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
    Ideal.absNorm (labOf p j t Q).asIdeal = (blk p j t).q Q ∧
    (((l : ℕ) : 𝓞 D.host.E) ∈ (labOf p j t Q).asIdeal ↔ ((l : ℕ) : 𝓞 D.host.E) ∈ (plOf p j t Q).asIdeal)) ∧
  {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
    ¬ ∃ Q : (blk p j t).Pl, ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t Q).asIdeal ∧ labOf p j t Q = v}.Finite ∧
  ∀ ν ∈ (blk p j t).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j t).q Q : ℝ) ^ ((blk p j t).n - (blk p j t).t)

open Classical in

def AutAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  PlacesOk p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) ∧
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (T : Tied p j (p.R.mu w) F R.e0 R.ix inc)
    (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res P.Nr (mu τ))) → F.IsEig mu θ →
    ∃ π, IsSystemOf p j (p.R.mu w) T mu θ π

def AutSt : Prop := InRange fun _ _ _ _ p j P W w => AutAt p j P W w

end GlobalTheory.FrameAut

end
