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
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NotMemOfCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulInvGenusLatticeScalarIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralAbsNormPowMulOnIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetIdealCoprimeSplitSupportedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelCharacterIsTameHeckeUnramifiedStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.ClassScalarIntegral

set_option maxHeartbeats 1000000 in

theorem class_scalar_integral : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0 → ∀ a : D.what₂.LL, D.what₂.embLL a = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) → ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * a) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hO v hv hmu hQG hF0 hV0 hdel hMb hRun ℓ' hLev hAct χ ξR ω φ hK Λ h N hU hTb hTM hLN hΛ e Ps yd hh he hPs hs hy hcard a ha lam hTl
  have lemL1 := GlobalTheory.T.exists_coprime_mul_inv_genusLatticeScalar_integral
  have lemHV := GlobalTheory.T.exists_isIntegral_absNorm_pow_mul_onId_of_coprime
  have lemCC := GlobalTheory.T.exists_detIdeal_coprime_splitSupportedPoint
  have lemPSI := GlobalTheory.T.twistedKernelCharacter_isTameHecke_unramified
  obtain ⟨ψ, b, I, _, φs, n, hb0, hbP, hc, hu, hr, htame, hinf⟩ :=
    lemPSI D G Pl0 T0 A T R F κ v₀ fw O hT hC i hO v hv hmu hQG hF0 hV0 hdel hMb hRun ℓ' hLev hAct χ ξR ω φ hK Λ h N hU hTb hTM
      hLN hΛ e Ps yd hh he hPs
  have hp := Formalism.EigenvalueLevelCeiling.plc_prime lam
  obtain ⟨cc, c0, cb, cl, cv⟩ := lemCC D (Vc D i) hO.2.lift.std.1 hO.2.lift.std.2 h e Ps yd he hs hy b hbP _ ψ hc hu hr Λ hΛ
    (Formalism.EigenvalueLevelCeiling.plc lam) hp hTl
  obtain ⟨K, hK1⟩ := lemHV D.host.E ψ I φs n hinf htame b hb0 hu cc c0 cb
  obtain ⟨m, hm, hm1⟩ := lemL1 D T hT ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ Λ (O i).s0 (Formalism.EigenvalueLevelCeiling.plc lam) hp hU hTb hTl
  refine ⟨((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL), ?_, ?_⟩
  · intro hmem
    have hco : Nat.Coprime (m * Ideal.absNorm cc ^ K) (Formalism.EigenvalueLevelCeiling.plc lam) := Nat.Coprime.mul hm (Nat.Coprime.pow_left _ cl)
    have h1 : ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) ∈ lam.asIdeal := Formalism.EigenvalueLevelCeiling.plc_mem lam
    obtain ⟨u, w, huw⟩ : IsCoprime ((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL) ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) :=
      Nat.Coprime.cast hco
    exact lam.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (huw ▸ lam.asIdeal.add_mem (lam.asIdeal.mul_mem_left _ hmem) (lam.asIdeal.mul_mem_left _ h1)))
  · have hinj : Function.Injective D.what₂.embLL.toIntAlgHom := D.what₂.embLL.injective
    refine (isIntegral_algHom_iff _ hinj).1 ?_
    have e1 : D.what₂.embLL.toIntAlgHom (((((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL)) : D.what₂.LL) * a) =
        ((m : ℂ) * ((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹) *
        (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℂˣ) : ℂ)) *
        ((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℝ) : ℂ) := by
      rw [RingHom.toIntAlgHom_apply, map_mul, ha, ← cv]
      push_cast
      rw [map_mul, map_pow, map_natCast, map_natCast]
      ring
    rw [e1]
    refine (hm1.mul hK1).mul ?_
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), ← Nat.cast_pow, Complex.ofReal_natCast]
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ^ D.R.r : ℕ) : ℤ)))

end GlobalTheory.ClassScalarIntegral
