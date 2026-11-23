import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalTraceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelesCmFieldEqZeroOfComponents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecompose
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.InertFormFix.mul_idem_of_trivOutside {E : Type} [Field E] [NumberField E] [IsCMField E] (F : Subfield E)
    (hF : F = maximalRealSubfield E) (P : HeightOneSpectrum (𝓞 E))
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : NG.OverPl P v) (x : AL E)
    (hx : ∀ w, w ≠ v → compAt E w x = 0) :
    ((GlobalTheory.AdelicU.singleFin (P.under (𝓞 F)) 1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (1 : E)) *
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x := by
  subst hF
  have hvv : P.under (𝓞 (maximalRealSubfield E)) = v := HeightOneSpectrum.ext hv
  subst hvv
  have hx' : x = GlobalTheory.CongSplit.idemAt E (P.under (𝓞 (maximalRealSubfield E))) * x := by
    have h0 := GlobalTheory.AL_eq_zero_of_compAt E (x - GlobalTheory.CongSplit.idemAt E (P.under (𝓞 (maximalRealSubfield E))) * x)
      (fun w => by
        rw [RingHom.map_sub, RingHom.map_mul]
        by_cases hw : w = P.under (𝓞 (maximalRealSubfield E))
        · rw [hw, GlobalTheory.CongSplit.compAt_idemAt_self, one_mul, sub_self]
        · rw [GlobalTheory.CongSplit.compAt_idemAt_ne E _ hw, hx w hw, zero_mul, sub_zero])
    exact (sub_eq_zero.1 h0)
  conv_rhs => rw [hx']
  rw [RingEquiv.map_mul]
  congr 1

theorem GlobalTheory.InertFormFix.finPart_mul_of_trivOutside : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D), Formalism.IndefR.Mult.IsPrimeIdem P e f → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl P v → ∀ x : AL D.host.E, (∀ w, w ≠ v → compAt D.host.E w x = 0) → Formalism.L2.Theta.finPart D f * (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x := by
  intro D hF P e f hP v hv x hx
  have hf := GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hP rfl
  subst hf
  exact GlobalTheory.InertFormFix.mul_idem_of_trivOutside D.host.F hF P v hv x hx

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.InertFormFix.suppF_of_trivOutside : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (Q : Formalism.IndefR.principalLevelFrame.RowPsi V n), Formalism.IndefR.principalLevelFrame.StdPsi hF Q → ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D), Formalism.IndefR.Mult.IsPrimeIdem P e f → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl P v → ∀ κ : GAf D.host.E n, TrivOutside {v} κ → Formalism.IndefR.Mult.SuppF V f (Q.ψ κ) := by
  intro D hF V n Q hQ P e f hP v hv κ hT
  obtain ⟨⟨β, β', hββ', hβ'β, hmat⟩, -⟩ := hQ
  rw [GlobalTheory.SphTrans.suppF_iff f (Q.into κ), hmat κ]
  have hT' : ∀ w, w ≠ v → (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (compAt D.host.E w) = 1 :=
    fun w hw => hT w (by simpa using hw)
  change Formalism.L2.Theta.finPart D f • (β * (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm * β' - 1) = β * (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm * β' - 1
  set M : Matrix (Fin n) (Fin n) (AL D.host.E) := κ.1.1 with hMdef
  set K := M.map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm with hKdef
  have hcore : ∀ a b, Formalism.L2.Theta.finPart D f * (K - 1) a b = (K - 1) a b := by
    intro a b
    have hx : ∀ w, w ≠ v → compAt D.host.E w (M a b - (1 : Matrix (Fin n) (Fin n) (AL D.host.E)) a b) = 0 := by
      intro w hw
      have h1 := congrFun (congrFun (hT' w hw) a) b
      rw [Matrix.map_apply] at h1
      rw [RingHom.map_sub, h1]
      by_cases hab : a = b
      · rw [hab, Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, sub_self]
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, RingHom.map_zero, sub_zero]
    have h2 := GlobalTheory.InertFormFix.finPart_mul_of_trivOutside D hF P e f hP v hv _ hx
    have e3 : (K - 1) a b = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm (M a b -
        (1 : Matrix (Fin n) (Fin n) (AL D.host.E)) a b) := by
      rw [Matrix.sub_apply, hKdef, Matrix.map_apply, RingEquiv.map_sub]
      by_cases hab : a = b
      · rw [hab, Matrix.one_apply_eq, Matrix.one_apply_eq, RingEquiv.map_one]
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, RingEquiv.map_zero]
    rw [e3, h2]
  have hK : Formalism.L2.Theta.finPart D f • (K - 1) = K - 1 := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul, hcore]
  have e1 : β * K * β' - 1 = β * (K - 1) * β' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hββ']
  rw [e1]
  conv_rhs => rw [← hK]
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem GlobalTheory.InertFormFix.real_rt_eq_of_good_inert : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl Pp v → ∀ g : D.what₂.Mt (D.nd.mu i) (D.nd.j i), ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {v} κ → NG.rt D.host.E D.R.nV κ ((P.M.loc i).real g) = (P.M.loc i).real g := by
  intro hA hL D P X hX h41 h7 htie i hμ j hj h hh Pp hG hI v hv g κ hκ hT
  have hstd := hX.stdV j
  have hprime := GlobalTheory.InertFrameLoc.isPrimeIdem_tensAt hI rfl
  have hsupp := GlobalTheory.InertFormFix.suppF_of_trivOutside D hX.hF (Formalism.IndefR.Links.Vc D j) D.R.nV (hX.PV j) hstd Pp _ _ hprime v hv κ hT
  obtain ⟨c, hc⟩ := X.given.core.lev.βV j
  rw [one_pow] at hc
  have ls := (GlobalTheory.LevSplit.lev_split (Formalism.IndefR.Links.Vc D j) (X.R.βV j) (X.R.ΛV j) 1
    (Formalism.IndefR.RecTie.datVP X.R j (X.tupT (D.nd.mu i)) (X.R.levR X.F false)) hc).2 Pp _ _ hprime
    (by
      intro h1
      have : ((1 : ℕ) : 𝓞 D.host.E) = 1 := Nat.cast_one
      rw [this] at h1
      exact Pp.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1))
    (fun PP hPP => hG PP hPP)
  have hK : (hX.PV j).ψ κ ∈ Formalism.L2.Theta.KsphC (Formalism.IndefR.Links.Vc D j) ∅ := (hstd.2 κ).1 hκ
  have hlev := (ls.1 _ hsupp).2 hK
  have hchi := ls.2.1 _ hlev hsupp

  have hfix : ∀ (x : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) y,
      X.fn hμ j x (y * (hX.PV j).ψ κ) = X.fn hμ j x y := by
    intro x y
    have hm := ((X.IL.jMt (D.nd.mu i) hμ j) x).2
    obtain ⟨-, hm2⟩ := hm
    have e1 := hm2 ((hX.PV j).ψ κ) hlev y
    unfold GlobalTheory.NJoin.RealAt.fn
    rw [e1]
    rw [hchi]
    exact one_smul ℂ _
  have key : ∀ (j' : ℕ) (e : j.1 + 1 = j') (h1 : 1 ≤ j') (h2 : j' ≤ D.R.m) (x : D.what₂.Mt (D.nd.mu i) j'),
      NG.rt D.host.E D.R.nV κ ((P.M (D.nd.mu i) j' h1 h2).real x) = (P.M (D.nd.mu i) j' h1 h2).real x := by
    intro j' e h1 h2 x
    subst e
    funext y
    show (P.M _ _ h1 h2).real x (y * κ) = _
    rw [hX.real (D.nd.mu i) hμ j x (y * κ), hX.real (D.nd.mu i) hμ j x y, ← mul_assoc, map_mul, hfix]
  exact key _ hj _ _ g

end
