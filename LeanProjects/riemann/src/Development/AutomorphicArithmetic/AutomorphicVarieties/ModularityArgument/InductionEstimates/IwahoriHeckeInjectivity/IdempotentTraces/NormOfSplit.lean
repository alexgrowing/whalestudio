import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.SignMs
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem norm_of_split {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (w : HeightOneSpectrum (𝓞 M)) (h : GM.Split M (w.under (𝓞 K))) :
    Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := by
  haveI hl : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hs : Function.Surjective (completionMap (w.under (𝓞 K)) w) := h ⟨w, hl⟩
  have h1 : w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    rw [← finrank_eq_ramificationIdx_mul_inertiaDeg M (w.under (𝓞 K)) w]
    have hb : Function.Bijective (Algebra.linearMap ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion M)) :=
      ⟨(completionMap (w.under (𝓞 K)) w).injective, hs⟩
    rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, Nat.eq_one_of_mul_eq_one_left h1, pow_one]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.sysOf :
    SysOf := by
  intro K M _ _ _ _ _ _ _ _ h2 π π' P hsw hW
  have hp : (Module.finrank K M).Prime := h2 ▸ Nat.prime_two
  obtain ⟨χ, hχ, hP⟩ := R.twoParts_holds K M hp (2 * 2) P (Fin 2) (fun _ => 2) ![π, π'] (by norm_num)
    (fun _ => by norm_num) (by simp) hW
  obtain ⟨η, hη⟩ := R.classChar2 K M hp
  obtain ⟨j, hj0, hj, rfl⟩ := (R.normCharPow_holds K M hp η hη).1 χ hχ
  obtain rfl : j = 1 := by omega
  rw [pow_one] at hP
  filter_upwards [hW, hη.2, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually (R.decomp K M hp)] with w hw hg hd
  have hq : 1 < Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := NumberField.HeightOneSpectrum.one_lt_absNorm _
  refine ⟨fun w' hne hu => ?_, fun hn => ?_⟩
  · have hn : Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := by
      rcases hd with hd | hd
      · exact hd.2 w rfl
      · exact absurd (congrArg Subtype.val ((Nat.card_eq_one_iff_unique.1 hd.1).1.elim ⟨w', hu⟩ ⟨w, rfl⟩)) hne
    obtain ⟨A, hA, B, hB, e⟩ := hw 1 (by rw [pow_one]; exact hn)
    have e' : A = B 0 + B 1 := by simpa [Fin.sum_univ_two] using e
    exact ⟨B 0, B 1, hB 0, (hsw w w' hu.symm (Or.inl hne.symm) _).1 (hB 1), e' ▸ hA⟩
  · have hne : Formalism.ConjugateSelfDual.normV w ≠ Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := fun e => by
      have : (2 : ℕ) = 1 := Nat.pow_right_injective hq ((hn.symm.trans e).trans (pow_one _).symm)
      omega
    have hv : η.val (w.under (𝓞 K)) = -1 := by
      have h := hg.2.resolve_left hne
      rw [h2] at h
      exact Units.ext (IsPrimitiveRoot.coe_units_iff.2 h).eq_neg_one_of_two_right
    obtain ⟨A, hA, B, hB, e⟩ := hw 2 hn
    have hB0 : π.HasSat w (B 0) := hB 0
    have hB1 : π.HasSat w (B 1) := (hsw w w rfl (Or.inr fun h => hne (norm_of_split w h)) _).1 (hB 1)
    have e1 : B 1 = B 0 := hB1.unique hB0
    have hT := hA.twist hg.1
    rw [hP, hv] at hT
    have hs : A.map (fun x => -x) = A := by simpa using hT.unique hA
    obtain ⟨B', h3, h4⟩ := signMs A (B 0) hA.card hB0.card hs (by rw [e, Fin.sum_univ_two, e1])
    exact ⟨A, B', h3 ▸ hB0, h4, hA⟩
