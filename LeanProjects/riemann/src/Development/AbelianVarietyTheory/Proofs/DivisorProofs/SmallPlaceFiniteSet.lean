import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameAutCof

theorem sub_mem_of_prime_norm {K : Type} [Field K] [NumberField K] (σ : 𝓞 K →+* 𝓞 K) (I : Ideal (𝓞 K))
    (hp : (Ideal.absNorm I).Prime) (hI : I.map σ ≤ I) (x : 𝓞 K) : σ x - x ∈ I := by
  have hc : Nat.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Fact (Ideal.absNorm I).Prime := ⟨hp⟩
  have : Finite (𝓞 K ⧸ I) := Nat.finite_of_card_ne_zero (hc ▸ hp.ne_zero)
  have := Fintype.ofFinite (𝓞 K ⧸ I)
  let e := ZMod.ringEquivOfPrime (𝓞 K ⧸ I) hp (by rw [← Nat.card_eq_fintype_card, hc])
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (e.symm (Ideal.Quotient.mk I x))
  have h1 : x - (n : 𝓞 K) ∈ I := by
    rw [← Ideal.Quotient.eq, map_intCast]
    apply e.symm.injective
    rw [map_intCast, hn]
  have h2 : σ x - (n : 𝓞 K) ∈ I := by
    have := hI (Ideal.mem_map_of_mem σ h1)
    rwa [map_sub, map_intCast] at this
  have := I.sub_mem h2 h1
  rwa [sub_sub_sub_cancel_right] at this

theorem finite_fixed {K : Type} [Field K] [NumberField K] [StarRing K] (h : ∃ x : K, star x ≠ x) :
    {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal).Prime ∧ Formalism.DivisionValues.conjPl v = v}.Finite := by
  have hx : ∃ x : 𝓞 K, Formalism.DivisionValues.cO K x - x ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨y, hy⟩ := h
    apply hy
    have h0 : ∀ a : 𝓞 K, star (a : K) = a := fun a => congrArg (fun z : 𝓞 K => (z : K)) (sub_eq_zero.1 (hn a))
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
    rw [star_div₀]
    exact congrArg₂ (· / ·) (h0 a) (h0 b)
  obtain ⟨x, hx⟩ := hx
  refine (Ideal.finite_factors (I := Ideal.span {Formalism.DivisionValues.cO K x - x}) (by simpa using hx)).subset ?_
  rintro v ⟨hp, hv⟩
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  exact sub_mem_of_prime_norm (Formalism.DivisionValues.cO K : 𝓞 K →+* 𝓞 K) v.asIdeal hp
    (le_of_eq (congrArg HeightOneSpectrum.asIdeal hv)) x

theorem exists_star_ne (D : D7) : ∃ x : D.host.E, star x ≠ x := by
  by_contra hn
  push Not at hn
  apply IsCMField.complexConj_ne_one D.host.E
  refine AlgEquiv.ext fun x => ?_
  exact hn x

theorem cofinite_labels {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
    (j : Fin D.R.m) (t : p.P.T) {l : ℕ} (hl : l ≠ 0) :
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (GlobalTheory.ExpTie.blk p j t).Pl, ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t Q).asIdeal ∧ labOf p j t Q = v}.Finite := by
  obtain ⟨gR, c0R, c0L, hTie⟩ := p.charW.base.fam.tie
  have honto := p.charW.base.fam.pl_onto
  have hcc : ∀ v : HeightOneSpectrum (𝓞 D.host.E), Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl v) = v := Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl
  have hinj : Function.Injective (Formalism.DivisionValues.conjPl (K := D.host.E)) := Function.Involutive.injective hcc
  set S : Set (HeightOneSpectrum (𝓞 D.host.E)) := (p.R.Sb : Set (Pl D.host.E)) ∪ (p.R.Q t : Set (Pl D.host.E)) with hS
  have hSf : S.Finite := hTie.S_fin.union (Finset.finite_toSet _)
  have hlf : {v : HeightOneSpectrum (𝓞 D.host.E) | v.asIdeal ∣ Ideal.span {((l : ℕ) : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa using hl)
  refine (((finite_fixed (exists_star_ne D)).union hSf).union ((hSf.union hlf).preimage hinj.injOn)).subset ?_
  rintro v ⟨hp, hv⟩
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_preimage, not_or, not_and, Ideal.dvd_span_singleton] at hn
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hn
  have hci : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (Formalism.DivisionValues.conjPl v).asIdeal = v.asIdeal := by
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hcc]
  have hoff : Bridge.SplitOff (D := D) (Formalism.DivisionValues.conjPl v) S := by
    refine ⟨?_, h3, fun Q hQ he => h2 ?_⟩
    · rw [hci]
      exact fun he => h1 hp (HeightOneSpectrum.ext he).symm
    · rw [hci] at he
      exact HeightOneSpectrum.ext he ▸ hQ
  obtain ⟨P, hP⟩ := honto (Formalism.DivisionValues.conjPl v) ⟨hoff.1, fun h => hoff.2.1 (Or.inl h), fun Q hQ => hoff.2.2 Q (Or.inl hQ)⟩
  have hok := (hTie.ok t P).2 (hP ▸ hoff)
  have e1 : plOf p j t ⟨P, hok⟩ = Formalism.DivisionValues.conjPl v := hP
  refine hv ⟨⟨P, hok⟩, ?_, ?_⟩
  · rw [e1]; exact h4
  · show Formalism.DivisionValues.conjPl (plOf p j t ⟨P, hok⟩) = v
    rw [e1, hcc]

theorem cofinite_labels_at : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), PtAt.Rows p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite :=
  fun p _ _ j _ _ _ _ w _ _ hs => cofinite_labels p j (p.R.mu w) hs.1.ne_zero

end GlobalTheory.FrameAutCof
