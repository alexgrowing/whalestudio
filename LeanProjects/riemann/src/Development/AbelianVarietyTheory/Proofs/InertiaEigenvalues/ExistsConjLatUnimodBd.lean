import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ConjLatSplit

open GlobalTheory.UnRep GlobalTheory.UnRep.FullReps GlobalTheory.AdLat GlobalTheory.AdLat.Translate GlobalTheory.UnRep.SmallMat

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_conjLat_unimod_bd (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (bad : ℕ)
    (h : GL (Fin n) (RA (maximalRealSubfield E) E)) (hh : IsUnA (IsCMField.complexConj E) 1 h.1)
    (hs : SuppSplit (IsCMField.complexConj E) bad h.1) :
    ∃ (Λ : Submodule (𝓞 E) (Fin n → E)) (k : ℕ),
      (Λ : Set (Fin n → E)) = latOf (maximalRealSubfield E) h.1 (Formalism.L2.Pj.stdLat E n) ∧ (conjLat H Λ).Unimod ∧
      k.Coprime bad ∧ ∀ u : ℕ, Ideal.span {((u * k : ℕ) : 𝓞 E)} • (conjLat H Λ).La ≤ Formalism.L2.Pj.stdLat E n ∧
        Ideal.span {((u * k : ℕ) : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ (conjLat H Λ).La := by
  obtain ⟨-, -, hfg, hsp, -⟩ := StdInhab.main E H n
  obtain ⟨Λ, hΛ, -⟩ := exists_lattice_latOf (maximalRealSubfield E) E n (Formalism.L2.Pj.stdLat E n) h hfg hsp
  obtain ⟨e, -, -, he, hcut⟩ := hs
  have hcut' := cut_inv h _ hcut
  have he' : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      ((bad : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal → e v = 0 := fun v hv => by
    by_contra h0
    exact (he v h0).2 hv
  obtain ⟨t, ht, hb⟩ := exists_nat_bd _ hfg hsp _ e he' _ hcut
  obtain ⟨t', ht', hb'⟩ := exists_nat_bd _ hfg hsp _ e he' _ hcut'
  refine ⟨Λ, t' * t, hΛ, conjLat_unimod H hh hΛ, Nat.Coprime.mul_left ht' ht, fun u => ?_⟩
  refine conjLat_le H (by rw [← H.bar_eq, map_natCast]) (smul_mem_of_bd hfg hsp hΛ ?_ ?_)
  · have := hb.mul ((u * t' : ℕ) : 𝓞 E)
    rwa [← Nat.cast_mul, mul_assoc] at this
  · have := hb'.mul ((u * t : ℕ) : 𝓞 E)
    rwa [← Nat.cast_mul, mul_assoc, mul_comm t] at this

end General

end GlobalTheory.ConjLatSplit

open GlobalTheory.ConjLatSplit in

theorem GlobalTheory.SingleDatum.exists_conjLat_levOK : ∀ (D : D7) (V : HSp D), V.gram = 1 → L0c D V = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) → ∀ (bad M p : ℕ), Odd M → 2 ∣ bad → M ∣ bad → p ∣ bad → ∀ h : GA D V, SplitOffBad V bad h → ∃ (Λ : GenLat D.host.E V.rank) (u : ℕ), (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (finPt V h)) ∧ Λ.Unimod ∧ Λ.TrivAt M ∧ Nat.Coprime u p ∧ Λ.LevOK (M * u) M := by
  intro D V hg hL0 bad M p hM h2 hMb hpb h hs
  have hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank :=
    SetLike.coe_injective ((GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice V).trans hL0)
  have hc : GlobalTheory.Member.cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
  have hu := GlobalTheory.UnRep.Space.isUnA_finHom V h
  rw [show (HSpace.gram V)ᵀ = 1 by rw [hg, Matrix.transpose_one], hc] at hu
  have hs' : GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) bad (finHom V h).1 :=
    (GlobalTheory.RepsCompare.suppSplitOff_iff _ _ _).1 (GlobalTheory.RepsCompare.suppSplitOff_of_splitOffBad _ _ _ hs)
  rw [hc] at hs'
  obtain ⟨Λ, k, h1, hU, hk, hnat⟩ := exists_conjLat_unimod_bd (Formalism.L2.Pj.hostOfRecord D) bad (finHom V h) hu hs'
  rw [GlobalTheory.SplitReps.hLat_one] at hL
  have e := GlobalTheory.SplitReps.hLat_eq V (FWT.fin V h) Λ (by rw [hL]; exact h1)
  have hk1 := hnat 1
  rw [one_mul] at hk1
  refine ⟨GlobalTheory.UnRep.FullReps.conjLat (Formalism.L2.Pj.hostOfRecord D) Λ, k, fun v => ?_, hU,
    ⟨k, hk.coprime_dvd_right hMb, hk1⟩, hk.coprime_dvd_right hpb,
    ⟨hM.mul (Nat.Coprime.odd_of_right (hk.coprime_dvd_right h2)), dvd_mul_right _ _,
      le_inf (hnat M).2 Submodule.smul_le_right⟩⟩
  change _ ↔ _ ∈ Bridge.hLat V (FWT.fin V h)
  rw [e]
  exact Iff.rfl
