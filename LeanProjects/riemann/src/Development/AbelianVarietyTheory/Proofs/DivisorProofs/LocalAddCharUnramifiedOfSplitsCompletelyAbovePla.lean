import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SplitFullyUnr

open IsDedekindDomain NumberField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ramificationIdx_eq_one_of_splitsFully (v : HeightOneSpectrum (𝓞 F))
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v) (q : Ideal (𝓞 E)) (hq : q ∈ (v.asIdeal.under ℤ).primesOver (𝓞 E)) :
    q.ramificationIdx ℤ = 1 := by
  classical
  set P : Ideal ℤ := v.asIdeal.under ℤ with hP
  have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfin : (P.primesOver (𝓞 E)).Finite := Set.finite_of_ncard_pos (by rw [h]; exact hn)
  letI : Fintype (P.primesOver (𝓞 E)) := hfin.fintype
  have hcard : Fintype.card (P.primesOver (𝓞 E)) = Module.finrank ℚ E := by
    rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]; exact h
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
  rw [RingOfIntegers.rank] at hsum
  have hpos : ∀ r ∈ (Finset.univ : Finset (P.primesOver (𝓞 E))),
      (fun _ => 1) r ≤ r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ := fun r _ =>
    Nat.mul_pos (Ideal.ramificationIdx_pos r.1 ℤ) (Ideal.inertiaDeg_pos r.1 ℤ)
  have hall := (Finset.sum_eq_sum_iff_of_le hpos).1 (by rw [← Fintype.card_eq_sum_ones, hcard, hsum])
  have hm := (hall ⟨q, hq⟩ (Finset.mem_univ _)).symm
  exact Nat.eq_one_of_mul_eq_one_right hm

theorem under_eq_span_of_mem (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime)
    (hw : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
  have : NeZero w.asIdeal := ⟨w.ne_bot⟩
  have hq := Nat.absNorm_under_prime w.asIdeal
  have hd : (Ideal.absNorm (w.asIdeal.under ℤ) : ℤ) ∣ (p : ℤ) := by
    rw [← Int.cast_mem_ideal_iff]; simpa using hw
  have he : Ideal.absNorm (w.asIdeal.under ℤ) = p :=
    (Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 hd)
  rw [← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ), he]

theorem not_mem_sq_of_ramificationIdx {p : ℕ} (hl : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hv : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) (he : w.asIdeal.ramificationIdx ℤ = 1) :
    ((p : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {((p : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ w.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have := w.isPrime
  have : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) w.asIdeal hb] at he
  intro hsq
  have hne : Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) w.asIdeal ≠ 1 := by
    rw [Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le]; simpa using hsq
  exact hne he

theorem not_le_differentIdeal (v : HeightOneSpectrum (𝓞 F)) (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v) :
    ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := by
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  set p := Ideal.absNorm (v.asIdeal.under ℤ) with hpdef
  have hp : p.Prime := Nat.absNorm_under_prime v.asIdeal
  have hpv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := Int.absNorm_under_mem v.asIdeal
  have hP : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := (Int.ideal_span_absNorm_eq_self _).symm
  have hE : ∀ w : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ w.asIdeal → ((p : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
    intro w hw
    have hmem : w.asIdeal ∈ (v.asIdeal.under ℤ).primesOver (𝓞 E) :=
      ⟨w.isPrime, ⟨by rw [hP, under_eq_span_of_mem w hp hw]⟩⟩
    exact not_mem_sq_of_ramificationIdx hp w hw (ramificationIdx_eq_one_of_splitsFully v h _ hmem)
  have hnd := GlobalTheory.SplitUnram.not_dvd_different hp v hpv (GlobalTheory.SplitUnram.not_mem_sq_of_ext hE v)
  exact fun hle => hnd (Ideal.dvd_iff_le.2 hle)

end GlobalTheory.SplitFullyUnr

theorem GlobalTheory.SplitFullyUnr.psiUnr_of_splitsFully : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully D.host.E v → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr W.ψ v := by
  intro D T L sc G W v hv
  exact GlobalTheory.BaseGoodPlace.psiUnr_of_not_le W.ψ_std v (GlobalTheory.SplitFullyUnr.not_le_differentIdeal v hv)
