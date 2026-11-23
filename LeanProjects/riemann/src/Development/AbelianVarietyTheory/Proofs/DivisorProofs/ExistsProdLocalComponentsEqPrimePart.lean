import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartRationalTensorZeroAtPrimeIffPlaceIdem

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrimePart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.BotClassDict GlobalTheory.NormSum.VacInt

variable {D : D7}

theorem idem_orth {v w : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F}
    (h : IsPlaceIdem D v ε) (h' : IsPlaceIdem D w ε') (hv : v ≠ w) : ε * ε' = 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  obtain ⟨α', rfl, k1, k0⟩ := h'
  refine Prod.ext (mul_zero _) (FiniteAdeleRing.ext _ fun u => ?_)
  change α u * α' u = 0
  by_cases hu : u = v
  · subst hu
    exact (congrArg (α u * ·) (k0 u hv)).trans (mul_zero _)
  · exact (congrArg (· * α' u) (h0 u hu)).trans (zero_mul _)

theorem cut_mul_cut {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] {e f : R} (h : e * f = 0) (A : Matrix n n R) :
    (e • A + (1 - e • (1 : Matrix n n R))) * (f • A + (1 - f • (1 : Matrix n n R))) =
      (e + f) • A + (1 - (e + f) • (1 : Matrix n n R)) := by
  have h' : f * e = 0 := by rw [mul_comm, h]
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, smul_sub, smul_add,
    h, h', zero_smul, add_smul]
  abel

theorem mt_mul (V : HSp D) (x y : GA D V) :
    Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_prod (V : HSp D) (g : GA D V) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F)
    (hε : ∀ v, IsPlaceIdem D v (ε v)) (L : List (HeightOneSpectrum (𝓞 D.host.F))) (hL : L.Nodup) :
    Formalism.L2.Theta.mt V (L.map fun v => GlobalTheory.VacStab.locPart V v g).prod =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (L.map ε).sum • Formalism.L2.Theta.mt V g +
        (1 - algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (L.map ε).sum • 1) := by
  induction L with
  | nil =>
    rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil, RingHom.map_zero, zero_smul, zero_smul, zero_add, sub_zero]
    rfl
  | cons v L ih =>
    rw [List.nodup_cons] at hL
    have h0 : ε v * (L.map ε).sum = 0 := by
      rw [← List.sum_map_mul_left]
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact idem_orth (hε v) (hε w) fun e => hL.1 (e ▸ hw)
    rw [List.map_cons, List.prod_cons, mt_mul, GlobalTheory.VacStab.mt_locPart V (hε v), ih hL.2, List.map_cons, List.sum_cons,
      RingHom.map_add]
    exact cut_mul_cut (by rw [← RingHom.map_mul, h0, RingHom.map_zero]) _

theorem natCast_mem_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (q : ℕ)
    (Q : HeightOneSpectrum (𝓞 E)) : (q : 𝓞 F) ∈ (Q.under (𝓞 F)).asIdeal ↔ (q : 𝓞 E) ∈ Q.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 E) _ ∈ Q.asIdeal ↔ _
  rw [map_natCast]

theorem finQ_sum_idem {q : ℕ} (hq : q.Prime) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hS : ∀ v, v ∈ S ↔ (q : 𝓞 D.host.F) ∈ v.asIdeal) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F)
    (hε : ∀ v, IsPlaceIdem D v (ε v)) :
    finQ D (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (∑ v ∈ S, ε v)) = eps D.host.E fun p => p = q := by
  apply (GlobalTheory.BotFormula.toFinE D).injective
  refine FiniteAdeleRing.ext _ fun Q => ?_
  have hev : ∀ w : HeightOneSpectrum (𝓞 D.host.F), (∑ v ∈ S, ε v).2 w = if w ∈ S then 1 else 0 := by
    intro w
    have e1 : (∑ v ∈ S, ε v).2 w = ∑ v ∈ S, evalV D.host.F w (sndA D.host.F (ε v)) := by
      rw [← map_sum, ← map_sum]
      rfl
    have e2 : ∀ v, evalV D.host.F w (sndA D.host.F (ε v)) = if w = v then 1 else 0 := by
      intro v
      obtain ⟨α, h, h1, h0⟩ := hε v
      rw [h]
      change evalV D.host.F w α = _
      split_ifs with hw
      · subst hw; exact h1
      · exact h0 w hw
    rw [e1, Finset.sum_congr rfl fun v _ => e2 v, Finset.sum_ite_eq]
  have hr : GlobalTheory.BotFormula.toFinE D (eps D.host.E fun p => p = q) Q =
      GlobalTheory.AdeleBaseChange.locMap ℚ Q (if pr (Q.under (𝓞 ℚ)) = q then 1 else 0) := by
    have := toFinE_tmul (D := D) 1 (idem fun p => p = q)
    rw [map_one, one_mul] at this
    refine (congrArg (fun x : FiniteAdeleRing (𝓞 D.host.E) D.host.E => x Q) this).trans ?_
    refine (GlobalTheory.AdeleBaseChange.adMap_apply _ Q).trans (congrArg _ ?_)
    rw [idem, mkInt_apply]
    congr
  have hiff : Q.under (𝓞 D.host.F) ∈ S ↔ pr (Q.under (𝓞 ℚ)) = q := by
    rw [hS, natCast_mem_under, ← Nat.prime_dvd_prime_iff_eq (pr_prime _) hq, pr_dvd_iff, natCast_mem_under]
  rw [GlobalTheory.ZeroAtPlaces.comp_base, hev, hr]
  by_cases h : Q.under (𝓞 D.host.F) ∈ S
  · rw [if_pos h, if_pos (hiff.1 h), map_one, map_one]
  · rw [if_neg h, if_neg (fun e => h (hiff.2 e)), map_zero, map_zero]

theorem exists_prod_eq_part : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (q : ℕ), q.Prime → ∀ g : Formalism.L2.Theta.GA D V, ∃ l : List (Formalism.L2.Theta.GA D V), (∀ h ∈ l, ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), Formalism.L2.Theta.IsPlaceIdem D v ε ∧ (q : 𝓞 D.host.F) ∈ v.asIdeal ∧ GlobalTheory.WeilParts.SuppPl ε V h) ∧ GlobalTheory.BotClassDict.finStd V hG l.prod = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) (GlobalTheory.BotClassDict.finStd V hG g) := by
  intro D V hG q hq g
  have hI : Ideal.span {(q : 𝓞 D.host.F)} ≠ ⊥ := by simpa using hq.ne_zero
  let S : Finset (HeightOneSpectrum (𝓞 D.host.F)) := (Ideal.finite_factors hI).toFinset
  have hS : ∀ v, v ∈ S ↔ (q : 𝓞 D.host.F) ∈ v.asIdeal := fun v => by
    simp [S, Ideal.dvd_span_singleton]
  choose ε hε using fun v : HeightOneSpectrum (𝓞 D.host.F) => GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
  refine ⟨S.toList.map fun v => GlobalTheory.VacStab.locPart V v g, ?_, ?_⟩
  · intro h hh
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hh
    exact ⟨v, ε v, hε v, (hS v).1 (Finset.mem_toList.1 hv), GlobalTheory.VacStab.suppPl_locPart V (hε v) g⟩
  · have hm := mt_prod V g ε hε S.toList (Finset.nodup_toList S)
    rw [Finset.sum_map_toList] at hm
    have he := finQ_sum_idem hq S hS ε hε
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    have h1 : finQ D ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) i j) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · exact RingHom.map_one _
      · exact RingHom.map_zero _
    change finQ D (Formalism.L2.Theta.mt V _ i j) = eps D.host.E (fun p => p = q) * finQ D (Formalism.L2.Theta.mt V g i j) +
      (1 - eps D.host.E fun p => p = q) * (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j
    rw [hm, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, he, h1, sub_mul, one_mul]

end GlobalTheory.PrimePart

end
