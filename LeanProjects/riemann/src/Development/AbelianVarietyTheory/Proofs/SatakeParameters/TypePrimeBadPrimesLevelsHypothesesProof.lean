import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypotheses
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPAAAndPrimesNe

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.Proof.NarrowJetMoments

namespace GlobalTheory.DatumJets.HidaSetting

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S}

theorem conj_notMem (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hT : Pr.T u ∈ S) (hg : ∀ i, Pr.g i ∈ S) :
    ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  have hTn : ∀ P ∈ rowSG Pr sel mu, ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun P hP =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hP
  intro P hP hP'
  rcases (mem_Sall sel mu u P).1 hP with h | h <;> rcases (mem_Sall sel mu u _).1 hP' with h' | h'
  · refine conj_piT_notMem hPr u ⟨conjPrime₂ P, h'⟩ ?_
    change cO X.E (Pr.piT u) ∈ (conjPrime₂ P).asIdeal
    rw [mem_conjP, cO_cO]
    exact decoFin_mem_of_mem_divs h
  · exact hTn _ h' (natCast_mem_conjP.2 (T_mem hPr u ⟨P, h⟩))
  · exact hTn _ h (natCast_mem_conjP.1 (T_mem hPr u ⟨conjPrime₂ P, h'⟩))
  · exact conjP_notMem_rowSG hX hPr hsel hg h h'

theorem notMem_Sall (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) {l : ℕ} (hl : l.Prime) (hS : l ∈ S) (hd : l ∣ Pr.cond)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Sall sel mu u) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  rcases (mem_Sall sel mu u P).1 hP with h | h
  · intro hm
    have h0 : Pr.piT u ∈ P.asIdeal := decoFin_mem_of_mem_divs h
    have h1 : (l : 𝓞 X.E) ∣ Pr.piT u - 1 :=
      (Nat.cast_dvd_cast (hd.mul_right _)).trans (hPr.piT_cong u)
    have h2 : Pr.piT u - 1 ∈ P.asIdeal := Ideal.mem_of_dvd _ h1 hm
    have h3 := P.asIdeal.sub_mem h0 h2
    rw [sub_sub_cancel] at h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  · refine notMem_rowSG hPr hsel hl hS (fun i e => ?_) h
    subst e
    have h1 : Pr.g i ≡ 1 [MOD Pr.g i] := (hPr.g_cong i).of_dvd hd
    have h2 : Pr.g i ∣ 1 := (Nat.modEq_zero_iff_dvd).1 (h1.symm.trans ((Nat.modEq_zero_iff_dvd).2 dvd_rfl))
    exact (hPr.g_prime i).one_lt.ne' (Nat.dvd_one.1 h2)

theorem qOf_pos (P : HeightOneSpectrum (𝓞 X.E)) : 0 < Formalism.L2.Col.qOf P :=
  Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem vG_mem_rowSG {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) : P ∈ rowSG Pr sel mu := by
  classical
  exact Finset.mem_union.2 (Or.inl (mem_vGs_iff.2 ⟨i, h⟩))

theorem ne_bot_of_locP {E : Type} [Field E] [NumberField E] [StarRing E] {I : Submodule (𝓞 E) E} {P : HeightOneSpectrum (𝓞 E)}
    (h : localization₂ P.asIdeal I = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) : I ≠ ⊥ := by
  rintro rfl
  have h1 : (1 : E) ∈ localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) :=
    (mem_locP P _ _).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, Submodule.mem_one.2 ⟨1, by simp⟩⟩
  rw [← h] at h1
  obtain ⟨s, hs, hs'⟩ := (mem_locP P _ _).1 h1
  rw [Submodule.mem_bot, smul_eq_zero] at hs'
  rcases hs' with h | h
  · exact hs (h ▸ zero_mem _)
  · exact one_ne_zero h

theorem setting_of_unit (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (i : Fin 2) (u : Pr.Word) (hT : Pr.T u ∈ S)
    (hg : ∀ i, Pr.g i ∈ S) (cst : LocCst X (rowSG Pr sel mu)) (hcst : cst.Ok) (A : Amb X) (a b : ℕ) (hLa : A.LaHyp a b ∅)
    (hE : A.ESmooth a b) (hU : A.AAUnit (Sall sel mu u)) :
    SplitSet A a b (Sall sel mu u) (X.conjO (Pr.piG i)) (Pr.g i) ∧
      0 < cAof sel mu cst ∧ 0 < cBof sel mu cst u ∧ Pr.g i ∣ cBof sel mu cst u := by
  have hc2 : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P₀, hP₀⟩ : (Pr.vG i).Nonempty := Finset.card_pos.1 (hPr.vG_card i ▸ hX.f_pos)
  have hP₀r : P₀ ∈ rowSG Pr sel mu := vG_mem_rowSG hP₀
  have hne : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have := hPr.piG_norm i
    rw [h, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast this.symm)
  have hprod : 0 < ∏ P : rowSG Pr sel mu, Formalism.L2.Col.qOf P.1 := Finset.prod_pos fun P _ => qOf_pos P.1
  obtain ⟨h1, h2, -, -, h5, h6⟩ := hLa
  refine ⟨⟨hX, ⟨h1, h2, conj_notMem hX hPr hsel u hT hg, hU, h5, h6⟩,
    ne_bot_of_locP (hU P₀ ((mem_Sall sel mu u P₀).2 (Or.inr hP₀r))), hE, hPr.g_prime i, ?_, ?_, fun P hP => ?_⟩,
    pow_pos hprod _, Nat.mul_pos (hPr.T_prime u).pos (pow_pos hprod _), ?_⟩
  · rw [hc2, mul_comm]
    exact hPr.piG_norm i
  · rw [hc2]
    exact (hPr.piG_cop i).symm
  · exact (mem_Sall sel mu u P).2 (Or.inr (vG_mem_rowSG (i := i) ((mem_divs hne P).2 hP)))
  · refine Dvd.dvd.mul_left (dvd_pow ?_ (Nat.one_le_iff_ne_zero.1 hcst.B_pos)) _
    have e : Formalism.L2.Col.qOf P₀ = Pr.g i := hPr.vG_norm i P₀ hP₀
    have hd := Finset.dvd_prod_of_mem (fun P : rowSG Pr sel mu => Formalism.L2.Col.qOf P.1)
      (Finset.mem_univ (⟨P₀, hP₀r⟩ : rowSG Pr sel mu))
    beta_reduce at hd
    rw [e] at hd
    exact hd

theorem typePrimeBadPrimesLevelsHypotheses_proof : GlobalTheory.DatumJets.TypePrimeBadPrimesLevelsHypotheses := by
  intro D EX sel δ B χ cD hH hsel i u mu cst hcst a b hLa hE
  obtain ⟨hcc, -, -, hX1, hPr⟩ := hH
  have hT : (recPrimes EX).T u ∈ badS D := Or.inr (Or.inl ⟨u, rfl⟩)
  have hg : ∀ j, (recPrimes EX).g j ∈ badS D := fun j => Or.inl (by fin_cases j <;> simp)
  refine setting_of_unit hX1.ok hPr hsel i u hT hg cst hcst _ a b hLa hE fun P hP => ?_
  obtain ⟨l, n, -, hlP, hl, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow P.asIdeal
  refine GlobalTheory.AAUnitAway.locP_AA D _ (recSeam D) _ δ B χ cD P l hl ?_ ?_ hlP ?_
  · intro hs
    refine notMem_Sall hPr hsel u hl (GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.small_mem_badS D l hs) ?_ hP hlP
    exact ((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _
  · rintro rfl
    refine notMem_Sall hPr hsel u hl (Or.inl (by simp)) ?_ hP hlP
    exact (dvd_mul_left _ _).mul_right _
  · rw [hcc, Ideal.absNorm_top]
    exact Nat.coprime_one_left _

end GlobalTheory.DatumJets.HidaSetting
