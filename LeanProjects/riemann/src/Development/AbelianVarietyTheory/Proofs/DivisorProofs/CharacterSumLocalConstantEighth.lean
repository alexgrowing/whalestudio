import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSixth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLevelTypePrimeDatumLocallySmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecond
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa

noncomputable section

namespace GlobalTheory.ColNorms.LastDatum

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
open GlobalTheory.TopStep

section

variable {X : Fields}

theorem norm_psi {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {cst : LocCst X SB} (hc : cst.Ok) (P : SB) {a : X.E}
    (ha : IntAt P.1 ((Formalism.L2.Col.qOf P.1 : X.E) * a)) (σ : X.K →+* ℂ) : ‖σ (cst.psi P a)‖ = 1 := by
  have hD : ∀ k : ℕ, IntAt P.1 ((Formalism.L2.Col.qOf P.1 : X.E) ^ cst.D P * ((k : X.E) * a)) := fun k => by
    obtain ⟨D, hD⟩ : ∃ D, cst.D P = D + 1 := ⟨cst.D P - 1, by have := hc.D_pos P; omega⟩
    have := ((intAt_pow (intAt_nat (P := P.1) (Formalism.L2.Col.qOf P.1)) D).mul (intAt_nat k)).mul ha
    convert this using 1
    rw [hD]
    ring
  have hk : ∀ k : ℕ, cst.psi P ((k : X.E) * a) = cst.psi P a ^ k := fun k => by
    induction k with
    | zero => simpa using hc.psi_int P 0 (by simpa using intAt_nat (P := P.1) 0)
    | succ k ih =>
      have h1 := hc.psi_add P _ _ (hD k) (hD 1)
      rw [Nat.cast_one, one_mul] at h1
      rw [Nat.cast_succ, add_mul, one_mul, h1, ih, pow_succ]
  have h1 := hk (Formalism.L2.Col.qOf P.1)
  rw [hc.psi_int P _ ha] at h1
  have hq : Formalism.L2.Col.qOf P.1 ≠ 0 := fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have h2 : ‖σ (cst.psi P a)‖ ^ Formalism.L2.Col.qOf P.1 = 1 := by rw [← norm_pow, ← map_pow, ← h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hq).1 h2

variable {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

theorem locSmall_locTop (hm : R.m = m2 + 2) (hc : cst.Ok) (hs : cst.sharp = true) {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs)
    {y' : Sp X.E (R.N (m2 + 1))} (hy' : ∀ i, IntAt P.1 ((Formalism.L2.Col.qOf P.1 : X.E) * y' i)) :
    LocSmall (Formalism.L2.Col.qOf P.1) (stdAt X.E (R.N (m2 + 1)) P.1) (stdAt X.E (R.N R.m) P.1)
      (fun y => locTop Ch sel mu cst m2 P y y') 1 := by
  have hq := qOf_ne_zero (P := P.1)
  have hsingle : ∀ s : Fin (R.N (m2 + 1)), (Pi.single s 1 : Sp X.E (R.N (m2 + 1))) ∈ stdAt X.E (R.N (m2 + 1)) P.1 := fun s =>
    mem_stdAt.2 fun i => by
      rw [Pi.single_apply]
      split_ifs
      · simpa using intAt_nat (P := P.1) 1
      · simpa using intAt_nat (P := P.1) 0
  refine ⟨fun x hx y hy => mem_stdAt.2 fun l => ?_, fun x z hz => ?_, fun σ x => ?_⟩
  · rw [apply_eq_sum]
    exact intAt_sum _ fun j _ => (mem_stdAt.1 hy j).mul (mem_stdAt.1 (locTop_supp hm hP hx j) l)
  · have hz' : ∀ s l, IntAt P.1 (z (Pi.single s 1) l) := fun s l => mem_stdAt.1 (hz _ (hsingle s)) l
    have e : ∀ s l, (x + (Formalism.L2.Col.qOf P.1 : X.E) • z) (Pi.single s 1) l =
        x (Pi.single s 1) l + (Formalism.L2.Col.qOf P.1 : X.E) * z (Pi.single s 1) l := fun s l => rfl
    have hi : ∀ s l, IntAt P.1 ((x + (Formalism.L2.Col.qOf P.1 : X.E) • z) (Pi.single s 1) l) ↔ IntAt P.1 (x (Pi.single s 1) l) :=
      fun s l => by rw [e, GlobalTheory.SymLevelDatum.intAt_add_iff P.1 ((intAt_nat _).mul (hz' s l))]
    by_cases hx : ∀ s l, IntAt P.1 (x (Pi.single s 1) l)
    · refine locTop_congr hm hc hP hy' fun s l => ⟨(hi s l).2 (hx s l), hx s l, ?_⟩
      rw [e, add_sub_cancel_left, mul_div_cancel_left₀ _ hq]
      exact hz' s l
    · have h1 : locTop Ch sel mu cst m2 P x y' = 0 := by
        by_contra h
        exact hx fun s l => mem_stdAt.1 (locTop_supp hm hP h s) l
      have h2 : locTop Ch sel mu cst m2 P (x + (Formalism.L2.Col.qOf P.1 : X.E) • z) y' = 0 := by
        by_contra h
        exact hx fun s l => (hi s l).1 (mem_stdAt.1 (locTop_supp hm hP h s) l)
      exact h2.trans h1.symm
  · show ‖σ (locTop Ch sel mu cst m2 P x y')‖ ≤ 1
    unfold locTop
    rw [map_mul, norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · unfold PhiTop
      rw [if_pos hP, hs, if_pos rfl]
      have hq0 : Formalism.L2.Col.qOf P.1 ≠ 0 := fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
      have hN : ∀ j, R.N j = R.k + j * R.t + j := fun j => by unfold Ranks.N; ring
      have h0 : Formalism.L2.Col.cOf R (m2 + 1) = 0 := by unfold Formalism.L2.Col.cOf; omega
      refine (GlobalTheory.SymLevelDatum.locSmall_phiGS X.E X.K P.1 _ _ _ _ _ _ _ R.m _ _ 0 _ hq0 (Ideal.absNorm_mem _)
        ?_ ?_ ?_ ?_ ?_).2.2 σ _
      · rw [h0, rank_add_mul_eq_penultimate_rank hm, add_zero]
      · rw [h0, hN, hN, hm, show m2 + 2 = m2 + 1 + 1 from rfl, add_mul (m2 + 1) 1]; omega
      · rw [hN]; omega
      · rw [hN]; omega
      · unfold Ranks.r; omega
    · unfold ftY
      rw [if_pos hP]
      split_ifs with h
      · refine (norm_psi hc P ?_ σ).le
        have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
        have h' : ∀ j, IntAt P.1 (x (Pi.single j 1) (Br.iL (N_m_succ R))) := fun j => by
          have := h j
          rwa [LinearMap.comp_apply, atNL_last] at this
        have := he.mul (intAt_sum Finset.univ fun j _ => (hy' j).mul (h' j))
        convert this using 1
        rw [LinearMap.comp_apply, atNL_last, apply_eq_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      · simp

end

theorem smallDatum_xiCpl2 : ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), Hyp N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (d : RowPt Pr N.R sel mu), ∀ Y ∈ ybSet sel mu cst p.deco.1.N, SmallDatum (Sall sel mu u) p.deco.1.N (tilQ sel mu u d).1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl2 Ch sel mu cst (N.R.m - 2) p Y d) 1 := by
  intro D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H p d Y hY
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.ColNorms.BadPrimes.bad_primes D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hPr : Pr.Ok := H.1.2.2.2.2.2.2.2.2.2.1
  have hI := H.2.2.2.2.2.2.1
  have hT : TilOk Pr sel mu u := by
    refine tilOk_of hPr u fun P hP => ?_
    have hmu : mu = mu0 X.F X.E X.K Sg := H.2.2.2.2.1
    rw [hmu, twistPrimes_trivialTuple_empty sel Sg] at hP
    simp at hP
  have key := EntryDatum.smallDatum_prod (K := X.K) (S := Sall sel mu u) p.deco.1 (tilQ sel mu u d).1 (tilQ sel mu u d).2
    (frsF sel mu p) (tilFr hT d) (frsF_mem p) (fun P => (tilFr_isLiftFr hT d P).1)
    (fun P => by classical exact Finset.mem_union) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P hP => by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (h3 P hP)) (fun P => Formalism.L2.Col.qOf P.1)
    (fun P => by
      obtain ⟨j, -, hj, -⟩ := h2 P.1 (h1 P.1 P.2)
      rw [hj]
      refine Dvd.dvd.mul_left ?_ _
      fin_cases j
      · exact Dvd.intro _ rfl
      · exact Dvd.intro_left _ rfl)
    (fun P y => locTop Ch sel mu cst (N.R.m - 2) P y ((frsF sel mu p P).symm (repY Y))) (fun _ => 1)
    (fun P => locSmall_locTop hI.hm hI.cst_ok H.2.2.2.2.2.1 (h1 P.1 P.2) (repY_int p hY (h1 P.1 P.2)))
  rw [Finset.prod_const_one] at key
  convert key using 1
  funext x
  unfold XiCpl2
  simp only [locTop_tilFr]

end GlobalTheory.ColNorms.LastDatum
