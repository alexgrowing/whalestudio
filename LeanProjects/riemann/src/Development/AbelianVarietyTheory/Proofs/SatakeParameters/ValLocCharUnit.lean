import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred

noncomputable section

namespace GlobalTheory.ColPeriod.Scal

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)

variable {X : Fields} {Pr : Primes X}

theorem g_mem_of_vG (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [← hPr.piG_norm i]
  exact P.asIdeal.mul_mem_left _ (GlobalTheory.ColPeriod.mem_divs h)

theorem g_notMem_of_vGs (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vGs) (h' : P ∉ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  have h2 : ∃ k, P ∈ Pr.vG k := by
    rcases Finset.mem_union.1 h with h2 | h2
    exacts [⟨0, h2⟩, ⟨1, h2⟩]
  obtain ⟨k, hk⟩ := h2
  have hne : Pr.g i ≠ Pr.g k := by
    have h0 := hPr.g_ne
    fin_cases i <;> fin_cases k
    · exact absurd hk h'
    · exact h0
    · exact h0.symm
    · exact absurd hk h'
  exact natCast_notMem_of_ne (hPr.g_prime i) (hPr.g_prime k) hne P (g_mem_of_vG hPr hk)

theorem under_conjP (hX : X.Ok) (Q : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime₂ Q).asIdeal.under (𝓞 X.F) = Q.asIdeal.under (𝓞 X.F) := by
  ext r
  have e : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) r) = algebraMap (𝓞 X.F) (𝓞 X.E) r :=
    RingOfIntegers.ext (hX.star_F (r : X.F))
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, e]

variable {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem g_notMem_sel (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) {v : HeightOneSpectrum (𝓞 X.F)}
    (hv : ¬ ∃ P ∈ rowSG Pr sel mu, P.asIdeal.under (𝓞 X.F) = v.asIdeal) (k : Fin 2) :
    ((Pr.g k : ℕ) : 𝓞 X.E) ∉ (sel v).asIdeal := by
  classical
  intro h
  have hsub : ∀ Q, Q ∈ Pr.vG k → Q ∈ rowSG Pr sel mu := fun Q hQ => Finset.mem_union_left _ (by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hQ, Or.inr hQ])
  have h0 : X.conjO (Pr.piG k) ≠ 0 := by
    refine right_ne_zero_of_mul (a := Pr.piG k) ?_
    rw [hPr.piG_norm k]
    exact_mod_cast (hPr.g_prime k).ne_zero
  rw [← hPr.piG_norm k] at h
  rcases (sel v).isPrime.mem_or_mem h with h | h
  · refine hv ⟨conjPrime₂ (sel v), hsub _ ((Formalism.L2.Col.mem_divs h0 _).2 ?_), by rw [under_conjP hX, hsel v]⟩
    rw [mem_conjP]
    exact (cO_cO (Pr.piG k)).symm ▸ h
  · exact hv ⟨sel v, hsub _ ((Formalism.L2.Col.mem_divs h0 _).2 h), hsel v⟩

theorem val_locChar_unit {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 E)) (cq : K) (ψ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (ha : P.valuation E a = 1) :
    w.valuation K (LocE.locChar (qOf P) cq ψ a) = 1 := by
  have hu := GlobalTheory.LocCharVal.isUnit_redP P _ ha
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  rw [GlobalTheory.LastSteps.locChar_unit _ _ hu, LocE.unitV, dif_pos hu]
  exact GlobalTheory.CharVal.unit_of_finOrder (MonoidHom.isOfFinOrder ψ (isOfFinOrder_of_finite _))

theorem val_locChar {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 E)) {cq : K} (ψ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (hc : w.valuation K cq = 1) {a : E} (ha : a ≠ 0) : w.valuation K (LocE.locChar (qOf P) cq ψ a) = 1 := by
  obtain ⟨z, ζ, hζ, e⟩ := GlobalTheory.LocCharVal.locChar_eq_zpow_mul E K P (qOf P) cq ψ a
    (GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _) hq) ha
  rw [e, map_mul, map_zpow₀, hc, GlobalTheory.CharVal.unit_of_finOrder hζ, one_zpow, one_mul]

end GlobalTheory.ColPeriod.Scal

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker Scal

theorem scalarUnit_of (hL : LevelPrimes) (hH : HeckeUnit) (hT : TwistUnit) : ScalarUnit := by
  intro X Pr R Ch sel S mu cst L G m2 e eta hX hPr hsel hS ht hOk i w hw j hj
  have hH' := hH X Pr R.m Ch G.σ₀ (e ⟨j, hj⟩) ⟨j, hj⟩ (G.mu0 ⟨j, hj⟩) hX hPr (ht.mu0 _) (Pr.g i) w
  have hval : ∀ P : HeightOneSpectrum (𝓞 X.E), (∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.asIdeal) →
      w.valuation X.K (Ch.muVal ⟨j, hj⟩ P : X.K) = 1 := fun P hP =>
    hH' P (hPr.g_prime i) hw (hP i) (Formalism.L2.Host.unif P) _ (ht.muVal _ P hP)
  have h1 : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vG i → w.valuation X.K (cst.muq (j + 1) P) = 1 := by
    intro P hPi
    have hq := (hT X.F X.E X.K S mu P.1 w).2
    obtain ⟨hd, hn⟩ := hL X Pr sel S mu hX hPr hsel P
    by_cases hP : P.1 ∈ Pr.vGs
    · have h1 := hOk.muqG j hj P hP (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) rfl
      have h2 : G.σ₀ ((cst.muq (j + 1) P * ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K))⁻¹) =
          (((G.mu0 ⟨j, hj⟩).locK P.1 (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) : ℂˣ) : ℂ) := by
        rw [map_inv₀, map_mul, h1, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one, inv_inv]
      have h3 := hH' P.1 (hPr.g_prime i) hw (g_notMem_of_vGs hPr hP hPi) _ _ h2
      rwa [map_inv₀, map_mul, hq, mul_one, inv_eq_one] at h3
    · have hg : ∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := fun k =>
        natCast_notMem_of_ne (hPr.g_prime k) hd.1 (fun h => hn hP (h ▸ hS k)) P.1 (Ideal.absNorm_mem _)
      rw [hOk.muqQ j hj P hP, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀,
        hq, hval _ hg]
      simp
  refine ⟨h1, fun n N fr _ hN hfr => ?_⟩
  have h2 : w.valuation X.K (muOff sel (rowSG Pr sel mu) (mUof Ch mu j) N) = 1 := by
    unfold muOff
    refine finprod_induction (fun x => w.valuation X.K x = 1) (map_one _)
      (fun x y hx hy => by rw [map_mul, hx, hy, one_mul]) fun v => ?_
    split_ifs with hv
    · exact map_one _
    · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, mUof, dif_pos hj, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, hval _ (g_notMem_sel hX hPr hsel hv),
        (hT X.F X.E X.K S mu _ w).1]
      simp
  rw [muInvDet, map_mul, h2, one_mul, map_prod]
  refine Finset.prod_eq_one fun P _ => ?_
  unfold muAt
  by_cases hP : P.1 ∈ Pr.vG i
  · refine val_locChar_unit w P.1 _ _ ?_
    rw [LinearEquiv.coe_det]
    refine GlobalTheory.StdReps.val_det_eq fun x => ?_
    rw [← hfr P x, hN P.1 (g_mem_of_vG hPr hP)]
  · exact val_locChar w P.1 _ (hL X Pr sel S mu hX hPr hsel P).1.2 (h1 P hP) (Units.ne_zero _)

end GlobalTheory.ColPeriod
