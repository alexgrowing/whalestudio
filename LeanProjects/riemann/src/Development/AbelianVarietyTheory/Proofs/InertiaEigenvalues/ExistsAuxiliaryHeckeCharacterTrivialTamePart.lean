import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryHyperbolicVectors
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotTeichTrivOfIsDelta
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightExceedsCenterBound

noncomputable section

namespace GlobalTheory.LamTie.TeichEx

section General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.GridChars GlobalTheory.CMVal
open GlobalTheory.LamTie.AuxiliaryPrimeFunction

variable {L : Type} [Field L] [NumberField L]

theorem coprime_absNorm_sub_one (v : HeightOneSpectrum (𝓞 L)) {p : ℕ} (hp : p.Prime) (hv : (p : 𝓞 L) ∈ v.asIdeal) :
    Nat.Coprime p (Ideal.absNorm v.asIdeal - 1) := by
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI := v.isPrime
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 L ⧸ v.asIdeal) = 0 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← nsmul_one, card_nsmul_eq_zero']
  have h1 := GlobalTheory.Mem.WildChar.one_lt_absNorm v
  have hp0 : ((p : ℕ) : 𝓞 L ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem.2 hv]
  refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun ⟨t, ht⟩ => one_ne_zero (α := 𝓞 L ⧸ v.asIdeal) ?_
  have e : Ideal.absNorm v.asIdeal = p * t + 1 := by omega
  rw [e] at hN
  simpa [hp0] using hN

theorem exists_char_teich {F : Type} [Field F] [NumberField F] [Algebra F L] {c : L ≃ₐ[F] L} {I : Type} [Fintype I]
    {φ : I → L →+* ℂ} (hcm : CMData F c φ) (e : I → ℤ) (O : HeightOneSpectrum (𝓞 L) → Prop) (hfin : {w | O w}.Finite)
    (hO : ∀ w w', w.under (𝓞 F) = w'.under (𝓞 F) → O w → O w') (w0 : HeightOneSpectrum (𝓞 L)) (h0 : ¬ O w0)
    (hpr : ∀ w, O w → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ w.asIdeal) {q : ℕ} (hq : q.Prime) (h5 : Units.torsionOrder L + 1 < q)
    (hq0 : (q : 𝓞 L) ∈ w0.asIdeal)
    (hsp : ∀ w, O w ∨ w.under (𝓞 F) = w0.under (𝓞 F) → ¬ ConjPl c.toRingEquiv w w) :
    ∃ χ : Formalism.L2.Host.HChar L, χ.IsUnitary ∧ χ.TrivOn F ∧ χ.HasInf φ (fun i => 2 * e i) ∧
      (∀ w, ¬ O w → w.under (𝓞 F) ≠ w0.under (𝓞 F) → χ.UnrAt w) ∧ (∀ w, O w → ExpAt χ w 2) ∧
      (∀ w, w.under (𝓞 F) = w0.under (𝓞 F) → ExpAt χ w 1) ∧
      ∀ w, O w → ∀ x : (w.adicCompletion L)ˣ, x ^ (Ideal.absNorm w.asIdeal - 1) = 1 → χ.loc w x = 1 := by
  classical
  haveI : Nonempty (HeightOneSpectrum (𝓞 L)) := ⟨w0⟩
  let u : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 F) := fun w => w.under (𝓞 F)
  let r : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 L) := fun w => Function.invFun u (u w)
  have hr : ∀ w, (r w).under (𝓞 F) = w.under (𝓞 F) := fun w => Function.invFun_eq (f := u) ⟨w, rfl⟩
  have hrr : ∀ w w', w.under (𝓞 F) = w'.under (𝓞 F) → r w = r w' := fun w w' h => congrArg (Function.invFun u) h
  set w1 := r w0 with hw1
  have hu1 : w1.under (𝓞 F) = w0.under (𝓞 F) := hr w0
  have h1 : ¬ O w1 := fun h => h0 (hO _ _ hu1 h)
  let S : Finset (HeightOneSpectrum (𝓞 L)) := insert w1 (hfin.toFinset.filter fun w => r w = w)
  have hS : ∀ w, w ∈ S ↔ w = w1 ∨ (O w ∧ r w = w) := fun w => by simp [S]
  have hfix : ∀ w ∈ S, r w = w := fun w hw => by
    rcases (hS w).1 hw with rfl | h
    exacts [hrr _ _ hu1, h.2]
  have hne : ∀ w, O w → w ≠ w1 := fun w hw h => h1 (h ▸ hw)
  have hwild : ∀ w : HeightOneSpectrum (𝓞 L), ∃ θ : (w.adicCompletion L)ˣ →* ℂˣ,
      O w → ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ w.asIdeal ∧ (∀ x, θ x ^ p = 1) ∧
        (∀ x, IsUnitAt w x → Valued.v ((x : w.adicCompletion L) - 1) ≤ WithZero.exp (-2 : ℤ) → θ x = 1) ∧
        ∃ k : Lˣ, IsUnitAt w (atFin w k) ∧
          Valued.v (((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1) ≤
            WithZero.exp (-1 : ℤ) ∧ θ (atFin w k) ≠ 1 := fun w => by
    by_cases hw : O w
    · obtain ⟨p, hp, hp'⟩ := hpr w hw
      obtain ⟨θ, hθ⟩ := exists_wild w hp hp'
      exact ⟨θ, fun _ => ⟨p, hp, hp', hθ⟩⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose θ1 hθ1 using hwild
  have hw0 : w1 ∈ S := (hS _).2 (Or.inl rfl)
  obtain ⟨θ0, ht0, hθ0, k0, hk0, hk0'⟩ := exists_tame_par w1 hq h5 (natCast_mem_of_under hu1.symm hq0) φ e (S.erase w1) θ1
  let θ : ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletion L)ˣ →* ℂˣ := Function.update θ1 w1 θ0
  have e0 : θ w1 = θ0 := Function.update_self _ _ _
  have e1 : ∀ w, w ≠ w1 → θ w = θ1 w := fun w hw => Function.update_of_ne hw _ _
  obtain ⟨χ, hu, ht, hi, hunr, hloc⟩ := exists_hecke_level hcm e S θ
    (fun w hw => by
      rcases (hS w).1 hw with rfl | ⟨h2, -⟩
      · rw [e0]; exact GlobalTheory.ModelChar.continuous_of_tameLoc ht0
      · obtain ⟨p, -, -, -, h, -⟩ := hθ1 w h2
        rw [e1 w (hne w h2)]; exact continuous_of_level h)
    (fun w hw x => by
      rcases (hS w).1 hw with rfl | ⟨h2, -⟩
      · rw [e0]; exact ht0.1 x
      · obtain ⟨p, hp, -, h, -⟩ := hθ1 w h2
        rw [e1 w (hne w h2)]
        exact Complex.norm_eq_one_of_pow_eq_one (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]) hp.ne_zero)
    (fun w hw w' hcj hw' => by
      have := (under_eq_iff_conjPl c hcm.rank hcm.ne _ _).2 (Or.inr hcj)
      obtain rfl : w' = w := by rw [← hfix w' hw', hrr _ _ this, hfix w hw]
      refine hsp w' ?_ hcj
      rcases (hS w').1 hw with rfl | h
      exacts [Or.inr hu1, Or.inl h.1])
    (fun k hk => by
      have ep : ∏ w ∈ S.erase w1, θ w (atFin w k) = ∏ w ∈ S.erase w1, θ1 w (atFin w k) :=
        Finset.prod_congr rfl fun w hw => by rw [e1 w (Finset.ne_of_mem_erase hw)]
      rw [← Finset.mul_prod_erase _ _ hw0, e0, ep]
      exact hθ0 k hk)
  refine ⟨χ, hu, ht, hi, fun Q hQ hQ' => hunr Q fun w hw h => ?_, fun Q hQ => ?_, fun Q hQ => ?_, fun Q hQ x hx => ?_⟩
  · rcases (hS w).1 hw with rfl | h2
    exacts [hQ' (h.trans hu1), hQ (hO _ _ h.symm h2.1)]
  · have hOr : O (r Q) := hO _ _ (hr Q).symm hQ
    obtain ⟨σ, s1, s2, s3, -, s5⟩ := hloc (r Q) ((hS _).2 (Or.inr ⟨hOr, hrr _ _ (hr Q)⟩)) Q (hr Q).symm
    obtain ⟨p, -, -, -, t2, k, t3, t4, t5⟩ := hθ1 _ hOr
    rw [e1 _ (hne _ hOr)] at s5
    refine expAt_succ (n := 1) (fun x hx hx' => (s5 x hx).2 (t2 _ ((s2 x).2 hx) (by rw [s3]; exact hx'))) fun H => t5 ?_
    obtain ⟨x, hx⟩ := s1 k
    rw [← hx] at t3 t4 ⊢
    rw [s3] at t4
    exact (s5 x ((s2 x).1 t3)).1 (H x ((s2 x).1 t3) t4)
  · obtain ⟨σ, s1, s2, s3, -, s5⟩ := hloc w1 hw0 Q (hQ.trans hu1.symm)
    rw [e0] at s5
    refine expAt_succ (n := 0) (fun x hx hx' => (s5 x hx).2 (ht0.2 _ ((s2 x).2 hx) (by rw [s3]; exact hx'))) fun H => hk0' ?_
    obtain ⟨x, hx⟩ := s1 k0
    rw [← hx] at hk0 ⊢
    exact (s5 x ((s2 x).1 hk0)).1 ((χ.unrAt_iff Q).2 H x ((s2 x).1 hk0))
  · have hOr : O (r Q) := hO _ _ (hr Q).symm hQ
    obtain ⟨σ, -, -, -, s4, s5⟩ := hloc (r Q) ((hS _).2 (Or.inr ⟨hOr, hrr _ _ (hr Q)⟩)) Q (hr Q).symm
    obtain ⟨p, hp, hpm, t1, -⟩ := hθ1 _ hOr
    rw [e1 _ (hne _ hOr)] at s5
    have hpQ : (p : 𝓞 L) ∈ Q.asIdeal := natCast_mem_of_under (hr Q) hpm
    refine (s5 x (GlobalTheory.LamTie.isUnitAt_of_pow_eq_one hx)).2 ?_
    have a2 : θ1 (r Q) (σ x) ^ (Ideal.absNorm Q.asIdeal - 1) = 1 := by rw [← map_pow, s4 x _ hx, map_one]
    have : θ1 (r Q) (σ x) ^ Nat.gcd p (Ideal.absNorm Q.asIdeal - 1) = 1 := by
      rw [pow_gcd_eq_one]; exact ⟨t1 _, a2⟩
    rwa [Nat.Coprime.gcd_eq_one (coprime_absNorm_sub_one Q hp hpQ), pow_one] at this

end General

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
open GlobalTheory.LamTie.AuxiliaryPrimeFunction

theorem exists_auxiliaryHeckeCharacter_trivial_tame_part : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)) (c : R.Psi → ℤ),
    PlacesOk H q0 w0 → Units.torsionOrder H.E + 1 < q0 → ∃ χ, IsAuxiliaryHeckeCharacter H w0 c χ ∧ TeichTriv H χ := by
  intro R H q0 w0 c hP h5
  obtain ⟨cc, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  haveI : IsCMField H.E := H.isCMField_hostE
  have hd := hP.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil] at hd
  have hq := hP.splits q0 (by simp)
  have hpr : ∀ w, Over4 H w → ∃ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p ≠ q0 ∧ (p : 𝓞 H.E) ∈ w.asIdeal := by
    rintro w (⟨k, h⟩ | h | h)
    · fin_cases k
      · exact ⟨H.g 0, by simp, by tauto, h⟩
      · exact ⟨H.g 1, by simp, by tauto, h⟩
    · exact ⟨H.pde, by simp, by tauto, h⟩
    · exact ⟨H.pde', by simp, by tauto, h⟩
  have hsp : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ w : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ w.asIdeal →
      ¬ GlobalTheory.Mem.Chr.ConjPl cc.toRingEquiv w w := fun p hp w hw hc => by
    obtain ⟨h1, -, h2, h3⟩ := hP.splits p hp
    obtain ⟨P, P', hne, hP1, hP2⟩ := GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm H.E p h1 h2 h3 w hw
    have key : ∀ Q, GlobalTheory.CMVal.Over Q (below w) → Q = w := fun Q hQ => by
      rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl cc hcm.rank hcm.ne w Q).1 (HeightOneSpectrum.ext hQ) with h | h
      · exact h
      · exact (GlobalTheory.Mem.Chr.existsUnique_conjPl cc.toRingEquiv w).unique h hc
    exact hne ((key P hP1).trans (key P' hP2).symm)
  obtain ⟨χ, h1, h2, h3, h4, h5, h6, h7⟩ := exists_char_teich hcm c (Over4 H)
    ((((finite_over (L := H.E) (hP.splits (H.g 0) (by simp)).1).union (finite_over (hP.splits (H.g 1) (by simp)).1)).union
      ((finite_over (hP.splits H.pde (by simp)).1).union (finite_over (hP.splits H.pde' (by simp)).1))).subset (by
        rintro w (⟨k, h⟩ | h | h)
        · fin_cases k
          exacts [Or.inl (Or.inl h), Or.inl (Or.inr h)]
        exacts [Or.inr (Or.inl h), Or.inr (Or.inr h)]))
    (by
      rintro w w' h (⟨k, h'⟩ | h' | h')
      exacts [Or.inl ⟨k, natCast_mem_of_under h h'⟩, Or.inr (Or.inl (natCast_mem_of_under h h')),
        Or.inr (Or.inr (natCast_mem_of_under h h'))])
    w0 (fun h => by
      obtain ⟨p, hp, h1, h2⟩ := hpr w0 h
      exact h1 (prime_eq (hP.splits p hp).1 hq.1 h2 hP.referencePlaceOverPrime))
    (fun w h => by
      obtain ⟨p, hp, -, h2⟩ := hpr w h
      exact ⟨p, (hP.splits p hp).1, h2⟩)
    hq.1 h5 hP.referencePlaceOverPrime
    (by
      rintro w (h | h)
      · obtain ⟨p, hp, -, h2⟩ := hpr w h
        exact hsp p hp w h2
      · exact hsp q0 (by simp) w (natCast_mem_of_under h.symm hP.referencePlaceOverPrime))
  exact ⟨χ, ⟨h1, h2, ⟨fun g => 2 * c g, fun g => by push_cast; rfl, h3⟩, h4, h5, h6⟩, fun w hw => h7 w (Or.inr hw)⟩

end GlobalTheory.LamTie.TeichEx

namespace GlobalTheory.LamTie

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom

end GlobalTheory.LamTie
