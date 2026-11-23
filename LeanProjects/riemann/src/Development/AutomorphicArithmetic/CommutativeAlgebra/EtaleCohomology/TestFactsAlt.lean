import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationSquareOfValuationMod
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.FiltrationSpanDividedPowers

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

private theorem val_aic {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S]
    (hnz : ϖ ∈ nonZeroDivisors S) (h0 : Val0 (S ⧸ Ideal.span {ϖ ^ 2})) (ha : Aic (S ⧸ Ideal.span {ϖ ^ 2})) :
    Val ϖ ∧ Aic S := by
  have hj : ϖ ∈ (⊥ : Ideal S).jacobson :=
    IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self ϖ)
  have hjb : ∀ J : Ideal S, Ideal.Quotient.mk J ϖ ∈ (⊥ : Ideal (S ⧸ J)).jacobson := by
    intro J
    rw [Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    simpa using (Ideal.mem_jacobson_bot.1 hj z).map (Ideal.Quotient.mk J)
  have hd : ∀ P : Ideal S, P.IsPrime → Dich (Ideal.Quotient.mk (compI P) ϖ) := fun P hP =>
    RL.dich_of_mod _ (hjb _) (RL.valuation_square_of_valuation_mod ϖ h0 P hP)
  have hv : Val ϖ := RL.val_of_dich ϖ fun m hm => hd m hm.isPrime
  refine ⟨hv, RL.aic_limit ϖ (RL.step_glob ϖ fun m hm => ?_) (RL.pow_dvd ϖ hnz hv)⟩
  refine RL.step_comp _ (hjb _) ((RL.dich_comp ϖ m hm.isPrime).2 hnz) (hd m hm.isPrime) ?_
  refine (RL.surj_pass (Ideal.Quotient.lift (Ideal.span {ϖ ^ 2})
    ((Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (compI m) ϖ ^ 2})).comp (Ideal.Quotient.mk (compI m))) ?_)
    (Ideal.Quotient.lift_surjective_of_surjective _ _
      (Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective))).1 ha
  intro a ha'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha'
  simp only [RingHom.comp_apply, map_mul, map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

private theorem splits {T : Type} [CommRing T] (ha : Aic T) (hl : Loc T) (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of T)) (he : Etale f) (hs : Surjective f) : ∃ s, s ≫ f = 𝟙 _ := by
  obtain ⟨h0, hm, h1⟩ := RL.sec_rules Y f
  exact h1 (RL.glue (SecOn f) h0 (fun e e' _ _ h => hm e e' h)
    (fun e e' h₁ h₂ h₃ => RL.sec_add Y f e e' h₁ h₂ h₃) fun m hm' => RL.split_pt ha hl Y f he hs m hm')

theorem UpperTheory.Ru.crystallineComparison.testFacts :
    UpperTheory.Ru.crystallineComparison.TestFacts := by
  intro l _ A hA
  obtain ⟨ϖ, hϖ, h0, ha⟩ := RL.untilt_valuation_mod_square A hA
  have hl : (l : A.U) ∈ nonZeroDivisors A.U := (RL.u_tf A).1
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : IsAdicComplete (Ideal.span {ϖ}) A.U :=
    (RL.val_pow ϖ l hl0).2 (by rw [hϖ]; exact RL.u_complete A)
  have hnz : ϖ ∈ nonZeroDivisors A.U := by
    have h : ϖ ^ (l - 1) * ϖ ∈ nonZeroDivisors A.U := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hl0), hϖ]
      exact hl
    exact (mul_mem_nonZeroDivisors.1 h).2
  obtain ⟨hv, hU⟩ := val_aic ϖ hnz h0 ha
  have hvl : Val (l : A.U) := by
    rw [← hϖ]
    exact (RL.val_pow ϖ l hl0).1.2 hv
  obtain ⟨hL, hLg⟩ := (RL.loc_aic (l : A.U)).1 hvl
  exact ⟨hl, RL.int_closed _ hl hvl, fun Y f he hs => splits ((RL.loc_aic (l : A.U)).2 hU) hLg Y f he hs,
    fun Y f he hs => splits hU hL Y f he hs, RL.idem_au A⟩
