import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.TwistAcrisZeroPreservesFiltration

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.R

variable {S : Type} [CommRing S]

theorem mk_mem_jacobson {ϖ : S} (h : ϖ ∈ (⊥ : Ideal S).jacobson) (I : Ideal S) :
    Ideal.Quotient.mk I ϖ ∈ (⊥ : Ideal (S ⧸ I)).jacobson := by
  rw [Ideal.mem_jacobson_bot] at h ⊢
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  simpa using (h y).map (Ideal.Quotient.mk I)

theorem mem_jacobson_of_complete (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S] : ϖ ∈ (⊥ : Ideal S).jacobson :=
  IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self ϖ)

theorem valuation_of_valuation_mod_square (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S] (h : Val0 (S ⧸ Ideal.span {ϖ ^ 2})) : Val ϖ :=
  RL.val_of_dich ϖ fun m hm =>
    RL.dich_of_mod _ (mk_mem_jacobson (mem_jacobson_of_complete ϖ) _) (RL.valuation_square_of_valuation_mod ϖ h m hm.isPrime)

theorem aic_of_mod (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S] (h0 : ϖ ∈ nonZeroDivisors S) (hv : Val ϖ)
    (h : Aic (S ⧸ Ideal.span {ϖ ^ 2})) : Aic S := by
  refine RL.aic_limit ϖ (RL.step_glob ϖ fun m hm => ?_) (RL.pow_dvd ϖ h0 hv)
  refine RL.step_comp _ (mk_mem_jacobson (mem_jacobson_of_complete ϖ) _) ((RL.dich_comp ϖ m hm.isPrime).2 h0)
    ((RL.dich_comp ϖ m hm.isPrime).1 hv) ((RL.surj_pass (Ideal.quotientMap _ (Ideal.Quotient.mk (compI m)) ?_) ?_).1 h)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _
  · exact Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective

theorem splits (ha : Aic S) (hl : Loc S) : Splits (Spec (CommRingCat.of S)) := fun Y f he hs =>
  (RL.sec_rules Y f).2.2 (RL.glue (SecOn f) (RL.sec_rules Y f).1 (fun e e' _ _ => (RL.sec_rules Y f).2.1 e e')
    (RL.sec_add Y f) (RL.split_pt ha hl Y f he hs))

end CrystallineSemistableComparison.R

namespace CrystallineSemistableComparison.PAlg

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem l_mem_nzd_U : (l : A.U) ∈ nonZeroDivisors A.U := (RL.u_tf A).1

instance completeU : IsAdicComplete (Ideal.span {(l : A.U)}) A.U := RL.u_complete A

variable {A}

theorem IsTest.val_aic (h : A.IsTest) : R.Val (l : A.U) ∧ R.Aic A.U := by
  obtain ⟨ϖ, e, h0, h1⟩ := RL.untilt_valuation_mod_square A h
  have hl := (Fact.out : l.Prime).ne_zero
  have : IsAdicComplete (Ideal.span {ϖ}) A.U := (RL.val_pow ϖ l hl).2 (e.symm ▸ A.completeU)
  have hv := R.valuation_of_valuation_mod_square ϖ h0
  have hz : ϖ ∈ nonZeroDivisors A.U := by
    have := A.l_mem_nzd_U
    rw [← e] at this
    obtain ⟨c, hc⟩ := dvd_pow_self ϖ hl
    rw [hc] at this
    exact (mul_mem_nonZeroDivisors.1 this).1
  exact ⟨e ▸ (RL.val_pow ϖ l hl).1.2 hv, R.aic_of_mod ϖ hz hv h1⟩

theorem IsTest.splitU (h : A.IsTest) : R.Splits (Spec (CommRingCat.of A.U)) :=
  R.splits h.val_aic.2 ((RL.loc_aic (l : A.U)).1 h.val_aic.1).1

theorem IsTest.splitUg (h : A.IsTest) : R.Splits (Spec (CommRingCat.of A.Ug)) :=
  R.splits ((RL.loc_aic (l : A.U)).2 h.val_aic.2) ((RL.loc_aic (l : A.U)).1 h.val_aic.1).2

theorem IsTest.intClosed (h : A.IsTest) (x : A.Ug) (hx : IsIntegral A.U x) : ∃ y, algebraMap A.U A.Ug y = x :=
  RL.int_closed _ A.l_mem_nzd_U h.val_aic.1 x hx

theorem algebraMap_Ug_injective (A : PAlg l) : Function.Injective (algebraMap A.U A.Ug) :=
  IsLocalization.injective _ (M := Submonoid.powers (l : A.U)) (Submonoid.powers_le.2 A.l_mem_nzd_U)

theorem IsTest.idem (h : A.IsTest) (e : A.Ug) (he : IsIdempotentElem e) :
    ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ algebraMap A.U A.Ug (A.sharp e₀) = e := by
  obtain ⟨y, rfl⟩ := h.intClosed e ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by decide)), by
    simp [pow_two, he.eq]⟩
  have hy : IsIdempotentElem y := A.algebraMap_Ug_injective (by rw [map_mul, he.eq])
  obtain ⟨e₀, h₀, hu⟩ := RL.idem_au A y hy
  exact ⟨e₀, ⟨h₀.1, by rw [h₀.2]⟩, fun e₁ h₁ => hu e₁ ⟨h₁.1, A.algebraMap_Ug_injective h₁.2⟩⟩

theorem IsTest.sharp_surjective (h : A.IsTest) : Function.Surjective A.sharp := fun f => by
  have hl := (Fact.out : l.Prime).pos
  have hr : ∀ x : A.U, ∃ y, y ^ l = x := fun x => by
    rcases subsingleton_or_nontrivial A.U with h' | h'
    · exact ⟨0, Subsingleton.elim _ _⟩
    obtain ⟨y, hy⟩ := h.val_aic.2 (Polynomial.X ^ l - Polynomial.C x) (Polynomial.monic_X_pow_sub_C x hl.ne')
      (by rw [Polynomial.natDegree_X_pow_sub_C]; exact hl)
    exact ⟨y, by simpa [sub_eq_zero] using hy⟩
  choose r hr using hr
  obtain ⟨a, -, ha⟩ := RL.tilt_ex A (fun i => r^[i] f) fun i => by rw [Function.iterate_succ_apply', hr]
  exact ⟨a 0, ha 0⟩

theorem IsTest.sharp_unit (h : A.IsTest) (u : (A.U)ˣ) : ∃ w : (A.A)ˣ, A.sharp w = u := by
  obtain ⟨a, ha⟩ := h.sharp_surjective u
  obtain ⟨w, rfl⟩ := RL.unit_lift A a (ha ▸ u.isUnit)
  exact ⟨w, ha⟩

end CrystallineSemistableComparison.PAlg
