import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigen
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsSplitIdempotentConjugation
import Development.WeilBound.CoreStatements.HodgeTatePoints.RiRank
import Development.WeilBound.CoreStatements.HodgeTatePoints.PmonoCount

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Pmono

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
lemma mem_xIdeal (M : Submodule R (F → C)) (χ : MulChar F R) (r : R) :
    r ∈ xIdeal M χ ↔ (fun a => algebraMap R C (r * χ a)) ∈ M := by
  have : (fun a => algebraMap R C (r * χ a)) = r • fun a => algebraMap R C (χ a) := by
    funext a
    simp [Algebra.smul_def]
  rw [this]
  rfl

lemma pow_mem (AA : HopfOrder (C := C) R F) {g : F → C} (hg : g ∈ AA.carrier) (k : ℕ) :
    g ^ k ∈ AA.carrier := by
  induction k with
  | zero => rw [pow_zero]; exact AA.one_mem
  | succ k ih => rw [pow_succ]; exact AA.mul_mem _ _ ih hg

lemma mono_mem (AA : HopfOrder (C := C) R F) (σ : MulChar F R) {p f : ℕ} (hp : p ≠ 0)
    (c : ℕ → R) (hc : ∀ n, c n ∈ xIdeal AA.carrier (σ ^ p ^ n)) (e : Fin f → ℕ)
    (he : ∑ n : Fin f, e n * p ^ (n : ℕ) ≠ 0) :
    ∏ n : Fin f, c n ^ e n ∈ xIdeal AA.carrier (σ ^ (∑ n : Fin f, e n * p ^ (n : ℕ))) := by
  rw [mem_xIdeal]
  have hmem : (∏ n : Fin f, (fun a => algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a)) ^ e n) ∈
      AA.carrier :=
    Finset.prod_induction _ (fun g => g ∈ AA.carrier) (fun a b ha hb => AA.mul_mem a b ha hb)
      AA.one_mem fun n _ => pow_mem AA ((mem_xIdeal _ _ _).1 (hc n)) _
  have hfun : (fun a => algebraMap R C ((∏ n : Fin f, c n ^ e n) *
      (σ ^ (∑ n : Fin f, e n * p ^ (n : ℕ))) a)) =
      ∏ n : Fin f, (fun a => algebraMap R C (c n * (σ ^ p ^ (n : ℕ)) a)) ^ e n := by
    funext a
    rw [Finset.prod_apply, MulChar.pow_apply' _ he, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [Pi.pow_apply, MulChar.pow_apply' _ (pow_ne_zero _ hp), ← map_pow (algebraMap R C), mul_pow,
      ← pow_mul,
      mul_comm (e n)]
  rw [hfun]
  exact hmem

end

lemma prod_digits {p f : ℕ} (hp : p ≠ 0) (w : ℕ → NNReal) :
    (∏ d : Fin f → Fin p, if ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = 0 then 1
      else w (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ))) = ∏ m ∈ Finset.Icc 1 (p ^ f - 1), w m := by
  have h1 : (∏ d : Fin f → Fin p, if ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = 0 then 1
      else w (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ))) =
      ∏ i : Fin (p ^ f), if (i : ℕ) = 0 then 1 else w i :=
    Fintype.prod_equiv finFunctionFinEquiv _ _ fun d => by rw [finFunctionFinEquiv_apply]
  have hq : 0 < p ^ f := pow_pos (Nat.pos_of_ne_zero hp) _
  have h2 : Finset.range (p ^ f) = insert 0 (Finset.Icc 1 (p ^ f - 1)) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [h1, Fin.prod_univ_eq_prod_range (fun i => if i = 0 then 1 else w i), h2,
    Finset.prod_insert (by simp), if_pos rfl, one_mul]
  refine Finset.prod_congr rfl fun m hm => if_neg ?_
  have := (Finset.mem_Icc.1 hm).1
  omega

theorem r_mono : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → (∀ n, v (p : C) ≤ v (algebraMap R C (c n)) ^ (p - 1)) ∧ ∀ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) → xIdeal AA.carrier (σ ^ (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ))) = Ideal.span {∏ n : Fin f, c n ^ (d n : ℕ)} := by
  intro p hpp C _ _ _ v R _ _ hv hvp F _ _ _ _ f hf AA hst σ hσ c hc
  have hp0 : p ≠ 0 := hpp.out.ne_zero
  obtain ⟨AD, hstD, hcol, hfund⟩ := rank_one_sum p C v R hv hvp F f hf AA hst
  obtain ⟨-, -, hpow, -, -⟩ := GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hvp F f hf σ hσ
  choose g hg0 hg using fun m : ℕ => (eig_rank_one p C v R hv hvp F f hf AA hst (σ ^ m)).1
  choose gD hgD0 hgD using fun m : ℕ => (eig_rank_one p C v R hv hvp F f hf AD hstD (σ ^ m)).1
  have hx : ∀ n : ℕ, (v (algebraMap R C (c n)) * v (algebraMap R C (gD (p ^ n)))) ^ (p - 1) =
      v (p : C) := fun n => hfund (σ ^ p ^ n) (hpow n) _ _ (hc n) (hgD _)
  have hle : ∀ (BB : HopfOrder (C := C) R F) (γ b : ℕ → R),
      (∀ m, xIdeal BB.carrier (σ ^ m) = Ideal.span {γ m}) →
      (∀ n, xIdeal BB.carrier (σ ^ p ^ n) = Ideal.span {b n}) →
      ∀ d : Fin f → Fin p, ∏ n : Fin f, v (algebraMap R C (b n)) ^ (d n : ℕ) ≤
        if ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) = 0 then 1
        else v (algebraMap R C (γ (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ)))) := by
    intro BB γ b hγ hb d
    split_ifs with h
    · exact Finset.prod_le_one' fun n _ => pow_le_one' (hv.map_le_one _) _
    · have hm := mono_mem BB σ hp0 b
        (fun n => by rw [hb n]; exact Ideal.mem_span_singleton_self _) (fun n => (d n : ℕ)) h
      rw [hγ, Ideal.mem_span_singleton, hv.dvd_iff_le] at hm
      simpa only [map_prod, map_pow] using hm
  refine ⟨fun n => ?_, fun d hd => ?_⟩
  · rw [← hx n]
    exact pow_le_pow_left' (mul_le_of_le_one_right' (hv.map_le_one _)) _
  · have hN := (PositivityTheory.HtPt.Ri.r_decomp p C v R hv hvp F f hf AA hst σ hσ g hg).2.2
    have hD := (PositivityTheory.HtPt.Ri.r_decomp p C v R hv hvp F f hf AD hstD σ hσ gD hgD).2.2
    have hP : v (p : C) ≠ 0 := by
      rw [Ne, map_eq_zero]
      exact_mod_cast hp0
    have key := (count p f hpp.out.two_le (v (p : C)) hP (fun n => v (algebraMap R C (c n)))
      (fun n => v (algebraMap R C (gD (p ^ (n : ℕ))))) _ _ (fun n => hx n) (hle AA g c hg hc)
      (hle AD gD (fun n => gD (p ^ n)) hgD fun n => hgD _)
      (by
        rw [Finset.prod_mul_distrib, prod_digits hp0 fun m => v (algebraMap R C (g m)),
          prod_digits hp0 fun m => v (algebraMap R C (gD m))]
        exact hcol _ _ hN hD) d).1
    have hne : ∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ) ≠ 0 := by
      obtain ⟨n, hn⟩ := hd
      intro h
      exact mul_ne_zero hn (pow_ne_zero _ hp0)
        (Finset.sum_eq_zero_iff.1 h n (Finset.mem_univ n))
    rw [if_neg hne] at key
    rw [hg]
    have hval : v (algebraMap R C (∏ n : Fin f, c n ^ (d n : ℕ))) =
        v (algebraMap R C (g (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ)))) := by
      rw [key]
      simp only [map_prod, map_pow]
    exact le_antisymm (Ideal.span_singleton_le_span_singleton.2 (hv.dvd_of_le hval.ge))
      (Ideal.span_singleton_le_span_singleton.2 (hv.dvd_of_le hval.le))

end PositivityTheory.HtPt.Pmono
