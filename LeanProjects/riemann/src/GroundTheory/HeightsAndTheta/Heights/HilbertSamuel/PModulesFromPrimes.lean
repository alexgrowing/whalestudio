import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDegLTGrowth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFiltrationHilbSum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u v

theorem degLT_diffStep {K : Type*} {n : ℕ} {f : (K → ℤ) → ℤ} (hf : DegLT f (n + 1))
    (b : K → ℤ) : DegLT (diffStep b f) n := by
  intro bs
  have h := hf (Fin.snoc bs b)
  have he : mixedDiff (Fin.snoc bs b) f = mixedDiff bs (diffStep b f) := by
    unfold mixedDiff
    rw [List.ofFn_succ', List.concat_eq_append, List.foldr_append]
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  rwa [he] at h

theorem exists_le_of_filtration {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (N : Fin (n + 1) → Submodule R M) (x : Fin n → M) (q : Fin n → Ideal R)
    (h0 : N 0 = ⊥) (htop : N (Fin.last n) = ⊤)
    (hstep : ∀ j : Fin n, N j.succ = N j.castSucc ⊔ Submodule.span R {x j} ∧
      ∀ s : R, s • x j ∈ N j.castSucc ↔ s ∈ q j)
    (p : Ideal R) [hp : p.IsPrime] (hann : Module.annihilator R M ≤ p) : ∃ j, q j ≤ p := by
  by_contra hne
  push Not at hne
  have hs : ∀ j, ∃ s ∈ q j, s ∉ p := fun j => Set.not_subset.mp (hne j)
  choose s hsq hsp using hs
  have key : ∀ i (hi : i < n + 1), ∃ t ∉ p, ∀ y ∈ N ⟨i, hi⟩, t • y = 0 := by
    intro i
    induction i with
    | zero =>
      intro hi
      refine ⟨1, (Ideal.ne_top_iff_one p).mp hp.ne_top, fun y hy => ?_⟩
      rw [show (⟨0, hi⟩ : Fin (n + 1)) = 0 from Fin.ext (by simp), h0, Submodule.mem_bot] at hy
      simp [hy]
    | succ i ih =>
      intro hi
      obtain ⟨t, htp, ht⟩ := ih (by omega)
      let j : Fin n := ⟨i, by omega⟩
      refine ⟨t * s j, fun hm => (hp.mem_or_mem hm).elim htp (hsp j), fun y hy => ?_⟩
      have hy' : y ∈ N j.succ := hy
      rw [(hstep j).1, Submodule.mem_sup] at hy'
      obtain ⟨z, hz, w, hw, rfl⟩ := hy'
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have h1 : s j • (z + r • x j) ∈ N j.castSucc := by
        rw [smul_add, smul_comm (s j) r (x j)]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ hz)
          (Submodule.smul_mem _ _ (((hstep j).2 _).2 (hsq j)))
      rw [mul_smul]
      exact ht _ h1
  obtain ⟨t, htp, ht⟩ := key n (Nat.lt_succ_self n)
  apply htp
  apply hann
  rw [Module.mem_annihilator]
  intro y
  apply ht
  rw [show (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n from rfl, htop]
  trivial

theorem ModulesFromPrimes.proof (hF : MultigradedFiltration.Statement.{u, v})
    (hS : FiltrationHilbSum.Statement.{u, v}) (hG : DegLTGrowth.Statement) :
    ModulesFromPrimes.Statement.{u, v} := by
  intro d hP F _ K _ _ ι _ M _ _ _ _ _ piece hM hdim
  classical
  obtain ⟨n, N, x, c, q, hN0, hNtop, hstep, hcount⟩ := hF F K ι M piece hM
  have hsum := hS F K ι M piece hM n N x c q hN0 hNtop
    (fun j => ⟨(hstep j).1, (hstep j).2.1, (hstep j).2.2.2.2⟩)
  have hann : ∀ j, Module.annihilator (MRing ι F) M ≤ q j := by
    intro j s hs
    refine ((hstep j).2.2.2.2 s).1 ?_
    rw [Module.mem_annihilator.mp hs (x j)]
    exact Submodule.zero_mem _

  have hmin : ∀ W : Ideal (MRing ι F), IsMultiProjPrime W →
      Module.annihilator (MRing ι F) M ≤ W →
      ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
      W ∈ (Module.annihilator (MRing ι F) M).minimalPrimes ∧ ∃ j, q j = W := by
    intro W hW hannW hdimW
    have := hW.isPrime
    obtain ⟨p, hp, hpW⟩ := Ideal.exists_minimalPrimes_le hannW
    have : p.IsPrime := hp.1.1
    obtain ⟨j, hjp⟩ := exists_le_of_filtration N x q hN0 hNtop
      (fun j => ⟨(hstep j).2.1, (hstep j).2.2.2.2⟩) p hp.1.2
    have hjW : q j = W := by
      by_contra hne
      have hlt : q j < W := lt_of_le_of_ne (hjp.trans hpW) hne
      obtain ⟨-, -, hprime, hhom, -⟩ := hstep j
      have := hprime
      have hrel : IsRelevant (q j) := fun k =>
        (hW.relevant k).imp fun i hi hm => hi ((hjp.trans hpW) hm)
      have h1 := hdim (q j) ⟨hprime, hhom, hrel⟩ (hann j)
      have h2 := DimStrictDrop.full (MRing ι F) (q j) W hlt
      rw [hdimW] at h2
      have h3 := h2.trans h1
      have h4 : (((d + Fintype.card K + 1 : ℕ)) : WithBot ℕ∞) ≤
          ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by exact_mod_cast h3
      have h5 : d + Fintype.card K + 1 ≤ d + Fintype.card K := by exact_mod_cast h4
      omega
    have hpeq : p = W := le_antisymm hpW (hjW ▸ hjp)
    exact ⟨hpeq ▸ hp, j, hjW⟩

  obtain ⟨t, ht_def⟩ : ∃ t : Fin n → (K → ℕ) → ℤ, ∀ j a, t j a =
      if IsRelevant (q j) ∧
          ringKrullDim (MRing ι F ⧸ q j) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) then
        intNum F (q j) (fun _ : Fin d => fun k => (a k : ℤ))
      else 0 := ⟨_, fun _ _ => rfl⟩

  have hj : ∀ j, ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |(hilbFn (q j) ((fun k => (a k : ℤ)) - c j) : ℝ) - (t j a : ℝ) / d.factorial| ≤
        C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1) := by
    intro j
    obtain ⟨-, -, hprime, hhom, -⟩ := hstep j
    by_cases hrel : IsRelevant (q j)
    · by_cases htop : ringKrullDim (MRing ι F ⧸ q j) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
      ·
        obtain ⟨a₁, C₁, h₁⟩ := hP d le_rfl F K ι (q j) ⟨hprime, hhom, hrel⟩ htop
        have hlt : ringKrullDim (MRing ι F ⧸ q j) <
            (((d + 1) + Fintype.card K : ℕ) : WithBot ℕ∞) := by
          rw [htop]
          exact_mod_cast (by omega : d + Fintype.card K < d + 1 + Fintype.card K)
        have hdeg := HilbDegBound.full F K ι (d + 1) (q j) hprime hhom hlt
        obtain ⟨a₂, C₂, h₂⟩ := hG K d _ (degLT_diffStep hdeg (c j))
        refine ⟨max a₁ a₂, C₁ + C₂, fun a ha => ?_⟩
        have e1 := h₁ a (fun k => le_trans (le_max_left _ _) (ha k))
        have e2 := h₂ a (fun k => le_trans (le_max_right _ _) (ha k))
        rw [ht_def, if_pos ⟨hrel, htop⟩]
        simp only [diffStep] at e2
        push_cast at e2
        rw [abs_le] at e1 e2 ⊢
        constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2]
      ·
        have hle := hdim (q j) ⟨hprime, hhom, hrel⟩ (hann j)
        have hlt : ringKrullDim (MRing ι F ⧸ q j) < ((d + Fintype.card K : ℕ) : WithBot ℕ∞) :=
          lt_of_le_of_ne hle htop
        have hdeg := HilbDegBound.full F K ι d (q j) hprime hhom hlt
        have hsh := (DegLTClosure.full K d (hilbFn (q j)) (hilbFn (q j)) 0 (c j)).2.2.1 hdeg
        obtain ⟨a₀, C, h⟩ := hG K d _ hsh
        refine ⟨a₀, C, fun a ha => ?_⟩
        rw [ht_def, if_neg (fun h' => htop h'.2)]
        simpa [shiftFn] using h a ha
    ·
      have ht0 : ∀ a, t j a = 0 := fun a => by rw [ht_def, if_neg (fun h' => hrel h'.1)]
      simp only [IsRelevant, not_forall, not_exists, not_not] at hrel
      obtain ⟨k₀, hk₀⟩ := hrel
      refine ⟨(c j k₀).toNat + 1, 0, fun a ha => ?_⟩
      have hv : hilbFn (q j) ((fun k => (a k : ℤ)) - c j) = 0 := by
        apply HilbFnVanishBlock.full F K ι (q j) k₀ hk₀
        have := ha k₀
        simp only [Pi.sub_apply]
        omega
      rw [ht0, hv]
      simp
  choose A C hAC using hj
  refine ⟨Finset.univ.sup A, ∑ j, C j, fun a ha => ?_⟩
  have hA : ∀ j k, A j ≤ a k := fun j k => le_trans (Finset.le_sup (Finset.mem_univ j)) (ha k)

  have hcyc : topCycleNum F ι M d (fun _ : Fin d => fun k => (a k : ℤ)) = ∑ j, t j a := by
    unfold topCycleNum
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image q) ?sub]
    case sub =>
      intro W hW
      rw [Function.mem_support] at hW
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      by_contra hnot
      apply hW
      rw [dif_neg]
      rintro ⟨h1, h2, h3⟩
      obtain ⟨-, j, hj⟩ := hmin W h1 h2 h3
      exact hnot ⟨j, hj⟩
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image q) (g := q)
      (fun j _ => Finset.mem_image_of_mem q (Finset.mem_univ j))]
    refine Finset.sum_congr rfl fun W hW => ?_
    obtain ⟨j₀, -, rfl⟩ := Finset.mem_image.mp hW
    have hfib : ∀ j ∈ Finset.univ.filter (fun j => q j = q j₀), t j a = t j₀ a := by
      intro j hj
      rw [ht_def, ht_def, (Finset.mem_filter.mp hj).2]
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul, ht_def]
    obtain ⟨-, -, hprime, hhom, -⟩ := hstep j₀
    by_cases htop : IsRelevant (q j₀) ∧
        ringKrullDim (MRing ι F ⧸ q j₀) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
    · have hc : IsMultiProjPrime (q j₀) ∧ Module.annihilator (MRing ι F) M ≤ q j₀ ∧
          ringKrullDim (MRing ι F ⧸ q j₀) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) :=
        ⟨⟨hprime, hhom, htop.1⟩, hann j₀, htop.2⟩
      rw [dif_pos hc, if_pos htop]
      have hm := (hmin _ hc.1 hc.2.1 hc.2.2).1
      have hct := hcount (q j₀) hm
      congr 1
      rw [← hct]
      simp
    · rw [dif_neg (fun h => htop ⟨h.1.relevant, h.2.2⟩), if_neg htop, mul_zero]
  have hfin : (Module.finrank F (piece fun k => (a k : ℤ)) : ℝ) =
      ∑ j, (hilbFn (q j) ((fun k => (a k : ℤ)) - c j) : ℝ) := by
    have := hsum (fun k => (a k : ℤ))
    exact_mod_cast this
  rw [hfin, hcyc, Int.cast_sum, Finset.sum_div, ← Finset.sum_sub_distrib, Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hAC j a (hA j))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
