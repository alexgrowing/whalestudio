import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem UpperTheory.V.Pa.BC.chain_lift_down (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B']
    [Module.Flat B B'] (P : Ideal B') (q : Ideal B) (hP : P.IsPrime) (hq : q.IsPrime)
    (hle : q ≤ P.comap (algebraMap B B')) :
    ∃ Q : Ideal B', Q.IsPrime ∧ Q.comap (algebraMap B B') = q ∧ Q ≤ P := by
  haveI : (P.comap (algebraMap B B')).IsPrime := Ideal.comap_isPrime _ _
  haveI : P.LiesOver (P.comap (algebraMap B B')) := ⟨rfl⟩
  obtain ⟨Q, h1, h2, h3⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := q)
    (q := P.comap (algebraMap B B')) P hle
  exact ⟨Q, h2, h3.over.symm, h1⟩

private theorem UpperTheory.V.Pa.BC.prime_chain_lift_extension (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B']
    [Algebra.IsIntegral B B'] [Module.Flat B B'] (h : ℕ) :
    ∀ (p : Fin (h + 1) → Ideal B) (e : Fin h → Ideal B), (∀ i, (p i).IsPrime) →
      (∀ i, (e i).IsPrime ∧ e i ≤ p i.castSucc ∧ e i ≤ p i.succ) →
      ∀ P0 : Ideal B', P0.IsPrime → P0.comap (algebraMap B B') = p 0 →
      ∃ (P : Fin (h + 1) → Ideal B') (E : Fin h → Ideal B'), P 0 = P0 ∧
        (∀ i, (P i).IsPrime ∧ (P i).comap (algebraMap B B') = p i) ∧
        ∀ i, (E i).IsPrime ∧ (E i).comap (algebraMap B B') = e i ∧ E i ≤ P i.castSucc ∧
          E i ≤ P i.succ := by
  induction h with
  | zero =>
    intro p e _ _ P0 hP0 hP0c
    refine ⟨fun _ => P0, Fin.elim0, rfl, ?_, fun i => i.elim0⟩
    intro i
    rw [Fin.fin_one_eq_zero i]
    exact ⟨hP0, hP0c⟩
  | succ h ih =>
    intro p e hp he P0 hP0 hP0c
    obtain ⟨he0, he0l, he0r⟩ := he 0
    obtain ⟨E0, hE0, hE0c, hE0le⟩ :=
      UpperTheory.V.Pa.BC.chain_lift_down B B' P0 (e 0) hP0 he0 (by rw [hP0c]; exact he0l)
    haveI := hp (Fin.succ 0)
    haveI := hE0
    obtain ⟨P1, hP1ge, hP1, hP1c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
      (p (Fin.succ 0)) E0 (by rw [hE0c]; exact he0r)
    obtain ⟨P', E', hP'0, hP', hE'⟩ := ih (fun i => p i.succ) (fun i => e i.succ)
      (fun i => hp i.succ)
      (fun i => by
        obtain ⟨a, b, c⟩ := he i.succ
        refine ⟨a, ?_, c⟩
        rw [← Fin.succ_castSucc] at b
        exact b)
      P1 hP1 hP1c
    refine ⟨(Fin.cons P0 P' : Fin (h + 1 + 1) → Ideal B'),
      (Fin.cons E0 E' : Fin (h + 1) → Ideal B'), Fin.cons_zero _ _, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => rw [Fin.cons_zero]; exact ⟨hP0, hP0c⟩
      | succ j => rw [Fin.cons_succ]; exact hP' j
    · intro i
      cases i using Fin.cases with
      | zero =>
        rw [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hP'0]
        exact ⟨hE0, hE0c, hE0le, hP1ge⟩
      | succ j =>
        rw [Fin.cons_succ, ← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact hE' j

theorem UpperTheory.V.Pa.BC.chain_lift :
    ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B'] [Algebra.IsIntegral B B'] [Module.Flat B B'] [FaithfulSMul B B'] (h : ℕ) (p : Fin (h + 1) → Ideal B) (e : Fin h → Ideal B), (∀ i, (p i).IsPrime) → (∀ i, (e i).IsPrime ∧ e i ≤ p i.castSucc ∧ e i ≤ p i.succ) → (∃ (P : Fin (h + 1) → Ideal B') (E : Fin h → Ideal B'), (∀ i, (P i).IsPrime ∧ (P i).comap (algebraMap B B') = p i) ∧ ∀ i, (E i).IsPrime ∧ (E i).comap (algebraMap B B') = e i ∧ E i ≤ P i.castSucc ∧ E i ≤ P i.succ) ∧ ∀ (P : Ideal B') (q : Ideal B), P.IsPrime → q.IsPrime → q ≤ P.comap (algebraMap B B') → ∃ Q : Ideal B', Q.IsPrime ∧ Q.comap (algebraMap B B') = q ∧ Q ≤ P := by
  intro B B' _ _ _ _ _ _ h p e hp he
  refine ⟨?_, fun P q hP hq hle => UpperTheory.V.Pa.BC.chain_lift_down B B' P q hP hq hle⟩
  haveI := hp 0
  obtain ⟨P0, _, hP0, hP0c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B') (p 0) ⊥ (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    rw [(FaithfulSMul.algebraMap_injective B B') (hx.trans (map_zero _).symm)]
    exact Ideal.zero_mem _)
  obtain ⟨P, E, _, hPc, hE⟩ := UpperTheory.V.Pa.BC.prime_chain_lift_extension B B' h p e hp he P0 hP0 hP0c
  exact ⟨P, E, hPc, hE⟩
