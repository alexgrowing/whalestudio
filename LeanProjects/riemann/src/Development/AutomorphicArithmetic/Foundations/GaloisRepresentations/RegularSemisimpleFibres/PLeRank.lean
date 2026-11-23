import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem gcd_step {m m' c l : ℕ} (hm : 0 < m) (hl : l.Prime) (h : m' * Nat.gcd m c = m) :
    (if l ∣ m' then m' / l else m') * Nat.gcd m (c * l) = m := by
  have hg : 0 < Nat.gcd m c := Nat.gcd_pos_of_pos_left _ hm
  obtain ⟨m₁, c₁, hco, hm₁, hc₁⟩ := Nat.exists_coprime m c
  have hmm : m₁ = m' := by
    apply Nat.eq_of_mul_eq_mul_right hg
    rw [← hm₁, h]
  subst hmm
  set g := Nat.gcd m c with hgdef
  have hgcd : Nat.gcd m (c * l) = Nat.gcd m₁ l * g := by
    have e : c * l = (c₁ * l) * g := by
      rw [hc₁]; ring
    rw [e]
    conv_lhs => rw [hm₁]
    rw [Nat.gcd_mul_right, Nat.Coprime.gcd_mul_left_cancel_right l hco.symm]
  rw [hgcd]
  split_ifs with hd
  · rw [Nat.gcd_eq_right hd, ← mul_assoc, Nat.div_mul_cancel hd]
    exact h
  · have : Nat.gcd m₁ l = 1 := ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).symm
    rw [this, one_mul]
    exact h

theorem UpperTheory.Gal.InertialTypesAlt.leRank :
    LiftOk → LeRank := by
  intro hOk a b ha hab
  have key : b.Ok ∧ ∃ c : ℕ, 0 < c ∧ b.q = a.q ^ c ∧
      ∀ p ∈ b.L, ∃ r ∈ a.L, p.1 * Nat.gcd r.1 c = r.1 := by
    induction hab with
    | refl =>
      refine ⟨ha, 1, Nat.one_pos, (pow_one _).symm, fun p hp => ⟨p, hp, ?_⟩⟩
      rw [Nat.gcd_one_right, mul_one]
    | @tail b' b'' _ hs ih =>
      obtain ⟨hb, c, hc, hq, hL⟩ := ih
      obtain ⟨l, hl, rfl⟩ := hs
      refine ⟨(hOk b' l hl hb).1, c * l, Nat.mul_pos hc hl.pos, ?_, ?_⟩
      · change b'.q ^ l = _
        rw [hq, pow_mul]
      · intro p hp
        have hp' : p ∈ liftAll b'.q l b'.L := hp
        unfold liftAll at hp'
        obtain ⟨s, hs, hps⟩ := List.mem_flatMap.1 hp'
        obtain ⟨r, hr, hsr⟩ := hL s hs
        refine ⟨r, hr, ?_⟩
        have hm : 0 < r.1 := (ha.2.2 r hr).1
        have hstep := gcd_step (l := l) hm hl hsr
        have hp1 : p.1 = if l ∣ s.1 then s.1 / l else s.1 := by
          split_ifs at hps ⊢ with hd
          · simp only [liftL, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map] at hps
            obtain ⟨i, -, rfl⟩ := hps
            rfl
          · simp only [List.mem_singleton] at hps
            rw [hps]
        rw [hp1]
        exact hstep
  exact key.2
