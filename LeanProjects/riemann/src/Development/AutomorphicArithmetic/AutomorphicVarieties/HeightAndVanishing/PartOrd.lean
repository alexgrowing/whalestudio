import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem orderOf_pow_coprime_parts {Γ : Type} [Group Γ] (x : Γ) (P C e : ℕ) (hn : orderOf x = P * C)
    (hP : 0 < P) (hC : 0 < C) (hco : P.Coprime C) (h1 : C ∣ e) (h2 : e ≡ 1 [MOD P]) :
    orderOf (x ^ e) = P ∧ orderOf (x * (x ^ e)⁻¹) = C := by
  have hcx : Commute (x ^ e) x := (Commute.refl x).pow_left e
  have hcomm : Commute (x ^ e) (x * (x ^ e)⁻¹) := hcx.mul_right (Commute.refl _).inv_right
  have hyz : x ^ e * (x * (x ^ e)⁻¹) = x := by
    rw [← mul_assoc, hcx.eq, mul_inv_cancel_right]
  have hoy : orderOf (x ^ e) ∣ P := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, orderOf_dvd_iff_pow_eq_one.mp]
    rw [hn, mul_comm P C]
    exact Nat.mul_dvd_mul_right h1 P
  have hoz : orderOf (x * (x ^ e)⁻¹) ∣ C := by
    apply orderOf_dvd_of_pow_eq_one
    rw [(hcx.symm.inv_right).mul_pow, inv_pow, ← pow_mul]
    have : x ^ (e * C) = x ^ C := by
      rw [pow_eq_pow_iff_modEq, hn]
      have := Nat.ModEq.mul_right' C h2
      simpa using this
    rw [this, mul_inv_cancel]
  have hco' : (orderOf (x ^ e)).Coprime (orderOf (x * (x ^ e)⁻¹)) := Nat.Coprime.of_dvd hoy hoz hco
  have hprod : orderOf (x ^ e) * orderOf (x * (x ^ e)⁻¹) = P * C := by
    rw [← hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco', hyz, hn]
  obtain ⟨a, ha⟩ := hoy
  obtain ⟨b, hb⟩ := hoz
  have hab : a * b = 1 := by
    have : P * C * (a * b) = P * C * 1 := by
      calc P * C * (a * b)
          = (orderOf (x ^ e) * orderOf (x * (x ^ e)⁻¹)) * (a * b) := by rw [hprod]
        _ = (orderOf (x ^ e) * a) * (orderOf (x * (x ^ e)⁻¹) * b) := by ring
        _ = P * C * 1 := by rw [← ha, ← hb, mul_one]
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hP hC) this
  have ha1 : a = 1 := Nat.eq_one_of_mul_eq_one_right hab
  have hb1 : b = 1 := Nat.eq_one_of_mul_eq_one_left hab
  refine ⟨?_, ?_⟩
  · rw [ha, ha1, mul_one]
  · rw [hb, hb1, mul_one]

theorem UpperTheory.V.HV.partOrd :
    ∀ (Γ : Type) [Group Γ] (l : ℕ), l.Prime → ∀ x : Γ, 0 < orderOf x →
      orderOf (lPart l x) = ordProj[l] (orderOf x) ∧ orderOf (lPrime l x) = ordCompl[l] (orderOf x) ∧ ¬ l ∣ orderOf (lPrime l x) ∧
      lPart l x ∈ Subgroup.zpowers x ∧ lPrime l x ∈ Subgroup.zpowers x ∧ (¬ l ∣ orderOf x → lPart l x = 1 ∧ lPrime l x = x) ∧
      ∀ a b : Γ, Commute a b → a * b = x → ¬ l ∣ orderOf a → (∃ s, b ^ l ^ s = 1) → lPrime l x = a ∧ lPart l x = b := by
  intro Γ _ l hl x hx
  have hn0 : orderOf x ≠ 0 := hx.ne'
  obtain ⟨P, hPd⟩ : ∃ P, P = ordProj[l] (orderOf x) := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ C, C = ordCompl[l] (orderOf x) := ⟨_, rfl⟩
  obtain ⟨e, hed⟩ : ∃ e, e = C ^ Nat.totient P := ⟨_, rfl⟩
  have hPC : P * C = orderOf x := by rw [hPd, hCd]; exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have hP : 0 < P := by rw [hPd]; exact pow_pos hl.pos _
  have hC : 0 < C := by rw [hCd]; exact Nat.ordCompl_pos l hn0
  have hlC : ¬ l ∣ C := by rw [hCd]; exact Nat.not_dvd_ordCompl hl hn0
  have hcoC : l.Coprime C := (Nat.Prime.coprime_iff_not_dvd hl).2 hlC
  have hco : P.Coprime C := by rw [hPd]; exact hcoC.pow_left _
  have hlp : lPart l x = x ^ e := by rw [hed, hPd, hCd]; rfl
  have hlpr : lPrime l x = x * (lPart l x)⁻¹ := rfl
  have h1 : C ∣ e := by rw [hed]; exact dvd_pow_self _ (Nat.totient_pos.2 hP).ne'
  have h2 : e ≡ 1 [MOD P] := by rw [hed]; exact Nat.ModEq.pow_totient hco.symm
  obtain ⟨hA, hB⟩ := orderOf_pow_coprime_parts x P C e hPC.symm hP hC hco h1 h2
  rw [← hlp] at hA hB
  rw [← hlpr] at hB
  rw [← hCd, ← hPd]
  refine ⟨hA, hB, hB ▸ hlC, ?_, ?_, ?_, ?_⟩
  · rw [hlp]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _
  · rw [hlpr, hlp]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers x)
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
  · intro hnd
    have hf : (orderOf x).factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
    have ho : orderOf (lPart l x) = 1 := by rw [hA, hPd, hf, pow_zero]
    have h1' := orderOf_eq_one_iff.mp ho
    exact ⟨h1', by rw [hlpr, h1', inv_one, mul_one]⟩
  · rintro a b hab habx hna ⟨s, hs⟩
    have hcoa : (orderOf a).Coprime l := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2 hna)
    have hob : orderOf b ∣ l ^ s := orderOf_dvd_of_pow_eq_one hs
    have hab' : (orderOf a).Coprime (orderOf b) := Nat.Coprime.coprime_dvd_right hob (hcoa.pow_right s)
    have hx' : orderOf x = orderOf a * orderOf b := by
      rw [← habx]; exact hab.orderOf_mul_eq_mul_orderOf_of_coprime hab'
    have hoaC : orderOf a ∣ C := by
      have hd : orderOf a ∣ P * C := by rw [hPC, hx']; exact dvd_mul_right _ _
      have hcP : (orderOf a).Coprime P := by rw [hPd]; exact hcoa.pow_right _
      exact hcP.dvd_of_dvd_mul_left hd
    have hobP : orderOf b ∣ P := by
      have hd : orderOf b ∣ P * C := by rw [hPC, hx']; exact dvd_mul_left _ _
      have hcC : (orderOf b).Coprime C := Nat.Coprime.coprime_dvd_left hob (hcoC.pow_left s)
      exact hcC.dvd_of_dvd_mul_right hd
    have hae : a ^ e = 1 := orderOf_dvd_iff_pow_eq_one.mp (hoaC.trans h1)
    have hbe : b ^ e = b := by
      have := (pow_eq_pow_iff_modEq (x := b) (n := e) (m := 1)).2 (h2.of_dvd hobP)
      simpa using this
    have hpart : lPart l x = b := by
      calc lPart l x = x ^ e := hlp
        _ = (a * b) ^ e := by rw [habx]
        _ = b := by rw [hab.mul_pow, hae, hbe, one_mul]
    refine ⟨?_, hpart⟩
    rw [hlpr, hpart, ← habx, mul_inv_cancel_right]
