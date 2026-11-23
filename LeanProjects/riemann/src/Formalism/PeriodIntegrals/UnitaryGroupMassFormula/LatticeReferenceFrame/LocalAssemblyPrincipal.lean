import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.SpanSmulInto

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.PPA

open PI.ScRefExists.Sk

def IsInt (I : Formalism.MainNotions.S.AutInst) (x : I.E) : Prop := ∃ a : 𝓞 I.E, (a : I.E) = x

section Int

variable (I : Formalism.MainNotions.S.AutInst)

theorem isInt_coe (a : 𝓞 I.E) : IsInt I (a : I.E) := ⟨a, rfl⟩

theorem isInt_mul {x y : I.E} (hx : IsInt I x) (hy : IsInt I y) : IsInt I (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by push_cast; rfl⟩

theorem isInt_sub {x y : I.E} (hx : IsInt I x) (hy : IsInt I y) : IsInt I (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by push_cast; rfl⟩

theorem isInt_add {x y : I.E} (hx : IsInt I x) (hy : IsInt I y) : IsInt I (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; rfl⟩

theorem isInt_one : IsInt I (1 : I.E) := ⟨1, by simp⟩

theorem isInt_hG {x y : Fin I.n → I.E} (hx : x ∈ I.L) (hy : y ∈ I.L) : IsInt I (hG I x y) := by
  obtain ⟨a, ha⟩ := (I.L_dual y).1 hy x hx
  exact ⟨a, ha⟩

theorem isInt_star (θ : 𝓞 I.E) : IsInt I (star (θ : I.E)) :=
  ⟨⟨star (θ : I.E), (RingOfIntegers.isIntegral_coe θ).map (starRingEnd I.E).toIntAlgHom⟩, rfl⟩

theorem natCast_mem_Ap (p s : ℕ) : (s : I.E) ∈ Ap I p := by
  refine ⟨1, Nat.coprime_one_left p, (s : 𝓞 I.E), ?_⟩
  simp

end Int

theorem local_assembly_principal : PPAssemble := by
  unfold PPAssemble
  intro I p m r k θ e f M w wd hp hm hH hw hew hwd hspan
  obtain ⟨-, -, hθ, -, -, -, -, hMc, -⟩ := hH
  obtain ⟨hθ1, hθ2, hθ3⟩ := hθ
  have hm0 : m ≠ 0 := by omega
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hMp : Nat.Coprime M p := Nat.Coprime.coprime_dvd_right (dvd_pow_self p hm0) hMc
  have hM0 : (M : I.E) ≠ 0 := by
    have hM : M ≠ 0 := by
      rintro rfl
      exact hp1 ((Nat.coprime_zero_left _).1 hMp)
    exact_mod_cast hM

  choose sw hsw using fun i => LA_clear (I := I) p (hw i).1
  choose sd hsd using fun i => LA_clear (I := I) p (hw i).2
  have hT0p : Nat.Coprime ((∏ i, sw i) * ∏ i, sd i) p :=
    Nat.Coprime.mul (Nat.Coprime.prod_left fun i _ => (hsw i).1)
      (Nat.Coprime.prod_left fun i _ => (hsd i).1)
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ, T = ((∏ i, sw i) * ∏ i, sd i) ^ Nat.totient (p ^ m) := ⟨_, rfl⟩
  have hTp : Nat.Coprime T p := hTdef ▸ Nat.Coprime.pow_left _ hT0p
  have hT0dvd : ((∏ i, sw i) * ∏ i, sd i) ∣ T :=
    hTdef ▸ dvd_pow_self _ (Nat.totient_pos.2 (pow_pos hp.pos m)).ne'
  have hTne : T ≠ 0 := by
    rintro h0
    rw [h0] at hTp
    exact hp1 ((Nat.coprime_zero_left _).1 hTp)
  have hTE : (T : I.E) ≠ 0 := by exact_mod_cast hTne
  have hTmod : T ≡ 1 [MOD p ^ m] := hTdef ▸ Nat.ModEq.pow_totient (Nat.Coprime.pow_right m hT0p)
  obtain ⟨c, hc⟩ : ∃ c, T = 1 + p ^ m * c := by
    have h1 : 1 ≤ T := Nat.one_le_iff_ne_zero.2 hTne
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' h1).1 hTmod.symm
    refine ⟨c, ?_⟩
    generalize p ^ m * c = q at hc ⊢
    omega
  have hT1 : QA I p (p ^ m) (1 - (T : I.E) ^ 2) := by
    apply QA_of_GE (I := I)
    refine ⟨-((c : 𝓞 I.E) + c + (p : 𝓞 I.E) ^ m * c * c), ?_⟩
    rw [hc]
    push_cast
    ring
  have hTA : (T : I.E) ^ 2 ∈ Ap I p := pow_mem (natCast_mem_Ap I p T) 2
  have hTw : ∀ i, (T : I.E) • w i ∈ I.L := by
    intro i
    obtain ⟨d, hd⟩ : sw i ∣ T := dvd_trans (dvd_trans (Finset.dvd_prod_of_mem sw (Finset.mem_univ i))
      (dvd_mul_right _ _)) hT0dvd
    rw [hd, Nat.cast_mul, mul_comm, mul_smul, natE_smul (I := I)]
    exact I.L.smul_mem _ (hsw i).2
  have hTwd : ∀ i, (T : I.E) • wd i ∈ I.L := by
    intro i
    obtain ⟨d, hd⟩ : sd i ∣ T := dvd_trans (dvd_trans (Finset.dvd_prod_of_mem sd (Finset.mem_univ i))
      (dvd_mul_left _ _)) hT0dvd
    rw [hd, Nat.cast_mul, mul_comm, mul_smul, natE_smul (I := I)]
    exact I.L.smul_mem _ (hsd i).2

  have hθ1s : GE I (p ^ m) (star (θ : I.E) * star (θ : I.E) - star (θ : I.E)) := by
    obtain ⟨t, ht⟩ := hθ1
    obtain ⟨ts, hts⟩ := isInt_star I t
    refine ⟨ts, ?_⟩
    have h := congrArg star ht
    simp only [star_sub, star_mul, star_natCast] at h
    rw [h, hts]
    ring
  obtain ⟨θs, hθs⟩ := isInt_star I θ
  obtain ⟨z, hzdef⟩ : ∃ z : Fin I.n → I.E,
      z = (T : I.E) • ((θ : I.E) • w (Fin.last k) - star (θ : I.E) • wd (Fin.last k)) := ⟨_, rfl⟩
  have hz : z ∈ I.L := by
    rw [hzdef, smul_sub, smul_comm (T : I.E) (θ : I.E), smul_comm (T : I.E) (star (θ : I.E)), ← hθs]
    exact I.L.sub_mem (I.L.smul_mem θ (hTw _)) (I.L.smul_mem θs (hTwd _))
  have hl1 : hG I (wd (Fin.last k)) (w (Fin.last k)) = 1 := by
    simpa using hwd (Fin.last k) (Fin.last k)
  have hl2 : hG I (w (Fin.last k)) (wd (Fin.last k)) = 1 := by
    rw [hG_symm (I := I) (wd (Fin.last k)) (w (Fin.last k)), hl1, star_one]
  have hl3 : ∀ i : Fin k, hG I (wd (Fin.last k)) (w i.castSucc) = 0 := by
    intro i
    rw [hwd, if_neg (Fin.castSucc_ne_last i).symm]
  have hl4 : ∀ i : Fin k, hG I (w (Fin.last k)) (wd i.castSucc) = 0 := by
    intro i
    rw [hG_symm (I := I) (wd i.castSucc) (w (Fin.last k)), hwd, if_neg (Fin.castSucc_ne_last i), star_zero]
  unfold Concl
  refine ⟨z, fun i => (T : I.E) • w i.castSucc, fun i => (T : I.E) • wd i.castSucc, hz,
    fun i => ⟨hTw _, hTwd _⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [hzdef]
    refine ⟨?_, ?_⟩ <;> rw [hG_smul_right, hG_sub_right, hG_smul_right, hG_smul_right]
    · rw [(hew a _).1, (hew a _).2.2.1]
      ring
    · rw [(hew a _).2.1, (hew a _).2.2.2]
      ring
  · intro a i
    simp [hG_smul_right, hew]
  ·
    apply GE_of_QA (I := I) p m (isInt_add I (isInt_hG I hz hz) (isInt_one I))
    have hzz : hG I z z + 1 =
        ((T : I.E) ^ 2 * (hG I (w (Fin.last k)) (w (Fin.last k)) + hG I (wd (Fin.last k)) (wd (Fin.last k))))
          * ((θ : I.E) * star (θ : I.E))
        - (T : I.E) ^ 2 * ((θ : I.E) * θ - θ)
        - (T : I.E) ^ 2 * (star (θ : I.E) * star (θ : I.E) - star (θ : I.E))
        + (T : I.E) ^ 2 * (1 - (θ : I.E) - star (θ : I.E))
        + (1 - (T : I.E) ^ 2) := by
      rw [hzdef]
      simp only [hG_smul_left, hG_smul_right, hG_sub_left, hG_sub_right, star_natCast, star_star, star_sub,
        star_smul]
      rw [hl1, hl2]
      ring
    rw [hzz]
    have hAD : (T : I.E) ^ 2 * (hG I (w (Fin.last k)) (w (Fin.last k)) + hG I (wd (Fin.last k)) (wd (Fin.last k)))
        ∈ Ap I p :=
      mul_mem hTA (add_mem (hG_mem_Ap (I := I) p (hw _).1 (hw _).1) (hG_mem_Ap (I := I) p (hw _).2 (hw _).2))
    refine QA_add (I := I) p _ (QA_add (I := I) p _ (QA_sub (I := I) p _ (QA_sub (I := I) p _
      (QA_mul (I := I) p _ hAD (QA_of_GE (I := I) p _ hθ2))
      (QA_mul (I := I) p _ hTA (QA_of_GE (I := I) p _ hθ1)))
      (QA_mul (I := I) p _ hTA (QA_of_GE (I := I) p _ hθ1s)))
      (QA_mul (I := I) p _ hTA (QA_of_GE (I := I) p _ hθ3))) hT1
  · intro i
    constructor
    · apply GE_of_QA (I := I) p m (isInt_mul I (isInt_coe I θ) (isInt_hG I hz (hTw _)))
      have h : (θ : I.E) * hG I z ((T : I.E) • w i.castSucc) =
          ((T : I.E) ^ 2 * hG I (w (Fin.last k)) (w i.castSucc)) * ((θ : I.E) * star (θ : I.E)) := by
        rw [hzdef]
        simp only [hG_smul_left, hG_smul_right, hG_sub_left, star_natCast, star_star, star_sub]
        rw [hl3]
        ring
      rw [h]
      exact QA_mul (I := I) p _ (mul_mem hTA (hG_mem_Ap (I := I) p (hw _).1 (hw _).1))
        (QA_of_GE (I := I) p _ hθ2)
    · apply GE_of_QA (I := I) p m
        (isInt_mul I (by rw [← hθs]; exact isInt_coe I θs) (isInt_hG I hz (hTwd _)))
      have h : star (θ : I.E) * hG I z ((T : I.E) • wd i.castSucc) =
          -((T : I.E) ^ 2 * hG I (wd (Fin.last k)) (wd i.castSucc)) * ((θ : I.E) * star (θ : I.E)) := by
        rw [hzdef]
        simp only [hG_smul_left, hG_smul_right, hG_sub_left, star_natCast, star_star, star_sub]
        rw [hl4]
        ring
      rw [h]
      exact QA_mul (I := I) p _ (neg_mem (mul_mem hTA (hG_mem_Ap (I := I) p (hw _).2 (hw _).2)))
        (QA_of_GE (I := I) p _ hθ2)
  · intro i j
    have h : hG I ((T : I.E) • wd i.castSucc) ((T : I.E) • w j.castSucc) =
        (T : I.E) ^ 2 * (if i = j then 1 else 0) := by
      rw [hG_smul_left, hG_smul_right, hwd, star_natCast]
      simp only [Fin.castSucc_inj]
      ring
    rw [h]
    by_cases hij : i = j
    · rw [if_pos hij, mul_one]
      apply GE_of_QA (I := I) p m
        (isInt_mul I (isInt_coe I θ) (isInt_sub I ⟨(T : 𝓞 I.E) ^ 2, by push_cast; rfl⟩ (isInt_one I)))
      have h2 : (θ : I.E) * ((T : I.E) ^ 2 - 1) = -(θ : I.E) * (1 - (T : I.E) ^ 2) := by ring
      rw [h2]
      exact QA_mul (I := I) p _ (neg_mem (int_mem_Ap (I := I) p θ)) hT1
    · rw [if_neg hij]
      exact ⟨0, by simp⟩
  · exact span_part (I := I) p m r k θ e f M T w wd hMp hM0 hTp hTE hθ1 hθ2 hθ3 hw hspan _
      (fun a => Or.inl (Or.inl (Or.inl (Or.inl ⟨a, rfl⟩))))
      (fun a => Or.inl (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩))))
      (Or.inl (Or.inl (Or.inr hzdef.symm)))
      (fun i => Or.inl (Or.inr ⟨i, rfl⟩))
      (fun i => Or.inr ⟨i, rfl⟩)

end PI.ScRefExists.PPA
