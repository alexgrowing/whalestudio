import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AbsProdSubProdSubLinLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.LengthLocQuotEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem natCast_mem_of_charOf (W : Ideal (MRing ι)) : ((charOf W : ℕ) : MRing ι) ∈ W := by
  show (((Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs : ℕ) : MRing ι) ∈ W
  have hg := Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing ι))
  have hn : (((Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs : ℕ) : ℤ) ∈
      W.comap (C : ℤ →+* MRing ι) := by
    obtain ⟨u, hu⟩ : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) ∣
        ((Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs : ℤ) :=
      Int.dvd_natAbs.2 dvd_rfl
    rw [hu]
    exact Ideal.mul_mem_right u _ hg
  have h := Ideal.mem_comap.1 hn
  rwa [map_natCast] at h

theorem charOf_ne_zero_of_mem {W : Ideal (MRing ι)} {p : ℕ} (hp : p ≠ 0)
    (hpW : (p : MRing ι) ∈ W) : charOf W ≠ 0 := by
  intro h0
  have hp' : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, map_natCast]; exact hpW
  have hg0 : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) = 0 := Int.natAbs_eq_zero.1 h0
  obtain ⟨s, hs⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator _).1 hp'
  rw [hg0, smul_zero] at hs
  exact hp (by exact_mod_cast hs)

theorem charOf_eq_of_mem {W : Ideal (MRing ι)} (hW : W.IsPrime) {p : ℕ} (hp : p.Prime)
    (hpW : (p : MRing ι) ∈ W) : charOf W = p := by
  have hp' : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, map_natCast]; exact hpW
  have hdvd := (Submodule.IsPrincipal.mem_iff_generator_dvd _).1 hp'
  have hd : charOf W ∣ p := Int.natAbs_dvd_natAbs.2 hdvd
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h1
  · exfalso
    have hu : IsUnit (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))) :=
      Int.isUnit_iff_natAbs_eq.2 h1
    have h1m : (1 : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) :=
      (Submodule.IsPrincipal.mem_iff_generator_dvd _).2 hu.dvd
    rw [Ideal.mem_comap, map_one] at h1m
    exact hW.ne_top ((Ideal.eq_top_iff_one _).2 h1m)
  · exact h1

theorem isMultiHomogIdeal_chain {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)} {f : Fin N → MRing ι}
    {c : Fin N → K → ℕ} (h0 : IsMultiHomogIdeal (F 0))
    (hj : ∀ j : Fin N, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j}) :
    ∀ j : Fin (N + 1), IsMultiHomogIdeal (F j) := by
  intro j
  induction j using Fin.induction with
  | zero => exact h0
  | succ i ih =>
    obtain ⟨S, hS, hSe⟩ := ih
    refine ⟨S ∪ {f i}, ?_, ?_⟩
    · rintro g (hg | hg)
      · exact hS g hg
      · rw [Set.mem_singleton_iff.1 hg]; exact ⟨c i, (hj i).1⟩
    · rw [(hj i).2, hSe, Ideal.span_union]

theorem le_chain {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)} {f : Fin N → MRing ι}
    (hj : ∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j}) :
    ∀ j : Fin (N + 1), F 0 ≤ F j := by
  intro j
  induction j using Fin.induction with
  | zero => exact le_rfl
  | succ i ih => rw [hj i]; exact ih.trans le_sup_left

theorem card_mPiece_top (a : K → ℕ) : Nat.card (mPiece (⊤ : Ideal (MRing ι)) a) = 1 := by
  have : Subsingleton (MRing ι ⧸ (⊤ : Ideal (MRing ι))) := Ideal.Quotient.subsingleton_iff.2 rfl
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨0⟩⟩

theorem card_mPiece_chain (a : K → ℕ) : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι))
    (f : Fin N → MRing ι) (c : Fin N → K → ℕ) (q : Fin N → Ideal (MRing ι)),
    IsMultiHomogIdeal (F 0) → F (Fin.last N) = ⊤ →
    (∀ j : Fin N, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    (∀ j k, c j k ≤ a k) →
    Nat.card (mPiece (F 0) a) = ∏ j, Nat.card (mPiece (q j) (a - c j))
  | 0, F, f, c, q, _, hlast, _, _ => by
    have : F 0 = ⊤ := hlast
    rw [this, card_mPiece_top, Fin.prod_univ_zero]
  | N + 1, F, f, c, q, h0, hlast, hj, ha => by
    have ih := card_mPiece_chain a N (fun j => F j.succ) (fun j => f j.succ) (fun j => c j.succ)
      (fun j => q j.succ)
      (isMultiHomogIdeal_chain h0 (fun j => ⟨(hj j).1, (hj j).2.1⟩) 1)
      (by simpa [Fin.succ_last] using hlast)
      (fun j => by
        have h := hj j.succ
        rwa [← Fin.succ_castSucc] at h)
      (fun j => ha j.succ)
    obtain ⟨h1, h2, h3⟩ := hj 0
    rw [Fin.castSucc_zero] at h2 h3
    rw [card_mPiece_step h0 h1 h3 (ha 0), ← h2, Fin.prod_univ_succ, mul_comm]
    rw [ih]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
