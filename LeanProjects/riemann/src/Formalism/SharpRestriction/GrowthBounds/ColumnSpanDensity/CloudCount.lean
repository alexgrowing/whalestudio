import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorsLEOfFintype

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

variable {p n' : ℕ} (R : RS p n') {m : ℕ}

theorem RS.pK_ne : (p : R.Kf) ≠ 0 := by
  obtain ⟨hS, hw, -, -⟩ := R.std
  haveI := hS.frac_O
  have hO : (p : R.O) ≠ 0 := by
    rw [← hS.w_sq]
    exact pow_ne_zero _ hw.ne_zero
  intro h
  apply hO
  apply IsFractionRing.injective R.O R.Kf
  rw [map_zero, map_natCast]
  exact h

theorem be_pull (lam mu : Fin n' → Fin (m + 1) → ℤ) (f : Vsp R.Kf lam →ₗ[R.Kf] Vsp R.Kf mu)
    (g : Module.Dual R.Kf (Vsp R.Kf mu)) (v : Vsp R.Kf lam) :
    be p 1 lam v (((p : R.Kf) ^ (Ar 1 mu - Ar 1 lam)) • (g ∘ₗ f)) = be p 1 mu (f v) g := by
  unfold be
  rw [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, ← zpow_add₀ R.pK_ne, sub_add_cancel]

theorem cloud_count (hS : LemmaSMat) (hRet : LatRetract) (hBP : BePerfect) (hD3 : DualHeightBasis)
    (H Hp lam : Fin n' → Fin (m + 1) → ℤ) (hdH : IsDominant H) (hdHp : IsDominant Hp)
    (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) (t c₂ c₃ : ℕ) (hc : c₃ ≤ c₂) (D₁ : ℝ) (hD : 0 ≤ D₁)
    (hDc : 4 * D₁ < c₂) (nb kk : ℕ) (io : Vsp R.Kf H →ₗ[R.Kf] Vsp R.Kf Hp)
    (U : Fin nb → Vsp R.Kf H →ₗ[R.Kf] Vsp R.Kf lam) (L : Fin nb → Vsp R.Kf lam →ₗ[R.Kf] Vsp R.Kf Hp)
    (ka : Fin nb → ℕ) (hka : ∀ b, ka b ≤ kk)
    (h24 : ∀ a b F, L a (U b F) = if a = b then ((p : R.Kf) ^ ka b) • io F else 0)
    (hiso : ∀ F, io F ∈ Re p R.ι R.σ R.w 1 Hp e ↔ F ∈ Re p R.ι R.σ R.w 1 H e)
    (hio : ∀ F ∈ CCL R H t c₂ e, io F ∈ CCL R Hp t c₂ e)
    (hU : ∀ b, ∀ F ∈ CCL R H t c₂ e, U b F ∈ CCL R lam t c₂ e)
    (hL : ∀ a, ∀ g ∈ CCL' R Hp t c₂ e, ((p : R.Kf) ^ (Ar 1 Hp - Ar 1 lam)) • (g ∘ₗ L a) ∈ CCL' R lam t c₃ e)
    (n1 n2 : ℕ) (f1 : FacL R H t c₂ e n1 D₁) (f2 : FacL R Hp t c₂ e n2 D₁) :
    ∃ r : ℕ, (n1 : ℝ) + n2 - dL R Hp ≤ r ∧ FacL R lam t c₃ e (nb * r) (2 * D₁ + kk) := by
  classical
  have : IsFractionRing R.O R.Kf := R.std.1.frac_O
  obtain ⟨x1, y1, z1, hx1, hy1, hz1, hv1, hG1⟩ := wit_of_factors R H hD f1
  obtain ⟨x2, y2, z2, hx2, hy2, hz2, hv2, hG2⟩ := wit_of_factors R Hp hD f2
  have hw0 := R.w_ne

  obtain ⟨bH, πH, -, -, -, -, hReH, -⟩ :=
    hD3 p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 H hdH e he
  obtain ⟨bP, πP, -, -, -, -, hReP, -⟩ :=
    hD3 p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 Hp hdHp e he
  let cH := bH.isUnitSMul (w := fun i => algebraMap R.O R.Kf R.w ^ (-order 1 H (πH i)))
    (fun i => (zpow_ne_zero _ hw0).isUnit)
  let cP := bP.isUnitSMul (w := fun i => algebraMap R.O R.Kf R.w ^ (-order 1 Hp (πP i)))
    (fun i => (zpow_ne_zero _ hw0).isUnit)
  have hcH : Submodule.span R.O (Set.range cH) = Re p R.ι R.σ R.w 1 H e := by
    rw [← hReH]
    congr 2
    funext i
    exact Module.Basis.isUnitSMul_apply _ _
  have hcP : Submodule.span R.O (Set.range cP) = Re p R.ι R.σ R.w 1 Hp e := by
    rw [← hReP]
    congr 2
    funext i
    exact Module.Basis.isUnitSMul_apply _ _
  obtain ⟨ret, hret1, hret2⟩ := hRet R.O R.Kf _ _ _ _ cH cP io (by intro F; rw [hcH, hcP]; exact hiso F)
  rw [hcH, hcP] at hret2

  let tt : Fin n1 → Module.Dual R.Kf (Vsp R.Kf Hp) := fun l => ((p : R.Kf) ^ (Ar 1 H - Ar 1 Hp)) • (y1 l ∘ₗ ret)
  have htt : ∀ F l, be p 1 Hp F (tt l) = be p 1 H (ret F) (y1 l) := fun F l => be_pull R Hp H ret (y1 l) F
  have httm : ∀ l, tt l ∈ Re' p R.ι R.σ R.w 1 Hp e := fun l =>
    ((hBP p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 Hp hdHp e he).1 (tt l)).2 fun F hF => by
      rw [htt]
      obtain ⟨b, hb⟩ := be_Re R H e (hret2 F hF) (hy1 l).1.2
      exact ⟨b, hb.symm⟩
  have hGt : ∀ k k', be p 1 Hp (io (x1 k)) (tt k') =
      algebraMap R.O R.Kf ((z1 • (1 : Matrix (Fin n1) (Fin n1) R.O)) k k') := by
    intro k k'
    rw [htt, hret1, hG1, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hNint : ∀ i b, ∃ g : R.O, be p 1 Hp (io (x1 i)) (y2 b) = algebraMap R.O R.Kf g :=
    fun i b => be_Re R Hp e (hio _ (hx1 i)).1.2 (hy2 b).1.2
  choose Nm hNm using hNint
  have hBint : ∀ a l, ∃ g : R.O, be p 1 Hp (x2 a) (tt l) = algebraMap R.O R.Kf g :=
    fun a l => be_Re R Hp e (hx2 a).1.2 (httm l)
  choose Bm hBm using hBint
  obtain ⟨r, s, hrs, ⟨P, Q, hPQ⟩, ⟨P', P'', M, hPP, hblk⟩⟩ :=
    hS R.O n1 n2 z1 z2 hz1 hz2 (Matrix.of Nm) (Matrix.of Bm)
  have hz12 : z1 * z2 ≠ 0 := mul_ne_zero hz1 hz2
  have hv12 : vLEO p (z1 * z2) (2 * D₁) := by
    have := vLEO_mul hz1 hz2 hv1 hv2
    rwa [← two_mul] at this

  let Xb : Fin s ⊕ Fin n2 → Vsp R.Kf Hp :=
    Sum.elim (fun i => ∑ k, algebraMap R.O R.Kf (P' i k) • io (x1 k)) x2
  let Yb : Fin s ⊕ Fin n2 → Module.Dual R.Kf (Vsp R.Kf Hp) := Sum.elim (fun l => ∑ k, P'' k l • tt k) y2
  have hXb : ∀ i, Xb i ∈ CCL R Hp t c₂ e := by
    rintro (i | a)
    · refine Submodule.sum_mem _ fun k _ => ?_
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ _ (hio _ (hx1 k))
    · exact hx2 a
  have hYb : ∀ i, Yb i ∈ Re' p R.ι R.σ R.w 1 Hp e := by
    rintro (l | b)
    · exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (httm k)
    · exact (hy2 b).1.2
  have hGb : ∀ i j, be p 1 Hp (Xb i) (Yb j) = algebraMap R.O R.Kf
      (Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) R.O)) (P' * Matrix.of Nm) (Matrix.of Bm * P'')
        (z2 • (1 : Matrix (Fin n2) (Fin n2) R.O)) i j) := by
    rintro (i | a) (l | b)
    · show be p 1 Hp (∑ k, algebraMap R.O R.Kf (P' i k) • io (x1 k)) (∑ k, P'' k l • tt k) = _
      rw [be_mat R Hp (fun k => io (x1 k)) tt _ hGt P' P'' i l, Matrix.fromBlocks_apply₁₁]
      congr 1
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP]
    · show be p 1 Hp (∑ k, algebraMap R.O R.Kf (P' i k) • io (x1 k)) (y2 b) = _
      rw [be_sum_left, Matrix.fromBlocks_apply₁₂, Matrix.mul_apply, map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hNm, map_mul, Matrix.of_apply]
    · show be p 1 Hp (x2 a) (∑ k, P'' k l • tt k) = _
      rw [be_sum, Matrix.fromBlocks_apply₂₁, Matrix.mul_apply, map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hBm, map_mul, Matrix.of_apply]
    · show be p 1 Hp (x2 a) (y2 b) = _
      rw [hG2, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
  have hbadF : FactorsLE p (be (Kf := R.Kf) p 1 Hp) (CCL R Hp t c₂ e) (Re' p R.ι R.σ R.w 1 Hp e)
      (Fintype.card (Fin s ⊕ Fin n2)) (2 * D₁) := by
    refine factorsLE_of_fintype p _ _ _ Xb (fun j => ∑ l, M l j • Yb l) hXb
      (fun j => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hYb l)) (z1 * z2) hz12 hv12 fun i j => ?_
    rw [be_sum]
    have : ∑ l, be p 1 Hp (Xb i) (Yb l) * algebraMap R.O R.Kf (M l j) = algebraMap R.O R.Kf
        ((Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) R.O)) (P' * Matrix.of Nm) (Matrix.of Bm * P'')
          (z2 • (1 : Matrix (Fin n2) (Fin n2) R.O)) * M) i j) := by
      rw [Matrix.mul_apply, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [hGb, map_mul]
    rw [this, hblk, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hbad : ((s + n2 : ℕ) : ℝ) ≤ dL R Hp := by
    have hcard : Fintype.card (Fin s ⊕ Fin n2) = s + n2 := by simp
    rw [hcard] at hbadF
    exact nLeD R Hp hdHp t c₂ (s + n2) (2 * D₁) (by linarith) (by linarith) e he hbadF

  refine ⟨r, ?_, ?_⟩
  · have h1 : ((r + s : ℕ) : ℝ) = n1 := by exact_mod_cast hrs
    push_cast at h1 hbad
    linarith
  let Fg : Fin r → Vsp R.Kf H := fun i => ∑ k, algebraMap R.O R.Kf (P i k) • x1 k
  let gg : Fin r → Module.Dual R.Kf (Vsp R.Kf Hp) := fun j => ∑ b, Q b j • y2 b
  have hFg : ∀ i, Fg i ∈ CCL R H t c₂ e := fun i => by
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (hx1 k)
  have hgg : ∀ j, gg j ∈ CCL' R Hp t c₂ e := fun j =>
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hy2 b)
  have hFgg : ∀ i j, be p 1 Hp (io (Fg i)) (gg j) = if i = j then algebraMap R.O R.Kf (z1 * z2) else 0 := by
    intro i j
    have e1 : io (Fg i) = ∑ k, algebraMap R.O R.Kf (P i k) • io (x1 k) := by
      simp only [Fg, map_sum, map_smul]
    rw [e1, be_mat R Hp (fun k => io (x1 k)) y2 (Matrix.of Nm) (fun k k' => hNm k k') P Q i j, hPQ,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hcardg : Fintype.card (Fin nb × Fin r) = nb * r := by simp
  rw [← hcardg]
  refine factorsLE_of_fintype p _ _ _ (fun x : Fin nb × Fin r => U x.1 (Fg x.2))
    (fun y : Fin nb × Fin r => ((p : R.O) ^ (kk - ka y.1)) •
      (((p : R.Kf) ^ (Ar 1 Hp - Ar 1 lam)) • (gg y.2 ∘ₗ L y.1)))
    (fun x => CCL_anti_c R lam hc t e (hU x.1 _ (hFg x.2)))
    (fun y => Submodule.smul_mem _ _ (hL y.1 _ (hgg y.2)))
    ((p : R.O) ^ kk * (z1 * z2)) (mul_ne_zero (pow_ne_zero _ R.p_ne) hz12)
    (vLEO_pow_mul R.p_ne R.p_not_unit hz12 kk hv12) ?_
  rintro ⟨b, i⟩ ⟨a, j⟩
  show be p 1 lam (U b (Fg i)) (((p : R.O) ^ (kk - ka a)) •
      (((p : R.Kf) ^ (Ar 1 Hp - Ar 1 lam)) • (gg j ∘ₗ L a))) = _
  rw [be_smul, be_pull, h24]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, be_smulK_left, hFgg]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
      simp only [map_mul, map_pow, map_natCast]
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hka a)]
    · have : ((a, i) : Fin nb × Fin r) ≠ (a, j) := fun h => hij (Prod.mk.inj h).2
      rw [if_neg hij, if_neg this, mul_zero, mul_zero]
  · have : ((b, i) : Fin nb × Fin r) ≠ (a, j) := fun h => hab (Prod.mk.inj h).1.symm
    rw [if_neg hab, if_neg this]
    simp [be]

end Formalism.MainNotions.flipOneThree.Pf

end
