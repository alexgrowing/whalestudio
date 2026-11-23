import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImEmbHermSelf

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

namespace GlobalTheory.OrthoFrame.GramSchmidt

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_sum_left (G : Matrix (Fin r) (Fin r) E) (s : Finset (Fin r)) (f : Fin r → E)
    (w : Fin r → Fin r → E) (y : Fin r → E) :
    herm G (∑ j ∈ s, f j • w j) y = ∑ j ∈ s, f j * herm G (w j) y := by
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, ih]

theorem psi_nonempty (X : Data E r) : ∃ τ, τ ∈ X.Ψ := by
  let τ0 : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  by_cases h : τ0 ∈ X.Ψ
  · exact ⟨τ0, h⟩
  · exact ⟨_, not_not.mp (mt (X.cmType τ0).2 h)⟩

theorem dmin_frm_of_lt (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (u : Fin r → Fin r → E) (i : Fin (r + 1))
    (ho : ∀ j k : Fin r, (j : ℕ) < i → (k : ℕ) < i → j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) :
    dmin G (frm Ψ u) τ i = ∏ k : Fin i, τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
      (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))) := by
  unfold dmin lminor
  have : (gram τ.1 G (mat (frm Ψ u) τ)).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = Matrix.diagonal (fun k => τ.1 (herm G
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))) := by
    ext a b
    simp only [Matrix.submatrix_apply, gram, Matrix.of_apply, col_frm, hermC_emb, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · rw [ho _ _ (by rw [Fin.coe_castLE]; exact a.isLt) (by rw [Fin.coe_castLE]; exact b.isLt)
        (fun e => h (Fin.castLE_injective _ e)), map_zero]
  rw [this, Matrix.det_diagonal]

theorem herm_self_ne (X : Data E r) (v : Fin r → Fin r → E) (hv : frm X.Ψ v ∈ X.dom) (m : ℕ)
    (ho : ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0)
    (j : Fin r) (hj : (j : ℕ) < m) : herm X.Gm (v j) (v j) ≠ 0 := by
  obtain ⟨τ, hτ⟩ := psi_nonempty X
  have h1 := (hv ⟨τ, hτ⟩).2 j.succ
  have hd : dmin X.Gm (frm X.Ψ v) ⟨τ, hτ⟩ j.succ ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re, mul_zero] at h1
    exact lt_irrefl _ h1
  rw [dmin_frm_of_lt X.Ψ X.Gm v j.succ (fun a b ha hb hab => ho a b
    (by simp only [Fin.val_succ] at ha; omega) (by simp only [Fin.val_succ] at hb; omega) hab)] at hd
  have hf := Finset.prod_ne_zero_iff.mp hd ⟨j, by simp⟩ (Finset.mem_univ _)
  have he : (Fin.castLE (Nat.le_of_lt_succ j.succ.isLt) ⟨(j : ℕ), by simp⟩ : Fin r) = j := Fin.ext rfl
  rw [he] at hf
  intro h0
  exact hf (by rw [h0, map_zero])

def gsMat (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    Matrix (Fin r) (Fin r) E :=
  fun j a => (if j = a then 1 else 0) -
    (if a = m ∧ j < m then herm G (v m) (v j) / herm G (v j) (v j) else 0)

def gsStep (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    Fin r → Fin r → E :=
  fun a k => ∑ j, v j k * gsMat G v m j a

theorem gsStep_ne (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m a : Fin r)
    (h : a ≠ m) : gsStep G v m a = v a := by
  funext k
  simp [gsStep, gsMat, h]

theorem gsStep_self (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    gsStep G v m m = v m - ∑ j, (if j < m then herm G (v m) (v j) / herm G (v j) (v j) else 0) • v j := by
  funext k
  simp only [gsStep, gsMat, true_and, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem frm_gsStep (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E)
    (m : Fin r) : frm Ψ (gsStep G v m) = rmul (frm Ψ v) (fun τ j a => τ.1 (gsMat G v m j a)) := by
  funext τ k a
  simp [frm, rmul, mat, Matrix.mul_apply, gsStep, map_sum, map_mul]

theorem gsB_mem (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E)
    (m : Fin r) : (fun (τ : Ψ) j a => τ.1 (gsMat G v m j a)) ∈ Bor Ψ r := by
  have hlow : ∀ a c : Fin r, c < a → gsMat G v m a c = 0 := by
    intro a c hca
    have h1 : a ≠ c := fun h => lt_irrefl _ (h ▸ hca)
    have h2 : ¬ (c = m ∧ a < m) := fun h => lt_asymm hca (h.1 ▸ h.2)
    simp [gsMat, h1, h2]
  intro τ
  refine ⟨?_, fun a c hca => by simp [hlow a c hca]⟩
  have ht : (mat (fun (τ : Ψ) j a => τ.1 (gsMat G v m j a)) τ).BlockTriangular id := by
    intro a c hca
    simp [mat, hlow a c hca]
  rw [Matrix.det_of_upperTriangular ht]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  have hn : ¬ (a = m ∧ a < m) := by rintro ⟨rfl, h⟩; exact lt_irrefl _ h
  simp [mat, gsMat, hn]

theorem herm_gsStep_self (X : Data E r) (v : Fin r → Fin r → E) (hv : frm X.Ψ v ∈ X.dom) (m : Fin r)
    (ho : ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0)
    (k : Fin r) (hk : k < m) : herm X.Gm (gsStep X.Gm v m m) (v k) = 0 := by
  have hkm : (k : ℕ) < m := hk
  have hne := herm_self_ne X v hv m ho k hkm
  rw [gsStep_self, HermitianTraceFormVanishing.herm_sub_left, herm_sum_left,
    Finset.sum_eq_single k (fun i _ hik => ?_) (fun h => absurd (Finset.mem_univ k) h),
    if_pos hk, div_mul_cancel₀ _ hne, sub_self]
  split_ifs with him
  · rw [ho i k him hkm hik, mul_zero]
  · rw [zero_mul]

theorem exists_ortho_lt (X : Data E r) (u : Fin r → Fin r → E) (hu : frm X.Ψ u ∈ X.dom) :
    ∀ m ≤ r, ∃ v : Fin r → Fin r → E, frm X.Ψ v ∈ X.dom ∧
      ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0 := by
  intro m
  induction m with
  | zero => intro _; exact ⟨u, hu, fun j k hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨v, hv, ho⟩ := ih (Nat.le_of_succ_le hm)
    let mf : Fin r := ⟨m, hm⟩
    refine ⟨gsStep X.Gm v mf, ?_, ?_⟩
    · rw [frm_gsStep]
      exact OrthogonalFrameDomain.rmul_mem_dom X hv (gsB_mem X.Ψ X.Gm v mf)
    · intro j k hj hk hjk
      by_cases hjm : j = mf
      · have hkm : k ≠ mf := fun h => hjk (hjm.trans h.symm)
        have hk' : k < mf := by
          rw [Fin.lt_iff_val_lt_val]
          have : (k : ℕ) ≠ m := fun h => hkm (Fin.ext h)
          show (k : ℕ) < m
          omega
        rw [hjm, gsStep_ne X.Gm v mf k hkm]
        exact herm_gsStep_self X v hv mf ho k hk'
      · by_cases hkm : k = mf
        · have hj' : j < mf := by
            rw [Fin.lt_iff_val_lt_val]
            have : (j : ℕ) ≠ m := fun h => hjm (Fin.ext h)
            show (j : ℕ) < m
            omega
          rw [hkm, gsStep_ne X.Gm v mf j hjm, ← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm,
            herm_gsStep_self X v hv mf ho j hj', HermitianTraceFormVanishing.cc_zero]
        · rw [gsStep_ne X.Gm v mf j hjm, gsStep_ne X.Gm v mf k hkm]
          have hj' : (j : ℕ) ≠ m := fun h => hjm (Fin.ext h)
          have hk' : (k : ℕ) ≠ m := fun h => hkm (Fin.ext h)
          exact ho j k (by omega) (by omega) hjk

theorem exists_ortho_frm (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (u : Fin r → Fin r → E) :
    GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom → ∃ v : Fin r → Fin r → E,
      (∀ j k, j ≠ k → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v k) = 0) ∧ GlobalTheory.OrthoFrame.frm X.Ψ v ∈ X.dom := by
  intro hu
  obtain ⟨v, hv, ho⟩ := exists_ortho_lt X u hu r le_rfl
  exact ⟨v, fun j k hjk => ho j k j.isLt k.isLt hjk, hv⟩

end

end GlobalTheory.OrthoFrame.GramSchmidt
