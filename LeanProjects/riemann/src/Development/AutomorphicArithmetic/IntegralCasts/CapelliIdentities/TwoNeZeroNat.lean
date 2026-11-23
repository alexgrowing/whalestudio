import Mathlib

noncomputable def UpperTheory.Reformulated.B.hecke_existence.HasChar :
    ℕ → {M : ℕ} → DirichletCharacter ℂ M → (UpperHalfPlane → ℂ) → Prop :=
    fun (k : ℕ) {M : ℕ} (χ : DirichletCharacter ℂ M) (f : UpperHalfPlane → ℂ) ↦
      ∀ γ ∈ CongruenceSubgroup.Gamma0 M,
        SlashAction.map (↑k : ℤ) γ f =
          (χ : ZMod M → ℂ) (↑((↑γ : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) ℤ) (1 : Fin (2 : ℕ)) (1 : Fin (2 : ℕ))) : ZMod M) • f

noncomputable def UpperTheory.Reformulated.B.hecke_existence.coef :
    (UpperHalfPlane → ℂ) → ℕ → ℂ :=
    fun (f : UpperHalfPlane → ℂ) (n : ℕ) ↦ (PowerSeries.coeff n : PowerSeries ℂ → ℂ) (UpperHalfPlane.qExpansion (1 : ℝ) f)

noncomputable def UpperTheory.Reformulated.B.hecke_existence.HeckeEx :
    Prop :=
    ∀ (N k : ℕ) [NeZero N],
      (1 : ℕ) ≤ k →
        ∀ (χ : DirichletCharacter ℂ N)
          (f : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 N)) (↑k : ℤ)),
          UpperTheory.Reformulated.B.hecke_existence.HasChar k χ (⇑f : UpperHalfPlane → ℂ) →
            ∀ (p : ℕ),
              Nat.Prime p →
                ∃ (g : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 N)) (↑k : ℤ)),
                  UpperTheory.Reformulated.B.hecke_existence.HasChar k χ (⇑g : UpperHalfPlane → ℂ) ∧
                    ∀ (n : ℕ),
                      (1 : ℕ) ≤ n →
                        UpperTheory.Reformulated.B.hecke_existence.coef (⇑g : UpperHalfPlane → ℂ) n =
                          UpperTheory.Reformulated.B.hecke_existence.coef (⇑f : UpperHalfPlane → ℂ) (p * n) +
                            (χ : ZMod N → ℂ) (↑p : ZMod N) * (↑p : ℂ) ^ (k - (1 : ℕ)) *
                              if p ∣ n then UpperTheory.Reformulated.B.hecke_existence.coef (⇑f : UpperHalfPlane → ℂ) (n / p) else (0 : ℂ)

namespace UpperTheory.Reformulated.B.hecke_existence

open UpperHalfPlane Matrix Matrix.SpecialLinearGroup OnePoint
open scoped MatrixGroups ModularForm

private noncomputable def matU (p : ℕ) [NeZero p] (j : ℤ) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![1, (j : ℝ); 0, (p : ℝ)]
    (by simp [det_fin_two, NeZero.ne p])

private noncomputable def matV (p : ℕ) [NeZero p] : GL (Fin 2) ℝ :=
  GeneralLinearGroup.mkOfDetNeZero !![(p : ℝ), 0; 0, 1]
    (by simp [det_fin_two, NeZero.ne p])

private lemma matU_val (p : ℕ) [NeZero p] (j : ℤ) :
    (matU p j : Matrix (Fin 2) (Fin 2) ℝ) = !![1, (j : ℝ); 0, (p : ℝ)] := rfl

private lemma matV_val (p : ℕ) [NeZero p] :
    (matV p : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, 1] := rfl

private lemma matU_det (p : ℕ) [NeZero p] (j : ℤ) : (matU p j).det.val = p := by
  simp [matU_val, det_fin_two]

private lemma matV_det (p : ℕ) [NeZero p] : (matV p).det.val = p := by
  simp [matV_val, det_fin_two]

private lemma smul_slash_pos (k : ℤ) (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (f : ℍ → ℂ) (c : ℂ) :
    (c • f) ∣[k] g = c • f ∣[k] g := by
  rw [ModularForm.smul_slash, σ, if_pos hg]
  rfl

private lemma slash_factor {N k : ℕ} {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ}
    (hf : HasChar k χ f) (a b c d : ℤ) (hdet : a * d - b * c = 1) (hc : (c : ZMod N) = 0)
    (g h : GL (Fin 2) ℝ) (hh : 0 < h.det.val)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; c, d] * (h : Matrix (Fin 2) (Fin 2) ℝ)) :
    f ∣[(k : ℤ)] g = χ d • f ∣[(k : ℤ)] h := by
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by simpa [det_fin_two] using hdet⟩
  have hγ : γ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    exact hc
  have e : g = mapGL ℝ γ * h := by
    ext1
    rw [hg, Units.val_mul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have := hf γ hγ
  rw [e, SlashAction.slash_mul, ← smul_slash_pos _ _ hh]
  congr 1

private lemma slash_eq_U {N k p : ℕ} [NeZero p] {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ}
    (hf : HasChar k χ f) (a b c d : ℤ) (hdet : a * d - b * c = p) (hc : (c : ZMod N) = 0)
    (g : GL (Fin 2) ℝ) (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; c, d])
    (j : ℤ) (h1 : (p : ℤ) ∣ b - a * j) (h2 : (p : ℤ) ∣ d - c * j) :
    χ a • f ∣[(k : ℤ)] g = f ∣[(k : ℤ)] (matU p j) := by
  obtain ⟨b', hb⟩ := h1
  obtain ⟨d', hd⟩ := h2
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne p
  obtain rfl : b = a * j + p * b' := by linarith
  obtain rfl : d = c * j + p * d' := by linarith
  have hdet' : a * d' - b' * c = 1 := by
    apply mul_left_cancel₀ hp
    linear_combination hdet
  rw [slash_factor hf a b' c d' hdet' hc g (matU p j)
    (by rw [matU_det]; exact_mod_cast NeZero.pos p), smul_smul, ← map_mul]
  · have : (a : ZMod N) * d' = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod N) hdet'
      push_cast at this
      rw [hc] at this
      linear_combination this
    rw [this, map_one, one_smul]
  · rw [hg, matU_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma slash_eq_V {N k p : ℕ} [NeZero N] [NeZero p] (hp : p.Prime)
    {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ}
    (hf : HasChar k χ f) (a b c d : ℤ) (hdet : a * d - b * c = p) (hc : (c : ZMod N) = 0)
    (g : GL (Fin 2) ℝ) (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; c, d])
    (h1 : (p : ℤ) ∣ a) (h2 : (p : ℤ) ∣ c) :
    χ a • f ∣[(k : ℤ)] g = χ p • f ∣[(k : ℤ)] (matV p) := by
  obtain ⟨a, rfl⟩ := h1
  obtain ⟨c, rfl⟩ := h2
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne p
  by_cases hu : IsUnit (p : ZMod N)
  · have hdet' : a * d - b * c = 1 := by
      apply mul_left_cancel₀ hp0
      linear_combination hdet
    have hc' : (c : ZMod N) = 0 := by
      push_cast at hc
      exact (hu.mul_right_eq_zero).mp hc
    rw [slash_factor hf a b c d hdet' hc' g (matV p)
      (by rw [matV_det]; exact_mod_cast NeZero.pos p), smul_smul, ← map_mul]
    · have : ((p * a : ℤ) : ZMod N) * d = p := by
        have := congrArg (Int.cast : ℤ → ZMod N) hdet'
        push_cast at this ⊢
        rw [hc'] at this
        linear_combination (p : ZMod N) * this
      rw [this]
    · rw [hg, matV_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · have h0 : χ p = 0 := χ.map_nonunit hu
    push_cast
    rw [map_mul, h0, zero_mul, zero_smul, zero_smul]

private noncomputable def term {N : ℕ} (k p : ℕ) [NeZero p] (χ : DirichletCharacter ℂ N)
    (f : ℍ → ℂ) (x : OnePoint (ZMod p)) : ℍ → ℂ :=
  x.elim (χ p • f ∣[(k : ℤ)] (matV p)) (fun i ↦ f ∣[(k : ℤ)] (matU p (-(i.val : ℤ))))

private def Kills {p : ℕ} (a b c d : ZMod p) (x : OnePoint (ZMod p)) : Prop :=
  x.elim (a = 0 ∧ c = 0) (fun i ↦ a * i + b = 0 ∧ c * i + d = 0)

private lemma slash_eq_term {N k p : ℕ} [NeZero N] [NeZero p] (hp : p.Prime)
    {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ}
    (hf : HasChar k χ f) (a b c d : ℤ) (hdet : a * d - b * c = p) (hc : (c : ZMod N) = 0)
    (g : GL (Fin 2) ℝ) (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; c, d])
    (x : OnePoint (ZMod p)) (hx : Kills (a : ZMod p) b c d x) :
    χ a • f ∣[(k : ℤ)] g = term k p χ f x := by
  cases x with
  | infty =>
    obtain ⟨h1, h2⟩ := hx
    exact slash_eq_V hp hf a b c d hdet hc g hg
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2)
  | coe i =>
    obtain ⟨h1, h2⟩ := hx
    refine slash_eq_U hf a b c d hdet hc g hg _ ?_ ?_
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val]
      linear_combination h1
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val]
      linear_combination h2

private lemma term_slash {N k p : ℕ} [NeZero N] [hp : Fact p.Prime]
    {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ}
    (hf : HasChar k χ f) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (x : OnePoint (ZMod p)) :
    (term k p χ f (mapGL (ZMod p) γ • x)) ∣[(k : ℤ)] γ = χ (γ 1 1) • term k p χ f x := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    rw [← det_fin_two]; exact γ.det_coe
  have had : (γ 0 0 : ZMod N) * γ 1 1 = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at this
    rw [hγ] at this
    linear_combination this
  have hV : Kills ((p * γ 0 0 : ℤ) : ZMod p) (p * γ 0 1 : ℤ) (γ 1 0) (γ 1 1) x →
      (term k p χ f ∞) ∣[(k : ℤ)] γ = χ (γ 1 1) • term k p χ f x := by
    intro hx
    rw [← slash_eq_term hp.out hf _ _ _ _ (by linear_combination (p : ℤ) * hdet) hγ
      (matV p * mapGL ℝ γ) _ x hx]
    · rw [smul_smul, ← map_mul, SlashAction.slash_mul]
      have : (γ 1 1 : ZMod N) * (p * γ 0 0 : ℤ) = p := by
        push_cast
        linear_combination (p : ZMod N) * had
      rw [this]
      exact ModularForm.SL_smul_slash _ _ _ _
    · rw [Units.val_mul, matV_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hU : ∀ y : ZMod p, Kills ((γ 0 0 - y.val * γ 1 0 : ℤ) : ZMod p)
      (γ 0 1 - y.val * γ 1 1 : ℤ) (p * γ 1 0 : ℤ) (p * γ 1 1 : ℤ) x →
      (term k p χ f y) ∣[(k : ℤ)] γ = χ (γ 1 1) • term k p χ f x := by
    intro y hx
    rw [← slash_eq_term hp.out hf _ _ _ _ (by linear_combination (p : ℤ) * hdet)
      (by push_cast; rw [hγ, mul_zero])
      (matU p (-(y.val : ℤ)) * mapGL ℝ γ) _ x hx]
    · rw [smul_smul, ← map_mul, SlashAction.slash_mul]
      have : (γ 1 1 : ZMod N) * (γ 0 0 - y.val * γ 1 0 : ℤ) = 1 := by
        push_cast
        rw [hγ]
        linear_combination had
      rw [this, map_one, one_smul]
      rfl
    · rw [Units.val_mul, matU_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hent : ∀ i j, (mapGL (ZMod p) γ) i j = (γ i j : ZMod p) := fun i j ↦ rfl
  cases x with
  | infty =>
    rw [smul_infty_eq_ite]
    simp only [hent]
    split_ifs with h
    · exact hV ⟨by simp, h⟩
    · refine hU _ ⟨?_, by simp⟩
      push_cast
      rw [ZMod.natCast_zmod_val]
      field_simp
      ring
  | coe i =>
    rw [smul_some_eq_ite]
    simp only [hent]
    split_ifs with h
    · exact hV ⟨by simp, h⟩
    · refine hU _ ⟨?_, by simp⟩
      push_cast
      rw [ZMod.natCast_zmod_val]
      linear_combination (-1 : ZMod p) * div_mul_cancel₀ ((γ 0 0 : ZMod p) * i + γ 0 1) h

private lemma sum_hasChar {N k p : ℕ} [NeZero N] [Fact p.Prime]
    {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ} (hf : HasChar k χ f) :
    HasChar k χ (∑ x, term k p χ f x) := by
  intro γ hγ
  rw [← Equiv.sum_comp (MulAction.toPerm (mapGL (ZMod p) γ)), SlashAction.sum_slash,
    Equiv.sum_comp (MulAction.toPerm (mapGL (ZMod p) γ)), Finset.smul_sum]
  exact Finset.sum_congr rfl fun x _ ↦ term_slash hf γ hγ x

private lemma isCusp_smul {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {c : OnePoint ℝ}
    (hc : IsCusp c Γ) (g : GL (Fin 2) ℝ) (g' : GL (Fin 2) ℚ) (hg : g = g'.map (Rat.castHom ℝ)) :
    IsCusp (g • c) Γ := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  exact ⟨g' • c, by rw [hg, ← Rat.coe_castHom, OnePoint.map_smul]⟩

private lemma isCusp_U {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {c : OnePoint ℝ}
    (hc : IsCusp c Γ) (p : ℕ) [NeZero p] (j : ℤ) : IsCusp (matU p j • c) Γ := by
  refine isCusp_smul hc _ (GeneralLinearGroup.mkOfDetNeZero !![1, (j : ℚ); 0, (p : ℚ)]
    (by simp [det_fin_two, NeZero.ne p])) ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matU_val]

private lemma isCusp_V {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {c : OnePoint ℝ}
    (hc : IsCusp c Γ) (p : ℕ) [NeZero p] : IsCusp (matV p • c) Γ := by
  refine isCusp_smul hc _ (GeneralLinearGroup.mkOfDetNeZero !![(p : ℚ), 0; 0, 1]
    (by simp [det_fin_two, NeZero.ne p])) ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matV_val]

private lemma isZeroAt_smul {c : OnePoint ℝ} {f : ℍ → ℂ} {k : ℤ} (h : c.IsZeroAt f k) (a : ℂ) :
    c.IsZeroAt (a • f) k := by
  intro g hg
  rw [ModularForm.smul_slash]
  exact (h g hg).smul _

private lemma isZeroAt_sum {ι : Type*} (s : Finset ι) {c : OnePoint ℝ} {f : ι → ℍ → ℂ} {k : ℤ}
    (h : ∀ i, c.IsZeroAt (f i) k) : c.IsZeroAt (∑ i ∈ s, f i) k := by
  refine Finset.sum_induction f (fun u ↦ c.IsZeroAt u k) (fun _ _ ↦ IsZeroAt.add) ?_
    (fun i _ ↦ h i)
  intro g _
  rw [SlashAction.zero_slash]
  exact Filter.zero_zeroAtFilter _

private lemma slash_U_apply (k : ℤ) (p : ℕ) [NeZero p] (j : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] matU p j) τ = (p : ℂ)⁻¹ * f (matU p j • τ) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hd : denom (matU p j) τ = p := by simp [denom, matU_val]
  rw [ModularForm.slash_apply, σ, if_pos (by rw [matU_det]; exact_mod_cast NeZero.pos p),
    matU_det, hd, Nat.abs_cast, Complex.ofReal_natCast, mul_assoc, ← zpow_add₀ hp,
    show k - 1 + -k = -1 by ring]
  simp [mul_comm]

private lemma slash_V_apply (k : ℤ) (p : ℕ) [NeZero p] (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] matV p) τ = (p : ℂ) ^ (k - 1) * f (matV p • τ) := by
  have hd : denom (matV p) τ = 1 := by simp [denom, matV_val]
  rw [ModularForm.slash_apply, σ, if_pos (by rw [matV_det]; exact_mod_cast NeZero.pos p),
    matV_det, hd, Nat.abs_cast, Complex.ofReal_natCast]
  simp [mul_comm]

private lemma coe_U_smul (p : ℕ) [NeZero p] (j : ℤ) (τ : ℍ) :
    ((matU p j • τ : ℍ) : ℂ) = (τ + j) / p := by
  rw [coe_smul_of_det_pos (by rw [matU_det]; exact_mod_cast NeZero.pos p)]
  simp [num, denom, matU_val]

private lemma coe_V_smul (p : ℕ) [NeZero p] (τ : ℍ) :
    ((matV p • τ : ℍ) : ℂ) = p * τ := by
  rw [coe_smul_of_det_pos (by rw [matV_det]; exact_mod_cast NeZero.pos p)]
  simp [num, denom, matV_val]

open Function.Periodic in
private lemma hasSum_V (p : ℕ) [NeZero p] {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ a m * qParam 1 τ ^ m) (f τ)) (τ : ℍ) :
    HasSum (fun n ↦ (if p ∣ n then a (n / p) else 0) * qParam 1 τ ^ n) (f (matV p • τ)) := by
  have hinj : Function.Injective (fun m : ℕ ↦ p * m) := mul_right_injective₀ (NeZero.ne p)
  rw [← hinj.hasSum_iff]
  · convert hf (matV p • τ) using 2 with m
    have : qParam 1 ((matV p • τ : ℍ) : ℂ) = qParam 1 τ ^ p := by
      rw [coe_V_smul, qParam, qParam, ← Complex.exp_nat_mul]
      congr 1
      ring
    simp [this, pow_mul, Nat.mul_div_cancel_left _ (NeZero.pos p)]
  · intro n hn
    rw [if_neg, zero_mul]
    rintro ⟨m, rfl⟩
    exact hn ⟨m, rfl⟩

open Function.Periodic in
private lemma hasSum_U (p : ℕ) [NeZero p] {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ a m * qParam 1 τ ^ m) (f τ)) (τ : ℍ) :
    HasSum (fun n ↦ a (p * n) * qParam 1 τ ^ n)
      (∑ i : ZMod p, (p : ℂ)⁻¹ * f (matU p (-(i.val : ℤ)) • τ)) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hinj : Function.Injective (fun m : ℕ ↦ p * m) := mul_right_injective₀ (NeZero.ne p)
  have h1 := hasSum_sum (s := Finset.univ) fun (i : ZMod p) _ ↦
    (hf (matU p (-(i.val : ℤ)) • τ)).mul_left (p : ℂ)⁻¹
  have key : ∀ m : ℕ, ∑ i : ZMod p, (p : ℂ)⁻¹ *
      (a m * qParam 1 ((matU p (-(i.val : ℤ)) • τ : ℍ) : ℂ) ^ m) =
      if p ∣ m then a m * qParam 1 (τ / p) ^ m else 0 := by
    intro m
    have e : ∀ i : ZMod p, qParam 1 ((matU p (-(i.val : ℤ)) • τ : ℍ) : ℂ) ^ m =
        qParam 1 (τ / p) ^ m * ZMod.stdAddChar (i * (-(m : ZMod p))) := by
      intro i
      have : i * (-(m : ZMod p)) = ((-(i.val * m) : ℤ) : ZMod p) := by simp
      rw [this, ZMod.stdAddChar_coe, coe_U_smul, qParam, qParam, ← Complex.exp_nat_mul,
        ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [e, ← mul_assoc, ← Finset.mul_sum]
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p)]
    simp only [neg_eq_zero, ZMod.natCast_eq_zero_iff, ZMod.card]
    split_ifs
    · field_simp
    · simp
  simp only [key] at h1
  rw [← hinj.hasSum_iff] at h1
  · have : qParam 1 ((τ : ℂ) / p) ^ p = qParam 1 τ := by
      rw [qParam, qParam, ← Complex.exp_nat_mul]
      congr 1
      field_simp
    simpa only [Function.comp_def, dvd_mul_right, if_true, pow_mul, this] using h1
  · intro n hn
    rw [if_neg]
    rintro ⟨m, rfl⟩
    exact hn ⟨m, rfl⟩

end UpperTheory.Reformulated.B.hecke_existence

open UpperHalfPlane Matrix.SpecialLinearGroup OnePoint in
theorem UpperTheory.Reformulated.B.hecke_existence.heckeEx :
    UpperTheory.Reformulated.B.hecke_existence.HeckeEx := by
  intro N k _ hk χ f hf p hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hchar := sum_hasChar (p := p) hf
  have hper : (1 : ℝ) ∈ (Subgroup.map (mapGL ℝ) (CongruenceSubgroup.Gamma1 N)).strictPeriods := by
    simp
  let g : CuspForm (Subgroup.map (mapGL ℝ) (CongruenceSubgroup.Gamma1 N)) (k : ℤ) :=
    { toFun := ∑ x, term k p χ f x
      slash_action_eq' := by
        rintro - ⟨γ, hγ, rfl⟩
        have := hchar γ (CongruenceSubgroup.Gamma1_in_Gamma0 N hγ)
        rw [((CongruenceSubgroup.Gamma1_mem N γ).mp hγ).2.1, map_one, one_smul] at this
        exact this
      holo' := by
        refine Finset.sum_induction (fun x ↦ term k p χ f x) _ (fun _ _ ↦ MDifferentiable.add)
          mdifferentiable_const (fun x _ ↦ ?_)
        cases x with
        | infty => exact ((ModularFormClass.holo f).slash _ _).const_smul _
        | coe i => exact (ModularFormClass.holo f).slash _ _
      zero_at_cusps' := fun hc ↦ by
        refine isZeroAt_sum _ fun x ↦ ?_
        cases x with
        | infty =>
          exact isZeroAt_smul
            (IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f (isCusp_V hc p))) _
        | coe i => exact IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f (isCusp_U hc p _)) }
  refine ⟨g, hchar, fun n _ ↦ ?_⟩
  haveI : Fact (IsCusp ∞ (Subgroup.map (mapGL ℝ) (CongruenceSubgroup.Gamma1 N))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hper⟩
  have hs : ∀ τ : ℍ, HasSum (fun m ↦ coef f m * Function.Periodic.qParam 1 τ ^ m) (f τ) :=
    fun τ ↦ ModularForm.hasSum_qExpansion f one_pos hper τ
  symm
  refine ModularFormClass.qExpansion_coeff_unique (f := g) (c := fun n ↦ coef f (p * n) +
    χ p * (p : ℂ) ^ (k - 1) * if p ∣ n then coef f (n / p) else 0) one_pos hper (fun τ ↦ ?_) n
  have hval : g τ = (∑ i : ZMod p, (p : ℂ)⁻¹ * f (matU p (-(i.val : ℤ)) • τ)) +
      χ p * (p : ℂ) ^ (k - 1) * f (matV p • τ) := by
    change (∑ x, term k p χ f x) τ = _
    rw [Finset.sum_apply, add_comm]
    refine (Fintype.sum_option (fun x : Option (ZMod p) ↦ term k p χ f x τ)).trans ?_
    congr 1
    · change χ p * (SlashAction.map (k : ℤ) (matV p) ⇑f) τ = _
      rw [slash_V_apply, mul_assoc, ← zpow_natCast, Nat.cast_sub hk, Nat.cast_one]
    · exact Finset.sum_congr rfl fun i _ ↦ slash_U_apply _ _ _ _ _
  rw [hval]
  convert (hasSum_U p hs τ).add ((hasSum_V p hs τ).mul_left (χ p * (p : ℂ) ^ (k - 1))) using 2
  rw [smul_eq_mul]
  ring
