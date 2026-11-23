import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNilpotentAlgebraIsotropicFlagUnipotentRadi

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.SkewBasis

section Real

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_orthonormal_on {d : ℕ} (p : Fin d → Prop) [DecidablePred p] (G : Submodule ℝ V)
    (hG : Module.finrank ℝ G = Fintype.card {i // p i}) :
    ∃ f : Fin d → V, (∀ i k, p i → p k → inner ℝ (f i) (f k) = if i = k then 1 else 0) ∧
      G = Submodule.span ℝ (f '' {i | p i}) := by
  classical
  obtain ⟨e⟩ : Nonempty ({i // p i} ≃ Fin (Module.finrank ℝ G)) :=
    ⟨Fintype.equivFinOfCardEq hG.symm⟩
  let b := stdOrthonormalBasis ℝ G
  refine ⟨fun i => if h : p i then ((b (e ⟨i, h⟩) : G) : V) else 0, ?_, ?_⟩
  · intro i k hi hk
    simp only [dif_pos hi, dif_pos hk]
    rw [← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal]
    by_cases hik : i = k
    · subst hik
      simp
    · rw [if_neg hik, if_neg]
      intro h
      exact hik (congrArg Subtype.val (e.injective h))
  · have hset : (fun i => if h : p i then ((b (e ⟨i, h⟩) : G) : V) else 0) '' {i | p i} =
        G.subtype '' Set.range b := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨b (e ⟨i, hi⟩), ⟨_, rfl⟩, by simp [show p i from hi]⟩
      · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
        refine ⟨(e.symm j).1, (e.symm j).2, ?_⟩
        simp [(e.symm j).2]
    have hspan : Submodule.span ℝ (Set.range b) = ⊤ := by
      rw [← b.coe_toBasis]
      exact b.toBasis.span_eq
    rw [hset, ← Submodule.map_span, hspan, Submodule.map_subtype_top]

theorem exists_orthonormal_adapted {d m : ℕ} (P : ℕ → Submodule ℝ V) (deg : Fin d → ℕ)
    (hP : ∀ c, P (c + 1) ≤ P c) (hm : P m = ⊥)
    (hd : ∀ c, Module.finrank ℝ (P c) =
      Module.finrank ℝ (P (c + 1)) + Fintype.card {i : Fin d // deg i = c}) :
    ∃ b : Fin d → V, (∀ i k, inner ℝ (b i) (b k) = if i = k then 1 else 0) ∧
      ∀ c, P c = Submodule.span ℝ (b '' {i | c ≤ deg i}) := by
  classical

  have hQ : ∀ c, Module.finrank ℝ ((P (c + 1))ᗮ ⊓ P c : Submodule ℝ V) =
      Fintype.card {i : Fin d // deg i = c} := fun c =>
    Submodule.finrank_add_inf_finrank_orthogonal' (hP c) (hd c).symm
  have hf : ∀ c, ∃ f : Fin d → V,
      (∀ i k, deg i = c → deg k = c → inner ℝ (f i) (f k) = if i = k then 1 else 0) ∧
      ((P (c + 1))ᗮ ⊓ P c : Submodule ℝ V) = Submodule.span ℝ (f '' {i | deg i = c}) :=
    fun c => exists_orthonormal_on (fun i => deg i = c) _ (hQ c)
  choose f hfo hfs using hf
  have hanti : Antitone P := antitone_nat_of_succ_le hP
  have hbQ : ∀ i, f (deg i) i ∈ ((P (deg i + 1))ᗮ ⊓ P (deg i) : Submodule ℝ V) := by
    intro i
    rw [hfs (deg i)]
    exact Submodule.subset_span ⟨i, (rfl : deg i = deg i), rfl⟩

  have horth : ∀ c c', c < c' → ∀ x ∈ ((P (c + 1))ᗮ ⊓ P c : Submodule ℝ V),
      ∀ y ∈ ((P (c' + 1))ᗮ ⊓ P c' : Submodule ℝ V), inner ℝ x y = 0 := by
    intro c c' hcc x hx y hy
    have hy' : y ∈ P (c + 1) := hanti (Nat.succ_le_of_lt hcc) hy.2
    exact Submodule.inner_left_of_mem_orthogonal hy' hx.1
  have hbot : ∀ c, m ≤ c → P c = ⊥ := fun c hc => le_bot_iff.mp ((hanti hc).trans hm.le)
  have hdeg : ∀ i, deg i < m := by
    intro i
    by_contra h'
    have h : m ≤ deg i := not_lt.mp h'
    have h1 := hd (deg i)
    rw [hbot _ h, hbot _ (by omega)] at h1
    simp only [finrank_bot, zero_add] at h1
    exact (Fintype.card_eq_zero_iff.mp h1.symm).false ⟨i, rfl⟩
  refine ⟨fun i => f (deg i) i, ?_, ?_⟩
  · intro i k
    rcases lt_trichotomy (deg i) (deg k) with h | h | h
    · have hik : i ≠ k := fun e => by subst e; exact lt_irrefl _ h
      rw [if_neg hik]
      exact horth _ _ h _ (hbQ i) _ (hbQ k)
    · show inner ℝ (f (deg i) i) (f (deg k) k) = _
      rw [← h]
      exact hfo (deg i) i k rfl h.symm
    · have hik : i ≠ k := fun e => by subst e; exact lt_irrefl _ h
      rw [if_neg hik, real_inner_comm]
      exact horth _ _ h _ (hbQ k) _ (hbQ i)
  ·
    have key : ∀ j c, m ≤ c + j → P c = Submodule.span ℝ ((fun i => f (deg i) i) '' {i | c ≤ deg i}) := by
      intro j
      induction j with
      | zero =>
        intro c hc
        have hempty : {i | c ≤ deg i} = (∅ : Set (Fin d)) := by
          ext i
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
          have := hdeg i
          omega
        rw [hbot c (by omega), hempty, Set.image_empty, Submodule.span_empty]
      | succ j ih =>
        intro c hc
        have h1 := ih (c + 1) (by omega)
        have hsplit : {i | c ≤ deg i} = {i | c + 1 ≤ deg i} ∪ {i | deg i = c} := by
          ext i
          simp only [Set.mem_ofPred_eq, Set.mem_union]
          omega
        have himg : (fun i => f (deg i) i) '' {i | deg i = c} = f c '' {i | deg i = c} := by
          apply Set.image_congr
          intro i hi
          have hi' : deg i = c := hi
          simp only [hi']
        rw [hsplit, Set.image_union, Submodule.span_union, ← h1, himg, ← hfs c]
        exact (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hP c)).symm
    intro c
    exact key m c (by omega)

end Real

theorem exists_re_orthonormal_adapted {n d m : ℕ} (P : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (deg : Fin d → ℕ) (hP : ∀ c, P (c + 1) ≤ P c) (hm : P m = ⊥)
    (hd : ∀ c, Module.finrank ℝ (P c) =
      Module.finrank ℝ (P (c + 1)) + Fintype.card {i : Fin d // deg i = c}) :
    ∃ b : Fin d → Matrix (Fin n) (Fin n) ℂ,
      (∀ i k, ((b i * (b k)ᴴ).trace).re = if i = k then 1 else 0) ∧
      ∀ c, P c = Submodule.span ℝ (b '' {i | c ≤ deg i}) := by
  classical

  let e : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] PiLp 2 (fun _ : Fin n × Fin n => ℂ) :=
    ((Matrix.ofLinearEquiv ℝ).symm.trans (LinearEquiv.curry ℝ ℂ (Fin n) (Fin n)).symm).trans
      (WithLp.linearEquiv 2 ℝ (Fin n × Fin n → ℂ)).symm
  have hev : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (p : Fin n × Fin n), (e Z) p = Z p.1 p.2 :=
    fun Z p => rfl
  have hinner : ∀ X Y : Matrix (Fin n) (Fin n) ℂ, inner ℝ (e X) (e Y) = ((X * Yᴴ).trace).re := by
    intro X Y
    rw [PiLp.inner_apply, Fintype.sum_prod_type]
    simp only [hev, Complex.inner, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ → Submodule ℝ (PiLp 2 (fun _ : Fin n × Fin n => ℂ)),
      ∀ c, Q c = (P c).map (e : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] PiLp 2 (fun _ : Fin n × Fin n => ℂ)) :=
    ⟨_, fun c => rfl⟩
  have hQ1 : ∀ c, Q (c + 1) ≤ Q c := fun c => by
    rw [hQdef, hQdef]
    exact Submodule.map_mono (hP c)
  have hQ2 : Q m = ⊥ := by rw [hQdef, hm, Submodule.map_bot]
  have hQ3 : ∀ c, Module.finrank ℝ (Q c) =
      Module.finrank ℝ (Q (c + 1)) + Fintype.card {i : Fin d // deg i = c} := fun c => by
    rw [hQdef, hQdef, LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]
    exact hd c
  obtain ⟨b', hb'o, hb's⟩ := exists_orthonormal_adapted Q deg hQ1 hQ2 hQ3
  refine ⟨fun i => e.symm (b' i), ?_, ?_⟩
  · intro i k
    rw [← hinner, e.apply_symm_apply, e.apply_symm_apply]
    exact hb'o i k
  · intro c
    have h1 := hb's c
    rw [hQdef] at h1
    have h2 := congrArg
      (Submodule.map (e.symm : PiLp 2 (fun _ : Fin n × Fin n => ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)) h1
    rw [Submodule.map_span, ← Set.image_comp] at h2
    have h3 : Submodule.map (e.symm : PiLp 2 (fun _ : Fin n × Fin n => ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
        (Submodule.map (e : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] PiLp 2 (fun _ : Fin n × Fin n => ℂ)) (P c)) =
        P c := by
      ext X
      simp
    rw [h3] at h2
    exact h2

open GlobalTheory.RadicalAlg Formalism.REAL in

theorem trace_im_eq_zero {n : ℕ} (ε : Fin n → Bool) {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : negAdj ε X = X) (hY : negAdj ε Y = Y) : ((X * Yᴴ).trace).im = 0 := by
  have hJ : Jm ε * Jm ε = 1 := Jm_mul_self ε

  have key : ∀ Z : Matrix (Fin n) (Fin n) ℂ, negAdj ε Z = Z → Zᴴ = -(Jm ε * Z * Jm ε) := by
    intro Z hZ
    rw [negAdj_apply] at hZ
    calc Zᴴ = Jm ε * Jm ε * Zᴴ * (Jm ε * Jm ε) := by rw [hJ, one_mul, mul_one]
      _ = -(Jm ε * (-(Jm ε * Zᴴ * Jm ε)) * Jm ε) := by
          simp only [mul_neg, neg_mul, neg_neg, mul_assoc]
      _ = -(Jm ε * Z * Jm ε) := by rw [hZ]
  have h1 : (X * Yᴴ).trace = -((X * Jm ε) * (Y * Jm ε)).trace := by
    rw [key Y hY, mul_neg, Matrix.trace_neg]
    simp only [mul_assoc]
  have h2 : star (X * Yᴴ).trace = -((Y * Jm ε) * (X * Jm ε)).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      key X hX, mul_neg, Matrix.trace_neg]
    simp only [mul_assoc]
  have h3 : star (X * Yᴴ).trace = (X * Yᴴ).trace := by
    rw [h2, h1, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_im.mp h3

open GlobalTheory.RadicalAlg in

theorem exists_skew_basis : ∀ (n d m : ℕ) (ε : Fin n → Bool) (A : ℕ → Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (deg : Fin d → ℕ), (∀ c, A (c + 1) ≤ A c) → A m = ⊥ → (∀ c, ∀ X ∈ A c, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ A c) → (∀ c, Module.finrank ℂ (A c) = Module.finrank ℂ (A (c + 1)) + Fintype.card {i : Fin d // deg i = c}) → ∃ B : Fin d → Matrix (Fin n) (Fin n) ℂ, (∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) ∧ (∀ i, Formalism.REAL.inG ε (B i)) ∧ ∀ c, A c = Submodule.span ℂ (B '' {i | c ≤ deg i}) := by
  intro n d m ε A deg hA hm hstab hd
  classical
  have hσA : ∀ c, ∀ X ∈ A c, negAdj ε X ∈ A c := fun c X hX => by
    rw [negAdj_apply]
    exact (A c).neg_mem (hstab c X hX)
  have hreal : ∀ (r : ℝ) (X : Matrix (Fin n) (Fin n) ℂ), negAdj ε (r • X) = r • negAdj ε X := by
    intro r X
    have e1 : ∀ Z : Matrix (Fin n) (Fin n) ℂ, (r : ℂ) • Z = r • Z := fun Z => by
      ext i j
      simp [Complex.real_smul]
    have e2 : star (r : ℂ) = r := Complex.conj_ofReal r
    rw [← e1, ← e1, negAdj_smul, e2]

  obtain ⟨P, hPmem⟩ : ∃ P : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ),
      ∀ c X, X ∈ P c ↔ X ∈ A c ∧ negAdj ε X = X :=
    ⟨fun c =>
      { carrier := {X | X ∈ A c ∧ negAdj ε X = X}
        add_mem' := fun {X Y} hX hY => ⟨(A c).add_mem hX.1 hY.1, by rw [map_add, hX.2, hY.2]⟩
        zero_mem' := ⟨(A c).zero_mem, map_zero _⟩
        smul_mem' := fun r X hX => ⟨(A c).smul_of_tower_mem r hX.1, by rw [hreal, hX.2]⟩ },
      fun c X => Iff.rfl⟩
  have hPdim : ∀ c, Module.finrank ℝ (P c) = Module.finrank ℂ (A c) := fun c =>
    finrank_fixed (negAdj ε) (negAdj_negAdj ε) (negAdj_smul ε) (A c) (hσA c) (P c) (hPmem c)
  have hPle : ∀ c, P (c + 1) ≤ P c := fun c X hX => by
    rw [hPmem] at hX ⊢
    exact ⟨hA c hX.1, hX.2⟩
  have hPm : P m = ⊥ := by
    rw [eq_bot_iff]
    intro X hX
    rw [hPmem, hm] at hX
    rw [Submodule.mem_bot]
    exact (Submodule.mem_bot ℂ).mp hX.1
  have hPd : ∀ c, Module.finrank ℝ (P c) =
      Module.finrank ℝ (P (c + 1)) + Fintype.card {i : Fin d // deg i = c} := fun c => by
    rw [hPdim, hPdim]
    exact hd c
  obtain ⟨B, hBo, hBs⟩ := exists_re_orthonormal_adapted P deg hPle hPm hPd
  have hBP : ∀ c i, c ≤ deg i → B i ∈ P c := by
    intro c i hi
    rw [hBs c]
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  have hBfix : ∀ i, negAdj ε (B i) = B i := fun i => ((hPmem _ _).mp (hBP 0 i (Nat.zero_le _))).2
  refine ⟨B, ?_, ?_, ?_⟩
  · intro i k
    apply Complex.ext
    · rw [hBo i k]
      split_ifs <;> simp
    · rw [trace_im_eq_zero ε (hBfix i) (hBfix k)]
      split_ifs <;> simp
  · intro i
    exact (negAdj_eq_iff ε (B i)).mp (hBfix i)
  · intro c
    have hmem : ∀ Y ∈ P c, Y ∈ Submodule.span ℂ (B '' {i | c ≤ deg i}) := fun Y hY =>
      Submodule.span_le_restrictScalars (R := ℝ) (S := ℂ) (s := B '' {i | c ≤ deg i})
        (by rw [← hBs c]; exact hY)
    apply le_antisymm
    · intro X hX
      have hX1 : X + negAdj ε X ∈ P c := by
        rw [hPmem]
        exact ⟨(A c).add_mem hX (hσA c X hX), by rw [map_add, negAdj_negAdj, add_comm]⟩
      have hX2 : Complex.I • (X - negAdj ε X) ∈ P c := by
        rw [hPmem]
        refine ⟨(A c).smul_mem _ ((A c).sub_mem hX (hσA c X hX)), ?_⟩
        have eI : star Complex.I = -Complex.I := Complex.conj_I
        rw [negAdj_smul, map_sub, negAdj_negAdj, eI, neg_smul, ← smul_neg, neg_sub]
      have hc : -(Complex.I / 2) * Complex.I = (1 / 2 : ℂ) := by
        linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
      have hdec : X = (1 / 2 : ℂ) • (X + negAdj ε X) + (-(Complex.I / 2)) • (Complex.I • (X - negAdj ε X)) := by
        rw [smul_smul, hc]
        module
      rw [hdec]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem _ hX1)) (Submodule.smul_mem _ _ (hmem _ hX2))
    · rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact ((hPmem _ _).mp (hBP c i hi)).1

end GlobalTheory.SkewBasis
