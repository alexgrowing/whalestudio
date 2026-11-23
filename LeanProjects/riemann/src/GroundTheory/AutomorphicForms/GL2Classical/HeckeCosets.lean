import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.Adelic
import GroundTheory.AutomorphicForms.GL2Classical.ConstantTerm

open NumberField IsDedekindDomain Matrix
open GroundTheory.Global
open scoped Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn

set_option linter.unusedSectionVars false

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem mem_integralFiniteAdeles_of_mem_levelIdeal {N : ℕ} {x : 𝔸f} (hx : x ∈ levelIdeal N) :
    x ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact mul_mem (natCast_mem _ N) ht

theorem add_mem_levelIdeal {N : ℕ} {x y : 𝔸f} (hx : x ∈ levelIdeal N) (hy : y ∈ levelIdeal N) :
    x + y ∈ levelIdeal N := by
  simpa using mul_add_mul_mem_levelIdeal (one_mem _) (one_mem _) hx hy

theorem neg_mem_levelIdeal {N : ℕ} {x : 𝔸f} (hx : x ∈ levelIdeal N) : -x ∈ levelIdeal N := by
  simpa using mul_mem_levelIdeal (neg_mem (one_mem (integralFiniteAdeles (𝓞 ℚ) ℚ))) hx

theorem intCast_mem_levelIdeal {N : ℕ} {m : ℤ} (hm : (N : ℤ) ∣ m) : (m : 𝔸f) ∈ levelIdeal N := by
  obtain ⟨t, rfl⟩ := hm
  exact ⟨t, intCast_mem_integralFiniteAdeles t, by push_cast; ring⟩

theorem natCast_mul_mem_levelIdeal (N : ℕ) {x : 𝔸f} (hx : x ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    (N : 𝔸f) * x ∈ levelIdeal N :=
  ⟨x, hx, rfl⟩

theorem natCast_mul_mem_levelIdeal' {N m : ℕ} {x : 𝔸f} (hx : x ∈ levelIdeal N) :
    (m : 𝔸f) * x ∈ levelIdeal N :=
  mul_mem_levelIdeal (natCast_mem _ m) hx

theorem levelIdeal_subset_of_dvd {p N : ℕ} (h : p ∣ N) {x : 𝔸f} (hx : x ∈ levelIdeal N) :
    x ∈ levelIdeal p := by
  obtain ⟨m, rfl⟩ := h
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨m * t, mul_mem (natCast_mem _ m) ht, by push_cast; ring⟩

theorem int_dvd_of_mem_levelIdeal (N : ℕ) [NeZero N] {m : ℤ} (hm : (m : 𝔸f) ∈ levelIdeal N) :
    (N : ℤ) ∣ m := by
  obtain ⟨t, ht⟩ := exists_int_of_mem_levelIdeal N (x := (m : ℚ)) (by simpa using hm)
  exact ⟨t, by exact_mod_cast ht⟩

theorem one_notMem_levelIdeal {p : ℕ} (hp : 2 ≤ p) : (1 : 𝔸f) ∉ levelIdeal p := by
  intro h
  have : NeZero p := ⟨by omega⟩
  have := int_dvd_of_mem_levelIdeal p (m := 1) (by simpa using h)
  have h1 := Int.le_of_dvd one_pos this
  omega

theorem exists_int_sub_mem_levelIdeal (N : ℕ) [NeZero N] {x : 𝔸f}
    (hx : x ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) : ∃ m : ℤ, x - m ∈ levelIdeal N := by
  have hU : IsOpen ((fun y : 𝔸f => y - x) ⁻¹' levelIdeal N) :=
    (isOpen_levelIdeal N).preimage (continuous_id.sub continuous_const)
  obtain ⟨q, hq⟩ := (denseRange_algebraMap_finiteAdeleRing ℚ).exists_mem_open hU
    ⟨x, by simpa using zero_mem_levelIdeal N⟩
  have hq' : algebraMap ℚ 𝔸f q - x ∈ levelIdeal N := hq
  have hqZ : algebraMap ℚ 𝔸f q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    simpa using add_mem (mem_integralFiniteAdeles_of_mem_levelIdeal hq') hx
  obtain ⟨m, rfl⟩ := exists_int_of_mem_integralFiniteAdeles hqZ
  refine ⟨m, ?_⟩
  have := neg_mem_levelIdeal hq'
  rwa [neg_sub, map_intCast] at this

theorem exists_fin_add_mul_mem_levelIdeal {p : ℕ} [hp : Fact p.Prime] {b d : 𝔸f}
    (hb : b ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) (hd : d ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hdp : d ∉ levelIdeal p) : ∃ j : Fin p, b + ((j : ℕ) : 𝔸f) * d ∈ levelIdeal p := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨b', hb'⟩ := exists_int_sub_mem_levelIdeal p hb
  obtain ⟨d', hd'⟩ := exists_int_sub_mem_levelIdeal p hd
  have hd'0 : (d' : ZMod p) ≠ 0 := by
    intro h0
    apply hdp
    have : ((d' : ℤ) : 𝔸f) ∈ levelIdeal p :=
      intCast_mem_levelIdeal ((ZMod.intCast_zmod_eq_zero_iff_dvd d' p).1 h0)
    simpa using add_mem_levelIdeal hd' this
  set j : ZMod p := -(b' : ZMod p) / (d' : ZMod p)
  refine ⟨⟨j.val, ZMod.val_lt j⟩, ?_⟩
  have hdiv : (p : ℤ) ∣ b' + (j.val : ℤ) * d' := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val]
    simp only [j]
    field_simp
    ring
  have e : b + ((j.val : ℕ) : 𝔸f) * d =
      (b - b') + ((j.val : ℕ) : 𝔸f) * (d - d') + (((b' + (j.val : ℤ) * d' : ℤ)) : 𝔸f) := by
    push_cast; ring
  rw [e]
  refine add_mem_levelIdeal (add_mem_levelIdeal hb' (mul_mem_levelIdeal (natCast_mem _ _) hd'))
    (intCast_mem_levelIdeal hdiv)

variable (N : ℕ) [NeZero N]

theorem mem_Gamma0Level_of {g : FiniteAdelicGL ℚ 2}
    (hg : ∀ a b, (g : Matrix (Fin 2) (Fin 2) 𝔸f) a b ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hdet : ((Matrix.GeneralLinearGroup.det g)⁻¹ : 𝔸fˣ).val ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hc : (g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 ∈ levelIdeal N) : g ∈ Gamma0Level N := by
  refine ⟨(mem_integralFiniteGL_iff ℚ 2).2 ⟨hg, fun a b => ?_⟩, hc⟩
  have hinv : ((g⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) =
      ((Matrix.GeneralLinearGroup.det g)⁻¹ : 𝔸fˣ).val • adjugate (g : Matrix (Fin 2) (Fin 2) 𝔸f) := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, ← Matrix.GeneralLinearGroup.val_det_apply,
      Ring.inverse_unit]
  rw [hinv, Matrix.smul_apply, smul_eq_mul]
  refine mul_mem hdet ?_
  rw [Matrix.adjugate_fin_two]
  fin_cases a <;> fin_cases b <;> simp [hg _ _]

theorem inv_det_mem_of_mem_Gamma0Level {k : FiniteAdelicGL ℚ 2} (hk : k ∈ Gamma0Level N) :
    ((Matrix.GeneralLinearGroup.det k)⁻¹ : 𝔸fˣ).val ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  have h2 := ((mem_integralFiniteGL_iff ℚ 2).1 hk.1).2
  have := det_mem_of_forall_mem (integralFiniteAdeles (𝓞 ℚ) ℚ) h2
  rwa [← Matrix.GeneralLinearGroup.val_det_apply, map_inv] at this

theorem entry_mem_of_mem_Gamma0Level {k : FiniteAdelicGL ℚ 2} (hk : k ∈ Gamma0Level N) (a b : Fin 2) :
    (k : Matrix (Fin 2) (Fin 2) 𝔸f) a b ∈ integralFiniteAdeles (𝓞 ℚ) ℚ :=
  ((mem_integralFiniteGL_iff ℚ 2).1 hk.1).1 a b

theorem inv_mul_mem_Gamma0Level_of (ξ g : FiniteAdelicGL ℚ 2) (M : Matrix (Fin 2) (Fin 2) 𝔸f)
    (hM : (ξ : Matrix (Fin 2) (Fin 2) 𝔸f) * M = g)
    (hent : ∀ a b, M a b ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) (hc : M 1 0 ∈ levelIdeal N)
    (u : 𝔸fˣ) (hu : M.det = u) (hu' : (u⁻¹ : 𝔸fˣ).val ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    ξ⁻¹ * g ∈ Gamma0Level N := by
  have hval : ((ξ⁻¹ * g : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) = M := by
    rw [Units.val_mul, ← hM, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]
  have hdet : Matrix.GeneralLinearGroup.det (ξ⁻¹ * g) = u := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hval, hu]
  refine mem_Gamma0Level_of N (fun a b => ?_) ?_ ?_
  · rw [hval]; exact hent a b
  · rw [hdet]; exact hu'
  · rw [hval]; exact hc

variable (p : ℕ) [NeZero p]

theorem natCast_ne_zero_rat : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)

def upperHecke (j : ℤ) : GL (Fin 2) ℚ where
  val := !![(p : ℚ), j; 0, 1]
  inv := !![(p : ℚ)⁻¹, -j / p; 0, 1]
  val_inv := by
    have := natCast_ne_zero_rat p
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  inv_val := by
    have := natCast_ne_zero_rat p
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

def lowerHecke : GL (Fin 2) ℚ where
  val := !![1, 0; 0, (p : ℚ)]
  inv := !![1, 0; 0, (p : ℚ)⁻¹]
  val_inv := by
    have := natCast_ne_zero_rat p
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    have := natCast_ne_zero_rat p
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

abbrev heckeAlpha : GL (Fin 2) ℚ := upperHecke p 0

theorem coe_upperHecke (j : ℤ) :
    ((upperHecke p j : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(p : ℚ), j; 0, 1] := rfl

theorem coe_upperHecke_inv (j : ℤ) :
    (((upperHecke p j)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(p : ℚ)⁻¹, -j / p; 0, 1] := rfl

theorem coe_lowerHecke :
    ((lowerHecke p : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; 0, (p : ℚ)] := rfl

theorem coe_lowerHecke_inv :
    (((lowerHecke p)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; 0, (p : ℚ)⁻¹] := rfl

theorem coe_finiteDiagonal (γ : GL (Fin 2) ℚ) :
    ((finiteDiagonal ℚ 2 γ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) =
      !![algebraMap ℚ 𝔸f (γ 0 0), algebraMap ℚ 𝔸f (γ 0 1);
        algebraMap ℚ 𝔸f (γ 1 0), algebraMap ℚ 𝔸f (γ 1 1)] := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem finiteDiagonal_unip_mem (j : ℤ) :
    finiteDiagonal ℚ 2 (upperHecke 1 j) ∈ Gamma0Level N := by
  refine finiteDiagonal_mem_Gamma0Level_of_int N !![1, j; 0, 1] !![1, -j; 0, 1] ?_ ?_ (by simp)
  · intro a b
    fin_cases a <;> fin_cases b <;> simp [coe_upperHecke]
  · intro a b
    rw [coe_upperHecke_inv]
    fin_cases a <;> fin_cases b <;> simp

theorem upperHecke_eq_mul (j : ℤ) : upperHecke p j = upperHecke 1 j * heckeAlpha p := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_upperHecke, Matrix.mul_apply, Fin.sum_univ_two]

def heckeReps : Finset (GL (Fin 2) ℚ) := by
  classical
  exact (Finset.univ.image fun j : Fin p => upperHecke p (-(j : ℕ))) ∪
    (if p ∣ N then ∅ else {lowerHecke p})

theorem mem_heckeReps {ξ : GL (Fin 2) ℚ} :
    ξ ∈ heckeReps N p ↔ (∃ j : Fin p, upperHecke p (-(j : ℕ)) = ξ) ∨ (¬ p ∣ N ∧ ξ = lowerHecke p) := by
  classical
  unfold heckeReps
  by_cases h : p ∣ N <;> simp [h, or_comm]

def heckeSet : Set (FiniteAdelicGL ℚ 2) :=
  {g | ∃ k₁ ∈ Gamma0Level N, ∃ k₂ ∈ Gamma0Level N,
    g = k₁ * finiteDiagonal ℚ 2 (heckeAlpha p) * k₂}

variable [Fact p.Prime]

def glOfDetOne (a b c d : ℤ) (h : a * d - b * c = 1) : GL (Fin 2) ℚ where
  val := !![(a : ℚ), b; c, d]
  inv := !![(d : ℚ), -b; -c, a]
  val_inv := by
    have h' : (a : ℚ) * d - b * c = 1 := by exact_mod_cast h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | linear_combination h' | ring
  inv_val := by
    have h' : (a : ℚ) * d - b * c = 1 := by exact_mod_cast h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | linear_combination h' | ring

theorem coe_glOfDetOne (a b c d : ℤ) (h : a * d - b * c = 1) :
    ((glOfDetOne a b c d h : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![(a : ℚ), b; c, d] := rfl

theorem finiteDiagonal_glOfDetOne_mem {a b c d : ℤ} (h : a * d - b * c = 1) (hc : (N : ℤ) ∣ c) :
    finiteDiagonal ℚ 2 (glOfDetOne a b c d h) ∈ Gamma0Level N := by
  refine finiteDiagonal_mem_Gamma0Level_of_int N !![a, b; c, d] !![d, -b; -c, a] ?_ ?_ (by simpa using hc)
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [coe_glOfDetOne]
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl

theorem exists_lowerHecke_mul_eq (hpN : Nat.Coprime p N) :
    ∃ γ δ : GL (Fin 2) ℚ, finiteDiagonal ℚ 2 γ ∈ Gamma0Level N ∧
      finiteDiagonal ℚ 2 δ ∈ Gamma0Level N ∧ lowerHecke p * δ = γ * heckeAlpha p := by
  obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, x * p + y * N = 1 := by
    have := Nat.Coprime.gcd_eq_one hpN
    refine ⟨Nat.gcdA p N, Nat.gcdB p N, ?_⟩
    have h := Nat.gcd_eq_gcd_ab p N
    rw [this] at h
    push_cast at h
    linarith
  refine ⟨glOfDetOne x (-y) N p (by linarith), glOfDetOne (x * p) (-y) N 1 (by linarith),
    finiteDiagonal_glOfDetOne_mem N _ dvd_rfl, finiteDiagonal_glOfDetOne_mem N _ dvd_rfl, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, coe_glOfDetOne, coe_lowerHecke, coe_upperHecke] <;> ring

theorem finiteDiagonal_mem_heckeSet {ξ : GL (Fin 2) ℚ} (hξ : ξ ∈ heckeReps N p) :
    finiteDiagonal ℚ 2 ξ ∈ heckeSet N p := by
  rcases (mem_heckeReps N p).1 hξ with ⟨j, rfl⟩ | ⟨hpN, rfl⟩
  · refine ⟨_, finiteDiagonal_unip_mem N (-((j : ℕ) : ℤ)), 1, one_mem _, ?_⟩
    rw [mul_one, ← map_mul, ← upperHecke_eq_mul]
  · have hcop : Nat.Coprime p N := by
      rcases Nat.coprime_or_dvd_of_prime (Fact.out : p.Prime) N with h | h
      · exact h
      · exact absurd h hpN
    obtain ⟨γ, δ, hγ, hδ, he⟩ := exists_lowerHecke_mul_eq N p hcop
    refine ⟨_, hγ, _, inv_mem hδ, ?_⟩
    rw [← map_mul, ← he, ← map_inv, ← map_mul, mul_inv_cancel_right]

theorem exists_heckeReps_inv_mul_mem {k : FiniteAdelicGL ℚ 2} (hk : k ∈ Gamma0Level N) :
    ∃ ξ ∈ heckeReps N p,
      (finiteDiagonal ℚ 2 ξ)⁻¹ * (k * finiteDiagonal ℚ 2 (heckeAlpha p)) ∈ Gamma0Level N := by
  have hprime : p.Prime := Fact.out
  set K : Matrix (Fin 2) (Fin 2) 𝔸f := (k : Matrix (Fin 2) (Fin 2) 𝔸f) with hK
  have ha : K 0 0 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := entry_mem_of_mem_Gamma0Level N hk 0 0
  have hb : K 0 1 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := entry_mem_of_mem_Gamma0Level N hk 0 1
  have hc : K 1 0 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := entry_mem_of_mem_Gamma0Level N hk 1 0
  have hd : K 1 1 ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := entry_mem_of_mem_Gamma0Level N hk 1 1
  have hcN : K 1 0 ∈ levelIdeal N := hk.2
  have hdetk : (Matrix.GeneralLinearGroup.det k : 𝔸f) = K 0 0 * K 1 1 - K 0 1 * K 1 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hkα : ((k * finiteDiagonal ℚ 2 (heckeAlpha p) : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) =
      !![K 0 0 * p, K 0 1; K 1 0 * p, K 1 1] := by
    rw [Units.val_mul, coe_finiteDiagonal, ← hK, Matrix.eta_fin_two K]
    simp [Matrix.mul_fin_two, coe_upperHecke]
  by_cases hdp : K 1 1 ∈ levelIdeal p
  · have hpN : ¬ p ∣ N := by
      intro hpN
      apply one_notMem_levelIdeal hprime.two_le
      have hcp : K 1 0 ∈ levelIdeal p := levelIdeal_subset_of_dvd hpN hcN
      have hmem : (Matrix.GeneralLinearGroup.det k : 𝔸f) ∈ levelIdeal p := by
        rw [hdetk]
        exact sub_mem_levelIdeal (mul_mem_levelIdeal ha hdp) (mul_mem_levelIdeal hb hcp)
      have h1 : (1 : 𝔸f) = ((Matrix.GeneralLinearGroup.det k)⁻¹ : 𝔸fˣ).val *
          (Matrix.GeneralLinearGroup.det k : 𝔸f) := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [h1]
      exact mul_mem_levelIdeal (inv_det_mem_of_mem_Gamma0Level N hk) hmem
    obtain ⟨t, ht, hdt⟩ := hdp
    refine ⟨lowerHecke p, (mem_heckeReps N p).2 (Or.inr ⟨hpN, rfl⟩), ?_⟩
    refine inv_mul_mem_Gamma0Level_of N _ _ !![K 0 0 * p, K 0 1; K 1 0, t] ?_ ?_ hcN
      (Matrix.GeneralLinearGroup.det k) ?_ (inv_det_mem_of_mem_Gamma0Level N hk)
    · rw [hkα, coe_finiteDiagonal, hdt]
      simp [Matrix.mul_fin_two, coe_lowerHecke]
      ring_nf
    · intro i j
      fin_cases i <;> fin_cases j
      · exact mul_mem ha (natCast_mem _ p)
      · exact hb
      · exact hc
      · exact ht
    · rw [Matrix.det_fin_two_of, hdetk, hdt]
      ring
  · obtain ⟨j, hj⟩ := exists_fin_add_mul_mem_levelIdeal hb hd hdp
    obtain ⟨t, ht, hjt⟩ := hj
    refine ⟨upperHecke p (-((j : ℕ) : ℤ)), (mem_heckeReps N p).2 (Or.inl ⟨j, rfl⟩), ?_⟩
    refine inv_mul_mem_Gamma0Level_of N _ _
      !![K 0 0 + (j : ℕ) * K 1 0, t; p * K 1 0, K 1 1] ?_ ?_ (natCast_mul_mem_levelIdeal' hcN)
      (Matrix.GeneralLinearGroup.det k) ?_ (inv_det_mem_of_mem_Gamma0Level N hk)
    · rw [hkα, coe_finiteDiagonal]
      simp [Matrix.mul_fin_two, coe_upperHecke]
      exact ⟨⟨by ring, by linear_combination -hjt⟩, by ring⟩
    · intro i j'
      fin_cases i <;> fin_cases j'
      · exact add_mem ha (mul_mem (natCast_mem _ _) hc)
      · exact ht
      · exact mul_mem (natCast_mem _ p) hc
      · exact hd
    · rw [Matrix.det_fin_two_of, hdetk]
      linear_combination (K 1 0) * hjt

theorem mem_heckeSet_iff {g : FiniteAdelicGL ℚ 2} :
    g ∈ heckeSet N p ↔ ∃ ξ ∈ heckeReps N p, (finiteDiagonal ℚ 2 ξ)⁻¹ * g ∈ Gamma0Level N := by
  constructor
  · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    obtain ⟨ξ, hξ, h⟩ := exists_heckeReps_inv_mul_mem N p hk₁
    exact ⟨ξ, hξ, by simpa [mul_assoc] using mul_mem h hk₂⟩
  · rintro ⟨ξ, hξ, h⟩
    obtain ⟨k₁, hk₁, k₂, hk₂, he⟩ := finiteDiagonal_mem_heckeSet N p hξ
    refine ⟨k₁, hk₁, k₂ * ((finiteDiagonal ℚ 2 ξ)⁻¹ * g), mul_mem hk₂ h, ?_⟩
    rw [← mul_assoc, ← he, mul_inv_cancel_left]

theorem eq_of_inv_mul_mem_Gamma0Level {ξ ξ' : GL (Fin 2) ℚ} (hξ : ξ ∈ heckeReps N p)
    (hξ' : ξ' ∈ heckeReps N p)
    (h : (finiteDiagonal ℚ 2 ξ)⁻¹ * finiteDiagonal ℚ 2 ξ' ∈ Gamma0Level N) : ξ = ξ' := by
  have hprime : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := natCast_ne_zero_rat p
  rw [← map_inv, ← map_mul] at h
  obtain ⟨A, hA⟩ := exists_int_entries N h
  have hnot : ∀ m : ℤ, (m : ℚ) ≠ (p : ℚ)⁻¹ := by
    intro m hm
    have h1 : (m : ℚ) * p = 1 := by rw [hm, inv_mul_cancel₀ hp0]
    have h2 : m * (p : ℤ) = 1 := by exact_mod_cast h1
    have h3 : (p : ℤ) ∣ 1 := ⟨m, by linarith⟩
    have := Int.le_of_dvd one_pos h3
    have := hprime.two_le
    omega
  rcases (mem_heckeReps N p).1 hξ with ⟨i, rfl⟩ | ⟨-, rfl⟩ <;>
    rcases (mem_heckeReps N p).1 hξ' with ⟨j, rfl⟩ | ⟨-, rfl⟩
  · have e := hA 0 1
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_upperHecke_inv, coe_upperHecke] at e
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at e
    have e2 : (A 0 1 : ℚ) * p = (i : ℕ) - (j : ℕ) := by
      rw [e]; field_simp; push_cast; ring
    have e3 : A 0 1 * (p : ℤ) = ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) := by exact_mod_cast e2
    have hdvd : (p : ℤ) ∣ ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) := ⟨A 0 1, by linarith⟩
    have hi := i.isLt
    have hj := j.isLt
    have hlt : |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| < p := by
      rw [abs_lt]; constructor <;> omega
    have hij := Int.eq_zero_of_abs_lt_dvd hdvd hlt
    have : i = j := Fin.ext (by omega)
    rw [this]
  · exfalso
    have e := hA 0 0
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_upperHecke_inv, coe_lowerHecke] at e
    simp at e
    exact hnot _ e
  · exfalso
    have e := hA 1 1
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_lowerHecke_inv, coe_upperHecke] at e
    simp at e
    exact hnot _ e
  · rfl

omit [Fact p.Prime] in

theorem isCompact_Gamma0Level : IsCompact (Gamma0Level N : Set (FiniteAdelicGL ℚ 2)) :=
  (isCompact_integralFiniteGL ℚ 2).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_Gamma0Level N)) (Gamma0Level_le_integralFiniteGL N)

theorem heckeSet_eq_biUnion :
    heckeSet N p = ⋃ ξ ∈ heckeReps N p,
      finiteDiagonal ℚ 2 ξ • (Gamma0Level N : Set (FiniteAdelicGL ℚ 2)) := by
  ext g
  simp only [Set.mem_iUnion, mem_heckeSet_iff, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul,
    SetLike.mem_coe, exists_prop]

theorem isCompact_heckeSet : IsCompact (heckeSet N p) := by
  rw [heckeSet_eq_biUnion]
  exact (heckeReps N p).isCompact_biUnion fun ξ _ => (isCompact_Gamma0Level N).smul _

theorem isOpen_heckeSet : IsOpen (heckeSet N p) := by
  rw [heckeSet_eq_biUnion]
  exact isOpen_biUnion fun ξ _ => (isOpen_Gamma0Level N).smul _

omit [Fact p.Prime] in
theorem mul_mem_heckeSet_left {k g : FiniteAdelicGL ℚ 2} (hk : k ∈ Gamma0Level N) :
    k * g ∈ heckeSet N p ↔ g ∈ heckeSet N p := by
  constructor
  · rintro ⟨k₁, hk₁, k₂, hk₂, he⟩
    exact ⟨k⁻¹ * k₁, mul_mem (inv_mem hk) hk₁, k₂, hk₂, by rw [mul_assoc, mul_assoc, ← mul_assoc k₁, ← he, inv_mul_cancel_left]⟩
  · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    exact ⟨k * k₁, mul_mem hk hk₁, k₂, hk₂, by simp only [mul_assoc]⟩

omit [Fact p.Prime] in
theorem mul_mem_heckeSet_right {k g : FiniteAdelicGL ℚ 2} (hk : k ∈ Gamma0Level N) :
    g * k ∈ heckeSet N p ↔ g ∈ heckeSet N p := by
  constructor
  · rintro ⟨k₁, hk₁, k₂, hk₂, he⟩
    exact ⟨k₁, hk₁, k₂ * k⁻¹, mul_mem hk₂ (inv_mem hk), by rw [← mul_assoc, ← he, mul_inv_cancel_right]⟩
  · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    exact ⟨k₁, hk₁, k₂ * k, mul_mem hk₂ hk, by simp only [mul_assoc]⟩

end GL2Classical

end

end GroundTheory.Automorphic
