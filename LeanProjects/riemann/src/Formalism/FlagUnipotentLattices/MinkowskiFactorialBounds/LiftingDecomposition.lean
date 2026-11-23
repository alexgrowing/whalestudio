import Formalism.FlagUnipotentLattices.LiftUnitaryFixesBase
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
import Formalism.HyperbolicPlaceProducts.SecondLevelArithmeticNorm

open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix

namespace Formalism.HermitianLatticeCounting.P

namespace CellDecomposition

section Cell

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

end Cell

end CellDecomposition

open CellDecomposition

namespace CellDecomposition

section Lift

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

lemma flag_vector_mem_base_lattice (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' := by
  refine Fin.lastCases ?_ (fun b => ?_) a
  · exact Submodule.mem_sup_right (Submodule.subset_span (by simp [FlagD.z]))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X F b))

lemma hermFlag_secondFrame_mem_frameSpan (F F' : FlagD H r) (a : Fin (r + 1)) : F'.e a ∈ V0 F F' := by
  refine Fin.lastCases ?_ (fun b => ?_) a
  · exact Submodule.mem_sup_right (Submodule.subset_span (by simp [FlagD.z]))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_right (e_mem_X F' b))

def perpL (H : HermSpace K V) (W : Submodule K V) : Submodule K V where
  carrier := {y | ∀ w ∈ W, H.B y w = 0}
  add_mem' := by
    intro a b ha hb w hw
    simp [ha w hw, hb w hw]
  zero_mem' := by intro w _; simp
  smul_mem' := by
    intro c a ha w hw
    simp [ha w hw]

lemma aniso_decomp [FiniteDimensional K V] (H : HermSpace K V) (W : Submodule K V)
    (hW : ∀ w ∈ W, H.B w w = 0 → w = 0) (y : V) :
    ∃! w : V, w ∈ W ∧ ∀ w' ∈ W, H.B (y - w) w' = 0 := by
  obtain ⟨v, hv, hvl⟩ := repr_aniso H W hW (H.B.flip y)
  refine ⟨v, ⟨hv, fun w' hw' => ?_⟩, ?_⟩
  · apply B_swap0
    rw [map_sub, hvl w' hw']
    simp
  · rintro v' ⟨hv', h'⟩
    have hd : v' - v ∈ W := W.sub_mem hv' hv
    apply sub_eq_zero.1
    apply hW _ hd
    have h1 : H.B (y - v) (v' - v) = 0 := by
      apply B_swap0
      rw [map_sub, hvl _ hd]
      simp
    have h2 := h' _ hd
    have e : v' - v = (y - v) - (y - v') := by abel
    calc H.B (v' - v) (v' - v) = H.B ((y - v) - (y - v')) (v' - v) := by rw [← e]
      _ = 0 := by rw [LinearMap.map_sub₂, h1, h2, sub_zero]

lemma aniso_isCompl [FiniteDimensional K V] (H : HermSpace K V) (W : Submodule K V)
    (hW : ∀ w ∈ W, H.B w w = 0 → w = 0) : IsCompl W (perpL H W) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    exact hW x hx (hx' x hx)
  · rw [codisjoint_iff, eq_top_iff]
    intro y _
    obtain ⟨w, ⟨hw, hw'⟩, -⟩ := aniso_decomp H W hW y
    have : y = w + (y - w) := by abel
    rw [this]
    exact Submodule.add_mem_sup hw hw'

end Lift

end CellDecomposition

theorem lifting_anisotropic : Formalism.HermitianLatticeCounting.S6.LiftAniso := by
  intro K V _ _ _ _ H r F F' Wt hA hA' hL w hw hww
  have h1 : w ∈ F.X := hA w (fun a => hL.1 w hw _ (flag_vector_mem_base_lattice F F' a)) hww
  have h2 : w ∈ F'.X := hA' w (fun a => hL.1 w hw _ (hermFlag_secondFrame_mem_frameSpan F F' a)) hww
  have : w ∈ Wt ⊓ II F F' := ⟨hw, h1, h2⟩
  rw [hL.2.1] at this
  exact (Submodule.mem_bot K).1 this

theorem lifting_unitary : Formalism.HermitianLatticeCounting.S6.LiftUnitary := by
  intro K V _ _ _ _ _ H r F F' Wt h hA hA' hL hh
  have han := lifting_anisotropic K V H r F F' Wt hA hA' hL
  have hc := aniso_isCompl H Wt han
  let g : V →ₗ[K] V := LinearMap.ofIsCompl hc (Wt.subtype ∘ₗ h) (perpL H Wt).subtype
  have hgW : ∀ w : Wt, g (w : V) = (h w : V) := fun w => by
    simp [g]
  have hgP : ∀ y : V, (∀ w ∈ Wt, H.B y w = 0) → g y = y := fun y hy => by
    have := LinearMap.ofIsCompl_apply_right hc (φ := Wt.subtype ∘ₗ h) (ψ := (perpL H Wt).subtype) ⟨y, hy⟩
    simpa [g] using this
  have hsplit : ∀ y : V, ∃ a : Wt, ∃ b : V, (∀ w ∈ Wt, H.B b w = 0) ∧ y = (a : V) + b := by
    intro y
    obtain ⟨w, ⟨hw, hw'⟩, -⟩ := aniso_decomp H Wt han y
    exact ⟨⟨w, hw⟩, y - w, hw', by simp⟩
  have hiso : ∀ x y : V, H.B (g x) (g y) = H.B x y := by
    intro x y
    obtain ⟨a, b, hb, rfl⟩ := hsplit x
    obtain ⟨c, d, hd, rfl⟩ := hsplit y
    have e1 : g ((a : V) + b) = (h a : V) + b := by rw [map_add, hgW, hgP b hb]
    have e2 : g ((c : V) + d) = (h c : V) + d := by rw [map_add, hgW, hgP d hd]
    rw [e1, e2]
    simp only [map_add, LinearMap.add_apply, hh, hb _ (h c).2, hb _ c.2,
      B_swap0 H (hd _ (h a).2), B_swap0 H (hd _ a.2)]
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply H.nondeg
    intro y
    rw [← hiso, hx]; simp
  refine ⟨g, ⟨⟨hiso, hgP⟩, ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩, hgW⟩, ?_⟩
  rintro g' ⟨⟨-, hP'⟩, -, hW'⟩
  ext y
  obtain ⟨a, b, hb, rfl⟩ := hsplit y
  rw [map_add, map_add, hgW, hW', hgP b hb, hP' b hb]

theorem lifting_fixes_base_vector : Formalism.HermitianLatticeCounting.S6.LiftUnitaryFixesBase := by
  intro K V _ _ _ _ H r F F' Wt g hL hg
  have h0 : ∀ y ∈ V0 F F', g y = y := fun y hy => hg.2 y (fun w hw => hL.1 w hw y hy)
  exact ⟨h0, fun a => h0 _ (flag_vector_mem_base_lattice F F' a), fun a => h0 _ (hermFlag_secondFrame_mem_frameSpan F F' a)⟩

theorem lifting_isometry_weight : Formalism.HermitianLatticeCounting.S6.LiftIsoW := by
  intro K V _ _ _ _ H r F F' j hj c Wt hNF hL
  obtain ⟨-, -, -, -, -, hk, hk', hs, hs'⟩ := hNF
  constructor
  · intro w hw
    obtain ⟨x, hx, hv⟩ := hs w hw
    obtain ⟨wt, hwt, i, hi, e⟩ := Submodule.mem_sup.1 (hL.2.2 _ hv)
    refine ⟨wt, ⟨hwt, ?_⟩, ?_⟩
    · have : w - wt = x + i := by rw [eq_sub_iff_add_eq] at e; rw [← e]; abel
      rw [this]; exact F.X.add_mem hx hi.1
    · rintro wt' ⟨hwt', hx'⟩
      have hX1 : w - wt ∈ F.X := by
        have : w - wt = x + i := by rw [eq_sub_iff_add_eq] at e; rw [← e]; abel
        rw [this]; exact F.X.add_mem hx hi.1
      have hd : wt' - wt ∈ F.X := by
        have : wt' - wt = (w - wt) - (w - wt') := by abel
        rw [this]; exact F.X.sub_mem hX1 hx'
      have hdW : wt' - wt ∈ Wt := Wt.sub_mem hwt' hwt
      have hI : wt' - wt ∈ II F F' := (hk _ hd).1 (fun y hy => hL.1 _ hdW y hy)
      have : wt' - wt ∈ Wt ⊓ II F F' := ⟨hdW, hI⟩
      rw [hL.2.1] at this
      exact sub_eq_zero.1 ((Submodule.mem_bot K).1 this)
  · intro w hw
    obtain ⟨x, hx, hv⟩ := hs' w hw
    obtain ⟨wt, hwt, i, hi, e⟩ := Submodule.mem_sup.1 (hL.2.2 _ hv)
    have hX1 : w - wt ∈ F'.X := by
      have : w - wt = x + i := by rw [eq_sub_iff_add_eq] at e; rw [← e]; abel
      rw [this]; exact F'.X.add_mem hx hi.2
    refine ⟨wt, ⟨hwt, hX1⟩, ?_⟩
    rintro wt' ⟨hwt', hx'⟩
    have hd : wt' - wt ∈ F'.X := by
      have : wt' - wt = (w - wt) - (w - wt') := by abel
      rw [this]; exact F'.X.sub_mem hX1 hx'
    have hdW : wt' - wt ∈ Wt := Wt.sub_mem hwt' hwt
    have hI : wt' - wt ∈ II F F' := (hk' _ hd).1 (fun y hy => hL.1 _ hdW y hy)
    have : wt' - wt ∈ Wt ⊓ II F F' := ⟨hdW, hI⟩
    rw [hL.2.1] at this
    exact sub_eq_zero.1 ((Submodule.mem_bot K).1 this)

theorem relIndex_intersection : Formalism.HermitianLatticeCounting.S6.RelIndexInter := by
  intro G _ abelian₂ M W La hle
  have hM : La ≤ M := hle.trans inf_le_left
  have hW : La ≤ W := hle.trans inf_le_right
  have e1 : (abelian₂ ⊓ W).relIndex La = abelian₂.relIndex La := by
    rw [← AddSubgroup.inf_relIndex_right, inf_assoc, inf_eq_right.2 hW, AddSubgroup.inf_relIndex_right]
  rw [e1, ← AddSubgroup.relIndex_addSubgroupOf hM]
  exact AddSubgroup.relIndex_dvd_index_of_normal _ _

theorem index_chain : Formalism.HermitianLatticeCounting.S6.IndexChain := by
  intro G _ abelian₂ L W La h1 h2 h0
  refine ⟨?_, ?_⟩
  · rw [mul_comm]; exact AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (relIndex_intersection G abelian₂ L W (L ⊓ W) le_rfl)

theorem pairs_loss_bound : Formalism.HermitianLatticeCounting.S6.PairsLoss := by
  intro C s k D' D'' NT Hh S' S'' hsk hH hS' hS'' hD' hD'' hNT h1 h2 h3
  have hb : D' * D'' * NT ≤ Hh ^ 3 * (S' * S'') ^ 2 := by
    calc D' * D'' * NT ≤ (Hh * S' ^ 2) * (Hh * S'' ^ 2) * Hh := by gcongr
      _ = Hh ^ 3 * (S' * S'') ^ 2 := by ring
  have hSS : 1 ≤ S' * S'' := by nlinarith
  calc (D' * D'' * NT) ^ (C * s) ≤ (Hh ^ 3 * (S' * S'') ^ 2) ^ (C * s) :=
        pow_le_pow_left₀ (by positivity) hb _
    _ = Hh ^ (3 * C * s) * (S' * S'') ^ (2 * C * s) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc 3, mul_assoc 2]
    _ ≤ Hh ^ (3 * C * s) * (S' * S'') ^ (2 * C * k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_right₀ hSS (Nat.mul_le_mul_left _ hsk)

lemma CellDecomposition.sum_half (n : ℕ) : ∑ s ∈ Finset.Icc 1 n, (1 / 2 : ℝ) ^ s = 1 - (1 / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

theorem ratio_sum_bound : Formalism.HermitianLatticeCounting.S6.RatioSum := by
  intro C k f g Hh hg hH hρ
  set ρ := ((C : ℝ) / g) ^ (k * f) * Hh ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f) with hρd
  have hρ0 : 0 ≤ ρ := by positivity
  have hterm : ∀ s ∈ Finset.Icc 1 (k - 1),
      ((C : ℝ) / g) ^ (s * k * f) * Hh ^ (C * s) * ((C * s * f : ℕ) : ℝ) ^ (4 * s * f) ≤ (1 / 2 : ℝ) ^ s := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    have hsk : s ≤ k := by omega
    have hc : ((C * s * f : ℕ) : ℝ) ≤ ((C * k * f : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsk)
    calc ((C : ℝ) / g) ^ (s * k * f) * Hh ^ (C * s) * ((C * s * f : ℕ) : ℝ) ^ (4 * s * f)
        ≤ ((C : ℝ) / g) ^ (s * k * f) * Hh ^ (C * s) * ((C * k * f : ℕ) : ℝ) ^ (4 * s * f) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (by positivity) hc _
      _ = ρ ^ s := by
          rw [hρd, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
          have e1 : s * k * f = k * f * s := by ring
          have e2 : 4 * s * f = 4 * f * s := by ring
          rw [e1, e2]
      _ ≤ (1 / 2 : ℝ) ^ s := pow_le_pow_left₀ hρ0 hρ _
  calc _ ≤ ∑ s ∈ Finset.Icc 1 (k - 1), (1 / 2 : ℝ) ^ s := Finset.sum_le_sum hterm
    _ = 1 - (1 / 2) ^ (k - 1) := sum_half _
    _ ≤ 1 := by have : (0 : ℝ) ≤ (1 / 2) ^ (k - 1) := by positivity
                linarith

theorem equal_rank_close : Formalism.HermitianLatticeCounting.S6.SEqKClose := by
  intro C k f g Hh NT hC hg hH hNT hNTH hρ
  set ρ := ((C : ℝ) / g) ^ (k * f) * Hh ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f) with hρd
  have hρ0 : 0 ≤ ρ := by positivity
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast (by omega : 2 ≤ C)
  have h1 : (2 / g) ^ (k * k * f) ≤ ((C : ℝ) / g) ^ (k * k * f) :=
    pow_le_pow_left₀ (by positivity) (by gcongr) _
  have h2 : ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) ≤ ((C * k * f : ℕ) : ℝ) ^ (4 * k * f) := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hC)
  have h3 : NT ^ k * Hh ^ ((C - 1) * k) ≤ Hh ^ (C * k) := by
    calc NT ^ k * Hh ^ ((C - 1) * k) ≤ Hh ^ k * Hh ^ ((C - 1) * k) := by gcongr
      _ = Hh ^ (C * k) := by
          rw [← pow_add]; congr 1
          obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
          simp; ring
  calc (2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * NT ^ k * Hh ^ ((C - 1) * k)
      = (2 / g) ^ (k * k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * k * f) * (NT ^ k * Hh ^ ((C - 1) * k)) := by ring
    _ ≤ ((C : ℝ) / g) ^ (k * k * f) * ((C * k * f : ℕ) : ℝ) ^ (4 * k * f) * Hh ^ (C * k) := by gcongr
    _ = ρ ^ k := by
        rw [hρd, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
        have e1 : k * k * f = k * f * k := by ring
        have e2 : 4 * k * f = 4 * f * k := by ring
        rw [e1, e2]; ring
    _ ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ hρ0 hρ _
    _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

theorem ratio_bound_alt : Formalism.HermitianLatticeCounting.S6.RatioBound := by
  intro C hC
  refine ⟨C ^ 2, ?_⟩
  intro k r f b g hb hf hlf hk hg
  have hexp : (2 * r + 2) ^ 2 = 4 * r ^ 2 + 8 * r + 4 := by ring
  have hm4 : 4 ≤ (2 * r + 2) ^ 2 := by omega
  have hC2 : C ≤ C ^ 2 := by nlinarith
  have hmk : (2 * r + 2) ^ 2 ≤ k := by nlinarith
  have hk4 : 4 ≤ k := by omega
  have hCk : C ≤ k := by nlinarith
  have hr4 : 4 * r ^ 2 ≤ k := by omega
  set n := k * f with hn
  have hn1 : 1 ≤ n := by rw [hn]; nlinarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hCk' : (C : ℝ) ≤ k := by exact_mod_cast hCk
  have hg0 : 0 < g := lt_of_lt_of_le (by positivity) hg
  have h1 : (C : ℝ) ^ n ≤ (k : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hCk' _
  have h2 : (b ^ (C * (2 * r + 2) ^ 2 * f)) ^ C ≤ b ^ n := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ hb1
    calc C * (2 * r + 2) ^ 2 * f * C = (C ^ 2 * (2 * r + 2) ^ 2) * f := by ring
      _ ≤ k * f := Nat.mul_le_mul_right _ hk
  have hfexp : (f : ℝ) ≤ b ^ (2 * r ^ 2) := by
    have hfpos : (0 : ℝ) < f := by exact_mod_cast (by omega : 0 < f)
    have h0 : (f : ℝ) ≤ Real.exp ((r : ℝ) ^ 2) := (Real.log_le_iff_le_exp hfpos).1 hlf
    have e : Real.exp ((r : ℝ) ^ 2) = Real.exp 1 ^ (r ^ 2) := by
      rw [Real.exp_one_pow]; push_cast; rfl
    have he : Real.exp 1 ≤ b ^ 2 := by have := Real.exp_one_lt_d9; nlinarith
    calc (f : ℝ) ≤ Real.exp 1 ^ (r ^ 2) := by rw [← e]; exact h0
      _ ≤ (b ^ 2) ^ (r ^ 2) := pow_le_pow_left₀ (Real.exp_pos 1).le he _
      _ = b ^ (2 * r ^ 2) := by rw [← pow_mul]
  have h3 : ((C * k * f : ℕ) : ℝ) ^ (4 * f) ≤ (k : ℝ) ^ n * (k : ℝ) ^ n * b ^ (2 * n) := by
    push_cast
    rw [mul_pow, mul_pow]
    have a2 : (k : ℝ) ^ (4 * f) ≤ (k : ℝ) ^ n := pow_le_pow_right₀ hk1 (Nat.mul_le_mul_right _ hk4)
    have a1 : (C : ℝ) ^ (4 * f) ≤ (k : ℝ) ^ n := (pow_le_pow_left₀ (by positivity) hCk' _).trans a2
    have a3 : (f : ℝ) ^ (4 * f) ≤ b ^ (2 * n) :=
      calc (f : ℝ) ^ (4 * f) ≤ (b ^ (2 * r ^ 2)) ^ (4 * f) := pow_le_pow_left₀ (by positivity) hfexp _
        _ = b ^ (2 * r ^ 2 * (4 * f)) := (pow_mul _ _ _).symm
        _ ≤ b ^ (2 * n) := pow_le_pow_right₀ hb1 (by
            calc 2 * r ^ 2 * (4 * f) = 2 * ((4 * r ^ 2) * f) := by ring
              _ ≤ 2 * (k * f) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hr4))
    gcongr
  have h4 : (k : ℝ) ^ (8 * n) * b ^ (8 * n) ≤ g ^ n := by
    calc (k : ℝ) ^ (8 * n) * b ^ (8 * n) = (((k : ℝ) * b) ^ 8) ^ n := by rw [← pow_mul, mul_pow]
      _ ≤ g ^ n := pow_le_pow_left₀ (by positivity) hg _
  have h5 : 2 ≤ b ^ n := hb.trans (le_self_pow₀ hb1 (by omega))
  have hgn : 0 < g ^ n := by positivity
  have h6 : (k : ℝ) ^ (3 * n) * b ^ (3 * n) * 2 ≤ (k : ℝ) ^ (8 * n) * b ^ (8 * n) := by
    calc (k : ℝ) ^ (3 * n) * b ^ (3 * n) * 2 ≤ (k : ℝ) ^ (3 * n) * b ^ (3 * n) * b ^ n := by gcongr
      _ = (k : ℝ) ^ (3 * n) * b ^ (4 * n) := by rw [mul_assoc, ← pow_add]; congr 2; ring
      _ ≤ (k : ℝ) ^ (8 * n) * b ^ (8 * n) :=
          mul_le_mul (pow_le_pow_right₀ hk1 (by omega)) (pow_le_pow_right₀ hb1 (by omega))
            (by positivity) (by positivity)
  rw [div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hgn]
  calc (C : ℝ) ^ n * (b ^ (C * (2 * r + 2) ^ 2 * f)) ^ C * ((C * k * f : ℕ) : ℝ) ^ (4 * f)
      ≤ (k : ℝ) ^ n * b ^ n * ((k : ℝ) ^ n * (k : ℝ) ^ n * b ^ (2 * n)) := by gcongr
    _ = (k : ℝ) ^ (3 * n) * b ^ (3 * n) := by ring
    _ ≤ 1 / 2 * g ^ n := by linarith

end Formalism.HermitianLatticeCounting.P
