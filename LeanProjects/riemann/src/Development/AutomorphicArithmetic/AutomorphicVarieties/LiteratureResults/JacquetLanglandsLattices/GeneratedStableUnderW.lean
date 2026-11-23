import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LocF
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CompositionMem
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.BasicNotions MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.JL

namespace UpperTheory.V.Lit.JL.DiscreteSeriesWeights

section Abstract

variable {M : Type} [AddCommGroup M] [Module ℂ M]

private theorem comp_mem {ι : Type} (W : Module.End ℂ M) (μ : ι → ℂ) (hμ : Function.Injective μ) (Y : Submodule ℂ M)
    (hY : ∀ y ∈ Y, W y ∈ Y) (s : Finset ι) :
    ∀ x : ι → M, (∀ j, W (x j) = μ j • x j) → ∑ j ∈ s, x j ∈ Y → ∀ j ∈ s, x j ∈ Y :=
  _root_.UpperTheory.Reformulated.B.CompositionMem.comp_mem W μ hμ Y hY s

private structure Rel (W : Module.End ℂ M) (X : ℤˣ → Module.End ℂ M) : Prop where
  wx : ∀ (s : ℤˣ) x, W (X s x) = X s (W x) + (2 * ((s : ℤ) : ℂ) * Complex.I) • X s x
  xx : ∀ (s : ℤˣ) x, X (-s) (X s x) = X s (X (-s) x) + (4 * ((s : ℤ) : ℂ) * Complex.I) • W x

private def ext (V : Submodule ℂ M) (W : Module.End ℂ M) (X : ℤˣ → Module.End ℂ M) (k : ℕ) (s : ℤˣ) : Submodule ℂ M where
  carrier := {x | x ∈ V ∧ W x = (((s : ℤ) : ℂ) * Complex.I * (k + 2)) • x ∧ X (-s) x = 0}
  add_mem' := fun hx hy => ⟨V.add_mem hx.1 hy.1, by rw [map_add, hx.2.1, hy.2.1, smul_add], by rw [map_add, hx.2.2, hy.2.2, add_zero]⟩
  zero_mem' := ⟨V.zero_mem, by simp, by simp⟩
  smul_mem' := fun c x hx => ⟨V.smul_mem c hx.1, by rw [map_smul, hx.2.1, smul_comm], by rw [map_smul, hx.2.2, smul_zero]⟩

private def gen (V : Submodule ℂ M) (W : Module.End ℂ M) (X : ℤˣ → Module.End ℂ M) (k : ℕ) : Submodule ℂ M :=
  ⨆ p : ℤˣ × ℕ, (ext V W X k p.1).map (X p.1 ^ p.2)

variable {V : Submodule ℂ M} {W : Module.End ℂ M} {X : ℤˣ → Module.End ℂ M} {k : ℕ}

private theorem sq_sign (s : ℤˣ) : ((s : ℤ) : ℂ) * ((s : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp

private theorem wt (h : Rel W X) {s : ℤˣ} {u : M} (hu : u ∈ ext V W X k s) (n : ℕ) :
    W ((X s ^ n) u) = (((s : ℤ) : ℂ) * Complex.I * (k + 2 + 2 * n)) • (X s ^ n) u := by
  induction n with
  | zero => simpa using hu.2.1
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, h.wx, ih, map_smul, ← add_smul]
    congr 1
    push_cast
    ring

private theorem down (h : Rel W X) {s : ℤˣ} {u : M} (hu : u ∈ ext V W X k s) (n : ℕ) :
    X (-s) ((X s ^ (n + 1)) u) = (-4 * ((n : ℂ) + 1) * (k + 2 + n)) • (X s ^ n) u := by
  induction n with
  | zero =>
    rw [zero_add, pow_one, h.xx, hu.2.2, hu.2.1, map_zero, zero_add, smul_smul, pow_zero, Module.End.one_apply]
    congr 1
    push_cast
    linear_combination (4 * ((k : ℂ) + 2) * Complex.I ^ 2) * sq_sign s + 4 * ((k : ℂ) + 2) * Complex.I_sq
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, h.xx, ih, wt h hu, map_smul, smul_smul, ← Module.End.mul_apply, ← pow_succ', ← add_smul]
    congr 1
    push_cast
    linear_combination (4 * ((k : ℂ) + 2 + 2 * (n + 1)) * Complex.I ^ 2) * sq_sign s + 4 * ((k : ℂ) + 2 + 2 * (n + 1)) * Complex.I_sq

private theorem extract (h : Rel W X) {s : ℤˣ} {u : M} (hu : u ∈ ext V W X k s) (Y : Submodule ℂ M)
    (hY : ∀ y ∈ Y, X (-s) y ∈ Y) (n : ℕ) (hn : (X s ^ n) u ∈ Y) : u ∈ Y := by
  induction n with
  | zero => exact hn
  | succ n ih =>
    have h1 := hY _ hn
    rw [down h hu] at h1
    refine ih ((Y.smul_mem_iff (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_)).1 h1) <;> norm_cast <;> omega

private theorem mem_gen {s : ℤˣ} {u : M} (hu : u ∈ ext V W X k s) (n : ℕ) : (X s ^ n) u ∈ gen V W X k :=
  Submodule.mem_iSup_of_mem (s, n) ⟨u, hu, rfl⟩

private theorem gen_stable (T : Module.End ℂ M) (Y : Submodule ℂ M)
    (hT : ∀ s n, ∀ u ∈ ext V W X k s, T ((X s ^ n) u) ∈ Y) : ∀ x ∈ gen V W X k, T x ∈ Y := by
  have : gen V W X k ≤ Y.comap T := iSup_le fun p => by
    rintro _ ⟨u, hu, rfl⟩
    exact hT _ _ u hu
  exact this

private theorem gen_le (hV : ∀ s, ∀ x ∈ V, X s x ∈ V) : gen V W X k ≤ V :=
  gen_stable 1 V fun s n u hu => by
    induction n with
    | zero => exact hu.1
    | succ n ih => rw [pow_succ']; exact hV _ _ ih

private theorem generated_stable_under_W (h : Rel W X) : ∀ x ∈ gen V W X k, W x ∈ gen V W X k :=
  gen_stable _ _ fun s n u hu => by
    rw [wt h hu]
    exact Submodule.smul_mem _ _ (mem_gen hu n)

private theorem gen_X (h : Rel W X) (t : ℤˣ) : ∀ x ∈ gen V W X k, X t x ∈ gen V W X k :=
  gen_stable _ _ fun s n u hu => by
    by_cases e : t = s
    · subst e
      rw [← Module.End.mul_apply, ← pow_succ']
      exact mem_gen hu _
    · have e' : t = -s := Int.units_ne_iff_eq_neg.1 e
      subst e'
      cases n with
      | zero => rw [pow_zero, Module.End.one_apply, hu.2.2]; exact Submodule.zero_mem _
      | succ n => rw [down h hu]; exact Submodule.smul_mem _ _ (mem_gen hu n)

private structure Nor (V : Submodule ℂ M) (W : Module.End ℂ M) (X : ℤˣ → Module.End ℂ M) (T : Module.End ℂ M) (d : ℤˣ) : Prop where
  mem : ∀ x ∈ V, T x ∈ V
  tw : ∀ x, T (W x) = ((d : ℤ) : ℂ) • W (T x)
  tx : ∀ s, ∃ c : ℂ, c ≠ 0 ∧ ∀ x, T (X s x) = c • X (d * s) (T x)

private theorem Nor.of_comm {T : Module.End ℂ M} (h0 : ∀ x ∈ V, T x ∈ V) (h1 : ∀ x, T (W x) = W (T x))
    (h2 : ∀ s x, T (X s x) = X s (T x)) : Nor V W X T 1 :=
  ⟨h0, by simpa using h1, fun s => ⟨1, one_ne_zero, by simpa using h2 s⟩⟩

private theorem Nor.ext_mem {T : Module.End ℂ M} {d : ℤˣ} (hT : Nor V W X T d) {s : ℤˣ} {u : M} (hu : u ∈ ext V W X k s) :
    T u ∈ ext V W X k (d * s) := by
  refine ⟨hT.mem _ hu.1, ?_, ?_⟩
  · have h := congrArg (((d : ℤ) : ℂ) • ·) (hT.tw u)
    simp only [smul_smul, sq_sign, one_smul, hu.2.1, map_smul] at h
    rw [← h]
    congr 1
    push_cast
    ring
  · obtain ⟨c, hc, h⟩ := hT.tx (-s)
    have h1 := h u
    rw [hu.2.2, map_zero, mul_neg] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left hc

private theorem Nor.gen_mem {T : Module.End ℂ M} {d : ℤˣ} (hT : Nor V W X T d) : ∀ x ∈ gen V W X k, T x ∈ gen V W X k :=
  gen_stable _ _ fun s n u hu => by
    obtain ⟨c, -, h⟩ := hT.tx s
    have e : T ((X s ^ n) u) = c ^ n • (X (d * s) ^ n) (T u) := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', Module.End.mul_apply, h, ih, map_smul, smul_smul, pow_succ', pow_succ', Module.End.mul_apply]
    rw [e]
    exact Submodule.smul_mem _ _ (mem_gen (hT.ext_mem hu) n)

private theorem exists_ext (h : Rel W X) (Y : Submodule ℂ M) (hW : ∀ y ∈ Y, W y ∈ Y) (hX : ∀ s, ∀ y ∈ Y, X s y ∈ Y)
    {x : M} (hx : x ∈ gen V W X k) (hxY : x ∈ Y) (h0 : x ≠ 0) : ∃ s, ∃ u ∈ ext V W X k s, u ∈ Y ∧ u ≠ 0 := by
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx
  have hinj : Function.Injective fun p : ℤˣ × ℕ => ((p.1 : ℤ) : ℂ) * Complex.I * (k + 2 + 2 * p.2) := by
    rintro ⟨s, n⟩ ⟨t, l⟩ e
    have e1 : ((s : ℤ) : ℂ) * (k + 2 + 2 * n) = ((t : ℤ) : ℂ) * (k + 2 + 2 * l) :=
      mul_left_cancel₀ Complex.I_ne_zero (by linear_combination e)
    have e2 : (s : ℤ) * (k + 2 + 2 * n) = (t : ℤ) * (k + 2 + 2 * l) := by exact_mod_cast e1
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;> simp at e2 ⊢ <;> omega
  have hc := comp_mem W _ hinj Y hW f.support f (fun p => by
    obtain ⟨u, hu, e⟩ := hf p
    rw [← e]
    exact wt h hu _) hxY
  obtain ⟨p, hp, hp0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
  obtain ⟨u, hu, e⟩ := hf p
  refine ⟨p.1, u, hu, extract h hu Y (hX _) p.2 (e ▸ hc p hp), fun e0 => hp0 ?_⟩
  rw [← e, e0, map_zero]

end Abstract

section Units

variable {M : Type} [AddCommGroup M] [Module ℂ M]

private def wOp (E : Fin 2 → Fin 2 → Module.End ℂ M) : Module.End ℂ M := E 0 1 - E 1 0

private noncomputable def xOp (E : Fin 2 → Fin 2 → Module.End ℂ M) (s : ℤˣ) : Module.End ℂ M :=
  E 0 0 - E 1 1 + (((s : ℤ) : ℂ) * Complex.I) • (E 0 1 + E 1 0)

private theorem wOp_apply (E : Fin 2 → Fin 2 → Module.End ℂ M) (x : M) : wOp E x = E 0 1 x - E 1 0 x := rfl

private theorem xOp_apply (E : Fin 2 → Fin 2 → Module.End ℂ M) (s : ℤˣ) (x : M) :
    xOp E s x = E 0 0 x - E 1 1 x + (((s : ℤ) : ℂ) * Complex.I) • (E 0 1 x + E 1 0 x) := rfl

private theorem rel_of (E : Fin 2 → Fin 2 → Module.End ℂ M) (h : Formalism.REAL.GlRel E) : Rel (wOp E) (xOp E) := by
  have g : ∀ i j k l x, E i j (E k l x) = E k l (E i j x) + ((if j = k then E i l else 0) - (if l = i then E k j else 0)) x :=
    fun i j k l x => sub_eq_iff_eq_add'.1 (LinearMap.congr_fun (h i j k l) x)
  have a : ∀ x, E 0 0 (E 0 1 x) = E 0 1 (E 0 0 x) + E 0 1 x := fun x => by simpa using g 0 0 0 1 x
  have b : ∀ x, E 1 1 (E 0 1 x) = E 0 1 (E 1 1 x) + -E 0 1 x := fun x => by simpa using g 1 1 0 1 x
  have c : ∀ x, E 0 0 (E 1 0 x) = E 1 0 (E 0 0 x) + -E 1 0 x := fun x => by simpa using g 0 0 1 0 x
  have d : ∀ x, E 1 1 (E 1 0 x) = E 1 0 (E 1 1 x) + E 1 0 x := fun x => by simpa using g 1 1 1 0 x
  have e : ∀ x, E 0 1 (E 1 0 x) = E 1 0 (E 0 1 x) + (E 0 0 x - E 1 1 x) := fun x => by simpa using g 0 1 1 0 x
  have f : ∀ x, E 1 1 (E 0 0 x) = E 0 0 (E 1 1 x) := fun x => by simpa using g 1 1 0 0 x
  refine ⟨fun s x => ?_, fun s x => ?_⟩
  · simp only [wOp_apply, xOp_apply, map_add, map_sub, map_smul, a, b, c, d, e, f]
    rcases Int.units_eq_one_or s with rfl | rfl <;> match_scalars <;> push_cast <;> ring_nf <;> simp
  · simp only [wOp_apply, xOp_apply, map_add, map_sub, map_smul, a, b, c, d, e, f]
    rcases Int.units_eq_one_or s with rfl | rfl <;> match_scalars <;> push_cast <;> ring_nf <;> simp

private theorem nor_of (E : Fin 2 → Fin 2 → Module.End ℂ M) (V : Submodule ℂ M) (T : Module.End ℂ M) (hV : ∀ x ∈ V, T x ∈ V)
    (P : Fin 2 → Fin 2 → ℂ) (hT : ∀ i j x, T (E i j x) = ∑ k, ∑ l, (P k i * P l j) • E k l (T x)) (d : ℤˣ)
    (h1 : P 0 0 ^ 2 + P 0 1 ^ 2 = 1) (h2 : P 1 0 = -((d : ℤ) : ℂ) * P 0 1) (h3 : P 1 1 = ((d : ℤ) : ℂ) * P 0 0) :
    Nor V (wOp E) (xOp E) T d := by
  refine ⟨hV, fun x => ?_, fun s => ⟨(P 0 0 + ((s : ℤ) : ℂ) * Complex.I * P 0 1) ^ 2, pow_ne_zero _ fun e => ?_, fun x => ?_⟩⟩
  · simp only [wOp_apply, map_sub, hT, Fin.sum_univ_two, h2, h3]
    match_scalars
    · ring
    · linear_combination ((d : ℤ) : ℂ) * h1
    · linear_combination -((d : ℤ) : ℂ) * h1
    · ring
  · have hs := sq_sign s
    have : (1 : ℂ) = 0 := by
      linear_combination -h1 + (P 0 0 - ((s : ℤ) : ℂ) * Complex.I * P 0 1) * e + (P 0 1 ^ 2 * Complex.I ^ 2) * hs + P 0 1 ^ 2 * Complex.I_sq
    exact one_ne_zero this
  · simp only [xOp_apply, map_sub, map_add, map_smul, hT, Fin.sum_univ_two, h2, h3]
    have h4 : Complex.I ^ 3 = -Complex.I := Complex.I_pow_three
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or d with rfl | rfl <;> match_scalars <;> push_cast <;> ring_nf <;>
      simp only [Complex.I_sq, h4] <;> ring

private theorem unit_mem (E : Fin 2 → Fin 2 → Module.End ℂ M) (Y : Submodule ℂ M) (x : M) (c : ℂ) (hx : x ∈ Y) (hW : wOp E x ∈ Y)
    (hX : ∀ s, xOp E s x ∈ Y) (hc : E 0 0 x + E 1 1 x = c • x) (i j : Fin 2) : E i j x ∈ Y := by
  have hZ : E 0 0 x + E 1 1 x ∈ Y := hc ▸ Y.smul_mem c hx
  have hH : E 0 0 x - E 1 1 x ∈ Y := by
    have := Y.smul_mem (1 / 2 : ℂ) (Y.add_mem (hX 1) (hX (-1)))
    convert this using 1
    simp only [xOp_apply]
    match_scalars <;> push_cast <;> ring
  have hS : E 0 1 x + E 1 0 x ∈ Y := by
    have := Y.sub_mem (hX 1) hH
    rw [xOp_apply, add_sub_cancel_left] at this
    exact (Y.smul_mem_iff (by simp)).1 this
  rw [wOp_apply] at hW
  refine (Y.smul_mem_iff (two_ne_zero (α := ℂ))).1 ?_
  fin_cases i <;> fin_cases j
  · convert Y.add_mem hZ hH using 1; simp [two_smul]
  · convert Y.add_mem hS hW using 1; simp [two_smul]
  · convert Y.sub_mem hS hW using 1; simp [two_smul]
  · convert Y.sub_mem hZ hH using 1; simp [two_smul]

end Units

section Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem orth (a b c e : ℝ) (h1 : a * a + b * b = 1) (h2 : a * c + b * e = 0) (h3 : c * c + e * e = 1) :
    ∃ d : ℤˣ, c = -((d : ℤ) : ℝ) * b ∧ e = ((d : ℤ) : ℝ) * a := by
  have h : (a * e - b * c) * (a * e - b * c) = 1 := by
    linear_combination (c * c + e * e) * h1 + h3 - (a * c + b * e) * h2
  rcases mul_self_eq_one_iff.1 h with h | h
  · refine ⟨1, ?_, ?_⟩ <;> push_cast
    · linear_combination -c * h1 + a * h2 - b * h
    · linear_combination -e * h1 + b * h2 + a * h
  · refine ⟨-1, ?_, ?_⟩ <;> push_cast
    · linear_combination -c * h1 + a * h2 - b * h
    · linear_combination -e * h1 + b * h2 + a * h

omit [NumberField F] [IsTotallyReal F] in
private theorem row (k : TR.Kinf F 2) (v : InfinitePlace F) (i j : Fin 2) :
    k.1 i 0 v * k.1 j 0 v + k.1 i 1 v * k.1 j 1 v = if i = j then 1 else 0 := by
  have h := congrFun (congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 k.2) i) j) v
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply] at h
  split_ifs at h ⊢ <;> simpa using h

private theorem nor_cpt {V : Submodule ℂ (TR.Sm F 2)} (hV : TR.IsStable V) (k : TR.Kinf F 2) (v : InfinitePlace F) (d : ℤˣ)
    (h2 : k.1 1 0 v = -((d : ℤ) : ℝ) * k.1 0 1 v) (h3 : k.1 1 1 v = ((d : ℤ) : ℝ) * k.1 0 0 v) :
    Nor V (wOp (TR.Eop v)) (xOp (TR.Eop v)) (TR.cptRep F 2 k) d := by
  refine nor_of _ V _ (hV (.cpt k)) (fun i j => ((k.1 i j v : ℝ) : ℂ)) (fun i j x => ?_) d ?_ (by exact_mod_cast h2) (by exact_mod_cast h3)
  · have h := LinearMap.congr_fun (TR.Cen.rt_Eop (Unitary.toUnits k) v i j) x
    simp only [Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] at h
    exact h
  · have h := row k v 0 0
    rw [if_pos rfl, ← sq, ← sq] at h
    exact_mod_cast h

private theorem nor_comm {V : Submodule ℂ (TR.Sm F 2)} (v : InfinitePlace F) (T : Module.End ℂ (TR.Sm F 2)) (hV : ∀ x ∈ V, T x ∈ V)
    (h : ∀ i j x, T (TR.Eop v i j x) = TR.Eop v i j (T x)) : Nor V (wOp (TR.Eop v)) (xOp (TR.Eop v)) T 1 :=
  Nor.of_comm hV (fun x => by simp only [wOp_apply, map_sub, h]) fun s x => by simp only [xOp_apply, map_sub, map_add, map_smul, h]

private theorem eop_mem {V : Submodule ℂ (TR.Sm F 2)} (hV : TR.IsStable V) (v : InfinitePlace F) (i j : Fin 2) :
    ∀ x ∈ V, TR.Eop v i j x ∈ V := hV (.lie _)

private theorem w_mem {V : Submodule ℂ (TR.Sm F 2)} (hV : TR.IsStable V) (v : InfinitePlace F) :
    ∀ x ∈ V, wOp (TR.Eop v) x ∈ V := fun x hx => V.sub_mem (eop_mem hV v _ _ x hx) (eop_mem hV v _ _ x hx)

private theorem x_mem {V : Submodule ℂ (TR.Sm F 2)} (hV : TR.IsStable V) (v : InfinitePlace F) (s : ℤˣ) :
    ∀ x ∈ V, xOp (TR.Eop v) s x ∈ V := fun x hx =>
  V.add_mem (V.sub_mem (eop_mem hV v _ _ x hx) (eop_mem hV v _ _ x hx))
    (V.smul_mem _ (V.add_mem (eop_mem hV v _ _ x hx) (eop_mem hV v _ _ x hx)))

private theorem eop_comm {v w : InfinitePlace F} (h : v ≠ w) (i j k l : Fin 2) (x : TR.Sm F 2) :
    TR.Eop v i j (TR.Eop w k l x) = TR.Eop w k l (TR.Eop v i j x) := LinearMap.congr_fun (TR.Eop_comm h i j k l) x

private theorem gen_isStable {V : Submodule ℂ (TR.Sm F 2)} (hV : TR.IsStable V) (v : InfinitePlace F) (m : ℕ) (c : ℂ)
    (hc : HasCen V v c) : TR.IsStable (gen V (wOp (TR.Eop v)) (xOp (TR.Eop v)) m) := by
  classical
  have hr := rel_of _ (TR.glRel_Eop (a := 2) v)
  intro o
  cases o with
  | fin k => exact (nor_comm v _ (hV (.fin k)) fun i j x => (LinearMap.congr_fun (TR.lie_rt_fin _ k) x).symm).gen_mem
  | cpt k =>
    obtain ⟨d, h2, h3⟩ := orth _ _ _ _ (row k v 0 0) (row k v 0 1) (row k v 1 1)
    exact (nor_cpt hV k v d h2 h3).gen_mem
  | lie X =>
    intro x hx
    have e : X = ∑ i, ∑ j, ∑ w, X i j w • TR.toL (Matrix.single i j (Pi.single w (1 : ℝ) : TR.Rinf F)) := by
      funext a b u
      fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_two, Finset.sum_apply, Pi.single_apply]
    change TR.lie F 2 X x ∈ _
    rw [e]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun w _ => Submodule.smul_of_tower_mem _ _ ?_
    have key : TR.Eop w i j x ∈ gen V (wOp (TR.Eop v)) (xOp (TR.Eop v)) m := by
      by_cases h : w = v
      · subst h
        exact unit_mem _ _ x c hx (generated_stable_under_W hr x hx) (fun s => gen_X hr s x hx) (hc x (gen_le (x_mem hV w) hx)) i j
      · exact (nor_comm v _ (eop_mem hV w i j) (eop_comm h i j)).gen_mem x hx
    convert key using 1
    rfl

private theorem mem_ext_iff {V : Submodule ℂ (TR.Sm F 2)} (v : InfinitePlace F) (m : ℕ) (φ : TR.Sm F 2) :
    φ ∈ ext V (wOp (TR.Eop v)) (xOp (TR.Eop v)) m 1 ↔ φ ∈ V ∧ TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * (m + 2)) • φ ∧
      TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ) := by
  refine and_congr_right fun _ => and_congr ?_ ?_
  · rw [wOp_apply]; simp
  · rw [xOp_apply, add_eq_zero_iff_eq_neg, ← neg_smul]; simp

open Classical in

private noncomputable def flip (v : InfinitePlace F) (s : ℤˣ) : TR.Kinf F 2 :=
  ⟨Matrix.diagonal ![1, fun w => if w = v then ((s : ℤ) : ℝ) else 1], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j w
    rcases Int.units_eq_one_or s with rfl | rfl <;> fin_cases i <;> fin_cases j <;> by_cases h : w = v <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply, h]⟩

end Forms

end UpperTheory.V.Lit.JL.DiscreteSeriesWeights

open UpperTheory.V.Lit.JL.DiscreteSeriesWeights in
theorem UpperTheory.V.Lit.JL.dsAll :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : DiscG F) (m : InfinitePlace F → ℕ) (c : InfinitePlace F → ℂ), (∀ v, IsDS π.V v (m v) (c v)) → ∃ φ ∈ π.V, φ ≠ 0 ∧ (∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * (m v + 2)) • φ ∧ TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)) := by
  classical
  intro F _ _ _ π m c h
  let U : InfinitePlace F → ℤˣ → Submodule ℂ (TR.Sm F 2) := fun v => ext π.V (wOp (TR.Eop v)) (xOp (TR.Eop v)) (m v)
  have key : ∀ S : Finset (InfinitePlace F), ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∈ S, φ ∈ U w 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      obtain ⟨φ, h1, h2⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
      exact ⟨φ, h1, h2, by simp⟩
    | insert v S hv ih =>
      obtain ⟨φ, h1, h2, h3⟩ := ih
      obtain ⟨hc, ψ, p1, p2, p3⟩ := h v
      have hgen : gen π.V (wOp (TR.Eop v)) (xOp (TR.Eop v)) (m v) = π.V := by
        refine (π.irred _ (gen_le (x_mem π.stable v)) (gen_isStable π.stable v _ _ hc)).resolve_left fun e => p2 ?_
        have := mem_gen ((mem_ext_iff v (m v) ψ).2 ⟨p1, p3⟩) 0
        rw [e] at this
        exact this
      have hne : ∀ w ∈ S, v ≠ w := fun w hw e => hv (e ▸ hw)
      have hY : ∀ T : Module.End ℂ (TR.Sm F 2), (∀ w ∈ S, Nor π.V (wOp (TR.Eop w)) (xOp (TR.Eop w)) T 1) →
          ∀ y ∈ (⨅ w ∈ S, U w 1), T y ∈ (⨅ w ∈ S, U w 1) := fun T hT y hy => by
        simp only [Submodule.mem_iInf] at hy ⊢
        intro w hw
        have := (hT w hw).ext_mem (s := 1) (hy w hw)
        rwa [one_mul] at this
      obtain ⟨s, u, u1, u2, u3⟩ := exists_ext (rel_of _ (TR.glRel_Eop (a := 2) v)) (⨅ w ∈ S, U w 1)
        (hY _ fun w hw => nor_comm w _ (w_mem π.stable v) fun i j x => by
          simp only [wOp_apply, map_sub, eop_comm (hne w hw)])
        (fun s => hY _ fun w hw => nor_comm w _ (x_mem π.stable v s) fun i j x => by
          simp only [xOp_apply, map_sub, map_add, map_smul, eop_comm (hne w hw)])
        (hgen.ge h1) (by simpa only [Submodule.mem_iInf] using h3) h2
      refine ⟨TR.cptRep F 2 (DiscreteSeriesWeights.flip v s) u, π.stable (.cpt _) u u1.1, fun e => u3 ?_, fun w hw => ?_⟩
      · have := congrArg (TR.cptRep F 2 (DiscreteSeriesWeights.flip v s)⁻¹) e
        rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at this
      · rcases Finset.mem_insert.1 hw with rfl | hw
        · have := (nor_cpt π.stable (DiscreteSeriesWeights.flip w s) w s (by simp [DiscreteSeriesWeights.flip]) (by simp [DiscreteSeriesWeights.flip])).ext_mem u1
          rwa [Int.units_mul_self] at this
        · have := hY _ (fun w hw => nor_cpt π.stable (DiscreteSeriesWeights.flip v s) w 1 (by simp [DiscreteSeriesWeights.flip])
            (by simp [DiscreteSeriesWeights.flip, (hne w hw).symm])) u u2
          simp only [Submodule.mem_iInf] at this
          exact this w hw
  obtain ⟨φ, h1, h2, h3⟩ := key Finset.univ
  exact ⟨φ, h1, h2, fun v => ((mem_ext_iff v (m v) φ).1 (h3 v (Finset.mem_univ v))).2⟩
