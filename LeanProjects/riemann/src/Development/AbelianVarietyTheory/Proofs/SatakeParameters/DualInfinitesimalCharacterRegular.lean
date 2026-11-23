import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL

noncomputable section

open NumberField Matrix Topology GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL

namespace GlobalTheory.AlgInfChar

section Lin

variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem exists_joint_eigenvector {ι : Type} (T : ι → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i)
    (W : Submodule ℂ V) (h0 : W ≠ ⊥) (hW : ∀ i, ∀ v ∈ W, T i v ∈ W) :
    ∃ v ∈ W, v ≠ 0 ∧ ∃ c : ι → ℂ, ∀ i, T i v = c i • v := by
  obtain ⟨U, ⟨hU0, hUW, hU⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Submodule ℂ V))
    {U | U ≠ ⊥ ∧ U ≤ W ∧ ∀ i, ∀ v ∈ U, T i v ∈ U} ⟨W, h0, le_rfl, hW⟩
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU0
  have key : ∀ i, ∃ c : ℂ, ∀ v ∈ U, T i v = c • v := by
    intro i
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((T i).restrict (hU i))
    obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
    have hx1 : T i x = c • (x : V) := congrArg Subtype.val hx.apply_eq_smul
    refine ⟨c, ?_⟩
    have h1 : U ⊓ Module.End.eigenspace (T i) c = U := by
      refine (inf_le_left.eq_or_lt).resolve_right (hmin _ ⟨?_, inf_le_left.trans hUW, fun j v hv => ⟨hU j v hv.1, ?_⟩⟩)
      · exact (Submodule.ne_bot_iff _).2 ⟨x, ⟨x.2, Module.End.mem_eigenspace_iff.2 hx1⟩,
          fun h => hx.2 (Subtype.ext h)⟩
      · have h2 := Module.End.mem_eigenspace_iff.1 hv.2
        refine Module.End.mem_eigenspace_iff.2 ?_
        rw [← Module.End.mul_apply, hT, Module.End.mul_apply, h2, map_smul]
    intro v hv
    rw [← h1] at hv
    exact Module.End.mem_eigenspace_iff.1 hv.2
  choose c hc using key
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hU0
  exact ⟨v, hUW hv, hv0, c, fun i => hc i v hv⟩

theorem exists_nat_of_primitive (e f h : Module.End ℂ V) (hef : e * f - f * e = h) (hf : h * f - f * h = (-2 : ℂ) • f)
    (v : V) (μ : ℂ) (hv : v ≠ 0) (he : e v = 0) (hh : h v = μ • v) : ∃ m : ℕ, μ = (m : ℂ) := by
  have h1 : ∀ n : ℕ, h ((f ^ n) v) = (μ - 2 * n) • (f ^ n) v := by
    intro n
    induction n with
    | zero => simpa using hh
    | succ n ih =>
      have h2 := LinearMap.congr_fun hf ((f ^ n) v)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, ih, map_smul] at h2
      rw [pow_succ', Module.End.mul_apply, sub_eq_iff_eq_add.1 h2, ← add_smul]
      congr 1; push_cast; ring
  have h2 : ∀ n : ℕ, e ((f ^ (n + 1)) v) = ((n + 1) * (μ - n)) • (f ^ n) v := by
    intro n
    induction n with
    | zero =>
      have h3 := LinearMap.congr_fun hef v
      simpa [he, hh] using h3
    | succ n ih =>
      have h3 := LinearMap.congr_fun hef ((f ^ (n + 1)) v)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, ih, map_smul, h1] at h3
      rw [pow_succ' f (n + 1), Module.End.mul_apply, sub_eq_iff_eq_add.1 h3, ← Module.End.mul_apply f (f ^ n),
        ← pow_succ', ← add_smul]
      congr 1; push_cast; ring
  by_contra hno
  push Not at hno
  have h3 : ∀ n : ℕ, (f ^ n) v ≠ 0 := by
    intro n
    induction n with
    | zero => simpa using hv
    | succ n ih =>
      intro h0
      have h4 := h2 n
      rw [h0, map_zero, eq_comm, smul_eq_zero] at h4
      rcases h4 with h4 | h4
      · rcases mul_eq_zero.1 h4 with h5 | h5
        · exact Nat.cast_add_one_ne_zero n h5
        · exact hno n (sub_eq_zero.1 h5)
      · exact ih h4
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => μ - 2 * (n : ℂ)) (s := {c | h.HasEigenvalue c})
    (fun n m hnm => ?_) (fun n => ?_) (Module.End.finite_hasEigenvalue h)
  · have : (n : ℂ) = m := by linear_combination (-1 / 2 : ℂ) * hnm
    exact Nat.cast_injective this
  · exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (h1 n), h3 n⟩

theorem exists_highest [Nontrivial V] (n : ℕ) (F : Fin n → Fin n → Module.End ℂ V) (hF : Formalism.REAL.GlRel F) :
    ∃ (ν : Fin n → ℂ) (v : V), v ≠ 0 ∧ Formalism.REAL.IsHW F ν v ∧ ∀ i j, i < j → ∃ m : ℕ, ν i - ν j = (m : ℂ) := by
  have hc : ∀ k i j, F k k * F i j - F i j * F k k =
      ((if k = i then (1 : ℂ) else 0) - (if j = k then 1 else 0)) • F i j := by
    intro k i j
    rw [hF]
    by_cases h1 : k = i <;> by_cases h2 : j = k <;> simp_all
  let H : Module.End ℂ V := ∑ k : Fin n, ((k : ℕ) : ℂ) • F k k
  have hH : ∀ i j, H * F i j = F i j * H + (((i : ℕ) : ℂ) - (j : ℕ)) • F i j := by
    intro i j
    rw [← sub_eq_iff_eq_add', Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, hc, smul_smul, ← Finset.sum_smul]
    simp [mul_sub]
  obtain ⟨l, hl, hmin⟩ := Set.exists_min_image {c | H.HasEigenvalue c} Complex.re (Module.End.finite_hasEigenvalue H)
    (Module.End.exists_eigenvalue H)
  obtain ⟨v, hv, hv0, ν, hν⟩ := exists_joint_eigenvector (fun k => F k k)
    (fun i j => by rw [← sub_eq_zero, hc]; by_cases h : i = j <;> simp [h, eq_comm]) (H.eigenspace l) hl
    (fun k v hv => by
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [← Module.End.mul_apply, hH]
      simp [hv])
  rw [Module.End.mem_eigenspace_iff] at hv
  have hup : ∀ i j, i < j → F i j v = 0 := by
    intro i j hij
    by_contra h0
    have h1 : H (F i j v) = (l + (((i : ℕ) : ℂ) - (j : ℕ))) • F i j v := by
      rw [← Module.End.mul_apply, hH]
      simp [hv, add_smul]
    have h2 := hmin _ (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h1, h0⟩)
    simp at h2
    exact absurd hij (not_lt.2 h2)
  refine ⟨ν, v, hv0, ⟨hν, hup⟩, fun i j hij => exists_nat_of_primitive (F i j) (F j i) (F i i - F j j) ?_ ?_ v _ hv0
    (hup i j hij) ?_⟩
  · rw [hF]; simp
  · have h1 := hc i j i
    have h2 := hc j j i
    simp only [hij.ne, if_false, if_true] at h1 h2
    rw [sub_mul, mul_sub]
    linear_combination (norm := module) h1 - h2
  · simp [hν, sub_smul]

end Lin

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

section Diff

open scoped Matrix.Norms.Operator

def dCL (Ξ : AlgRep E a) : Lie E a →L[ℝ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ := LinearMap.toContinuousLinearMap Ξ.dmat

theorem hasDerivAt_mat (Ξ : AlgRep E a) (c : ℝ → GL (Fin a) (Cinf E)) (X : Lie E a) (h0 : c 0 = 1)
    (hc : HasDerivAt (fun t => toL (c t).val) X 0) : HasDerivAt (fun t => Ξ.mat (c t)) (Ξ.dmat X) 0 :=
  (hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => Ξ.hasDerivAt_curve c X h0 hc i j :
    HasDerivAt (fun t => Matrix.of.symm (Ξ.mat (c t))) (Matrix.of.symm (Ξ.dmat X)) 0)

theorem dmat_bracket (Ξ : AlgRep E a) (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    Ξ.dmat (toL X) * Ξ.dmat (toL Y) - Ξ.dmat (toL Y) * Ξ.dmat (toL X) = Ξ.dmat (toL (X * Y - Y * X)) := by
  let c : ℝ → GL (Fin a) (Cinf E) := fun t => (Matrix.isUnit_exp (t • X)).unit
  have h0 : c 0 = 1 := Units.ext (by simp [c])
  have hi : ∀ t, ((c t)⁻¹).val = NormedSpace.exp (t • -X) := fun t => by
    rw [smul_neg, Matrix.exp_neg, Matrix.coe_units_inv]; rfl
  have h1 : HasDerivAt (fun t => (c t).val) X 0 := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  have h2 : HasDerivAt (fun t => ((c t)⁻¹).val) (-X) 0 := by
    simp only [hi]
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  have h3 : HasDerivAt (fun t => (c t).val * Y * ((c t)⁻¹).val) (X * Y - Y * X) 0 := by
    have h := (h1.mul_const Y).mul h2
    simp only [h0, inv_one, Units.val_one, mul_one, one_mul, mul_neg, ← sub_eq_add_neg] at h
    exact h
  have h4 := hasDerivAt_mat Ξ c (toL X) h0 h1
  have h3' : HasDerivAt (fun t => toL ((c t).val * Y * ((c t)⁻¹).val)) (toL (X * Y - Y * X)) 0 := h3
  have h5 := ((dCL Ξ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3').mul h4
  have h6 := (h4.mul_const (Ξ.dmat (toL Y))).unique
    (h5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => Ξ.mat_mul_dmat (c t) Y))
  simp only [Function.comp_apply, h0, inv_one, Units.val_one, mul_one, one_mul, map_one] at h6
  rw [h6]
  exact add_sub_cancel_right _ _

theorem isPreconnected_invSet : IsPreconnected (invSet E a) := by
  refine isPreconnected_of_forall (oneL E a) fun y hy => ?_
  let B : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of y - 1
  let x : ℂ → Lie E a := fun s => toL (1 + s • B)
  let p : InfinitePlace E → Polynomial ℂ := fun w =>
    (1 + (Polynomial.X : Polynomial ℂ) • B.map fun z => Polynomial.C (z w)).det
  have hp : ∀ w s, (p w).eval s = (1 + s • B).det w := by
    intro w s
    refine ((Polynomial.evalRingHom s).map_det _).trans (Eq.trans ?_ ((Pi.evalRingHom (fun _ => ℂ) w).map_det _).symm)
    congr 1
    ext i j
    by_cases h : i = j <;> simp [h] <;> ring
  have hc : {s | x s ∉ invSet E a}.Countable := by
    refine (Set.countable_iUnion fun w => (Polynomial.finite_setOf_isRoot (p := p w) fun h => ?_).countable).mono
      fun s hs => ?_
    · simpa [h] using hp w 0
    · have h : ¬ IsUnit (1 + s • B).det := fun h => hs ((Matrix.isUnit_iff_isUnit_det _).2 h)
      rw [Pi.isUnit_iff, not_forall] at h
      obtain ⟨w, hw⟩ := h
      exact Set.mem_iUnion.2 ⟨w, (hp w s).trans (by simpa using hw)⟩
  have hx : Continuous x := (continuous_const.add (continuous_id.smul continuous_const) :
    Continuous fun s : ℂ => toL 1 + s • toL B)
  have e0 : x 0 = oneL E a := by simp [x]
  have e1 : x 1 = y := by simp [x, B]
  refine ⟨x '' {s | x s ∉ invSet E a}ᶜ, ?_, ⟨0, ?_, e0⟩, ⟨1, ?_, e1⟩,
    (hc.isPathConnected_compl_of_one_lt_rank (by simp)).isConnected.isPreconnected.image _ hx.continuousOn⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact not_not.1 hs
  · exact not_not.2 (e0 ▸ isUnit_one)
  · exact not_not.2 (e1 ▸ hy)

theorem commute_mat (Ξ : AlgRep E a) (Z : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (hZ : ∀ X, Z * Ξ.dmat X = Ξ.dmat X * Z)
    (y : GL (Fin a) (Cinf E)) : Z * Ξ.mat y = Ξ.mat y * Z := by
  let M : Lie E a → Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ := fun x => Matrix.of fun i j => extGL (fun y => Ξ.mat y i j) x
  have hM : ∀ u : GL (Fin a) (Cinf E), M (toL u.val) = Ξ.mat u := fun u => by
    ext i j; exact extGL_val (fun y => Ξ.mat y i j) u
  have hU : ∀ x ∈ invSet E a, IsUnit (M x) := by
    rintro x ⟨u, hu⟩
    have e : x = toL u.val := hu.symm
    rw [e, hM]
    exact (Group.isUnit u).map Ξ.mat
  have hd : ∀ x ∈ invSet E a, DifferentiableAt ℝ M x := fun x hx =>
    (differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => differentiableAt_extGL (Ξ.reg i j) hx :
      DifferentiableAt ℝ (fun x => Matrix.of.symm (M x)) x)
  have h1 : HasFDerivAt M (dCL Ξ) (oneL E a) := by
    have h : HasFDerivAt (fun x => Matrix.of.symm (M x)) _ (oneL E a) :=
      hasFDerivAt_pi.2 fun i => hasFDerivAt_pi.2 fun j =>
        (differentiableAt_extGL (Ξ.reg i j) (x := oneL E a) isUnit_one).hasFDerivAt
    exact h
  let G : Lie E a → Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ := fun x => M x * Z * Ring.inverse (M x)
  have hG : ∀ x ∈ invSet E a, DifferentiableAt ℝ G x := fun x hx =>
    ((hd x hx).mul_const Z).mul ((hd x hx).inverse (hU x hx))
  have hGM : ∀ x ∈ invSet E a, G x * M x = M x * Z := fun x hx => by
    simp only [G]
    rw [mul_assoc, Ring.inverse_mul_cancel _ (hU x hx), mul_one]
  have h2 : Set.EqOn (fderiv ℝ G) 0 (invSet E a) := by
    intro x hx
    obtain ⟨u, hu⟩ := id hx
    obtain rfl : x = toL u.val := hu.symm
    have e1 : lmul (toL (u⁻¹).val) (toL u.val) = oneL E a := u.inv_mul
    have h3 := ((HasFDerivAt.comp (toL u.val) (e1.symm ▸ h1) (lmul (toL (u⁻¹).val)).hasFDerivAt).const_mul
      (Ξ.mat u)).congr_of_eventuallyEq (f₁ := M) (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hx) fun z hz => by
        obtain ⟨v, hv⟩ := hz
        obtain rfl : z = toL v.val := hv.symm
        have e2 : lmul (toL (u⁻¹).val) (toL v.val) = toL (u⁻¹ * v).val := rfl
        simp only [Function.comp_apply, e2, hM, ← map_mul, mul_inv_cancel_left])
    have h4 := (h3.mul_const' Z).unique (((hG _ hx).hasFDerivAt.mul' h3).congr_of_eventuallyEq
      (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hx) fun z hz => (hGM z hz).symm))
    ext1 v
    have h5 := congrArg (fun L : Lie E a →L[ℝ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ => L v) h4
    have h6 := hGM _ hx
    rw [hM] at h6
    have h7 : Ξ.mat u * Ξ.dmat (lmul (toL (u⁻¹).val) v) * Z =
      G (toL u.val) * (Ξ.mat u * Ξ.dmat (lmul (toL (u⁻¹).val) v)) + fderiv ℝ G (toL u.val) v * M (toL u.val) := h5
    rw [← mul_assoc, h6, mul_assoc _ Z, hZ, mul_assoc, left_eq_add] at h7
    exact (hU _ hx).mul_left_eq_zero.1 h7
  have h3 := isOpen_invSet.is_const_of_fderiv_eq_zero isPreconnected_invSet
    (fun x hx => (hG x hx).differentiableWithinAt) h2 (val_mem_invSet y) (val_mem_invSet 1)
  have h4 := hGM _ (val_mem_invSet y)
  rw [h3, hM] at h4
  simpa only [G, hM, map_one, one_mul, Ring.inverse_one, mul_one] using h4

end Diff

omit [NumberField E] in

def expDiag (δ : Fin a → Cinf E) : GL (Fin a) (Cinf E) :=
  ⟨diagonal fun l w => Complex.exp (δ l w), diagonal fun l w => Complex.exp (-δ l w),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr; funext l w; simp [← Complex.exp_add],
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr; funext l w; simp [← Complex.exp_add]⟩

omit [NumberField E] in

theorem expDiag_add (δ δ' : Fin a → Cinf E) : expDiag (δ + δ') = expDiag δ * expDiag δ' := Units.ext (by
  change diagonal _ = diagonal _ * diagonal _
  rw [diagonal_mul_diagonal]; congr; funext l w; simp [Complex.exp_add])

omit [NumberField E] in

theorem expDiag_zero : expDiag (0 : Fin a → Cinf E) = 1 := Units.ext (by
  change diagonal _ = 1
  rw [← diagonal_one]; congr; funext l w; simp)

theorem hasDerivAt_expDiag (δ : Fin a → Cinf E) :
    HasDerivAt (fun t : ℝ => toL (expDiag (t • δ)).val) (toL (diagonal δ)) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w => ?_
  by_cases h : i = j
  · subst h
    simpa [expDiag] using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (δ i w)).cexp
  · simpa [expDiag, h] using hasDerivAt_const (0 : ℝ) (0 : ℂ)

def expChar (p : ℤ × ℤ) : Multiplicative ℂ →* ℂ where
  toFun z := Complex.exp (p.1 * z.toAdd + p.2 * starRingEnd ℂ z.toAdd)
  map_one' := by simp
  map_mul' x y := by rw [← Complex.exp_add]; congr 1; simp only [toAdd_mul, map_add]; ring

def laurent : Submodule ℂ (Multiplicative ℂ → ℂ) :=
  Submodule.span ℂ ((fun f : Multiplicative ℂ →* ℂ => (f : Multiplicative ℂ → ℂ)) '' Set.range expChar)

theorem expChar_mem (p : ℤ × ℤ) : (expChar p : Multiplicative ℂ → ℂ) ∈ laurent :=
  Submodule.subset_span ⟨_, ⟨p, rfl⟩, rfl⟩

theorem laurent_mul {f g : Multiplicative ℂ → ℂ} (hf : f ∈ laurent) (hg : g ∈ laurent) : f * g ∈ laurent := by
  have h := Submodule.mul_mem_mul hf hg
  rw [laurent, Submodule.span_mul_span] at h
  refine Submodule.span_le.2 ?_ h
  rintro _ ⟨_, ⟨_, ⟨p, rfl⟩, rfl⟩, _, ⟨_, ⟨q, rfl⟩, rfl⟩, rfl⟩
  suffices e : (expChar p : Multiplicative ℂ → ℂ) * expChar q = expChar (p + q) from
    (show (expChar p : Multiplicative ℂ → ℂ) * expChar q ∈ laurent from e ▸ expChar_mem (p + q))
  funext z
  simp only [expChar, Pi.mul_apply, MonoidHom.coe_mk, OneHom.coe_mk, ← Complex.exp_add, Prod.fst_add, Prod.snd_add]
  congr 1; push_cast; ring

omit [NumberField E] in

theorem exists_coord_exp (τ τ' : E →+* ℂ) : ∃ p : ℤ × ℤ, ∀ z : Multiplicative ℂ,
    coord τ' (fun w => Complex.exp (atEmb τ z.toAdd w)) = expChar p z := by
  classical
  by_cases hw : InfinitePlace.mk τ' = InfinitePlace.mk τ
  · unfold coord atEmb
    rw [hw]
    split_ifs
    · exact ⟨(1, 0), fun z => by simp [expChar]⟩
    · exact ⟨(0, 1), fun z => by simp [expChar]⟩
    · exact ⟨(0, 1), fun z => by simp [expChar, ← Complex.exp_conj]⟩
    · exact ⟨(1, 0), fun z => by simp [expChar, ← Complex.exp_conj]⟩
  · refine ⟨0, fun z => ?_⟩
    unfold coord atEmb
    split_ifs <;> simp [expChar, Pi.single_eq_of_ne hw]

omit [NumberField E] in

def torus (τ : E →+* ℂ) (k : Fin a) (z : ℂ) : GL (Fin a) (Cinf E) := expDiag (Pi.single k (atEmb τ z))

omit [NumberField E] in

theorem reg_torus (τ : E →+* ℂ) (k : Fin a) {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) :
    (fun z : Multiplicative ℂ => f (torus τ k z.toAdd)) ∈ laurent := by
  have h1 : (1 : Multiplicative ℂ → ℂ) ∈ laurent := by
    convert expChar_mem 0 using 1
    funext z; simp [expChar]
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with ⟨τ', i, j, rfl⟩ | ⟨τ', rfl⟩
    · obtain ⟨p, hp⟩ := exists_coord_exp τ τ'
      by_cases h : i = j
      · subst h
        by_cases h : i = k
        · subst h
          convert expChar_mem p using 1
          funext z
          simpa [torus, expDiag] using hp z
        · convert h1 using 1
          funext z
          simp only [torus, expDiag, diagonal_apply_eq, Pi.single_eq_of_ne h, Pi.zero_apply, Complex.exp_zero]
          exact map_one (coord τ')
      · convert laurent.zero_mem using 1
        funext z
        simp [torus, expDiag, h]
    · obtain ⟨p, hp⟩ := exists_coord_exp τ τ'
      convert expChar_mem (-p) using 1
      funext z
      have e : (torus τ k z.toAdd).val.det = fun w => Complex.exp (atEmb τ z.toAdd w) := by
        change (diagonal _).det = _
        rw [det_diagonal, Finset.prod_eq_single k]
        · simp
        · intro l _ hl; funext w; simp [hl]
        · simp
      beta_reduce
      rw [e, hp]
      simp only [expChar, MonoidHom.coe_mk, OneHom.coe_mk, ← Complex.exp_neg, Prod.fst_neg, Prod.snd_neg]
      congr 1; push_cast; ring
  | algebraMap c => convert laurent.smul_mem c h1 using 1; funext z; simp
  | add f g _ _ h1 h2 => exact laurent.add_mem h1 h2
  | mul f g _ _ h1 h2 => exact laurent_mul h1 h2

theorem eigenvalue_int (Ξ : AlgRep E a) (τ : E →+* ℂ) (k : Fin a) (v : Fin Ξ.d → ℂ) (c : ℂ) (hv : v ≠ 0)
    (h : dualE Ξ τ k k *ᵥ v = c • v) : ∃ n : ℤ, c = (n : ℂ) := by
  have hadd : ∀ z z', torus τ k (z + z') = torus τ k z * torus τ k z' := fun z z' => by
    rw [torus, torus, torus, ← expDiag_add, ← Pi.single_add, atEmb_eq τ (z + z'), atEmb_eq τ z, atEmb_eq τ z']
    congr 2
    simp only [Complex.add_re, Complex.add_im, add_smul]; abel
  have hsm : ∀ (t : ℝ) z, torus τ k (t * z) = expDiag (t • Pi.single k (atEmb τ z)) := fun t z => by
    rw [torus, ← Pi.single_smul, atEmb_eq, atEmb_eq τ z]; simp [smul_smul]
  have h0 : torus τ k 0 = 1 := by simpa [expDiag_zero] using hsm 0 0
  have hS : ∀ z x, Commute (Ξ.mat (torus τ k z))ᵀ (dualS Ξ k k x) := fun z x => by
    have h1 := Ξ.mat_mul_dmat (torus τ k z) (Matrix.single k k x)
    have h2 : (torus τ k z).val * Matrix.single k k x = Matrix.single k k x * (torus τ k z).val := by
      rw [← Matrix.diagonal_single]; exact Matrix.commute_diagonal _ _
    rw [h2, Units.mul_inv_cancel_right] at h1
    refine Commute.neg_right ?_
    exact (Matrix.transpose_mul _ _).symm.trans ((congrArg Matrix.transpose h1).symm.trans (Matrix.transpose_mul _ _))
  obtain ⟨u, hu, hu0, χ, hχ⟩ := exists_joint_eigenvector (fun z : ℂ => Matrix.toLin' (Ξ.mat (torus τ k z))ᵀ)
    (fun z z' => by
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
        ← Matrix.transpose_mul, ← Matrix.transpose_mul, ← map_mul, ← map_mul, ← hadd, ← hadd, add_comm])
    (Module.End.eigenspace (Matrix.toLin' (dualE Ξ τ k k)) c)
    ((Submodule.ne_bot_iff _).2 ⟨v, Module.End.mem_eigenspace_iff.2 h, hv⟩)
    (fun z u hu => by
      have h1 : Commute (Ξ.mat (torus τ k z))ᵀ (dualE Ξ τ k k) :=
        ((hS z _).sub_right ((hS z _).smul_right _)).smul_right _
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hu ⊢
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← h1.eq, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul])
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hu
  simp only [Matrix.toLin'_apply] at hχ
  let ψ : Multiplicative ℂ →* ℂ :=
    { toFun := fun z => χ z.toAdd
      map_one' := smul_left_injective ℂ hu0 (by simpa [h0] using (hχ 0).symm)
      map_mul' := fun z z' => smul_left_injective ℂ hu0 (by
        simp only [toAdd_mul]
        rw [← hχ, hadd, map_mul, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hχ, Matrix.mulVec_smul, hχ, smul_smul]) }
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hu0
  have hi' : u i ≠ 0 := hi
  have hc : ∀ z, χ z * u i = ∑ j, Ξ.mat (torus τ k z) j i * u j := fun z => (congrFun (hχ z) i).symm
  have hψ : (ψ : Multiplicative ℂ → ℂ) ∈ laurent := by
    convert laurent.sum_mem (t := Finset.univ) fun j _ => laurent.smul_mem (u j / u i) (reg_torus τ k (Ξ.reg j i)) using 1
    funext z
    change χ z.toAdd = _
    rw [← mul_left_inj' hi', hc, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  obtain ⟨p, hp⟩ : ψ ∈ Set.range expChar := by
    by_contra hn
    exact (linearIndependent_monoidHom (Multiplicative ℂ) ℂ).notMem_span_image hn hψ
  have key : ∀ z, (dualS Ξ k k (atEmb τ z) *ᵥ u) i = -(p.1 * z + p.2 * starRingEnd ℂ z) * u i := by
    intro z
    have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (Ξ.hasDerivAt_curve _ _ (by simp [expDiag_zero])
      (hasDerivAt_expDiag (Pi.single k (atEmb τ z))) j i).mul_const (u j)
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (t * (p.1 * z + p.2 * starRingEnd ℂ z)) * u i)
        ((p.1 * z + p.2 * starRingEnd ℂ z) * u i) 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const
        (p.1 * z + p.2 * starRingEnd ℂ z)).cexp.mul_const (u i)
    have h3 := h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      have e : χ (t * z) = _ := (DFunLike.congr_fun hp (Multiplicative.ofAdd (t * z))).symm
      simp only [← hsm, ← hc, e, expChar, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, map_mul, Complex.conj_ofReal]
      congr 2; ring))
    rw [neg_mul, ← h3, dualS, Matrix.neg_mulVec, Matrix.diagonal_single]
    rfl
  refine ⟨-p.1, mul_right_cancel₀ hi' ?_⟩
  have h1 := congrFun hu i
  simp only [dualE, Matrix.smul_mulVec, Matrix.sub_mulVec, Pi.smul_apply, Pi.sub_apply, key, smul_eq_mul, map_one,
    Complex.conj_I] at h1
  push_cast
  linear_combination -h1 + ((p.1 - p.2) / 2 * u i) * Complex.I_mul_I

def dualL (Ξ : AlgRep E a) (i j : Fin a) : Cinf E →ₗ[ℝ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ where
  toFun := dualS Ξ i j
  map_add' x y := by
    have h : toL (Matrix.single i j (x + y)) = toL (Matrix.single i j x) + toL (Matrix.single i j y) :=
      congrArg toL (Matrix.single_add i j x y)
    simp only [dualS, h, map_add, Matrix.transpose_add, neg_add]
  map_smul' c x := by
    have h : toL (Matrix.single i j (c • x)) = c • toL (Matrix.single i j x) :=
      congrArg toL (Matrix.smul_single c i j x).symm
    simp only [dualS, h, map_smul, Matrix.transpose_smul, smul_neg, RingHom.id_apply]

theorem dualL_apply (Ξ : AlgRep E a) (i j : Fin a) (x : Cinf E) : dualL Ξ i j x = dualS Ξ i j x := rfl

theorem dualL_comm (Ξ : AlgRep E a) (i j k l : Fin a) (x y : Cinf E) :
    dualL Ξ i j x * dualL Ξ k l y - dualL Ξ k l y * dualL Ξ i j x =
      (if j = k then dualL Ξ i l (x * y) else 0) - (if l = i then dualL Ξ k j (x * y) else 0) := by
  have h := congrArg (fun M => -Mᵀ) (dmat_bracket Ξ (Matrix.single i j x) (Matrix.single k l y))
  have e : ∀ X Y : Matrix (Fin a) (Fin a) (Cinf E), toL (X - Y) = toL X - toL Y := fun _ _ => rfl
  simp only [e, map_sub, Matrix.transpose_sub, Matrix.transpose_mul, neg_sub] at h
  simp only [dualL_apply, dualS, neg_mul_neg]
  rw [h, sub_eq_neg_add, sub_eq_add_neg]
  have z : Ξ.dmat (toL 0) = 0 := map_zero _
  congr 1
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, z]; simp
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same, mul_comm y, neg_neg]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, z]; simp

theorem dualLieActionMatrixUnit_commutator_formula (Ξ : AlgRep E a) (τ τ' : E →+* ℂ) (i j k l : Fin a) :
    dualE Ξ τ i j * dualE Ξ τ' k l - dualE Ξ τ' k l * dualE Ξ τ i j =
      (if j = k then (1 / 4 : ℂ) • (dualL Ξ i l (atEmb τ 1 * atEmb τ' 1) - dualL Ξ i l (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (dualL Ξ i l (atEmb τ 1 * atEmb τ' .I) + dualL Ξ i l (atEmb τ .I * atEmb τ' 1))) else 0) -
      (if l = i then (1 / 4 : ℂ) • (dualL Ξ k j (atEmb τ 1 * atEmb τ' 1) - dualL Ξ k j (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (dualL Ξ k j (atEmb τ 1 * atEmb τ' .I) + dualL Ξ k j (atEmb τ .I * atEmb τ' 1))) else 0) := by
  have h1 := dualL_comm Ξ i j k l (atEmb τ 1) (atEmb τ' 1)
  have h2 := dualL_comm Ξ i j k l (atEmb τ 1) (atEmb τ' .I)
  have h3 := dualL_comm Ξ i j k l (atEmb τ .I) (atEmb τ' 1)
  have h4 := dualL_comm Ξ i j k l (atEmb τ .I) (atEmb τ' .I)
  simp only [dualE, ← dualL_apply, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  split_ifs at h1 h2 h3 h4 ⊢ <;>
    linear_combination (norm := skip) (exp := 1) (1 / 4 : ℂ) • h1 - (Complex.I / 4 : ℂ) • h2 - (Complex.I / 4 : ℂ) • h3 - (1 / 4 : ℂ) • h4 <;>
    match_scalars <;> ring_nf <;> simp

theorem glRel_dualE (Ξ : AlgRep E a) (τ : E →+* ℂ) : Formalism.REAL.GlRel (dualE Ξ τ) := by
  intro i j k l
  have e : atEmb τ (Complex.I * Complex.I) = -atEmb τ 1 := by
    rw [atEmb_eq]; simp
  rw [dualLieActionMatrixUnit_commutator_formula]
  simp only [atEmb_mul, one_mul, mul_one, e, map_neg, dualE, ← dualL_apply]
  congr 1 <;> split_ifs <;> first | rfl | (match_scalars <;> ring)

variable [IsTotallyComplex E]

theorem dualE_comm (Ξ : AlgRep E a) {τ τ' : E →+* ℂ} (h : τ ≠ τ') (i j k l : Fin a) :
    dualE Ξ τ i j * dualE Ξ τ' k l = dualE Ξ τ' k l * dualE Ξ τ i j := by
  rw [← sub_eq_zero, dualLieActionMatrixUnit_commutator_formula]
  by_cases hw : InfinitePlace.mk τ = InfinitePlace.mk τ'
  · obtain rfl : ComplexEmbedding.conjugate τ = τ' := (InfinitePlace.mk_eq_iff.1 hw).resolve_left h
    have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
      rw [atEmb_eq]; simp
    have e' : atEmb τ (-1) = -atEmb τ 1 := by
      rw [atEmb_eq]; simp
    simp [atEmb_conj, atEmb_mul, e, e']
  · simp [atEmb_mul_of_ne hw]

theorem qdet_commute_dualE (Ξ : AlgRep E a) (τ τ' : E →+* ℂ) (u : ℂ) (i j : Fin a) :
    Commute (Formalism.REAL.qdet (dualE Ξ τ) u) (dualE Ξ τ' i j) := by
  by_cases h : τ = τ'
  · subst h; exact Formalism.REAL.qDetCentral _ a _ (glRel_dualE Ξ τ) u i j
  · refine Commute.sum_left _ _ _ fun σ _ => Commute.mul_left (Int.cast_commute _ _)
      (Commute.list_prod_left _ _ fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine Commute.add_left ?_ (dualE_comm Ξ h _ _ _ _)
    split_ifs
    · exact Algebra.commutes _ _
    · exact Commute.zero_left _

theorem commute_dmat (Ξ : AlgRep E a) (Z : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)
    (h : ∀ τ i j, Commute Z (dualE Ξ τ i j)) (X : Lie E a) : Commute Z (Ξ.dmat X)ᵀ := by
  classical
  have h1 : ∀ τ i j z, Commute Z (dualL Ξ i j (atEmb τ z)) := by
    intro τ i j z
    have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
      rw [atEmb_eq]; simp
    have e1 : dualL Ξ i j (atEmb τ 1) = dualE Ξ τ i j + dualE Ξ (ComplexEmbedding.conjugate τ) i j := by
      simp only [dualE, ← dualL_apply, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
      match_scalars <;> ring
    have e2 : dualL Ξ i j (atEmb τ Complex.I) =
        Complex.I • (dualE Ξ τ i j - dualE Ξ (ComplexEmbedding.conjugate τ) i j) := by
      simp only [dualE, ← dualL_apply, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
      match_scalars
      · linear_combination Complex.I_mul_I
      · ring
    rw [atEmb_eq, map_add, map_smul, map_smul, e1, e2]
    exact (((h _ _ _).add_right (h _ _ _)).smul_right _).add_right
      ((((h _ _ _).sub_right (h _ _ _)).smul_right _).smul_right _)
  have h2 : ∀ i j x, Commute Z (dualL Ξ i j x) := by
    intro i j x
    have e : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
      conv_lhs => rw [← Finset.univ_sum_single x]
      refine Finset.sum_congr rfl fun w _ => ?_
      unfold atEmb
      rw [if_pos (by rw [InfinitePlace.mk_embedding])]
      congr 1 <;> simp
    rw [e, map_sum]
    exact Commute.sum_right _ _ _ fun w _ => h1 _ _ _ _
  have e : X = ∑ i, ∑ j, toL (Matrix.single i j (X i j)) := Matrix.matrix_eq_sum_single (Matrix.of X)
  rw [e, map_sum, Matrix.transpose_sum]
  refine Commute.sum_right _ _ _ fun i _ => ?_
  rw [map_sum, Matrix.transpose_sum]
  refine Commute.sum_right _ _ _ fun j _ => ?_
  simpa [dualL_apply, dualS] using (h2 i j (X i j)).neg_right

omit [IsTotallyComplex E] in

theorem exists_scalar (Ξ : AlgRep E a) (Z : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (h : ∀ y, Z * Ξ.mat y = Ξ.mat y * Z) :
    ∃ c : ℂ, Z = c • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := by
  haveI : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' Z)
  refine ⟨c, ?_⟩
  have h1 := (Ξ.irred (Module.End.eigenspace (Matrix.toLin' Z) c) fun y v hv => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]).resolve_left hc
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ Module.End.eigenspace (Matrix.toLin' Z) c := h1 ▸ Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff.1 hv]
  simp

theorem qdet_scalar (Ξ : AlgRep E a) (τ : E →+* ℂ) (u : ℂ) :
    ∃ c : ℂ, Formalism.REAL.qdet (dualE Ξ τ) u = c • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := by
  obtain ⟨c, hc⟩ := exists_scalar Ξ (Formalism.REAL.qdet (dualE Ξ τ) u)ᵀ (commute_mat Ξ _ fun X => by
    have h := congrArg Matrix.transpose (commute_dmat Ξ _ (fun τ' => qdet_commute_dualE Ξ τ τ' u) X).eq
    simpa [Matrix.transpose_mul] using h.symm)
  exact ⟨c, by simpa using congrArg Matrix.transpose hc⟩

theorem exists_dualInfChar (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a)
    (τ : E →+* ℂ) : ∃ m : Multiset ℂ, HasDualInfChar Ξ τ m ∧ m.Nodup ∧
      ∀ z ∈ m, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2 := by
  haveI : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
  let f := (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin Ξ.d → ℂ)).toAlgHom
  have hf : ∀ M v, f M v = M *ᵥ v := fun _ _ => rfl
  have hgl : Formalism.REAL.GlRel fun i j => f (dualE Ξ τ i j) := fun i j k l => by
    have h := congrArg f (glRel_dualE Ξ τ i j k l)
    simpa only [map_sub, map_mul, apply_ite f, map_zero] using h
  obtain ⟨ν, v, hv, hw, hν⟩ := exists_highest a _ hgl
  refine ⟨Finset.univ.val.map fun k : Fin a => ν k + (((a : ℂ) - 1) / 2 - (k : ℕ)), ⟨by simp, fun u => ?_⟩, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := qdet_scalar Ξ τ (u + ((a : ℂ) - 1) / 2)
    have h := Formalism.REAL.qDetHW _ a _ ν v hgl hw (u + ((a : ℂ) - 1) / 2)
    rw [← map_qdet, hc, hf, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    rw [hc, smul_left_injective ℂ hv h, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
    congr 1
    exact Finset.prod_congr rfl fun k _ => by simp only [Function.comp_apply]; ring
  · have key : ∀ i j : Fin a, i < j →
        ν i + (((a : ℂ) - 1) / 2 - (i : ℕ)) ≠ ν j + (((a : ℂ) - 1) / 2 - (j : ℕ)) := by
      intro i j hij h
      obtain ⟨m, hm⟩ := hν i j hij
      have h2 : ((m + j : ℕ) : ℂ) = ((i : ℕ) : ℂ) := by push_cast; linear_combination h - hm
      have h3 : m + (j : ℕ) = i := Nat.cast_injective h2
      have : (i : ℕ) < j := hij
      omega
    refine Multiset.Nodup.map (fun i j h => ?_) Finset.univ.nodup
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd h (key i j h')
    · exact h'
    · exact absurd h.symm (key j i h')
  · intro z hz
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨n, hn⟩ := eigenvalue_int Ξ τ k v (ν k) hv (hw.1 k)
    exact ⟨n - (k : ℕ), by rw [hn]; push_cast; ring⟩

end GlobalTheory.AlgInfChar

end
