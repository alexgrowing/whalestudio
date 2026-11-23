import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.MemParahoricTimesPrincipalCongruenceIff
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Qminor

noncomputable section

namespace UpperTheory.Esk.FixedPointOrthogonalCases

section Z

open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.TR Matrix

private theorem infGL_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (Rinf F)ˣ) :
    infGL F 2 (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (infId F u) := by
  have h : ∀ x, pInf F (sInf F x) = x := fun x => (infEq F).symm_apply_apply x
  have h1 : pInf F (infId F u : Ideles F) = u := by
    change pInf F (1 - sInf F 1 + sInf F _) = _
    simp [h]
  have h2 : pFin F (infId F u : Ideles F) = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem fin_expU {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Rinf F) : ω.1 (infId F (expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : expU z = expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

private theorem lie_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    {φ : Sm F 2} (hφ : ∀ (z : Ideles F) (g : GA F 2), φ.1 (GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) (z : Rinf F) : lie F 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
    (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
        simpa using this
      · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h2 : (fun t : ℝ => φ.1 (g * infGL F 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) = fun _ => φ.1 g := by
    funext t
    rw [infGL_scalar, ← GeneralLinearGroup.scalar_commute, hφ, fin_expU h]
    simp
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

private theorem casimir {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (k : ℂ) (φ : V) (h0 : E 0 0 φ + E 1 1 φ = 0)
    (h1 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ) (h2 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℂ) :
    Formalism.REAL.qdet E (u + 1 / 2) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ :=
  _root_.UpperTheory.Reformulated.B.Qf10.casimir E hE k φ h0 h1 h2 u

theorem zfinV {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (k : InfinitePlace F → ℕ) (ω : HChar F)
    (hω : IsOfFinOrder ω) (φ : Sm F 2)
    (hc : ∀ (z : Ideles F) (g : GA F 2), φ.1 (GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g)
    (hw : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k v) • φ)
    (hl : ∀ v, TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F 2) => z φ) '' TR.Zalg F 2)) := by
  have hcap : ∀ v u, ∃ c : ℂ, TR.cap v u φ = c • φ := fun v u => by
    have h0 : Eop v 0 0 φ + Eop v 1 1 φ = 0 := by
      classical
      rw [← lie_scalar hω hc (Pi.single v 1), TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add]
      congr 2
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have := casimir _ (TR.glRel_Eop v) (k v) φ h0 (hw v) (hl v) u
    refine ⟨_, Eq.trans ?_ this⟩
    rw [TR.cap]
    norm_num
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, u, rfl⟩ := hx
    obtain ⟨c, e⟩ := hcap v u
    exact Submodule.mem_span_singleton.2 ⟨c, e.symm⟩
  | algebraMap c => exact Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy =>
    obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 hy
    have e' : c • φ = y φ := e
    change x (y φ) ∈ Submodule.span ℂ {φ}
    rw [← e', map_smul]
    exact Submodule.smul_mem _ _ hx

end Z

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem rot_fix (m : GL (Fin 2) ℝ) (a b : ℝ) (h00 : m.val 0 0 = a) (h01 : m.val 0 1 = b) (h10 : m.val 1 0 = -b)
    (h11 : m.val 1 1 = a) : m • iP = iP := by
  apply Subtype.ext
  rw [coe_smul]
  have hI : (iP : P).1 = Complex.I := rfl
  rw [hI, div_eq_iff (den_ne m (by simp))]
  simp only [num, den]
  change (m.val 0 0 : ℂ) * Complex.I + (m.val 0 1 : ℂ) = Complex.I * ((m.val 1 0 : ℂ) * Complex.I + (m.val 1 1 : ℂ))
  rw [h00, h01, h10, h11]
  push_cast
  linear_combination (b : ℂ) * Complex.I_sq

theorem rot_rt (hB : B1b) (k : InfinitePlace F → ℕ) (f : X (InfinitePlace F) × GF F → ℂ) (φ : TR.Sm F 2)
    (hrel : Rel k f φ.1) (y : GL (Fin 2) (TR.Rinf F)) (hy : ∀ v, gv v y • iP = iP) :
    ∃ c : ℂ, TR.rt F 2 (TR.infGL F 2 y) φ = c • φ := by
  refine ⟨∏ v, (j1 (k v) (gv v y) iP)⁻¹, Subtype.ext (funext fun g => ?_)⟩
  rw [TR.rt_apply]
  change _ = (∏ v, (j1 (k v) (gv v y) iP)⁻¹) * φ.1 g
  obtain ⟨a, b, rfl⟩ : ∃ a b, g = TR.infGL F 2 a * finGL F 2 b := ⟨_, _, (TR.infGL_mul_finGL g).symm⟩
  have e : TR.infGL F 2 a * finGL F 2 b * TR.infGL F 2 y = TR.infGL F 2 (a * y) * finGL F 2 b := by
    rw [mul_assoc, ← TR.infGL_comm, ← mul_assoc, map_mul]
  have h1 := hrel (a * y) b
  have h2 := hrel a b
  rw [e]
  have e3 : (fun v => gv v (a * y) • iP) = fun v => gv v a • iP := funext fun v => by rw [map_mul, mul_smul, hy v]
  rw [e3, ← h2] at h1
  have hc : ∀ v, j1 (k v) (gv v (a * y)) iP = j1 (k v) (gv v a) iP * j1 (k v) (gv v y) iP := fun v => by
    rw [map_mul, hB.1, hy v]
  simp only [hc, Finset.prod_mul_distrib] at h1
  have hA : ∏ v, j1 (k v) (gv v a) iP ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hB.2.1 _ _ _
  have hB' : ∏ v, j1 (k v) (gv v y) iP ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hB.2.1 _ _ _
  rw [Finset.prod_inv_distrib, eq_inv_mul_iff_mul_eq₀ hB']
  apply mul_right_cancel₀ hA
  linear_combination h1

private theorem orth_cases {a b c d : ℝ} (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1)
    (h3 : a * c + b * d = 0) : (c = -b ∧ d = a) ∨ (c = b ∧ d = -a) := by
  have hD : (a * d - b * c - 1) * (a * d - b * c + 1) = 0 := by
    linear_combination (c ^ 2 + d ^ 2) * h1 + h2 - (a * c + b * d) * h3
  rcases mul_eq_zero.1 hD with h | h
  · exact Or.inl ⟨by linear_combination (-c) * h1 + a * h3 - b * h, by linear_combination (-d) * h1 + b * h3 + a * h⟩
  · exact Or.inr ⟨by linear_combination (-c) * h1 + a * h3 - b * h, by linear_combination (-d) * h1 + b * h3 + a * h⟩

open Classical in

def sg (S : Set (InfinitePlace F)) : InfinitePlace F → ℝ := fun v => if v ∈ S then -1 else 1

theorem sg_sq (S : Set (InfinitePlace F)) (v : InfinitePlace F) : sg S v * sg S v = 1 := by
  unfold sg; split_ifs <;> norm_num

theorem diag_sq (S : Set (InfinitePlace F)) :
    (Matrix.diagonal ![(sg S : TR.Rinf F), 1]) * Matrix.diagonal ![(sg S : TR.Rinf F), 1] = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · funext v; exact sg_sq S v
  · simp

def eS (S : Set (InfinitePlace F)) : GL (Fin 2) (TR.Rinf F) :=
  ⟨Matrix.diagonal ![(sg S : TR.Rinf F), 1], Matrix.diagonal ![(sg S : TR.Rinf F), 1], diag_sq S, diag_sq S⟩

theorem eS_sq (S : Set (InfinitePlace F)) : eS S * eS S = 1 := Units.ext (diag_sq S)

theorem gv_eS_mul (S : Set (InfinitePlace F)) (x : GL (Fin 2) (TR.Rinf F)) (v : InfinitePlace F) :
    (gv v (eS S * x)).val 0 0 = sg S v * (gv v x).val 0 0 ∧ (gv v (eS S * x)).val 0 1 = sg S v * (gv v x).val 0 1 ∧
    (gv v (eS S * x)).val 1 0 = (gv v x).val 1 0 ∧ (gv v (eS S * x)).val 1 1 = (gv v x).val 1 1 := by
  simp [gv, eS, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

theorem kfin (hB : B1b) (k : InfinitePlace F → ℕ) (f : X (InfinitePlace F) × GF F → ℂ) (φ : TR.Sm F 2)
    (hrel : Rel k f φ.1) : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun r => TR.cptRep F 2 r φ)) := by
  classical
  let T := Submodule.span ℂ (Set.range fun S : Set (InfinitePlace F) => TR.rt F 2 (TR.infGL F 2 (eS S)) φ)
  haveI : FiniteDimensional ℂ T := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  refine Submodule.finiteDimensional_of_le (S₂ := T) (Submodule.span_le.2 ?_)
  rintro _ ⟨r, rfl⟩
  have e : TR.cptRep F 2 r φ = TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits r)) φ := rfl
  change TR.cptRep F 2 r φ ∈ T
  rw [e]
  have hr : ∀ v (i j : Fin 2), (gv v (Unitary.toUnits r)).val i 0 * (gv v (Unitary.toUnits r)).val j 0 +
      (gv v (Unitary.toUnits r)).val i 1 * (gv v (Unitary.toUnits r)).val j 1 = if i = j then 1 else 0 := by
    intro v i j
    have h := congrArg (fun m => (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v) (m i j)) r.2.2
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, map_add, map_mul, Matrix.one_apply] at h
    rw [apply_ite (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v), map_one, map_zero] at h
    exact h
  generalize Unitary.toUnits r = x at hr ⊢
  let S : Set (InfinitePlace F) := {v | ¬ ((gv v x).val 1 0 = -(gv v x).val 0 1 ∧ (gv v x).val 1 1 = (gv v x).val 0 0)}
  have hy : ∀ v, gv v (eS S * x) • iP = iP := by
    intro v
    have h1 : (gv v x).val 0 0 ^ 2 + (gv v x).val 0 1 ^ 2 = 1 := by
      have := hr v 0 0; simp only [if_true] at this; linear_combination this
    have h2 : (gv v x).val 1 0 ^ 2 + (gv v x).val 1 1 ^ 2 = 1 := by
      have := hr v 1 1; simp only [if_true] at this; linear_combination this
    have h3 : (gv v x).val 0 0 * (gv v x).val 1 0 + (gv v x).val 0 1 * (gv v x).val 1 1 = 0 := by simpa using hr v 0 1
    obtain ⟨e00, e01, e10, e11⟩ := gv_eS_mul S x v
    by_cases hv : v ∈ S
    · have hs : sg S v = -1 := if_pos hv
      have hcase : (gv v x).val 1 0 = (gv v x).val 0 1 ∧ (gv v x).val 1 1 = -(gv v x).val 0 0 :=
        (orth_cases h1 h2 h3).resolve_left hv
      refine rot_fix _ (-(gv v x).val 0 0) (-(gv v x).val 0 1) ?_ ?_ ?_ ?_
      · rw [e00, hs]; ring
      · rw [e01, hs]; ring
      · rw [e10, hcase.1]; ring
      · rw [e11, hcase.2]
    · have hs : sg S v = 1 := if_neg hv
      have hcase : (gv v x).val 1 0 = -(gv v x).val 0 1 ∧ (gv v x).val 1 1 = (gv v x).val 0 0 := not_not.1 hv
      refine rot_fix _ ((gv v x).val 0 0) ((gv v x).val 0 1) ?_ ?_ ?_ ?_
      · rw [e00, hs]; ring
      · rw [e01, hs]; ring
      · rw [e10, hcase.1]
      · rw [e11, hcase.2]
  obtain ⟨c, hc⟩ := rot_rt hB k f φ hrel (eS S * x) hy
  have e2 : x = eS S * (eS S * x) := by rw [← mul_assoc, eS_sq, one_mul]
  have e3 : TR.rt F 2 (TR.infGL F 2 x) φ = c • TR.rt F 2 (TR.infGL F 2 (eS S)) φ := by
    conv_lhs => rw [e2]
    rw [map_mul, map_mul, Module.End.mul_apply, hc, map_smul]
  rw [e3]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩)

theorem isOpen_fix (c : Pl F → ℕ) (hc : {w | c w ≠ 0}.Finite) (ψ : TR.Sm F 2)
    (h : ∀ u ∈ Kc c, TR.finRep F 2 u ψ = ψ) : IsOpen {u | TR.finRep F 2 u ψ = ψ} := by
  let S : Subgroup (GF F) :=
    { carrier := {u | TR.finRep F 2 u ψ = ψ}
      one_mem' := by
        show TR.finRep F 2 1 ψ = ψ
        rw [map_one, Module.End.one_apply]
      mul_mem' := fun {a b} ha hb => by
        have ha' : TR.finRep F 2 a ψ = ψ := ha
        have hb' : TR.finRep F 2 b ψ = ψ := hb
        show TR.finRep F 2 (a * b) ψ = ψ
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := fun {a} ha => by
        have ha' : TR.finRep F 2 a ψ = ψ := ha
        show TR.finRep F 2 a⁻¹ ψ = ψ
        calc TR.finRep F 2 a⁻¹ ψ = TR.finRep F 2 a⁻¹ (TR.finRep F 2 a ψ) := by rw [ha']
          _ = ψ := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  exact Subgroup.isOpen_mono (H₁ := Kc c) (H₂ := S) h ((UpperTheory.V.Sd.Wc.kcTop F).1 c hc).1

end UpperTheory.Esk.FixedPointOrthogonalCases

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Wc in
theorem UpperTheory.Esk.hyperbolic_tail_estimate_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.H2a → UpperTheory.Esk.H2b → UpperTheory.Esk.H2c → UpperTheory.Esk.H2d := by
  intro hB hA hS hC F _ _ _ k c hc ω χ hω hχ hsg hk f φ hf hrel
  obtain ⟨hl, hK, hcent, C, hC'⟩ := hA F k c hc ω χ hω hχ hsg hk f φ hf hrel
  have hs : φ ∈ TR.Sm F 2 := hS F k c hc ω χ hω hχ hsg hk f φ hf hrel
  have hwl := hC F k c hc ω χ hω hχ hsg hk f φ hf hrel hs
  have hfix : ∀ u ∈ Kc c, TR.finRep F 2 u ⟨φ, hs⟩ = ⟨φ, hs⟩ := fun u hu => Subtype.ext (funext fun g => by
    change ((TR.rt F 2 (finGL F 2 u)) ⟨φ, hs⟩).1 g = φ g
    rw [TR.rt_apply]
    exact hK u hu g)
  refine ⟨hs, ⟨⟨hl, UpperTheory.Esk.FixedPointOrthogonalCases.isOpen_fix c hc _ hfix, UpperTheory.Esk.FixedPointOrthogonalCases.kfin hB k f ⟨φ, hs⟩ hrel,
    UpperTheory.Esk.FixedPointOrthogonalCases.zfinV k ω hω ⟨φ, hs⟩ hcent (fun v => (hwl v).1) (fun v => (hwl v).2),
    fun g => ⟨C, 0, fun y => by rw [pow_zero, mul_one]; exact hC' _⟩⟩,
    fun w u hu => hfix _ ((UpperTheory.V.Sd.Wc.kcTop F).2.2.2.2.2 c w u hu), hcent, fun v => (hwl v).1, fun v => (hwl v).2⟩⟩
