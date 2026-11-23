import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorScalarUniformizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
open GlobalTheory.PRep GlobalTheory.SmGL Matrix GlobalTheory.CellScalarTwo
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.CellOff

theorem intertwining_eq_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : ρ.IntertwiningMap σ) (x : G) (l m : ℂ) (h₁ : ∀ v, ρ x v = l • v) (h₂ : ∀ w, σ x w = m • w)
    (hne : l ≠ m) : φ.toLinearMap = 0 := by
  ext v
  have h := φ.isIntertwining ρ σ x v
  rw [h₁, h₂, map_smul] at h
  have h3 : (l - m) • φ.toLinearMap v = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.2 h
  rw [LinearMap.zero_apply]
  exact (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Cell

variable {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def cellChar (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j) (χ' : Levi k m →* ℂˣ) :
    relParab k g →* ℂˣ :=
  ((relDeltaHalf k (fun j i => c i j)).comp (relProj k g)) *
    ((relDeltaHalf k c).comp ((swapBlocks k c).comp (relProj k g)))⁻¹ *
      (χ'.comp ((relEmb k f).comp ((swapBlocks k c).comp (relProj k g))))

theorem cellFunctor_law (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (ρ : Representation ℂ (Levi k m) W) (χ' : Levi k m →* ℂˣ)
    (hρ : ∀ y v, ρ y v = ((χ' y : ℂˣ) : ℂ) • v) (p : relParab k g) (y : Levi k m')
    (w : smoothPart (ind (relParab k g) ((twist ((relJac f ρ).comp (swapBlocks k c))
      (relDeltaHalf k fun j i => c i j)).comp (relProj k g)))) :
    w.1.1 (p.1 * y) = ((cellChar f g χ' p : ℂˣ) : ℂ) • w.1.1 y := by
  rw [w.1.2 p y]
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective (GlobalTheory.PRep.twKer ρ (GlobalTheory.SmGL.relUnip k f) 1) (w.1.1 y)
  rw [← hv]
  have hT : ∀ (q : ∀ i, Levi k (c i)) (u : W),
      GlobalTheory.SmGL.relJac f ρ q (Submodule.Quotient.mk u : GlobalTheory.PRep.Jacquet ρ (GlobalTheory.SmGL.relUnip k f)) =
        ((((relDeltaHalf k c) q)⁻¹ : ℂˣ) : ℂ) •
          (Submodule.Quotient.mk (ρ (relEmb k f q) u) : GlobalTheory.PRep.Jacquet ρ (GlobalTheory.SmGL.relUnip k f)) :=
    fun _ _ => rfl
  have hS : ∀ (r : relParab k g) (z : GlobalTheory.PRep.Jacquet ρ (GlobalTheory.SmGL.relUnip k f)),
      ((GlobalTheory.SmGL.twist ((GlobalTheory.SmGL.relJac f ρ).comp (swapBlocks k c)) (relDeltaHalf k fun j i => c i j)).comp
        (relProj k g)) r z =
        ((relDeltaHalf k (fun j i => c i j) (relProj k g r) : ℂˣ) : ℂ) •
          GlobalTheory.SmGL.relJac f ρ (swapBlocks k c (relProj k g r)) z :=
    fun _ _ => rfl
  rw [hS, hT, hρ, Submodule.Quotient.mk_smul]
  simp only [cellChar, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, Units.val_mul, mul_smul]

theorem cellChar_conj (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (χ' : Levi k m →* ℂˣ) (p q : relParab k g) :
    cellChar f g χ' (q * p * q⁻¹) = cellChar f g χ' p := by
  rw [map_mul, map_mul, map_inv]
  exact mul_inv_cancel_comm _ _

theorem cellFunctor_of_top (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (ρ : Representation ℂ (Levi k m) W) (χ' : Levi k m →* ℂˣ)
    (hρ : ∀ y v, ρ y v = ((χ' y : ℂˣ) : ℂ) • v) (hP : ∀ x, x ∈ relParab k g) (x : Levi k m')
    (w : smoothPart (ind (relParab k g) ((twist ((relJac f ρ).comp (swapBlocks k c))
      (relDeltaHalf k fun j i => c i j)).comp (relProj k g)))) :
    cellFunctor f g ρ x w = ((cellChar f g χ' ⟨x, hP x⟩ : ℂˣ) : ℂ) • w := by
  apply Subtype.ext
  apply Subtype.ext
  funext y
  have hp : y * x * y⁻¹ ∈ relParab k g := hP _
  have hyx : y * x = (y * x * y⁻¹) * y := by group
  have hc : cellChar f g χ' ⟨y * x * y⁻¹, hp⟩ = cellChar f g χ' ⟨x, hP x⟩ :=
    cellChar_conj f g χ' ⟨x, hP x⟩ ⟨y, hP y⟩
  show w.1.1 (y * x) = ((cellChar f g χ' ⟨x, hP x⟩ : ℂˣ) : ℂ) • w.1.1 y
  rw [hyx, ← hc]
  exact cellFunctor_law f g ρ χ' hρ ⟨y * x * y⁻¹, hp⟩ y w

theorem intertwining_zero_central {V : Type} [AddCommGroup V] [Module ℂ V]
    (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (ρ : Representation ℂ (Levi k m) W) (χ' : Levi k m → ℂˣ)
    (hρ : ∀ y v, ρ y v = ((χ' y : ℂˣ) : ℂ) • v) {σ : Representation ℂ (Levi k m') V}
    (φ : (cellFunctor f g ρ).IntertwiningMap σ)
    (x : Levi k m') (hx : x ∈ relParab k g) (hcomm : ∀ y, y * x = x * y) (l : ℂ)
    (hσ : ∀ t, σ x t = l • t)
    (hne : ((relDeltaHalf k (fun j i => c i j) (relProj k g ⟨x, hx⟩) *
        (relDeltaHalf k c (swapBlocks k c (relProj k g ⟨x, hx⟩)))⁻¹ *
          χ' (relEmb k f (swapBlocks k c (relProj k g ⟨x, hx⟩))) : ℂˣ) : ℂ) ≠ l) :
    φ.toLinearMap = 0 := by
  exact intertwining_eq_zero φ x _ l (fun w => cellFunctor_central f g ρ χ' hρ x hx hcomm w) hσ hne

theorem intertwining_zero_of_top {V : Type} [AddCommGroup V] [Module ℂ V]
    (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (ρ : Representation ℂ (Levi k m) W) (χ' : Levi k m →* ℂˣ)
    (hρ : ∀ y v, ρ y v = ((χ' y : ℂˣ) : ℂ) • v) {σ : Representation ℂ (Levi k m') V}
    (φ : (cellFunctor f g ρ).IntertwiningMap σ) (hP : ∀ x, x ∈ relParab k g)
    (x : Levi k m') (l : ℂ) (hσ : ∀ t, σ x t = l • t)
    (hne : ((cellChar f g χ' ⟨x, hP x⟩ : ℂˣ) : ℂ) ≠ l) : φ.toLinearMap = 0 := by
  exact intertwining_eq_zero φ x _ l (fun w => cellFunctor_of_top f g ρ χ' hρ hP x w) hσ hne

end Cell

theorem det_of_isEmpty {n : Type} [Fintype n] [DecidableEq n] [IsEmpty n] (g : GL n k) :
    GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_isEmpty, Units.val_one]

theorem relDeltaHalf_eq_one (c : Bool → Bool → Type) [∀ i j, Fintype (c i j)]
    [∀ i j, DecidableEq (c i j)] (h₀ : IsEmpty (c false false)) (h₁ : IsEmpty (c true true))
    (q : ∀ i, Levi k (c i)) : relDeltaHalf k c q = 1 := by
  haveI := h₀
  haveI := h₁
  have hA : ∀ x : kˣ, GlobalTheory.SmGL.absPow k 0 x = 1 := by
    intro x
    apply Units.ext
    show ((GlobalTheory.SplitWeil.nabs k x : ℝ) : ℂ) ^ (0 : ℂ) = 1
    exact Complex.cpow_zero _
  have hE : ∀ (i j : Bool), GlobalTheory.SmGL.detChar (c i j) (GlobalTheory.SmGL.absPow k (↑(GlobalTheory.SmGL.modExp (c i) j) / 2)) (q i j) = 1 := by
    intro i j
    cases i <;> cases j
    · show GlobalTheory.SmGL.absPow k _ (GeneralLinearGroup.det (q false false)) = 1
      rw [det_of_isEmpty (q false false), map_one]
    · show GlobalTheory.SmGL.absPow k (↑(GlobalTheory.SmGL.modExp (c false) true) / 2) (GeneralLinearGroup.det (q false true)) = 1
      rw [GlobalTheory.CellScalarTwo.modExp_true, Fintype.card_eq_zero]
      simp only [Nat.cast_zero, neg_zero, Int.cast_zero, zero_div]
      exact hA _
    · show GlobalTheory.SmGL.absPow k (↑(GlobalTheory.SmGL.modExp (c true) false) / 2) (GeneralLinearGroup.det (q true false)) = 1
      rw [GlobalTheory.CellScalarTwo.modExp_false, Fintype.card_eq_zero]
      simp only [Nat.cast_zero, Int.cast_zero, zero_div]
      exact hA _
    · show GlobalTheory.SmGL.absPow k _ (GeneralLinearGroup.det (q true true)) = 1
      rw [det_of_isEmpty (q true true), map_one]
  show (∏ i, (GlobalTheory.SmGL.deltaHalf k (c i)).comp (Pi.evalMonoidHom (fun i => Levi k (c i)) i)) q = 1
  rw [MonoidHom.finsetProd_apply]
  refine Finset.prod_eq_one fun i _ => ?_
  show (∏ j, (GlobalTheory.SmGL.detChar (c i j) (GlobalTheory.SmGL.absPow k (↑(GlobalTheory.SmGL.modExp (c i) j) / 2))).comp
    (Pi.evalMonoidHom (fun j => GL (c i j) k) j)) (q i) = 1
  rw [MonoidHom.finsetProd_apply]
  exact Finset.prod_eq_one fun j _ => hE i j

def twoChar (χ₁ χ₂ : kˣ →* ℂˣ) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    Levi k (Two a b) →* ℂˣ where
  toFun y := χ₁ (GeneralLinearGroup.det (y false)) * χ₂ (GeneralLinearGroup.det (y true))
  map_one' := by simp
  map_mul' x y := by
    simp only [Pi.mul_apply, map_mul]
    exact mul_mul_mul_comm _ _ _ _

variable (k) in

theorem exists_nabs_lt : ∃ s : kˣ, GlobalTheory.SplitWeil.nabs k s < 1 := by
  obtain ⟨z, -, hz⟩ := GlobalTheory.CentralExponent.exists_nabs_lt_one k
  exact ⟨z, hz⟩

section TwoBlocks

variable {a b : ℕ}

theorem twoChar_apply (χ₁ χ₂ : kˣ →* ℂˣ) (y : Levi k (Two (Fin a) (Fin b))) :
    twoChar χ₁ χ₂ (Fin a) (Fin b) y =
      χ₁ (GeneralLinearGroup.det (y false)) * χ₂ (GeneralLinearGroup.det (y true)) := rfl

theorem mem_relParab_of_antidiag (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)))
    (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j)
    (h₀ : B.1 false false = 0) (h₁ : B.1 true true = 0) (x : Levi k (Two (Fin a) (Fin b))) :
    x ∈ relParab k g := by
  have key : ∀ (j : Bool) (t : Two (Fin a) (Fin b) j), GlobalTheory.SmGL.blk (g j) t = !j := by
    intro j t
    show ((g j).symm t).1 = !j
    generalize (g j).symm t = u
    obtain ⟨i, q⟩ := u
    cases i <;> cases j
    · exact absurd q.isLt (by omega)
    · rfl
    · rfl
    · exact absurd q.isLt (by omega)
  show x ∈ Subgroup.pi Set.univ fun j => GlobalTheory.SmGL.parab k (g j)
  rw [Subgroup.mem_pi]
  intro j _
  show Matrix.BlockTriangular ((x j : GL _ k) : Matrix _ _ k) (GlobalTheory.SmGL.blk (g j))
  intro r s hrs
  rw [key, key] at hrs
  exact absurd hrs (lt_irrefl _)

theorem cellChar_antidiag (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)))
    (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i)
    (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j)
    (h₀ : B.1 false false = 0) (h₁ : B.1 true true = 0) (χ₁ χ₂ : kˣ →* ℂˣ)
    (x : Levi k (Two (Fin a) (Fin b))) (hx : x ∈ relParab k g) :
    cellChar (c := fun i j => Fin (B.1 i j)) f g (twoChar χ₁ χ₂ (Fin a) (Fin b)) ⟨x, hx⟩ =
      χ₁ (GeneralLinearGroup.det (x true)) * χ₂ (GeneralLinearGroup.det (x false)) := by
  haveI e00 : IsEmpty (Fin (B.1 false false)) := by rw [h₀]; infer_instance
  haveI e11 : IsEmpty (Fin (B.1 true true)) := by rw [h₁]; infer_instance
  have hb1 : GeneralLinearGroup.det (swapBlocks k (fun i j => Fin (B.1 i j)) (relProj k g ⟨x, hx⟩) false true) =
      GeneralLinearGroup.det (x true) := by
    have hxt : x true ∈ GlobalTheory.SmGL.parab k (g true) := ((Subgroup.mem_pi Set.univ).1 hx) true (Set.mem_univ _)
    have h := GlobalTheory.SmGL.det_parab k (g true) ⟨x true, hxt⟩
    rw [Fintype.prod_bool, det_of_isEmpty (n := Fin (B.1 true true)), one_mul] at h
    exact h.symm
  have hb0 : GeneralLinearGroup.det (swapBlocks k (fun i j => Fin (B.1 i j)) (relProj k g ⟨x, hx⟩) true false) =
      GeneralLinearGroup.det (x false) := by
    have hxf : x false ∈ GlobalTheory.SmGL.parab k (g false) := ((Subgroup.mem_pi Set.univ).1 hx) false (Set.mem_univ _)
    have h := GlobalTheory.SmGL.det_parab k (g false) ⟨x false, hxf⟩
    rw [Fintype.prod_bool, det_of_isEmpty (n := Fin (B.1 false false)), mul_one] at h
    exact h.symm
  simp only [cellChar, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply]
  rw [relDeltaHalf_eq_one (fun j i => Fin (B.1 i j)) e00 e11, relDeltaHalf_eq_one (fun i j => Fin (B.1 i j)) e00 e11,
    inv_one, one_mul, one_mul, twoChar_apply, relEmb_apply, relEmb_apply, det_leviEmb, det_leviEmb,
    Fintype.prod_bool, Fintype.prod_bool,
    det_of_isEmpty (n := Fin (B.1 false false)), det_of_isEmpty (n := Fin (B.1 true true)), mul_one, one_mul, hb1, hb0]

theorem exists_det_eq (ha : 0 < a) (t : kˣ) : ∃ y : GL (Fin a) k, GeneralLinearGroup.det y = t := by
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  exact Matrix.GeneralLinearGroup.det_surjective t

theorem sizes (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) :
    B.1 false false + B.1 false true = a ∧ B.1 true false + B.1 true true = b ∧
      B.1 false false + B.1 true false = a ∧ B.1 false true + B.1 true true = b := by
  obtain ⟨h1, h2⟩ := B.2
  have e1 := h1 false
  have e2 := h1 true
  have e3 := h2 false
  have e4 := h2 true
  simp only [Fintype.sum_bool] at e1 e2 e3 e4
  have c0 : Fintype.card (Two (Fin a) (Fin b) false) = a := Fintype.card_fin a
  have c1 : Fintype.card (Two (Fin a) (Fin b) true) = b := Fintype.card_fin b
  rw [c0] at e1 e3
  rw [c1] at e2 e4
  omega

theorem absPow_half (s : kˣ) (z : ℤ) (n : ℕ) :
    absPow k ((z : ℂ) / 2) (s ^ n) = (absPow k (1 / 2) s) ^ (z * n) := by
  apply Units.ext
  have hv : ∀ (t : ℂ) (y : kˣ), ((absPow k t y : ℂˣ) : ℂ) = ((GlobalTheory.SplitWeil.nabs k y : ℝ) : ℂ) ^ t :=
    fun _ _ => rfl
  have hr : 0 ≤ GlobalTheory.SplitWeil.nabs k s := NNReal.coe_nonneg _
  have hpow : GlobalTheory.SplitWeil.nabs k (s ^ n) = GlobalTheory.SplitWeil.nabs k s ^ n := by
    show ((MeasureTheory.distribHaarChar k (s ^ n) : NNReal) : ℝ) =
      ((MeasureTheory.distribHaarChar k s : NNReal) : ℝ) ^ n
    rw [map_pow, NNReal.coe_pow]
  rw [Units.val_zpow_eq_zpow_val, hv, hv, hpow]
  have e1 : ((z : ℂ) / 2) = (((z : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, ← Complex.ofReal_cpow (pow_nonneg hr n), ← Complex.ofReal_cpow hr, ← Complex.ofReal_zpow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr, ← Real.rpow_intCast, ← Real.rpow_mul hr]
  congr 1
  push_cast
  ring

theorem norm_absPow_half_lt {s : kˣ} (hs : GlobalTheory.SplitWeil.nabs k s < 1) :
    0 < ‖((absPow k (1 / 2) s : ℂˣ) : ℂ)‖ ∧ ‖((absPow k (1 / 2) s : ℂˣ) : ℂ)‖ < 1 := by
  have hv : ((absPow k (1 / 2) s : ℂˣ) : ℂ) = ((GlobalTheory.SplitWeil.nabs k s : ℝ) : ℂ) ^ ((1 : ℂ) / 2) := rfl
  have hr0 : 0 < GlobalTheory.SplitWeil.nabs k s := by
    have h1 : MeasureTheory.distribHaarChar k s * MeasureTheory.distribHaarChar k s⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have h2 : MeasureTheory.distribHaarChar k s ≠ 0 := left_ne_zero_of_mul_eq_one h1
    show (0 : ℝ) < ((MeasureTheory.distribHaarChar k s : NNReal) : ℝ)
    exact_mod_cast pos_iff_ne_zero.2 h2
  have e2 : ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hv, e2, ← Complex.ofReal_cpow hr0.le, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hr0 _)]
  exact ⟨Real.rpow_pos_of_pos hr0 _, Real.rpow_lt_one hr0.le hs (by norm_num)⟩

theorem cell_scalar_case {W : Type} [AddCommGroup W] [Module ℂ W] (χ₁ χ₂ : kˣ →* ℂˣ)
    (u₁ : IsUnitaryChar χ₁) (u₂ : IsUnitaryChar χ₂)
    (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)))
    (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i)
    (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j)
    (hc : B.1 false true ≠ 0) (hz : B.1 false false + B.1 true true ≠ 0) (s : kˣ)
    (hs : GlobalTheory.SplitWeil.nabs k s < 1)
    (ρ : Representation ℂ (Levi k (Two (Fin a) (Fin b))) W)
    (hρ : ∀ y v, ρ y v = ((twoChar χ₁ χ₂ (Fin a) (Fin b) y : ℂˣ) : ℂ) • v)
    (φ : (cellFunctor f g ρ).IntertwiningMap ρ) : φ.toLinearMap = 0 := by
  classical
  obtain ⟨sv, hsvT, hsvF⟩ : ∃ sv : Bool → kˣ, sv true = 1 ∧ sv false = s := ⟨fun j => cond j 1 s, rfl, rfl⟩
  obtain ⟨x, hxj⟩ : ∃ x : Levi k (Two (Fin a) (Fin b)),
      ∀ j, x j = GeneralLinearGroup.scalar (Two (Fin a) (Fin b) j) (sv j) := ⟨fun j => _, fun j => rfl⟩
  have hx : x ∈ relParab k g := scalar_mem g sv x hxj
  have hcomm : ∀ y, y * x = x * y := scalar_comm sv x hxj
  have hδ : ∀ (C : Bool → Bool → Type) [∀ i j, Fintype (C i j)] [∀ i j, DecidableEq (C i j)]
      (Q : ∀ i, Levi k (C i)) (t : Bool → Bool → kˣ),
      (∀ i j, GeneralLinearGroup.det (Q i j) = t i j ^ Fintype.card (C i j)) →
      relDeltaHalf k C Q = ∏ i, ∏ j, absPow k (↑(modExp (C i) j) / 2) (t i j ^ Fintype.card (C i j)) := by
    intro C _ _ Q t hQ
    show (∏ i, (GlobalTheory.SmGL.deltaHalf k (C i)).comp (Pi.evalMonoidHom (fun i => Levi k (C i)) i)) Q = _
    rw [MonoidHom.finsetProd_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    show (∏ j, (GlobalTheory.SmGL.detChar (C i j) (absPow k (↑(modExp (C i) j) / 2))).comp
      (Pi.evalMonoidHom (fun j => GL (C i j) k) j)) (Q i) = _
    rw [MonoidHom.finsetProd_apply]
    refine Finset.prod_congr rfl fun j _ => ?_
    show absPow k (↑(modExp (C i) j) / 2) (GeneralLinearGroup.det (Q i j)) = _
    rw [hQ]
  have h1 : relDeltaHalf k (fun j i => Fin (B.1 i j)) (relProj k g ⟨x, hx⟩) = 1 := by
    rw [hδ (fun j i => Fin (B.1 i j)) (relProj k g ⟨x, hx⟩) (fun j _ => sv j)
      (fun j i => det_relProj g sv x hxj hx j i)]
    simp only [Fintype.prod_bool, hsvT, hsvF, one_pow, map_one, _root_.one_zpow, one_mul, mul_one, absPow_half,
      modExp_false, modExp_true, Fintype.card_fin]
    rw [← _root_.zpow_add]
    convert zpow_zero (absPow k (1 / 2) s) using 2
    push_cast
    ring
  have h2 : relDeltaHalf k (fun i j => Fin (B.1 i j))
      (swapBlocks k (fun i j => Fin (B.1 i j)) (relProj k g ⟨x, hx⟩)) =
      absPow k (1 / 2) s ^ (((B.1 true true * B.1 true false + B.1 false true * B.1 false false : ℕ)) : ℤ) := by
    rw [hδ (fun i j => Fin (B.1 i j)) (swapBlocks k (fun i j => Fin (B.1 i j)) (relProj k g ⟨x, hx⟩)) (fun _ j => sv j) (fun i j => det_relProj g sv x hxj hx j i)]
    simp only [Fintype.prod_bool, hsvT, hsvF, one_pow, map_one, _root_.one_zpow, one_mul, mul_one, absPow_half,
      modExp_false, modExp_true, Fintype.card_fin]
    rw [← _root_.zpow_add]
    congr 1
    all_goals (push_cast; ring)
  have hτ : ∀ z, ‖((twoChar χ₁ χ₂ (Fin a) (Fin b) z : ℂˣ) : ℂ)‖ = 1 := by
    intro z
    rw [twoChar_apply, Units.val_mul, norm_mul, u₁ _, u₂ _, one_mul]
  obtain ⟨e1, e2, e3, e4⟩ := sizes B
  have hBeq : B.1 true false = B.1 false true := by omega
  have hN : B.1 true true * B.1 true false + B.1 false true * B.1 false false ≠ 0 := by
    have hr : B.1 true true * B.1 false true + B.1 false true * B.1 false false =
        B.1 false true * (B.1 false false + B.1 true true) := by ring
    rw [hBeq, hr]
    exact Nat.mul_ne_zero hc hz
  have hu := norm_absPow_half_lt hs
  refine intertwining_zero_central f g ρ (fun y => twoChar χ₁ χ₂ (Fin a) (Fin b) y) hρ φ x hx hcomm _ (hρ x) ?_
  rw [h1, h2, one_mul]
  intro h
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val] at h
  have hn := congrArg (fun z : ℂ => ‖z‖) h
  rw [norm_mul, norm_inv, norm_zpow, hτ, hτ, mul_one, zpow_natCast, inv_eq_one] at hn
  exact (pow_lt_one₀ hu.1.le hu.2 hN).ne hn

theorem cell_antidiag_case {W : Type} [AddCommGroup W] [Module ℂ W] (χ₁ χ₂ : kˣ →* ℂˣ)
    (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)))
    (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i)
    (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j)
    (h₀ : B.1 false false = 0) (h₁ : B.1 true true = 0) (y : GL (Fin a) k)
    (hy : χ₁ (GeneralLinearGroup.det y) ≠ χ₂ (GeneralLinearGroup.det y))
    (ρ : Representation ℂ (Levi k (Two (Fin a) (Fin b))) W)
    (hρ : ∀ y v, ρ y v = ((twoChar χ₁ χ₂ (Fin a) (Fin b) y : ℂˣ) : ℂ) • v)
    (φ : (cellFunctor f g ρ).IntertwiningMap ρ) : φ.toLinearMap = 0 := by
  have hP : ∀ z, z ∈ relParab k g := mem_relParab_of_antidiag B g h₀ h₁
  refine intertwining_zero_of_top f g ρ (twoChar χ₁ χ₂ (Fin a) (Fin b)) hρ φ hP
    (GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b) (y, 1)) _ (hρ _) ?_
  rw [cellChar_antidiag B f g h₀ h₁ χ₁ χ₂ _ (hP _), twoChar_apply]
  show ((χ₁ (GeneralLinearGroup.det (1 : GL (Fin b) k)) * χ₂ (GeneralLinearGroup.det y) : ℂˣ) : ℂ) ≠
    ((χ₁ (GeneralLinearGroup.det y) * χ₂ (GeneralLinearGroup.det (1 : GL (Fin b) k)) : ℂˣ) : ℂ)
  rw [map_one, map_one, map_one, one_mul, mul_one]
  exact fun h => hy (Units.ext h).symm

theorem exists_sep (ha : 0 < a) {χ₁ χ₂ : kˣ →* ℂˣ} (h : χ₁ ≠ χ₂) :
    ∃ y : GL (Fin a) k, χ₁ (GeneralLinearGroup.det y) ≠ χ₂ (GeneralLinearGroup.det y) := by
  by_contra hall
  simp only [not_exists, ne_eq, not_not] at hall
  apply h
  refine MonoidHom.ext fun t => ?_
  obtain ⟨y, rfl⟩ := exists_det_eq ha t
  exact hall y

theorem cell_zero {W : Type} [AddCommGroup W] [Module ℂ W] (χ₁ χ₂ : kˣ →* ℂˣ)
    (u₁ : IsUnitaryChar χ₁) (u₂ : IsUnitaryChar χ₂) (hne : a ≠ b ∨ χ₁ ≠ χ₂)
    (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)))
    (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i)
    (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j)
    (hc : B.1 false true ≠ 0) (s : kˣ) (hs : GlobalTheory.SplitWeil.nabs k s < 1)
    (ρ : Representation ℂ (Levi k (Two (Fin a) (Fin b))) W)
    (hρ : ∀ y v, ρ y v = ((twoChar χ₁ χ₂ (Fin a) (Fin b) y : ℂˣ) : ℂ) • v)
    (φ : (cellFunctor f g ρ).IntertwiningMap ρ) : φ.toLinearMap = 0 := by
  by_cases hz : B.1 false false + B.1 true true = 0
  · have h0 : B.1 false false = 0 := by omega
    have h1 : B.1 true true = 0 := by omega
    obtain ⟨e1, e2, e3, e4⟩ := sizes B
    have hab : a = b := by omega
    have ha : 0 < a := by omega
    have hχ : χ₁ ≠ χ₂ := hne.resolve_left (fun h => h hab)
    obtain ⟨y, hy⟩ := exists_sep ha hχ
    exact cell_antidiag_case χ₁ χ₂ B f g h0 h1 y hy ρ hρ φ
  · exact cell_scalar_case χ₁ χ₂ u₁ u₂ B f g hc hz s hs ρ hρ φ

end TwoBlocks

theorem offCell_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → ∀ (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i) (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j), B.1 false true ≠ 0 → ∀ φ : (cellFunctor f g ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)).IntertwiningMap ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom), φ.toLinearMap = 0 := by
  intro k _ _ _ _ a b χ₁ χ₂ _ _ u₁ u₂ hne B f g hc φ
  obtain ⟨s, hs⟩ := exists_nabs_lt k
  exact cell_zero χ₁ χ₂ u₁ u₂ hne B f g hc s hs _
    (fun y v => by rw [extTensor_detRep_apply, twoChar_apply]) φ

end GlobalTheory.CompanionTheory.CellOff
