import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section

namespace GlobalTheory.CellScalarTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Cell

variable {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem cellFunctor_central (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (ρ : Representation ℂ (Levi k m) W) (χ' : Levi k m → ℂˣ) (hρ : ∀ y v, ρ y v = ((χ' y : ℂˣ) : ℂ) • v)
    (x : Levi k m') (hx : x ∈ relParab k g) (hcomm : ∀ y, y * x = x * y) (w) :
    cellFunctor f g ρ x w =
      ((relDeltaHalf k (fun j i => c i j) (relProj k g ⟨x, hx⟩) *
        (relDeltaHalf k c (swapBlocks k c (relProj k g ⟨x, hx⟩)))⁻¹ *
          χ' (relEmb k f (swapBlocks k c (relProj k g ⟨x, hx⟩))) : ℂˣ) : ℂ) • w := by
  apply Subtype.ext; apply Subtype.ext; funext y
  show w.1.1 (y * x) = _
  rw [hcomm y]
  have h2 : w.1.1 (x * y) = _ := w.1.2 ⟨x, hx⟩ y
  rw [h2]
  show _ = ((relDeltaHalf k (fun j i => c i j) (relProj k g ⟨x, hx⟩) *
        (relDeltaHalf k c (swapBlocks k c (relProj k g ⟨x, hx⟩)))⁻¹ *
          χ' (relEmb k f (swapBlocks k c (relProj k g ⟨x, hx⟩))) : ℂˣ) : ℂ) • w.1.1 y
  generalize w.1.1 y = u
  induction u using Submodule.Quotient.induction_on with
  | H v =>
  rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, relJac_mk, hρ]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, smul_smul, ← Submodule.Quotient.mk_smul]
  rw [mul_assoc]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype β] in

theorem scalar_comm (s : β → kˣ) (x : Levi k m') (hx : ∀ j, x j = GeneralLinearGroup.scalar _ (s j))
    (y : Levi k m') : y * x = x * y := by
  funext j
  rw [Pi.mul_apply, Pi.mul_apply, hx]
  ext1
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm.eq

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype β] [LinearOrder β] in

theorem scalar_mem (g : ∀ j, (Σ i, c i j) ≃ m' j) (s : β → kˣ) (x : Levi k m')
    (hx : ∀ j, x j = GeneralLinearGroup.scalar _ (s j)) : x ∈ relParab k g := by
  intro j _
  rw [hx]
  refine mem_parab.2 fun a b hab => ?_
  have hne : a ≠ b := by rintro rfl; exact lt_irrefl _ hab
  simp [Matrix.GeneralLinearGroup.scalar, hne]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype β] [LinearOrder β] in

theorem det_relProj (g : ∀ j, (Σ i, c i j) ≃ m' j) (s : β → kˣ) (x : Levi k m')
    (hx : ∀ j, x j = GeneralLinearGroup.scalar _ (s j)) (h : x ∈ relParab k g) (j : β) (i : α) :
    GeneralLinearGroup.det (relProj k g ⟨x, h⟩ j i) = s j ^ Fintype.card (c i j) := by
  have e : relProj k g ⟨x, h⟩ j i = GeneralLinearGroup.scalar _ (s j) := by
    ext a a'
    refine (leviProj_apply k (g j) ⟨x j, h j trivial⟩ i a a').trans ?_
    show ((x j : GL (m' j) k) : Matrix (m' j) (m' j) k) _ _ = _
    rw [hx]
    by_cases h : a = a'
    · subst h; simp [Matrix.GeneralLinearGroup.scalar]
    · have h' : g j ⟨i, a⟩ ≠ g j ⟨i, a'⟩ := by simpa using h
      simp [Matrix.GeneralLinearGroup.scalar, h, h']
  rw [e]
  ext
  simp [Matrix.GeneralLinearGroup.scalar]

end Cell

theorem modExp_false (m : Bool → Type) [∀ a, Fintype (m a)] :
    modExp m false = Fintype.card (m true) := by
  simp [modExp, Finset.sum_filter]

theorem modExp_true (m : Bool → Type) [∀ a, Fintype (m a)] :
    modExp m true = -(Fintype.card (m false) : ℤ) := by
  simp [modExp, Finset.sum_filter]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem extTensor_detRep_apply (χ₁ χ₂ : kˣ →* ℂˣ) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (y : Levi k (Two a b)) (t : TensorProduct ℂ ℂ ℂ) :
    ((extTensor (detRep a χ₁) (detRep b χ₂)).comp (leviTwo k a b).symm.toMonoidHom) y t =
      ((χ₁ (GeneralLinearGroup.det (y false)) * χ₂ (GeneralLinearGroup.det (y true)) : ℂˣ) : ℂ) • t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => rw [map_add, hs, ht, smul_add]
  | tmul s t =>
    refine (extTensor_tmul (detRep a χ₁) (detRep b χ₂) (y false, y true) s t).trans ?_
    rw [detRep, detRep, ofChar_apply, ofChar_apply, ← smul_eq_mul, ← smul_eq_mul,
      TensorProduct.smul_tmul_smul]
    rfl

theorem cellFunctor_scalar_action {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1))) (hb : b.1 false true = 1)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
    (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j) (ϖ : kˣ)
    (x : Levi k (Two (Fin (u + v)) (Fin 1)))
    (hx : ∀ j, x j = GeneralLinearGroup.scalar _ ((fun j : Bool => if j then ϖ else 1) j)) (w) :
    cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
        (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)
      x w =
      (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ) • w := by
  have hm := scalar_mem (c := fun i j => Fin (b.1 i j)) g _ x hx
  have hd := det_relProj (c := fun i j => Fin (b.1 i j)) g _ x hx hm
  have h11 : b.1 true true = 0 := by
    have := b.2.2 true
    simp only [Fintype.sum_bool, Fintype.card_fin] at this
    omega
  have h00 : (b.1 false false : ℂ) = u - 1 := by
    have := b.2.1 false
    simp only [Fintype.sum_bool, Fintype.card_fin] at this
    have h3 : b.1 false false + 1 = u := by omega
    rw [eq_sub_iff_add_eq]
    exact_mod_cast h3
  refine (cellFunctor_central (c := fun i j => Fin (b.1 i j)) f g _
    (fun y => χ₁ (GeneralLinearGroup.det (y false)) * χ₂ (GeneralLinearGroup.det (y true)))
    (extTensor_detRep_apply χ₁ χ₂ (Fin u) (Fin (v + 1))) x hm (scalar_comm _ x hx) w).trans ?_
  refine congrArg (fun s : ℂˣ => (s : ℂ) • w) ?_
  have hd' : ∀ i j, GeneralLinearGroup.det
      (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g ⟨x, hm⟩) i j) = _ := fun i j => hd j i
  simp only [relDeltaHalf_apply, deltaHalf_apply, relEmb_apply, det_leviEmb, Fintype.prod_bool, hd, hd',
    modExp_false, modExp_true, Fintype.card_fin, hb, h11]
  have hz : absPow k (-(b.1 false false : ℂ) / 2) = (absPow k (((u : ℂ) - 1) / 2))⁻¹ := by
    rw [h00, neg_div, absPow_neg]
  simp [hz, mul_comm]

theorem cellFunctor_scalar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1))) (hb : b.1 false true = 1)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
    (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j) (ϖ : kˣ) (w) :
    cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
        (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)
      (leviTwo k (Fin (u + v)) (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) w =
      (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ) • w := by
  have hx : ∀ j, leviTwo k (Fin (u + v)) (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ) j =
      GeneralLinearGroup.scalar _ ((fun j : Bool => if j then ϖ else 1) j) := by
    intro j
    cases j
    · exact (map_one (GeneralLinearGroup.scalar (R := k) (Fin (u + v)))).symm
    · rfl
  exact cellFunctor_scalar_action χ₁ χ₂ u v b hb f g ϖ _ hx w

end GlobalTheory.CellScalarTwo
