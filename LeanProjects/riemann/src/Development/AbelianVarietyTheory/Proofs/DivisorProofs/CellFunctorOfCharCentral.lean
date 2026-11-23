import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section

open GlobalTheory.SmGL GlobalTheory.PRep

namespace GlobalTheory.LeviBlockExponentLocal

theorem prod_ofFn_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] (A : Module.End ℂ V) :
    ∀ (M : ℕ) (S : Fin (M + 1) → Submodule ℂ V) (c : Fin M → ℂ),
      (∀ t : Fin M, ∀ v ∈ S t.succ, A v - c t • v ∈ S t.castSucc) → S 0 = ⊥ →
        ∀ v ∈ S (Fin.last M), polyAt A (List.ofFn c) v = 0 := by
  unfold polyAt
  intro M
  induction M with
  | zero =>
    intro S c _ h0 v hv
    have : v ∈ S 0 := hv
    rw [h0, Submodule.mem_bot] at this
    simp [this]
  | succ M ih =>
    intro S c hstep h0 v hv
    rw [List.ofFn_succ', List.concat_eq_append, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply]
    refine ih (fun t => S t.castSucc) (fun t => c t.castSucc) (fun t w hw => ?_) h0 _ ?_
    · have := hstep t.castSucc w (by rw [Fin.succ_castSucc]; exact hw)
      exact this
    · have := hstep (Fin.last M) v (by simpa using hv)
      simpa using this

theorem toSubmodule_bot' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

theorem toSubmodule_top' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

section Cell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
  {c : α → β → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]

def cellScalar (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j) (χ' : Levi k m →* ℂˣ)
    (x : relParab k g) : ℂˣ :=
  relDeltaHalf k (fun j i => c i j) (relProj k g x) *
    (relDeltaHalf k c (swapBlocks k c (relProj k g x)))⁻¹ *
      χ' (relEmb k f (swapBlocks k c (relProj k g x)))

theorem cellFunctor_ofChar_central (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (χ' : Levi k m →* ℂˣ) (x : Levi k m') (hx : x ∈ relParab k g) (hcomm : ∀ y, y * x = x * y) (w) :
    cellFunctor f g (ofChar χ') x w = ((cellScalar f g χ' ⟨x, hx⟩ : ℂˣ) : ℂ) • w := by
  apply Subtype.ext; apply Subtype.ext; funext y
  show w.1.1 (y * x) = _
  rw [hcomm y]
  have h2 : w.1.1 (x * y) = _ := w.1.2 ⟨x, hx⟩ y
  rw [h2]
  show _ = ((cellScalar f g χ' ⟨x, hx⟩ : ℂˣ) : ℂ) • w.1.1 y
  generalize w.1.1 y = u
  induction u using Submodule.Quotient.induction_on with
  | H v =>
  rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, relJac_mk, ofChar, twist_apply]
  simp only [Representation.trivial_apply, cellScalar, Units.val_mul, Units.val_inv_eq_inv_val, smul_smul,
    ← Submodule.Quotient.mk_smul]
  rw [mul_assoc]

end Cell

section Slot

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blockScalar_apply (N i : ℕ) (ϖ : kˣ) (j : Fin (i + 2)) :
    blockScalar₂ k N i ϖ j = Matrix.GeneralLinearGroup.scalar _ (if j = ⟨i, by omega⟩ then ϖ else 1) := by
  unfold blockScalar₂
  by_cases h : j = ⟨i, by omega⟩
  · subst h; simp
  · rw [Pi.mulSingle_eq_of_ne h, if_neg h, map_one]

theorem blockScalar_comm (N i : ℕ) (ϖ : kˣ) (y : Levi k (fun j : Fin (i + 2) => Fin (blockSizes₂ N i j))) :
    y * blockScalar₂ k N i ϖ = blockScalar₂ k N i ϖ * y := by
  funext j
  rw [Pi.mul_apply, Pi.mul_apply, blockScalar_apply]
  ext1
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm.eq

theorem blockScalar_mem_relParab (N i : ℕ) (ϖ : kˣ) {β : Type} {c : Fin (i + 2) → β → Type} [LinearOrder β] [Fintype β]
    [∀ j r, Fintype (c j r)] [∀ j r, DecidableEq (c j r)]
    (g : ∀ j, (Σ r, c j r) ≃ Fin (blockSizes₂ N i j)) : blockScalar₂ k N i ϖ ∈ relParab k g := by
  intro j _
  rw [blockScalar_apply]
  refine mem_parab.2 fun a b hab => ?_
  have hne : a ≠ b := by rintro rfl; exact lt_irrefl _ hab
  simp [Matrix.GeneralLinearGroup.scalar, hne]

end Slot

end GlobalTheory.LeviBlockExponentLocal
