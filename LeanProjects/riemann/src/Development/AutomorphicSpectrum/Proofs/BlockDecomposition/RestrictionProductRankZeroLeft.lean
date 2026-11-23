import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.CompanionTheory.BZRes
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibRes0Left

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def evalTop (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : Representation ℂ H W) (hσ : IsSmooth σ) :
    smoothPart (ind H σ) ≃ₗ[ℂ] W where
  toFun f := f.1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨⟨fun g => σ ⟨g, hH g⟩ w, by
      intro h g
      show σ ⟨(h : G) * g, hH _⟩ w = σ h (σ ⟨g, hH g⟩ w)
      rw [← Module.End.mul_apply, ← map_mul]
      rfl⟩, by
      have hop : IsOpen {g : G | σ ⟨g, hH g⟩ w = w} :=
        (hσ w).preimage (continuous_id.subtype_mk hH)
      have h1 : (1 : G) ∈ {g : G | σ ⟨g, hH g⟩ w = w} := by
        show σ ⟨1, hH 1⟩ w = w
        rw [show (⟨1, hH 1⟩ : H) = 1 from rfl, map_one, Module.End.one_apply]
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset (hop.mem_nhds h1) fun g hg => ?_)
      refine Subtype.ext (funext fun x => ?_)
      show σ ⟨x * g, hH _⟩ w = σ ⟨x, hH x⟩ w
      rw [show (⟨x * g, hH _⟩ : H) = ⟨x, hH x⟩ * ⟨g, hH g⟩ from rfl, map_mul, Module.End.mul_apply]
      exact congrArg _ hg⟩
  left_inv f := by
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    show σ ⟨g, hH g⟩ (f.1.1 1) = f.1.1 g
    have := f.1.2 ⟨g, hH g⟩ 1
    rw [← this, mul_one]
  right_inv w := by
    show σ ⟨1, hH 1⟩ w = w
    rw [show (⟨1, hH 1⟩ : H) = 1 from rfl, map_one, Module.End.one_apply]

theorem mem_cIndSpace_top (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : Representation ℂ H W) (f : smoothPart (ind H σ)) :
    f ∈ cIndSpace H σ := by
  exact ⟨{1}, isCompact_singleton, fun g _ => ⟨g, hH g, 1, Set.mem_singleton 1, (mul_one g).symm⟩⟩

def cTop (H : Subgroup G) (hH : ∀ g, g ∈ H) (σ : Representation ℂ H W) :
    cIndSpace H σ ≃ₗ[ℂ] smoothPart (ind H σ) where
  toFun f := f.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f, mem_cIndSpace_top H hH σ f⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {P W₂ : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [AddCommGroup W₂] [Module ℂ W₂]

theorem equiv_of_top (ι : P →* G) (hι : Continuous ι) (Q : Subgroup G) (H : Subgroup P) (hQ : ∀ g, g ∈ Q)
    (hH : ∀ p, p ∈ H) (σ : Representation ℂ Q W) (τ : Representation ℂ H W₂) (E : W ≃ₗ[ℂ] W₂) (hσ : IsSmooth σ)
    (hE : ∀ (h : H) (v : W), τ h (E v) = E (σ ⟨ι h, hQ _⟩ v)) :
    Nonempty (Representation.Equiv ((smInd Q σ).comp ι) (cInd H τ)) := by
  have hτ : IsSmooth τ := by
    intro w
    obtain ⟨v, rfl⟩ := E.surjective w
    have hset : {h : H | τ h (E v) = E v} =
        (fun h : H => (⟨ι h, hQ _⟩ : Q)) ⁻¹' {q : Q | σ q v = v} := by
      ext h
      show τ h (E v) = E v ↔ σ ⟨ι h, hQ _⟩ v = v
      rw [hE h v]
      exact E.injective.eq_iff
    rw [hset]
    exact (hσ v).preimage ((hι.comp continuous_subtype_val).subtype_mk _)
  let L : smoothPart (ind Q σ) ≃ₗ[ℂ] cIndSpace H τ :=
    ((evalTop Q hQ σ hσ).trans E).trans ((evalTop H hH τ hτ).symm.trans (cTop H hH τ).symm)
  refine ⟨Representation.Equiv.mk L fun p => ?_⟩
  refine LinearMap.ext fun f => ?_
  refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun x => ?_)))
  show τ ⟨x, hH x⟩ (E (f.1.1 (1 * ι p))) = τ ⟨x * p, hH _⟩ (E (f.1.1 1))
  have hf : f.1.1 (ι p) = σ ⟨ι p, hQ _⟩ (f.1.1 1) := by
    have := f.1.2 ⟨ι p, hQ _⟩ 1
    rw [mul_one] at this
    exact this
  rw [one_mul, hf, show E (σ ⟨ι p, hQ _⟩ (f.1.1 1)) = τ ⟨p, hH p⟩ (E (f.1.1 1)) from (hE ⟨p, hH p⟩ _).symm,
    ← Module.End.mul_apply, ← map_mul]
  rfl

end Abstract

section Concrete

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hgp_twist_tE {m j : ℕ}
    (π₁ : Representation ℂ (GL (Fin m) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : MirabolicParabolic k m j)
    (hq : ((g : Mir k (m + j)) : GL (Fin (m + j + 1)) k) ∈
      parab k (two (stdSum (rfl : m + (j + 1) = m + j + 1))))
    (v : ⨂[ℂ] x, TwoT V W x) :
    ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k m) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((m : ℕ) : ℝ) / 2)).ρ).comp (gpProj k m j)) g (tE V W v) =
      tE V W (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩ v) := by
  set L := leviProj k (two (stdSum (rfl : m + (j + 1) = m + j + 1))) ⟨_, hq⟩ with hL
  have hL2 : leviTwo k (Fin m) (Fin (j + 1)) (L false, L true) = L := by
    funext b
    cases b <;> rfl
  have hδ := GlobalTheory.SmGL.deltaHalf_two (k := k) (a := Fin m) (b := Fin (j + 1)) (L false, L true)
  rw [hL2] at hδ
  have hc : (((dpow m (((j + 1 : ℕ) : ℝ) / 2)) (L false) : ℂˣ) : ℂ) *
      (((dpow (j + 1) (-((m : ℕ) : ℝ) / 2)) (L true) : ℂˣ) : ℂ) =
      ((deltaHalf k (Two (Fin m) (Fin (j + 1))) L : ℂˣ) : ℂ) := by
    rw [hδ, Units.val_mul]
    simp only [dpow, GlobalTheory.SmGL.detChar_apply, Fintype.card_fin]
    congr 4 <;> push_cast <;> ring
  have key : ∀ x : (b : Bool) → TwoT V W b,
      ((extTensor (GRep.tw (⟨V, π₁⟩ : GRep k m) (((j + 1 : ℕ) : ℝ) / 2)).ρ
        (mtw (gres (⟨W, π₂⟩ : GRep k (j + 1))) (-((m : ℕ) : ℝ) / 2)).ρ).comp (gpProj k m j)) g
          (tE V W (PiTensorProduct.tprod ℂ x)) =
      tE V W (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) := by
    intro x
    have e1 : tE V W (PiTensorProduct.tprod ℂ x) = x false ⊗ₜ[ℂ] x true :=
      GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod x
    have e2 : sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x) =
        ((deltaHalf k (Two (Fin m) (Fin (j + 1))) L : ℂˣ) : ℂ) •
          PiTensorProduct.tprod ℂ (fun b => twoRep π₁ π₂ b (L b) (x b)) := by
      show ((deltaHalf k (Two (Fin m) (Fin (j + 1))) L : ℂˣ) : ℂ) •
          (piTensor (twoRep π₁ π₂) L) (PiTensorProduct.tprod ℂ x) = _
      rw [GlobalTheory.SmGL.piTensor_tprod]
    have e3 : tE V W (PiTensorProduct.tprod ℂ (fun b => twoRep π₁ π₂ b (L b) (x b))) =
        π₁ (L false) (x false) ⊗ₜ[ℂ] π₂ (L true) (x true) :=
      GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod _
    rw [e1, e2, map_smul, e3, MonoidHom.comp_apply]
    erw [GlobalTheory.SmGL.extTensor_tmul]
    show ((((dpow m (((j + 1 : ℕ) : ℝ) / 2)) (L false) : ℂˣ) : ℂ) • π₁ (L false) (x false)) ⊗ₜ[ℂ]
        ((((dpow (j + 1) (-((m : ℕ) : ℝ) / 2)) (L true) : ℂˣ) : ℂ) • π₂ (L true) (x true)) = _
    rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, hc]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [LinearEquiv.map_smul (tE V W) r,
      LinearMap.map_smul (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩) r,
      LinearEquiv.map_smul (tE V W), ← key x]
    exact LinearMap.map_smul _ _ _
  | add a b ha hb =>
    rw [LinearEquiv.map_add (tE V W) a b,
      LinearMap.map_add (sQ (rfl : m + (j + 1) = m + j + 1) π₁ π₂ ⟨_, hq⟩) a b,
      LinearEquiv.map_add (tE V W), ← ha, ← hb]
    exact LinearMap.map_add _ _ _

theorem mem_parab_zero {j : ℕ} (g : GL (Fin (0 + j + 1)) k) :
    g ∈ parab k (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1))) := by
  intro a b hab
  have key : ∀ x : Fin (0 + j + 1), GlobalTheory.SmGL.blk (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1))) x = true := by
    intro x
    unfold GlobalTheory.SmGL.blk
    rcases (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1))).symm x with ⟨b, y⟩
    cases b
    · exact Fin.elim0 y
    · rfl
  rw [key, key] at hab
  exact absurd hab (lt_irrefl _)

theorem isSmooth_sQ {r t N : ℕ} (h : r + t = N) {π₁ : Representation ℂ (GL (Fin r) k) V}
    {π₂ : Representation ℂ (GL (Fin t) k) W} (h₁ : IsSmooth π₁) (h₂ : IsSmooth π₂) : IsSmooth (sQ h π₁ π₂) := by
  refine GlobalTheory.SmGL.isSmooth_comp (GlobalTheory.SmGL.isSmooth_twist (GlobalTheory.SmGL.isSmooth_piTensor fun b => ?_)
    (GlobalTheory.SmGL.isSmoothChar_deltaHalf k)) _ ?_
  · cases b
    · exact h₁
    · exact h₂
  · refine continuous_pi fun b => Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_submatrix
        (fun i => (two (stdSum h)) ⟨b, i⟩) (fun i => (two (stdSum h)) ⟨b, i⟩)
    · have hinv : Continuous fun p : parab k (two (stdSum h)) =>
          (((p⁻¹ : parab k (two (stdSum h))) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) :=
        (Units.continuous_val.comp continuous_subtype_val).comp continuous_inv
      refine (hinv.matrix_submatrix (fun i => (two (stdSum h)) ⟨b, i⟩)
        (fun i => (two (stdSum h)) ⟨b, i⟩)).congr fun p => ?_
      rw [← Pi.inv_apply, ← map_inv]
      rfl

theorem gres_prod_zero_left (j n : ℕ) (π₁ : GRep k 0) (π₂ : GRep k (j + 1)) (h : 0 + (j + 1) = n + 1) (h' : 0 + j = n)
    (h₁ : IsSmooth π₁.ρ) (h₂ : IsSmooth π₂.ρ) :
    MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodGPn π₁ (gres π₂))) := by
  subst h'
  exact equiv_of_top (Mir k (0 + j)).subtype continuous_subtype_val
    (parab k (two (stdSum (rfl : 0 + (j + 1) = 0 + j + 1)))) (MirabolicParabolic k 0 j)
    (fun g => mem_parab_zero g) (fun p => mem_parab_zero (p : GL (Fin (0 + j + 1)) k))
    (sQ (rfl : 0 + (j + 1) = 0 + j + 1) π₁.ρ π₂.ρ)
    ((extTensor (π₁.tw (((j + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres π₂) (-((0 : ℕ) : ℝ) / 2)).ρ).comp (gpProj k 0 j))
    (tE π₁.V π₂.V) (isSmooth_sQ rfl h₁ h₂)
    (fun hh v => hgp_twist_tE π₁.ρ π₂.ρ hh (mem_parab_zero _) v)

theorem gres_prod_zero_left' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (j n : ℕ) (π₁ : GRep k 0) (π₂ : GRep k (j + 1)) (h : 0 + (j + 1) = n + 1) (h' : 0 + j = n),
    IsSmooth π₁.ρ → IsSmooth π₂.ρ → MIso (gres ((π₁.prod π₂).cast h)) (mcast h' (prodGPn π₁ (gres π₂))) := by
  intro k _ _ _ _ j n π₁ π₂ h h' h₁ h₂
  exact gres_prod_zero_left j n π₁ π₂ h h' h₁ h₂

end Concrete

end GlobalTheory.CompanionTheory.LeibRes0Left

end
