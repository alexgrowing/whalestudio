import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.StepData ValuativeRel Matrix
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.ParahoricVec

theorem exists_biequivariant {G : Type} [Group G] (P J : Subgroup G) (c : P →* ℂˣ) (d : J →* ℂˣ)
    (h : ∀ (p : P) (j : J), (p : G) = j → c p = d j) :
    ∃ f : G → ℂ, f 1 = 1 ∧ (∀ (p : P) (x : G), f (p * x) = (c p : ℂ) * f x) ∧
      ∀ (x : G) (j : J), f (x * j) = f x * (d j : ℂ) := by
  classical
  let f : G → ℂ := fun x =>
    if hx : ∃ q : P × J, x = q.1 * q.2 then (c hx.choose.1 : ℂ) * (d hx.choose.2 : ℂ) else 0
  have key : ∀ (p : P) (j : J), f (p * j) = (c p : ℂ) * (d j : ℂ) := by
    intro p j
    have hx : ∃ q : P × J, ((p : G) * j) = q.1 * q.2 := ⟨(p, j), rfl⟩
    have hq := hx.choose_spec
    simp only [f, dif_pos hx]
    set q := hx.choose
    have e : ((q.1⁻¹ * p : P) : G) = ((q.2 * j⁻¹ : J) : G) := by
      push_cast
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hq]
      group
    have := h _ _ e
    rw [map_mul, map_mul, map_inv, map_inv, inv_mul_eq_iff_eq_mul] at this
    have h2 : c p * d j = c q.1 * d q.2 := by
      rw [this, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
    rw [← Units.val_mul, ← Units.val_mul, h2]
  have zero : ∀ x : G, (¬ ∃ q : P × J, x = q.1 * q.2) → f x = 0 := fun x hx => dif_neg hx
  refine ⟨f, ?_, fun p x => ?_, fun x j => ?_⟩
  · simpa using key 1 1
  · by_cases hx : ∃ q : P × J, x = q.1 * q.2
    · obtain ⟨⟨p', j⟩, rfl⟩ := hx
      have := key (p * p') j
      rw [Subgroup.coe_mul, mul_assoc] at this
      show f (p * (p' * j)) = _
      rw [this, key, map_mul, Units.val_mul, mul_assoc]
    · rw [zero x hx, mul_zero]
      refine zero _ fun ⟨q, hq⟩ => hx ⟨(p⁻¹ * q.1, q.2), ?_⟩
      simp [mul_assoc, ← hq]
  · by_cases hx : ∃ q : P × J, x = q.1 * q.2
    · obtain ⟨⟨p, j'⟩, rfl⟩ := hx
      have := key p (j' * j)
      rw [Subgroup.coe_mul, ← mul_assoc] at this
      show f (p * j' * j) = f (p * j') * _
      rw [this, key, map_mul, Units.val_mul, mul_assoc]
    · rw [zero x hx, zero_mul]
      refine zero _ fun ⟨q, hq⟩ => hx ⟨(q.1, q.2 * j⁻¹), ?_⟩
      simp [← mul_assoc, ← hq]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : ℕ}

local notation "e₀" => stdSum (rfl : r + t = r + t)
local notation "E₀" => two (stdSum (rfl : r + t = r + t))

variable (r t) in

def lev (χ : kˣ →* ℂˣ) (hχ : IsTame χ) : Level (GL (Fin (r + t)) k) :=
  (parahoric (Fin r) (Fin t) χ hχ).toLevel.map (reGL (stdSum (rfl : r + t = r + t)))

variable (r t) in

def leftChar (χ : kˣ →* ℂˣ) : parab k (two (stdSum (rfl : r + t = r + t))) →* ℂˣ :=
  (deltaHalf k (Two (Fin r) (Fin t))).comp (leviProj k (two (stdSum (rfl : r + t = r + t)))) *
    (detChar (Fin t) χ).comp
      ((Pi.evalMonoidHom (fun x => GL (Two (Fin r) (Fin t) x) k) true).comp
        (leviProj k (two (stdSum (rfl : r + t = r + t)))))

theorem leftChar_eq_lam (χ : kˣ →* ℂˣ) (hχ : IsTame χ) (p : parab k (two (stdSum (rfl : r + t = r + t))))
    (j : (lev r t χ hχ).J) (h : (p : GL (Fin (r + t)) k) = j) : leftChar r t χ p = (lev r t χ hχ).lam j := by
  have hj : (reGL (stdSum (rfl : r + t = r + t))).symm (j : GL (Fin (r + t)) k) ∈
      (parahoric (Fin r) (Fin t) χ hχ).J := j.2
  obtain ⟨hK, hC⟩ := mem_parahoric.1 hj
  obtain ⟨⟨g, hg, hgv⟩, D, hD, hDv⟩ := exists_diag_blocks hK hC
  have eA : leviProj k (two (stdSum (rfl : r + t = r + t))) p false = g := by
    apply Units.ext
    rw [hgv, ← h]
    ext a b
    rfl
  have eD : leviProj k (two (stdSum (rfl : r + t = r + t))) p true = D := by
    apply Units.ext
    rw [hDv, ← h]
    ext a b
    rfl
  have hl : (lev r t χ hχ).lam j = χ (GeneralLinearGroup.det D) :=
    parahoric_lam (⟨_, hj⟩ : (parahoric (Fin r) (Fin t) χ hχ).J) D hDv
  rw [hl]
  show deltaHalf k (Two (Fin r) (Fin t)) (leviProj k _ p) *
    χ (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : r + t = r + t))) p true)) = _
  rw [deltaHalf_apply, Fintype.prod_bool, eA, eD]
  have h1 := isUnram_absPow k ((modExp (Two (Fin r) (Fin t)) true : ℂ) / 2) _ (valuation_det_of_mem_KO hD)
  have h2 := isUnram_absPow k ((modExp (Two (Fin r) (Fin t)) false : ℂ) / 2) _ (valuation_det_of_mem_KO hg)
  rw [h1, h2, one_mul, one_mul]

theorem act_one (χ : kˣ →* ℂˣ) (p : parab k (two (stdSum (rfl : r + t = r + t)))) :
    ((twist ((extTensor (detRep (Fin r) (1 : kˣ →* ℂˣ)) (detRep (Fin t) χ)).comp
        (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) (deltaHalf k (Two (Fin r) (Fin t)))).comp
      (leviProj k (two (stdSum (rfl : r + t = r + t))))) p ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) =
    (leftChar r t χ p : ℂ) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) := by
  show (deltaHalf k (Two (Fin r) (Fin t)) (leviProj k _ p) : ℂ) •
    extTensor (detRep (Fin r) (1 : kˣ →* ℂˣ)) (detRep (Fin t) χ)
      ((leviTwo k (Fin r) (Fin t)).symm (leviProj k _ p)) ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = _
  rw [extTensor_tmul]
  simp only [detRep, ofChar_apply, detChar_apply, MonoidHom.one_apply, Units.val_one, mul_one]
  rw [show ∀ c : ℂ, (1 : ℂ) ⊗ₜ[ℂ] c = c • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) from fun c => by
    rw [← TensorProduct.tmul_smul, smul_eq_mul, mul_one], smul_smul]
  rfl

theorem exists_parahoricVec_prod₂_detRep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ), IsSmoothChar χ → IsTame χ → ∃ v, v ≠ 0 ∧ IsParahoricVec χ (prod₂ (detRep (Fin r) (1 : kˣ →* ℂˣ)) (detRep (Fin t) χ)) v := by
  intro k _ _ _ _ r t χ _ hχ
  obtain ⟨f, f1, fl, fr⟩ := exists_biequivariant (parab k (two (stdSum (rfl : r + t = r + t)))) (lev r t χ hχ).J
    (leftChar r t χ) (lev r t χ hχ).lam (leftChar_eq_lam χ hχ)
  have hK : ∀ g ∈ KOne k (Fin (r + t)), ∃ hg : g ∈ (lev r t χ hχ).J, (lev r t χ hχ).lam ⟨g, hg⟩ = 1 := by
    intro g hg
    have h1 : (reGL (stdSum (rfl : r + t = r + t))).symm g ∈ KOne k (Fin r ⊕ Fin t) := by
      rw [mem_KOne] at hg ⊢
      intro a b
      have := hg (stdSum rfl a) (stdSum rfl b)
      simpa [reGL_symm_val, Matrix.one_apply] using this
    exact ⟨(parahoric (Fin r) (Fin t) χ hχ).KOne_le h1, (parahoric (Fin r) (Fin t) χ hχ).lam_eq_one _ h1⟩
  have hnat : ∀ i : Fin t, stdSum (rfl : r + t = r + t) (Sum.inr i) = Fin.natAdd r i := fun i => Fin.ext (by simp)
  have hcast : ∀ i : Fin r, stdSum (rfl : r + t = r + t) (Sum.inl i) = Fin.castAdd t i := fun i => Fin.ext (by simp)
  let F : GL (Fin (r + t)) k → ℂ ⊗[ℂ] ℂ := fun g => f g • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
  have h11 : ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) ≠ 0 := fun h => by
    have := congrArg (TensorProduct.lid ℂ ℂ) h
    simp at this
  refine ⟨⟨⟨F, fun p g => ?_⟩, ?_⟩, ?_, ?_⟩
  · show f ((p : GL (Fin (r + t)) k) * g) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) =
      ((twist ((extTensor (detRep (Fin r) (1 : kˣ →* ℂˣ)) (detRep (Fin t) χ)).comp
        (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) (deltaHalf k (Two (Fin r) (Fin t)))).comp
      (leviProj k (two (stdSum (rfl : r + t = r + t))))) p (f g • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)))
    rw [map_smul, act_one, fl, smul_smul, mul_comm]
  · refine mem_smoothPart_of_nhds (Filter.mem_of_superset (isOpen_KOne.mem_nhds (one_mem _)) fun u hu => ?_)
    obtain ⟨hg, hl⟩ := hK u hu
    apply Subtype.ext
    funext x
    show f (x * u) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = f x • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
    have := fr x ⟨u, hg⟩
    rw [hl] at this
    simp only [Units.val_one, mul_one] at this
    rw [this]
  · intro h
    have h1 : F 1 = 0 := congrArg (fun v => v.1.1 1) h
    simp only [F, f1, one_smul] at h1
    exact h11 h1
  · intro h hh hC u hu
    have hK' : (reGL (stdSum (rfl : r + t = r + t))).symm h ∈ KO k (Fin r ⊕ Fin t) := by
      obtain ⟨a1, a2⟩ := mem_KO.1 hh
      refine mem_KO.2 ⟨fun a b => a1 _ _, ?_⟩
      rw [← map_inv]
      exact fun a b => a2 _ _
    have hC' : MaxM ((reGL (stdSum (rfl : r + t = r + t))).symm h).val.toBlocks₂₁ := by
      intro a b
      have := hC a b
      rw [← hnat, ← hcast] at this
      exact this
    have hj0 : (reGL (stdSum (rfl : r + t = r + t))).symm h ∈ (parahoric (Fin r) (Fin t) χ hχ).J :=
      mem_parahoric.2 ⟨hK', hC'⟩
    have hj : h ∈ (lev r t χ hχ).J := hj0
    obtain ⟨-, D, -, hDv⟩ := exists_diag_blocks hK' hC'
    have hl : (lev r t χ hχ).lam ⟨h, hj⟩ = χ u := by
      have hu' : GeneralLinearGroup.det D = u := by
        apply Units.ext
        rw [GeneralLinearGroup.val_det_apply, hDv, hu]
        congr 1
      rw [← hu']
      exact parahoric_lam (⟨_, hj0⟩ : (parahoric (Fin r) (Fin t) χ hχ).J) D hDv
    apply Subtype.ext
    apply Subtype.ext
    funext x
    show f (x * h) • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = (χ u : ℂ) • f x • ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
    have := fr x ⟨h, hj⟩
    rw [hl] at this
    rw [this, smul_smul, mul_comm]

end GlobalTheory.ParahoricVec
