import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAt
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantVanishingAtZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFunctionalLargeRankVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilInvariantFunctionalInductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitWeilEquivariantFunctionalUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitWeilEquivariantFunctionalBlockStatement

noncomputable section

open GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.DetEqv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mul_right_mem_SB {n d : ℕ} (c : ℂ) (A : GL (Fin d) k) (Φ : Matrix (Fin n) (Fin d) k → ℂ)
    (hΦ : Φ ∈ SB (Matrix (Fin n) (Fin d) k)) :
    (fun X => c * Φ (X * (A : Matrix (Fin d) (Fin d) k))) ∈ SB (Matrix (Fin n) (Fin d) k) := by
  let e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
    { toFun := fun X => X * (A : Matrix (Fin d) (Fin d) k)
      invFun := fun X => X * ((A⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k)
      left_inv := fun X => by simp [Matrix.mul_assoc]
      right_inv := fun X => by simp [Matrix.mul_assoc]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  refine ⟨(IsLocallyConstant.const c).mul (hΦ.1.comp_continuous e.continuous), ?_⟩
  exact (hΦ.2.comp_homeomorph e).mul_left

theorem vanishAt_all : ∀ n : ℕ, VanishAt k n
  | 0 => GlobalTheory.T.determinant_vanishing_at_zero k
  | n + 1 => by
    intro Y _ m hm μ hμ L hL
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact GlobalTheory.T.invariant_functional_large_rank_vanish k n (vanishAt_all n) Y (m' + 1) hm μ hμ L hL (fun Φ hΦ =>
      GlobalTheory.T.weil_invariant_functional_induction k n Y m' μ L hL (fun Φ' hΦ' =>
        GlobalTheory.T.split_weil_equivariant_functional_unique k n (vanishAt_all n) Y m' (by omega) μ hμ L hL Φ' hΦ') Φ hΦ)

theorem transpose_inv_leviEmb (x x' : ℕ) (g : GL (Fin (![x, x'] 1)) k) :
    (((leviEmb k (GlobalTheory.ThK.MidJac.e2 x x') (Pi.mulSingle (1 : Fin 2) (GlobalTheory.SplitFlip.invT g)))⁻¹ :
        GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k).transpose =
      ((leviEmb k (GlobalTheory.ThK.MidJac.e2 x x') (Pi.mulSingle (1 : Fin 2) g) : GL (Fin (x + x')) k) :
        Matrix (Fin (x + x')) (Fin (x + x')) k) := by
  rw [← map_inv, ← Pi.mulSingle_inv]
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (GlobalTheory.ThK.MidJac.e2 x x').surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (GlobalTheory.ThK.MidJac.e2 x x').surjective j
  rw [Matrix.transpose_apply]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, leviEmb_apply_same]
    by_cases ha : a = 1
    · subst ha
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, GlobalTheory.SplitFlip.invT_inv_val, Matrix.transpose_apply]
    · rw [Pi.mulSingle_eq_of_ne ha, Pi.mulSingle_eq_of_ne ha]
      simp [Matrix.one_apply, eq_comm]
  · rw [leviEmb_apply_ne _ _ _ (Ne.symm hab), leviEmb_apply_ne _ _ _ hab]

end GlobalTheory.DetEqv

namespace GlobalTheory.DetEqv

theorem modExp_two_one (x x' : ℕ) : modExp (fun a : Fin 2 => Fin (![x, x'] a)) 1 = -(x : ℤ) := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_two]

theorem no_map_of_lt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x x' n : ℕ), n < x' → ∀ (α β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar α → GlobalTheory.SmGL.IsSmoothChar β → (∀ t : ℝ, α * β⁻¹ ≠ GlobalTheory.SmGL.absPow k (t : ℂ)) →
    ∀ T : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin (x + x')) k) →ₗ[ℂ]
        GlobalTheory.SmGL.IndSp (GlobalTheory.ThK.MidJac.e2 x x') (GlobalTheory.SmGL.ofChar (GlobalTheory.ThK.DetProd.twoDet x x' α β)),
      (∀ (h : GL (Fin (x + x')) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin (x + x')) k)),
        (∀ X, (Φ' : Matrix (Fin n) (Fin (x + x')) k → ℂ) X = (α (Matrix.GeneralLinearGroup.det h) : ℂ) *
          ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
          (Φ : Matrix (Fin n) (Fin (x + x')) k → ℂ) (X * Matrix.transpose ((h⁻¹ : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k))) →
        T Φ' = GlobalTheory.ThK.MidJac.detInd x x' α β h (T Φ)) →
      T = 0 := by
  intro k _ _ _ _ x x' n hn α β _ _ hαβ T hT
  let L : SB (Matrix (Fin n) (Fin (x + x')) k) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => (T Φ).1.1 1
      map_add' := fun Φ Ψ => by simp only [map_add]; rfl
      map_smul' := fun c Φ => by simp only [map_smul]; rfl }
  have hmod : ∀ (h : GL (Fin (x + x')) k) (Φ : SB (Matrix (Fin n) (Fin (x + x')) k)),
      ∃ Φ' : SB (Matrix (Fin n) (Fin (x + x')) k), ∀ X, (Φ' : Matrix (Fin n) (Fin (x + x')) k → ℂ) X =
        (α (Matrix.GeneralLinearGroup.det h) : ℂ) *
          ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
          (Φ : Matrix (Fin n) (Fin (x + x')) k → ℂ)
            (X * Matrix.transpose ((h⁻¹ : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k)) :=
    fun h Φ => ⟨⟨_, mul_right_mem_SB ((α (Matrix.GeneralLinearGroup.det h) : ℂ) *
          ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) : ℝ) : ℂ)) (GlobalTheory.SplitFlip.invT h) _ Φ.2⟩,
      fun X => rfl⟩
  have hval : ∀ (h : GL (Fin (x + x')) k) (Φ Φ' : SB (Matrix (Fin n) (Fin (x + x')) k)),
      (∀ X, (Φ' : Matrix (Fin n) (Fin (x + x')) k → ℂ) X =
        (α (Matrix.GeneralLinearGroup.det h) : ℂ) *
          ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
          (Φ : Matrix (Fin n) (Fin (x + x')) k → ℂ)
            (X * Matrix.transpose ((h⁻¹ : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k))) →
      L Φ' = (T Φ).1.1 h := by
    intro h Φ Φ' hΦ'
    show (T Φ').1.1 1 = _
    rw [hT h Φ Φ' hΦ']
    show (parInd _ _ h (T Φ)).1.1 1 = _
    rw [parInd_apply, one_mul]
  have hL : L = 0 := by
    refine GlobalTheory.T.split_weil_equivariant_functional_block k x x' n (vanishAt_all n) hn (α * β⁻¹ * absPow k (((x : ℂ) - n) / 2)) ?_ L ?_
    · intro t ht
      apply hαβ (t - ((x : ℝ) - n) / 2)
      rw [show (((t - ((x : ℝ) - n) / 2 : ℝ)) : ℂ) = (t : ℂ) + -(((x : ℂ) - n) / 2) by push_cast; ring,
        absPow_add, absPow_neg, ← ht, mul_inv_cancel_right]
    · intro g Φ Φ' hΦ'
      set u := GlobalTheory.SplitFlip.invT g with hu
      set h := leviEmb k (GlobalTheory.ThK.MidJac.e2 x x') (Pi.mulSingle (1 : Fin 2) u) with hh
      obtain ⟨Φ₁, hΦ₁⟩ := hmod h Φ
      set c : ℂ := (α (Matrix.GeneralLinearGroup.det h) : ℂ) *
          ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) with hc
      have e1 : Φ₁ = c • Φ' := by
        refine Subtype.ext (funext fun X => ?_)
        rw [hΦ₁, hh, hu, transpose_inv_leviEmb, ← hΦ']
        rfl
      have h1 := hval h Φ Φ₁ hΦ₁
      rw [e1, map_smul, smul_eq_mul] at h1
      have h2 := parInd_law (GlobalTheory.ThK.MidJac.e2 x x') (ofChar (GlobalTheory.ThK.DetProd.twoDet x x' α β)) (T Φ)
        ⟨h, leviEmb_mem_parab k _ _⟩ 1
      rw [mul_one] at h2
      change (T Φ).1.1 h = _ at h2
      rw [leviProj_leviEmb, ofChar_apply] at h2
      have hdh : Matrix.GeneralLinearGroup.det h = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
        rw [hh, det_leviEmb, Fin.prod_univ_two, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide),
          map_one, one_mul, hu]
        exact GlobalTheory.SplitFlip.gdet_invT g
      have hdu : Matrix.GeneralLinearGroup.det u = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
        rw [hu]; exact GlobalTheory.SplitFlip.gdet_invT g
      have hδ : deltaHalf k (fun a : Fin 2 => Fin (![x, x'] a)) (Pi.mulSingle (1 : Fin 2) u) =
          absPow k (((-(x : ℤ) : ℤ) : ℂ) / 2) (Matrix.GeneralLinearGroup.det u) := by
        rw [deltaHalf_apply, Fin.prod_univ_two, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide),
          map_one, map_one, one_mul, modExp_two_one]
      have htw : GlobalTheory.ThK.DetProd.twoDet x x' α β (Pi.mulSingle (1 : Fin 2) u) =
          β (Matrix.GeneralLinearGroup.det u) := by
        change α (Matrix.GeneralLinearGroup.det ((Pi.mulSingle (1 : Fin 2) u : ∀ a : Fin 2, GL (Fin (![x, x'] a)) k) 0)) *
          β (Matrix.GeneralLinearGroup.det ((Pi.mulSingle (1 : Fin 2) u : ∀ a : Fin 2, GL (Fin (![x, x'] a)) k) 1)) = _
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide), map_one, map_one, one_mul]
      rw [h2, hδ, htw, hdu, smul_eq_mul] at h1
      rw [hc, hdh] at h1
      set t := Matrix.GeneralLinearGroup.det g
      have hP : ∀ s : ℝ, (((nabs k t⁻¹ ^ s : ℝ)) : ℂ) = ((absPow k (s : ℂ) t)⁻¹ : ℂˣ) := by
        intro s
        rw [← val_absPow_ofReal, map_inv]
      rw [hP] at h1
      have hrel : absPow k (((x : ℂ) - n) / 2) t * absPow k (((-(x : ℤ) : ℤ) : ℂ) / 2) t =
          absPow k ((-(n : ℝ) / 2 : ℝ) : ℂ) t := by
        rw [← MonoidHom.mul_apply, ← absPow_add]
        congr 2
        push_cast; ring
      have hne : ∀ z : ℂˣ, (z : ℂ) ≠ 0 := fun z => z.ne_zero
      show L Φ' = ((α * β⁻¹ * absPow k (((x : ℂ) - n) / 2)) t : ℂ) * L Φ
      rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply]
      rw [map_inv, map_inv, map_inv] at h1
      rw [← hrel] at h1
      have hA := hne (α t)
      have hB := hne (β t)
      have hC := hne (absPow k (((x : ℂ) - n) / 2) t)
      have hD := hne (absPow k (((-(x : ℤ) : ℤ) : ℂ) / 2) t)
      push_cast at h1 ⊢
      field_simp at h1 ⊢
      linear_combination h1
  refine LinearMap.ext fun Φ => Subtype.ext (Subtype.ext (funext fun g => ?_))
  obtain ⟨Φ₁, hΦ₁⟩ := hmod g Φ
  rw [← hval g Φ Φ₁ hΦ₁]
  show L Φ₁ = _
  rw [hL]
  rfl

end GlobalTheory.DetEqv
