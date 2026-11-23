import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeInvLeviEmb
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGlLocalComponentExponentLeOne

noncomputable section

open GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.PRep

namespace GlobalTheory.DetEqv.Pairing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem twoDet_inv_apply (x x' : ℕ) (α β : kˣ →* ℂˣ) (g : Levi k (fun a : Fin 2 => Fin (![x, x'] a))) :
    GlobalTheory.ThK.DetProd.twoDet x x' α⁻¹ β⁻¹ g = (GlobalTheory.ThK.DetProd.twoDet x x' α β g)⁻¹ := by
  simp only [GlobalTheory.ThK.DetProd.twoDet, detChar, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, mul_inv]

theorem continuous_invT {d : ℕ} : Continuous (GlobalTheory.SplitFlip.invT (k := k) (D := Fin d)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.comp continuous_inv).matrix_transpose
  · exact Units.continuous_val.matrix_transpose

theorem nabs_inv (t : kˣ) : nabs k t⁻¹ = (nabs k t)⁻¹ := by
  simp [nabs, map_inv]

theorem om_invT (α : kˣ →* ℂˣ) {n d : ℕ} (h : GL (Fin d) k) (Φ : Matrix (Fin n) (Fin d) k → ℂ)
    (X : Matrix (Fin n) (Fin d) k) :
    om α (GlobalTheory.SplitFlip.invT h) (1 : GL (Fin n) k) Φ X =
      ((α (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) *
        ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
        Φ (X * Matrix.transpose ((h⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k)) := by
  have hd : Matrix.GeneralLinearGroup.det (GlobalTheory.SplitFlip.invT h) = (Matrix.GeneralLinearGroup.det h)⁻¹ :=
    GlobalTheory.SplitFlip.gdet_invT h
  have hv : ((GlobalTheory.SplitFlip.invT h : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) =
      ((h⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).transpose := rfl
  have hpos := nabs_pos' k (Matrix.GeneralLinearGroup.det h)
  have hr : (nabs k (Matrix.GeneralLinearGroup.det h))⁻¹ ^ ((n : ℝ) / 2) =
      nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) := by
    rw [Real.inv_rpow hpos.le, neg_div, Real.rpow_neg hpos.le]
  have h1 : nabs k (1 : kˣ) = 1 := by simp [nabs]
  simp only [om, hd, h1, map_inv, map_one, inv_one, Units.val_one, mul_one, Fintype.card_fin, hv, Matrix.one_mul,
    nabs_inv, hr, Real.one_rpow, Complex.ofReal_one, mul_one]

theorem stab_mem_nhds (α : kˣ →* ℂˣ) (hα : IsSmoothChar α) {n d : ℕ} (Φ : SB (Matrix (Fin n) (Fin d) k)) :
    {h : GL (Fin d) k | ∀ X, (Φ : Matrix (Fin n) (Fin d) k → ℂ) X =
      ((α (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) *
        ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
        (Φ : Matrix (Fin n) (Fin d) k → ℂ) (X * Matrix.transpose ((h⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k))} ∈
      nhds (1 : GL (Fin d) k) := by
  have hO := (om_isSmoothRepresentation k (Fin d) (Fin n) α hα).2.2.2.2 Φ.1 Φ.2
  have hc : Continuous (fun h : GL (Fin d) k => (GlobalTheory.SplitFlip.invT h, (1 : GL (Fin n) k))) :=
    continuous_invT.prodMk continuous_const
  refine Filter.mem_of_superset ((hO.preimage hc).mem_nhds ?_) ?_
  · show om α (GlobalTheory.SplitFlip.invT 1) 1 Φ.1 = Φ.1
    rw [map_one]
    exact (om_isSmoothRepresentation k (Fin d) (Fin n) α hα).1 _
  · intro h hh X
    have := congrFun (show om α (GlobalTheory.SplitFlip.invT h) 1 Φ.1 = Φ.1 from hh) X
    rw [om_invT] at this
    exact this.symm

def evOne {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (χ ψ : G →* ℂˣ)
    (h : ∀ g, ψ g = (χ g)⁻¹) : (contra (ofChar χ)).IntertwiningMap (ofChar ψ) where
  toLinearMap :=
    { toFun := fun l => (l : Module.Dual ℂ ℂ) 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' g := by
    refine LinearMap.ext fun l => ?_
    show (l : Module.Dual ℂ ℂ) (ofChar χ g⁻¹ 1) = ofChar ψ g ((l : Module.Dual ℂ ℂ) 1)
    rw [ofChar_apply, ofChar_apply, h, mul_one, map_inv]
    have hs := (l : Module.Dual ℂ ℂ).map_smul (((χ g)⁻¹ : ℂˣ) : ℂ) 1
    rw [smul_eq_mul, mul_one] at hs
    rw [hs, smul_eq_mul]

theorem eq_zero_of_apply_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (χ : G →* ℂˣ)
    (l : smoothPart (ofChar χ).dual) (hl : (l : Module.Dual ℂ ℂ) 1 = 0) : l = 0 := by
  refine Subtype.ext (LinearMap.ext fun c => ?_)
  rw [show c = c • (1 : ℂ) by rw [smul_eq_mul, mul_one], map_smul, hl, smul_zero]
  rfl

end GlobalTheory.DetEqv.Pairing

namespace GlobalTheory.DetEqv

open GlobalTheory.DetEqv.Pairing

theorem no_pairing_of_lt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x x' n : ℕ), n < x' → ∀ (α β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar α → GlobalTheory.SmGL.IsSmoothChar β → (∀ t : ℝ, α * β⁻¹ ≠ GlobalTheory.SmGL.absPow k (t : ℂ)) →
    ∀ P : GlobalTheory.SmGL.IndSp (GlobalTheory.ThK.MidJac.e2 x x') (GlobalTheory.SmGL.ofChar (GlobalTheory.ThK.DetProd.twoDet x x' α β)) →ₗ[ℂ]
        GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin (x + x')) k) →ₗ[ℂ] ℂ,
      (∀ (h : GL (Fin (x + x')) k) u (Φ Φ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin (x + x')) k)),
        (∀ X, (Φ' : Matrix (Fin n) (Fin (x + x')) k → ℂ) X = ((α (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) *
          ((GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
          (Φ : Matrix (Fin n) (Fin (x + x')) k → ℂ) (X * Matrix.transpose ((h⁻¹ : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k))) →
        P (GlobalTheory.ThK.MidJac.detInd x x' α β h u) Φ' = P u Φ) →
      P = 0 := by
  intro k _ _ _ _ x x' n hn α β hα hβ hαβ P hP
  let e := GlobalTheory.ThK.MidJac.e2 x x'
  let ρ := ofChar (GlobalTheory.ThK.DetProd.twoDet x x' α β)
  have hρ : IsSmooth ρ := (isSmooth_ofChar_iff _).2 (GlobalTheory.ThK.DetProd.isSmoothChar_twoDet x x' hα hβ)
  obtain ⟨Ψ⟩ := InductionContragredient.nonempty_equiv (IndDual.inductionContragredient k) e hρ
  have hcancel : ∀ (h : GL (Fin (x + x')) k) (u : IndSp e ρ), parInd e ρ h (parInd e ρ h⁻¹ u) = u := by
    intro h u
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hsm : ∀ Φ : SB (Matrix (Fin n) (Fin (x + x')) k),
      (P.flip Φ : Module.Dual ℂ (IndSp e ρ)) ∈ smoothPart (parInd e ρ).dual := by
    intro Φ
    refine mem_smoothPart_of_nhds (Filter.mem_of_superset (stab_mem_nhds α hα Φ) ?_)
    intro h hh
    show (parInd e ρ).dual h (P.flip Φ) = P.flip Φ
    refine LinearMap.ext fun u => ?_
    show P (parInd e ρ h⁻¹ u) Φ = P u Φ
    have := hP h (parInd e ρ h⁻¹ u) Φ Φ hh
    rw [← this]
    exact congrArg (fun v => P v Φ) (hcancel h u)
  let L : SB (Matrix (Fin n) (Fin (x + x')) k) →ₗ[ℂ] smoothPart (parInd e ρ).dual :=
    { toFun := fun Φ => ⟨P.flip Φ, hsm Φ⟩
      map_add' := fun a b => Subtype.ext (map_add P.flip a b)
      map_smul' := fun c a => Subtype.ext (map_smul P.flip c a) }
  let ev := evOne (GlobalTheory.ThK.DetProd.twoDet x x' α β) (GlobalTheory.ThK.DetProd.twoDet x x' α⁻¹ β⁻¹)
    (twoDet_inv_apply x x' α β)
  let T : SB (Matrix (Fin n) (Fin (x + x')) k) →ₗ[ℂ]
      IndSp e (ofChar (GlobalTheory.ThK.DetProd.twoDet x x' α⁻¹ β⁻¹)) :=
    (parIndMap e ev).toLinearMap ∘ₗ Ψ.symm.toIntertwiningMap.toLinearMap ∘ₗ L
  have hne : ∀ t : ℝ, α⁻¹ * β⁻¹⁻¹ ≠ absPow k (t : ℂ) := by
    intro t ht
    apply hαβ (-t)
    rw [show (((-t : ℝ)) : ℂ) = -(t : ℂ) by push_cast; ring, absPow_neg, ← ht]
    simp only [mul_inv, inv_inv]
  have hT : ∀ (h : GL (Fin (x + x')) k) (Φ Φ' : SB (Matrix (Fin n) (Fin (x + x')) k)),
      (∀ X, (Φ' : Matrix (Fin n) (Fin (x + x')) k → ℂ) X = ((α⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
          (Φ : Matrix (Fin n) (Fin (x + x')) k → ℂ)
            (X * Matrix.transpose ((h⁻¹ : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k))) →
      T Φ' = GlobalTheory.ThK.MidJac.detInd x x' α⁻¹ β⁻¹ h (T Φ) := by
    intro h Φ Φ' hΦ'
    have hL : L Φ' = contra (parInd e ρ) h (L Φ) := by
      refine Subtype.ext (LinearMap.ext fun u => ?_)
      show P u Φ' = P (parInd e ρ h⁻¹ u) Φ
      have := hP h (parInd e ρ h⁻¹ u) Φ Φ' (fun X => by rw [hΦ' X, MonoidHom.inv_apply])
      rw [← this]
      exact congrArg (fun v => P v Φ') (hcancel h u).symm
    have i1 : Ψ.symm.toIntertwiningMap.toLinearMap (contra (parInd e ρ) h (L Φ)) =
        parInd e (contra ρ) h (Ψ.symm.toIntertwiningMap.toLinearMap (L Φ)) :=
      LinearMap.congr_fun (Ψ.symm.toIntertwiningMap.isIntertwining' h) (L Φ)
    have i2 : (parIndMap e ev).toLinearMap (parInd e (contra ρ) h (Ψ.symm.toIntertwiningMap.toLinearMap (L Φ))) =
        parInd e (ofChar (GlobalTheory.ThK.DetProd.twoDet x x' α⁻¹ β⁻¹)) h
          ((parIndMap e ev).toLinearMap (Ψ.symm.toIntertwiningMap.toLinearMap (L Φ))) :=
      LinearMap.congr_fun ((parIndMap e ev).isIntertwining' h) (Ψ.symm.toIntertwiningMap.toLinearMap (L Φ))
    show (parIndMap e ev).toLinearMap (Ψ.symm.toIntertwiningMap.toLinearMap (L Φ')) =
      parInd e (ofChar (GlobalTheory.ThK.DetProd.twoDet x x' α⁻¹ β⁻¹)) h
        ((parIndMap e ev).toLinearMap (Ψ.symm.toIntertwiningMap.toLinearMap (L Φ)))
    exact (congrArg (fun l => (parIndMap e ev).toLinearMap (Ψ.symm.toIntertwiningMap.toLinearMap l)) hL).trans
      ((congrArg (parIndMap e ev).toLinearMap i1).trans i2)
  have hT0 := no_map_of_lt k x x' n hn α⁻¹ β⁻¹ hα.inv hβ.inv hne T hT
  refine LinearMap.ext fun u => LinearMap.ext fun Φ => ?_
  have h0 : T Φ = 0 := by rw [hT0]; rfl
  have h1 : Ψ.symm.toIntertwiningMap.toLinearMap (L Φ) = 0 := by
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    have hg := congrArg (fun f : IndSp e (ofChar (GlobalTheory.ThK.DetProd.twoDet x x' α⁻¹ β⁻¹)) => f.1.1 g) h0
    change (((Ψ.symm.toIntertwiningMap.toLinearMap (L Φ)).1.1 g : smoothPart (ofChar
      (GlobalTheory.ThK.DetProd.twoDet x x' α β)).dual) : Module.Dual ℂ ℂ) 1 = 0 at hg
    exact eq_zero_of_apply_one _ _ hg
  have h2 : L Φ = 0 := by
    have h1' : Ψ.symm.toLinearEquiv (L Φ) = 0 := h1
    exact (LinearEquiv.map_eq_zero_iff _).1 h1'
  have h3 := congrArg (fun l : smoothPart (parInd e ρ).dual => (l : Module.Dual ℂ (IndSp e ρ)) u) h2
  exact h3

end GlobalTheory.DetEqv
