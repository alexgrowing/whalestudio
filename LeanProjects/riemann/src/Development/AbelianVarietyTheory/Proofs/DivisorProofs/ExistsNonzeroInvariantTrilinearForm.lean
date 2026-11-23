import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwiningMapIntoInducedRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedRepresentationIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedCharIntertwiningUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient

noncomputable section

open MeasureTheory Matrix Filter Topology GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
  GlobalTheory.ThK.DetProd GlobalTheory.ThK.MidJac

namespace GlobalTheory.TrivPair

private def idForm {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (χ : G →* ℂˣ) (hχ : IsSmoothChar χ) :
    smoothPart (ofChar χ).dual :=
  ⟨LinearMap.id, mem_smoothPart_of_nhds (Filter.mem_of_superset (hχ.mem_nhds (one_mem χ.ker)) fun g hg => by
    have hg' : χ g = 1 := MonoidHom.mem_ker.1 hg
    refine LinearMap.ext fun v => ?_
    show (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (ofChar χ g⁻¹ v) = v
    simp [hg'])⟩

private def lineToContra {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (χ χ' : G →* ℂˣ)
    (hχ : IsSmoothChar χ) (h : ∀ g, χ' g = χ g⁻¹) : (ofChar χ').IntertwiningMap (contra (ofChar χ)) where
  toLinearMap := LinearMap.toSpanSingleton ℂ _ (idForm χ hχ)
  isIntertwining' g := by
    refine LinearMap.ext fun c => Subtype.ext (LinearMap.ext fun v => ?_)
    show (ofChar χ' g c) * v = c * (ofChar χ g⁻¹ v)
    rw [ofChar_apply, ofChar_apply, h g]
    ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section MapB

variable {a a' : ℕ} {ν α β : kˣ →* ℂˣ}

private theorem mapB_add' {z : ℂ} {l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ} (hl : IsEqv ν z l)
    {Φ Φ' : Matrix (Fin a') (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) (h' : Φ' ∈ SB _) :
    mapB a l ν α (Φ + Φ') = mapB a l ν α Φ + mapB a l ν α Φ' := by
  funext x
  rw [Pi.add_apply, mapB, mapB, mapB, ← hl.1 _ (restrict_Y0 (omB_mem_SB ν α 1 x h)) _ (restrict_Y0 (omB_mem_SB ν α 1 x h'))]
  congr 1
  funext g
  simp only [omB, Pi.add_apply, mul_add]

private theorem mapB_smul' {z : ℂ} {l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ} (hl : IsEqv ν z l) (c : ℂ)
    {Φ : Matrix (Fin a') (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) : mapB a l ν α (c • Φ) = c • mapB a l ν α Φ := by
  funext x
  rw [Pi.smul_apply, smul_eq_mul, mapB, mapB, ← hl.2.1 c _ (restrict_Y0 (omB_mem_SB ν α 1 x h))]
  congr 1
  funext g
  simp only [omB, Pi.smul_apply, smul_eq_mul]
  ring

private theorem mapB_omB_left' {l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ} (hl : IsEqv ν (((a + a' : ℕ) : ℂ) / 2) l) (g : GL (Fin a') k)
    {Φ : Matrix (Fin a') (Fin (a + a')) k → ℂ} (h : Φ ∈ SB _) : mapB a l ν α (omB ν α g 1 Φ) = mapB a l ν α Φ := by
  funext x
  have hs := restrict_Y0 (omB_mem_SB ν α 1 x h)
  have e : omB ν α 1 x (omB ν α g 1 Φ) = omB ν α g 1 (omB ν α 1 x Φ) := by
    rw [← omB_mul, ← omB_mul, one_mul, mul_one, one_mul, mul_one]
  have hd : gdet (invT g)⁻¹ = gdet g := by rw [gdet, map_inv, ← gdet, gdet_invT, inv_inv]
  rw [mapB, mapB, e, ← hl.2.2 (invT g)⁻¹ 1 _ hs, ← hl.2.1 _ _ (comp_mul_mem_SB (invT g)⁻¹ 1 hs), hd]
  congr 1
  funext y
  simp only [omB, Pi.smul_apply, smul_eq_mul, map_one, mul_one, Units.val_one, Matrix.mul_one, apow_one,
    Fintype.card_fin, Matrix.mul_assoc, invT_inv_val, transpose_one, Matrix.one_mul, one_mul]

private theorem mapB_ne_zero' {l : (Matrix (Fin a') (Fin a') k → ℂ) → ℂ} (hl : ∃ φ ∈ SB _, l φ ≠ 0) :
    ∃ Φ ∈ SB (Matrix (Fin a') (Fin (a + a')) k), mapB a l ν α Φ 1 ≠ 0 := by
  obtain ⟨φ, hφ, h0⟩ := hl
  have hf := frame_rel (k := k) (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a'))
  obtain ⟨Φ, hΦ, h⟩ := exists_extend_SB hf.2.1 hf.2.2.2.1 ((add_comm _ _).trans hf.2.2.2.2) hφ
  refine ⟨Φ, hΦ, ?_⟩
  have e : omB ν α 1 1 Φ = Φ := by funext X; simp [omB]
  rw [mapB, e, funext h]
  exact h0

private theorem IsSmU_div' (hα : IsSmU α) (hβ : IsSmU β) : IsSmU (α / β) := by
  refine ⟨Subgroup.isOpen_mono (H₁ := α.ker ⊓ β.ker) (fun x hx => ?_) (hα.1.inter hβ.1), fun x => ?_⟩
  · rw [MonoidHom.mem_ker, MonoidHom.div_apply, hx.1, hx.2, div_one]
  · rw [MonoidHom.div_apply, Units.val_div_eq_div_val, norm_div, hα.2, hβ.2, div_one]

end MapB

private theorem twoDet_inv' (x x' : ℕ) (α β : kˣ →* ℂˣ) (g : Levi k (fun a : Fin 2 => Fin (![x, x'] a))) :
    twoDet x x' α⁻¹ β⁻¹ g = twoDet x x' α β g⁻¹ := by
  simp only [twoDet, detChar, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv, mul_inv]

private theorem isSmoothChar_twoDet'' (x x' : ℕ) {χ₁ χ₂ : kˣ →* ℂˣ} (h₁ : IsSmoothChar χ₁) (h₂ : IsSmoothChar χ₂) :
    IsSmoothChar (twoDet x x' χ₁ χ₂) :=
  (h₁.detChar.comp _ (continuous_apply (0 : Fin 2))).mul (h₂.detChar.comp _ (continuous_apply (1 : Fin 2)))

private theorem exists_vec_of_mem_indSp {x x' : ℕ} (α' β' : kˣ →* ℂˣ) {f : GL (Fin (x + x')) k → ℂ}
    (hf : f ∈ indSp x x' α' β') : ∃ F : IndSp (e2 x x') (ofChar (twoDet x x' α' β')), F.1.1 = f := by
  rw [indSp_eq_indScal] at hf
  have := GlobalTheory.DetIndScal.exists_of_mem_indScal _ _ x x' hf
  rwa [inv_mul_cancel_right] at this

private theorem isSmU_inv {χ : kˣ →* ℂˣ} (h : IsSmU χ) : IsSmU χ⁻¹ :=
  ⟨IsSmoothChar.inv (χ := χ) h.1, fun x => by simp [h.2 x]⟩

end GlobalTheory.TrivPair

set_option maxHeartbeats 1600000 in
open GlobalTheory.TrivPair in

theorem _root_.GlobalTheory.T.exists_nonzero_invariant_trilinear_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x x' : ℕ), x' ≤ x → ∀ (α β : kˣ →* ℂˣ), GlobalTheory.KSplit.IsSmU α → GlobalTheory.KSplit.IsSmU β →
    ∃ P : GlobalTheory.SplitWeil.SB (Matrix (Fin x') (Fin (x + x')) k) →ₗ[ℂ] GlobalTheory.SmGL.IndSp (GlobalTheory.ThK.MidJac.e2 x x') (GlobalTheory.SmGL.ofChar (GlobalTheory.ThK.DetProd.twoDet x x' α β)) →ₗ[ℂ] ℂ, P ≠ 0 ∧
      ∀ (g : GL (Fin x') k) (h : GL (Fin (x + x')) k) (Ψ Ψ' : GlobalTheory.SplitWeil.SB (Matrix (Fin x') (Fin (x + x')) k)),
        (Ψ' : Matrix (Fin x') (Fin (x + x')) k → ℂ) = GlobalTheory.SplitFlip.omB (α / β)⁻¹ α⁻¹ g h Ψ →
          ∀ u, P Ψ' (GlobalTheory.ThK.MidJac.detInd x x' α β h u) = P Ψ u := by
  intro k _ _ _ _ x x' hxx α β hα hβ
  borelize k
  have hν : IsSmU (α / β)⁻¹ := by rw [inv_div]; exact IsSmU_div' hβ hα
  have hνe : α⁻¹ / β⁻¹ = (α / β)⁻¹ := (inv_div_inv α β).trans (inv_div α β).symm
  have hzr : (x' : ℝ) - 1 < ((((x + x' : ℕ) : ℂ) / 2)).re := by
    have e : ((((x + x' : ℕ) : ℂ) / 2)).re = ((x : ℝ) + x') / 2 := by simp
    have : (x' : ℝ) ≤ x := by exact_mod_cast hxx
    rw [e]; linarith
  obtain ⟨hl, φ₀, hφ₀, hl0⟩ := GlobalTheory.GJForm.isEqv_integral_and_ne_zero k x' (α / β)⁻¹ _ hν hzr
  set l : (Matrix (Fin x') (Fin x') k → ℂ) → ℂ := fun φ => ∫ g : GL (Fin x') k, φ g.val * ((α / β)⁻¹ (gdet g) : ℂ) *
    apow (gdet g) (((x + x' : ℕ) : ℂ) / 2) ∂(haarVol (KO k (Fin x'))) with hld
  have hl' : IsEqv (α⁻¹ / β⁻¹) (((x + x' : ℕ) : ℂ) / 2) l := hνe ▸ hl
  have hmem : ∀ Ψ : SB (Matrix (Fin x') (Fin (x + x')) k), mapB x l (α / β)⁻¹ α⁻¹ Ψ ∈ indSp x x' α⁻¹ β⁻¹ := fun Ψ => by
    have := mapB_mem_indSp k x x' α⁻¹ β⁻¹ l (isSmU_inv hα) hl' Ψ Ψ.2
    rwa [hνe] at this
  choose F hF using fun Ψ => exists_vec_of_mem_indSp α⁻¹ β⁻¹ (hmem Ψ)
  obtain ⟨Fm, hFm⟩ : ∃ Fm : SB (Matrix (Fin x') (Fin (x + x')) k) →ₗ[ℂ] IndSp (e2 x x') (ofChar (twoDet x x' α⁻¹ β⁻¹)),
      ∀ Ψ, (Fm Ψ).1.1 = mapB x l (α / β)⁻¹ α⁻¹ Ψ :=
    ⟨{ toFun := F
       map_add' := fun Ψ Ψ' => Subtype.ext (Subtype.ext (by
         show (F (Ψ + Ψ')).1.1 = (F Ψ).1.1 + (F Ψ').1.1
         rw [hF, hF, hF]; exact mapB_add' hl Ψ.2 Ψ'.2))
       map_smul' := fun c Ψ => Subtype.ext (Subtype.ext (by
         show (F (c • Ψ)).1.1 = c • (F Ψ).1.1
         rw [hF, hF]; exact mapB_smul' hl c Ψ.2)) }, hF⟩
  have hχ : IsSmoothChar (twoDet x x' α β) := isSmoothChar_twoDet'' x x' hα.1 hβ.1
  have hE := twoDet_inv' x x' α β
  have hρ : IsSmooth (ofChar (twoDet x x' α β)) := (isSmooth_ofChar_iff _).2 hχ
  let E := lineToContra (twoDet x x' α β) (twoDet x x' α⁻¹ β⁻¹) hχ hE
  obtain ⟨Φ⟩ := InductionContragredient.nonempty_equiv (IndDual.inductionContragredient k) (e2 x x') hρ
  let P := (smoothPart (parInd (e2 x x') (ofChar (twoDet x x' α β))).dual).subtype ∘ₗ
      Φ.toIntertwiningMap.toLinearMap ∘ₗ (parIndMap (e2 x x') E).toLinearMap ∘ₗ Fm
  have hP : ∀ Ψ u, P Ψ u = (Φ.toIntertwiningMap (parIndMap (e2 x x') E (Fm Ψ)) :
        Module.Dual ℂ (IndSp (e2 x x') (ofChar (twoDet x x' α β)))) u := fun _ _ => rfl
  refine ⟨P, ?_, ?_⟩
  · intro hP0
    obtain ⟨Ψ₀, hΨ₀, h0⟩ := mapB_ne_zero' (a := x) (ν := (α / β)⁻¹) (α := α⁻¹) (l := l) ⟨φ₀, hφ₀, hl0⟩
    have hw : Φ.toLinearEquiv (parIndMap (e2 x x') E (Fm ⟨Ψ₀, hΨ₀⟩)) = 0 := by
      refine Subtype.ext (LinearMap.ext fun u => ?_)
      have h2 := hP ⟨Ψ₀, hΨ₀⟩ u
      rw [hP0] at h2
      exact h2.symm
    have hw' := (LinearEquiv.map_eq_zero_iff _).1 hw
    have h3 := congrArg (fun G : IndSp (e2 x x') (contra (ofChar (twoDet x x' α β))) =>
      ((G.1.1 1 : smoothPart (ofChar (twoDet x x' α β)).dual) : Module.Dual ℂ ℂ) 1) hw'
    change ((E ((Fm ⟨Ψ₀, hΨ₀⟩).1.1 1) : smoothPart (ofChar (twoDet x x' α β)).dual) : Module.Dual ℂ ℂ) 1 = 0 at h3
    rw [hFm] at h3
    apply h0
    simpa [E, lineToContra, idForm] using h3
  · intro g h Ψ Ψ' hΨ' u
    have e1 : Fm Ψ' = parInd (e2 x x') (ofChar (twoDet x x' α⁻¹ β⁻¹)) h (Fm Ψ) := by
      refine Subtype.ext (Subtype.ext (funext fun y => ?_))
      show (Fm Ψ').1.1 y = (Fm Ψ).1.1 (y * h)
      rw [hFm, hFm, hΨ']
      have e : omB (α / β)⁻¹ α⁻¹ g h (Ψ : Matrix (Fin x') (Fin (x + x')) k → ℂ) =
          omB (α / β)⁻¹ α⁻¹ 1 h (omB (α / β)⁻¹ α⁻¹ g 1 Ψ) := by rw [← omB_mul, one_mul, mul_one]
      rw [e, mapB_omB_right, mapB_omB_left' hl g Ψ.2]
    have i1 : parIndMap (e2 x x') E (Fm Ψ') = parInd (e2 x x') (contra (ofChar (twoDet x x' α β))) h
        (parIndMap (e2 x x') E (Fm Ψ)) :=
      (congrArg (parIndMap (e2 x x') E) e1).trans
        (Representation.IntertwiningMap.isIntertwining (parInd (e2 x x') (ofChar (twoDet x x' α⁻¹ β⁻¹)))
          (parInd (e2 x x') (contra (ofChar (twoDet x x' α β)))) (parIndMap (e2 x x') E) h (Fm Ψ))
    have i2 : Φ.toIntertwiningMap (parIndMap (e2 x x') E (Fm Ψ')) =
        contra (parInd (e2 x x') (ofChar (twoDet x x' α β))) h
          (Φ.toIntertwiningMap (parIndMap (e2 x x') E (Fm Ψ))) :=
      (congrArg Φ.toIntertwiningMap i1).trans
        (Representation.IntertwiningMap.isIntertwining (parInd (e2 x x') (contra (ofChar (twoDet x x' α β))))
          (contra (parInd (e2 x x') (ofChar (twoDet x x' α β)))) Φ.toIntertwiningMap h (parIndMap (e2 x x') E (Fm Ψ)))
    have hc : parInd (e2 x x') (ofChar (twoDet x x' α β)) h⁻¹ (parInd (e2 x x') (ofChar (twoDet x x' α β)) h u) = u := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    refine (hP Ψ' _).trans ((congrArg (fun w : smoothPart (parInd (e2 x x') (ofChar (twoDet x x' α β))).dual =>
      (w : Module.Dual ℂ (IndSp (e2 x x') (ofChar (twoDet x x' α β)))) (detInd x x' α β h u)) i2).trans ?_)
    refine Eq.trans ?_ (hP Ψ u).symm
    exact congrArg (fun v => (Φ.toIntertwiningMap (parIndMap (e2 x x') E (Fm Ψ)) :
      Module.Dual ℂ (IndSp (e2 x x') (ofChar (twoDet x x' α β)))) v) hc
