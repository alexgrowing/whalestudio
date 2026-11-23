import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThK.MidJac GlobalTheory.CuspBlock GlobalTheory.LocGL

namespace GlobalTheory.MidJacTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSubquotient_jac_of_twistEquiv {α : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {d : ℕ} (e : (Σ a, m a) ≃ Fin d)
    {H : Type} [Group H] (s : H →* Levi k m)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {π : Representation ℂ (GL (Fin d) k) V} {π' : Representation ℂ (GL (Fin d) k) V'}
    {χ : kˣ →* ℂˣ} (Φ : (twist π (detChar (Fin d) χ)).Equiv π') (ψ : H →* ℂˣ)
    (hψ : ∀ h, (ψ h : ℂ) = (((deltaHalf k m (s h))⁻¹ : ℂˣ) : ℂ) *
      (χ (Matrix.GeneralLinearGroup.det (leviEmb k e (s h))) : ℂ))
    {W : Type} [AddCommGroup W] [Module ℂ W] {Q : Representation ℂ H W}
    (hQ : IsSubquotient Q ((jacU e π).comp s)) :
    IsSubquotient (twist Q ψ) ((jac e π').comp s) := by
  let L := Φ.toLinearEquiv
  have hL : ∀ g w, L (twist π (detChar (Fin d) χ) g w) = π' g (L w) := fun g w =>
    Φ.toIntertwiningMap.isIntertwining _ _ g w
  have hinv : ∀ g v, L.symm (π' g v) = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • π g (L.symm v) := by
    intro g v
    apply L.injective
    rw [LinearEquiv.apply_symm_apply]
    have := hL g (L.symm v)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this, twist_apply, detChar_apply]
  let U := unipRad k e
  have hle : twKer π' U 1 ≤ (twKer π U 1).comap L.symm.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    refine Submodule.subset_span ⟨u, L.symm v, ?_⟩
    have hu : Matrix.GeneralLinearGroup.det (u : GL (Fin d) k) = 1 := det_eq_one_of_mem_unipRad k u.2
    simp [hinv, hu]
  let M : Jacquet π' U →ₗ[ℂ] Jacquet π U := (twKer π' U 1).mapQ (twKer π U 1) L.symm.toLinearMap hle
  have hM : ∀ v, M (Submodule.Quotient.mk v) = Submodule.Quotient.mk (L.symm v) := fun v => rfl
  let f : Representation.IntertwiningMap ((jac e π').comp s) (twist ((jacU e π).comp s) ψ) := ⟨M, fun h => by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show M (jac e π' (s h) (Submodule.Quotient.mk v)) = twist ((jacU e π).comp s) ψ h (M (Submodule.Quotient.mk v))
    rw [jac_mk, map_smul, hM, hM, twist_apply, hinv, hψ]
    show _ = _ • (Submodule.Quotient.mk (π (leviEmb k e (s h)) (L.symm v)) : Jacquet π U)
    rw [Submodule.Quotient.mk_smul, smul_smul]⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk (L w), by show M _ = _; rw [hM, LinearEquiv.symm_apply_apply]⟩
  exact (isSubquotient_twist hQ ψ).trans (.of_surjective f hf)

theorem isSubquotient_midJac_congr {l n d c₁ c₂ : ℕ} (hc : c₁ = c₂)
    (p₁ : ∑ i, (![l, n, c₁] : Fin 3 → ℕ) i = d) (p₂ : ∑ i, (![l, n, c₂] : Fin 3 → ℕ) i = d)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin d) k) V)
    {W : Type} [AddCommGroup W] [Module ℂ W] {Q : Representation ℂ (GL (Fin n) k) W}
    (hQ : IsSubquotient Q ((jac (finSigmaFinEquiv.trans (finCongr p₁)) π).comp (midIncl l n c₁))) :
    IsSubquotient Q ((jac (finSigmaFinEquiv.trans (finCongr p₂)) π).comp (midIncl l n c₂)) := by
  subst hc
  exact hQ

theorem modExp_mid (l n c : ℕ) : modExp (fun j : Fin 3 => Fin ((![l, n, c] : Fin 3 → ℕ) j)) 1 = (c : ℤ) - l := by
  simp [modExp, Finset.sum_filter, Fin.sum_univ_three]

theorem isSubquotient_midJac_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a a' l n : ℕ)
    (h : l + n ≤ a + a') (x : ℝ), ∃ z : ℝ, ∀ (α β : kˣ →* ℂˣ)
    (W : Type) [AddCommGroup W] [Module ℂ W] (Q : Representation ℂ (GL (Fin n) k) W),
      IsSubquotient Q ((jacU (tripPlace h) (detInd a a' α β)).comp (midHom k l n (a + a'))) →
      IsSubquotient (twist Q (detChar (Fin n) (absPow k (x : ℂ))))
        (midJac l n (a + a') h (detInd a a' (α * absPow k (z : ℂ)) (β * absPow k (z : ℂ)))) := by
  intro k _ _ _ _ a a' l n h x
  refine ⟨x + (((a + a' - (l + n) : ℕ) : ℝ) - l) / 2, ?_⟩
  intro α β W _ _ Q hQ
  have hsm : IsSmoothChar (absPow k ((x + (((a + a' - (l + n) : ℕ) : ℝ) - l) / 2 : ℝ) : ℂ)) :=
    isSmoothChar_of_isUnram (isUnram_absPow k _)
  let Φ := smIndTwistEquiv (Q := parab k (e2 a a')) (P := parab k (e2 a a'))
    (σ := (twist (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' α β)) (deltaHalf k _)).comp (leviProj k (e2 a a')))
    (τ := (twist (ofChar (GlobalTheory.ThK.DetProd.twoDet a a'
      (α * absPow k ((x + (((a + a' - (l + n) : ℕ) : ℝ) - l) / 2 : ℝ) : ℂ))
      (β * absPow k ((x + (((a + a' - (l + n) : ℕ) : ℝ) - l) / 2 : ℝ) : ℂ)))) (deltaHalf k _)).comp
        (leviProj k (e2 a a')))
    le_rfl le_rfl hsm.detChar (.refl ℂ ℂ) fun q v => by
      have hd := det_parab k (e2 a a') q
      rw [Fin.prod_univ_two] at hd
      simp only [twist_apply, ofChar_apply, MonoidHom.comp_apply, GlobalTheory.ThK.DetProd.twoDet, MonoidHom.mul_apply,
        detChar_apply, Pi.evalMonoidHom_apply, hd, map_mul, Units.val_mul, smul_eq_mul, LinearEquiv.refl_apply,
        Subtype.coe_eta]
      ring
  have hme : modExp (fun j : Fin 3 => Fin (tripSizes l n (a + a') j)) 1 = ((a + a' - (l + n) : ℕ) : ℤ) - l :=
    modExp_mid l n _
  have hchar : absPow k (x : ℂ) =
      (absPow k (((modExp (fun j : Fin 3 => Fin (tripSizes l n (a + a') j)) 1 : ℤ) : ℂ) / 2))⁻¹ *
      absPow k ((x + (((a + a' - (l + n) : ℕ) : ℝ) - l) / 2 : ℝ) : ℂ) := by
    rw [← absPow_neg, ← absPow_add, hme]
    congr 1
    push_cast
    ring
  have h1 := isSubquotient_jac_of_twistEquiv (tripPlace h) (midHom k l n (a + a')) Φ
    (detChar (Fin n) (absPow k (x : ℂ))) (fun g => by
      have hs0 : (midHom k l n (a + a') g) 0 = 1 := by
        show Pi.mulSingle (M := fun j : Fin 3 => GL (Fin (tripSizes l n (a + a') j)) k) 1 g 0 = 1
        exact Pi.mulSingle_eq_of_ne (by decide) _
      have hs1 : (midHom k l n (a + a') g) 1 = g := by
        show Pi.mulSingle (M := fun j : Fin 3 => GL (Fin (tripSizes l n (a + a') j)) k) 1 g 1 = g
        exact Pi.mulSingle_eq_same _ _
      have hs2 : (midHom k l n (a + a') g) 2 = 1 := by
        show Pi.mulSingle (M := fun j : Fin 3 => GL (Fin (tripSizes l n (a + a') j)) k) 1 g 2 = 1
        exact Pi.mulSingle_eq_of_ne (by decide) _
      have hdet : Matrix.GeneralLinearGroup.det (leviEmb k (tripPlace h) (midHom k l n (a + a') g)) =
          Matrix.GeneralLinearGroup.det g := by
        rw [det_leviEmb, Fin.prod_univ_three, hs0, hs1, hs2]
        simp only [map_one, one_mul, mul_one]
        try rfl
      have hdel : deltaHalf k _ (midHom k l n (a + a') g) =
          absPow k (((modExp (fun j : Fin 3 => Fin (tripSizes l n (a + a') j)) 1 : ℤ) : ℂ) / 2)
            (Matrix.GeneralLinearGroup.det g) := by
        rw [deltaHalf_apply, Fin.prod_univ_three, hs0, hs1, hs2]
        simp only [map_one, one_mul, mul_one]
        try rfl
      rw [hdet, hdel, detChar_apply, hchar, MonoidHom.mul_apply, Units.val_mul, MonoidHom.inv_apply])
    hQ
  exact isSubquotient_midJac_congr (Nat.sub_sub _ _ _).symm _ _ _ h1

end GlobalTheory.MidJacTwist
