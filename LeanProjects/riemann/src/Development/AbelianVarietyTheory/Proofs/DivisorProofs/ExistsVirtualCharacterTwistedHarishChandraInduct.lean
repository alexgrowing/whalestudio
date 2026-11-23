import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjectionStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section
namespace GlobalTheory.Shin.HatInd

theorem inPar_gal {F' : Type} [Field F'] (u : F' →+* F') (a : ℕ) {n : ℕ} (x : GL (Fin n) F') :
    InPar a (gal u n x) ↔ InPar a x := by
  unfold InPar gal
  simp only [Matrix.GeneralLinearGroup.map_apply, map_eq_zero]

theorem par_facts {F' : Type} [Field F'] (a b n : ℕ) (h : n = a + b) :
    (∀ x y : GL (Fin n) F', InPar a x → InPar a y → InPar a (x * y)) ∧ InPar a (1 : GL (Fin n) F') ∧
    (∀ x : GL (Fin n) F', InPar a x → InPar a x⁻¹) ∧
    (∀ x y : GL (Fin n) F', InPar a x → InPar a y → tlG a (x * y) = tlG a x * tlG a y) ∧
    (∀ x : GL (Fin n) F', InPar a x →
      ((tlG a x : GL (Fin a) F') : Matrix (Fin a) (Fin a) F') = tl a (x : Matrix (Fin n) (Fin n) F')) := by
  obtain ⟨H, π, hH, -, hπ, hmat, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F' a b n h
  refine ⟨fun x y hx hy => (hH _).1 (H.mul_mem ((hH x).2 hx) ((hH y).2 hy)), (hH 1).1 H.one_mem,
    fun x hx => (hH _).1 (H.inv_mem ((hH x).2 hx)), fun x y hx hy => ?_, fun x hx => ?_⟩
  · have := π.map_mul ⟨x, (hH x).2 hx⟩ ⟨y, (hH y).2 hy⟩
    rw [hπ, hπ, hπ] at this
    exact congrArg Prod.fst this
  · have := (hmat ⟨x, (hH x).2 hx⟩).1
    rw [hπ] at this
    exact this

theorem tlG_gal {F' : Type} [Field F'] (u : F' →+* F') (a b n : ℕ) (h : n = a + b) (x : GL (Fin n) F')
    (hx : InPar a x) : tlG a (gal u n x) = gal u a (tlG a x) := by
  have hm := (par_facts (F' := F') a b n h).2.2.2.2
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [hm _ ((inPar_gal u a x).2 hx)]
  unfold gal
  rw [Matrix.GeneralLinearGroup.map_apply, hm _ hx]
  unfold tl ent
  split_ifs <;> simp [Matrix.GeneralLinearGroup.map_apply]

theorem finite_gal (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] :
    Finite (F' ≃ₐ[F] F') :=
  Finite.of_injective (fun e : F' ≃ₐ[F] F' => (e : F' → F')) (fun _ _ h => AlgEquiv.ext (congrFun h))

theorem galAct_symm {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (u : F' ≃ₐ[F] F')
    (x : GL (Fin n) F') : (galAct F F' n u).symm x = gal ((u⁻¹ : F' ≃ₐ[F] F') : F' →+* F') n x := rfl

theorem hat_ind : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (a b n : ℕ), n = a + b →
    ∀ X ∈ Virt ℂ ℂ (GHat F F' a), ∃ Z ∈ Virt ℂ ℂ (GHat F F' n), ∀ (t : F' ≃ₐ[F] F') (δ : GL (Fin n) F'),
      Z (inl δ * inr t) = hcTw (t : F' →+* F') a b (fun d => X (inl d * inr t)) (fun _ => 1) n δ := by
  intro F F' _ _ _ _ a b n hn X hX
  haveI : Finite (F' ≃ₐ[F] F') := finite_gal F F'
  haveI : Finite (GHat F F' n) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  haveI : Finite (GHat F F' a) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  obtain ⟨hmul, hone, hinv, htl, -⟩ := par_facts (F' := F') a b n hn
  let P : Subgroup (GHat F F' n) :=
    { carrier := {x | InPar a x.left}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, mul_left, galAct_apply] at hx hy ⊢
        exact hmul _ _ hx ((inPar_gal _ a _).2 hy)
      one_mem' := by simpa using hone
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq, inv_left, galAct_apply] at hx ⊢
        exact (inPar_gal _ a _).2 (hinv _ hx) }
  have hP : ∀ x : GHat F F' n, x ∈ P ↔ InPar a x.left := fun _ => Iff.rfl
  let πh : P →* GHat F F' a := MonoidHom.mk' (fun p => (⟨tlG a p.1.left, p.1.right⟩ : GHat F F' a))
    (fun p q => by
      have hp := (hP _).1 p.2
      have hq := (hP _).1 q.2
      apply SemidirectProduct.ext
      · simp only [Subgroup.coe_mul, mul_left, galAct_apply]
        rw [htl _ _ hp ((inPar_gal _ a _).2 hq), tlG_gal _ a b n hn _ hq]
      · simp)
  have hcl := (virt_mul_comap_conj_ind_linear (GHat F F' a)).2.2.1 X hX
  set ψ : P → ℂ := fun p => X (πh p) with hψ
  refine ⟨ind P ψ, (virt_mul_comap_conj_ind_linear (GHat F F' n)).2.2.2.1 P ψ
    ((virt_mul_comap_conj_ind_linear (GHat F F' a)).2.1 X hX P πh), fun t δ => ?_⟩

  have key : ∀ (w : GHat F F' n) (u : F' ≃ₐ[F] F'), ext0 P ψ ((inr u)⁻¹ * w * inr u) = ext0 P ψ w := by
    intro w u
    have hl : ((inr u)⁻¹ * w * inr u).left = gal ((u⁻¹ : F' ≃ₐ[F] F') : F' →+* F') n w.left := by
      simp [mul_left, galAct_apply, galAct_symm]
    have hr : ((inr u)⁻¹ * w * inr u).right = u⁻¹ * w.right * u := by simp
    unfold ext0
    by_cases hw : InPar a w.left
    · have hw' : (inr u)⁻¹ * w * inr u ∈ P := by rw [hP, hl]; exact (inPar_gal _ a _).2 hw
      rw [dif_pos hw', dif_pos ((hP w).2 hw)]
      simp only [hψ]
      have : πh ⟨(inr u)⁻¹ * w * inr u, hw'⟩ = (inr u)⁻¹ * πh ⟨w, (hP w).2 hw⟩ * inr u := by
        apply SemidirectProduct.ext
        · change tlG a ((inr u)⁻¹ * w * inr u).left = _
          rw [hl, tlG_gal _ a b n hn _ hw]
          simp [MonoidHom.mk'_apply, mul_left, galAct_apply, galAct_symm, πh]
        · change ((inr u)⁻¹ * w * inr u).right = _
          rw [hr]
          simp [MonoidHom.mk'_apply, πh]
      rw [this]
      have := hcl (πh ⟨w, (hP w).2 hw⟩) (inr u)
      simpa using this
    · have hw' : (inr u)⁻¹ * w * inr u ∉ P := by
        rw [hP, hl]; exact fun h => hw ((inPar_gal _ a _).1 h)
      rw [dif_neg hw', dif_neg (fun h => hw ((hP w).1 h))]
  haveI : Fintype (GHat F F' n) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin n) F') := Fintype.ofFinite _
  haveI : Fintype (F' ≃ₐ[F] F') := Fintype.ofFinite _
  set g : GHat F F' n := inl δ * inr t with hg
  have hval : ∀ y : GL (Fin n) F', ext0 P ψ ((inl y)⁻¹ * g * inl y) =
      if InPar a (y⁻¹ * δ * gal (t : F' →+* F') n y) then
        X (inl (tlG a (y⁻¹ * δ * gal (t : F' →+* F') n y)) * inr t) * 1 else 0 := by
    intro y
    have hl : ((inl y)⁻¹ * g * inl y).left = y⁻¹ * δ * gal (t : F' →+* F') n y := by
      simp [hg, mul_left, galAct_apply]
    have hr : ((inl y)⁻¹ * g * inl y).right = t := by simp [hg]
    unfold ext0
    by_cases hw : InPar a (y⁻¹ * δ * gal (t : F' →+* F') n y)
    · rw [dif_pos (by rw [hP, hl]; exact hw), if_pos hw, mul_one]
      simp only [hψ]
      congr 1
      apply SemidirectProduct.ext
      · change tlG a ((inl y)⁻¹ * g * inl y).left = _
        rw [hl]; simp
      · change ((inl y)⁻¹ * g * inl y).right = _
        rw [hr]; simp
    · rw [dif_neg (by rw [hP, hl]; exact hw), if_neg hw]
  have hz : ∀ (y : GL (Fin n) F') (u : F' ≃ₐ[F] F'),
      ((SemidirectProduct.equivProd (φ := galAct F F' n)).symm (y, u)) = inl y * inr u := by
    intro y u
    apply SemidirectProduct.ext <;> simp [SemidirectProduct.equivProd]
  have hsum : ∑ᶠ z : GHat F F' n, ext0 P ψ (z⁻¹ * g * z) =
      (Nat.card (F' ≃ₐ[F] F') : ℂ) * ∑ᶠ y : GL (Fin n) F', ext0 P ψ ((inl y)⁻¹ * g * inl y) := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← (SemidirectProduct.equivProd (φ := galAct F F' n)).symm.sum_comp, Fintype.sum_prod_type,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : ∀ u : F' ≃ₐ[F] F', ext0 P ψ ((inl y * inr u)⁻¹ * g * (inl y * inr u)) =
        ext0 P ψ ((inl y)⁻¹ * g * inl y) := by
      intro u
      have e : (inl y * inr u)⁻¹ * g * (inl y * inr u) = (inr u)⁻¹ * ((inl y)⁻¹ * g * inl y) * inr u := by
        simp only [mul_inv_rev, mul_assoc]
      rw [e, key]
    simp only [hz, this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hcard : Nat.card P = Nat.card {p : GL (Fin n) F' // InPar a p} * Nat.card (F' ≃ₐ[F] F') := by
    rw [← Nat.card_prod]
    exact Nat.card_congr
      { toFun := fun p => (⟨p.1.left, p.2⟩, p.1.right)
        invFun := fun q => ⟨⟨q.1.1, q.2⟩, q.1.2⟩
        left_inv := fun p => rfl
        right_inv := fun q => rfl }
  have hB : (Nat.card (F' ≃ₐ[F] F') : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := F' ≃ₐ[F] F')).ne'
  unfold ind hcTw
  rw [hcard, hsum]
  simp only [hval]
  push_cast
  rw [mul_inv, mul_assoc, ← mul_assoc _ (Nat.card (F' ≃ₐ[F] F') : ℂ), inv_mul_cancel₀ hB, one_mul]

end GlobalTheory.Shin.HatInd
