import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnlinkedCommuteOfIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestDerivativeOfProduct
import BuildAid.D3

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.BZSegComm GlobalTheory.CompanionTheory.BZShell

namespace GlobalTheory.CompanionTheory.BZShell.SwapPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem contra_ind₂_swap {r t N : ℕ} (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W)
    (hs₁ : IsSmooth π₁) (hi₁ : π₁.IsIrreducible) (hs₂ : IsSmooth π₂) (hi₂ : π₂.IsIrreducible)
    (h : r + t = N) (h' : t + r = N) (hX : (ind₂ (stdSum h) (extTensor π₁ π₂)).IsIrreducible) :
    Nonempty ((contra (ind₂ (stdSum h) (extTensor π₁ π₂))).Equiv
      (ind₂ (stdSum h') (extTensor (contra π₂) (contra π₁)))) := by
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  have Gx := nonempty_comp_invT_equiv_contra π₁ (hA k _ _ _ hs₁ hi₁) hi₁
  have Gy := nonempty_comp_invT_equiv_contra π₂ (hA k _ _ _ hs₂ hi₂) hi₂
  have T := nonempty_extTensor_swap π₁ π₂
  have K := ind₂_swap_equiv_comp_invT (k := k) (stdSum h) (stdSum h') (extTensor π₁ π₂)
  have GX := nonempty_comp_invT_equiv_contra (ind₂ (stdSum h) (extTensor π₁ π₂))
    (hA k N _ _ (isSmooth_parInd _ _) hX) hX
  exact Gx.elim fun gx => Gy.elim fun gy => T.elim fun τ => K.elim fun κ => GX.elim fun gX =>
    ⟨gX.symm.trans (κ.symm.trans (ind₂Equiv _ (τ.trans (extTensorCongr gy gx))))⟩

theorem ind₂_contra_fam (F : Fin 2 → IrrGL k) {N : ℕ} (h : (F 0).1 + (F 1).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra (F 0).rep) (contra (F 1).rep))).Equiv
      (contra (ind₂ (stdSum h) (extTensor (F 0).rep (F 1).rep)))) := by
  have hd : ∑ a, (F a).1 = N := (Fin.sum_univ_two _).trans h
  have E₂ := nonempty_ind₂_contra_equiv GlobalTheory.CompanionTheory.BZCuspPair.irrAdm F hd h
  have E₁ := nonempty_ind₂_equiv_multiProd (d := fun a => (F a).1) hd h fun a => (F a).rep
  refine E₂.elim fun ε₂ => E₁.elim fun ε₁ => ?_
  have ε₃ : (ind₂ (stdSum h) (extTensor (F 0).rep (F 1).rep)).Equiv (prodIrr F hd) := ε₁
  have ε₄ : (contra (prodIrr F hd)).Equiv (contra (ind₂ (stdSum h) (extTensor (F 0).rep (F 1).rep))) :=
    GlobalTheory.ContraRefl.contraEquiv ε₃
  exact ⟨ε₂.trans ε₄⟩

theorem induced_two_contragredient_equiv (F : Fin 2 → IrrGL k) (x y : IrrGL k) (h₀ : F 0 = x) (h₁ : F 1 = y) {N : ℕ}
    (h : x.1 + y.1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra x.rep) (contra y.rep))).Equiv
      (contra (ind₂ (stdSum h) (extTensor x.rep y.rep)))) := by
  subst h₀ h₁
  exact ind₂_contra_fam F h

theorem ind₂_contra_rep (x y : IrrGL k) {N : ℕ} (h : x.1 + y.1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra x.rep) (contra y.rep))).Equiv
      (contra (ind₂ (stdSum h) (extTensor x.rep y.rep)))) :=
  induced_two_contragredient_equiv ![x, y] x y rfl rfl h

theorem ind₂_contra_of_equiv (x y : IrrGL k) {N : ℕ} (h : x.1 + y.1 = N)
    (π₁ : Representation ℂ (GL (Fin x.1) k) V) (π₂ : Representation ℂ (GL (Fin y.1) k) W)
    (φ₁ : π₁.Equiv x.rep) (φ₂ : π₂.Equiv y.rep) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra π₁) (contra π₂))).Equiv
      (contra (ind₂ (stdSum h) (extTensor π₁ π₂)))) :=
  (ind₂_contra_rep x y h).elim fun ε =>
    ⟨(ind₂Equiv _ (extTensorCongr (GlobalTheory.ContraRefl.contraEquiv φ₁.symm) (GlobalTheory.ContraRefl.contraEquiv φ₂.symm))).trans
      (ε.trans (GlobalTheory.ContraRefl.contraEquiv (ind₂Equiv _ (extTensorCongr φ₁ φ₂))))⟩

theorem ind₂_contra_equiv {r t N : ℕ} (π₁ : Representation ℂ (GL (Fin r) k) V)
    (π₂ : Representation ℂ (GL (Fin t) k) W)
    (hs₁ : IsSmooth π₁) (hi₁ : π₁.IsIrreducible) (hs₂ : IsSmooth π₂) (hi₂ : π₂.IsIrreducible) (h : r + t = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor (contra π₁) (contra π₂))).Equiv
      (contra (ind₂ (stdSum h) (extTensor π₁ π₂)))) :=
  ind₂_contra_of_equiv (IrrGL.of π₁ hs₁ hi₁) (IrrGL.of π₂ hs₂ hi₂) h π₁ π₂
    (IrrGL.equivOf π₁ hs₁ hi₁) (IrrGL.equivOf π₂ hs₂ hi₂)

theorem exists_form_of_equiv_contra {N : ℕ} (A : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth A)
    (C : Representation ℂ (GL (Fin N) k) W) (E : C.Equiv (contra A)) :
    ∃ B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ, (∀ g v v', B (A g v) (C g v') = B v v') ∧ ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := by
  let B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ := LinearMap.flip ((smoothPart A.dual).subtype ∘ₗ E.toLinearEquiv.toLinearMap)
  have hB : ∀ v v', B v v' = ((E.toLinearEquiv v' : smoothPart A.dual) : Module.Dual ℂ V) v := fun _ _ => rfl
  refine ⟨B, fun g v v' => ?_, fun v hv => ?_⟩
  · have hE : E.toLinearEquiv (C g v') = contra A g (E.toLinearEquiv v') :=
      E.toIntertwiningMap.isIntertwining _ _ g v'
    rw [hB, hB, hE, contra_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hs (GlobalTheory.SqIntUnit.compactOpen_basis k N) hv
    refine ⟨E.toLinearEquiv.symm l, ?_⟩
    rw [hB, LinearEquiv.apply_symm_apply]
    exact hl

theorem isIrreducible_ind₂_segTerm {a N : ℕ} (π : Representation ℂ (GL (Fin a) k) V) (hN : 2 * a = N) (h : a + a = N)
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 a) (segTerm π 2)).IsIrreducible) :
    (ind₂ (stdSum h) (extTensor (segTerm π 2 0) (segTerm π 2 1))).IsIrreducible := by
  subst hN
  have hd : ∑ _ : Fin 2, a = 2 * a := by simp
  obtain ⟨E⟩ := nonempty_ind₂_equiv_multiProd (d := fun _ : Fin 2 => a) hd h (X := fun _ => V) (segTerm π 2)
  obtain ⟨ψ⟩ := (Placing.parInd_jac_placing k (Fin 2) (Fin (2 * a)) (fun _ => Fin a)
    (stdBlocks (fun _ : Fin 2 => a) hd) (GlobalTheory.Published.consecBlocks 2 a) _).1 (piTensor (segTerm π 2))
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv (E.trans ψ).symm hirr

theorem segTerm_zero {a : ℕ} (π : Representation ℂ (GL (Fin a) k) V) : segTerm π 2 0 = π := by
  have h : detChar (Fin a) (absPow k (((0 : Fin 2) : ℕ) : ℂ)) = 1 := by
    ext g
    simp
  rw [segTerm, h, twist_one]

theorem segTerm_one {a : ℕ} (π : Representation ℂ (GL (Fin a) k) V) : segTerm π 2 1 = twist π (dpow a 1) := by
  simp [segTerm, dpow]

theorem product_two_contragredient_equiv {a : ℕ} (σ : IrrRep (GL (Fin a) k))
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 a) (segTerm σ.ρ 2)).IsIrreducible) :
    Nonempty ((prod2 (k := k) rfl (contra σ.ρ) (twist (contra σ.ρ) (dpow a (-1)))).Equiv
      (contra (prod2 (k := k) rfl (twist σ.ρ (dpow a 1)) σ.ρ))) := by
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  have hs := σ.smooth
  have hi := σ.irr
  have hs₁ : IsSmooth (twist σ.ρ (dpow (k := k) a 1)) := isSmooth_twist hs (isSmoothChar_absPow _).detChar
  have hi₁ : (twist σ.ρ (dpow (k := k) a 1)).IsIrreducible := isIrreducible_twist hi _
  have hX : (ind₂ (stdSum (rfl : a + a = a + a)) (extTensor σ.ρ (twist σ.ρ (dpow (k := k) a 1)))).IsIrreducible := by
    have h := isIrreducible_ind₂_segTerm σ.ρ (by omega : 2 * a = a + a) rfl hirr
    rwa [segTerm_zero, segTerm_one] at h
  have S := contra_ind₂_swap σ.ρ (twist σ.ρ (dpow (k := k) a 1)) hs hi hs₁ hi₁ rfl rfl hX
  have B₁ := ind₂_contra_equiv σ.ρ (twist σ.ρ (dpow (k := k) a 1)) hs hi hs₁ hi₁ rfl
  have B₂ := ind₂_contra_equiv (twist σ.ρ (dpow (k := k) a 1)) σ.ρ hs₁ hi₁ hs hi rfl
  have Tw : Nonempty ((twist (contra σ.ρ) (dpow (k := k) a (-1))).Equiv (contra (twist σ.ρ (dpow (k := k) a 1)))) :=
    GlobalTheory.CompanionTheory.ZcDual.nonempty_equiv_contra_twist hA σ.ρ hs hi (isSmoothChar_absPow _) (isSmoothChar_absPow _)
      (by rw [Complex.ofReal_neg, absPow_neg, mul_inv_cancel])
  have P₁ := GlobalTheory.CompanionTheory.HighestDeriv.nonempty_prod2_equiv (k := k) (contra σ.ρ) (twist (contra σ.ρ) (dpow (k := k) a (-1)))
  have P₂ := GlobalTheory.CompanionTheory.HighestDeriv.nonempty_prod2_equiv (k := k) (twist σ.ρ (dpow (k := k) a 1)) σ.ρ
  refine S.elim fun s => B₁.elim fun b₁ => B₂.elim fun b₂ => Tw.elim fun τ => P₁.elim fun p₁ => P₂.elim fun p₂ => ?_
  have c₁ : (prod2 (k := k) rfl (contra σ.ρ) (twist (contra σ.ρ) (dpow a (-1)))).Equiv
      (ind₂ (stdSum (rfl : a + a = a + a)) (extTensor (contra σ.ρ) (contra (twist σ.ρ (dpow (k := k) a 1))))) :=
    p₁.trans (ind₂Equiv _ (extTensorCongr (.refl _) τ))
  have c₂ : (contra (ind₂ (stdSum (rfl : a + a = a + a)) (extTensor (twist σ.ρ (dpow (k := k) a 1)) σ.ρ))).Equiv
      (contra (prod2 (k := k) rfl (twist σ.ρ (dpow a 1)) σ.ρ)) :=
    GlobalTheory.ContraRefl.contraEquiv p₂
  exact ⟨c₁.trans (b₁.trans (s.trans (b₂.trans c₂)))⟩

theorem exists_pairing_cast (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k))
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 (m + 1)) (segTerm σ.ρ 2)).IsIrreducible) {N : ℕ}
    (h : (m + 1) + (m + 1) = N) :
    ∃ B : ((((gOf σ).tw 1).prod (gOf σ)).cast h).V →ₗ[ℂ]
        (((gDual σ).prod ((gDual σ).tw (-1))).cast h).V →ₗ[ℂ] ℂ,
      (∀ g v v', B ((((gOf σ).tw 1).prod (gOf σ)).cast h |>.ρ g v)
        (((gDual σ).prod ((gDual σ).tw (-1))).cast h |>.ρ g v') = B v v') ∧
      ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := by
  subst h
  exact (product_two_contragredient_equiv σ hirr).elim fun E =>
    exists_form_of_equiv_contra (prod2 (k := k) rfl (twist σ.ρ (dpow (m + 1) 1)) σ.ρ) (isSmooth_parInd _ _) _ E

theorem exists_invariant_pairing : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ)
    (hirr : (multiProd (GlobalTheory.Published.consecBlocks 2 (m + 1)) (segTerm σ.ρ 2)).IsIrreducible),
    ∃ B : ((((gOf σ).tw 1).prod (gOf σ)).cast (size_eq m)).V →ₗ[ℂ]
        (((gDual σ).prod ((gDual σ).tw (-1))).cast (size_eq m)).V →ₗ[ℂ] ℂ,
      (∀ g v v', B ((((gOf σ).tw 1).prod (gOf σ)).cast (size_eq m) |>.ρ g v)
        (((gDual σ).prod ((gDual σ).tw (-1))).cast (size_eq m) |>.ρ g v') = B v v') ∧
      ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 :=
  fun m σ _ hirr => exists_pairing_cast m σ hirr (size_eq m)

end GlobalTheory.CompanionTheory.BZShell.SwapPair

end
