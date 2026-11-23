import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralProd2
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalPairIrreducibleProduct

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open scoped TensorProduct
open GlobalTheory.CompanionTheory.BZSegComm
open Zc.Cos (invT)

namespace PositivityTheory.RgUd.Exp.Comm

section Lemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem isIrreducible_comp_invT {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (h : π.IsIrreducible) :
    Representation.IsIrreducible (π.comp (invT : GL (Fin N) k →* GL (Fin N) k)) := by
  have e : (π.comp (invT : GL (Fin N) k →* GL (Fin N) k)).comp (invT : GL (Fin N) k →* GL (Fin N) k) = π :=
    MonoidHom.ext fun g => congrArg (⇑π) (invT_invT g)
  exact GlobalTheory.SwapTwo.isIrreducible_of_comp (invT : GL (Fin N) k →* GL (Fin N) k) (by rw [e]; exact h)

theorem isIrreducible_of_contra_swap {r t N : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W)
    (hAa : IsAdmissible A) (hAi : A.IsIrreducible) (hBa : IsAdmissible B) (hBi : B.IsIrreducible)
    (h : r + t = N) (h' : t + r = N)
    (ρX : Representation ℂ (GL (Fin N) k) X) (ρY : Representation ℂ (GL (Fin N) k) Y)
    (eX : ρX.Equiv (ind₂ (stdSum h) (extTensor A B)))
    (eY : (ind₂ (stdSum h') (extTensor (contra B) (contra A))).Equiv ρY)
    (hX : ρX.IsIrreducible) : ρY.IsIrreducible := by
  obtain ⟨κ⟩ := ind₂_swap_equiv_comp_invT (k := k) (stdSum h) (stdSum h') (extTensor A B)
  obtain ⟨τ⟩ := nonempty_extTensor_swap A B
  obtain ⟨ga⟩ := nonempty_comp_invT_equiv_contra A hAa hAi
  obtain ⟨gb⟩ := nonempty_comp_invT_equiv_contra B hBa hBi
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv
    (((compEquiv eX _).trans κ.symm).trans ((ind₂Equiv _ (τ.trans (extTensorCongr gb ga))).trans eY))
    (isIrreducible_comp_invT _ hX)

theorem prodIrr_swap_isIrreducible (F G : Fin 2 → IrrGL k) (e₀ : G 0 = F 1) (e₁ : G 1 = F 0) {N : ℕ}
    (hd : ∑ a, (F a).1 = N) (hd' : ∑ a, (G a).1 = N) (hX : (prodIrr F hd).IsIrreducible) :
    (prodIrr G hd').IsIrreducible := by
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have h : (F 0).1 + (F 1).1 = N := (Fin.sum_univ_two _).symm.trans hd
  have h' : (G 0).1 + (G 1).1 = N := (Fin.sum_univ_two _).symm.trans hd'
  have h'' : (F 1).1 + (F 0).1 = N := by rw [← e₀, ← e₁]; exact h'
  have aX := hA k N _ _ (isSmooth_prodIrr _ hd) hX
  have a0 := hA k _ _ (F 0).rep (F 0).2.rep.smooth (F 0).2.rep.irr
  have a1 := hA k _ _ (F 1).rep (F 1).2.rep.smooth (F 1).2.rep.irr
  have R0 := GlobalTheory.ContraRefl.contra_irreducible_reflexive (GL (Fin (F 0).1) k)
    (GlobalTheory.LocalThetaGL.compact_open_basis _) _ _ _ _ a0 a0
  have R1 := GlobalTheory.ContraRefl.contra_irreducible_reflexive (GL (Fin (F 1).1) k)
    (GlobalTheory.LocalThetaGL.compact_open_basis _) _ _ _ _ a1 a1
  have RX := GlobalTheory.ContraRefl.contra_irreducible_reflexive (GL (Fin N) k) (GlobalTheory.LocalThetaGL.compact_open_basis _)
    _ _ _ _ aX aX
  have c0i := R0.1 (F 0).2.rep.irr
  have c1i := R1.1 (F 1).2.rep.irr
  have c0a := hA k _ _ (contra (F 0).rep) (isSmooth_contra _) c0i
  have c1a := hA k _ _ (contra (F 1).rep) (isSmooth_contra _) c1i
  obtain ⟨ε⟩ := nonempty_ind₂_contra_equiv hA F hd h
  have e0 := R0.2.1.some
  have e1 := R1.2.1.some
  obtain ⟨m⟩ := nonempty_ind₂_equiv_multiProd (k := k) (d := fun a => (G a).1) hd' h' fun a => (G a).rep
  have E₃ : ∀ (u v : IrrGL k), u = F 1 → v = F 0 → ∀ h₁ : u.1 + v.1 = N,
      Nonempty ((ind₂ (stdSum h'') (extTensor (F 1).rep (F 0).rep)).Equiv
        (ind₂ (stdSum h₁) (extTensor u.rep v.rep))) := by
    rintro _ _ rfl rfl _
    exact ⟨.refl _⟩
  have e₄ := (E₃ _ _ e₀ e₁ h').some
  exact isIrreducible_of_contra_swap (contra (F 0).rep) (contra (F 1).rep) c0a c0i c1a c1i h h''
    (contra (prodIrr F hd)) (prodIrr G hd') ε.symm
    (((ind₂Equiv _ (extTensorCongr e1.symm e0.symm)).trans e₄).trans m) (RX.1 hX)

end Lemmas

theorem comm2Irr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.Exp.Comm2Irr k := by
  intro x y N hd hd' hX
  exact prodIrr_swap_isIrreducible ![x, y] ![y, x] rfl rfl hd hd' hX

end PositivityTheory.RgUd.Exp.Comm

end
