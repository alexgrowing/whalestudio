import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ProdReorder
section SlopeTestRemainingChoices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem multiProd_single_equiv {dτ : Fin 1 → ℕ} (τ : ∀ a, Irr k (dτ a)) (e : (Σ a, Fin (dτ a)) ≃ Fin (dτ 0)) :
    Nonempty ((multiProd e fun a => (τ a).π).Equiv (τ 0).π) := by
  have A := multiProd_head (k := k) (fun a => (τ a).π) e (by simp : dτ 0 + 0 = dτ 0)
          (Equiv.equivOfIsEmpty (Σ a : Fin 0, Fin (dτ a.succ)) (Fin 0))
  have B := ind₂_unit_right (k := k) (by simp : dτ 0 + 0 = dτ 0) (τ 0).π (τ 0).smooth (fun a : Fin 0 => (τ a.succ).π) (Equiv.equivOfIsEmpty (Σ a : Fin 0, Fin (dτ a.succ)) (Fin 0))
  exact A.elim fun a => B.elim fun b => ⟨a.trans b⟩

theorem commutes_multiProd_single {p : ℕ} (x : Irr k p) {dτ : Fin 1 → ℕ} (τ : ∀ a, Irr k (dτ a)) (hc : Commutes x (τ 0)) (N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin (dτ 0)) (h₁ : p + dτ 0 = N) (h₂ : dτ 0 + p = N) : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  have M := multiProd_single_equiv τ e
  have s1 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₁) (extTensor x.π (τ 0).π))) := ind₂_congr h₁ (eqv_refl _) M
  have s2 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (τ 0).π)).Equiv (ind₂ (stdSum h₂) (extTensor (τ 0).π x.π))) := hc N h₁ h₂
  have s3 : Nonempty ((ind₂ (stdSum h₂) (extTensor (τ 0).π x.π)).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := ind₂_congr h₂ (eqv_symm M) (eqv_refl _)
  exact s1.elim fun a => s2.elim fun b => s3.elim fun c => ⟨(a.trans b).trans c⟩

theorem commutes_ind₂_of_head {p d T' T N : ℕ} (x : Irr k p) (y : Irr k d) {W : Type} [AddCommGroup W] [Module ℂ W]
    (R : Representation ℂ (GL (Fin T') k) W) (sR : IsSmooth R) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (P : Representation ℂ (GL (Fin T) k) Y) (h : d + T' = T) (H : Nonempty (P.Equiv (ind₂ (stdSum h) (extTensor y.π R))))
    (hc : Commutes x y)
    (IH : ∀ M (g₁ : p + T' = M) (g₂ : T' + p = M),
      Nonempty ((ind₂ (stdSum g₁) (extTensor x.π R)).Equiv (ind₂ (stdSum g₂) (extTensor R x.π))))
    (h₁ : p + T = N) (h₂ : T + p = N) :
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.π P)).Equiv (ind₂ (stdSum h₂) (extTensor P x.π))) := by
  have hA2 : (p + d) + T' = N := by omega
  have hB1 : d + p = p + d := Nat.add_comm _ _
  have h₄ : d + (p + T') = N := by omega
  have hD : T' + p = p + T' := Nat.add_comm _ _
  have s1 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π P)).Equiv
      (ind₂ (stdSum h₁) (extTensor x.π (ind₂ (stdSum h) (extTensor y.π R))))) :=
    ind₂_congr h₁ (eqv_refl x.π) H
  have s2 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (ind₂ (stdSum h) (extTensor y.π R)))).Equiv
      (ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum (rfl : p + d = p + d)) (extTensor x.π y.π)) R))) :=
    (ind₂_assoc' (k := k) rfl hA2 h h₁ x.π y.π R x.smooth y.smooth sR).elim fun a => ⟨a.symm⟩
  have s3 : Nonempty ((ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum (rfl : p + d = p + d)) (extTensor x.π y.π)) R)).Equiv
      (ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum hB1) (extTensor y.π x.π)) R))) :=
    ind₂_congr hA2 (hc (p + d) rfl hB1) (eqv_refl R)
  have s4 : Nonempty ((ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum hB1) (extTensor y.π x.π)) R)).Equiv
      (ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum (rfl : p + T' = p + T')) (extTensor x.π R))))) :=
    ind₂_assoc' (k := k) hB1 hA2 rfl h₄ y.π x.π R y.smooth x.smooth sR
  have s5 : Nonempty ((ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum (rfl : p + T' = p + T')) (extTensor x.π R)))).Equiv
      (ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum hD) (extTensor R x.π))))) :=
    ind₂_congr h₄ (eqv_refl y.π) (IH _ rfl hD)
  have s6 : Nonempty ((ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum hD) (extTensor R x.π)))).Equiv
      (ind₂ (stdSum h₂) (extTensor (ind₂ (stdSum h) (extTensor y.π R)) x.π))) :=
    (ind₂_assoc' (k := k) h h₂ hD h₄ y.π R x.π y.smooth sR x.smooth).elim fun a => ⟨a.symm⟩
  have s7 : Nonempty ((ind₂ (stdSum h₂) (extTensor (ind₂ (stdSum h) (extTensor y.π R)) x.π)).Equiv
      (ind₂ (stdSum h₂) (extTensor P x.π))) :=
    ind₂_congr h₂ (H.elim fun a => ⟨a.symm⟩) (eqv_refl x.π)
  exact s1.elim fun a1 => s2.elim fun a2 => s3.elim fun a3 => s4.elim fun a4 => s5.elim fun a5 =>
    s6.elim fun a6 => s7.elim fun a7 => ⟨a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7)))))⟩

end SlopeTestRemainingChoices

section Succ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem commutes_multiProd_succ {p s : ℕ} (x : Irr k p)
    (ih : ∀ (dτ : Fin s → ℕ) (τ : ∀ a, Irr k (dτ a)), (∀ a, Commutes x (τ a)) → ∀ (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N), Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))))
    (dτ : Fin (s + 1) → ℕ) (τ : ∀ a, Irr k (dτ a)) (hc : ∀ a, Commutes x (τ a)) (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N) :
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  have key : ∀ (S : ℕ) (e' : (Σ a : Fin s, Fin (dτ a.succ)) ≃ Fin S) (h : dτ 0 + S = T),
      Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
    intro S e' h
    have H := multiProd_head (k := k) (fun a => (τ a).π) e h e'
    have sR : IsSmooth (multiProd e' fun a : Fin s => (τ a.succ).π) :=
      GlobalTheory.SmGL.isSmooth_parInd e' (piTensor fun a : Fin s => (τ a.succ).π)
    exact commutes_ind₂_of_head x (τ 0) _ sR _ h H (hc 0)
      (fun M g₁ g₂ => ih (fun a => dτ a.succ) (fun a => τ a.succ) (fun a => hc a.succ) _ M e' g₁ g₂) h₁ h₂
  have h : dτ 0 + ∑ a : Fin s, dτ a.succ = T := by
    have := Fintype.card_congr e
    simp only [Fintype.card_sigma, Fintype.card_fin] at this
    rw [← this]
    exact (Fin.sum_univ_succ _).symm
  exact key _ (finSigmaFinEquiv (n := fun a : Fin s => dτ a.succ)) h
end Succ

theorem commutes_multiProd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p u : ℕ) (x : Irr k p) (dτ : Fin (u + 1) → ℕ) (τ : ∀ a, Irr k (dτ a)), (∀ a, Commutes x (τ a)) → ∀ (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N), Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  intro k _ _ _ _ p u x
  induction u with
  | zero =>
    intro dτ τ hc T N e h₁ h₂
    have hT : T = dτ 0 := by
      have := Fintype.card_congr e
      simpa [Fintype.card_sigma] using this.symm
    subst hT
    exact commutes_multiProd_single x τ (hc 0) N e h₁ h₂
  | succ u ih =>
    exact commutes_multiProd_succ x ih

end GlobalTheory.ProdReorder
