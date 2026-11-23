import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinC
import Development.WeilBound.ThetaLifts.LatticeBasics.SecLaw
import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat

noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ β : Type} [Fintype κ] [Fintype β] {m n : ℕ}

variable {A : Spc F E m} {Y : Spc F E n} {B : Base F E}

theorem isSec_of {dd} {χ : Chr F E} {om S l} (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ ⊕ κ) B.ψ dd χ om S l)
    {K : Subgroup (G2 σ Y)} {Φ} (hΦ : Φ ∈ kfin om K) : IsSec K χ (((m : ℂ) - n) / 2) fun x => l (om x Φ) := by
  obtain ⟨N, _, h0, h1, h2⟩ := hΦ
  obtain ⟨c1, c2⟩ := sec_cont_law h (h0 h1)
  refine ⟨c1, c2, Submodule.finiteDimensional_of_le (S₂ := N.map (LinearMap.pi fun x => l ∘ₗ om x)) (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨k, rfl⟩
  exact ⟨_, h2 k.1 k.2 Φ h1, funext fun x => by simp [map_mul]⟩

theorem polData_kfin {a d : ℕ} {X : Spc F E a} {W : Spc F E d} {M : Model σ X W} (hM : M.IsGood B.ψ)
    {N : Submodule ℂ (((Fin a × Fin d) ⊕ (Fin a × Fin d) → AF F) → ℂ)}
    (h : ∀ g₁ ∈ SB _, ∀ g₂ ∈ SB _, ∀ f₁ ∈ M.Pol B.ψ B.emb, ∀ f₂ ∈ M.Pol B.ψ B.emb,
      boxFun (pureA F f₁ g₁) (star (pureA F f₂ g₂)) ∈ N) {Φ₁ Φ₂} (h1 : Φ₁ ∈ PolData B M) (h2 : Φ₂ ∈ PolData B M) :
    boxFun Φ₁ (star Φ₂) ∈ N := by
  induction h1 using Submodule.span_induction with
  | mem Φ₁ m1 =>
    obtain ⟨f, hf, φ, a1, a2, rfl⟩ := m1
    induction h2 using Submodule.span_induction with
    | mem Φ₂ m2 =>
      obtain ⟨f', hf', φ', b1, b2, rfl⟩ := m2
      exact h _ (pf_mem ⟨a1, (a2.and hM.std).mono fun v hv => hv.1.trans hv.2⟩) _
        (pf_mem ⟨b1, (b2.and hM.std).mono fun v hv => hv.1.trans hv.2⟩) f hf f' hf'
    | zero => convert N.zero_mem; funext z; simp [boxFun]
    | add _ _ _ _ i j => convert N.add_mem i j; funext z; simp [boxFun, mul_add]
    | smul c _ _ i => convert N.smul_mem (star c) i; funext z; simp [boxFun, mul_left_comm]
  | zero => convert N.zero_mem; funext z; simp [boxFun]
  | add _ _ _ _ i j => convert N.add_mem i j; funext z; simp [boxFun, add_mul]
  | smul c _ _ i => convert N.smul_mem c i; funext z; simp [boxFun, mul_assoc]

theorem _root_.GlobalTheory.ThK.Dbl.boxSec_of (hL : FinLevel) (hC : Stab2Cpt) : BoxSec := by
  intro F E _ _ _ _ _ σ B m n A Y M r s r' s' hB _ _ _ _ hY hM χ _ _ dd om S l hd h K a hK _ Φ₁ h1 Φ₂ h2
  refine isSec_of h (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => box_kfin hL hB hK (hC F E σ B n Y r' s' hB (.inr hY) K hK)
    h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
      fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) h1 h2)
  · exact hε u u' hu hu' e _ _ (actsD_dop M hB.std hu f) (actsD_dop M hB.std hu' f)
  · rw [actsD_unique' M hB.std hu e]; exact n2 u hu f hf

theorem _root_.GlobalTheory.ThK.Dbl.boxSecX_of (hL : FinLevel) (hC : Stab2Cpt) : BoxSecX := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hX _ _ hM χ _ _ dd om S l ⟨d', ht, hd⟩ h K a hK _ Φ₁ h1 Φ₂ h2
  have tr : ∀ {p q : ℕ} {u : Matrix (Fin p) (Fin q) (AE F E)}, At (evI F) u → At (evI F) uᵀ := fun hu c hc => by
    rw [← Matrix.transpose_smul, hu c hc, Matrix.transpose_zero]
  refine isSec_of h (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => box_kfin hL hB hK (hC F E σ B n X r s hB (.inl hX) K hK)
    h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
      fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) h1 h2)
  · rw [← u.transpose_transpose, ← u'.transpose_transpose, ht, ht]
    refine hε uᵀ u'ᵀ (tr hu) (tr hu') (fun w => ?_) _ _ (actsD_dop M hB.std (tr hu) f) (actsD_dop M hB.std (tr hu') f)
    rw [Matrix.transpose_map, Matrix.transpose_map, e w, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  · rw [actsD_unique' M hB.std hu e]
    have := n2 uᵀ (tr hu) f hf
    rwa [ht] at this

end GlobalTheory.ThK.Dbl.Box

end
