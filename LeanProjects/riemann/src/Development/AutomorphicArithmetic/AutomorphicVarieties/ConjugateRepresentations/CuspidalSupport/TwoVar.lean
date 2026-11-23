import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

namespace UpperTheory.V.Cj.S

section SlopeTestRemainingChoices

variable {X Y V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private noncomputable def sl1 (jW : W →ₗ[ℂ] (Y → ℂ)) (y : Y) : V ⊗[ℂ] W →ₗ[ℂ] V :=
  (TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V (LinearMap.proj y ∘ₗ jW)

private noncomputable def sl2 (jV : V →ₗ[ℂ] (X → ℂ)) (x : X) : V ⊗[ℂ] W →ₗ[ℂ] W :=
  (TensorProduct.lid ℂ W).toLinearMap ∘ₗ LinearMap.rTensor W (LinearMap.proj x ∘ₗ jV)

private theorem slice_first_tmul (jW : W →ₗ[ℂ] (Y → ℂ)) (y : Y) (v : V) (w : W) : sl1 jW y (v ⊗ₜ[ℂ] w) = jW w y • v := by
  simp [sl1]

end SlopeTestRemainingChoices

end UpperTheory.V.Cj.S

private theorem tensor_exists_finBasis_expansion {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] (t : V ⊗[ℂ] W) :
    ∃ m : Fin (Module.finrank ℂ V) → W, t = ∑ a, Module.finBasis ℂ V a ⊗ₜ[ℂ] m a := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul v w =>
    refine ⟨fun a => (Module.finBasis ℂ V).repr v a • w, ?_⟩
    conv_lhs => rw [← (Module.finBasis ℂ V).sum_repr v]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact TensorProduct.smul_tmul _ _ _
  | add t1 t2 h1 h2 =>
    obtain ⟨m1, rfl⟩ := h1
    obtain ⟨m2, rfl⟩ := h2
    exact ⟨m1 + m2, by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

private theorem tensor_eq_zero_of_sl1_vanishing {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] (jW : W →ₗ[ℂ] (Y → ℂ)) (hjW : Function.Injective jW) (t : V ⊗[ℂ] W)
    (ht : ∀ y, UpperTheory.V.Cj.S.sl1 jW y t = 0) : t = 0 := by
  obtain ⟨m, rfl⟩ := tensor_exists_finBasis_expansion (V := V) (W := W) t
  have hm : ∀ a, m a = 0 := by
    intro a
    apply hjW
    rw [map_zero]
    funext y
    have hy := ht y
    simp only [map_sum, UpperTheory.V.Cj.S.slice_first_tmul] at hy
    have := (Fintype.linearIndependent_iff.mp (Module.finBasis ℂ V).linearIndependent) (fun a => jW (m a) y) hy a
    simpa using this
  simp [hm]

private theorem exists_vec_of_dual_apply_col {X Y V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] (jV : V →ₗ[ℂ] (X → ℂ)) (hjV : Function.Injective jV)
    (jW : W →ₗ[ℂ] (Y → ℂ)) (col : Y → V) (hrow : ∀ x, ∃ w : W, jW w = fun y => jV (col y) x)
    (φ : Module.Dual ℂ V) : ∃ w : W, jW w = fun y => φ (col y) := by
  let P : Submodule ℂ (Module.Dual ℂ V) :=
    { carrier := {ψ | ∃ w : W, jW w = fun y => ψ (col y)}
      add_mem' := by
        rintro ψ χ ⟨w1, h1⟩ ⟨w2, h2⟩
        exact ⟨w1 + w2, by rw [map_add, h1, h2]; rfl⟩
      zero_mem' := ⟨0, by rw [map_zero]; rfl⟩
      smul_mem' := by
        rintro c ψ ⟨w, h⟩
        exact ⟨c • w, by rw [map_smul, h]; rfl⟩ }
  have hev : ∀ x, (LinearMap.proj x ∘ₗ jV) ∈ P := by
    intro x
    obtain ⟨w, h⟩ := hrow x
    exact ⟨w, h⟩
  have hco : P.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    rw [Submodule.mem_bot]
    apply hjV
    funext x
    simpa using hv _ (hev x)
  have htop : P = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := P), hco, Submodule.dualAnnihilator_bot]
  have hφ : φ ∈ P := by
    rw [htop]
    exact Submodule.mem_top
  exact hφ

theorem UpperTheory.V.Cj.S.twoVar :
    UpperTheory.V.Cj.S.TensEig → UpperTheory.V.Cj.S.TwoVar := by
  intro hT X Y M N V W hVf hWf ι κ A B hAV hBW hAc hBc F hF hcol hrow
  let jV : V →ₗ[ℂ] (X → ℂ) := M.subtype ∘ₗ V.subtype
  let jW : W →ₗ[ℂ] (Y → ℂ) := N.subtype ∘ₗ W.subtype
  have hjV : Function.Injective jV := Subtype.val_injective.comp Subtype.val_injective
  have hjW : Function.Injective jW := Subtype.val_injective.comp Subtype.val_injective
  choose col hcolV hcolF using hcol
  let colV : Y → V := fun y => ⟨col y, hcolV y⟩
  have hjcol : ∀ y, jV (colV y) = fun x => F x y := fun y => hcolF y
  have hrow' : ∀ x, ∃ w : W, jW w = fun y => jV (colV y) x := by
    intro x
    obtain ⟨f, hfW, hf⟩ := hrow x
    refine ⟨⟨f, hfW⟩, ?_⟩
    funext y
    rw [hjcol]
    show (f : Y → ℂ) y = F x y
    rw [hf]
  let bV := Module.finBasis ℂ V
  choose w hw using fun a => exists_vec_of_dual_apply_col jV hjV jW colV hrow' (bV.coord a)
  let z : V ⊗[ℂ] W := ∑ a, bV a ⊗ₜ[ℂ] w a
  have hz : ∀ y, UpperTheory.V.Cj.S.sl1 jW y z = colV y := by
    intro y
    simp only [z, map_sum, UpperTheory.V.Cj.S.slice_first_tmul, hw]
    simpa [Module.Basis.coord_apply] using bV.sum_repr (colV y)
  have hFz : ∀ x y, jV (UpperTheory.V.Cj.S.sl1 jW y z) x = F x y := by
    intro x y
    rw [hz, hjcol]
  have hz0 : z ≠ 0 := by
    obtain ⟨x0, y0, h0⟩ := hF
    intro h
    apply h0
    rw [← hFz, h]
    simp
  let A' : ι → Module.End ℂ V := fun i => (A i).restrict (hAV i)
  let B' : κ → Module.End ℂ W := fun k => (B k).restrict (hBW k)
  have hA' : ∀ i (v : V), ((A' i v : V) : M) = A i v := fun i v => rfl
  have hB' : ∀ k (w : W), ((B' k w : W) : N) = B k w := fun k w => rfl
  have cA : ∀ i i', Commute (A' i) (A' i') := by
    intro i i'
    exact LinearMap.ext fun v => Subtype.ext (hAc i i' v v.2)
  have cB : ∀ k k', Commute (B' k) (B' k') := by
    intro k k'
    exact LinearMap.ext fun w => Subtype.ext (hBc k k' w w.2)
  obtain ⟨v, w', l, m, hv, hw', hAv, hBw, hprop⟩ := hT V W ι κ A' B' cA cB z hz0
  refine ⟨v, v.2, w', w'.2, l, m, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hv (Subtype.ext h)
  · intro h
    exact hw' (Subtype.ext h)
  · intro i
    have := congrArg Subtype.val (hAv i)
    simpa [hA'] using this
  · intro k
    have := congrArg Subtype.val (hBw k)
    simpa [hB'] using this
  · intro σ _ c ip kp G e hAct hsum
    have hsumV : ∀ y', (∑ a, jW (w a) y' • bV a) = colV y' := by
      intro y'
      simpa [hw, Module.Basis.coord_apply] using bV.sum_repr (colV y')
    have key : ∀ i k (Gp : X → Y → ℂ), Act2 (A i) (B k) F Gp → ∀ x y,
        jV (UpperTheory.V.Cj.S.sl1 jW y (TensorProduct.map (A' i) (B' k) z)) x = Gp x y := by
      intro i k Gp hG x y
      obtain ⟨H, h1, h2⟩ := hG
      have hH : ∀ x' y', H x' y' = ∑ a, jW (w a) y' * jV (A' i (bV a)) x' := by
        intro x' y'
        obtain ⟨f, hf1, hf2⟩ := h1 y'
        have hf : f = ((∑ a, jW (w a) y' • bV a : V) : M) := by
          apply Subtype.val_injective
          rw [hf1, hsumV]
          exact (hjcol y').symm
        have := congrFun hf2 x'
        rw [← this, hf]
        simp [map_sum, jV, hA']
      obtain ⟨f', hf'1, hf'2⟩ := h2 x
      have hf' : f' = ((∑ a, jV (A' i (bV a)) x • w a : W) : N) := by
        apply Subtype.val_injective
        rw [hf'1]
        funext y'
        rw [hH]
        simp [jW, jV, Finset.sum_apply, mul_comm]
      rw [← hf'2, hf']
      simp [z, map_sum, TensorProduct.map_tmul, UpperTheory.V.Cj.S.slice_first_tmul, jV, jW, hB', mul_comm]
    apply hprop σ c ip kp e
    rw [← sub_eq_zero]
    apply tensor_eq_zero_of_sl1_vanishing jW hjW
    intro y
    apply hjV
    rw [map_zero]
    funext x
    have key' : ∀ p, jV (UpperTheory.V.Cj.S.sl1 jW y (TensorProduct.map (A' (ip p)) (B' (kp p)) z)) x = G p x y :=
      fun p => key _ _ _ (hAct p) x y
    have hval : jV (UpperTheory.V.Cj.S.sl1 jW y
        (∑ p, c p • TensorProduct.map (A' (ip p)) (B' (kp p)) z - e • z)) x = ∑ p, c p * G p x y - e * F x y := by
      simp only [map_sub, map_sum, map_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, key', hFz]
    rw [hval, hsum, sub_self]
    rfl
