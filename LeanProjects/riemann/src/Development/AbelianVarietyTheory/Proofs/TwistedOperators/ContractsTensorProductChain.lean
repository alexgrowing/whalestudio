import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv

noncomputable section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem exists_piTensor_succ_equiv (m : ℕ) (F : Fin (m + 1) → Type) [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] :
    ∃ e : ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] F 0) ≃ₗ[ℂ] (⨂[ℂ] j, F j),
      ∀ (f : ∀ j, F j), e (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ f 0) = PiTensorProduct.tprod ℂ f := by
  let σ : Fin m ⊕ Unit ≃ Fin (m + 1) :=
    { toFun := Sum.elim Fin.succ (fun _ => 0)
      invFun := fun k => Fin.cases (motive := fun _ => Fin m ⊕ Unit) (Sum.inr ()) Sum.inl k
      left_inv := by rintro (j | ⟨⟩) <;> simp
      right_inv := by intro k; cases k using Fin.cases <;> simp }
  refine ⟨(TensorProduct.congr (LinearEquiv.refl ℂ _)
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Unit => F 0) ()).symm).trans
      ((PiTensorProduct.tmulEquivDep ℂ (fun i : Fin m ⊕ Unit => F (σ i))).trans
        (PiTensorProduct.reindex ℂ F σ.symm).symm), fun f => ?_⟩
  have h1 : TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] j : Fin m, F j.succ))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Unit => F 0) ()).symm
      (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ f 0) =
      PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ PiTensorProduct.tprod ℂ (fun _ : Unit => f 0) := by
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, PiTensorProduct.subsingletonEquiv_symm_apply']
  have h2 : PiTensorProduct.tmulEquivDep ℂ (fun i : Fin m ⊕ Unit => F (σ i))
      (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ PiTensorProduct.tprod ℂ (fun _ : Unit => f 0)) =
      PiTensorProduct.tprod ℂ (fun i => f (σ i)) := by
    rw [← LinearEquiv.eq_symm_apply, PiTensorProduct.tmulEquivDep_symm_apply]
    all_goals rfl
  have h3 : (PiTensorProduct.reindex ℂ F σ.symm).symm (PiTensorProduct.tprod ℂ (fun i => f (σ i))) =
      PiTensorProduct.tprod ℂ f := by
    rw [LinearEquiv.symm_apply_eq, PiTensorProduct.reindex_tprod]
    all_goals rfl
  show (PiTensorProduct.reindex ℂ F σ.symm).symm (PiTensorProduct.tmulEquivDep ℂ (fun i : Fin m ⊕ Unit => F (σ i))
    (TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] j : Fin m, F j.succ))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Unit => F 0) ()).symm
      (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ f 0))) = PiTensorProduct.tprod ℂ f
  rw [h1]
  exact (congrArg (PiTensorProduct.reindex ℂ F σ.symm).symm h2).trans h3

theorem exists_piTensor_succ_equiv_map (m : ℕ) (F : Fin (m + 1) → Type) [∀ j, AddCommGroup (F j)]
    [∀ j, Module ℂ (F j)] :
    ∃ e : ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] F 0) ≃ₗ[ℂ] (⨂[ℂ] j, F j),
      ∀ (A : ∀ j, F j →ₗ[ℂ] F j) (t : ⨂[ℂ] j : Fin m, F j.succ) (a : F 0),
        PiTensorProduct.map A (e (t ⊗ₜ a)) = e (PiTensorProduct.map (fun j : Fin m => A j.succ) t ⊗ₜ A 0 a) := by
  obtain ⟨e, he⟩ := exists_piTensor_succ_equiv m F
  refine ⟨e, fun A t a => ?_⟩
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h1 := he (Fin.cons a f : ∀ j, F j)
    have h2 := he (fun j => A j ((Fin.cons a f : ∀ j, F j) j))
    simp only [Fin.cons_succ, Fin.cons_zero] at h1 h2
    simp only [← TensorProduct.smul_tmul', map_smul, PiTensorProduct.map_tprod, h1, h2]
  | add x y hx hy =>
    simp only [TensorProduct.add_tmul, map_add, hx, hy]

private theorem factor_dual_lemma {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (p : X →ₗ[ℂ] Y) (hp : Function.Surjective p) (l : Module.Dual ℂ X) (hl : ∀ x, p x = 0 → l x = 0) :
    ∃ l' : Module.Dual ℂ Y, ∀ x, l x = l' (p x) := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
  refine ⟨l ∘ₗ s, fun x => ?_⟩
  have hps : p (s (p x)) = p x := by rw [← LinearMap.comp_apply p s, hs, LinearMap.id_apply]
  have h0 : p (x - s (p x)) = 0 := by rw [map_sub, hps, sub_self]
  have h1 := hl _ h0
  rw [map_sub, sub_eq_zero] at h1
  rw [LinearMap.comp_apply]
  exact h1

private theorem lTensor_ker_lemma_2 {Q N P : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup N] [Module ℂ N]
    [AddCommGroup P] [Module ℂ P] (g : N →ₗ[ℂ] P) (hg : Function.Surjective g)
    (l : Module.Dual ℂ (Q ⊗[ℂ] N)) (hl : ∀ q n, g n = 0 → l (q ⊗ₜ n) = 0) :
    ∀ z, LinearMap.lTensor Q g z = 0 → l z = 0 := by
  intro z hz
  obtain ⟨y, rfl⟩ := ((lTensor_exact Q (LinearMap.exact_subtype_ker_map g) hg) z).mp hz
  clear hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul q k =>
    rw [LinearMap.lTensor_tmul]
    exact hl q k.1 (LinearMap.mem_ker.mp k.2)
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

theorem contracts_chain : ∀ (m : ℕ) (G : Fin (m + 1) → Type) [∀ j, Monoid (G j)] (F : Fin m → Type) [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] (V : Fin (m + 1) → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (φ : ∀ j : Fin m, Representation ℂ (G j.castSucc × G j.succ) (F j)) (σ : ∀ j, Representation ℂ (G j) (V j)), (∀ j : Fin m, Contracts (φ j) (σ j.castSucc) (σ j.succ)) → ∃ π : ((⨂[ℂ] j, F j) ⊗[ℂ] V 0) →ₗ[ℂ] V (Fin.last m), Function.Surjective π ∧ (∀ (g : ∀ j, G j) (f : ⨂[ℂ] j, F j) (v : V 0), π (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = σ (Fin.last m) (g (Fin.last m)) (π (f ⊗ₜ[ℂ] v))) ∧ ∀ l : Module.Dual ℂ ((⨂[ℂ] j, F j) ⊗[ℂ] V 0), (∀ g : ∀ j, G j, g (Fin.last m) = 1 → ∀ (f : ⨂[ℂ] j, F j) (v : V 0), l (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = l (f ⊗ₜ[ℂ] v)) → ∀ x, π x = 0 → l x = 0 := by
  intro m
  induction m with
  | zero =>
    intro G _ F _ _ V _ _ φ σ _
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ((⨂[ℂ] j : Fin 0, F j) ⊗[ℂ] V 0) ≃ₗ[ℂ] V 0,
        ∀ (f : ⨂[ℂ] j : Fin 0, F j) (v : V 0), ψ (f ⊗ₜ v) = PiTensorProduct.isEmptyEquiv (Fin 0) f • v :=
      ⟨(TensorProduct.congr (PiTensorProduct.isEmptyEquiv (Fin 0)) (LinearEquiv.refl ℂ (V 0))).trans
        (TensorProduct.lid ℂ (V 0)), fun f v => by simp⟩
    have hmap : ∀ (A : ∀ j : Fin 0, F j →ₗ[ℂ] F j) (f : ⨂[ℂ] j : Fin 0, F j),
        PiTensorProduct.isEmptyEquiv (Fin 0) (PiTensorProduct.map A f) =
          PiTensorProduct.isEmptyEquiv (Fin 0) f := by
      intro A f
      induction f using PiTensorProduct.induction_on with
      | smul_tprod r x => simp [PiTensorProduct.map_tprod]
      | add x y hx hy => simp only [map_add, hx, hy]
    refine ⟨ψ.toLinearMap, ψ.surjective, ?_, ?_⟩
    · intro g f v
      simp only [LinearEquiv.coe_coe]
      rw [hψ, hψ, hmap, map_smul]
      all_goals rfl
    · intro l _ x hx
      have hx' : ψ x = 0 := hx
      rw [ψ.map_eq_zero_iff] at hx'
      rw [hx', map_zero]
  | succ m ih =>
    intro G _ F _ _ V _ _ φ σ hc
    obtain ⟨e, he⟩ := exists_piTensor_succ_equiv_map m F
    have hc0 : Contracts (φ 0) (σ 0) (σ (Fin.succ 0)) := hc 0
    obtain ⟨π₀, hs₀, he₀, hk₀⟩ := hc0
    obtain ⟨π', hs', he', hk'⟩ := ih (fun j => G j.succ) (fun j => F j.succ) (fun j => V j.succ)
      (fun j => φ j.succ) (fun j => σ j.succ) (fun j => hc j.succ)
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ((⨂[ℂ] j, F j) ⊗[ℂ] V 0) ≃ₗ[ℂ]
        ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] (F 0 ⊗[ℂ] V 0)),
        ∀ t a v, ψ (e (t ⊗ₜ a) ⊗ₜ v) = t ⊗ₜ (a ⊗ₜ v) :=
      ⟨(TensorProduct.congr e.symm (LinearEquiv.refl ℂ _)).trans (TensorProduct.assoc ℂ _ _ _),
        fun t a v => by simp⟩
    refine ⟨π' ∘ₗ LinearMap.lTensor _ π₀ ∘ₗ ψ.toLinearMap,
      hs'.comp ((LinearMap.lTensor_surjective _ hs₀).comp ψ.surjective), ?_, ?_⟩
    · intro g f v
      show π' (LinearMap.lTensor _ π₀ (ψ (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ
        σ 0 (g 0) v))) = σ (Fin.last (m + 1)) (g (Fin.last (m + 1))) (π' (LinearMap.lTensor _ π₀ (ψ (f ⊗ₜ v))))
      obtain ⟨y, rfl⟩ := e.surjective f
      induction y using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero, TensorProduct.zero_tmul]
        all_goals exact (map_zero _).symm
      | tmul t a =>
        rw [he, hψ, hψ, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
        have h0 : π₀ (φ 0 (g (Fin.castSucc 0), g (Fin.succ 0)) a ⊗ₜ σ 0 (g 0) v) =
            σ (Fin.succ 0) (g (Fin.succ 0)) (π₀ (a ⊗ₜ v)) := he₀ _ _ a v
        rw [h0]
        exact he' (fun j => g j.succ) t (π₀ (a ⊗ₜ v))
      | add y₁ y₂ h₁ h₂ =>
        simp only [map_add, TensorProduct.add_tmul] at h₁ h₂ ⊢
        rw [h₁, h₂]
    · intro l hl x hx
      obtain ⟨L, hL⟩ : ∃ L : Module.Dual ℂ ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] (F 0 ⊗[ℂ] V 0)),
          ∀ z, L z = l (ψ.symm z) := ⟨l ∘ₗ ψ.symm.toLinearMap, fun z => rfl⟩
      have hLe : ∀ t a v, L (t ⊗ₜ (a ⊗ₜ v)) = l (e (t ⊗ₜ a) ⊗ₜ v) := by
        intro t a v
        rw [hL, ← hψ t a v, LinearEquiv.symm_apply_apply]

      have hA : ∀ t u, π₀ u = 0 → L (t ⊗ₜ u) = 0 := by
        intro t u hu
        refine hk₀ (L.comp (TensorProduct.mk ℂ _ _ t)) ?_ u hu
        intro h a v
        simp only [LinearMap.comp_apply, TensorProduct.mk_apply, hLe]
        obtain ⟨gs, hg0, hg0', hg1, hg2, hg3, hgl⟩ : ∃ gs : ∀ j, G j, gs (Fin.castSucc 0) = h ∧ gs 0 = h ∧
            gs (Fin.succ 0) = 1 ∧ (∀ j : Fin m, gs j.succ.castSucc = 1) ∧ (∀ j : Fin m, gs j.succ.succ = 1) ∧
            gs (Fin.last (m + 1)) = 1 :=
          ⟨Pi.mulSingle (Fin.castSucc 0) h, Pi.mulSingle_eq_same _ _, Pi.mulSingle_eq_same _ _,
            Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _, fun j => Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _,
            fun j => Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _, Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _⟩
        have hinv := hl gs hgl (e (t ⊗ₜ a)) v
        rw [← hinv, he]
        simp only [hg0, hg0', hg1, hg2, hg3, ← Prod.one_eq_mk, map_one, PiTensorProduct.map_one,
          Module.End.one_apply]
        all_goals rfl
      have hB := lTensor_ker_lemma_2 π₀ hs₀ L (fun q n hn => hA q n hn)
      obtain ⟨L', hL'⟩ := factor_dual_lemma (LinearMap.lTensor _ π₀) (LinearMap.lTensor_surjective _ hs₀) L hB

      have hD : ∀ g' : ∀ j : Fin (m + 1), G j.succ, g' (Fin.last m) = 1 → ∀ t w,
          L' (PiTensorProduct.map (fun j : Fin m => φ j.succ ((g' j.castSucc : G j.succ.castSucc), g' j.succ)) t ⊗ₜ σ (Fin.succ 0) (g' 0) w) =
            L' (t ⊗ₜ w) := by
        intro g' hg' t w
        obtain ⟨u, rfl⟩ := hs₀ w
        induction u using TensorProduct.induction_on with
        | zero => simp only [map_zero, TensorProduct.tmul_zero]
        | tmul a v =>
          rw [← he₀ 1 (g' 0) a v]
          have k1 := hL' (PiTensorProduct.map (fun j : Fin m => φ j.succ ((g' j.castSucc : G j.succ.castSucc), g' j.succ)) t ⊗ₜ
            (φ 0 (1, g' 0) a ⊗ₜ σ 0 1 v))
          have k2 := hL' (t ⊗ₜ (a ⊗ₜ v))
          rw [LinearMap.lTensor_tmul, hLe] at k1 k2
          have hinv := hl (Fin.cons (1 : G 0) g' : ∀ j, G j)
            (by rw [← Fin.succ_last, Fin.cons_succ]; exact hg') (e (t ⊗ₜ a)) v
          rw [he] at hinv
          exact k1.symm.trans (hinv.trans k2)
        | add u₁ u₂ h₁ h₂ => simp only [map_add, TensorProduct.tmul_add, h₁, h₂]
      have hx' : π' (LinearMap.lTensor _ π₀ (ψ x)) = 0 := hx
      have h1 := hk' L' hD _ hx'
      rw [← hL', hL, LinearEquiv.symm_apply_apply] at h1
      exact h1

end GlobalTheory.OneFunctional
