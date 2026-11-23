import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands TensorProduct Module

namespace DiscreteGroups.sglob.DzType

section Split

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem gsplit_tensor_sum {V V' V'' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] [AddCommGroup V''] [Module ℂ V'']
    [FiniteDimensional ℂ V''] (a : WDRep h V) (b : WDRep h V') (c : WDRep h V'') :
    (a.tensor (b.sum c)).Iso ((a.tensor b).sum (a.tensor c)) := by
  refine ⟨TensorProduct.prodRight ℂ ℂ V V' V'', fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => obtain ⟨y1, y2⟩ := y; simp
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => obtain ⟨y1, y2⟩ := y; simp
    | add x y hx hy => simp only [map_add, hx, hy]

theorem gsplit_lpChar_lpSum (x y z : WD h) :
    x.lpChar (y.lpSum z) = (x.lpChar y).lpSum (x.lpChar z) := by
  obtain ⟨n1, a, rfl⟩ := x.exists_rep
  obtain ⟨n2, b, rfl⟩ := y.exists_rep
  obtain ⟨n3, c, rfl⟩ := z.exists_rep
  rw [WD.lpSum_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpSum_mk]
  exact WD.sound (gsplit_tensor_sum a b c)

def gsplitEquiv (n : ℕ) : (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin 1 → ℂ) × (Fin n → ℂ) where
  toFun v := (fun _ => v 0, fun j => v j.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := Fin.cons (p.1 0) p.2
  left_inv v := Fin.cons_self_tail v
  right_inv p := by
    obtain ⟨p1, p2⟩ := p
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · rw [Subsingleton.elim i 0]
      simp
    · simp

theorem gsplitEquiv_apply (n : ℕ) (v : Fin (n + 1) → ℂ) :
    gsplitEquiv n v = (fun _ => v 0, fun j => v j.succ) := rfl

theorem gsplit_diag_succ {n : ℕ} (c : Fin (n + 1) → ℂˣ) :
    WD.mk (WDRep.diag h c) =
      (WD.lpOfChar h (unrChar h (c 0)) (isSmooth_unrChar h _)).lpSum
        (WD.mk (WDRep.diag h fun j : Fin n => c j.succ)) := by
  rw [WD.lpOfChar, WD.lpSum_mk]
  refine WD.sound ⟨gsplitEquiv n, fun σ v => ?_, fun v => ?_⟩
  · refine Prod.ext (funext fun i => ?_) (funext fun j => ?_) <;> simp [gsplitEquiv_apply]
  · simp only [gsplitEquiv_apply, WDRep.diag_N, WDRep.sum_N, WDRep.ofChars_N, LinearMap.zero_apply,
      LinearMap.prodMap_apply]
    rfl

theorem lpSum_self_of_dim_zero (y : WD h) (hy : y.lpDim = 0) : y.lpSum y = y := by
  obtain ⟨m, a, rfl⟩ := y.exists_rep
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hy
  subst hy
  rw [WD.lpSum_mk]
  exact WD.sound ⟨LinearEquiv.ofFinrankEq _ _ (by simp), fun _ _ => Subsingleton.elim _ _,
    fun _ => Subsingleton.elim _ _⟩

theorem epsilon_eq_one_of_dim_zero {ε : EpsFamily A} (hε : IsDeligneEps ε) (ψ : AddChar (w.adicCompletion E) Circle)
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (y : WD h) (hy : y.lpDim = 0) : ε E w h ψ y = 1 := by
  have h1 := hε.add E w h ψ hψ hψ1 y y
  rw [lpSum_self_of_dim_zero y hy] at h1
  exact mul_left_cancel (a := ε E w h ψ y) (by rw [mul_one]; exact h1.symm)

theorem lpChar_diag_dim_zero (x : WD h) (c : Fin 0 → ℂˣ) : (x.lpChar (WD.mk (WDRep.diag h c))).lpDim = 0 := by
  obtain ⟨m, a, rfl⟩ := x.exists_rep
  rw [WD.lpChar_mk, WD.lpDim_mk, Module.finrank_tensorProduct]
  simp

theorem gsplit_eps {ε : EpsFamily A} (hε : IsDeligneEps ε) (ψ : AddChar (w.adicCompletion E) Circle)
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (x : WD h) :
    ∀ (n : ℕ) (c : Fin n → ℂˣ), ε E w h ψ (x.lpChar (WD.mk (WDRep.diag h c))) =
      ∏ j, ε E w h ψ (x.lpTwist (unrChar h (c j)) (isSmooth_unrChar h (c j)))
  | 0, c => by
    rw [Fin.prod_univ_zero]
    exact epsilon_eq_one_of_dim_zero hε ψ hψ hψ1 _ (lpChar_diag_dim_zero x c)
  | n + 1, c => by
    rw [gsplit_diag_succ, gsplit_lpChar_lpSum, hε.add E w h ψ hψ hψ1, lpChar_lpOfChar,
      gsplit_eps hε ψ hψ hψ1 x n, Fin.prod_univ_succ]

end Split

theorem eps_unr_split {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (u : WD h) (hu : u.unr) :
    ∃ c : Fin u.lpDim → ℂˣ, ∀ ε : EpsFamily A, IsDeligneEps ε →
      ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → ψ ≠ 1 →
      ∀ x : WD h, ε E w h ψ (x.lpChar u) =
        ∏ j, ε E w h ψ (x.lpTwist (unrChar h (c j)) (isSmooth_unrChar h (c j))) := by
  obtain ⟨n, c, rfl⟩ := Unram.exists_diag hu
  have hn : (WD.mk (WDRep.diag h c)).lpDim = n := by rw [WD.lpDim_mk, Module.finrank_fin_fun]
  refine ⟨fun j => c (Fin.cast hn j), fun ε hε ψ hψ hψ1 x => ?_⟩
  rw [gsplit_eps hε ψ hψ hψ1 x n c]
  exact (Fintype.prod_equiv (finCongr hn) _ _ fun j => rfl).symm

end DiscreteGroups.sglob.DzType
