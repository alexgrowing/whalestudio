import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.EtaleTrace

theorem bilin_ext_one_tmul (l : ℕ) [Fact l.Prime] {M N W : Type 1} [AddCommGroup M] [Module ℤ_[l] M] [AddCommGroup N]
    [Module ℤ_[l] N] [AddCommGroup W] [Module ℚ_[l] W]
    (f g : (ℚ_[l] ⊗[ℤ_[l]] M) ⊗[ℚ_[l]] (ℚ_[l] ⊗[ℤ_[l]] N) →ₗ[ℚ_[l]] W)
    (h : ∀ x y, f ((1 ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y)) = g ((1 ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y))) : f = g := by
  refine TensorProduct.ext' fun u v => ?_
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [TensorProduct.add_tmul, map_add, map_add, ha, hb]
  | tmul a x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => rw [TensorProduct.tmul_add, map_add, map_add, hc, hd]
    | tmul b y =>
      have e1 : (a ⊗ₜ[ℤ_[l]] x : ℚ_[l] ⊗[ℤ_[l]] M) = a • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have e2 : (b ⊗ₜ[ℤ_[l]] y : ℚ_[l] ⊗[ℤ_[l]] N) = b • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1, e2, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul, map_smul, map_smul, map_smul, h]

theorem kun_bijective_of_kunIso (l : ℕ) [Fact l.Prime] {k : Type} [Field k] {X Y : Scheme.{0}} (p : X ⟶ S k) (q : Y ⟶ S k)
    (n : ℤ) (hc : ∀ (a m r : ℤ) (h : a + m = r), IsCup l (pullback p q) h (cupV l (pullback p q) h))
    (hk : LateralTheory.KummerTheory.KunIso l p q n 0) : Function.Bijective (kun l p q n) := by
  obtain ⟨κ, hκ⟩ := hk
  have e : kun l p q n = κ.toLinearMap := by
    refine DirectSum.linearMap_ext _ fun a => ?_
    refine bilin_ext_one_tmul l _ _ fun x y => ?_
    obtain ⟨z, hz, hz'⟩ := hκ a x y
    refine Eq.trans ?_ hz'.symm
    have h1 := hc a (n - a) n (by omega) (pullHl l (sch.map (pullback.fst p q)) a 0 x)
      (pullHl l (sch.map (pullback.snd p q)) (n - a) 0 y) z (fun j => hz j)
    refine Eq.trans ?_ h1
    simp only [kun, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    rfl
  rw [e]
  exact κ.bijective

theorem LKunneth_of (hR : LRing) (hK : LateralTheory.KummerTheory.GOAL) : LKunneth := by
  intro hB l _ k _ _ hl d e X Y p q hp hq n
  have hc := (hR hB l).1
  obtain ⟨⟨-, a2, -, -, -, a6n, a6r, -, -, a7, a8, a9, a10, a11⟩, ⟨b1, b2, b3, -, -⟩, -, ⟨-, e2, e3, e4, -, -⟩⟩ := hB
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, -⟩ := hq
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  exact kun_bijective_of_kunIso l p q n (hc _)
    (hK a2 a6n a6r a7 a8 a9 a10 a11 b1 b2 b3 e2 e3 e4 l k (isUnit_iff_ne_zero.2 hl) p q n 0)

end LateralTheory.EtaleTrace

end
