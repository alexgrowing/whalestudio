import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PairingExtends

noncomputable section

namespace PositivityTheory.HtPt.Twpdiv

open TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {G : PDivGroup p O}

def lvl (G : PDivGroup p O) (n : ℕ) : G.Tate →+ Additive (WithConv (G.A n →ₐ[O] O)) where
  toFun x := Additive.ofMul (x.conv n)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem lvl_smul (n : ℕ) (a : ℤ_[p]) (x : G.Tate) : lvl G n (a • x) = digit n a • lvl G n x := rfl

theorem tate_equiv {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (τ : La →+ G.Tate)
    (h1 : ∀ n a a', (τ a).conv n = (τ a').conv n ↔ ∃ b : La, a - a' = (p ^ n) • b)
    (h2 : ∀ n y, ∃ a, (τ a).conv n = y) :
    ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] G.Tate, ∀ a, j (1 ⊗ₜ a) = τ a := by
  classical
  let j : ℤ_[p] ⊗[ℤ] La →ₗ[ℤ_[p]] G.Tate := LinearMap.liftBaseChange ℤ_[p] τ.toIntLinearMap
  have hj : ∀ (c : ℤ_[p]) a, j (c ⊗ₜ a) = c • τ a := fun c a => rfl
  let b := Module.Free.chooseBasis ℤ La
  have key : ∀ (c : Module.Free.ChooseBasisIndex ℤ La → ℤ_[p]) n,
      (j (∑ i, c i ⊗ₜ b i)).conv n = (τ (∑ i, digit n (c i) • b i)).conv n := by
    intro c n
    change lvl G n _ = lvl G n _
    simp only [map_sum, hj, lvl_smul, map_nsmul]
  have hdiv : ∀ n (a a' : La), (∃ u : La, a - a' = (p ^ n) • u) ↔
      ∀ i, ((b.repr a i : ℤ) : ZMod (p ^ n)) = (b.repr a' i : ℤ) := by
    intro n a a'
    simp only [ZMod.intCast_eq_intCast_iff_dvd_sub]
    constructor
    · rintro ⟨u, hu⟩ i
      have := congrArg (fun x => b.repr x i) hu
      simp only [map_sub, map_nsmul, Finsupp.sub_apply, Finsupp.smul_apply, nsmul_eq_mul] at this
      rw [dvd_sub_comm]
      exact ⟨_, this⟩
    · intro H
      choose u hu using fun i => dvd_sub_comm.1 (H i)
      refine ⟨b.equivFun.symm u, b.equivFun.injective (funext fun i => ?_)⟩
      rw [map_nsmul, LinearEquiv.apply_symm_apply, map_sub]
      simpa using hu i
  have hrep : ∀ (k : Module.Free.ChooseBasisIndex ℤ La → ℕ) i, b.repr (∑ i, k i • b i) i = k i := by
    intro k i
    have : ∑ i, k i • b i = b.equivFun.symm fun i => (k i : ℤ) := by simp
    rw [this, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨LinearEquiv.ofBijective j ⟨?_, fun x => ?_⟩, fun a => (hj 1 a).trans (one_smul _ _)⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨c, rfl⟩ : ∃ c : Module.Free.ChooseBasisIndex ℤ La → ℤ_[p], z = ∑ i, c i ⊗ₜ b i := by
      refine ⟨(b.baseChange ℤ_[p]).repr z, ?_⟩
      conv_lhs => rw [← (b.baseChange ℤ_[p]).sum_repr z]
      simp [TensorProduct.smul_tmul']
    have hc : ∀ i, c i = 0 := fun i => PadicInt.ext_of_toZModPow.1 fun n => by
      have h3 := key c n
      rw [hz, ← map_zero τ] at h3
      have h4 := (hdiv n _ _).1 ((h1 n _ _).1 h3) i
      rw [hrep] at h4
      rw [map_zero, ← cast_digit]
      simpa using h4.symm
    simp [hc]
  · choose a ha using fun n => h2 n (x.conv n)
    have hc : ∀ n, (τ (a (n + 1))).conv n = (τ (a n)).conv n := fun n => by
      rw [← TateOver.compat_conv, ha, ha, TateOver.compat_conv]
    have hd : ∀ i n, (p : ℤ) ^ n ∣ b.repr (a (n + 1)) i - b.repr (a n) i := fun i n => by
      have := (hdiv n _ _).1 ((h1 n _ _).1 (hc n).symm) i
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
      exact_mod_cast this
    refine ⟨∑ i, PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (fun n => b.repr (a n) i) p (hd i)) ⊗ₜ b i,
      TateOver.ext_conv fun n => ?_⟩
    rw [key, ← ha, h1, hdiv]
    intro i
    rw [hrep, Int.cast_natCast, cast_digit, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
      (fun n => b.repr (a n) i) p (hd i)]

end PositivityTheory.HtPt.Twpdiv
