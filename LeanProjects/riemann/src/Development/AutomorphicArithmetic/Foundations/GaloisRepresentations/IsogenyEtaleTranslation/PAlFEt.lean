import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel
import Development.AbelianVarietyTheory.Definitions.Divisors.NontrivialOfArtinQE

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo

namespace UpperTheory.Gal.FixZ

private theorem act_nat {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] (act : OActN O A) (n : ℕ) :
    act.act (n : O) = (𝟙 A) ^ n := by
  induction n with
  | zero => simp [KS.Model.act_zero]
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, _root_.pow_succ]

private theorem list_prod_ofFn_eq_of_eq_one_of_ne' {M : Type*} [Monoid M] :
    ∀ {m : ℕ} (f : Fin m → M) (i : Fin m), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i := by
  intro m
  induction m with
  | zero => intro f i; exact i.elim0
  | succ m ih =>
    intro f i hf
    rw [List.ofFn_succ, List.prod_cons]
    cases i using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, _root_.mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact hf _ (Fin.succ_ne_zero j)
    | succ i =>
      rw [hf 0 (Fin.succ_ne_zero i).symm, _root_.one_mul]
      exact ih (fun j => f j.succ) i (fun j hj => hf _ (fun h => hj (Fin.succ_injective _ h)))

private theorem matEnd_diagonal_pr {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ}
    (d : Fin m → O) (i : Fin m) :
    GlobalTheory.KS.matEnd act (Matrix.diagonal d) ≫ GlobalTheory.KS.pr A i = GlobalTheory.KS.pr A i ≫ act.act (d i) := by
  simp only [GlobalTheory.KS.matEnd, GlobalTheory.KS.pr, Pi.lift_π]
  rw [list_prod_ofFn_eq_of_eq_one_of_ne' _ i]
  · simp [Matrix.diagonal_apply_eq]
  · intro j hj
    rw [Matrix.diagonal_apply_ne d (Ne.symm hj), KS.Model.act_zero, comp_one]

end UpperTheory.Gal.FixZ

open UpperTheory.Gal.FixZ in
theorem UpperTheory.Gal.FixZ.alFEt_of :
    UpperTheory.Gal.G3.IsogFEt → UpperTheory.Gal.FixZ.PowFEt → UpperTheory.Gal.FixZ.AlFEt := by
  intro hIsog hPow p _ D G L gb k T N α hα
  have hc : ∀ a : 𝓞 D.toG.F, a ≠ 0 → ∃ b : 𝓞 D.toG.F, ∃ d : ℕ, 0 < d ∧ a * b = (d : 𝓞 D.toG.F) := by
    intro a ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    refine ⟨b, Ideal.absNorm (Ideal.span {a}), Nat.pos_of_ne_zero ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact ha
    · rw [← hb, mul_comm]
  set U := (T.M N).univ with hU
  letI := U.grp
  letI := U.comm
  have key : ∀ x y : 𝓞 D.toG.F, ∀ d : ℕ, x * y = d →
      U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O y) ≫ U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O x)
        = 𝟙 U.A ^ d := by
    intro x y d h
    rw [← U.act.mul, ← map_mul, h, map_natCast, act_nat]
  have hf : ∀ s : Fin k, IsFinite (Over.Hom.left (U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s)))) ∧
      Etale (Over.Hom.left (U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s)))) ∧
      Surjective (Over.Hom.left (U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s)))) := by
    intro s
    obtain ⟨b, d, hd, hab⟩ := hc (α s) (hα s)
    have e1 := key b (α s) d ((mul_comm b (α s)).trans hab)
    have e2 := key (α s) b d hab
    exact hIsog ℂ (T.M N).X (T.M N).s U.A U.A U.ab U.ab _ _ d hd (U.act.hom _) (U.act.hom _) e1 e2
  have hg := hPow _ U.A k (fun s => U.act.act (algebraMap (𝓞 D.toG.F) D.toG.O (α s))) hf
    (KS.matEnd U.act (LocalSmoothExtension.diagO D α)) (fun i => matEnd_diagonal_pr U.act _ i)
  obtain ⟨h1, h2, -⟩ := hg
  show IsFinite ((T.e N).hom ≫ _ ≫ (T.e N).inv) ∧ Etale ((T.e N).hom ≫ _ ≫ (T.e N).inv)
  exact ⟨inferInstance, inferInstance⟩

end
