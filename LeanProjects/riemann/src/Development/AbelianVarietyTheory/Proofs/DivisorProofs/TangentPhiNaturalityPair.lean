import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.PDiv

namespace GlobalTheory.SqZeroPt

theorem tanDer_cn : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) → ∀ (v : epsR O ⟶ A) (hv : IsTangent v) (h : zeroSec O O ≫ v = η[A]) (n : ℕ) (w : Wmod A), t.tanDer hv n (cn t n w) = Ideal.Quotient.mk _ (Phi v h w) := by
  intro p O _ G A _ t hlin hpt v hv h n w
  haveI : IsCentralScalar O (ModPow p O n) := ⟨fun r m => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
    change (Submodule.Quotient.mk (MulOpposite.op r • x) : ModPow p O n) =
      Submodule.Quotient.mk (r • x)
    rw [op_smul_eq_smul]⟩
  let mk : O →ₗ[O] ModPow p O n := (Ideal.Quotient.mkₐ O _).toLinearMap
  let v' : TM O (ModPow p O n) ⟶ A := GlobalTheory.GrpTangent.sqZeroMap mk ≫ v
  have hsq : ∀ l : O →ₗ[O] ModPow p O n,
      GlobalTheory.GrpTangent.sqZeroMap l = spOver (TrivSqZeroExt.map l) := fun _ => rfl
  have hsc : ∀ c : O, GlobalTheory.GrpTangent.epsScale c =
      spOver (TrivSqZeroExt.map (c • (LinearMap.id : O →ₗ[O] O))) := fun _ => rfl
  have hpow : v' ^ p ^ n = 1 := by
    have h0 : mk ∘ₗ (((p ^ n : ℕ) : O) • (LinearMap.id : O →ₗ[O] O)) =
        mk ∘ₗ ((0 : O) • (LinearMap.id : O →ₗ[O] O)) := by
      refine LinearMap.ext fun x => ?_
      have hz : mk ((p ^ n : ℕ) : O) = 0 := by
        change Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) ((p ^ n : ℕ) : O) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
        exact Ideal.mem_span_singleton_self _
      change mk (((p ^ n : ℕ) : O) • x) = mk ((0 : O) • x)
      rw [zero_smul, map_zero, smul_eq_mul, mul_comm, ← smul_eq_mul, map_smul, hz, smul_zero]
    have e1 : GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale ((p ^ n : ℕ) : O) =
        GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale 0 := by
      rw [hsq, hsc, hsc, spOver_comp, spOver_comp, ← TrivSqZeroExt.map_comp_map,
        ← TrivSqZeroExt.map_comp_map, h0]
    change (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v) ^ p ^ n = 1
    rw [← MonObj.comp_pow, GlobalTheory.GrpTangent.pow_eq_epsScale_comp hv, ← Category.assoc, e1,
      Category.assoc, GlobalTheory.GrpTangent.epsScale_zero_comp hv, MonObj.comp_one]
  obtain ⟨φ, hφv⟩ := t.surj n (TrivSqZeroExt O (ModPow p O n)) v' hpow
  have hone : spOver (TrivSqZeroExt.fstHom O O O) ≫ v = 1 := by
    have h2 := congrArg Over.Hom.left h
    simp only [Over.comp_left] at h2
    ext1
    simp only [Over.comp_left]
    change (zeroSec O O).left ≫ v.left = _
    rw [h2]
    have hu : (toUnit (Over.mk (spMap (algebraMap O O)))).left = 𝟙 (Sp O) := by
      rw [Over.toUnit_left]; exact Spec.map_id _
    change _ = (toUnit (Over.mk (spMap (algebraMap O O)))).left ≫ η[A].left
    erw [hu]
    exact (Category.id_comp _).symm
  have hφ : (TrivSqZeroExt.fstHom O O (ModPow p O n)).comp φ =
      Bialgebra.counitAlgHom O (G.A n) := by
    have e : (TrivSqZeroExt.fstHom O O (ModPow p O n)).comp (TrivSqZeroExt.map mk) =
        TrivSqZeroExt.fstHom O O O := by
      ext; simp
    have h1 : spOver ((TrivSqZeroExt.fstHom O O (ModPow p O n)).comp φ) ≫ t.y n = 1 := by
      rw [← spOver_comp, Category.assoc, hφv]
      change spOver _ ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v = 1
      rw [hsq, ← Category.assoc, spOver_comp, e, hone]
    exact AlgHom.ext fun a => ((t.eq_one_iff n _).1 h1 a).trans (by simp)
  let q := Ideal.Quotient.mk (Ideal.span {(p : O) ^ n})
  let κ : TrivSqZeroExt O (ModPow p O n) →ₐ[O] DualNumber (ModPow p O n) :=
    { toFun := fun z => TrivSqZeroExt.inl (q z.fst) + TrivSqZeroExt.inr z.snd
      map_one' := by ext <;> simp
      map_mul' := fun x y => by
        ext
        · simp
        · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr]
          simp [Algebra.smul_def, q, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp [q]
      commutes' := fun r => by ext <;> simp [q, TrivSqZeroExt.algebraMap_eq_inl', Ideal.Quotient.algebraMap_eq] }
  have key : κ.comp (TrivSqZeroExt.map mk) = epsTo O (ModPow p O n) := by
    ext <;> simp [κ, q, mk]
  have htan : t.tanPt hv n = κ.comp φ := by
    refine t.inj n _ _ _ ?_
    rw [t.tanPt_y hv n, ← spOver_comp, Category.assoc, hφv]
    change _ = spOver κ ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v
    rw [hsq, ← Category.assoc, spOver_comp, key]
  have hder : t.tanDer hv n =
      GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) (ModPow p O n) ⟨φ, hφ⟩ :=
    GlobalTheory.AugCot.hom_ext fun a => by
      change t.tanDer hv n (dUnit O a) = _
      rw [t.tanDer_d hv n, GlobalTheory.AugCot.sqZeroEquiv_d, htan]
      simp [κ]
  have h' : zeroSec O (ModPow p O n) ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v = η[A] :=
    by have e := zeroSec_spOver_y t n φ hφ; rw [hφv] at e; exact e
  have hc : ∀ (z z' : TM O (ModPow p O n) ⟶ A) (e : z = z') (hz : zeroSec O (ModPow p O n) ≫ z = η[A])
      (hz' : zeroSec O (ModPow p O n) ≫ z' = η[A]), Phi z hz w = Phi z' hz' w := by
    intro z z' e hz hz'; subst e; rfl
  rw [hder, ← hpt (ModPow p O n) n φ hφ w, hc _ _ hφv _ h']
  exact hlin O (ModPow p O n) mk v h h' w

end GlobalTheory.SqZeroPt
