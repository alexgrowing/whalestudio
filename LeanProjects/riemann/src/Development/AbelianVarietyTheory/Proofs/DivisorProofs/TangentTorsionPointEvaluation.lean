import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpOverFstComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
open GlobalTheory.SqZeroPt
open scoped GlobalTheory.SqZeroPt
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.OpenOmega

namespace GlobalTheory.OpenOmega

theorem snd_pt_tanTors : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (GG : PDivGroup p R) (θ : TorsionMap G GG) (n : ℕ) (hs : PtSurj θ n), SpecProp θ n hs → ∀ (x : Pdiv.LieG G) (h : zeroSec R R ≫ x.1 = η[G]) (w : Wmod G) (a : GG.A n), dUnit R a = cnθ θ n hs w → (θ.pt n _ (tanTors p n x) a).snd = Ideal.Quotient.mk _ (Phi x.1 h w) := by
  intro p _ O _ A _ G θ n hs hsp x h w a ha
  have hv : IsTangent (G := A) x.1 := isTangent_lieG x
  haveI : IsCentralScalar O (ModPow p O n) := ⟨fun r m => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
    change (Submodule.Quotient.mk (MulOpposite.op r • x) : ModPow p O n) =
      Submodule.Quotient.mk (r • x)
    rw [op_smul_eq_smul]⟩
  let v : epsR O ⟶ A := x.1
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
  let z : Tors A (p ^ n) (TrivSqZeroExt O (ModPow p O n)) := ⟨v', hpow⟩
  have h' : zeroSec O (ModPow p O n) ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v = η[A] := by
    rw [← Category.assoc, zeroSec_sqZeroMap]; exact h
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
  have htan : θ.pt n _ (tanTors p n x) = κ.comp (θ.pt n _ z) := by
    refine θ.nat n _ _ κ z _ ?_
    change spOver (epsTo O (ModPow p O n)) ≫ v = spOver κ ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v
    rw [hsq, ← Category.assoc, spOver_comp, key]
  have h1 := hsp (ModPow p O n) z h' w
  have h2 := Phi_sqZeroMap_comp O O (ModPow p O n) A mk v h h' w
  rw [← ha] at h1
  have h3 : AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) (ModPow p O n)
      ⟨θ.pt n _ z, fst_comp_pt θ n z h'⟩ (dUnit O a) = (θ.pt n _ z a).snd :=
    GlobalTheory.AugCot.sqZeroEquiv_d _ _ _
  have h4 : (κ.comp (θ.pt n _ z) a).snd = (θ.pt n _ z a).snd := by simp [κ]
  rw [htan, h4, ← h3, ← h1]
  exact h2

end GlobalTheory.OpenOmega
