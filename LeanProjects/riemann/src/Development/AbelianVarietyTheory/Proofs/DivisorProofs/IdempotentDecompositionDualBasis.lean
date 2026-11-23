import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EAComm

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory.ChainParts

namespace GlobalTheory.ChainParts

theorem idem_coeff {Λ R : Type} [CommRing Λ] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (b : Module.Basis (Fin n) ℤ Λ) (ev : ι → (Λ →+* R)) (cf : ι → Fin n → R)
    (hev : ∀ τ σ, ∑ k, cf τ k * ev σ (b k) = if σ = τ then 1 else 0) (hn : Fintype.card ι = n) (τ : ι) (m : Fin n) :
    ∑ k, ∑ l, cf τ k * cf τ l * ((b.repr (b k * b l) m : ℤ) : R) = cf τ m := by
  let C : Matrix ι (Fin n) R := Matrix.of cf
  let E : Matrix (Fin n) ι R := Matrix.of fun k σ => ev σ (b k)
  have hCE : C * E = 1 := by
    ext τ' σ
    simp only [C, E, Matrix.mul_apply, Matrix.of_apply, hev, Matrix.one_apply, eq_comm]
  have hEC : E * C = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivFinOfCardEq hn)).1 hCE
  have inj : ∀ d d' : Fin n → R, Matrix.vecMul d E = Matrix.vecMul d' E → d = d' := by
    intro d d' h
    have := congrArg (fun v => Matrix.vecMul v C) h
    simpa only [Matrix.vecMul_vecMul, hEC, Matrix.vecMul_one] using this
  have hb : ∀ σ (x : Λ), ∑ m, ((b.repr x m : ℤ) : R) * ev σ (b m) = ev σ x := by
    intro σ x
    conv_rhs => rw [← b.sum_repr x]
    simp only [map_sum, zsmul_eq_mul, map_mul, map_intCast]
  refine congrFun (inj (fun m => ∑ k, ∑ l, cf τ k * cf τ l * ((b.repr (b k * b l) m : ℤ) : R)) (cf τ) ?_) m
  ext σ
  simp only [Matrix.vecMul, dotProduct, E, Matrix.of_apply]
  calc ∑ m, (∑ k, ∑ l, cf τ k * cf τ l * ((b.repr (b k * b l) m : ℤ) : R)) * ev σ (b m)
      = ∑ k, ∑ l, cf τ k * cf τ l * ∑ m, ((b.repr (b k * b l) m : ℤ) : R) * ev σ (b m) := by
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
    _ = (∑ k, cf τ k * ev σ (b k)) * (∑ l, cf τ l * ev σ (b l)) := by
        simp only [hb, map_mul, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ m, cf τ m * ev σ (b m) := by
        rw [hev]; split_ifs <;> simp

theorem idem_ring {Λ R A : Type} [CommRing Λ] [CommRing R] [Ring A] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (b : Module.Basis (Fin n) ℤ Λ) (ev : ι → (Λ →+* R)) (cf : ι → Fin n → R)
    (hev : ∀ τ σ, ∑ k, cf τ k * ev σ (b k) = if σ = τ then 1 else 0) (hn : Fintype.card ι = n) (τ : ι)
    (s : R →+* A) (ρ : Λ →+* A) (hc : ∀ r a, s r * ρ a = ρ a * s r) :
    (∑ k, ρ (b k) * s (cf τ k)) * (∑ k, ρ (b k) * s (cf τ k)) = ∑ k, ρ (b k) * s (cf τ k) := by
  have hb : ∀ x : Λ, ρ x = ∑ m, ρ (b m) * s ((b.repr x m : ℤ) : R) := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, zsmul_eq_mul, map_mul, map_intCast]
    exact Finset.sum_congr rfl fun m _ => Int.cast_comm _ _
  calc (∑ k, ρ (b k) * s (cf τ k)) * (∑ k, ρ (b k) * s (cf τ k))
      = ∑ k, ∑ l, ∑ m, ρ (b m) * s (cf τ k * cf τ l * ((b.repr (b k * b l) m : ℤ) : R)) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        have : ρ (b k) * s (cf τ k) * (ρ (b l) * s (cf τ l)) = ρ (b k * b l) * s (cf τ k * cf τ l) := by
          rw [map_mul, map_mul, mul_assoc, ← mul_assoc (s _), hc, mul_assoc, mul_assoc]
        rw [this, hb (b k * b l), Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [mul_assoc, ← map_mul, mul_comm ((b.repr (b k * b l) m : ℤ) : R)]
    _ = ∑ m, ρ (b m) * s (∑ k, ∑ l, cf τ k * cf τ l * ((b.repr (b k * b l) m : ℤ) : R)) := by
        simp only [map_sum, Finset.mul_sum]
        symm
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by simp only [idem_coeff b ev cf hev hn τ]

theorem eA_idem : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ] {R : Type} [CommRing R] [Algebra R Γ(B.X, ⊤)] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ) (ev : ι → (Λ →+* R)) (cf : ι → Fin n → R) (hev : ∀ τ σ, ∑ k, cf τ k * ev σ (b k) = if σ = τ then 1 else 0) (hn : Fintype.card ι = n) (τ : ι) (M : AM B Λ) (hM : IsAdd M), eA M (fun k => algebraMap R Γ(B.X, ⊤) (cf τ k)) b ≫ eA M (fun k => algebraMap R Γ(B.X, ⊤) (cf τ k)) b =
      eA M (fun k => algebraMap R Γ(B.X, ⊤) (cf τ k)) b := by
  intro O _ _ _ B Λ _ R _ _ ι _ _ n b ev cf hev hn τ M hM
  let ρ : Λ →+* End M.V :=
    { M.ρ with
      map_zero' := by
        have := hM 0 0
        rw [add_zero] at this
        exact left_eq_add.1 this
      map_add' := hM }
  let s : R →+* End M.V := (smulEnd M.V).comp (algebraMap R Γ(B.X, ⊤))
  have hc : ∀ r a, s r * ρ a = ρ a * s r := fun r a =>
    (smulHom_comp (F := M.V) (G := M.V) (M.ρ a) (algebraMap R Γ(B.X, ⊤) r)).symm
  exact idem_ring b ev cf hev hn τ s ρ hc

end GlobalTheory.ChainParts
