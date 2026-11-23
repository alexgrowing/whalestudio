import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDlogUniqueModuloP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
open scoped TensorProduct NNReal

namespace GlobalTheory.HalfGeo.PowFam

attribute [local instance] Over.cartesianMonoidalCategory

theorem dual_pow {R : Type} [CommRing R] (u : DualNumber R) (hu : u.fst = 1) (k : ℕ) :
    (u ^ k).fst = 1 ∧ (u ^ k).snd = (k : R) * u.snd := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    refine ⟨by rw [TrivSqZeroExt.fst_mul, ih.1, hu, _root_.mul_one], ?_⟩
    rw [TrivSqZeroExt.snd_mul, ih.1, ih.2, hu]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Nat.cast_succ]
    ring

theorem dual_prod {R J : Type} [CommRing R] (s : Finset J) (f : J → DualNumber R) (hf : ∀ i, (f i).fst = 1) :
    (∏ i ∈ s, f i).fst = 1 ∧ (∏ i ∈ s, f i).snd = ∑ i ∈ s, (f i).snd := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    refine ⟨by rw [TrivSqZeroExt.fst_mul, ih.1, hf, _root_.mul_one], ?_⟩
    rw [TrivSqZeroExt.snd_mul, ih.1, ih.2, hf]
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, _root_.one_mul, _root_.mul_one]
    ring

section Chars

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {O : Type} [CommRing O] {x : Sp O ⟶ X} {q : ℕ}

theorem chi_one (c : TorsChar t x q) (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] :
    c.χ B (1 : Over.mk (spMap (algebraMap O B) ≫ x) ⟶ t.G) = 1 := by
  have h := c.mul B 1 1 (one_pow _) (one_pow _)
  rw [_root_.one_mul] at h
  exact left_eq_mul.1 h

theorem chi_pow (c : TorsChar t x q) (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
    (w : Over.mk (spMap (algebraMap O B) ≫ x) ⟶ t.G) (hw : w ^ q = 1) (k : ℕ) : c.χ B (w ^ k) = c.χ B w ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, chi_one]
  | succ k ih =>
    rw [pow_succ, pow_succ, c.mul B _ _ (by rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]) hw, ih]

theorem chi_pow_q (c : TorsChar t x q) (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
    (w : Over.mk (spMap (algebraMap O B) ≫ x) ⟶ t.G) (hw : w ^ q = 1) : c.χ B w ^ q = 1 := by
  rw [← chi_pow c B w hw, hw, chi_one]

def prodChar {N : ℕ} (c : Fin N → TorsChar t x q) (n : Fin N → ℕ) : TorsChar t x q where
  χ B _ _ _ w := ∏ m, (c m).χ B w ^ n m
  mul B _ _ _ g g' hg hg' := by
    simp only [(c _).mul B g g' hg hg', mul_pow, Finset.prod_mul_distrib]
  nat B B' _ _ _ _ _ _ φ g g' hg hg' := by
    simp only [Units.coe_prod, Units.val_pow_eq_pow_val, map_prod, map_pow]
    exact Finset.prod_congr rfl fun m _ => by rw [(c m).nat B B' φ g g' hg hg']

theorem prodChar_val {N : ℕ} (c : Fin N → TorsChar t x q) (n : Fin N → ℕ) (B : Type) [CommRing B] [Algebra O B]
    [Module.Finite O B] (w : Over.mk (spMap (algebraMap O B) ≫ x) ⟶ t.G) :
    ((prodChar c n).χ B w : B) = ∏ m, ((c m).χ B w : B) ^ n m := by
  simp only [prodChar, Units.coe_prod, Units.val_pow_eq_pow_val]

end Chars

end GlobalTheory.HalfGeo.PowFam

open GlobalTheory.HalfGeo.PowFam in

theorem GlobalTheory.HalfGeo.fullSt : FullSt := by
  intro E _ _ _ H X t p hp x N c hc
  classical
  have hq1 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.out.one_lt
  let eqv := Fintype.equivFin (Fin N → Fin (p ^ 2))
  refine ⟨Fintype.card (Fin N → Fin (p ^ 2)), fun j => prodChar c (fun m => (eqv.symm j m : ℕ)),
    fun j m => (eqv.symm j m : ℕ), fun m => eqv (Pi.single m ⟨1, hq1⟩), ?_, ?_, ?_⟩
  · intro c₀
    obtain ⟨n, hn⟩ := hc c₀
    refine ⟨eqv (fun m => ⟨n m % p ^ 2, Nat.mod_lt _ (by omega)⟩), ?_⟩
    intro B _ _ _ w hw
    rw [hn B w hw]
    show _ = ∏ m, (c m).χ B w ^ ((eqv.symm (eqv _) m : Fin (p ^ 2)) : ℕ)
    simp only [Equiv.symm_apply_apply]
    refine Finset.prod_congr rfl fun m _ => ?_
    conv_lhs => rw [← Nat.mod_add_div (n m) (p ^ 2), pow_add, pow_mul, chi_pow_q (c m) B w hw, one_pow,
      _root_.mul_one]
  · intro m
    funext m'
    simp only [Equiv.symm_apply_apply]
    by_cases h : m' = m
    · subst h; simp
    · simp [h]
  · intro g e h he hdl j a v hav w hw
    have hv := GlobalTheory.ShFam.Pad.Guard.comb_tan he hav
    have hqR : ((p ^ 2 : ℕ) : ↥(intO ℂ_[p]) ⧸ Ideal.span {(p : ↥(intO ℂ_[p])) ^ 2}) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : ↥(intO ℂ_[p])) ^ 2})), Ideal.Quotient.eq_zero_iff_mem,
        Nat.cast_pow]
      exact Ideal.mem_span_singleton_self _
    have hw' : w = GlobalTheory.DlogEx.red _ (GlobalTheory.LieMet.tanOf hv) :=
      Over.OverMorphism.ext (by rw [hw, GlobalTheory.DlogEx.red_left, GlobalTheory.LieMet.left_tanOf])
    have hf : ∀ m, ((c m).χ _ w : DualNumber (↥(intO ℂ_[p]) ⧸ Ideal.span {(p : ↥(intO ℂ_[p])) ^ 2})).fst = 1 := fun m => by
      rw [hw']; exact GlobalTheory.DlogEx.chi_fst _ hqR (c m) _
    rw [prodChar_val]
    rw [(dual_prod _ _ fun m => (dual_pow _ (hf m) _).1).2]
    simp only [map_sum, map_mul, map_natCast, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [(dual_pow _ (hf m) _).2, hdl m a v hav w hw, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring
