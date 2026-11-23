import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import GroundTheory.AutomorphicForms.GLnLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCommutantMulIntegralConjugate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open ValuativeRel GroundTheory.Automorphic.GLnLocal
open scoped Pointwise

noncomputable section
namespace GlobalTheory.StabInt

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem mem_O_iff (x : w.adicCompletion E) : x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ w.adicCompletionIntegers E := by
  show _ ↔ Valued.v x ≤ 1
  simp only [Valuation.mem_integer_iff]
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h1 := (Valuation.Compatible.vle_iff_le (v := Valued.v) x 1)
  rw [map_one] at h1
  rw [← h1]
  exact Iff.symm (Valuation.vle_one_iff (valuation (w.adicCompletion E)))

theorem mem_integralGL_of_mem_KGL {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL w n) :
    g ∈ integralGL (w.adicCompletion E) n := by
  obtain ⟨u, rfl⟩ := hg
  rw [mem_integralGL_iff]
  refine ⟨fun i j => (mem_O_iff _).2 (u i j).2, fun i j => (mem_O_iff _).2 ?_⟩
  rw [← map_inv]
  exact ((u⁻¹ : GL (Fin n) (Ov E w)) i j).2

theorem mem_KGL_of_mem_integralGL {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ integralGL (w.adicCompletion E) n) :
    g ∈ GlobalTheory.LFun.KGL w n := by
  rw [mem_integralGL_iff] at hg
  have h1 : ∀ i j, g.1 i j ∈ Ov E w := fun i j => (mem_O_iff _).1 (hg.1 i j)
  have h2 : ∀ i j, g⁻¹.1 i j ∈ Ov E w := fun i j => (mem_O_iff _).1 (hg.2 i j)
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem mem_integralGL_of_conj (N t g : GL (Fin n) (w.adicCompletion E))
    (hN : N ∈ integralGL (w.adicCompletion E) n)
    (hsep : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1)
    (htN : t * N = N * t) (ht' : g⁻¹ * t * g ∈ integralGL (w.adicCompletion E) n)
    (hN' : g⁻¹ * N * g ∈ integralGL (w.adicCompletion E) n) : t ∈ integralGL (w.adicCompletion E) n := by
  set F := w.adicCompletion E
  letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField _ _
  haveI : IsUltrametricDist F :=
    inferInstanceAs (@IsUltrametricDist F (Valued.toNormedField F (WithZero (Multiplicative ℤ))).toDist)
  have hO : ∀ x : F, ‖x‖ ≤ 1 ↔ x ∈ 𝒪[F] := fun x =>
    (Valued.toNormedField.norm_le_one_iff).trans (mem_O_iff x).symm
  have hs : N.val.charpoly.Separable := by
    obtain ⟨u, v, -, -, h⟩ := hsep
    exact ⟨u, v, h⟩
  have hsep' : ∃ u v : Polynomial F, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.val.charpoly + v * Polynomial.derivative N.val.charpoly = 1 := by
    obtain ⟨u, v, hu, hv, h⟩ := hsep
    exact ⟨u, v, fun i => (hO _).2 ((mem_O_iff _).2 (hu i)), fun i => (hO _).2 ((mem_O_iff _).2 (hv i)), h⟩
  have hNi : ∀ i j, ‖N.val i j‖ ≤ 1 := fun i j => (hO _).2 ((mem_integralGL_iff F n).1 hN |>.1 i j)
  have hN'i : ∀ i j, ‖((g.val)⁻¹ * N.val * g.val) i j‖ ≤ 1 := by
    intro i j
    have := ((mem_integralGL_iff F n).1 hN').1 i j
    rw [← Matrix.coe_units_inv]
    exact (hO _).2 this
  obtain ⟨c, hcu, hcN, hy, hdet⟩ := GlobalTheory.IntConj.exists_commuting_mul_integral F n N.val g.val hNi hsep' g.isUnit hN'i
  set cU := hcu.unit with hcU
  have hcUv : (cU : Matrix (Fin n) (Fin n) F) = c := rfl
  have hcadj : c ∈ Algebra.adjoin F {N.val} := GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N.val c hs hcN
  have htNv : Commute t.val N.val := by
    show t.val * N.val = N.val * t.val
    have := congrArg Units.val htN
    simpa [Units.val_mul] using this
  have htc : Commute t.val c := Algebra.commute_of_mem_adjoin_singleton_of_commute hcadj htNv
  have htcU : t * cU = cU * t := Units.ext (by simpa [Units.val_mul, hcUv] using htc.eq)
  set yU := cU⁻¹ * g with hyU
  have hyv : (yU : Matrix (Fin n) (Fin n) F) = c⁻¹ * g.val := by
    rw [hyU, Units.val_mul, Matrix.coe_units_inv, hcUv]
  have hyO : yU ∈ integralGL F n := by
    rw [mem_integralGL_iff]
    have h1 : ∀ i j, (yU : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := fun i j => by
      rw [hyv]; exact (hO _).1 (hy i j)
    refine ⟨h1, fun i j => ?_⟩
    let y₀ : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨_, h1 i j⟩
    have hy₀ : (RingHom.mapMatrix (𝒪[F]).subtype) y₀ = (yU : Matrix (Fin n) (Fin n) F) := rfl
    have hadj : ∀ i j, (yU : Matrix (Fin n) (Fin n) F).adjugate i j ∈ 𝒪[F] := fun i j => by
      rw [← hy₀, ← RingHom.map_adjugate]
      exact (y₀.adjugate i j).2
    have hd : ‖Ring.inverse (yU : Matrix (Fin n) (Fin n) F).det‖ ≤ 1 := by
      rw [Ring.inverse_eq_inv', norm_inv, hyv, hdet, inv_one]
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    exact Subring.mul_mem _ ((hO _).1 hd) (hadj i j)
  have e : t = yU * (g⁻¹ * t * g) * yU⁻¹ := by
    have e1 : cU⁻¹ * t * cU = t := by
      rw [mul_assoc, htcU, ← mul_assoc, inv_mul_cancel, one_mul]
    calc t = cU⁻¹ * t * cU := e1.symm
      _ = (cU⁻¹ * g) * (g⁻¹ * t * g) * (cU⁻¹ * g)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyO ht') (Subgroup.inv_mem _ hyO)

def pairGrp {G : Type} [Group G] (t N : G) (h : Commute t N) : Subgroup G where
  carrier := {x | ∃ a b : ℤ, x = t ^ a * N ^ b}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a + c, b + d, ?_⟩
    rw [_root_.zpow_add, _root_.zpow_add, mul_assoc, mul_assoc, ← mul_assoc (N ^ b), (h.zpow_zpow c b).eq.symm, mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    rw [_root_.mul_inv_rev, _root_.zpow_neg, _root_.zpow_neg]
    exact (h.zpow_zpow a b).inv_inv.eq.symm

theorem mem_KGL_of_commute : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N t : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w n →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    t * N = N * t → IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) (w.adicCompletion E)))) →
    t ∈ GlobalTheory.LFun.KGL w n := by
  intro E _ _ n w N t hN hsep htN htc
  set F := w.adicCompletion E
  have hNO : N ∈ integralGL F n := mem_integralGL_of_mem_KGL hN
  let H0 := pairGrp t N htN
  have hC : IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) F)) * (integralGL F n : Set (GL (Fin n) F))) :=
    htc.mul (isCompact_integralGL F n)
  have hsub : (H0 : Set (GL (Fin n) F)) ⊆
      closure (Subgroup.zpowers t : Set (GL (Fin n) F)) * (integralGL F n : Set (GL (Fin n) F)) := by
    rintro _ ⟨a, b, rfl⟩
    exact Set.mul_mem_mul (subset_closure (Subgroup.zpow_mem_zpowers t a)) (Subgroup.zpow_mem _ hNO b)
  have hH : IsCompact (H0.topologicalClosure : Set (GL (Fin n) F)) := by
    rw [Subgroup.topologicalClosure_coe]
    exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)
  obtain ⟨g, hg⟩ := exists_conj_le_integralGL F n hH
  have ht' := hg t (H0.le_topologicalClosure ⟨1, 0, by simp⟩)
  have hN' := hg N (H0.le_topologicalClosure ⟨0, 1, by simp⟩)
  exact mem_KGL_of_mem_integralGL (mem_integralGL_of_conj N t g hNO hsep htN ht' hN')

end GlobalTheory.StabInt
