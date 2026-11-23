import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxAd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxGen

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Loc

open Formalism.MainNotions.S.Loc PI.StrongApproxE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {p : HeightOneSpectrum (𝓞 F)} (L : LocAt F E sig p)

def latS (c : L.Fp) : AddSubgroup L.Ep where
  carrier := {x | ∃ y ∈ L.O, x = algebraMap L.Fp L.Ep c * y}
  zero_mem' := ⟨0, L.O.zero_mem, by simp⟩
  add_mem' := by
    rintro x x' ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨y + y', L.O.add_mem hy hy', by ring⟩
  neg_mem' := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨-y, L.O.neg_mem hy, by ring⟩

variable {L}

theorem mem_latS {c : L.Fp} {x : L.Ep} : x ∈ latS L c ↔ ∃ y ∈ L.O, x = algebraMap L.Fp L.Ep c * y := Iff.rfl

theorem alg_mem_O {s : L.Fp} (hs : s ∈ 𝒪[L.Fp]) : algebraMap L.Fp L.Ep s ∈ L.O := by
  refine (L.O_def _).mpr ?_
  first
  | exact isIntegral_algebraMap (x := (⟨s, hs⟩ : 𝒪[L.Fp]))
  | exact (IsScalarTower.algebraMap_apply (𝒪[L.Fp]) L.Fp L.Ep ⟨s, hs⟩) ▸ isIntegral_algebraMap

theorem latS_mul {c c' : L.Fp} {x y : L.Ep} (hx : x ∈ latS L c) (hy : y ∈ latS L c') : x * y ∈ latS L (c * c') := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a * b, L.O.mul_mem ha hb, by rw [map_mul]; ring⟩

theorem O_mul_latS {c : L.Fp} {x y : L.Ep} (hy : y ∈ L.O) (hx : x ∈ latS L c) : y * x ∈ latS L c := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨y * a, L.O.mul_mem hy ha, by ring⟩

theorem latS_mono {c c' : L.Fp} (hc' : c' ∈ 𝒪[L.Fp]) {x : L.Ep} (hx : x ∈ latS L (c * c')) : x ∈ latS L c := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨algebraMap L.Fp L.Ep c' * a, L.O.mul_mem (alg_mem_O hc') ha, by rw [map_mul]; ring⟩

theorem bounded_Fp (a : L.Fp) : ∃ s : L.Fp, s ≠ 0 ∧ s ∈ 𝒪[L.Fp] ∧ s * a ∈ 𝒪[L.Fp] := by
  by_cases ha : a ∈ 𝒪[L.Fp]
  · exact ⟨1, one_ne_zero, one_mem _, by rw [one_mul]; exact ha⟩
  · have h0 : a ≠ 0 := by
      rintro rfl
      exact ha (zero_mem _)
    refine ⟨a⁻¹, inv_ne_zero h0, ?_, by rw [inv_mul_cancel₀ h0]; exact one_mem _⟩
    rw [Valuation.mem_integer_iff] at ha ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp ha))

theorem bounded (x : L.Ep) : ∃ s : L.Fp, s ≠ 0 ∧ s ∈ 𝒪[L.Fp] ∧ algebraMap L.Fp L.Ep s * x ∈ L.O := by
  classical
  obtain ⟨n, b, hbint, hbspan⟩ := intSpan' F E
  obtain ⟨α, hα⟩ := local_span_holds F E sig p L n b hbspan x
  choose s hs0 hsO hsa using fun i => bounded_Fp (L := L) (α i)
  have hbO : ∀ i, L.ιE (b i) ∈ L.O := by
    intro i
    have := local_integral_of_substitution F E sig p L 1 (b i) (by simp) (hbint i)
    simpa using this
  refine ⟨∏ i, s i, Finset.prod_ne_zero_iff.2 fun i _ => hs0 i, Subring.prod_mem _ fun i _ => hsO i, ?_⟩
  rw [hα, Finset.mul_sum]
  refine L.O.sum_mem fun i _ => ?_
  have e : algebraMap L.Fp L.Ep (∏ j, s j) * (α i • L.ιE (b i)) =
      algebraMap L.Fp L.Ep ((∏ j ∈ Finset.univ.erase i, s j) * (s i * α i)) * L.ιE (b i) := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    ring_nf
  rw [e]
  exact L.O.mul_mem (alg_mem_O (Subring.mul_mem _ (Subring.prod_mem _ fun j _ => hsO j) (hsa i))) (hbO i)

theorem bounded_mat {n : ℕ} (B : Matrix (Fin n) (Fin n) L.Ep) :
    ∃ s : L.Fp, s ≠ 0 ∧ s ∈ 𝒪[L.Fp] ∧ ∀ i j, algebraMap L.Fp L.Ep s * B i j ∈ L.O := by
  choose s hs0 hsO hsB using fun (p : Fin n × Fin n) => bounded (B p.1 p.2)
  refine ⟨∏ p, s p, Finset.prod_ne_zero_iff.mpr fun p _ => hs0 p, prod_mem fun p _ => hsO p, ?_⟩
  intro i j
  rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ (i, j)), map_mul, mul_comm (algebraMap L.Fp L.Ep (s (i, j))), mul_assoc]
  exact L.O.mul_mem (alg_mem_O (prod_mem fun p _ => hsO p)) (hsB (i, j))

theorem entIn_mul_left {n : ℕ} {B : Matrix (Fin n) (Fin n) L.Ep} {s : L.Fp}
    (hs : ∀ i j, algebraMap L.Fp L.Ep s * B i j ∈ L.O) {c : L.Fp} {X : Matrix (Fin n) (Fin n) L.Ep}
    (hX : EntIn (latS L (s * c)) X) : EntIn (latS L c) (B * X) := by
  intro i j
  rw [Matrix.mul_apply]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  obtain ⟨y, hy, hxy⟩ := hX k j
  refine ⟨algebraMap L.Fp L.Ep s * B i k * y, L.O.mul_mem (hs i k) hy, ?_⟩
  rw [hxy, map_mul]
  ring

theorem entIn_mul_right {n : ℕ} {B : Matrix (Fin n) (Fin n) L.Ep} {s : L.Fp}
    (hs : ∀ i j, algebraMap L.Fp L.Ep s * B i j ∈ L.O) {c : L.Fp} {X : Matrix (Fin n) (Fin n) L.Ep}
    (hX : EntIn (latS L (s * c)) X) : EntIn (latS L c) (X * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  obtain ⟨y, hy, hxy⟩ := hX i k
  refine ⟨algebraMap L.Fp L.Ep s * B k j * y, L.O.mul_mem (hs k j) hy, ?_⟩
  rw [hxy, map_mul]
  ring

theorem latS_mul_self {c : L.Fp} (hc : c ∈ 𝒪[L.Fp]) {x y : L.Ep} (hx : x ∈ latS L c) (hy : y ∈ latS L c) :
    x * y ∈ latS L c := latS_mono hc (latS_mul hx hy)

end Loc

end Formalism.L2.SG.Pf.ProdEApprox
