import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.LocalToGlobal.HermitianForms.TiedStep

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
open Formalism.UG.P

namespace GlobalTheory.St.G.IntAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem levelafC_natCast (m : ℕ) : levelafC (F := F) E (m : 𝓞 F) = (m : E ⊗[F] Ad F) := by
  induction m with
  | zero => simp only [levelafC, Nat.cast_zero, map_zero, TensorProduct.tmul_zero]
  | succ k ih =>
    simp only [levelafC] at ih ⊢
    rw [Nat.cast_succ, Nat.cast_succ, map_add, map_one, TensorProduct.tmul_add, ih,
      Algebra.TensorProduct.one_def]

private theorem sum_afsplitI_one_apply_of_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∈ S) : (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w = 1 := by
  rw [show (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w =
      ∑ v ∈ S, (afsplitI v (1 : v.adicCompletion F)) w from map_sum (evalV F w) _ S]
  rw [Finset.sum_eq_single_of_mem w hw (fun v _ hv => afsplitI_ne v w (Ne.symm hv) 1),
    afsplitI_self]

private theorem sum_afsplitI_one_apply_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∉ S) : (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w = 0 := by
  rw [show (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w =
      ∑ v ∈ S, (afsplitI v (1 : v.adicCompletion F)) w from map_sum (evalV F w) _ S]
  exact Finset.sum_eq_zero (fun v hv => afsplitI_ne v w (fun h => hw (by rw [h]; exact hv)) 1)

theorem mem_of_local (a : E ⊗[F] Ad F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), prV (E := E) v a ∈ intV E v) : a ∈ OAd F E := by
  classical
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (E := E) a
  have hfin := levelaf_finite_places (F := F) d hd0
  set S := hfin.toFinset with hS
  set dF : F := algebraMap (𝓞 F) F d with hdF
  have hdF0 : dF ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  set s : Ad F := ∑ v ∈ S, afsplitI v (1 : v.adicCompletion F) with hs
  set u : Ad F := (1 - s) * algebraMap F (Ad F) dF⁻¹ with hu
  have hu_int : u ∈ intAd F := by
    show ∀ w : HeightOneSpectrum (𝓞 F), u w ∈ w.adicCompletionIntegers F
    intro w
    have hcomp : u w = (1 - s w) * (dF⁻¹ • (1 : w.adicCompletion F)) := by
      rw [hu, afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply,
        Algebra.algebraMap_eq_smul_one, afsplit_smul_apply, afsplit_one_apply]
    by_cases hw : w ∈ S
    · rw [hcomp, hs, sum_afsplitI_one_apply_of_mem S w hw, sub_self, zero_mul]
      exact zero_mem _
    · rw [hcomp, hs, sum_afsplitI_one_apply_of_not_mem S w hw, sub_zero, one_mul, Algebra.smul_def, mul_one, map_inv₀,
        HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
      have h1 := levelaf_int_mem_v w d
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
      have h2 : ¬ Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) d) < 1 :=
        fun hlt => hw (hfin.mem_toFinset.mpr hlt)
      have h3 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) d) = 1 :=
        le_antisymm h1 (not_lt.mp h2)
      rw [hdF, ← IsScalarTower.algebraMap_apply, h3, inv_one]
  have he : ∑ v ∈ S, afsplitEps E v = (1 : E) ⊗ₜ[F] s := by
    rw [hs, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  have h1 : (1 : E ⊗[F] Ad F) - ∑ v ∈ S, afsplitEps E v = ((1 : E) ⊗ₜ[F] u) * levelafC E d := by
    rw [he, levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hu, mul_assoc,
      IsScalarTower.algebraMap_apply (𝓞 F) F (Ad F) d, ← hdF, ← map_mul, inv_mul_cancel₀ hdF0,
      map_one, mul_one, TensorProduct.tmul_sub, ← Algebra.TensorProduct.one_def]
  have hsplit : a = (∑ v ∈ S, afsplitEps E v) * a + ((1 : E) ⊗ₜ[F] u) * (levelafC E d * a) := by
    rw [← mul_assoc, ← h1]
    ring
  rw [hsplit]
  refine add_mem ?_ (mul_mem ?_ hd)
  · rw [Finset.sum_mul]
    refine sum_mem (fun v _ => ?_)
    rw [← afsplit_decomp]
    exact afsplit_IE_int v _ (h v)
  · have hmem := levelaf_tmul_mem (E := E) (1 : 𝓞 E) hu_int
    rwa [map_one] at hmem

theorem expand_trace {ι : Type} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F E)
    (a : E ⊗[F] Ad F) :
    a = ∑ i, ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i) ⊗ₜ[F]
      adelstabT F E (inclE (F := F) (Ad F) (β i) * a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero, TensorProduct.tmul_zero, Finset.sum_const_zero]
  | tmul e y =>
    have hT : ∀ i, adelstabT F E (inclE (F := F) (Ad F) (β i) * (e ⊗ₜ[F] y)) =
        Algebra.trace F E (e * β i) • y := by
      intro i
      rw [inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, adelstabT_tmul, Algebra.smul_def, mul_comm (β i) e]
    simp_rw [hT, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
    congr 1
    conv_lhs => rw [← ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β).sum_repr e]
    simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_add, map_add, TensorProduct.tmul_add]

private theorem adelstabT_inclE_of_forall_divisible (a : E ⊗[F] Ad F)
    (h : ∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) (e : E) :
    adelstabT F E (inclE (F := F) (Ad F) e * a) = 0 := by
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (E := E) (inclE (F := F) (Ad F) e)
  have hxS : inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) ∈ OAd F E := by
    rw [map_mul, adelstab_incl_C]
    exact hd
  have hzero : adelstabT F E (inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) * a) = 0 := by
    refine GlobalTheory.IntegralFinAdele.eq_zero_of_forall_mul F _ (fun M hM => ?_)
    obtain ⟨t, ht, hat⟩ := h M hM
    refine ⟨adelstabT F E (inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) * t),
      adelstabT_mem (mul_mem hxS ht), ?_⟩
    rw [hat, mul_left_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  have hdF0 : algebraMap (𝓞 F) F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  have hxe : inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) * a =
      algebraMap (𝓞 F) F d • (inclE (F := F) (Ad F) e * a) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F E d, ← Algebra.smul_def, inclE,
      Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
      ← TensorProduct.smul_tmul', smul_mul_assoc]
  rw [hxe, map_smul] at hzero
  calc adelstabT F E (inclE (F := F) (Ad F) e * a)
      = (algebraMap (𝓞 F) F d)⁻¹ • algebraMap (𝓞 F) F d • adelstabT F E (inclE (F := F) (Ad F) e * a) :=
        (inv_smul_smul₀ hdF0 _).symm
    _ = 0 := by rw [hzero, smul_zero]

theorem eq_zero_of_multiples (a : E ⊗[F] Ad F)
    (h : ∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) : a = 0 := by
  classical
  rw [expand_trace (Module.Free.chooseBasis F E) a]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [adelstabT_inclE_of_forall_divisible a h, TensorProduct.tmul_zero]

theorem exists_nat_denom (a : E ⊗[F] Ad F) :
    ∃ m : ℕ, 0 < m ∧ (m : E ⊗[F] Ad F) * a ∈ OAd F E := by
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (E := E) a
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd0
  · rw [← levelafC_natCast, hq, levelafC_mul, mul_comm (levelafC E d), mul_assoc]
    exact mul_mem (levelafC_mem q) hd

theorem integral_adeles_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ a : E ⊗[F] Ad F, a ∈ OAd F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), prV (E := E) v a ∈ intV E v) ∧ (∀ a ∈ OAd F E, ∀ m : ℕ, 0 < m → ∃ x : 𝓞 E, ∃ t ∈ OAd F E, a = inclE (F := F) (Ad F) (x : E) + (m : E ⊗[F] Ad F) * t) ∧ (∀ a : E ⊗[F] Ad F, (∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) → a = 0) ∧ (∀ a : E ⊗[F] Ad F, ∃ m : ℕ, 0 < m ∧ (m : E ⊗[F] Ad F) * a ∈ OAd F E) ∧ (∀ x : E, inclE (F := F) (Ad F) x ∈ OAd F E ↔ x ∈ intOE E) := by
  intro F E _ _ _ _ _
  refine ⟨fun a => ⟨fun ha v => afsplit_prV_int v a ha, mem_of_local a⟩, ?_,
    fun a => eq_zero_of_multiples a, exists_nat_denom, fun x => ⟨?_, ?_⟩⟩
  · intro a ha m hm
    have hm' : (m : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    obtain ⟨b, t, ht, hab⟩ := csGlob_approx (E := E) csGlob_intAdApprox (m : 𝓞 F) hm' a ha
    refine ⟨b, t, ht, ?_⟩
    rw [hab, levelafC_natCast]
    try rfl
  · intro hx
    exact ⟨⟨x, csGlob_int x hx⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact adelstab_incl_int b

end GlobalTheory.St.G.IntAd
