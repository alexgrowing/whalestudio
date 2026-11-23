import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemIffForallMemLocalizeRingOfIntegers

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.LocalLattice

noncomputable section

namespace GlobalTheory.SemiLocalFrame

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem algebraMapSubmonoid_le :
    Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl ≤ (𝓞 E)⁰ :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ v.asIdeal.primeCompl_le_nonZeroDivisors

def semiLoc : Subalgebra (𝓞 E) E :=
  Localization.subalgebra.ofField E (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl)
    (algebraMapSubmonoid_le E v)

instance isLocalization_semiLoc :
    IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl) (semiLoc E v) :=
  Localization.subalgebra.isLocalization_ofField E _ _

instance isFractionRing_semiLoc : IsFractionRing (semiLoc E v) E :=
  Localization.subalgebra.isFractionRing_ofField E _ _

instance isPrincipalIdealRing_semiLoc : IsPrincipalIdealRing (semiLoc E v) :=
  haveI : IsDedekindDomain (semiLoc E v) :=
    IsLocalization.isDedekindDomain (𝓞 E) (algebraMapSubmonoid_le E v) _
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 E) v.asIdeal v.ne_bot

variable {E}

theorem mem_span_semiLoc_iff {V : Type*} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (N : Submodule (𝓞 E) V) (x : V) :
    x ∈ Submodule.span (semiLoc E v) (N : Set V) ↔
      ∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • x ∈ N := by
  rw [mem_span_localization_iff (semiLoc E v)
    (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl)]
  exact ⟨fun ⟨_, ⟨s, hs, rfl⟩, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨_, ⟨s, hs, rfl⟩, h⟩⟩

theorem exists_of_mem_semiLoc {z : E} (hz : z ∈ semiLoc E v) :
    ∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • z ∈ (1 : Submodule (𝓞 E) E) := by
  have h := mem_span_semiLoc_iff v (1 : Submodule (𝓞 E) E) z
  rw [Submodule.one_eq_span, Submodule.span_span_of_tower, Submodule.mem_span_singleton,
    ← Submodule.one_eq_span] at h
  exact h.1 ⟨⟨z, hz⟩, mul_one z⟩

theorem exists_common {ι : Type*} [Finite ι] {V : Type*} [AddCommGroup V] [Module (𝓞 E) V]
    (N : Submodule (𝓞 E) V) (x : ι → V)
    (h : ∀ i, ∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • x i ∈ N) :
    ∃ s ∉ v.asIdeal, ∀ i, algebraMap (𝓞 F) (𝓞 E) s • x i ∈ N := by
  classical
  haveI := Fintype.ofFinite ι
  choose s hs h using h
  refine ⟨∏ i, s i, (prod_mem (S := v.asIdeal.primeCompl) fun i _ => hs i), fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, mul_smul]
  exact N.smul_mem _ (h i)

theorem exists_frame {k : ℕ} (L : Submodule (𝓞 E) (Fin k → E)) (h1 : L.FG)
    (h2 : Submodule.span E (L : Set (Fin k → E)) = ⊤) :
    ∃ g : GL (Fin k) E, ∀ x, (∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • x ∈ L) ↔
      ∀ i, (((g⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i ∈ semiLoc E v := by
  haveI : Submodule.IsLattice E (Submodule.span (semiLoc E v) (L : Set (Fin k → E))) := by
    constructor
    · obtain ⟨s, rfl⟩ := h1
      exact ⟨s, (Submodule.span_span_of_tower (𝓞 E) _ _).symm⟩
    · rw [Submodule.span_span_of_tower, h2]
  obtain ⟨g, hg⟩ := exists_eq_frameLattice (Submodule.span (semiLoc E v) (L : Set (Fin k → E)))
  refine ⟨g, fun x => ?_⟩
  rw [← mem_span_semiLoc_iff, hg, mem_frameLattice_iff_inv]
  exact forall_congr' fun i =>
    Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

theorem smul_eq (c : 𝓞 F) (z : E) :
    algebraMap (𝓞 F) (𝓞 E) c • z = algebraMap F E (c : F) * z := by
  rw [Algebra.smul_def]; rfl

theorem exists_frame_denominator (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (Fin k → E)) = ⊤) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (B : GL (Fin k) E) (c : 𝓞 F), c ∉ v.asIdeal ∧
      (∀ x ∈ Λ, ∀ i, algebraMap F E (c : F) *
        (((B⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i ∈
          (algebraMap (𝓞 E) E).range) ∧
      ∀ j, (fun i => algebraMap F E (c : F) * (B : Matrix (Fin k) (Fin k) E) i j) ∈ Λ := by
  have hfg : Λ.FG := Module.Finite.iff_fg.1 hfin
  obtain ⟨g, hg⟩ := exists_frame v Λ hfg hspan
  obtain ⟨S, hS⟩ := hfg
  have hone : (1 : 𝓞 F) ∉ v.asIdeal := (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top
  obtain ⟨a, ha, hA⟩ := exists_common v (ι := S × Fin k) (1 : Submodule (𝓞 E) E)
    (fun p => (((g⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ (p.1 : Fin k → E)) p.2)
    (fun p => exists_of_mem_semiLoc v ((hg _).1 ⟨1, hone, by
      rw [map_one, one_smul, ← hS]; exact Submodule.subset_span p.1.2⟩ p.2))
  obtain ⟨b, hb, hB⟩ := exists_common v Λ
    (fun j : Fin k => fun i => (g : Matrix (Fin k) (Fin k) E) i j) (fun j => by
      refine (hg _).2 fun i => ?_
      have : (((g⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ
          (fun k => (g : Matrix _ _ E) k j)) i = (1 : Matrix (Fin k) (Fin k) E) i j := by
        rw [← Units.inv_mul g]; rfl
      rw [this, Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _])
  refine ⟨g, b * a, fun h => (v.isPrime.mem_or_mem h).elim hb ha, fun x hx i => ?_, fun j => ?_⟩
  · have key : algebraMap (𝓞 F) (𝓞 E) a •
        (((g⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i ∈ (1 : Submodule (𝓞 E) E) := by
      rw [← hS] at hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact hA (⟨y, hy⟩, i)
      | zero => simp
      | add y z _ _ hy hz => rw [Matrix.mulVec_add, Pi.add_apply, smul_add]; exact add_mem hy hz
      | smul r y _ hy =>
        rw [Matrix.mulVec_smul, Pi.smul_apply, smul_comm]; exact Submodule.smul_mem _ _ hy
    have := Submodule.smul_mem _ (algebraMap (𝓞 F) (𝓞 E) b) key
    rw [← mul_smul, ← map_mul, smul_eq] at this
    exact Submodule.mem_one.1 this
  · have := Λ.smul_mem (algebraMap (𝓞 F) (𝓞 E) a) (hB j)
    rw [← mul_smul, ← map_mul, mul_comm a b] at this
    convert this using 1
    funext i
    rw [Pi.smul_apply, smul_eq]

end GlobalTheory.SemiLocalFrame
