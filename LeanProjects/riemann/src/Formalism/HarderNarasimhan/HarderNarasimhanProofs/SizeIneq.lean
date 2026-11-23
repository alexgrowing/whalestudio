import Formalism.HarderNarasimhan.StatementPl
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Lemmata.GeneralBFactSecondTail.Imports

open Module NumberField

noncomputable section

namespace Formalism.HN

section SlopeTestRemainingChoices

variable {K : Type*} [Field K] [NumberField K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {W : Type*} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem sizeIneq_exists_mul_mem (A : Submodule (𝓞 K) V) (x : V)
    (hx : x ∈ Submodule.span K (A : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ A := by
  first | exact Bl.general_b_fact_second''''''.goal1 .. | (apply Bl.general_b_fact_second''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''''''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second''''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''''''.goal1 <;> first | assumption | infer_instance)

theorem sizeIneq_span_inf_ker (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) :
    Submodule.span K ((A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K (A : Set V) ⊓ LinearMap.ker φ := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨hxA, hxk⟩
    exact ⟨Submodule.subset_span hxA, hxk⟩
  · rintro x ⟨hxS, hxk⟩
    obtain ⟨d, hd, hdx⟩ := sizeIneq_exists_mul_mem A x hxS
    have hd' : algebraMap (𝓞 K) K d ≠ 0 := by
      intro h0
      exact hd (FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero]))
    have hmem : d • x ∈ (A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) := by
      refine ⟨hdx, ?_⟩
      show φ (d • x) = 0
      rw [← algebraMap_smul K d x, map_smul, LinearMap.mem_ker.mp hxk, smul_zero]
    have hx : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem sizeIneq_rk [FiniteDimensional K V] (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) :
    rkK (A.map (φ.restrictScalars (𝓞 K))) + rkK (A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) =
      rkK A := by
  unfold rkK
  set S := Submodule.span K (A : Set V) with hS
  have h1 : Submodule.span K ((A.map (φ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) W) : Set W) =
      S.map φ := by
    rw [Submodule.map_coe, hS, Submodule.map_span]
    rfl
  rw [h1, sizeIneq_span_inf_ker]
  have := (φ.domRestrict S).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at this
  rw [← this, ← Submodule.map_comap_subtype S (LinearMap.ker φ)]
  congr 1
  exact (Submodule.equivMapOfInjective _ S.injective_subtype _).finrank_eq.symm

end SlopeTestRemainingChoices

theorem sizeIneq_of (h1 : SizeMu) (h2 : HtImage) (h3 : PlLat) : SizeIneq := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B hAfg hBfg hIB hI0
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hrkeq := sizeIneq_rk φ A
  set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef
  set A₀ := A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) with hA₀def
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'
  have hIfg : I.FG := hAfg.map _
  have hA0 : A ≠ ⊥ := by
    intro h
    apply hI0
    rw [hIdef, h, Submodule.map_bot]
  have hB0 : B ≠ ⊥ := fun h => hI0 (le_bot_iff.mp (h ▸ hIB))
  obtain ⟨hAlat, -, -⟩ := h3 K V ι b X hX A hAfg
  obtain ⟨hBlat, -, -⟩ := h3 K W κ b' X' hX' B hBfg
  obtain ⟨-, hrkI, hhtI⟩ := h3 K W κ b' X' hX' I hIfg
  obtain ⟨hsat, hht⟩ := h2 K V ι W κ b X b' X' hX hX' φ A hAfg
  have hSA := h1 K V ι b X hX A hAfg hA0
  have hSB := h1 K W κ b' X' hX' B hBfg hB0
  obtain ⟨-, -, hsQ, -, hlarge, -⟩ := hSA
  obtain ⟨-, -, -, hleast, -, -⟩ := hSB
  have hSI := (h1 K W κ b' X' hX' I hIfg hI0).1

  have hA₀ne : A₀ ≠ A := by
    intro h
    apply hI0
    rw [eq_bot_iff]
    rintro y ⟨x, hx, rfl⟩
    have hx0 : x ∈ A₀ := h ▸ hx
    exact (Submodule.mem_bot _).2 (LinearMap.mem_ker.1 hx0.2)

  have hSBB := saturation_basic_properties (𝓞 K) W _ ρ' B hBlat
  have hrkIpos : 0 < rk ρ' I := by
    rcases Nat.eq_zero_or_pos (rk ρ' I) with h | h
    · exact absurd ((hSBB.2.2.2.1 I hIB).1 h) hI0
    · exact h
  have hMB := slope_characterization (𝓞 K) W _ ρ' B hBlat hB0
  have hdegI := (hMB.1 (muMax ρ' B)).1 le_rfl I hIB
  have hslI : slope ρ' I ≤ muMax ρ' B := by
    show Formalism.F.deg (zl ρ' I) / (Formalism.F.rk (zl ρ' I) : ℝ) ≤ _
    rw [div_le_iff₀ (by exact_mod_cast hrkIpos)]
    exact hdegI
  have hleI : leastSize b' X' B ≤ size b' X' I := by
    rw [hleast, hSI]
    exact Real.exp_le_exp.2 (by linarith)

  have hSBA := saturation_basic_properties (𝓞 K) V _ ρ A hAlat
  have hq := hSBA.2.2.2.2.2.2.2 A₀ hsat
  have hlt : rk ρ A₀ < rk ρ A := by
    refine lt_of_le_of_ne hq.2.1 (fun h => hA₀ne ?_)
    exact (hSBA.2.2.1 A₀ A hsat hsat.1 le_rfl h.symm).symm
  have hMA := slope_characterization (𝓞 K) V _ ρ A hAlat hA0
  have hmin := (hMA.2.1 (muMin ρ A)).1 le_rfl A₀ hsat.1
  have hslQ : muMin ρ A ≤ Formalism.F.slope (Formalism.F.quot (zl ρ A) (zl ρ A₀)) := by
    have hr : (Formalism.F.rk (Formalism.F.quot (zl ρ A) (zl ρ A₀)) : ℝ) = (rk ρ A : ℝ) - rk ρ A₀ := by
      rw [hq.1, Nat.cast_sub hq.2.1]
    have hrpos : (0 : ℝ) < (rk ρ A : ℝ) - rk ρ A₀ := by
      have : (rk ρ A₀ : ℝ) < rk ρ A := by exact_mod_cast hlt
      linarith
    unfold Formalism.F.slope
    rw [hr, le_div_iff₀ hrpos, hq.2.2]
    exact hmin
  have hQle : sizeQ b X A A₀ ≤ largestSize b X A := by
    rw [hlarge, hsQ A₀ hsat hA₀ne]
    exact Real.exp_le_exp.2 (by linarith)
  have hlargepos : 0 < largestSize b X A := by rw [hlarge]; exact Real.exp_pos _

  set P := ∏ v, opNormAt b X b' X' v φ with hPdef
  have hP : 0 ≤ P := Finset.prod_nonneg (fun v _ => norm_nonneg _)
  have hf : (0 : ℝ) < nPl K := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hs : (0 : ℝ) < rkK I := by
    have : rkK I ≠ 0 := by
      intro h
      rw [hrkI, h, mul_zero] at hrkIpos
      exact lt_irrefl _ hrkIpos
    exact_mod_cast Nat.pos_of_ne_zero this
  have hrkR : ((rkK A : ℝ) - rkK A₀) = rkK I := by
    rw [← hrkeq]; push_cast; ring
  rw [Finset.prod_pow] at hht
  have hX0 : 0 ≤ P ^ (2 * rkK I) := pow_nonneg hP _
  have hQpos : 0 < htQ b X A A₀ := pos_of_mul_pos_right (lt_of_lt_of_le hhtI hht) hX0
  have he : (0 : ℝ) ≤ 1 / (2 * (nPl K : ℝ) * (rkK I : ℝ)) := by positivity
  have hcore : size b' X' I ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * sizeQ b X A A₀ := by
    unfold size sizeQ
    rw [hrkR]
    calc ht b' X' I ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ)))
        ≤ (P ^ (2 * rkK I) * htQ b X A A₀) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.rpow_le_rpow hhtI.le hht he
      _ = (P ^ (2 * rkK I)) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) *
            htQ b X A A₀ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.mul_rpow hX0 hQpos.le
      _ = P ^ ((1 : ℝ) / (nPl K : ℝ)) *
            htQ b X A A₀ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hP]
          congr 1
          push_cast
          field_simp
  rw [div_le_iff₀ hlargepos]
  calc leastSize b' X' B ≤ size b' X' I := hleI
    _ ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * sizeQ b X A A₀ := hcore
    _ ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * largestSize b X A :=
        mul_le_mul_of_nonneg_left hQle (Real.rpow_nonneg hP _)

end Formalism.HN
