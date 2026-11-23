import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitCompactModCentralizerSeparableLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteOfCommuteSeparableCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactModNormOneKernelInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixSqrtNearOneUltrametricStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

noncomputable section
namespace GlobalTheory.OrbitU

theorem locCpt (E : Type) [Field E] [NumberField E] (w : Pl E) : LocallyCompactSpace (w.adicCompletion E) := by
  have h : (w.adicCompletionIntegers E : Set (w.adicCompletion E)) =
      ((Valued.v : Valuation (w.adicCompletion E) _).integer : Set (w.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  have ho : IsOpen (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
    rw [h]; exact Valued.isOpen_integer _
  exact (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w).locallyCompactSpace_of_mem_nhds_of_addGroup
    (ho.mem_nhds (zero_mem _))

theorem glTop (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) : LocallyCompactSpace (GLw n w) ∧ SigmaCompactSpace (GLw n w) := by
  haveI := locCpt E w
  haveI hM : LocallyCompactSpace (Matrix (Fin n) (Fin n) (w.adicCompletion E)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → w.adicCompletion E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  haveI : ProperSpace (w.adicCompletion E) := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (w.adicCompletion E)) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → w.adicCompletion E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (GLw n w) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GLw n w) := Units.isClosedEmbedding_embedProduct.isEmbedding.secondCountableTopology
  exact ⟨inferInstance, sigmaCompactSpace_of_locallyCompact_secondCountable⟩

def starU {K : Type} [Field K] {n : ℕ} (σ : K →+* K) (g : GL (Fin n) K) : GL (Fin n) K where
  val := cT σ (g : Matrix (Fin n) (Fin n) K)
  inv := cT σ ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  val_inv := by rw [← cT_mul, Units.inv_mul, cT_one]
  inv_val := by rw [← cT_mul, Units.mul_inv, cT_one]

theorem orbit_cpt_U : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ C : Set (UL n w), IsCompact C → ∃ Ω : Set (UL n w), IsCompact Ω ∧ ∀ g : UL n w, g⁻¹ * y * g ∈ C → ∃ t ∈ twCent (MonoidHom.id (UL n w)) y, ∃ ω ∈ Ω, g = t * ω := by
  intro E _ _ _ hE n w y hy C hC
  have hCG : IsCompact (Subtype.val '' C : Set (GLw n w)) := hC.image continuous_subtype_val
  obtain ⟨D, hD, hDg⟩ := GlobalTheory.OrbitCptW.orbit_cpt_w E hE n w y.1 hy _ hCG
  have hcl := (GlobalTheory.LocFinU.isClosed_UL n w).isClosedEmbedding_subtypeVal
  have hgC : ∀ g : UL n w, g⁻¹ * y * g ∈ C → g.1⁻¹ * y.1 * g.1 ∈ (Subtype.val '' C : Set (GLw n w)) :=
    fun g hg => ⟨_, hg, rfl⟩
  by_cases hs : IsSplitAt w
  · have hUL : ∀ g : GLw n w, g ∈ UL n w := fun g => by unfold UL; rw [if_pos hs]; trivial
    refine ⟨Subtype.val ⁻¹' D, hcl.isCompact_preimage hD, fun g hg => ?_⟩
    obtain ⟨z, hz, d, hd, hgd⟩ := hDg g.1 (hgC g hg)
    exact ⟨⟨z, hUL z⟩, Subtype.ext hz, ⟨d, hUL d⟩, hd, Subtype.ext hgd⟩
  obtain ⟨hσc, hσi, -⟩ := GlobalTheory.ConjAtPlace.main E hE w
  set σ := cj w with hσ
  have hmemU : ∀ g : GLw n w, g ∈ UL n w ↔ cT σ g.val * g.val = 1 := by
    intro g; unfold UL; rw [if_neg hs]; show cT σ _ * 1 * _ = 1 ↔ _; rw [Matrix.mul_one]
  have hcTc : Continuous fun M : Matrix (Fin n) (Fin n) (w.adicCompletion E) => cT σ M :=
    (continuous_id.matrix_map hσc).matrix_transpose
  have hcc : ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E), cT σ (cT σ M) = M := by
    intro M; ext i j; simp [cT, hσi]
  have hstarc : Continuous (starU σ : GLw n w → GLw n w) := by
    rw [Units.continuous_iff]
    exact ⟨hcTc.comp Units.continuous_val, hcTc.comp Units.continuous_coe_inv⟩
  obtain ⟨lc, sc⟩ := glTop E w n
  let Z : Subgroup (GLw n w) := Subgroup.centralizer {y.1}
  have hZ : ∀ z : GLw n w, z ∈ Z ↔ z.val * y.1.val = y.1.val * z.val := by
    intro z
    rw [Subgroup.mem_centralizer_singleton_iff, Units.ext_iff, Units.val_mul, Units.val_mul]
  have hZc : IsClosed (Z : Set (GLw n w)) := by
    have : (Z : Set (GLw n w)) = {z | z * y.1 = y.1 * z} := by
      ext z; exact Subgroup.mem_centralizer_singleton_iff
    rw [this]
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  haveI : LocallyCompactSpace Z := hZc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace Z := hZc.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  have hcomm : ∀ a b : Z, a * b = b * a := fun a b => Subtype.ext (Units.ext
    (GlobalTheory.commute_of_commute_separable_charpoly _ n y.1.val a.1.val b.1.val hy ((hZ _).1 a.2) ((hZ _).1 b.2)))
  have hyU : cT σ y.1.val * y.1.val = 1 := (hmemU _).1 y.2
  have hyU' : y.1.val * cT σ y.1.val = 1 := mul_eq_one_comm.1 hyU
  have hst : ∀ z ∈ Z, starU σ z ∈ Z := by
    intro z hz
    rw [hZ] at hz ⊢
    have h1 : cT σ y.1.val * cT σ z.val = cT σ z.val * cT σ y.1.val := by rw [← cT_mul, ← cT_mul, hz]
    show cT σ z.val * y.1.val = y.1.val * cT σ z.val
    calc cT σ z.val * y.1.val = (y.1.val * cT σ y.1.val) * cT σ z.val * y.1.val := by rw [hyU', Matrix.one_mul]
      _ = y.1.val * (cT σ y.1.val * cT σ z.val) * y.1.val := by simp only [Matrix.mul_assoc]
      _ = y.1.val * (cT σ z.val * cT σ y.1.val) * y.1.val := by rw [h1]
      _ = y.1.val * cT σ z.val * (cT σ y.1.val * y.1.val) := by simp only [Matrix.mul_assoc]
      _ = y.1.val * cT σ z.val := by rw [hyU, Matrix.mul_one]
  let τ : Z →* Z :=
    { toFun := fun z => ⟨starU σ z.1, hst _ z.2⟩
      map_one' := Subtype.ext (Units.ext (cT_one σ))
      map_mul' := fun a b => by
        have : (⟨starU σ (a * b).1, hst _ (a * b).2⟩ : Z) = ⟨starU σ b.1, hst _ b.2⟩ * ⟨starU σ a.1, hst _ a.2⟩ :=
          Subtype.ext (Units.ext (by show cT σ (a.1.val * b.1.val) = cT σ b.1.val * cT σ a.1.val; exact cT_mul σ _ _))
        rw [this, hcomm] }
  have hτ : ∀ z : Z, ((τ z : Z) : GLw n w) = starU σ z.1 := fun z => rfl
  have hτc : Continuous τ := continuous_induced_rng.2 (hstarc.comp continuous_subtype_val)
  have hτi : ∀ z, τ (τ z) = z := fun z => Subtype.ext (Units.ext (hcc _))
  have hsq : ∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s := by
    obtain ⟨W, hW, hWs⟩ : ∃ W ∈ nhds (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)), ∀ s ∈ W, ∃ r : Matrix (Fin n) (Fin n) (w.adicCompletion E), r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) (w.adicCompletion E), a * s = s * a → a * r = r * a) ∧ ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
      haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
      letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
      exact GlobalTheory.T.exists_matrix_sqrt_near_one_ultrametric (w.adicCompletion E) n σ hσc
    refine ⟨(fun z : Z => (z.1 : Matrix (Fin n) (Fin n) _)) ⁻¹' W,
      (Units.continuous_val.comp continuous_subtype_val).continuousAt.preimage_mem_nhds (by simpa using hW), ?_⟩
    intro s hs hτs
    obtain ⟨r, hrr, hrc, hrs⟩ := hWs _ hs
    have hsv : cT σ s.1.val = s.1.val := by
      have h := congrArg (fun u : Z => u.1.val) hτs
      exact h
    have hrr' : r * r = s.1.val := hrr
    have hu : IsUnit r := isUnit_of_mul_isUnit_left (hrr'.symm ▸ s.1.isUnit)
    have hrZ : hu.unit ∈ Z := (hZ _).2 (hrc _ ((hZ _).1 s.2).symm).symm
    refine ⟨⟨hu.unit, hrZ⟩, Subtype.ext (Units.ext (hrs hsv)), Subtype.ext (Units.ext hrr')⟩
  let DZ : Set Z := Subtype.val ⁻¹' ((fun d : GLw n w => starU σ d⁻¹ * d⁻¹) '' D)
  have hDZ : IsCompact DZ := hZc.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hD.image ((hstarc.comp continuous_inv).mul continuous_inv))
  obtain ⟨B, hB, hBz⟩ := GlobalTheory.T.exists_compact_mod_normOneKernel_involution Z hcomm τ hτc hτi hsq DZ hDZ
  refine ⟨Subtype.val ⁻¹' ((Subtype.val '' B : Set (GLw n w)) * D),
    hcl.isCompact_preimage ((hB.image continuous_subtype_val).mul hD), fun g hg => ?_⟩
  obtain ⟨z, hz, d, hd, hgd⟩ := hDg g.1 (hgC g hg)
  have hzZ : z ∈ Z := (hZ z).2 (by simpa using congrArg Units.val hz)
  have hgU : cT σ g.1.val * g.1.val = 1 := (hmemU _).1 g.2
  have hN : τ ⟨z, hzZ⟩ * ⟨z, hzZ⟩ ∈ DZ := by
    refine ⟨d, hd, Units.ext ?_⟩
    have hg' : g.1.val = z.val * d.val := by rw [hgd, Units.val_mul]
    rw [hg', cT_mul] at hgU
    have e1 : cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * cT σ d.val = 1 := by
      rw [← cT_mul, Units.mul_inv, cT_one]
    show cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) = cT σ z.val * z.val
    calc cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _)
        = cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * (cT σ d.val * cT σ z.val * (z.val * d.val)) * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) := by
          rw [hgU, Matrix.mul_one]
      _ = (cT σ ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _) * cT σ d.val) * (cT σ z.val * z.val) * (d.val * ((d⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) _)) := by
          simp only [Matrix.mul_assoc]
      _ = cT σ z.val * z.val := by rw [e1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨t, ht, b, hb, hzt⟩ := hBz _ hN
  have htU : t.1 ∈ UL n w := by
    have h := congrArg (fun u : Z => u.1.val) ht
    exact (hmemU _).2 h
  have hgt : g.1 = t.1 * (b.1 * d) := by
    rw [hgd, ← mul_assoc]; exact congrArg (· * d) (congrArg Subtype.val hzt)
  have hωU : b.1 * d ∈ UL n w := by
    have : b.1 * d = t.1⁻¹ * g.1 := by rw [hgt, inv_mul_cancel_left]
    rw [this]; exact (UL n w).mul_mem ((UL n w).inv_mem htU) g.2
  refine ⟨⟨t.1, htU⟩, Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 t.2), ⟨b.1 * d, hωU⟩,
    ⟨b.1, ⟨b, hb, rfl⟩, d, hd, rfl⟩, Subtype.ext hgt⟩

end GlobalTheory.OrbitU
