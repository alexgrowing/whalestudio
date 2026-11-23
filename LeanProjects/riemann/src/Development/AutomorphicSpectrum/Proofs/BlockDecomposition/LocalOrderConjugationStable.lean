import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.Shear

theorem measurePreserving_of_compactOpen {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] (T S : G → G) (hadd : ∀ x y, T (x + y) = T x + T y)
    (hT : Continuous T) (hS : Continuous S) (hST : ∀ x, S (T x) = x) (hTS : ∀ x, T (S x) = x)
    (K : Set G) (hKc : IsCompact K) (hKo : IsOpen K) (hKn : K.Nonempty) (hK : T ⁻¹' K = K) :
    MeasurePreserving T μ μ := by
  let e : G ≃+ G := AddEquiv.mk' ⟨T, S, hST, hTS⟩ hadd
  haveI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ hT hS
  have hTm : Measurable T := hT.measurable
  have hsm := Measure.isAddLeftInvariant_eq_smul (Measure.map e μ) μ
  have hmapK : Measure.map e μ K = μ K := by
    change Measure.map T μ K = μ K
    rw [Measure.map_apply hTm hKo.measurableSet, hK]
  have h0 : μ K ≠ 0 := hKo.measure_ne_zero μ hKn
  have ht : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  set c := Measure.addHaarScalarFactor (Measure.map e μ) μ with hc
  have hc1 : c = 1 := by
    have h := congrArg (fun m : Measure G => m K) hsm
    simp only [Measure.smul_apply, hmapK] at h
    have h' : (1 : ℝ≥0∞) * μ K = (c : ℝ≥0∞) * μ K := by
      rw [one_mul]
      simpa [ENNReal.smul_def] using h
    have := (ENNReal.mul_left_inj h0 ht).1 h'
    exact_mod_cast this.symm
  refine ⟨hTm, ?_⟩
  change Measure.map e μ = μ
  rw [hsm, hc1, one_smul]

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem rmul_one {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    GlobalTheory.CompanionTheory.SW.rmul R X (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = X := by
  funext a i
  simp [GlobalTheory.CompanionTheory.SW.rmul, Matrix.one_apply]

theorem rmul_add {M n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    GlobalTheory.CompanionTheory.SW.rmul R (X + Y) g = GlobalTheory.CompanionTheory.SW.rmul R X g + GlobalTheory.CompanionTheory.SW.rmul R Y g := by
  funext a i
  simp [GlobalTheory.CompanionTheory.SW.rmul, add_mul, Finset.sum_add_distrib]

theorem negCol_self {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) : negCol R l a l = 1 := by
  simp [negCol]

theorem negCol_negCol {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) (hl : a l = 1) :
    negCol R l (negCol R l a) = a := by
  funext i
  by_cases h : i = l
  · subst h; simp [negCol, hl]
  · simp [negCol, h]

theorem eMat_mem {n : ℕ} (O : Subring (R ⊗[F] E)) (l : Fin n) (a : Fin n → R ⊗[F] E)
    (ha : ∀ i, a i ∈ O) (i k : Fin n) : eMat R l a i k ∈ O := by
  simp only [eMat, Matrix.updateCol_apply, Matrix.one_apply]
  split_ifs
  · exact ha i
  · exact O.one_mem
  · exact O.zero_mem

theorem rmul_mem {M n : ℕ} (O : Subring (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hg : ∀ i k, g i k ∈ O)
    (hX : X ∈ tupIn R (O : Set (R ⊗[F] E))) :
    GlobalTheory.CompanionTheory.SW.rmul R X g ∈ tupIn R (O : Set (R ⊗[F] E)) := fun a i =>
  O.sum_mem fun c _ => O.mul_mem (hX c i) (hg c a)

theorem continuous_rmul [TopologicalSpace (R ⊗[F] E)] [IsTopologicalRing (R ⊗[F] E)] {M n : ℕ}
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Continuous fun X : Fin n → Fin M → R ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul R X g := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  unfold GlobalTheory.CompanionTheory.SW.rmul
  refine continuous_finset_sum _ fun c _ => ?_
  exact (continuous_apply_apply c i).mul continuous_const

theorem isOpen_tupIn [TopologicalSpace (R ⊗[F] E)] {M n : ℕ} {L : Set (R ⊗[F] E)} (hL : IsOpen L) :
    IsOpen (tupIn (M := M) (n := n) R L) := by
  have : tupIn (M := M) (n := n) R L = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => L := by
    ext X
    simp [tupIn]
  rw [this]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hL

end GlobalTheory.CompanionTheory.AvgFree.Shear

open GlobalTheory.CompanionTheory.AvgFree.Shear in

theorem GlobalTheory.CompanionTheory.AvgFree.shear_measurePreserving : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ O : Subring (Fv F v ⊗[F] E), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → (∀ x ∈ O, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Fv F v) σ x ∈ O) → ∀ (n M : ℕ) (l : Fin n) (a : Fin n → (Fv F v ⊗[F] E)), (∀ i, a i ∈ O) → a l = 1 → MeasurePreserving (fun X : (Fin n → Fin M → (Fv F v ⊗[F] E)) => GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) l a)) (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv O hOc hOo _ n M l a ha hl
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  haveI := hlv.1
  obtain ⟨-, hW, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hW n M
  have hna : ∀ i, negCol (Fv F v) l a i ∈ O := fun i => by
    by_cases h : i = l
    · simp [negCol, h, O.one_mem]
    · simpa [negCol, h] using O.neg_mem (ha i)
  have hg1 : eMat (Fv F v) l a * eMat (Fv F v) l (negCol (Fv F v) l a) = 1 :=
    eMat_mul_negCol (Fv F v) l a hl
  have hg2 : eMat (Fv F v) l (negCol (Fv F v) l a) * eMat (Fv F v) l a = 1 := by
    have h := eMat_mul_negCol (Fv F v) l (negCol (Fv F v) l a) (negCol_self (Fv F v) l a)
    rwa [negCol_negCol (Fv F v) l a hl] at h
  have hST : ∀ X : Fin n → Fin M → Fv F v ⊗[F] E,
      GlobalTheory.CompanionTheory.SW.rmul (Fv F v) (GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) l a))
        (eMat (Fv F v) l (negCol (Fv F v) l a)) = X := fun X => by
    rw [rmul_mul, hg1, rmul_one]
  have hTS : ∀ X : Fin n → Fin M → Fv F v ⊗[F] E,
      GlobalTheory.CompanionTheory.SW.rmul (Fv F v) (GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) l (negCol (Fv F v) l a)))
        (eMat (Fv F v) l a) = X := fun X => by
    rw [rmul_mul, hg2, rmul_one]
  refine measurePreserving_of_compactOpen _ _
    (fun X => GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) l (negCol (Fv F v) l a)))
    (fun X Y => rmul_add (Fv F v) X Y _) (continuous_rmul (Fv F v) _) (continuous_rmul (Fv F v) _)
    hST hTS (tupIn (Fv F v) (O : Set (Fv F v ⊗[F] E))) (isCompact_tupIn (Fv F v) hOc)
    (isOpen_tupIn (Fv F v) hOo) ⟨0, fun _ _ => O.zero_mem⟩ ?_
  ext X
  constructor
  · intro hX
    have h := rmul_mem (Fv F v) O _ _ (eMat_mem (Fv F v) O l _ hna) hX
    rwa [hST] at h
  · exact rmul_mem (Fv F v) O X _ (eMat_mem (Fv F v) O l a ha)
