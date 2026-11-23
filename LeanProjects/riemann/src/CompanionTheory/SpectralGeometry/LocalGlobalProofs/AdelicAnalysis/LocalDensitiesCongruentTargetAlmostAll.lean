import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureProdOfAddGroupsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlacesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlacesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentitiesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalLatticeCompactOpenUnitVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresSupportStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GoodScale

theorem map_eq_self {V : Type} [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [IsTopologicalAddGroup V] (μ : Measure V) [μ.IsAddHaarMeasure] (e f : V → V)
    (he : ∀ x y, e (x + y) = e x + e y) (hef : ∀ x, e (f x) = x) (hfe : ∀ x, f (e x) = x)
    (hec : Continuous e) (hfc : Continuous f) (L : Set V) (hLc : IsCompact L) (hLo : IsOpen L)
    (hLn : L.Nonempty) (heL : ∀ x ∈ L, e x ∈ L) (hfL : ∀ x ∈ L, f x ∈ L) : μ.map e = μ := by
  let e' : V ≃+ V :=
    { toFun := e, invFun := f, left_inv := hfe, right_inv := hef, map_add' := he }
  exact (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open V V μ μ e' hec hfc).2 L L hLc hLo hLn
    (fun x => ⟨fun h => by simpa [e', hfe] using hfL _ h, heL x⟩) rfl

theorem mul_entry_mem {K : Type} [CommRing K] (O : Subring K) {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) K} (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) (i j : Fin n) :
    (A * B) i j ∈ O := by
  rw [Matrix.mul_apply]
  exact O.sum_mem fun k _ => O.mul_mem (hA i k) (hB k j)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem rmul_add (R : Type) [CommRing R] [Algebra F R] {M n : ℕ}
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X Y : Fin n → Fin M → R ⊗[F] E) :
    rmul R (X + Y) g = rmul R X g + rmul R Y g := by
  funext a i
  simp [rmul, add_mul, Finset.sum_add_distrib]

theorem continuous_rmul (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (hK : IsTopologicalRing (R ⊗[F] E)) {M n : ℕ} (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Continuous (fun X : Fin n → Fin M → R ⊗[F] E => rmul R X g) := by
  haveI := hK
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [rmul]
  exact continuous_finset_sum _ fun c _ =>
    (continuous_apply_apply c i).mul continuous_const

theorem mass_eq_of_integral (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F)
    (hσ : ∀ y ∈ O, sigR (Fv F v) σ y ∈ O)
    (g gi : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (hg : ∀ i j, g i j ∈ O)
    (hgi : ∀ i j, gi i j ∈ O) (hggi : g * gi = 1) (hgig : gi * g = 1)
    (lam : Measure (Fv F v)) (hlam : IsStdV v lam)
    (m : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m)
    (S S' : HermR (Fv F v) σ n)
    (hS : (S' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) =
      cT (sigR (Fv F v) σ) g * (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * g) :
    m S' (latV b v) = m S (latV b v) := by
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR; haveI := hLC; haveI := hSC; haveI := hT2
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hKring, hKlc, hKsc, hKt2, -, -, -, hWb, hHcl, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)
  haveI := hKring; haveI := hKlc; haveI := hKsc; haveI := hKt2
  haveI := hWb n M
  haveI hWb' := hWb n n
  obtain ⟨hHlc, hHsc, hHt2, hHb, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM (Fv F v) n
  haveI := hHlc; haveI := hHsc; haveI := hHt2; haveI := hHb
  obtain ⟨-, hμ, hν⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b lam hlam.1
  haveI := hμ n M
  haveI := hν n
  obtain ⟨-, hcomp, hone, hherm, -⟩ := GlobalTheory.T.gram_right_action_identities F E σ hCM M J hJ (Fv F v) n
  obtain ⟨hLc, hLo, hL0, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b n M v
  obtain ⟨hLc', hLo', hL0', -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b n n v
  have hrm : ∀ (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)), (∀ i j, h i j ∈ O) →
      ∀ X ∈ latV (M := M) (n := n) b v, rmul (Fv F v) X h ∈ latV (M := M) (n := n) b v := by
    intro h hh X hX a i
    exact (hO _).1 (O.sum_mem fun c _ => O.mul_mem ((hO _).2 (hX c i)) (hh c a))
  have hmapW : (coordW (Fv F v) b lam n M).map (fun X => rmul (Fv F v) X g) =
      coordW (Fv F v) b lam n M :=
    map_eq_self _ _ (fun X => rmul (Fv F v) X gi) (fun X Y => rmul_add (Fv F v) g X Y)
      (fun X => by simp only [hcomp, hgig, hone]) (fun X => by simp only [hcomp, hggi, hone])
      (continuous_rmul (Fv F v) hKring g) (continuous_rmul (Fv F v) hKring gi) (latV b v) hLc hLo
      ⟨0, hL0⟩ (hrm g hg) (hrm gi hgi)
  have hc1 : cT (sigR (Fv F v) σ) gi * cT (sigR (Fv F v) σ) g = 1 := by
    rw [← cT_mul, hggi, cT_one]
  have hc2 : cT (sigR (Fv F v) σ) g * cT (sigR (Fv F v) σ) gi = 1 := by
    rw [← cT_mul, hgig, cT_one]
  let τ : HermR (Fv F v) σ n → HermR (Fv F v) σ n := fun S => ⟨_, hherm S g⟩
  let τi : HermR (Fv F v) σ n → HermR (Fv F v) σ n := fun S => ⟨_, hherm S gi⟩
  let L' : Set (HermR (Fv F v) σ n) :=
    (Subtype.val : HermR (Fv F v) σ n → Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ⁻¹'
      (latV (M := n) (n := n) b v : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))
  have hconj : ∀ (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)), (∀ i j, h i j ∈ O) →
      ∀ (A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)),
      A ∈ (latV (M := n) (n := n) b v : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) →
      cT (sigR (Fv F v) σ) h * A * h ∈
        (latV (M := n) (n := n) b v : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) := by
    intro h hh A hA a i
    refine (hO _).1 (mul_entry_mem O (mul_entry_mem O ?_ ?_) hh a i)
    · intro p q
      exact hσ _ (hh q p)
    · intro p q
      exact (hO _).2 (hA p q)
  have hcont : ∀ h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
      Continuous (fun A : HermR (Fv F v) σ n =>
        cT (sigR (Fv F v) σ) h * (A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * h) := fun h =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  have hinv : ∀ (h h' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)),
      cT (sigR (Fv F v) σ) h * cT (sigR (Fv F v) σ) h' = 1 → h' * h = 1 →
      ∀ A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
      cT (sigR (Fv F v) σ) h * (cT (sigR (Fv F v) σ) h' * A * h') * h = A := by
    intro h h' e1 e2 A
    calc _ = (cT (sigR (Fv F v) σ) h * cT (sigR (Fv F v) σ) h') * A * (h' * h) := by
          simp only [Matrix.mul_assoc]
      _ = A := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
  have hmapH : (coordHerm (Fv F v) σ b lam n).map τ = coordHerm (Fv F v) σ b lam n := by
    refine map_eq_self _ τ τi ?_ ?_ ?_ ((hcont g).subtype_mk _) ((hcont gi).subtype_mk _) L' ?_ ?_
      ⟨0, hL0'⟩ ?_ ?_
    · intro A B
      apply Subtype.ext
      simp [τ, Matrix.mul_add, Matrix.add_mul]
    · intro A
      exact Subtype.ext (hinv g gi hc2 hgig _)
    · intro A
      exact Subtype.ext (hinv gi g hc1 hggi _)
    · exact (hHcl n).isClosedEmbedding_subtypeVal.isCompact_preimage hLc'
    · exact hLo'.preimage continuous_subtype_val
    · intro A hA
      exact hconj g hg _ hA
    · intro A hA
      exact hconj gi hgi _ hA
  have hdet : IsUnit g.det := Matrix.isUnit_det_of_right_inverse hggi
  have hs := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hCM M J hJ (Fv F v) hloc n _ _ m (hμ n M) (hν n) hm g hdet τ
    (fun _ => rfl) 1 1 (by simpa using hmapW) (by simpa using hmapH) S
  simp only [one_smul] at hs
  have hτ : τ S = S' := Subtype.ext hS.symm
  rw [hτ] at hs
  rw [hs, Measure.map_apply (continuous_rmul (Fv F v) hKring g).measurable hLo.measurableSet]
  congr 1
  ext X
  constructor
  · intro hX
    have := hrm gi hgi _ hX
    simpa only [hcomp, hggi, hone] using this
  · exact hrm g hg X

theorem mass_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (g : Matrix (Fin n) (Fin n) E), g.det ≠ 0 → ∀ (T' : Matrix (Fin n) (Fin n) E) (hT' : ∀ a b, σ (T' b a) = T' a b), T' = cT (σ : E →+* E) g * T * g → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m → m (hermOf (Fv F v) σ T' hT') (latV b v) = m (hermOf (Fv F v) σ T hT) (latV b v) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n T hT _ g hg T' hT' hTT' d b
  have hint := (GlobalTheory.T.integral_almost_all_places F E σ hCM d b).1
  have hev : ∀ A : Matrix (Fin n) (Fin n) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (A i j)) k ∈
        v.adicCompletionIntegers F := fun A =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hint (A i j)
  filter_upwards [GlobalTheory.T.tensor_integer_ring_almost_all_places F E σ hCM d b, hev g, hev g⁻¹] with v hv hgv hgiv lam hlam m hm
  obtain ⟨O, hO, hσ, -⟩ := hv
  have hu : IsUnit g.det := isUnit_iff_ne_zero.2 hg
  have hc : cT (sigR (Fv F v) σ) (g.map (inclR (Fv F v))) =
      (cT (σ : E →+* E) g).map (inclR (Fv F v)) := by
    ext i j
    simp [cT, sigR, inclR]
  refine mass_eq_of_integral σ hCM J hJ n b v O hO hσ (g.map (inclR (Fv F v)))
    (g⁻¹.map (inclR (Fv F v))) (fun i j => (hO _).2 (hgv i j)) (fun i j => (hO _).2 (hgiv i j))
    ?_ ?_ lam hlam m hm _ _ ?_
  · rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  · change T'.map (inclR (Fv F v)) = _ * T.map (inclR (Fv F v)) * _
    rw [hTT', Matrix.map_mul, Matrix.map_mul, hc]

end GlobalTheory.CompanionTheory.SW.GoodScale
