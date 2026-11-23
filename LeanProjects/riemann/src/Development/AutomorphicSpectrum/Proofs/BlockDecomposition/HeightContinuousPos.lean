import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximalStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.CompanionTheory.Iwasawa

theorem continuous_of_mul_compact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {P K : Set G} {f : G → ℝ}
    (hP : IsClosed P) (hK : IsCompact K) (hf : ContinuousOn f P)
    (hd : ∀ x, ∃ p ∈ P, ∃ k ∈ K, x = p * k) (hv : ∀ p ∈ P, ∀ k ∈ K, f (p * k) = f p) : Continuous f := by
  refine continuous_iff_isClosed.2 fun C hC => ?_
  have hD : IsClosed (P ∩ f ⁻¹' C) := hf.preimage_isClosed_of_isClosed hP hC
  convert hD.mul_right_of_isCompact hK using 1
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, k, hk, rfl⟩ := hd x
    exact Set.mem_mul.2 ⟨p, ⟨hp, by simpa [Set.mem_preimage, hv p hp k hk] using hx⟩, k, hk, rfl⟩
  · rintro ⟨p, ⟨hp, hc⟩, k, hk, rfl⟩
    simpa [Set.mem_preimage, hv p hp k hk] using hc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem topRing_AE : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)

theorem t2Space_cm_host_adeles : T2Space (AE F E) := by
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  exact GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)

theorem topologicalGroup_unitary_double : IsTopologicalGroup (G2 σ Y) := by
  haveI := topRing_AE (F := F) (E := E)
  infer_instance

def parT (x : G2 σ Y) : Matrix (Fin n) (Fin n) (AE F E) := (mat2 x * dC n (AE F E)).toRows₁

theorem continuous_mat2 : Continuous (mat2 : G2 σ Y → _) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_parT : Continuous (parT : G2 σ Y → _) := by
  haveI := topRing_AE (F := F) (E := E)
  have h : Continuous fun x : G2 σ Y => mat2 x * dC n (AE F E) := continuous_mat2.matrix_mul continuous_const
  exact continuous_matrix fun i j => h.matrix_elem _ _

theorem parT_eq {p : G2 σ Y} {t : GL (Fin n) (AE F E)} (h : IsPar p t) : parT p = t.1 := by
  rw [parT, isPar_iff.1 h, dC, diagCols, Matrix.fromRows_mul, Matrix.one_mul, Matrix.toRows₁_fromRows]

theorem exists_isPar_iff {x : G2 σ Y} : (∃ t, IsPar x t) ↔ mat2 x * dC n (AE F E) = dC n (AE F E) * parT x ∧
    mat2 x⁻¹ * dC n (AE F E) = dC n (AE F E) * parT x⁻¹ ∧ parT x * parT x⁻¹ = 1 ∧ parT x⁻¹ * parT x = 1 := by
  constructor
  · rintro ⟨t, h⟩
    have h' := IsPar.inv h
    rw [parT_eq h, parT_eq h']
    exact ⟨isPar_iff.1 h, isPar_iff.1 h', Units.mul_inv t, Units.inv_mul t⟩
  · rintro ⟨h1, -, h3, h4⟩
    exact ⟨⟨parT x, parT x⁻¹, h3, h4⟩, isPar_iff.2 h1⟩

theorem isClosed_siegel_stabiliser : IsClosed (par2 σ Y : Set (G2 σ Y)) := by
  haveI := topRing_AE (F := F) (E := E)
  haveI := t2Space_cm_host_adeles (F := F) (E := E)
  haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)
  have ci : Continuous fun x : G2 σ Y => parT x⁻¹ := continuous_parT.comp continuous_inv
  have cm : Continuous fun x : G2 σ Y => mat2 x⁻¹ := continuous_mat2.comp continuous_inv
  have e : (par2 σ Y : Set (G2 σ Y)) = {x | mat2 x * dC n (AE F E) = dC n (AE F E) * parT x} ∩
      ({x | mat2 x⁻¹ * dC n (AE F E) = dC n (AE F E) * parT x⁻¹} ∩
      ({x | parT x * parT x⁻¹ = 1} ∩ {x | parT x⁻¹ * parT x = 1})) := by
    ext x
    exact mem_parabolic_GL2_iff.trans exists_isPar_iff
  rw [e]
  exact (isClosed_eq (continuous_mat2.matrix_mul continuous_const) (continuous_const.matrix_mul continuous_parT)).inter
    ((isClosed_eq (cm.matrix_mul continuous_const) (continuous_const.matrix_mul ci)).inter
    ((isClosed_eq (continuous_parT.matrix_mul ci) continuous_const).inter
    (isClosed_eq (ci.matrix_mul continuous_parT) continuous_const)))

def parU (p : par2 σ Y) : GL (Fin n) (AE F E) :=
  ⟨parT p.1, parT p.1⁻¹, (exists_isPar_iff.1 (mem_parabolic_GL2_iff.1 p.2)).2.2.1, (exists_isPar_iff.1 (mem_parabolic_GL2_iff.1 p.2)).2.2.2⟩

theorem isPar_parU (p : par2 σ Y) : IsPar p.1 (parU p) := isPar_iff.2 (exists_isPar_iff.1 (mem_parabolic_GL2_iff.1 p.2)).1

theorem continuous_parU : Continuous (parU : par2 σ Y → GL (Fin n) (AE F E)) := by
  haveI := topRing_AE (F := F) (E := E)
  haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)
  exact Units.continuous_iff.2 ⟨continuous_parT.comp continuous_subtype_val,
    continuous_parT.comp (continuous_inv.comp continuous_subtype_val)⟩

theorem continuous_detGL : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) (AE F E) → (AE F E)ˣ) := by
  haveI := topRing_AE (F := F) (E := E)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · exact Units.continuous_coe_inv.matrix_det

theorem continuous_pos {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ}
    (hK : IsCompact (K : Set (G2 σ Y))) (ha : IsHgt K a) : Continuous a ∧ ∀ x, 0 < a x := by
  haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)
  have v1 : ∀ p t, IsPar p t → a p = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := fun p t h => by
    simpa using ha.val p t h 1 K.one_mem
  refine ⟨continuous_of_mul_compact (P := par2 σ Y) isClosed_siegel_stabiliser hK ?_ ?_ ?_, fun x => ?_⟩
  · refine continuousOn_iff_continuous_restrict.2 ?_
    exact (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (continuous_detGL.comp continuous_parU))).congr
      fun p => (v1 _ _ (isPar_parU p)).symm
  · intro x
    obtain ⟨p, t, h, k, hk, e⟩ := ha.iwa x
    exact ⟨p, mem_parabolic_GL2_iff.2 ⟨t, h⟩, k, hk, e⟩
  · intro p hp k hk
    obtain ⟨t, h⟩ := mem_parabolic_GL2_iff.1 hp
    rw [ha.val p t h k hk, v1 p t h]
  · obtain ⟨p, t, h, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t h k hk]
    have u : absE F E (Matrix.GeneralLinearGroup.det t) ≠ 0 := fun h0 => by
      have e := map_mul (absE F E) (Matrix.GeneralLinearGroup.det t) (Matrix.GeneralLinearGroup.det t)⁻¹
      rw [mul_inv_cancel, map_one, h0, zero_mul] at e
      exact one_ne_zero e
    exact_mod_cast pos_iff_ne_zero.2 u

theorem height_continuous_pos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → Continuous a ∧ ∀ x, 0 < a x :=
  fun F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha =>
    continuous_pos (GlobalTheory.T.isCompact_standard_maximal F E σ B n Y r s hB hn hY b K a hb hK ha) ha

end GlobalTheory.CompanionTheory.Iwasawa
