import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.MapHerm

open Topology

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

abbrev tm (E : Type) [Field E] [Algebra F E] (f : R →ₐ[F] R') : R ⊗[F] E →ₐ[F] R' ⊗[F] E :=
  Algebra.TensorProduct.map f (AlgHom.id F E)

theorem repr_tm (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (tm E f y) k =
      f ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [hx, hy]

theorem tm_sig (f : R →ₐ[F] R') (σ : E →ₐ[F] E) (y : R ⊗[F] E) :
    tm E f (sigR R σ y) = sigR R' σ (tm E f y) := by
  simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  ext <;> simp

end Tensor

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def joinT {d : ℕ} (b : Module.Basis (Fin d) F E) (x : Ainf F ⊗[F] E) (y : Af F ⊗[F] E) : AF F ⊗[F] E :=
  (Algebra.TensorProduct.basis (AF F) b).repr.symm
    (Finsupp.equivFunOnFinite.symm fun k =>
      pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr x k)
        ((Algebra.TensorProduct.basis (Af F) b).repr y k))

theorem repr_joinT {d : ℕ} (b : Module.Basis (Fin d) F E) (x : Ainf F ⊗[F] E) (y : Af F ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (AF F) b).repr (joinT b x y) k =
      pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr x k)
        ((Algebra.TensorProduct.basis (Af F) b).repr y k) := by
  simp [joinT]

theorem tm_fst_joinT {d : ℕ} (b : Module.Basis (Fin d) F E) (x : Ainf F ⊗[F] E) (y : Af F ⊗[F] E) :
    tm E (fstA F) (joinT b x y) = x := by
  apply (Algebra.TensorProduct.basis (Ainf F) b).repr.injective
  ext k
  rw [repr_tm, repr_joinT]
  rfl

theorem tm_snd_joinT {d : ℕ} (b : Module.Basis (Fin d) F E) (x : Ainf F ⊗[F] E) (y : Af F ⊗[F] E) :
    tm E (sndA F) (joinT b x y) = y := by
  apply (Algebra.TensorProduct.basis (Af F) b).repr.injective
  ext k
  rw [repr_tm, repr_joinT]
  rfl

theorem tm_ext {d : ℕ} (b : Module.Basis (Fin d) F E) {u v : AF F ⊗[F] E}
    (h1 : tm E (fstA F) u = tm E (fstA F) v) (h2 : tm E (sndA F) u = tm E (sndA F) v) : u = v := by
  apply (Algebra.TensorProduct.basis (AF F) b).repr.injective
  ext k
  have e1 := congrArg (fun w => (Algebra.TensorProduct.basis (Ainf F) b).repr w k) h1
  have e2 := congrArg (fun w => (Algebra.TensorProduct.basis (Af F) b).repr w k) h2
  simp only [repr_tm] at e1 e2
  exact Prod.ext e1 e2

def hermJoin {d : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) {n : ℕ}
    (p : HermR (Ainf F) σ n × HermR (Af F) σ n) : HermR (AF F) σ n :=
  ⟨Matrix.of fun i j => joinT b ((p.1 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j)
      ((p.2 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j), by
    intro i j
    apply tm_ext b
    · simp only [Matrix.of_apply]
      rw [tm_sig, tm_fst_joinT, tm_fst_joinT]
      exact p.1.2 i j
    · simp only [Matrix.of_apply]
      rw [tm_sig, tm_snd_joinT, tm_snd_joinT]
      exact p.2.2 i j⟩

def hermSplit {d : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (n : ℕ) :
    HermR (AF F) σ n ≃+ HermR (Ainf F) σ n × HermR (Af F) σ n where
  toFun x := (hermInf σ x, hermFin σ x)
  invFun := hermJoin b σ
  left_inv x := by
    apply Subtype.ext
    ext i j
    apply tm_ext b
    · exact tm_fst_joinT b _ _
    · exact tm_snd_joinT b _ _
  right_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · ext i j
      exact tm_fst_joinT b _ _
    · ext i j
      exact tm_snd_joinT b _ _
  map_add' x y := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · ext i j
      simp [hermInf]
    · ext i j
      simp [hermFin]

end Adelic

section Top

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finite_of_cm {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) : Module.Finite F E :=
  Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)

theorem continuous_tm {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {R R' : Type} [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [CommRing R'] [Algebra F R'] [TopologicalSpace R'] [IsTopologicalRing R'] [LocallyCompactSpace R']
    [SecondCountableTopology R'] [T2Space R'] (f : R →ₐ[F] R') (hf : Continuous f) :
    Continuous (tm E f) := by
  haveI := finite_of_cm hCM
  have h1 := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R).2.2.2.2.2.2.1 _ (Module.finBasis F E)
  have h2 := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R').2.2.2.2.2.2.1 _ (Module.finBasis F E)
  rw [h2.isEmbedding.continuous_iff]
  refine continuous_pi fun k => ?_
  simp only [Function.comp_def, repr_tm]
  exact hf.comp ((continuous_apply k).comp h1.continuous)

theorem continuous_joinT {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    {X : Type} [TopologicalSpace X] {f : X → Ainf F ⊗[F] E} {g : X → Af F ⊗[F] E}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => joinT b (f x) (g x) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  have h0 := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)).2.2.2.2.2.2.1 _ b
  have h1 := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)).2.2.2.2.2.2.1 _ b
  have h2 := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Af F)).2.2.2.2.2.2.1 _ b
  rw [h0.isEmbedding.continuous_iff]
  refine continuous_pi fun k => ?_
  simp only [Function.comp_def, repr_joinT]
  exact (((continuous_apply k).comp h1.continuous).comp hf).prodMk
    (((continuous_apply k).comp h2.continuous).comp hg)

theorem herm_facts {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (n : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] :
    IsTopologicalAddGroup (HermR R σ n) ∧ LocallyCompactSpace (HermR R σ n) ∧
      SecondCountableTopology (HermR R σ n) ∧ T2Space (HermR R σ n) := by
  obtain ⟨h1, h2, h3, h4, -, -, -, -, h9, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI : IsTopologicalRing (R ⊗[F] E) := h1
  haveI : LocallyCompactSpace (R ⊗[F] E) := h2
  haveI : SecondCountableTopology (R ⊗[F] E) := h3
  haveI : T2Space (R ⊗[F] E) := h4
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R ⊗[F] E))
  haveI : T2Space (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin n → Fin n → R ⊗[F] E))
  have hc : IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := h9 n
  exact ⟨inferInstance, hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology, inferInstance⟩

theorem continuous_hermInf {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (n : ℕ) :
    Continuous (hermInf σ : HermR (AF F) σ n → HermR (Ainf F) σ n) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have c1 := continuous_tm (E := E) hCM (fstA F) continuous_fst
  refine continuous_induced_rng.2 ?_
  change Continuous fun x : HermR (AF F) σ n =>
    (x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (tm E (fstA F))
  exact Continuous.matrix_map continuous_subtype_val c1

theorem continuous_hermFin {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (n : ℕ) :
    Continuous (hermFin σ : HermR (AF F) σ n → HermR (Af F) σ n) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  have c1 := continuous_tm (E := E) hCM (sndA F) continuous_snd
  refine continuous_induced_rng.2 ?_
  change Continuous fun x : HermR (AF F) σ n =>
    (x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (tm E (sndA F))
  exact Continuous.matrix_map continuous_subtype_val c1

theorem continuous_hermJoin {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) :
    Continuous (hermJoin b σ : HermR (Ainf F) σ n × HermR (Af F) σ n → HermR (AF F) σ n) := by
  refine continuous_induced_rng.2 ?_
  refine continuous_matrix fun i j => ?_
  change Continuous fun p : HermR (Ainf F) σ n × HermR (Af F) σ n =>
    joinT b ((p.1 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j) ((p.2 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j)
  have g1 : Continuous fun p : HermR (Ainf F) σ n × HermR (Af F) σ n =>
      (p.1 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j :=
    (continuous_id.matrix_elem i j).comp (continuous_subtype_val.comp continuous_fst)
  have g2 : Continuous fun p : HermR (Ainf F) σ n × HermR (Af F) σ n =>
      (p.2 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j :=
    (continuous_id.matrix_elem i j).comp (continuous_subtype_val.comp continuous_snd)
  exact continuous_joinT hCM b g1 g2

def hermHomeo {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) :
    HermR (AF F) σ n ≃ₜ HermR (Ainf F) σ n × HermR (Af F) σ n where
  toEquiv := (hermSplit b σ n).toEquiv
  continuous_toFun := (continuous_hermInf hCM n).prodMk (continuous_hermFin hCM n)
  continuous_invFun := continuous_hermJoin hCM b n

end Top

theorem map_eq_smul_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (n : ℕ) (db : Measure (HermR (AF F) σ n)), db.IsAddHaarMeasure →
  ∃ (ν₁ : Measure (HermR (Ainf F) σ n)) (ν₂ : Measure (HermR (Af F) σ n)) (c : ℝ≥0∞),
    ν₁.IsAddHaarMeasure ∧ ν₂.IsAddHaarMeasure ∧ SFinite ν₁ ∧ SFinite ν₂ ∧ c ≠ ⊤ ∧
    MeasurableEmbedding (fun b : HermR (AF F) σ n => (hermInf σ b, hermFin σ b)) ∧
    db.map (fun b => (hermInf σ b, hermFin σ b)) = c • ν₁.prod ν₂ := by
  intro F E _ _ _ _ _ σ hCM n db hdb
  haveI := finite_of_cm hCM
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  obtain ⟨a1, a2, a3, a4⟩ := herm_facts hCM n (AF F)
  obtain ⟨b1, b2, b3, b4⟩ := herm_facts hCM n (Ainf F)
  obtain ⟨c1, c2, c3, c4⟩ := herm_facts hCM n (Af F)
  let b := Module.finBasis F E
  let e := hermHomeo hCM b n
  have he : (e : HermR (AF F) σ n → _) = fun b => (hermInf σ b, hermFin σ b) := rfl
  haveI hmap : (db.map e).IsAddHaarMeasure :=
    (hermSplit b σ n).isAddHaarMeasure_map db e.continuous e.symm.continuous
  let ν₁ : Measure (HermR (Ainf F) σ n) := Measure.addHaar
  let ν₂ : Measure (HermR (Af F) σ n) := Measure.addHaar
  haveI : SFinite ν₁ := inferInstance
  haveI : SFinite ν₂ := inferInstance
  refine ⟨ν₁, ν₂, ((db.map e).addHaarScalarFactor (ν₁.prod ν₂) : ℝ≥0), inferInstance, inferInstance,
    inferInstance, inferInstance, ENNReal.coe_ne_top, ?_, ?_⟩
  · rw [← he]
    exact e.measurableEmbedding
  · rw [← he]
    exact Measure.isAddLeftInvariant_eq_smul (db.map e) (ν₁.prod ν₂)

end GlobalTheory.CompanionTheory.SiegelND.Integ.MapHerm
