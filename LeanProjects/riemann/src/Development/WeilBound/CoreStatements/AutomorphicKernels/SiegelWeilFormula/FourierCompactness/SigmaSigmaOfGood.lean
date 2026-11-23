import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries.Grp

namespace PositivityTheory.SiegelWeilFormula.kfour

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def nM (β : Matrix (Fin n) (Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := Matrix.fromBlocks 1 β 0 1

theorem nM_mul (β γ : Matrix (Fin n) (Fin n) (AE F E)) : nM β * nM γ = nM (β + γ) := by
  simp [nM, Matrix.fromBlocks_multiply, add_comm]

theorem nM_zero : nM (0 : Matrix (Fin n) (Fin n) (AE F E)) = 1 := by
  simp [nM, Matrix.fromBlocks_one]

variable (σ n) in

def nCond (ε : ℤˣ) : AddSubgroup (Matrix (Fin n) (Fin n) (AE F E)) where
  carrier := {β | βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ))}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.transpose_add, ha, hb, Matrix.map_add _ (map_add _), smul_add, neg_add]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.transpose_neg, ha, Matrix.map_neg _ (map_neg _), smul_neg]

def FrameEq (σ : E →ₐ[F] E) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) : Prop :=
  b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0

def nU (b : GL (Fin n ⊕ Fin n) E) (β : Matrix (Fin n) (Fin n) (AE F E)) : GL (Fin n ⊕ Fin n) (AE F E) where
  val := incM F b.1 * nM β * incM F (b⁻¹).1
  inv := incM F b.1 * nM (-β) * incM F (b⁻¹).1
  val_inv := (conj_mul_conj b _ _).trans (by rw [nM_mul, add_neg_cancel, nM_zero, Matrix.mul_one, incM_mul_inv])
  inv_val := (conj_mul_conj b _ _).trans (by rw [nM_mul, neg_add_cancel, nM_zero, Matrix.mul_one, incM_mul_inv])

omit [NumberField E] in
theorem inclR_int (z : ℤ) : inclR (F := F) (AF F) ((z : ℤ) : E) = ((z : ℤ) : AE F E) := map_intCast _ z

omit [NumberField E] in

theorem nM_form (e : AE F E) (β : Matrix (Fin n) (Fin n) (AE F E)) :
    (nM β)ᵀ * Matrix.fromBlocks 0 1 (e • 1) 0 * (nM β).map (cA σ) =
      Matrix.fromBlocks 0 1 (e • 1) (e • β.map (cA σ) + βᵀ) := by
  simp only [nM, Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero, Matrix.fromBlocks_map,
    Matrix.fromBlocks_multiply]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)]
  congr 1 <;> simp

theorem frameEq_adelic {b : GL (Fin n ⊕ Fin n) E} {ε : ℤˣ} (hb : FrameEq σ Y b ε) :
    (incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ) =
      Matrix.fromBlocks 0 1 ((((ε : ℤ) : AE F E)) • 1) 0 := by
  rw [frame_adelic (F := F) hb, inclR_int]

theorem nU_mem {b : GL (Fin n ⊕ Fin n) E} {ε : ℤˣ} (hσ : ∀ a, σ (σ a) = a) (hb : FrameEq σ Y b ε)
    {β : Matrix (Fin n) (Fin n) (AE F E)} (hβ : β ∈ nCond σ n ε) : nU b β ∈ UG (cA σ) (dbl (incM F Y.J)) := by
  have hF := frameEq_adelic (F := F) hb
  have h1 : (incM F (b⁻¹).1)ᵀ * (incM F b.1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, incM_mul_inv, Matrix.transpose_one]
  have h2 : (incM F b.1).map (cA σ) * (incM F (b⁻¹).1).map (cA σ) = 1 := by
    rw [← map_cA_mul, incM_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hβ' : βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ)) := hβ
  have hN : (nM β)ᵀ * Matrix.fromBlocks 0 1 ((((ε : ℤ) : AE F E)) • 1) 0 * (nM β).map (cA σ) =
      Matrix.fromBlocks 0 1 ((((ε : ℤ) : AE F E)) • 1) 0 := by
    rw [nM_form, hβ', add_neg_cancel]
  show (incM F b.1 * nM β * incM F (b⁻¹).1)ᵀ * dbl (incM F Y.J) *
    (incM F b.1 * nM β * incM F (b⁻¹).1).map (cA σ) = dbl (incM F Y.J)
  rw [map_cA_mul, map_cA_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  calc (incM F (b⁻¹).1)ᵀ * ((nM β)ᵀ * (incM F b.1)ᵀ) * dbl (incM F Y.J) *
        ((incM F b.1).map (cA σ) * (nM β).map (cA σ) * (incM F (b⁻¹).1).map (cA σ))
      = (incM F (b⁻¹).1)ᵀ * ((nM β)ᵀ * ((incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ)) *
          (nM β).map (cA σ)) * (incM F (b⁻¹).1).map (cA σ) := by simp only [Matrix.mul_assoc]
    _ = (incM F (b⁻¹).1)ᵀ * ((incM F b.1)ᵀ * dbl (incM F Y.J) * (incM F b.1).map (cA σ)) *
          (incM F (b⁻¹).1).map (cA σ) := by rw [hF, hN]
    _ = ((incM F (b⁻¹).1)ᵀ * (incM F b.1)ᵀ) * dbl (incM F Y.J) *
          ((incM F b.1).map (cA σ) * (incM F (b⁻¹).1).map (cA σ)) := by simp only [Matrix.mul_assoc]
    _ = dbl (incM F Y.J) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

variable (σ Y) in

def nbE (b : GL (Fin n ⊕ Fin n) E) (β : nA σ Y b) : G2 σ Y := by
  classical
  exact if h : nU b β.1 ∈ UG (cA σ) (dbl (incM F Y.J)) then ⟨nU b β.1, h⟩ else 1

theorem inFrame_nU {b : GL (Fin n ⊕ Fin n) E} (β : Matrix (Fin n) (Fin n) (AE F E))
    (h : nU b β ∈ UG (cA σ) (dbl (incM F Y.J))) : inFrame (σ := σ) (Y := Y) b ⟨nU b β, h⟩ = nM β := by
  show incM F (b⁻¹).1 * (incM F b.1 * nM β * incM F (b⁻¹).1) * incM F b.1 = nM β
  simp only [Matrix.mul_assoc]
  rw [incM_inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, incM_inv_mul, Matrix.one_mul]

theorem cond_of_inFrame {b : GL (Fin n ⊕ Fin n) E} {ε : ℤˣ} (hb : FrameEq σ Y b ε) (x : G2 σ Y)
    (β : Matrix (Fin n) (Fin n) (AE F E)) (hx : inFrame b x = nM β) : β ∈ nCond σ n ε := by
  have hF := frameEq_adelic (F := F) hb
  have hU : (mat2 x)ᵀ * dbl (incM F Y.J) * (mat2 x).map (cA σ) = dbl (incM F Y.J) := x.2
  rw [matrix_eq_frame_conjugate b x, hx] at hU
  have h1 : (incM F b.1)ᵀ * (incM F (b⁻¹).1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, incM_inv_mul, Matrix.transpose_one]
  have h2 : (incM F (b⁻¹).1).map (cA σ) * (incM F b.1).map (cA σ) = 1 := by
    rw [← map_cA_mul, incM_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hN : (nM β)ᵀ * Matrix.fromBlocks 0 1 ((((ε : ℤ) : AE F E)) • 1) 0 * (nM β).map (cA σ) =
      Matrix.fromBlocks 0 1 ((((ε : ℤ) : AE F E)) • 1) 0 := by
    rw [← hF]
    conv_rhs => rw [← hU]
    rw [map_cA_mul, map_cA_mul, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [h2, Matrix.mul_one, ← Matrix.mul_assoc (incM F b.1)ᵀ (incM F (b⁻¹).1)ᵀ, h1, Matrix.one_mul]
  rw [nM_form] at hN
  have h3 := (Matrix.fromBlocks_inj.1 hN).2.2.2
  show βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ))
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h3

theorem mem_nA_iff {b : GL (Fin n ⊕ Fin n) E} {ε : ℤˣ} (hσ : ∀ a, σ (σ a) = a) (hb : FrameEq σ Y b ε)
    (β : Matrix (Fin n) (Fin n) (AE F E)) : β ∈ nA σ Y b ↔ β ∈ nCond σ n ε := by
  constructor
  · intro h
    refine (AddSubgroup.closure_le (nCond σ n ε)).2 ?_ h
    rintro γ ⟨x, hx⟩
    exact cond_of_inFrame hb x γ hx
  · intro h
    exact AddSubgroup.subset_closure ⟨⟨nU b β, nU_mem hσ hb h⟩, inFrame_nU β _⟩

theorem nbE_mem {b : GL (Fin n ⊕ Fin n) E} (hσ : ∀ a, σ (σ a) = a) (hb : IsFrame2 σ Y b) (β : nA σ Y b) :
    nU b β.1 ∈ UG (cA σ) (dbl (incM F Y.J)) := by
  obtain ⟨⟨ε, hε⟩, -⟩ := hb
  exact nU_mem hσ hε ((mem_nA_iff hσ hε β.1).1 β.2)

theorem nbE_eq {b : GL (Fin n ⊕ Fin n) E} (hσ : ∀ a, σ (σ a) = a) (hb : IsFrame2 σ Y b) :
    nbE σ Y b = fun β => ⟨nU b β.1, nbE_mem hσ hb β⟩ := by
  funext β
  simp only [nbE, dif_pos (nbE_mem hσ hb β)]

theorem isNMap_nbE {b : GL (Fin n ⊕ Fin n) E} (hσ : ∀ a, σ (σ a) = a) (hb : IsFrame2 σ Y b) :
    IsNMap b (nbE σ Y b) := by
  intro β
  rw [nbE_eq hσ hb]
  exact inFrame_nU β.1 _

theorem inFrame_injective (b : GL (Fin n ⊕ Fin n) E) : Function.Injective (inFrame (σ := σ) (Y := Y) b) := by
  intro x y h
  have hx := matrix_eq_frame_conjugate b x
  have hy := matrix_eq_frame_conjugate b y
  exact Subtype.ext (Units.ext (hx.trans (h ▸ hy.symm)))

theorem nb_unique {b : GL (Fin n ⊕ Fin n) E} {nb nb' : nA σ Y b → G2 σ Y} (h : IsNMap b nb) (h' : IsNMap b nb') :
    nb = nb' := funext fun β => inFrame_injective b ((h β).trans (h' β).symm)

theorem nb_add {b : GL (Fin n ⊕ Fin n) E} {nb : nA σ Y b → G2 σ Y} (h : IsNMap b nb) (β γ : nA σ Y b) :
    nb (β + γ) = nb β * nb γ := by
  refine inFrame_injective b ?_
  rw [inFrame_mul, h, h, h]
  exact (nM_mul β.1 γ.1).symm

theorem nb_zero {b : GL (Fin n ⊕ Fin n) E} {nb : nA σ Y b → G2 σ Y} (h : IsNMap b nb) : nb 0 = 1 := by
  refine inFrame_injective b ?_
  rw [h, inFrame_one]
  exact nM_zero

theorem nb_comm {b : GL (Fin n ⊕ Fin n) E} {nb : nA σ Y b → G2 σ Y} (h : IsNMap b nb) (β γ : nA σ Y b) :
    nb β * nb γ = nb γ * nb β := by
  rw [← nb_add h, ← nb_add h, add_comm]

theorem continuous_nM : Continuous (nM (F := F) (E := E) (n := n)) :=
  continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const

theorem nb_continuous {b : GL (Fin n ⊕ Fin n) E} (hσ : ∀ a, σ (σ a) = a) (hb : IsFrame2 σ Y b)
    {nb : nA σ Y b → G2 σ Y} (h : IsNMap b nb) : Continuous nb := by
  rw [nb_unique h (isNMap_nbE hσ hb), nbE_eq hσ hb]
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (continuous_const.matrix_mul (continuous_nM.comp continuous_subtype_val)).matrix_mul continuous_const
  · exact (continuous_const.matrix_mul (continuous_nM.comp continuous_subtype_val.neg)).matrix_mul continuous_const

variable (σ Y) in

def nRat (b : GL (Fin n ⊕ Fin n) E) : AddSubgroup (nA σ Y b) where
  carrier := {β | ∃ T, β.1 = incM F T}
  add_mem' := by
    rintro a c ⟨T, hT⟩ ⟨T', hT'⟩
    exact ⟨T + T', by rw [incM_add, ← hT, ← hT']; rfl⟩
  zero_mem' := ⟨0, by rw [incM_zero]; rfl⟩
  neg_mem' := by
    rintro a ⟨T, hT⟩
    exact ⟨-T, by rw [incM_neg, ← hT]; rfl⟩

theorem mem_nF_iff {b : GL (Fin n ⊕ Fin n) E} (β : nA σ Y b) : β ∈ nF σ Y b ↔ ∃ T, β.1 = incM F T := by
  constructor
  · intro h
    exact (AddSubgroup.closure_le (nRat σ Y b)).2 (fun γ hγ => hγ) h
  · intro h
    exact AddSubgroup.subset_closure h

omit [NumberField E] in
theorem incM_mul' {α β γ : Type} [Fintype β] (X : Matrix α β E) (Z : Matrix β γ E) :
    incM F (X * Z) = incM F X * incM F Z := by
  simp only [incM]
  exact Matrix.map_mul

omit [NumberField E] in
theorem incM_nM (T : Matrix (Fin n) (Fin n) E) :
    incM F (Matrix.fromBlocks 1 T 0 1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) = nM (incM F T) := by
  simp only [incM, nM, Matrix.fromBlocks_map]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)]

theorem nb_rat {b : GL (Fin n ⊕ Fin n) E} {nb : nA σ Y b → G2 σ Y} (h : IsNMap b nb) (γ : nA σ Y b)
    (hγ : γ ∈ nF σ Y b) : nb γ ∈ rat2 σ Y := by
  obtain ⟨T, hT⟩ := (mem_nF_iff γ).1 hγ
  let gE : GL (Fin n ⊕ Fin n) E :=
    ⟨b.1 * Matrix.fromBlocks 1 T 0 1 * (b⁻¹).1, b.1 * Matrix.fromBlocks 1 (-T) 0 1 * (b⁻¹).1, by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (b⁻¹).1 b.1, Units.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.fromBlocks _ _ _ _),
        Matrix.fromBlocks_multiply]
      simp, by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (b⁻¹).1 b.1, Units.inv_mul, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.fromBlocks _ _ _ _),
        Matrix.fromBlocks_multiply]
      simp⟩
  refine Subgroup.mem_subgroupOf.2 ⟨gE, Units.ext ?_⟩
  show (b.1 * Matrix.fromBlocks 1 T 0 1 * (b⁻¹).1).map (inclR (F := F) (AF F)) = mat2 (nb γ)
  rw [matrix_eq_frame_conjugate b, h γ, hT]
  show incM F (b.1 * Matrix.fromBlocks 1 T 0 1 * (b⁻¹).1) = _
  rw [incM_mul', incM_mul', incM_nM]
  rfl

theorem isClosed_nCond (ε : ℤˣ) : IsClosed (nCond σ n ε : Set (Matrix (Fin n) (Fin n) (AE F E))) := by
  have hc : Continuous fun y : Matrix (Fin n) (Fin n) (AE F E) => -((((ε : ℤ) : AE F E)) • y.map (cA σ)) :=
    ((continuous_id.matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)).const_smul (((ε : ℤ) : AE F E))).neg
  exact isClosed_eq continuous_id.matrix_transpose hc

theorem isClosed_nA {b : GL (Fin n ⊕ Fin n) E} (hσ : ∀ a, σ (σ a) = a) (hb : IsFrame2 σ Y b) :
    IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) := by
  obtain ⟨⟨ε, hε⟩, -⟩ := hb
  have h : (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) = nCond σ n ε := by
    ext β
    exact mem_nA_iff hσ hε β
  rw [h]
  exact isClosed_nCond ε

theorem nA_top {b : GL (Fin n ⊕ Fin n) E} (hσ : ∀ a, σ (σ a) = a) (hb : IsFrame2 σ Y b) :
    LocallyCompactSpace (nA σ Y b) ∧ SecondCountableTopology (nA σ Y b) ∧ T2Space (nA σ Y b) ∧ BorelSpace (nA σ Y b) :=
  ⟨(isClosed_nA hσ hb).isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsInducing.subtypeVal.secondCountableTopology, inferInstance, Subtype.borelSpace _⟩

def nFtoRat {b : GL (Fin n ⊕ Fin n) E} (γ : nF σ Y b) : ratMx F E n n :=
  ⟨γ.1.1, mem_ratMx.2 (((mem_nF_iff γ.1).1 γ.2).elim fun T hT => ⟨T, hT.symm⟩)⟩

theorem nFtoRat_injective {b : GL (Fin n ⊕ Fin n) E} : Function.Injective (nFtoRat (σ := σ) (Y := Y) (b := b)) :=
  fun a c h => by
    have h1 : a.1.1 = c.1.1 := congrArg (fun r : ratMx F E n n => (r : Mx F E n n)) h
    exact Subtype.ext (Subtype.ext h1)

instance nF_discrete {b : GL (Fin n ⊕ Fin n) E} : DiscreteTopology (nF σ Y b) :=
  DiscreteTopology.of_continuous_injective
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) nFtoRat_injective

instance nF_countable {b : GL (Fin n ⊕ Fin n) E} : Countable (nF σ Y b) := nFtoRat_injective.countable

def prj (σ : E →ₐ[F] E) (ε : ℤˣ) (x : Matrix (Fin n) (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E) :=
  inclR (F := F) (AF F) (2⁻¹ : E) • (x - (((ε : ℤ) : AE F E)) • (x.map (cA σ))ᵀ)

omit [NumberField E] in
theorem cA_inclR' (σ : E →ₐ[F] E) (x : E) :
    cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] σ x
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

omit [NumberField E] in
theorem cA_cA' (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ
      (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [NumberField E] in
theorem cA_half : cA σ (inclR (F := F) (AF F) (2⁻¹ : E)) = inclR (F := F) (AF F) (2⁻¹ : E) := by
  rw [cA_inclR', map_inv₀, map_ofNat]

omit [NumberField E] in
theorem cA_int (z : ℤ) : cA σ ((z : ℤ) : AE F E) = ((z : ℤ) : AE F E) := map_intCast _ z

omit [NumberField E] in
theorem eps_sq (ε : ℤˣ) : (((ε : ℤ) : AE F E)) * (((ε : ℤ) : AE F E)) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

theorem half_two : inclR (F := F) (AF F) (2⁻¹ : E) * 2 = 1 := by
  rw [show (2 : AE F E) = inclR (F := F) (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul,
    inv_mul_cancel₀ (two_ne_zero : (2 : E) ≠ 0), map_one]

theorem prj_mem (hσ : ∀ a, σ (σ a) = a) (ε : ℤˣ) (x : Matrix (Fin n) (Fin n) (AE F E)) : prj σ ε x ∈ nCond σ n ε := by
  show (prj σ ε x)ᵀ = -((((ε : ℤ) : AE F E)) • (prj σ ε x).map (cA σ))
  have hcc := cA_cA' σ hσ
  have he := eps_sq (F := F) (E := E) ε
  ext i j
  simp only [prj, Matrix.transpose_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.neg_apply,
    smul_eq_mul, map_mul, map_sub, cA_half, cA_int, hcc]
  linear_combination (-(inclR (F := F) (AF F) (2⁻¹ : E) * x j i)) * he

theorem prj_of_mem (hσ : ∀ a, σ (σ a) = a) {ε : ℤˣ} {x : Matrix (Fin n) (Fin n) (AE F E)} (hx : x ∈ nCond σ n ε) :
    prj σ ε x = x := by
  have hx' : xᵀ = -((((ε : ℤ) : AE F E)) • x.map (cA σ)) := hx
  have hcc := cA_cA' σ hσ
  have he := eps_sq (F := F) (E := E) ε
  have h2 := half_two (F := F) (E := E)
  ext i j
  have hij : x i j = -((((ε : ℤ) : AE F E)) * cA σ (x j i)) := by
    have := congrFun (congrFun hx' j) i
    simpa [Matrix.transpose_apply] using this
  have hji : cA σ (x j i) = -((((ε : ℤ) : AE F E)) * x i j) := by
    have := congrArg (cA σ) (congrFun (congrFun hx' i) j)
    simpa [Matrix.transpose_apply, map_neg, map_mul, cA_int, hcc] using this
  simp only [prj, Matrix.transpose_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, smul_eq_mul, hji]
  linear_combination (inclR (F := F) (AF F) (2⁻¹ : E) * x i j) * he + x i j * h2

theorem prj_add (ε : ℤˣ) (x y : Matrix (Fin n) (Fin n) (AE F E)) : prj σ ε (x + y) = prj σ ε x + prj σ ε y := by
  ext i j
  simp only [prj, Matrix.transpose_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply,
    smul_eq_mul, map_add]
  ring

theorem continuous_prj (ε : ℤˣ) : Continuous (prj (F := F) (E := E) (n := n) σ ε) := by
  unfold prj
  exact (continuous_id.sub ((continuous_id.matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)).matrix_transpose.const_smul
    (((ε : ℤ) : AE F E)))).const_smul (inclR (F := F) (AF F) (2⁻¹ : E))

theorem prj_incM (ε : ℤˣ) (X : Matrix (Fin n) (Fin n) E) :
    prj σ ε (incM F X) = incM F ((2⁻¹ : E) • (X - ((ε : ℤ) : E) • (X.map σ)ᵀ)) := by
  ext i j
  simp only [prj, incM, Matrix.transpose_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, smul_eq_mul,
    map_mul, map_sub, cA_inclR', inclR_int]

theorem nF_cocompact {b : GL (Fin n ⊕ Fin n) E} (hσ : ∀ a, σ (σ a) = a) (hb : IsFrame2 σ Y b) :
    ∃ K : Set (nA σ Y b), IsCompact K ∧ ∀ x, ∃ γ ∈ nF σ Y b, γ + x ∈ K := by
  obtain ⟨⟨ε, hε⟩, -⟩ := hb
  obtain ⟨K, hK, hc⟩ := ratMx_cocompact (F := F) (E := E) n n
  let P : Matrix (Fin n) (Fin n) (AE F E) → nA σ Y b := fun x => ⟨prj σ ε x, (mem_nA_iff hσ hε _).2 (prj_mem hσ ε x)⟩
  have hP : Continuous P := (continuous_prj ε).subtype_mk _
  refine ⟨P '' K, hK.image hP, fun x => ?_⟩
  obtain ⟨γ, hγ, hγK⟩ := hc x.1
  obtain ⟨T, rfl⟩ := mem_ratMx.1 hγ
  refine ⟨P (incM F T), (mem_nF_iff _).2 ⟨_, prj_incM ε T⟩, incM F T + x.1, hγK, ?_⟩
  apply Subtype.ext
  show prj σ ε (incM F T + x.1) = prj σ ε (incM F T) + x.1
  rw [prj_add, prj_of_mem hσ ((mem_nA_iff hσ hε _).1 x.2)]

theorem aesm_of_continuous {b : GL (Fin n ⊕ Fin n) E} (hσ : ∀ a, σ (σ a) = a) (hb : IsFrame2 σ Y b)
    (lam : Measure (nA σ Y b)) (𝓖 : Set (nA σ Y b)) {u : nA σ Y b × (Fin n → Fin n → ℝ) → ℂ} (hu : Continuous u) :
    AEStronglyMeasurable u ((lam.restrict 𝓖).prod volume) := by
  obtain ⟨-, hsc, -, hbo⟩ := nA_top hσ hb
  exact hu.aestronglyMeasurable

theorem sigma_sigma_of_good {B : Base F E} (hB : B.IsGood σ) (a : E) : σ (σ a) = a := by
  obtain ⟨-, -, -, h⟩ := hB.cm
  let τ : E →+* ℂ := Classical.arbitrary _
  apply τ.injective
  rw [h, h, star_star]

theorem coefData_exists {B : Base F E} (hB : B.IsGood σ) {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) :
    ∃ nb lam 𝓖, CoefData (σ := σ) (Y := Y) b nb lam 𝓖 := by
  have hσ := sigma_sigma_of_good hB
  obtain ⟨hlc, hsc, ht2, hbo⟩ := nA_top hσ hb
  obtain ⟨K, hK, hc⟩ := nF_cocompact hσ hb
  obtain ⟨lam, 𝓖, hlam, h𝓖, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (nA σ Y b) (nF σ Y b) K hK hc).1
  exact ⟨nbE σ Y b, lam, 𝓖, isNMap_nbE hσ hb, hlam, h𝓖, h1⟩

theorem coefEx : CoefEx := fun _F _E _ _ _ _ _ _σ d => coefData_exists d.ok.good d.ok.frame

end PositivityTheory.SiegelWeilFormula.kfour

end
