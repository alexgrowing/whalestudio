import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormaliseMeanSquareOfCocompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixModel

variable {D : D7}

scoped infixl:70 " ⬝ " => HMul.hMul

def rat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n := M.map (incA D)

def adj {m n : ℕ} (x : Mx D m n) : Mx D n m := (x.map (cA D))ᵀ

def ratMx (D : D7) (m n : ℕ) : AddSubgroup (Mx D m n) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range

def half (D : D7) : AE D := incA D (1 / 2)

def gA (S : HSp D) : Mx D S.rank S.rank := rat S.gram

def giA (S : HSp D) : Mx D S.rank S.rank := rat S.gram⁻¹

section Basic

variable {l m n : ℕ}

theorem ratL_eq (V W : HSp D) : ratL V W = ratMx D V.rank W.rank := rfl

theorem ratW_eq (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) : ratW V W γ = rat γ := rfl

theorem mem_ratMx {x : Mx D m n} : x ∈ ratMx D m n ↔ ∃ γ, rat γ = x := Iff.rfl

theorem rat_mem (γ : Matrix (Fin m) (Fin n) D.host.E) : rat γ ∈ ratMx D m n := ⟨γ, rfl⟩

theorem incA_injective : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem rat_injective : Function.Injective (rat : Matrix (Fin m) (Fin n) D.host.E → Mx D m n) :=
  fun _ _ h => Matrix.map_injective incA_injective h

@[simp] theorem rat_mul (M : Matrix (Fin l) (Fin m) D.host.E) (N : Matrix (Fin m) (Fin n) D.host.E) :
    rat (M * N) = rat M ⬝ rat N := Matrix.map_mul

@[simp] theorem rat_add (M N : Matrix (Fin m) (Fin n) D.host.E) : rat (M + N) = rat M + rat N :=
  Matrix.map_add _ (map_add (incA D)) M N

@[simp] theorem rat_sub (M N : Matrix (Fin m) (Fin n) D.host.E) : rat (M - N) = rat M - rat N :=
  Matrix.map_sub _ (map_sub (incA D)) M N

@[simp] theorem rat_neg (M : Matrix (Fin m) (Fin n) D.host.E) : rat (-M) = -rat M := by
  funext i j; exact map_neg (incA D) (M i j)

@[simp] theorem rat_zero : rat (0 : Matrix (Fin m) (Fin n) D.host.E) = 0 :=
  Matrix.map_zero _ (map_zero (incA D))

@[simp] theorem rat_one : rat (1 : Matrix (Fin n) (Fin n) D.host.E) = 1 :=
  Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))

@[simp] theorem rat_smul (a : D.host.E) (M : Matrix (Fin m) (Fin n) D.host.E) : rat (a • M) = incA D a • rat M := by
  funext i j; exact map_mul (incA D) a (M i j)

theorem rat_conjTranspose (M : Matrix (Fin m) (Fin n) D.host.E) : rat Mᴴ = adj (rat M) := rfl

theorem cT_sig (M : Matrix (Fin m) (Fin n) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := rfl

@[simp] theorem adj_mul (x : Mx D l m) (y : Mx D m n) : adj (x ⬝ y) = adj y ⬝ adj x :=
  Formalism.UG.cT_mul (cA D) x y

@[simp] theorem adj_add (x y : Mx D m n) : adj (x + y) = adj x + adj y := by
  funext i j; exact map_add (cA D) (x j i) (y j i)

@[simp] theorem adj_sub (x y : Mx D m n) : adj (x - y) = adj x - adj y := by
  funext i j; exact map_sub (cA D) (x j i) (y j i)

@[simp] theorem adj_neg (x : Mx D m n) : adj (-x) = -adj x := by
  funext i j; exact map_neg (cA D) (x j i)

@[simp] theorem adj_zero : adj (0 : Mx D m n) = 0 := by
  funext i j; exact map_zero (cA D)

@[simp] theorem adj_one : adj (1 : Mx D n n) = 1 := Formalism.UG.cT_one (cA D)

@[simp] theorem adj_adj (x : Mx D m n) : adj (adj x) = x := by
  funext i j; exact cA_cA (x i j)

@[simp] theorem adj_smul (a : AE D) (x : Mx D m n) : adj (a • x) = cA D a • adj x := by
  funext i j; exact map_mul (cA D) a (x j i)

theorem trace_adj (x : Mx D n n) : (adj x).trace = cA D x.trace := by
  simp only [Matrix.trace, map_sum]; rfl

@[simp] theorem cA_half : cA D (half D) = half D := by
  rw [half, GlobalTheory.DualPairCheck.cA_incA]; congr 1; simp

theorem half_add_half : half D + half D = 1 := by
  rw [half, ← map_add, add_halves, map_one]

theorem half_smul_add (x : Mx D m n) : half D • x + half D • x = x := by
  rw [← add_smul, half_add_half, one_smul]

theorem continuous_adj : Continuous (adj : Mx D m n → Mx D n m) :=
  (continuous_id.matrix_map GlobalTheory.FockCompare.ThetaCont.continuous_conj).matrix_transpose

end Basic

section Gram

variable (S : HSp D)

theorem gram_conjTranspose : S.gramᴴ = S.gram := by
  funext i j; exact GlobalTheory.DualPairCheck.gram_star S j i

theorem gram_isUnit_det : IsUnit S.gram.det := isUnit_iff_ne_zero.2 (gram_det_ne S)

theorem gramInv_conjTranspose : (S.gram⁻¹)ᴴ = S.gram⁻¹ := by
  rw [Matrix.conjTranspose_nonsing_inv, gram_conjTranspose]

@[simp] theorem adj_gA : adj (gA S) = gA S := by rw [gA, ← rat_conjTranspose, gram_conjTranspose]

@[simp] theorem adj_giA : adj (giA S) = giA S := by rw [giA, ← rat_conjTranspose, gramInv_conjTranspose]

@[simp] theorem giA_mul_gA : giA S * gA S = 1 := by
  rw [giA, gA, ← rat_mul, Matrix.nonsing_inv_mul _ (gram_isUnit_det S), rat_one]

@[simp] theorem gA_mul_giA : gA S * giA S = 1 := by
  rw [giA, gA, ← rat_mul, Matrix.mul_nonsing_inv _ (gram_isUnit_det S), rat_one]

@[simp] theorem giA_gA_cancel {n : ℕ} (x : Mx D S.rank n) : giA S ⬝ (gA S ⬝ x) = x := by
  rw [← Matrix.mul_assoc, giA_mul_gA, Matrix.one_mul]

@[simp] theorem gA_giA_cancel {n : ℕ} (x : Mx D S.rank n) : gA S ⬝ (giA S ⬝ x) = x := by
  rw [← Matrix.mul_assoc, gA_mul_giA, Matrix.one_mul]

theorem hO_eq_trace (T : HSp D) (x y : WO S T) : hO S T x y = (giA S ⬝ (adj y ⬝ (gA T ⬝ x))).trace := by
  simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
  rfl

end Gram

section Unit

variable (S : HSp D)

theorem mt_unitary (g : GA D S) : adj (mt S g) * (gA S * mt S g) = gA S := by
  rw [← Matrix.mul_assoc]; exact mt_rel S g

theorem mt_mul (g h : GA D S) : mt S (g * h) = mt S g * mt S h := rfl

@[simp] theorem mt_one : mt S 1 = 1 := rfl

theorem mt_inv_mul (g : GA D S) : mt S g⁻¹ * mt S g = 1 := by rw [← mt_mul, inv_mul_cancel, mt_one]

theorem mt_mul_inv (g : GA D S) : mt S g * mt S g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]

theorem mt_inv (g : GA D S) : mt S g⁻¹ = giA S * (adj (mt S g) * gA S) := by
  have h : giA S * (adj (mt S g) * gA S) * mt S g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, mt_unitary, giA_mul_gA]
  rw [← Matrix.one_mul (mt S g⁻¹), ← h, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]

theorem mt_injective : Function.Injective (mt S) := fun _ _ h => Subtype.ext (Units.ext h)

def ofMat (M : Mx D S.rank S.rank) (h : adj M * (gA S * M) = gA S) : GA D S :=
  have h1 : giA S * (adj M * gA S) * M = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, h, giA_mul_gA]
  (⟨⟨M, giA S * (adj M * gA S), mul_eq_one_comm.1 h1, h1⟩, (Matrix.mul_assoc _ _ _).trans h⟩ :
    HR (AF D.host.F) D.sp.cm.sig S.gram)

@[simp] theorem mt_ofMat (M : Mx D S.rank S.rank) (h : adj M * (gA S * M) = gA S) : mt S (ofMat S M h) = M := rfl

theorem mem_GQ_iff (g : GA D S) : g ∈ GQ S ↔ mt S g ∈ ratMx D S.rank S.rank := by
  constructor
  · rintro ⟨γ, -, h⟩
    exact ⟨γ.1, congrArg Units.val h⟩
  · rintro ⟨γ, hγ⟩
    replace hγ : rat γ = mt S g := hγ
    have h : γᴴ * S.gram * γ = S.gram := by
      apply rat_injective
      rw [rat_mul, rat_mul, rat_conjTranspose, hγ]
      exact mt_rel S g
    have h1 : S.gram⁻¹ * (γᴴ * S.gram) * γ = 1 := by
      rw [Matrix.mul_assoc, h, Matrix.nonsing_inv_mul _ (gram_isUnit_det S)]
    exact ⟨⟨γ, _, mul_eq_one_comm.1 h1, h1⟩, h, Units.ext hγ⟩

theorem continuous_mt : Continuous (mt S) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_of_mt {X : Type} [TopologicalSpace X] {φ : X → GA D S} (h : Continuous fun x => mt S (φ x)) :
    Continuous φ := by
  refine Continuous.subtype_mk (f := fun x => matHom S (φ x)) (Units.continuous_iff.2 ⟨h, ?_⟩) _
  have : (fun x => ((matHom S (φ x))⁻¹ : GL _ _).1) = fun x => giA S * (adj (mt S (φ x)) * gA S) :=
    funext fun x => mt_inv S (φ x)
  rw [this]
  exact continuous_const.matrix_mul ((continuous_adj.comp h).matrix_mul continuous_const)

theorem actO_eq (T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h x = mt T h ⬝ x ⬝ mt S g⁻¹ := rfl

end Unit

section Rat

variable {l m n : ℕ}

theorem ratMx_mul {x : Mx D l m} {y : Mx D m n} (hx : x ∈ ratMx D l m) (hy : y ∈ ratMx D m n) :
    x ⬝ y ∈ ratMx D l n := by
  obtain ⟨a, rfl⟩ := mem_ratMx.1 hx
  obtain ⟨b, rfl⟩ := mem_ratMx.1 hy
  exact ⟨a * b, rat_mul a b⟩

theorem ratMx_adj {x : Mx D m n} (hx : x ∈ ratMx D m n) : adj x ∈ ratMx D n m := by
  obtain ⟨a, rfl⟩ := mem_ratMx.1 hx
  exact ⟨aᴴ, rfl⟩

theorem ratMx_smul (a : D.host.E) {x : Mx D m n} (hx : x ∈ ratMx D m n) : incA D a • x ∈ ratMx D m n := by
  obtain ⟨b, rfl⟩ := mem_ratMx.1 hx
  exact ⟨a • b, rat_smul a b⟩

theorem ratMx_one : (1 : Mx D n n) ∈ ratMx D n n := ⟨1, rat_one⟩

end Rat

section Lattice

variable (D) (m n : ℕ)

theorem lattice_Mx : IsTopologicalAddGroup (Mx D m n) ∧ LocallyCompactSpace (Mx D m n) ∧
    SecondCountableTopology (Mx D m n) ∧ T2Space (Mx D m n) ∧ DiscreteTopology (ratMx D m n) ∧
    ∃ K : Set (Mx D m n), IsCompact K ∧ ∀ x : Mx D m n, ∃ γ ∈ ratMx D m n, γ + x ∈ K :=
  GlobalTheory.AdelicMatrixLattice.lattice D (Examples₂.posSpace Examples₂.star_isIntegral m) (Examples₂.posSpace Examples₂.star_isIntegral n)

theorem exists_isCovolOne : ∃ μ 𝓕, IsCovolOne (ratMx D m n) μ 𝓕 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  exact (GlobalTheory.exists_normalise_meanSquare_of_cocompact (Mx D m n) (ratMx D m n) K hK hKc (fun _ => 1) continuous_const
    (fun h => one_ne_zero (congrFun h 0)) (fun _ _ _ => rfl)).1

variable {D m n}

theorem covolOne_measure_eq {μ μ' : Measure (Mx D m n)} {𝓕 𝓕' : Set (Mx D m n)}
    (h : IsCovolOne (ratMx D m n) μ 𝓕) (h' : IsCovolOne (ratMx D m n) μ' 𝓕') : μ' = μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨hμ, hF, h1⟩ := h
  obtain ⟨hμ', hF', h1'⟩ := h'
  have e := Measure.isAddLeftInvariant_eq_smul μ' μ
  have hF2 : IsAddFundamentalDomain (ratMx D m n) 𝓕 μ' := hF.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have h2 : μ' 𝓕 = 1 := (hF2.measure_eq hF').trans h1'
  rw [e, Measure.smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_eq_one] at h2
  rw [e, h2, one_smul]

theorem covolOne_integral_eq {μ μ' : Measure (Mx D m n)} {𝓕 𝓕' : Set (Mx D m n)}
    (h : IsCovolOne (ratMx D m n) μ 𝓕) (h' : IsCovolOne (ratMx D m n) μ' 𝓕') (φ : Mx D m n → ℂ)
    (hφ : ∀ γ ∈ ratMx D m n, ∀ a, φ (γ + a) = φ a) : ∫ a in 𝓕', φ a ∂μ' = ∫ a in 𝓕, φ a ∂μ := by
  obtain rfl := covolOne_measure_eq h h'
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := h.1
  exact h'.2.1.setIntegral_eq h.2.1 fun γ a => hφ γ γ.2 a

theorem covolOne_integrableOn {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (h : IsCovolOne (ratMx D m n) μ 𝓕) (φ : Mx D m n → ℂ) (hc : Continuous φ)
    (hφ : ∀ γ ∈ ratMx D m n, ∀ a, φ (γ + a) = φ a) : IntegrableOn φ 𝓕 μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine Integrable.of_bound hc.measurable.aestronglyMeasurable C (Filter.Eventually.of_forall fun a => ?_)
  obtain ⟨γ, hγ, ha⟩ := hKc a
  rw [← hφ γ hγ a]
  exact hC _ ha

theorem covolOne_integral_add {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (h : IsCovolOne (ratMx D m n) μ 𝓕) (φ : Mx D m n → ℂ)
    (hφ : ∀ γ ∈ ratMx D m n, ∀ a, φ (γ + a) = φ a) (u : Mx D m n) : ∫ a in 𝓕, φ (a + u) ∂μ = ∫ a in 𝓕, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := h.1
  have h1 : IsAddFundamentalDomain (ratMx D m n) (u +ᵥ 𝓕) μ := h.2.1.vadd_of_comm u
  rw [h.2.1.setIntegral_eq h1 (f := φ) fun γ w => hφ γ γ.2 w]
  have h2 := (measurePreserving_add_left μ u).setIntegral_image_emb (measurableEmbedding_addLeft u) φ 𝓕
  simp only [add_comm _ u]
  exact h2.symm

end Lattice

section Product

def trHalf (D : D7) : AE D →+ AF D.host.F where
  toFun z := algebraMap D.host.F (AF D.host.F) (1 / 2) *
    Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * z)
  map_zero' := by rw [mul_zero, map_zero, mul_zero]
  map_add' x y := by rw [mul_add, map_add, mul_add]

theorem symplOH_eq (S T : HSp D) (x y : WO S T) : symplOH S T x y = trHalf D (hO S T x y) := rfl

theorem symplO_eq (S T : HSp D) (x y : WO S T) :
    symplO S T x y = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * hO S T x y) := rfl

theorem symplOH_zero_left (S T : HSp D) (y : WO S T) : symplOH S T 0 y = 0 := by
  rw [symplOH_eq, hO_eq_trace, Matrix.mul_zero, Matrix.mul_zero, Matrix.mul_zero, Matrix.trace_zero, map_zero]

theorem symplOH_zero_right (S T : HSp D) (x : WO S T) : symplOH S T x 0 = 0 := by
  rw [symplOH_eq, hO_eq_trace, adj_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.trace_zero, map_zero]

theorem symplOH_skew (S T : HSp D) (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  rw [symplOH, symplOH, GlobalTheory.OrientedHeis.symplO_skew, mul_neg]

theorem map_mul_eq_zero_left {B : Type} [CommRing B] (φ : AE D →+* B) {l m n : ℕ} {x : Mx D l m} (hx : x.map φ = 0)
    (y : Mx D m n) : (x ⬝ y).map φ = 0 := by
  rw [Matrix.map_mul, hx, Matrix.zero_mul]

theorem map_mul_eq_zero_right {B : Type} [CommRing B] (φ : AE D →+* B) {l m n : ℕ} (x : Mx D l m) {y : Mx D m n}
    (hy : y.map φ = 0) : (x ⬝ y).map φ = 0 := by
  rw [Matrix.map_mul, hy, Matrix.mul_zero]

def sandwich {k l m n : ℕ} (P : Mx D k l) (Q : Mx D m n) : Mx D l m →+ Mx D k n where
  toFun w := P ⬝ w ⬝ Q
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]

theorem sandwich_apply {k l m n : ℕ} (P : Mx D k l) (Q : Mx D m n) (w : Mx D l m) : sandwich P Q w = P ⬝ w ⬝ Q := rfl

theorem continuous_sandwich {k l m n : ℕ} (P : Mx D k l) (Q : Mx D m n) : Continuous (sandwich P Q) :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem map_sandwich {B : Type} [CommRing B] (φ : AE D →+* B) {k l m n : ℕ} (P : Mx D k l) (Q : Mx D m n)
    {w : Mx D l m} (hw : w.map φ = 0) : (sandwich P Q w).map φ = 0 :=
  map_mul_eq_zero_left φ (map_mul_eq_zero_right φ P hw) Q

variable {ψ : AddChar (AF D.host.F) ℂ} {S T S₁ T₁ S₂ T₂ : HSp D}

theorem isThetaFunO_prod (P₁ : Matrix (Fin T₁.rank) (Fin T.rank) D.host.E) (Q₁ : Matrix (Fin S.rank) (Fin S₁.rank) D.host.E)
    (P₂ : Matrix (Fin T₂.rank) (Fin T.rank) D.host.E) (Q₂ : Matrix (Fin S.rank) (Fin S₂.rank) D.host.E)
    (h : ∀ x y : WO S T, symplOH S T x y =
      symplOH S₁ T₁ (sandwich (rat P₁) (rat Q₁) x) (sandwich (rat P₁) (rat Q₁) y) +
        symplOH S₂ T₂ (sandwich (rat P₂) (rat Q₂) x) (sandwich (rat P₂) (rat Q₂) y))
    {f₁ : WO S₁ T₁ → ℂ} {f₂ : WO S₂ T₂ → ℂ} (h₁ : IsThetaFunO ψ S₁ T₁ f₁) (h₂ : IsThetaFunO ψ S₂ T₂ f₂) :
    IsThetaFunO ψ S T fun w => f₁ (sandwich (rat P₁) (rat Q₁) w) * f₂ (sandwich (rat P₂) (rat Q₂) w) where
  quasi γ w := by
    have e₁ : sandwich (rat P₁) (rat Q₁) (ratW T S γ) = ratW T₁ S₁ (P₁ * γ * Q₁) := by
      rw [ratW_eq, ratW_eq, rat_mul, rat_mul]; rfl
    have e₂ : sandwich (rat P₂) (rat Q₂) (ratW T S γ) = ratW T₂ S₂ (P₂ * γ * Q₂) := by
      rw [ratW_eq, ratW_eq, rat_mul, rat_mul]; rfl
    rw [map_add, map_add, h, e₁, e₂, h₁.quasi, h₂.quasi, neg_add, AddChar.map_add_eq_mul]
    ring
  level := by
    obtain ⟨U₁, hU₁, k₁⟩ := h₁.level
    obtain ⟨U₂, hU₂, k₂⟩ := h₂.level
    refine ⟨U₁.comap (sandwich (rat P₁) (rat Q₁)) ⊓ U₂.comap (sandwich (rat P₂) (rat Q₂)),
      (hU₁.preimage (continuous_sandwich _ _)).inter (hU₂.preimage (continuous_sandwich _ _)), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1 (map_sandwich _ _ _ h0)) (sandwich (rat P₁) (rat Q₁) w)
    have e₂ := congrFun (k₂ _ hu.2 (map_sandwich _ _ _ h0)) (sandwich (rat P₂) (rat Q₂) w)
    simp only [heisO] at e₁ e₂ ⊢
    rw [← e₁, ← e₂, h, AddChar.map_add_eq_mul, map_add, map_add]
    ring
  cont := (h₁.cont.comp (continuous_sandwich _ _)).mul (h₂.cont.comp (continuous_sandwich _ _))
  smooth k L hL h0 w := by
    simp only [map_add]
    exact (h₁.smooth k ((sandwich (rat P₁) (rat Q₁)).comp L) ((continuous_sandwich _ _).comp hL)
      (fun t => map_sandwich _ _ _ (h0 t)) _).mul
      (h₂.smooth k ((sandwich (rat P₂) (rat Q₂)).comp L) ((continuous_sandwich _ _).comp hL)
        (fun t => map_sandwich _ _ _ (h0 t)) _)

end Product

end GlobalTheory.MixModel

end
