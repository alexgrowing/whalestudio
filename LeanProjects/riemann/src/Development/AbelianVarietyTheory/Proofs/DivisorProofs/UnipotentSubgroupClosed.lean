import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.UnipSpClosed

open Matrix GlobalTheory.ThKLiftCusp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mat_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) :
    mat (g * h) = mat g * mat h := rfl

theorem mat_inv_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) :
    mat g⁻¹ * mat g = 1 := by
  show ((g⁻¹ : UA σ J).1.1) * g.1.1 = 1
  rw [← Units.val_mul]
  show (((g⁻¹ * g : UA σ J) : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1
  simp

theorem mat_one' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} :
    mat (1 : UA σ J) = 1 := rfl

theorem formA_add (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x x' y : Fin d → AE F E) :
    formA σ J (x + x') y = formA σ J x y + formA σ J x' y := by
  simp only [formA, add_dotProduct]

theorem formA_neg (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x y : Fin d → AE F E) :
    formA σ J (-x) y = -formA σ J x y := by
  simp only [formA, neg_dotProduct]

theorem formA_zero (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (y : Fin d → AE F E) :
    formA σ J 0 y = 0 := by
  simp only [formA, zero_dotProduct]

variable (σ : E →ₐ[F] E)

def carrierSet {d j : ℕ} (W : Spc F E d) (Y : Matrix (Fin d) (Fin j) E) : Set (UA σ W.J) :=
  {u | mat u * incM F Y = incM F Y ∧
    (∀ z, (∀ k, formA σ W.J z (incV F fun i => Y i k) = 0) → ∃ a, mat u *ᵥ z = z + incM F Y *ᵥ a) ∧
    ∀ z k, formA σ W.J (mat u *ᵥ z - z) (incV F fun i => Y i k) = 0}

def carrierSub {d j : ℕ} (W : Spc F E d) (Y : Matrix (Fin d) (Fin j) E) : Subgroup (UA σ W.J) where
  carrier := carrierSet σ W Y
  one_mem' := ⟨by rw [mat_one', Matrix.one_mul],
    fun z _ => ⟨0, by rw [mat_one', Matrix.one_mulVec, mulVec_zero, add_zero]⟩,
    fun z k => by rw [mat_one', Matrix.one_mulVec, sub_self, formA_zero]⟩
  mul_mem' := by
    rintro u v ⟨hu1, hu2, hu3⟩ ⟨hv1, hv2, hv3⟩
    refine ⟨by rw [mat_mul', Matrix.mul_assoc, hv1, hu1], fun z hz => ?_, fun z k => ?_⟩
    · obtain ⟨a, ha⟩ := hv2 z hz
      obtain ⟨b, hb⟩ := hu2 z hz
      refine ⟨b + a, ?_⟩
      rw [mat_mul', ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, hb, Matrix.mulVec_mulVec, hu1,
        Matrix.mulVec_add, add_assoc]
    · have e : mat (u * v) *ᵥ z - z = (mat u *ᵥ (mat v *ᵥ z) - mat v *ᵥ z) + (mat v *ᵥ z - z) := by
        rw [mat_mul', ← Matrix.mulVec_mulVec]; abel
      rw [e, formA_add, hu3, hv3, add_zero]
  inv_mem' := by
    rintro u ⟨hu1, hu2, hu3⟩
    have hinv : ∀ z, mat u *ᵥ (mat u⁻¹ *ᵥ z) = z := fun z => by
      rw [Matrix.mulVec_mulVec]
      have : mat u * mat u⁻¹ = 1 := by
        rw [← mat_mul', mul_inv_cancel, mat_one']
      rw [this, Matrix.one_mulVec]
    have h3 : ∀ z k, formA σ W.J (mat u⁻¹ *ᵥ z - z) (incV F fun i => Y i k) = 0 := fun z k => by
      have e := hu3 (mat u⁻¹ *ᵥ z) k
      rw [hinv] at e
      rw [← neg_sub, formA_neg, e, neg_zero]
    refine ⟨?_, fun z hz => ?_, h3⟩
    · conv_lhs => rw [← hu1]
      rw [← Matrix.mul_assoc, mat_inv_mul', Matrix.one_mul]
    · have hz' : ∀ k, formA σ W.J (mat u⁻¹ *ᵥ z) (incV F fun i => Y i k) = 0 := fun k => by
        have e : mat u⁻¹ *ᵥ z = (mat u⁻¹ *ᵥ z - z) + z := by abel
        rw [e, formA_add, h3, hz, add_zero]
      obtain ⟨a, ha⟩ := hu2 _ hz'
      rw [hinv] at ha
      refine ⟨-a, ?_⟩
      calc mat u⁻¹ *ᵥ z = (mat u⁻¹ *ᵥ z + incM F Y *ᵥ a) - incM F Y *ᵥ a := by abel
        _ = z + -(incM F Y *ᵥ a) := by rw [← ha]; abel
        _ = z + incM F Y *ᵥ -a := by rw [Matrix.mulVec_neg]

theorem unipSp_eq {d j : ℕ} (W : Spc F E d) (Y : Matrix (Fin d) (Fin j) E) :
    unipSp σ W Y = carrierSub σ W Y := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun u hu => hu
  · intro u hu
    exact Subgroup.subset_closure hu

variable [T2Space (AE F E)] [IsTopologicalRing (AE F E)] in
theorem isClosed_carrierSet {d j : ℕ} (W : Spc F E d) (Y : Matrix (Fin d) (Fin j) E)
    (hY : Function.Injective Y.mulVec) : IsClosed (carrierSet σ W Y) := by

  have hker : LinearMap.ker (Matrix.mulVecLin Y) = ⊥ := LinearMap.ker_eq_bot.2 hY
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  set L := LinearMap.toMatrix' g with hL
  have hLY : L * Y = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have hLYA : incM F L * incM F Y = 1 := by
    simp only [incM]
    rw [← Matrix.map_mul, hLY, Matrix.map_one _ (map_zero _) (map_one _)]
  have hspan : ∀ w : Fin d → AE F E, (∃ a, w = incM F Y *ᵥ a) ↔ (incM F Y * incM F L) *ᵥ w = w := by
    intro w
    constructor
    · rintro ⟨a, rfl⟩
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hLYA, Matrix.mul_one]
    · intro h
      exact ⟨incM F L *ᵥ w, by rw [Matrix.mulVec_mulVec, h]⟩
  have hm : Continuous fun u : UA σ W.J => mat u := Units.continuous_val.comp continuous_subtype_val
  have h1 : IsClosed {u : UA σ W.J | mat u * incM F Y = incM F Y} :=
    isClosed_eq (hm.matrix_mul continuous_const) continuous_const
  have hd : ∀ z : Fin d → AE F E, Continuous fun u : UA σ W.J => mat u *ᵥ z - z :=
    fun z => (hm.matrix_mulVec continuous_const).sub continuous_const
  have h2 : ∀ z : Fin d → AE F E, IsClosed {u : UA σ W.J | (∀ k, formA σ W.J z (incV F fun i => Y i k) = 0) →
      ∃ a, mat u *ᵥ z = z + incM F Y *ᵥ a} := by
    intro z
    by_cases hz : ∀ k, formA σ W.J z (incV F fun i => Y i k) = 0
    · have : {u : UA σ W.J | (∀ k, formA σ W.J z (incV F fun i => Y i k) = 0) →
          ∃ a, mat u *ᵥ z = z + incM F Y *ᵥ a} =
          {u | (incM F Y * incM F L) *ᵥ (mat u *ᵥ z - z) = mat u *ᵥ z - z} := by
        ext u
        simp only [Set.mem_setOf_eq, ← hspan, sub_eq_iff_eq_add']
        exact ⟨fun h => h hz, fun h _ => h⟩
      rw [this]
      exact isClosed_eq (continuous_const.matrix_mulVec (hd z)) (hd z)
    · have : {u : UA σ W.J | (∀ k, formA σ W.J z (incV F fun i => Y i k) = 0) →
          ∃ a, mat u *ᵥ z = z + incM F Y *ᵥ a} = Set.univ := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact fun h => absurd h hz
      rw [this]
      exact isClosed_univ
  have h3 : ∀ (z : Fin d → AE F E) (k : Fin j),
      IsClosed {u : UA σ W.J | formA σ W.J (mat u *ᵥ z - z) (incV F fun i => Y i k) = 0} := by
    intro z k
    refine isClosed_eq ?_ continuous_const
    simp only [formA]
    exact Continuous.dotProduct (hd z) continuous_const
  have : carrierSet σ W Y = {u : UA σ W.J | mat u * incM F Y = incM F Y} ∩
      ((⋂ z : Fin d → AE F E, {u : UA σ W.J | (∀ k, formA σ W.J z (incV F fun i => Y i k) = 0) →
        ∃ a, mat u *ᵥ z = z + incM F Y *ᵥ a}) ∩
      ⋂ z : Fin d → AE F E, ⋂ k : Fin j,
        {u : UA σ W.J | formA σ W.J (mat u *ᵥ z - z) (incV F fun i => Y i k) = 0}) := by
    ext u
    simp only [carrierSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [this]
  exact h1.inter ((isClosed_iInter h2).inter (isClosed_iInter fun z => isClosed_iInter fun k => h3 z k))

theorem isClosed_unipSp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s →
    ∀ (j : ℕ) (Y : Matrix (Fin d) (Fin j) E), 1 ≤ j → Function.Injective Y.mulVec →
      (∀ k l, form σ W.J (fun a => Y a k) (fun a => Y a l) = 0) →
      IsClosed (GlobalTheory.ThKLiftCusp.unipSp σ W Y : Set (UA σ W.J)) := by
  intro F E _ _ _ _ _ σ _ _ d _ _ W _ j Y _ hY _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  rw [unipSp_eq]
  exact isClosed_carrierSet σ W Y hY

end GlobalTheory.UnipSpClosed

end
