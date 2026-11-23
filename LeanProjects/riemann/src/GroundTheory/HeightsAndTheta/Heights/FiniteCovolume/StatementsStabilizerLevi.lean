import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVecFixGroup
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsComplementForm

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal

noncomputable section

section Radical

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def unipRadical (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    Subgroup (archUnitary h v) where
  carrier := {g | ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
    vecAt v x₀ w ∧ ∀ z : ι → ℂ, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ∃ c : ℂ, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z + c • vecAt v x₀ w}
  one_mem' w := ⟨by simp, fun z _ => ⟨0, by simp⟩⟩
  mul_mem' {a b} ha hb w := by
    refine ⟨?_, fun z hz => ?_⟩
    · simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, (hb w).1,
        (ha w).1]
    · obtain ⟨c, hc⟩ := (hb w).2 z hz
      obtain ⟨d, hd⟩ := (ha w).2 z hz
      refine ⟨d + c, ?_⟩
      simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hc,
        Matrix.mulVec_add, Matrix.mulVec_smul, hd, (ha w).1, add_smul]
      abel
  inv_mem' {a} ha w := by
    have e : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *
        ((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
      rw [Subgroup.coe_inv, Pi.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hx : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        vecAt v x₀ w = vecAt v x₀ w := by
      conv_lhs => rw [← (ha w).1]
      rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
    refine ⟨hx, fun z hz => ?_⟩
    obtain ⟨c, hc⟩ := (ha w).2 z hz
    refine ⟨-c, ?_⟩
    have := congrArg ((((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ ·) hc
    simp only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
      hx] at this
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, ← this]

omit [NumberField E] in
theorem mem_unipRadical {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {g : archUnitary h v} : g ∈ unipRadical h v x₀ ↔
      ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w ∧
        ∀ z : ι → ℂ, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
          ∃ c : ℂ, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z + c • vecAt v x₀ w :=
  Iff.rfl

omit [NumberField E] in

theorem unipRadical_le_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    unipRadical h v x₀ ≤ vecFixGroup h v x₀ :=
  fun _ hg w => (hg w).1

omit [NumberField E] in

theorem isClosed_unipRadical (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    IsClosed (unipRadical h v x₀ : Set (archUnitary h v)) := by
  have hc : ∀ w, Continuous fun g : archUnitary h v =>
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) :=
    fun w => Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)
  have : (unipRadical h v x₀ : Set (archUnitary h v)) = ⋂ w, ({g : archUnitary h v |
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w} ∩
      ⋂ z ∈ {z : ι → ℂ | star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0},
        (fun g : archUnitary h v => ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z - z) ⁻¹'
          (Submodule.span ℂ {vecAt v x₀ w} : Set (ι → ℂ))) := by
    ext g
    simp only [SetLike.mem_coe, mem_unipRadical, Set.mem_iInter, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_preimage, Submodule.mem_span_singleton]
    refine forall_congr' fun w => and_congr Iff.rfl (forall_congr' fun z => imp_congr_right
      fun _ => ⟨fun ⟨c, hc⟩ => ⟨c, by rw [hc]; abel⟩, fun ⟨c, hc⟩ => ⟨c, by rw [hc]; abel⟩⟩)
  rw [this]
  refine isClosed_iInter fun w => (isClosed_eq ((hc w).matrix_mulVec continuous_const)
    continuous_const).inter (isClosed_biInter fun z _ => ?_)
  exact (Submodule.closed_of_finiteDimensional _).preimage
    (((hc w).matrix_mulVec continuous_const).sub continuous_const)

instance locallyCompactSpace_unipRadical (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    LocallyCompactSpace (unipRadical h v x₀) :=
  (isClosed_unipRadical h v x₀).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance secondCountableTopology_unipRadical (h : HermitianForm F E W) (v : Basis ι E W)
    (x₀ : W) : SecondCountableTopology (unipRadical h v x₀) :=
  TopologicalSpace.Subtype.secondCountableTopology _

end Radical

section Structure

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def StabilizerLevi.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h x₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) →
    ∀ (n : ℕ) (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
    ∃ (i : archUnitary h' v' →* vecFixGroup h v x₀) (q : vecFixGroup h v x₀ →* archUnitary h' v'),
      Continuous i ∧ Continuous q ∧ (∀ m, q (i m) = m) ∧
      (∀ g, q g = 1 ↔ (g : archUnitary h v) ∈ unipRadical h v x₀) ∧
      (∀ m, ((i m : vecFixGroup h v x₀) : archUnitary h v) ∈ vecFixGroup h v w₀) ∧
      ∀ (γ : h.unitaryGroup) (m : h'.unitaryGroup), γ • x₀ = x₀ → γ • w₀ = w₀ →
        (∀ x : hypComplement h x₀ w₀, γ • (x : W) = ((m • x : hypComplement h x₀ w₀) : W)) →
        ((i (archEmbed h' v' m) : vecFixGroup h v x₀) : archUnitary h v) = archEmbed h v γ

def UnipotentModulus.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ w₀ : W, IsHyperbolicPair h x₀ w₀ →
    ∀ (μ : Measure (unipRadical h v x₀)) [μ.IsHaarMeasure],
    ∀ g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀,
      μ.map (fun n : unipRadical h v x₀ => g * (n : archUnitary h v) * g⁻¹) = μ.map Subtype.val

def UnipotentCocompact.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ : W), IsDIntegral h D La → x₀ ∈ La → x₀ ≠ 0 →
    h.toSesq x₀ x₀ = 0 →
    ∃ C : Set (unipRadical h v x₀), IsCompact C ∧ ∀ n : unipRadical h v x₀,
      ∃ δ : unipRadical h v x₀, (δ : archUnitary h v) ∈ vecStabGroup h v La x₀ ∧ δ * n ∈ C

def CongruenceLift.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ w₀ : W), IsDIntegral h D La → x₀ ∈ La →
    IsHyperbolicPair h x₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h x₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) →
    ∃ (D' : ℕ) (La' : AddSubgroup (hypComplement h x₀ w₀)) (G'' : Subgroup h'.unitaryGroup),
      IsDIntegral h' D' La' ∧ G'' ≤ latticeStab h' La' ∧ G''.relIndex (latticeStab h' La') ≠ 0 ∧
      ∀ m ∈ G'', ∀ γ : h.unitaryGroup, γ • x₀ = x₀ → γ • w₀ = w₀ →
        (∀ x : hypComplement h x₀ w₀, γ • (x : W) = ((m • x : hypComplement h x₀ w₀) : W)) →
        γ ∈ latticeStab h La

end Structure

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
