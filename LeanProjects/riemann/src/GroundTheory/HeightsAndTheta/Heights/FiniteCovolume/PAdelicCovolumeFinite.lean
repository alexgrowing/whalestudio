import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsDoubleCoset
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdelicLattices

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem archEmbed_injective (h : HermitianForm F E W) (v : Basis ι E W) :
    Function.Injective (archEmbed h v) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  have h1 : ((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E).map w.embedding = 1 :=
    congrArg
      (fun g : archUnitary h v => (((g : InfinitePlace E → GL ι ℂ) w : GL ι ℂ) : Matrix ι ι ℂ)) hγ
  have h2 : ((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E) = 1 := by
    ext i j
    have := congrFun (congrFun h1 i) j
    rw [Matrix.map_apply] at this
    apply w.embedding.injective
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 : unitaryGroupEquivMatrix h v γ = 1 := Subtype.ext (Units.ext h2)
  rwa [MulEquiv.map_eq_one_iff] at h3

theorem countable_unitaryGroup (h : HermitianForm F E W) (v : Basis ι E W) :
    Countable h.unitaryGroup := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix ι ι E) := inferInstanceAs (Countable (ι → ι → E))
  refine Function.Injective.countable (f := fun γ : h.unitaryGroup =>
    ((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E)) ?_
  intro a b hab
  exact (unitaryGroupEquivMatrix h v).injective (Subtype.ext (Units.ext hab))

theorem AdelicCovolumeFinite.proof (h : HermitianForm F E W) (v : Basis ι E W)
    [FiniteDimensional E W] (h₁ : LatticeOrbitsFinite.Statement h)
    (h₂ : ArithmeticCovolumeFinite.Statement h v) (h₃ : ArchimedeanUnitaryEquiv.Statement h v)
    (h₄ : AdelicLatticeDictionary.Statement h v)
    (h₅ : DoubleCosetCovolume.Statement (unitaryPoints F E (gram h.toSesq v) 𝔸[F])
      (archUnitary h v) (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) :
    AdelicCovolumeFinite.Statement h v := by
  classical
  intro μ _
  obtain ⟨ψ, hψ⟩ := h₃
  obtain ⟨K, D, L, hKc, hKo, hLD, hLeq, hLinj⟩ := h₄
  let e : unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ×
      unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) ≃ₜ*
      archUnitary h v × unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) :=
    { toMulEquiv := MulEquiv.prodCongr ψ.toMulEquiv (MulEquiv.refl _)
      continuous_toFun := (ψ.continuous.comp continuous_fst).prodMk continuous_snd
      continuous_invFun := (ψ.symm.continuous.comp continuous_fst).prodMk continuous_snd }
  let Φ := (adeleSplit h v).trans e
  have hΦ₁ : ∀ γ : h.unitaryGroup, (Φ (hermitianDiagonal h v γ)).1 = archEmbed h v γ :=
    fun γ => hψ γ
  have hΦ₂ : ∀ γ : h.unitaryGroup, (Φ (hermitianDiagonal h v γ)).2 =
      (adeleSplit h v (hermitianDiagonal h v γ)).2 := fun γ => rfl
  haveI := countable_unitaryGroup h v
  haveI : Countable (hermitianDiagonal h v).range := by
    refine Function.Surjective.countable (f := fun γ : h.unitaryGroup =>
      (⟨hermitianDiagonal h v γ, γ, rfl⟩ : (hermitianDiagonal h v).range)) ?_
    rintro ⟨_, γ, rfl⟩
    exact ⟨γ, rfl⟩

  obtain ⟨S₀, hS₀, hS₀cov⟩ := h₁ D
  let r : AddSubgroup W → unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) := fun L₀ => if hL : ∃ y, L y = L₀ then hL.choose else 1
  have hr : ∀ y, L (r (L y)) = L y := fun y => by
    have hL : ∃ y', L y' = L y := ⟨y, rfl⟩
    simp only [r, dif_pos hL]
    exact hL.choose_spec

  have hstab : ∀ (γ : h.unitaryGroup) (s : unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F)),
      γ ∈ latticeStab h (L s) ↔ s⁻¹ * (Φ (hermitianDiagonal h v γ)).2 * s ∈ K := by
    intro γ s
    rw [latticeStab, MulAction.mem_stabilizer_iff, hΦ₂, ← hLeq, eq_comm, hLinj, mul_assoc]
  have hslice : ∀ s : unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F), sliceGroup Φ (hermitianDiagonal h v).range K s =
      archLatticeGroup h v (L s) := by
    intro s
    ext x
    rw [mem_sliceGroup, archLatticeGroup, Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨γ, rfl⟩, hk, rfl⟩
      exact ⟨γ, (hstab γ s).2 hk, (hΦ₁ γ).symm⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨hermitianDiagonal h v γ, ⟨γ, rfl⟩, (hstab γ s).1 hγ, hΦ₁ γ⟩
  obtain ⟨FD, hFD, hfin⟩ := h₅ Φ (hermitianDiagonal h v).range K (hS₀.toFinset.image r) hKc hKo
    (by
      rintro _ ⟨γ, rfl⟩ h1
      rw [hΦ₁, ← (archEmbed h v).map_one] at h1
      rw [archEmbed_injective h v h1, map_one])
    (by
      intro y
      obtain ⟨L₀, hL₀, g, hg⟩ := hS₀cov (L y) (hLD y)
      have hL₀' : L₀ = L ((adeleSplit h v (hermitianDiagonal h v g⁻¹)).2 * y) := by
        rw [hLeq, ← hg, smul_smul, inv_mul_cancel, one_smul]
      have hs : L (r L₀) = L₀ := by rw [hL₀']; exact hr _
      have hk : ((Φ (hermitianDiagonal h v g)).2 * r L₀)⁻¹ * y ∈ K := by
        rw [← hLinj, hΦ₂, hLeq, hs, hg]
      refine ⟨hermitianDiagonal h v g, ⟨g, rfl⟩, r L₀, ?_, _, hk, ?_⟩
      · exact Finset.mem_image_of_mem r (hS₀.mem_toFinset.2 hL₀)
      · group)
    (by
      intro s _ μ₁ _
      rw [hslice s]
      exact h₂ μ₁ D (L s) (hLD s))
    μ
  exact ⟨FD, hFD, hfin⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
