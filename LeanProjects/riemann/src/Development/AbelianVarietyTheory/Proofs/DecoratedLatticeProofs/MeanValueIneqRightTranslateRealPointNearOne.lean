import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinear
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLogNearOneUnitaryGroupOfFormLinearBoundStatement

noncomputable section

namespace GlobalTheory.CuspGeo.MeanValue

section Abstract

open GlobalTheory.SmoothForms

variable {L G ι : Type} [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] [Fintype ι]

theorem norm_sub_le (e : L → G) (he0 : e 0 = 1) (he : ∀ (Z : L) (s t : ℝ), e ((s + t) • Z) = e (s • Z) * e (t • Z))
    (b : Module.Basis ι ℝ L) {φ : G → ℂ} (hφ : Sm e φ) (g : G) (Z : L) (a : ℝ) (ha : ∀ i, |b.repr Z i| ≤ a) (c : ι → ℝ)
    (hc : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Der e (b i) φ (g * e (t • Z))‖ ≤ c i) :
    ‖φ (g * e Z) - φ g‖ ≤ a * ∑ i, c i := by
  have hc0 : ∀ i, 0 ≤ c i := fun i => (norm_nonneg _).trans (hc i 0 ⟨le_refl 0, zero_le_one⟩)

  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (g * e (s • Z)))
      (fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) ((t - t) • Z) Z) t := by
    intro t
    have hF : Differentiable ℝ (fun X : L => φ (g * e (t • Z) * e X)) :=
      (hφ (g * e (t • Z))).differentiable (by simp)
    have h1 : HasDerivAt (fun s : ℝ => (s - t) • Z) ((1 : ℝ) • Z) t :=
      ((hasDerivAt_id' t).sub_const t).smul_const Z
    rw [one_smul] at h1
    have h2 := (hF ((t - t) • Z)).hasFDerivAt.comp_hasDerivAt t h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show φ (g * e (s • Z)) = φ (g * e (t • Z) * e ((s - t) • Z))
    rw [mul_assoc, ← he, show t + (s - t) = s by ring]

  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) 0 Z‖ ≤ a * ∑ i, c i := by
    intro t ht
    set F' := fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) 0 with hF'
    have hZ : F' Z = ∑ i, b.repr Z i • F' (b i) := by
      have : F' Z = F' (∑ i, b.repr Z i • b i) := by rw [b.sum_repr]
      rw [this, map_sum]
      simp only [map_smul]
    rw [hZ, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    have hi : ‖F' (b i)‖ ≤ c i := by
      have := hc i t ht
      rwa [DerLinear.der_eq_fderiv hφ] at this
    exact mul_le_mul (ha i) hi (norm_nonneg _) ((abs_nonneg _).trans (ha i))
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => φ (g * e (s • Z))) (fun t _ => (hderiv t).hasDerivWithinAt)
    (fun t ht => by
      rw [sub_self, zero_smul]
      exact key t (Set.Ico_subset_Icc_self ht))
  simpa [he0] using hmv

theorem exists_coord_bound (b : Module.Basis ι ℝ L) : ∃ K : ℝ, 0 ≤ K ∧ ∀ Z i, |b.repr Z i| ≤ K * ‖Z‖ := by
  have : FiniteDimensional ℝ L := Module.Finite.of_basis b
  let f : ι → L →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖f i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun Z i => ?_⟩
  have h1 : |b.repr Z i| = ‖f i Z‖ := by
    simp [f, Real.norm_eq_abs]
  rw [h1]
  exact ((f i).le_opNorm Z).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => norm_nonneg (f j)) (Finset.mem_univ i)) (norm_nonneg Z))

end Abstract

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem expInf_zero (R : RealPoints θ V) : expInf θ V 0 = 1 := by
  have hE := isExpFam_expInf R
  refine R.2.2.1 _ (hE (0 : LieN V)).1 _ (GinfC V).one_mem fun τ => ?_
  rw [(hE (0 : LieN V)).2 τ, R.2.2.2.2.1 1 (GfC V).one_mem τ]
  show NormedSpace.exp (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 1
  exact NormedSpace.exp_zero

theorem expInf_add (R : RealPoints θ V) (Z : LieN V) (s t : ℝ) :
    expInf θ V ((s + t) • Z) = expInf θ V (s • Z) * expInf θ V (t • Z) := by
  have hE := isExpFam_expInf R
  refine R.2.2.1 _ (hE ((s + t) • Z)).1 _ (mul_mem (hE (s • Z)).1 (hE (t • Z)).1) fun τ => ?_
  rw [R.2.2.2.1, (hE ((s + t) • Z)).2 τ, (hE (s • Z)).2 τ, (hE (t • Z)).2 τ]
  show NormedSpace.exp ((s + t) • (Z τ).1) = NormedSpace.exp (s • (Z τ).1) * NormedSpace.exp (t • (Z τ).1)
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl (Z τ).1).smul_right t).smul_left s)

theorem continuous_expInf (hθ : IsInfFam θ) (R : RealPoints θ V) : Continuous (expInf θ V) := by
  have H := isLieData R
  have h1 : Continuous fun X : LieN V => NormedSpace.exp (jInf V X) :=
    (DerLinear.contDiff_exp H).continuous
  exact (GlobalTheory.Mem.DerClosed.continuousOn_secInf hθ V).comp_continuous h1 fun X => DerLinear.exp_unitary H X

open Classical in

theorem exists_basis (V : HSp D) : ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (LieN V)) (p : ι → D.what₂.Tau)
    (X : ∀ i, LieAt V (p i)), ∀ i, b i = atPlace V (p i) (X i) := by
  refine ⟨Σ τ, Fin (Module.finrank ℝ (lieU (gramAt D V τ)).toSubmodule), inferInstance,
    Pi.basis fun τ => Module.finBasis ℝ (lieU (gramAt D V τ)).toSubmodule, fun i => i.1,
    fun i => ⟨(Module.finBasis ℝ (lieU (gramAt D V i.1)).toSubmodule i.2).1,
      (Module.finBasis ℝ (lieU (gramAt D V i.1)).toSubmodule i.2).2⟩, fun i => ?_⟩
  exact (Pi.basis_apply _ i).trans rfl

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem norm_lieN_le (Z : LieN V) {r : ℝ} (hr : 0 ≤ r) (h : ∀ τ i j, ‖(Z τ).1 i j‖ ≤ r) : ‖Z‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).2 fun τ => ?_
  rw [Submodule.coe_norm]
  exact (Matrix.norm_le_iff hr).2 (h τ)

end

theorem exists_log (hθ : IsInfFam θ) (R : RealPoints θ V) : ∃ δ₁ C : ℝ, 0 < δ₁ ∧ 0 ≤ C ∧
    ∀ (u : GA D V) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseR θ V u δ → ∃ Z : LieN V, expInf θ V Z = u ∧ ‖Z‖ ≤ C * δ := by
  have hG : ∀ τ, IsUnit (gramAt D V τ).det := fun τ => (R.1 τ).2
  choose δτ Cτ hδτ hτ using fun τ => GlobalTheory.T.exists_log_near_one_unitaryGroup_of_form_linear_bound V.rank (gramAt D V τ) (hG τ)
  obtain ⟨δ₁, hδ₁, hle⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ τ, δ₁ ≤ δτ τ := by
    rcases isEmpty_or_nonempty D.what₂.Tau with h | h
    · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
    · obtain ⟨τ₀, hτ₀⟩ := Finite.exists_min δτ
      exact ⟨δτ τ₀, hδτ τ₀, hτ₀⟩
  have hC : ∀ τ, Cτ τ ≤ ∑ τ', |Cτ τ'| := fun τ =>
    (le_abs_self _).trans (Finset.single_le_sum (fun τ' _ => abs_nonneg (Cτ τ')) (Finset.mem_univ τ))
  refine ⟨δ₁, ∑ τ, |Cτ τ|, hδ₁, Finset.sum_nonneg fun τ _ => abs_nonneg _, fun u δ hδ hδle hu => ?_⟩

  have hX : ∀ τ, ∃ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 ∧
      NormedSpace.exp X = infMat D.sp.cm.sig V.gram (θ τ) u ∧ ∀ i j, ‖X i j‖ ≤ Cτ τ * δ := fun τ =>
    hτ τ _ δ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V u τ) (hδle.trans (hle τ)) (hu.2 τ)
  choose X hXl hXe hXn using hX
  let Z : LieN V := fun τ => ⟨X τ, (mem_lieAt_iff τ (X τ)).1 (hXl τ)⟩
  refine ⟨Z, ?_, ?_⟩
  · have hE := isExpFam_expInf R
    refine R.2.2.1 _ (hE Z).1 _ hu.1 fun τ => ?_
    rw [(hE Z).2 τ]
    exact hXe τ
  · refine norm_lieN_le Z (mul_nonneg (Finset.sum_nonneg fun τ _ => abs_nonneg _) hδ) fun τ i j => ?_
    exact (hXn τ i j).trans (mul_le_mul_of_nonneg_right (hC τ) hδ)

theorem mean_value : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ V : HSp D, ∃ (B : Finset (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (Ω : Set (GA D V)) (C δ₁ : ℝ), (∀ p ∈ B, p.2 ∈ lieAt V p.1) ∧ IsCompact Ω ∧ 0 < δ₁ ∧ 0 ≤ C ∧ ∀ ψ : GA D V → ℂ, SmoothW θ V ψ → ∀ (g u : GA D V) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseR θ V u δ → ∀ c : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → ℝ, (∀ p ∈ B, ∀ w ∈ Ω, ‖Rder θ V p.1 p.2 ψ (g * w)‖ ≤ c p) → ‖ψ (g * u) - ψ g‖ ≤ C * δ * ∑ p ∈ B, c p := by
  intro D θ hθ V
  classical
  have R : RealPoints θ V := (RealPts.realPoints D).2 θ hθ V
  obtain ⟨ι, hι, b, p, X, hb⟩ := exists_basis V
  obtain ⟨K, hK, hKb⟩ := exists_coord_bound b
  obtain ⟨δ₁, C₀, hδ₁, hC₀, hlog⟩ := exists_log hθ R
  have : FiniteDimensional ℝ (LieN V) := Module.Finite.of_basis b
  set B := Finset.univ.image fun i => (p i, (X i).1) with hB
  have hmemB : ∀ i, (p i, (X i).1) ∈ B := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have h0 : expInf θ V 0 ∈ expInf θ V '' Metric.closedBall 0 (C₀ * δ₁) :=
    ⟨0, Metric.mem_closedBall_self (mul_nonneg hC₀ hδ₁.le), rfl⟩
  refine ⟨B, expInf θ V '' Metric.closedBall 0 (C₀ * δ₁), K * C₀ * Fintype.card ι, δ₁, ?_, ?_, hδ₁,
    mul_nonneg (mul_nonneg hK hC₀) (Nat.cast_nonneg _), ?_⟩
  · intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
    exact (mem_lieAt_iff _ _).2 (X i).2
  · exact (isCompact_closedBall 0 _).image (continuous_expInf hθ R)
  · intro ψ hψ g u δ hδ hδle hu c hc
    obtain ⟨Z, rfl, hZ⟩ := hlog u δ hδ hδle hu
    have hsm : Sm (expInf θ V) ψ := (isSmoothInf_iff ψ).1 ((smooth_iff R ψ).1 hψ)
    have hcn : ∀ q ∈ B, 0 ≤ c q := fun q hq => (norm_nonneg _).trans (hc q hq _ h0)
    have ha : ∀ i, |b.repr Z i| ≤ K * (C₀ * δ) := fun i =>
      (hKb Z i).trans (mul_le_mul_of_nonneg_left hZ hK)
    have hder : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖Der (expInf θ V) (b i) ψ (g * expInf θ V (t • Z))‖ ≤ c (p i, (X i).1) := by
      intro i t ht
      rw [hb i, ← lieDer_eq, ← Rder_eq R]
      refine hc _ (hmemB i) _ ⟨t • Z, ?_, rfl⟩
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖Z‖ ≤ 1 * (C₀ * δ) := mul_le_mul ht.2 hZ (norm_nonneg _) zero_le_one
        _ ≤ C₀ * δ₁ := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hδle hC₀
    have key := norm_sub_le (expInf θ V) (expInf_zero R) (expInf_add R) b hsm g Z (K * (C₀ * δ)) ha
      (fun i => c (p i, (X i).1)) hder
    have hsum : ∑ i, c (p i, (X i).1) ≤ Fintype.card ι * ∑ q ∈ B, c q := by
      calc ∑ i, c (p i, (X i).1) ≤ ∑ _i : ι, ∑ q ∈ B, c q :=
            Finset.sum_le_sum fun i _ => Finset.single_le_sum hcn (hmemB i)
        _ = Fintype.card ι * ∑ q ∈ B, c q := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc ‖ψ (g * expInf θ V Z) - ψ g‖ ≤ K * (C₀ * δ) * ∑ i, c (p i, (X i).1) := key
      _ ≤ K * (C₀ * δ) * (Fintype.card ι * ∑ q ∈ B, c q) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hK (mul_nonneg hC₀ hδ))
      _ = K * C₀ * Fintype.card ι * δ * ∑ q ∈ B, c q := by ring

end GlobalTheory.CuspGeo.MeanValue

end
