import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussianKernelIntegrableOnThinSlab
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SetIntegralCompOfStable
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeasurePreservingMulLeft
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PeriodsLactSymplectic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClsAndStab
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFamilyInvariantOfFockInner
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatticeOperatorCoefficients
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KernelIdentity
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableSetIntegralOfSummableNorm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsOpenFrames
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegrableTsumOfSummableIntegralNorm

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.SpanMain

theorem unfold_span (Γ I Y A J : Type) [Group Γ] [Countable Γ] [Countable I] [MeasurableSpace Y]
    [MulAction Γ I] [MulAction Γ Y] [Fintype J] (ν : Measure Y) [SFinite ν]
    (hν : ∀ γ : Γ, MeasurePreserving (fun y : Y => γ • y) ν ν) (D : I → Set Y)
    (hD : ∀ i, MeasurableSet (D i)) (hD' : ∀ i, ∀ᵐ y ∂ν, ∃! γ : Γ, γ • y ∈ D (γ • i))
    (S : Set A) (f : A → I → Y → ℂ) (hf : ∀ a ∈ S, ∀ i, Integrable (f a i) ν)
    (hs : ∀ a ∈ S, Summable fun i => ∫ y, ‖f a i y‖ ∂ν) (e : J → A → ℂ) (t : J → I → Y → ℂ)
    (hk : ∀ a ∈ S, ∀ i, ∀ᵐ y ∂ν, ∑' γ : Γ, f a (γ • i) (γ • y) = ∑ j, e j a * t j i y) :
    ∃ (m : ℕ) (k : Fin m → J) (b : Fin m → ℂ), ∀ a ∈ S,
      ∑' i, ∫ y, f a i y ∂ν = ∑ j, b j * e (k j) a := by
  let k : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hk' : ∀ a ∈ S, ∀ i, (fun y => ∑' γ : Γ, f a (γ • i) (γ • y)) =ᵐ[ν.restrict (D i)]
      fun y => ∑ j, e (k j) a * t (k j) i y := fun a ha i => by
    refine ae_restrict_of_ae ((hk a ha i).mono fun y hy => ?_)
    exact hy.trans (k.sum_comp fun j => e j a * t j i y).symm
  obtain ⟨b, hb⟩ := finiteRank_integral_mem_span A I Y ν D S _ (fun j => e (k j))
    (fun j => t (k j)) fun a ha => by
      obtain ⟨h1, h2, -⟩ := unfolding_abstract Γ I Y ν hν D hD hD' (f a) (hf a ha) (hs a ha)
      refine ⟨fun i => (h1 i).congr (hk' a ha i), h2.congr fun i => ?_⟩
      exact integral_congr_ae ((hk' a ha i).mono fun y hy => congrArg norm hy)
  refine ⟨_, k, b, fun a ha => ?_⟩
  obtain ⟨-, -, h3⟩ := unfolding_abstract Γ I Y ν hν D hD hD' (f a) (hf a ha) (hs a ha)
  rw [← h3, ← hb a ha]
  exact tsum_congr fun i => integral_congr_ae (hk' a ha i)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem pnorm_of_gram (la : Wt X.Ψ r) (F : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnM X) : X.pnorm la F x = ‖F x‖ := by
  have h : ∀ τ i, ‖dmin X.Gm x τ i‖ = 1 := fun τ i => by
    unfold dmin lminor
    rw [hx τ, sgnM, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal,
      norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    simp only [Function.comp_apply, sgn]
    split_ifs <;> simp
  unfold Data.pnorm
  simp [h]

omit [NumberField E] [IsCMField E] in

theorem norm_bchar_le {Ψ : Finset (E →+* ℂ)} (la : Wt Ψ r) (C : ℝ) {b : Frame Ψ r}
    (hb : ∀ τ i, ‖b τ i i‖ ≤ C ∧ ‖(b τ i i)⁻¹‖ ≤ C) :
    ‖bchar la b‖ ≤ ∏ τ, ∏ i, C ^ (la τ i).natAbs := by
  unfold bchar
  rw [norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
  rw [norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (la τ i)
  · rw [hk, zpow_natCast, Int.natAbs_natCast, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb τ i).1 _
  · rw [hk, _root_.zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, ← inv_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb τ i).2 _

theorem summable_of_ne {α : Type} (𝓛 : Set α) (L : α) (u : α → ℝ)
    (h : Summable fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} => u L'.1) : Summable fun L' : 𝓛 => u L'.1 := by
  have h1 : Summable (u ∘ ((↑) : (𝓛 \ {L} : Set α) → α)) := h
  have h2 : Summable (u ∘ ((↑) : (𝓛 ∩ {L} : Set α) → α)) :=
    ((Set.finite_singleton L).subset Set.inter_subset_right).summable u
  rw [summable_subtype_iff_indicator] at h1 h2
  change Summable (u ∘ ((↑) : 𝓛 → α))
  rw [summable_subtype_iff_indicator]
  refine (h2.add h1).congr fun x => ?_
  by_cases hx : x ∈ 𝓛 <;> by_cases hL : x = L <;> simp [Set.indicator, hx, hL]

theorem bound_on (la : Wt X.Ψ r) (S : Set (Frame X.Ψ r)) (K B : ℝ)
    (hd : ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnM X) → x ∈ X.dom)
    (hK : ∀ x ∈ S, ∃ x' : Frame X.Ψ r, (∀ τ : X.Ψ, gram τ.1 X.Gm (mat x' τ) = sgnM X) ∧
      ∃ b ∈ Bor X.Ψ r, x = rmul x' b ∧ ∀ τ i j, ‖b τ i j‖ ≤ K ∧ ‖(b τ i i)⁻¹‖ ≤ K) :
    ∃ B' : ℝ, ∀ F : Frame X.Ψ r → ℂ,
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, F (rmul x b) = bchar la b * F x) →
      (∀ x ∈ X.dom, X.pnorm la F x ≤ B) → ∀ x ∈ S, ‖F x‖ ≤ B' := by
  refine ⟨(∏ τ, ∏ i, K ^ (la τ i).natAbs) * B, fun F h1 h2 x hx => ?_⟩
  obtain ⟨x', hx', b, hb, rfl, hbK⟩ := hK x hx
  have h3 := norm_bchar_le la K fun τ i => hbK τ i i
  rw [h1 x' (hd _ hx') b hb, norm_mul]
  refine mul_le_mul h3 ?_ (norm_nonneg _) ((norm_nonneg _).trans h3)
  rw [← pnorm_of_gram X la _ hx']
  exact h2 x' (hd _ hx')

@[reducible] noncomputable def frameAct (Δ : Subgroup (GL (Fin r) E)) :
    MulAction Δ (Frame X.Ψ r) where
  smul γ x := lact γ x
  one_smul x := by
    funext τ
    change (1 : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  mul_smul γ' γ x := by
    funext τ
    change (((γ' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *
      ((γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)).map τ.1 * mat x τ =
      ((γ' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
        (((γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
    rw [Matrix.map_mul, Matrix.mul_assoc]

omit [IsCMField E] in

theorem countable_gl : Countable (GL (Fin r) E) := by
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  have : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  exact (Units.val_injective (α := Matrix (Fin r) (Fin r) E)).countable

theorem sFinite_frame : SFinite (volume : Measure (Frame X.Ψ r)) := by
  have : SigmaFinite (volume : Measure (Fin r → ℂ)) := inferInstance
  have : SigmaFinite (volume : Measure (Fin r → Fin r → ℂ)) := inferInstance
  have : SigmaFinite (volume : Measure (X.Ψ → Fin r → Fin r → ℂ)) := inferInstance
  infer_instance

theorem unfold_frames (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (hun : ∀ γ ∈ Δ, IsUn X γ)
    (hlat : ∀ L ∈ 𝓛, L.FG ∧ Submodule.span E (L : Set (Fin r → E)) = ⊤)
    (hstab : ∀ γ ∈ Δ, ∀ L ∈ 𝓛, mapL γ L ∈ 𝓛) (S : Set (Frame X.Ψ r)) (hmeas : MeasurableSet S)
    (hsub : S ⊆ X.dom)
    (hmp : ∀ γ ∈ Δ, MeasurePreserving (lact γ : Frame X.Ψ r → Frame X.Ψ r)
      (volume.restrict S) (volume.restrict S))
    (A J : Type) [Fintype J] (T : Set A) (f : A → Lt E r → Frame X.Ψ r → ℂ)
    (hf : ∀ a ∈ T, ∀ L ∈ 𝓛, Integrable (f a L) (volume.restrict S))
    (hs : ∀ a ∈ T, Summable fun L : 𝓛 => ∫ y in S, ‖f a L y‖)
    (e : J → A → ℂ) (t : J → Lt E r → Frame X.Ψ r → ℂ)
    (hk : ∀ a ∈ T, ∀ L ∈ 𝓛, ∀ y ∈ S,
      ∑' γ : Δ, f a (mapL γ L) (lact γ y) = ∑ j, e j a * t j L y) :
    ∃ (m : ℕ) (k : Fin m → J) (b : Fin m → ℂ), ∀ a ∈ T,
      ∑' L : 𝓛, ∫ y in S, f a L y = ∑ j, b j * e (k j) a := by
  obtain ⟨hcount, hmul, hone, D, hD, hD'⟩ :=
    LatFrame.exists_fundamentalDomain E r X Δ 𝓛 hun hlat hstab
  have : Countable 𝓛 := hcount.to_subtype
  have : Countable (GL (Fin r) E) := countable_gl
  have := sFinite_frame X
  letI : MulAction Δ 𝓛 :=
    { smul := fun γ L => ⟨mapL γ L, hstab γ γ.2 L L.2⟩
      one_smul := fun L => Subtype.ext (hone _)
      mul_smul := fun γ γ' L => Subtype.ext (hmul _ _ _) }
  have hae : ∀ᵐ y ∂(volume.restrict S), y ∈ S := ae_restrict_mem hmeas
  exact @unfold_span Δ 𝓛 (Frame X.Ψ r) A J _ _ _ MeasureSpace.toMeasurableSpace _ (frameAct X Δ) _
    (volume.restrict S) _ (fun γ => hmp γ γ.2) (fun L => D L) (fun L => (hD L).1)
    (fun L => hae.mono fun y hy => hD' L L.2 y (hsub hy)) T (fun a L => f a L)
    (fun a ha L => hf a ha L L.2) hs e (fun j L => t j L)
    (fun a ha L => hae.mono fun y hy => hk a ha L L.2 y hy)

omit [NumberField E] [IsCMField E] in

theorem mp_restrict {Ψ : Finset (E →+* ℂ)} (S : Set (Frame Ψ r)) (hmeas : MeasurableSet S)
    (f : Frame Ψ r → Frame Ψ r) (h3 : MeasurePreserving f volume volume)
    (h4 : ∀ x, f x ∈ S ↔ x ∈ S) : MeasurePreserving f (volume.restrict S) (volume.restrict S) := by
  have h5 := h3.restrict_preimage hmeas
  rwa [show f ⁻¹' S = S from Set.ext h4] at h5

theorem theta_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * r < n → ∀ (M : ℕ) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (Φ : Lt E r → Lt E n → TF n g) (μ : GL (Fin r) E → Lt E r → ℂ), 0 < M → IsSystem X bas idx M Δ 𝓛 Φ μ → ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (F : Lt E r → Frame X.Ψ r → ℂ), IsForm X Δ 𝓛 μ (wtOf X hr c c' n) F → InSpan X hr bas idx M 𝓛 Φ (Harm.rowHighest ℂ c c' : Submodule ℂ (Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))) F := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn hrn M Δ 𝓛 Φ μ hM hS c c' F hF
  obtain ⟨m, P, hP, hP0, hPi⟩ := exists_invFam_rowHighest X.Ψ q0 X.p0 n c c' (by omega)
  obtain ⟨a, θ, ha, hθ, hC1, hC2⟩ := lattice_operator_coefficients E r X g bas idx n hs hn M Δ 𝓛 Φ μ hM hS
  obtain ⟨κ, hκ, hker⟩ := kernel_identity E r X g q0 hr bas idx n hs hn hrn M Δ 𝓛 Φ μ hM hS
  replace hker := hker c c' m P hP hPi
  obtain ⟨C, hC⟩ : ∃ C : Lt E r → Lt E r → ℂ,
      ∀ L L', classSum M (fun Λ => ip (Φ L Λ) (Φ L' Λ)) = C L L' := ⟨_, fun _ _ => rfl⟩
  simp only [hC] at hC1 hC2 hker
  obtain ⟨F', hF', hFF⟩ := Neumann.main E r X Δ 𝓛 μ (wtOf X hr c c' n) C a θ ha hθ
    (fun γ hγ L hL => ⟨hS.stab γ hγ L hL, (hS.mu γ hγ L hL).1⟩)
    (fun γ hγ x hx => (hS.un γ hγ).lact_mem hx) hC1 hC2 F hF
  obtain ⟨δ₀, hδ₀, hslab⟩ := thin_slab E r X
  obtain ⟨δ₁, hδ₁, hint⟩ := kern_integrableOn_slab E r X g q0 hr idx n c c' m P hn hP (by omega)
  obtain ⟨δ₂, hδ₂, hrep⟩ := kern_reproducing E r X g q0 hr idx n c c' m P hn hP (by omega) hP0
  obtain ⟨δ, hδ, h0, h1, h2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ δ ≤ δ₁ ∧ δ ≤ δ₂ :=
    ⟨min δ₀ (min δ₁ δ₂), by positivity, min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  obtain ⟨hopen, hsub, horth, -, hun, ⟨K, hK⟩, -⟩ := hslab δ hδ h0
  replace hint := hint δ hδ h1
  obtain ⟨ρ, hρ, hrep⟩ := hrep δ hδ h2
  have hmeas : MeasurableSet (slab X δ) := hopen.measurableSet
  obtain ⟨B, hB⟩ := hF'.bdd
  obtain ⟨B', hB0⟩ := bound_on X (wtOf X hr c c' n) (slab X δ) K B
    (fun x hx => hsub (horth x hx)) hK
  have hB' : ∀ L ∈ 𝓛, ∀ x ∈ slab X δ, ‖F' L x‖ ≤ B' := fun L hL =>
    hB0 _ (hF'.bor L hL) (hB L hL)
  have : Finite (Cls E n M) := (finite_cls_and_stab E n M hM).1
  letI : Fintype (Cls E n M) := Fintype.ofFinite _
  have hae : ∀ᵐ y ∂(volume.restrict (slab X δ)), y ∈ slab X δ := ae_restrict_mem hmeas
  have hi : ∀ x₁ ∈ X.dom, ∀ L ∈ 𝓛, Integrable (fun y => kern X hr idx P x₁ y * F' L y)
      (volume.restrict (slab X δ)) := fun x₁ hx₁ L hL =>
    Integrable.mul_bdd (c := B') (hint x₁ hx₁).1
      (((hF'.hol L hL).continuousOn.mono hsub).aestronglyMeasurable hmeas)
      (hae.mono fun y hy => hB' L hL y hy)
  have hmp : ∀ γ ∈ Δ, MeasurePreserving (lact γ : Frame X.Ψ r → Frame X.Ψ r)
      (volume.restrict (slab X δ)) (volume.restrict (slab X δ)) := fun γ hγ => by
    have e : (lact γ : Frame X.Ψ r → Frame X.Ψ r) =
        X.lmulC fun τ => (γ : Matrix (Fin r) (Fin r) E).map τ.1 := rfl
    have h3 := hun (fun τ => (γ : Matrix (Fin r) (Fin r) E).map τ.1)
      fun τ v w => by rw [PerMove.hermC_unitary _ _ _ (hS.un γ hγ)]
    rw [e]
    exact mp_restrict _ hmeas _ h3.1 h3.2.1
  generalize kern X hr idx P = Kr at hker hint hrep hi
  have hsum : ∀ p ∈ 𝓛 ×ˢ X.dom,
      Summable fun L : 𝓛 => ∫ y in slab X δ, ‖C p.1 L * (Kr p.2 y * F' L y)‖ := fun p hp => by
    refine Summable.of_nonneg_of_le (fun L => integral_nonneg fun y => norm_nonneg _)
      (fun L => ?_) ((summable_of_ne 𝓛 p.1 (fun L => ‖C p.1 L‖) (hC1 p.1 hp.1).2.1).mul_right
        (∫ y in slab X δ, ‖Kr p.2 y‖ * B'))
    simp only [norm_mul]
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left (integral_mono_ae ?_ ((hint p.2 hp.2).1.norm.mul_const _)
      (hae.mono fun y hy => ?_)) (norm_nonneg _)
    · simpa only [norm_mul] using (hi p.2 hp.2 L L.2).norm
    · exact mul_le_mul_of_nonneg_left (hB' L L.2 y hy) (norm_nonneg _)
  obtain ⟨th, hth⟩ : ∃ th : Lt E r → Lt E n → Fin m → Frame X.Ψ r → ℂ,
      ∀ L Λ j x, thP X hr bas idx (Φ L Λ) (P j) x = th L Λ j x := ⟨_, fun _ _ _ _ => rfl⟩
  simp only [hth] at hker
  obtain ⟨N, k, b, hb⟩ := unfold_frames X Δ 𝓛 hS.un hS.lat hS.stab (slab X δ) hmeas hsub hmp
    (Lt E r × Frame X.Ψ r) (Cls E n M × Fin m)
    (𝓛 ×ˢ X.dom) (fun p L y => C p.1 L * (Kr p.2 y * F' L y))
    (fun p hp L hL => (hi p.2 hp.2 L hL).const_mul _) hsum
    (fun j p => th p.1 (Quot.out j.1).1 j.2 p.2)
    (fun j L y => κ⁻¹ * (wt M (Quot.out j.1).1 : ℂ) *
      conj (th L (Quot.out j.1).1 j.2 y) * F' L y)
    (fun p hp L hL y hy => by
      have h3 := ((hker p.1 hp.1 L hL p.2 hp.2 y (hsub hy)).mul_left κ⁻¹).mul_right (F' L y)
      refine Eq.trans (tsum_congr fun γ => ?_) (h3.tsum_eq.trans ?_)
      · rw [hF'.aut γ γ.2 L hL y (hsub hy), Complex.inv_eq_conj (hS.mu γ γ.2 L hL).1]
        field_simp
      · rw [classSum, finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
        ring)
  refine ⟨N, fun i => (Quot.out (k i).1).1, fun i => P (k i).2, fun i => (ρ : ℂ)⁻¹ * b i,
    fun i => ⟨(Quot.out (k i).1).2, hP _⟩, fun L hL x hx => ?_⟩
  have h3 := hb (L, x) ⟨hL, hx⟩
  have hρ' : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.2 hρ.ne'
  have h4 : ∀ L' : 𝓛, ∫ y in slab X δ, C L L' * (Kr x y * F' L' y) =
      ρ * (C L L' * F' L' x) := fun L' => by
    rw [integral_const_mul, hrep (F' L') (hF'.hol _ L'.2) (hF'.bor _ L'.2)
      ⟨B, hB _ L'.2⟩ x hx]
    ring
  simp only [h4] at h3
  rw [tsum_mul_left, ← hFF L hL x hx] at h3
  simp only [mul_assoc, hth]
  rw [← Finset.mul_sum, ← h3, inv_mul_cancel_left₀ hρ']

end GlobalTheory.SW.SpanMain
