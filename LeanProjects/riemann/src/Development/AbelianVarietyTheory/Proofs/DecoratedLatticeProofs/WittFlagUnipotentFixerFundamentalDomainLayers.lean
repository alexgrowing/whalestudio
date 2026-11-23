import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Layers

section Abstract

open scoped Pointwise

variable {A B U X G : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [AddGroup B] [MeasurableSpace B]
  [MeasurableSpace U] [MeasurableSpace X] [Group G] [MulAction G X]
  {mA : Measure A} {mB : Measure B} {ν : Measure U} [SFinite mA] [SFinite mB] [SFinite ν]

theorem null_middle {N : Set B} (hN : mB N = 0) : (mA.prod (mB.prod ν)) {p | p.2.1 ∈ N} = 0 := by
  have h : {p : A × (B × U) | p.2.1 ∈ N} = Set.univ ×ˢ (N ×ˢ Set.univ) := by
    ext p; simp
  rw [h, Measure.prod_prod, Measure.prod_prod, hN]
  simp

theorem null_shear [mA.IsAddLeftInvariant] {φ : B → A} (hφ : Measurable φ) {N : Set A} (hN : mA N = 0) :
    (mA.prod (mB.prod ν)) {p | p.1 + φ p.2.1 ∈ N} = 0 := by
  have hM : MeasurableSet (toMeasurable mA N) := measurableSet_toMeasurable _ _
  have hM0 : mA (toMeasurable mA N) = 0 := by rw [measure_toMeasurable, hN]
  have hs : MeasurableSet {p : A × (B × U) | p.1 + φ p.2.1 ∈ toMeasurable mA N} :=
    (measurable_fst.add (hφ.comp (measurable_fst.comp measurable_snd))) hM
  refine measure_mono_null (t := {p : A × (B × U) | p.1 + φ p.2.1 ∈ toMeasurable mA N}) (fun p hp => subset_toMeasurable mA N hp) ?_
  rw [Measure.prod_apply_symm hs]
  have h0 : ∀ y : B × U, mA ((fun x => (x, y)) ⁻¹' {p : A × (B × U) | p.1 + φ p.2.1 ∈ toMeasurable mA N}) = 0 := fun y => by
    have h1 : (fun x : A => (x, y)) ⁻¹' {p : A × (B × U) | p.1 + φ p.2.1 ∈ toMeasurable mA N} =
        (fun x => φ y.1 + x) ⁻¹' toMeasurable mA N := by
      ext x; simp [add_comm]
    rw [h1, measure_preimage_add, hM0]
  exact (lintegral_congr h0).trans lintegral_zero

theorem isFundamentalDomain_layers [mA.IsAddLeftInvariant] (ΓA : AddSubgroup A) (ΓB : AddSubgroup B) [Countable ΓB]
    (κ : B → B → A) (hκ : ∀ b', Measurable (κ b')) (e : A × (B × U) ≃ᵐ X)
    (hfree : ∀ (g g' : G) (x : X), g • x = g' • x → g = g')
    (hG : ∀ g : G, ∃ (c' : ΓA) (b' : ΓB), ∀ p, g • e p = e (c'.1 + p.1 + κ b'.1 p.2.1, b'.1 + p.2.1, p.2.2))
    (hG' : ∀ (c' : ΓA) (b' : ΓB), ∃ g : G, ∀ p, g • e p = e (c'.1 + p.1 + κ b'.1 p.2.1, b'.1 + p.2.1, p.2.2))
    {𝓒 : Set A} {𝓕 : Set B} (hC : IsAddFundamentalDomain ΓA 𝓒 mA) (hF : IsAddFundamentalDomain ΓB 𝓕 mB) :
    IsFundamentalDomain G (e '' (𝓒 ×ˢ (𝓕 ×ˢ Set.univ))) ((mA.prod (mB.prod ν)).map e) := by
  have hmem : ∀ q, e q ∈ e '' (𝓒 ×ˢ (𝓕 ×ˢ (Set.univ : Set U))) ↔ q ∈ 𝓒 ×ˢ (𝓕 ×ˢ (Set.univ : Set U)) :=
    fun q => e.injective.mem_set_image
  have hmp := (e.measurable.measurePreserving (mA.prod (mB.prod ν))).symm e
  refine ⟨?_, ?_, ?_⟩
  · have hS : NullMeasurableSet (𝓒 ×ˢ (𝓕 ×ˢ (Set.univ : Set U))) (mA.prod (mB.prod ν)) :=
      hC.nullMeasurableSet.prod (hF.nullMeasurableSet.prod nullMeasurableSet_univ)
    rw [e.image_eq_preimage_symm]
    exact hS.preimage hmp.quasiMeasurePreserving
  · rw [e.measurableEmbedding.ae_map_iff]
    have h1 : ∀ᵐ p ∂(mA.prod (mB.prod ν)), ∃ g : ΓB, g +ᵥ p.2.1 ∈ 𝓕 := by
      have := null_middle (mA := mA) (ν := ν) (ae_iff.1 hF.ae_covers)
      exact ae_iff.2 this
    have h2 : ∀ᵐ p ∂(mA.prod (mB.prod ν)), ∀ b' : ΓB, ∃ g : ΓA, g +ᵥ (p.1 + κ b'.1 p.2.1) ∈ 𝓒 := by
      rw [ae_all_iff]
      intro b'
      exact ae_iff.2 (null_shear (hκ b'.1) (ae_iff.1 hC.ae_covers))
    filter_upwards [h1, h2] with p hp1 hp2
    obtain ⟨b', hb⟩ := hp1
    obtain ⟨c', hc⟩ := hp2 b'
    obtain ⟨g, hg⟩ := hG' c' b'
    refine ⟨g, ?_⟩
    rw [hg p, hmem]
    refine ⟨?_, hb, Set.mem_univ _⟩
    rw [AddSubgroup.vadd_def, vadd_eq_add] at hc
    simpa only [add_assoc] using hc
  · intro g₁ g₂ hne
    obtain ⟨c₁, b₁, h₁⟩ := hG g₁⁻¹
    obtain ⟨c₂, b₂, h₂⟩ := hG g₂⁻¹
    change (mA.prod (mB.prod ν)).map e (g₁ • (e '' _) ∩ g₂ • (e '' _)) = 0
    rw [e.map_apply]
    have hin : ∀ p, p ∈ e ⁻¹' (g₁ • (e '' (𝓒 ×ˢ (𝓕 ×ˢ (Set.univ : Set U)))) ∩ g₂ • (e '' (𝓒 ×ˢ (𝓕 ×ˢ (Set.univ : Set U))))) →
        (c₁.1 + p.1 + κ b₁.1 p.2.1 ∈ 𝓒 ∧ b₁.1 + p.2.1 ∈ 𝓕) ∧ (c₂.1 + p.1 + κ b₂.1 p.2.1 ∈ 𝓒 ∧ b₂.1 + p.2.1 ∈ 𝓕) := by
      rintro p ⟨hp1, hp2⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, h₁, hmem] at hp1
      rw [Set.mem_smul_set_iff_inv_smul_mem, h₂, hmem] at hp2
      exact ⟨⟨hp1.1, hp1.2.1⟩, ⟨hp2.1, hp2.2.1⟩⟩
    by_cases hb : b₁ = b₂
    · subst hb
      by_cases hc : c₁ = c₂
      · subst hc
        refine measure_mono_null (t := ∅) (fun p hp => ?_) (measure_empty)
        have : g₁⁻¹ • e p = g₂⁻¹ • e p := by rw [h₁, h₂]
        exact absurd (inv_injective (hfree _ _ _ this)) hne
      · have hd := hC.aedisjoint (i := -c₁) (j := -c₂) (fun h => hc (neg_injective h))
        have hd' : mA ((-c₁ +ᵥ 𝓒) ∩ (-c₂ +ᵥ 𝓒)) = 0 := hd
        refine measure_mono_null (fun p hp => ?_) (null_shear (hκ b₁.1) hd')
        obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := hin p hp
        refine ⟨?_, ?_⟩
        · rw [Set.mem_neg_vadd_set_iff]
          simpa only [AddSubgroup.vadd_def, vadd_eq_add, add_assoc] using h1
        · rw [Set.mem_neg_vadd_set_iff]
          simpa only [AddSubgroup.vadd_def, vadd_eq_add, add_assoc] using h2
    · have hd := hF.aedisjoint (i := -b₁) (j := -b₂) (fun h => hb (neg_injective h))
      have hd' : mB ((-b₁ +ᵥ 𝓕) ∩ (-b₂ +ᵥ 𝓕)) = 0 := hd
      refine measure_mono_null (fun p hp => ?_) (null_middle (mA := mA) (ν := ν) hd')
      obtain ⟨⟨-, h1⟩, ⟨-, h2⟩⟩ := hin p hp
      exact ⟨Set.mem_neg_vadd_set_iff.2 h1, Set.mem_neg_vadd_set_iff.2 h2⟩

end Abstract

section Concrete

variable {D : D7}

theorem rat_coords {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {b : Mx D ρ S₀.rank} {c : skewA D ρ}
    (h : d.nB b * d.nC c ∈ GQ S) : b ∈ ratMx D ρ S₀.rank ∧ c.1 ∈ ratMx D ρ ρ := by
  have hm := (mem_GQ_iff S _).1 h
  have hb : b ∈ ratMx D ρ S₀.rank := by
    have e1 : d.pX ⬝ (mt S (d.nB b * d.nC c) ⬝ d.j0) = b := by
      rw [mt_mul, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.pX_j0, ← Matrix.mul_assoc, d.pX_jX,
        Matrix.one_mul, zero_add]
    rw [← e1]
    exact ratMx_mul (rat_mem _) (ratMx_mul hm (rat_mem _))
  refine ⟨hb, ?_⟩
  have hc : d.nC c ∈ GQ S := by
    have := mul_mem (inv_mem (d.nB_mem_GQ hb)) h
    rwa [inv_mul_cancel_left] at this
  have hm2 := (mem_GQ_iff S _).1 hc
  have e2 : d.pX ⬝ (mt S (d.nC c) ⬝ d.jY) = c.1 := by
    rw [d.nC_jY, Matrix.mul_add, d.pX_jY, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul, zero_add]
  rw [← e2]
  exact ratMx_mul (rat_mem _) (ratMx_mul hm2 (rat_mem _))

theorem act_coords {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c' c : skewA D ρ) (b' b : Mx D ρ S₀.rank)
    (u : GL (Fin ρ) (AE D)) :
    d.nC c' * d.nB b' * (d.nC c * (d.nB b * d.levi u)) =
      d.nC (c' + c + cComm S₀ b' b) * (d.nB (b' + b) * d.levi u) := by
  have h1 : d.nB b' * d.nC c = d.nC c * d.nB b' := (d.nC_mul_nB b' c).symm
  have h2 : d.nB (b' + b) * d.nC (cComm S₀ b' b) = d.nC (cComm S₀ b' b) * d.nB (b' + b) :=
    (d.nC_mul_nB _ _).symm
  calc d.nC c' * d.nB b' * (d.nC c * (d.nB b * d.levi u))
      = d.nC c' * (d.nB b' * d.nC c) * d.nB b * d.levi u := by simp only [mul_assoc]
    _ = d.nC c' * d.nC c * (d.nB b' * d.nB b) * d.levi u := by rw [h1]; simp only [mul_assoc]
    _ = d.nC c' * d.nC c * d.nC (cComm S₀ b' b) * d.nB (b' + b) * d.levi u := by
        rw [d.nB_mul_nB, h2]; simp only [mul_assoc]
    _ = d.nC (c' + c + cComm S₀ b' b) * (d.nB (b' + b) * d.levi u) := by
        rw [d.nC_add, d.nC_add]; simp only [mul_assoc]

end Concrete

theorem fundDomain_layers : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC → ∀ (vb : VolM D ρ V₀.rank) (ν : Measure (UX D ρ)), SFinite vb.μ → SFinite ν → IsFundamentalDomain ((GQ V ⊓ radX d).subgroupOf (flagN d)) (e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ))) ((lC.prod (vb.μ.prod ν)).map e) := by
  intro D V V₀ ρ d e he lC 𝓒 _ _ hC vb ν _ _
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  haveI : SecondCountableTopology (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.1
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).1
  haveI : SecondCountableTopology (Mx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.1
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D ρ V₀.rank) := (lattice_Mx D ρ V₀.rank).2.2.2.2.1
  haveI : Countable (ratMx D ρ V₀.rank) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsTopologicalAddGroup (skewA D ρ) := inferInstance
  haveI hca : ContinuousAdd (skewA D ρ) := IsTopologicalAddGroup.toContinuousAdd
  haveI : MeasurableAdd₂ (skewA D ρ) := @ContinuousAdd.measurableMul₂ (skewA D ρ) _ _ _ _ _ hca
  have hstr := GlobalTheory.MixPer.flag_jacobi_structure D V V₀ ρ d
  have hκ : ∀ b' : Mx D ρ V₀.rank, Measurable (cComm V₀ b') := by
    intro b'
    have := (lattice_Mx D ρ ρ).1
    have : ContinuousSub (Mx D ρ ρ) := IsTopologicalAddGroup.to_continuousSub
    have hp : Continuous (plus V₀ : Mx D ρ V₀.rank → _) := continuous_const.matrix_mul continuous_adj
    have h1 : Continuous fun b : Mx D ρ V₀.rank => half D • (b ⬝ plus V₀ b' - b' ⬝ plus V₀ b) :=
      ((continuous_id.matrix_mul continuous_const).sub (continuous_const.matrix_mul hp)).const_smul (half D)
    exact (h1.subtype_mk _).measurable
  have key : ∀ (c' : skewA D ρ) (b' : Mx D ρ V₀.rank) (p : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ)),
      d.nC c' * d.nB b' * (e p : GA D V) = (e (c' + p.1 + cComm V₀ b' p.2.1, b' + p.2.1, p.2.2) : GA D V) := by
    intro c' b' p
    rw [he p, he (c' + p.1 + cComm V₀ b' p.2.1, b' + p.2.1, p.2.2)]
    exact act_coords d c' p.1 b' p.2.1 p.2.2.1
  have hsm : ∀ (g : ↥((GQ V ⊓ radX d).subgroupOf (flagN d))) (x : flagN d),
      ((g • x : flagN d) : GA D V) = ((g : flagN d) : GA D V) * (x : GA D V) := fun _ _ => rfl
  refine isFundamentalDomain_layers (mA := lC) (mB := vb.μ) (ν := ν) ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) (ratMx D ρ V₀.rank) (cComm V₀) hκ e
    ?_ ?_ ?_ hC vb.covol.2.1
  · intro g g' x h
    rw [Subgroup.smul_def, Subgroup.smul_def] at h
    exact Subtype.ext (mul_right_cancel h)
  · rintro ⟨⟨γ, hγN⟩, hγ⟩
    rw [Subgroup.mem_subgroupOf] at hγ
    obtain ⟨b, c, hbc⟩ := ((hstr.2.1 γ).1 (Subgroup.mem_inf.1 hγ).2)
    subst hbc
    have hr := rat_coords d (Subgroup.mem_inf.1 hγ).1
    refine ⟨⟨c, AddSubgroup.mem_addSubgroupOf.2 hr.2⟩, ⟨b, hr.1⟩, fun p => Subtype.ext ?_⟩
    rw [Subgroup.smul_def]
    have h := key c b p
    rw [d.nC_mul_nB] at h
    exact h
  · rintro ⟨c', hc'⟩ ⟨b', hb'⟩
    have hrad : d.nC c' * d.nB b' ∈ radX d := (hstr.2.1 _).2 ⟨b', c', d.nC_mul_nB b' c'⟩
    have hQ : d.nC c' * d.nB b' ∈ GQ V :=
      mul_mem (d.nC_mem_GQ (AddSubgroup.mem_addSubgroupOf.1 hc')) (d.nB_mem_GQ hb')
    have hN : d.nC c' * d.nB b' ∈ flagN d := (Subgroup.mem_inf.1 hrad).1
    let g : ((GQ V ⊓ radX d).subgroupOf (flagN d)) :=
      ⟨⟨d.nC c' * d.nB b', hN⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hQ, hrad⟩)⟩
    refine ⟨g, fun p => Subtype.ext ((hsm g (e p)).trans (key c' b' p))⟩

end GlobalTheory.Layers

end
