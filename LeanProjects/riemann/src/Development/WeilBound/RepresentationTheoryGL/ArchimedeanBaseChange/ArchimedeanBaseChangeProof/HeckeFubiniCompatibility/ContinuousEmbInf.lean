import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotIntegralZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.TrMulComm
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit

noncomputable section

open NumberField MeasureTheory Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace PositivityTheory.Rg.BcB.CG

namespace PSumH

variable {n : ℕ}

theorem isClosed_nilrad (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    IsClosed (nilrad W₁ W₂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hW : ∀ W : Submodule ℂ (Fin n → ℂ), IsClosed (W : Set (Fin n → ℂ)) := fun W =>
    W.closed_of_finiteDimensional
  have hc : ∀ y : Fin n → ℂ, Continuous fun X : Matrix (Fin n) (Fin n) ℂ => X *ᵥ y := fun y =>
    continuous_id.matrix_mulVec continuous_const
  have e : (nilrad W₁ W₂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
      (⋂ y, (fun X : Matrix (Fin n) (Fin n) ℂ => X *ᵥ y) ⁻¹' W₂) ∩
        ((⋂ y ∈ W₂, (fun X : Matrix (Fin n) (Fin n) ℂ => X *ᵥ y) ⁻¹' W₁) ∩
          ⋂ y ∈ W₁, (fun X : Matrix (Fin n) (Fin n) ℂ => X *ᵥ y) ⁻¹' {0}) := by
    ext X
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, Set.mem_singleton_iff]
    exact Iff.rfl
  rw [e]
  refine (isClosed_iInter fun y => (hW W₂).preimage (hc y)).inter
    ((isClosed_biInter fun y _ => (hW W₁).preimage (hc y)).inter
      (isClosed_biInter fun y _ => isClosed_singleton.preimage (hc y)))

theorem integrable_nil {f : GL (Fin n) ℂ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (u : nilrad W₁ W₂ → GL (Fin n) ℂ) (hu : ∀ X, (u X).val = 1 + X.1)
    (d : GL (Fin n) ℂ) [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂))
    [ν.IsAddHaarMeasure] : Integrable (fun X => f (u X * d)) ν := by
  have hu' : u = fun X => ((PVC.eH W₁ W₂ X : PVC.nilSub W₁ W₂) : GL (Fin n) ℂ) :=
    funext fun X => Units.ext (by rw [hu X]; rfl)
  have hcu : Continuous u := by
    rw [hu']; exact continuous_subtype_val.comp (PVC.eH W₁ W₂).continuous
  have hF : Continuous fun X => f (u X * d) := hf.comp (hcu.mul continuous_const)
  refine hF.integrable_of_hasCompactSupport ?_
  have hL : IsCompact ((fun k : GL (Fin n) ℂ => (k * d⁻¹).val - 1) '' tsupport f) :=
    hfc.isCompact.image ((Units.continuous_val.comp (continuous_id.mul continuous_const)).sub continuous_const)
  have hK : IsCompact (Subtype.val ⁻¹' ((fun k : GL (Fin n) ℂ => (k * d⁻¹).val - 1) '' tsupport f) :
      Set (nilrad W₁ W₂)) :=
    (isClosed_nilrad W₁ W₂).isClosedEmbedding_subtypeVal.isCompact_preimage hL
  refine HasCompactSupport.intro hK fun X hX => ?_
  by_contra h
  apply hX
  refine ⟨u X * d, subset_tsupport _ h, ?_⟩
  show ((u X * d) * d⁻¹).val - 1 = X.1
  rw [mul_inv_cancel_right, hu X, add_sub_cancel_left]

theorem veryCusp_add {f g : GL (Fin n) ℂ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hf' : VeryCusp f) (hg' : VeryCusp g) : VeryCusp fun x => f x + g x := by
  refine ⟨fun k d hk => by dsimp only; rw [hf'.1 k d hk, hg'.1 k d hk], fun d W₁ W₂ hne hle hp1 hp2 u hu _ _ ν _ => ?_⟩
  rw [integral_add (integrable_nil hf hfc u hu d ν) (integrable_nil hg hgc u hu d ν),
    hf'.2 d W₁ W₂ hne hle hp1 hp2 u hu ν, hg'.2 d W₁ W₂ hne hle hp1 hp2 u hu ν, add_zero]

theorem veryCusp_smul {f : GL (Fin n) ℂ → ℂ} (c : ℂ) (hf : VeryCusp f) : VeryCusp fun x => c * f x := by
  refine ⟨fun k d hk => by dsimp only; rw [hf.1 k d hk], fun d W₁ W₂ hne hle hp1 hp2 u hu _ _ ν _ => ?_⟩
  rw [integral_const_mul, hf.2 d W₁ W₂ hne hle hp1 hp2 u hu ν, mul_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gInf_embInf (v : InfinitePlace E) (d : GL (Fin n) ℂ) : gInf v (embInf n v d) = d := by
  classical
  have e : embInf n v d = infP n (Pi.mulSingle v d) := rfl
  rw [e, gInf_infP, Pi.mulSingle_eq_same]

theorem continuous_embInf (v : InfinitePlace E) : Continuous (embInf (E := E) n v) := by
  classical
  have e : (embInf (E := E) n v : GL (Fin n) ℂ → GA E n) = fun d => infP n (Pi.mulSingle v d) := rfl
  rw [e]
  exact (continuous_infP n).comp (continuous_mulSingle (A := fun _ : InfinitePlace E => GL (Fin n) ℂ) v)

theorem slice {φ : GA E n → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ) (v : InfinitePlace E) (g : GA E n)
    (hg : GeneralLinearGroup.map (cV v) g = 1) :
    Continuous (fun d => φ (embInf n v d * g)) ∧ HasCompactSupport (fun d => φ (embInf n v d * g)) := by
  refine ⟨hφ.comp ((continuous_embInf v).mul continuous_const), ?_⟩
  refine HasCompactSupport.intro (hc.isCompact.image (continuous_gInf n v)) fun d hd => ?_
  by_contra h
  apply hd
  refine ⟨embInf n v d * g, subset_tsupport _ h, ?_⟩
  have hg' : gInf v g = 1 := hg
  rw [map_mul, gInf_embInf, hg', mul_one]

omit [IsCMField E] in
theorem isTest_add [IsTotallyComplex E] {φ ψ : GA E n → ℂ} (hφ : IsTest φ) (hψ : IsTest ψ) : IsTest fun x => φ x + ψ x := by
  obtain ⟨U, hU, hUφ⟩ := hφ.level
  obtain ⟨U', hU', hUψ⟩ := hψ.level
  refine ⟨hφ.cont.add hψ.cont, hφ.supp.add hψ.supp, U ⊓ U', by rw [Subgroup.coe_inf]; exact hU.inter hU',
    fun u hu g => ?_⟩
  rw [Subgroup.mem_inf] at hu
  exact ⟨by rw [(hUφ u hu.1 g).1, (hUψ u hu.2 g).1], by rw [(hUφ u hu.1 g).2, (hUψ u hu.2 g).2]⟩

omit [IsCMField E] in
theorem isTest_smul [IsTotallyComplex E] {φ : GA E n → ℂ} (c : ℂ) (hφ : IsTest φ) : IsTest fun x => c * φ x := by
  obtain ⟨U, hU, hUφ⟩ := hφ.level
  refine ⟨continuous_const.mul hφ.cont, hφ.supp.mono fun x hx => right_ne_zero_of_mul hx, U, hU,
    fun u hu g => ?_⟩
  exact ⟨by rw [(hUφ u hu g).1], by rw [(hUφ u hu g).2]⟩

theorem regSupp_add {φ ψ : GA E n → ℂ} (hφ : RegSupp φ) (hψ : RegSupp ψ) : RegSupp fun x => φ x + ψ x := by
  intro d x h
  dsimp only at h
  by_cases h0 : φ (twConj (thetaA E n) x (ratGL E n d)) = 0
  · exact hψ d x (by rwa [h0, zero_add] at h)
  · exact hφ d x h0

theorem regSupp_smul {φ : GA E n → ℂ} (c : ℂ) (hφ : RegSupp φ) : RegSupp fun x => c * φ x :=
  fun d x h => hφ d x (right_ne_zero_of_mul h)

theorem vCAt_add {φ ψ : GA E n → ℂ} (hφ : IsTest φ) (hψ : IsTest ψ) (v : InfinitePlace E) (h₁ : VCAt v φ)
    (h₂ : VCAt v ψ) : VCAt v fun x => φ x + ψ x := fun g hg =>
  veryCusp_add (slice hφ.cont hφ.supp v g hg).1 (slice hφ.cont hφ.supp v g hg).2
    (slice hψ.cont hψ.supp v g hg).1 (slice hψ.cont hψ.supp v g hg).2 (h₁ g hg) (h₂ g hg)

theorem vCAt_smul {φ : GA E n → ℂ} (c : ℂ) (v : InfinitePlace E) (h : VCAt v φ) : VCAt v fun x => c * φ x :=
  fun g hg => veryCusp_smul c (h g hg)

end PSumH

open PSumH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem isTest2J_zero (r : ℝ) : IsTest2J (0 : GA E a × GA E b → ℂ) r :=
  ⟨⟨continuous_const, HasCompactSupport.zero, fun _ h => absurd rfl h,
    fun _ => ⟨isTest_zero, regSupp_zero, fun _ _ _ => veryCusp_zero⟩,
    fun _ => ⟨isTest_zero, regSupp_zero, fun _ _ _ => veryCusp_zero⟩⟩,
    ⊤, ⊤, isOpen_univ, isOpen_univ, fun _ _ _ _ _ => ⟨rfl, rfl⟩⟩

theorem isTest2J_smul {φ : GA E a × GA E b → ℂ} {r : ℝ} (c : ℂ) (h : IsTest2J φ r) : IsTest2J (c • φ) r := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hU⟩ := h.level
  refine ⟨⟨h.cont.const_smul c, h.supp.mono fun x hx => right_ne_zero_of_mul hx,
    fun g hg => h.size g (right_ne_zero_of_mul hg), fun g₂ => ?_, fun g₁ => ?_⟩,
    U₁, U₂, hU₁, hU₂, fun u₁ h₁ u₂ h₂ g => ?_⟩
  · obtain ⟨t, s, w⟩ := h.test₁ g₂
    exact ⟨isTest_smul c t, regSupp_smul c s, fun v => vCAt_smul c v (w v)⟩
  · obtain ⟨t, s, w⟩ := h.test₂ g₁
    exact ⟨isTest_smul c t, regSupp_smul c s, fun v => vCAt_smul c v (w v)⟩
  · exact ⟨by simp only [Pi.smul_apply, (hU u₁ h₁ u₂ h₂ g).1], by simp only [Pi.smul_apply, (hU u₁ h₁ u₂ h₂ g).2]⟩

theorem isTest2J_add {φ ψ : GA E a × GA E b → ℂ} {r : ℝ} (h : IsTest2J φ r) (h' : IsTest2J ψ r) :
    IsTest2J (φ + ψ) r := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hU⟩ := h.level
  obtain ⟨U₁', U₂', hU₁', hU₂', hU'⟩ := h'.level
  refine ⟨⟨h.cont.add h'.cont, h.supp.add h'.supp, fun g hg => ?_, fun g₂ => ?_, fun g₁ => ?_⟩,
    U₁ ⊓ U₁', U₂ ⊓ U₂', by rw [Subgroup.coe_inf]; exact hU₁.inter hU₁', by rw [Subgroup.coe_inf]; exact hU₂.inter hU₂',
    fun u₁ h₁ u₂ h₂ g => ?_⟩
  · by_cases h0 : φ g = 0
    · exact h'.size g (by simpa [h0] using hg)
    · exact h.size g h0
  · obtain ⟨t, s, w⟩ := h.test₁ g₂
    obtain ⟨t', s', w'⟩ := h'.test₁ g₂
    exact ⟨isTest_add t t', regSupp_add s s', fun v => vCAt_add t t' v (w v) (w' v)⟩
  · obtain ⟨t, s, w⟩ := h.test₂ g₁
    obtain ⟨t', s', w'⟩ := h'.test₂ g₁
    exact ⟨isTest_add t t', regSupp_add s s', fun v => vCAt_add t t' v (w v) (w' v)⟩
  · rw [Subgroup.mem_inf] at h₁ h₂
    exact ⟨by simp only [Pi.add_apply, (hU u₁ h₁.1 u₂ h₂.1 g).1, (hU' u₁ h₁.2 u₂ h₂.2 g).1],
      by simp only [Pi.add_apply, (hU u₁ h₁.1 u₂ h₂.1 g).2, (hU' u₁ h₁.2 u₂ h₂.2 g).2]⟩

theorem isTest2J_mono {φ : GA E a × GA E b → ℂ} {r r' : ℝ} (h : IsTest2J φ r) (hr : r ≤ r') : IsTest2J φ r' :=
  ⟨⟨h.cont, h.supp, fun g hg => ⟨(h.size g hg).1.trans hr, (h.size g hg).2.trans hr⟩, h.test₁, h.test₂⟩, h.level⟩

theorem isTest2J_sum {ι : Type*} (s : Finset ι) {φ : ι → GA E a × GA E b → ℂ} {r : ℝ}
    (h : ∀ i ∈ s, IsTest2J (φ i) r) : IsTest2J (∑ i ∈ s, φ i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isTest2J_zero r
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact isTest2J_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end PositivityTheory.Rg.BcB.CG

end
