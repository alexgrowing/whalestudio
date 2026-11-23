import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerIrreducibleFinitePlaceCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DiagWSB

variable {F : Type} [Field F] [NumberField F] {v : Pl F} {κ : Type} [Fintype κ]

def diagG (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (Φ : (κ ⊕ κ → Fv F v) → ℂ)
    (w : (κ → Fv F v) × (κ → Fv F v)) : ℂ :=
  ∫ x, ψ (x ⬝ᵥ w.2) * Φ (Sum.elim (x + w.1) x) ∂μ

omit [Fintype κ] in
theorem elim_add_elim {R : Type} [AddCommGroup R] (a b c d : κ → R) :
    Sum.elim a b + Sum.elim c d = Sum.elim (a + c) (b + d) := by
  funext i; rcases i with i | i <;> rfl

theorem elim_dot_elim {R : Type} [CommRing R] (a b c d : κ → R) :
    Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem diagW_eq (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (Φ : (κ ⊕ κ → Fv F v) → ℂ)
    (w : (κ → Fv F v) × (κ → Fv F v)) :
    diagW ψ μ Φ w = ψ (⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * diagG ψ μ Φ w := by
  unfold diagW diagG
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [schr, elim_dot_elim, dotProduct_zero, zero_dotProduct, add_zero, elim_add_elim]
  rw [AddChar.map_add_eq_mul]
  ring

omit [Fintype κ] in
theorem continuous_elim_add (a : κ → Fv F v) : Continuous fun x : κ → Fv F v => Sum.elim (x + a) x :=
  continuous_pi fun i => by rcases i with i | i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

theorem integrable_integrand (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (μ : @Measure (κ → Fv F v) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (Φ : (κ ⊕ κ → Fv F v) → ℂ) (hΦ : Φ ∈ SB (κ ⊕ κ → Fv F v))
    (w : (κ → Fv F v) × (κ → Fv F v)) :
    Integrable (fun x => ψ (x ⬝ᵥ w.2) * Φ (Sum.elim (x + w.1) x)) μ := by
  let _ : MeasurableSpace (κ → Fv F v) := borel _
  have _ : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  have _ := hμ
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hψ.comp (continuous_id.dotProduct continuous_const)).mul
      (hΦ.1.continuous.comp (continuous_elim_add w.1))
  · apply HasCompactSupport.mul_left
    refine HasCompactSupport.intro (K := (fun y : κ ⊕ κ → Fv F v => y ∘ Sum.inr) '' tsupport Φ)
      (hΦ.2.image (by fun_prop)) ?_
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hx ⟨_, h, rfl⟩

theorem diagG_zero (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) :
    diagG ψ μ (0 : (κ ⊕ κ → Fv F v) → ℂ) = 0 := by
  funext w; simp [diagG]

theorem diagG_add (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (μ : @Measure (κ → Fv F v) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) {Φ Ψ : (κ ⊕ κ → Fv F v) → ℂ} (hΦ : Φ ∈ SB (κ ⊕ κ → Fv F v))
    (hΨ : Ψ ∈ SB (κ ⊕ κ → Fv F v)) : diagG ψ μ (Φ + Ψ) = diagG ψ μ Φ + diagG ψ μ Ψ := by
  funext w
  simp only [diagG, Pi.add_apply, mul_add]
  exact integral_add (integrable_integrand ψ hψ μ hμ Φ hΦ w) (integrable_integrand ψ hψ μ hμ Ψ hΨ w)

theorem diagG_smul (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (a : ℂ)
    (Φ : (κ ⊕ κ → Fv F v) → ℂ) : diagG ψ μ (a • Φ) = a • diagG ψ μ Φ := by
  funext w
  simp only [diagG, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr 1; funext x; ring

theorem diagG_schr (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (Φ : (κ ⊕ κ → Fv F v) → ℂ) (p₁ p₂ q₁ q₂ : κ → Fv F v)
    (w : (κ → Fv F v) × (κ → Fv F v)) :
    diagG ψ μ (schr ψ (Sum.elim p₁ p₂, Sum.elim q₁ q₂) Φ) w =
      ψ (-(p₂ ⬝ᵥ w.2) + (w.1 - p₂) ⬝ᵥ q₁ - p₂ ⬝ᵥ q₂ + ⅟(2 : Fv F v) * (p₁ ⬝ᵥ q₁ + p₂ ⬝ᵥ q₂)) *
        diagG ψ μ Φ (w + (p₁ - p₂, q₁ + q₂)) := by
  let _ : MeasurableSpace (κ → Fv F v) := borel _
  have _ : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  have _ := hμ
  unfold diagG
  rw [← integral_sub_right_eq_self _ p₂, ← integral_const_mul]
  congr 1
  funext x
  simp only [schr, elim_dot_elim, elim_add_elim, Prod.fst_add, Prod.snd_add]
  have e : Sum.elim (x - p₂ + w.1 + p₁) (x - p₂ + p₂) = Sum.elim (x + (w.1 + (p₁ - p₂))) x := by
    congr 1 <;> abel
  rw [e, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
  ring

theorem sb_mul {X : Type} [TopologicalSpace X] {f g : X → ℂ} (hf : IsLocallyConstant f) (hg : g ∈ SB X) :
    (fun w => f w * g w) ∈ SB X :=
  ⟨hf.mul hg.1, hg.2.mul_left⟩

theorem sb_mul_translate {X : Type} [TopologicalSpace X] [AddGroup X] [ContinuousAdd X] {f g : X → ℂ}
    (hf : IsLocallyConstant f) (hg : g ∈ SB X) (t : X) : (fun w => f w * g (w + t)) ∈ SB X :=
  ⟨hf.mul (hg.1.comp_continuous (continuous_add_right t)), (hg.2.comp_homeomorph (Homeomorph.addRight t)).mul_left⟩

omit [Fintype κ] in
theorem isLocallyConstant_indicator {X : Type} [TopologicalSpace X] {S : Set X} (hS : IsClopen S) (c : ℂ) :
    IsLocallyConstant (S.indicator fun _ => c) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ S
  · exact ⟨S, hS.isOpen, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨Sᶜ, hS.compl.isOpen, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

theorem diagW_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ]
    (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ₀ ∈ SB (κ ⊕ κ → Fv F v), ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U →
      0 ∈ U → (∀ w, diagW ψ μ Φ₀ w = U.indicator (fun _ => c) w) →
    ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v)) := by
  intro F _ _ v κ _ ψ hψ h1 μ hμ Φ₀ hΦ₀ c hc U hUo hUc h0U hU Φ hΦ
  have _ := GlobalTheory.WeilM.nonarch_field (Fv F v)
  have hlc := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ

  have hph : ∀ a : Fv F v, IsLocallyConstant fun w : (κ → Fv F v) × (κ → Fv F v) => ψ (a * (w.1 ⬝ᵥ w.2)) :=
    fun a => hlc.comp_continuous (continuous_const.mul (continuous_fst.dotProduct continuous_snd))
  let N : Submodule ℂ ((κ ⊕ κ → Fv F v) → ℂ) :=
    { carrier := {Φ | Φ ∈ SB (κ ⊕ κ → Fv F v) ∧ diagG ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v))}
      zero_mem' := ⟨zero_mem _, by rw [diagG_zero]; exact zero_mem _⟩
      add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by
        rw [diagG_add ψ hψ μ hμ ha.1 hb.1]; exact add_mem ha.2 hb.2⟩
      smul_mem' := fun a Φ h => ⟨Submodule.smul_mem _ a h.1, by
        rw [diagG_smul]; exact Submodule.smul_mem _ a h.2⟩ }
  have hNle : N ≤ SB (κ ⊕ κ → Fv F v) := fun Φ h => h.1
  have hS : ∀ w, ∀ φ ∈ N, schr ψ w φ ∈ N := by
    rintro ⟨P, Q⟩ φ ⟨hφ1, hφ2⟩
    refine ⟨GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ (P, Q) φ hφ1, ?_⟩
    rw [← Sum.elim_comp_inl_inr P, ← Sum.elim_comp_inl_inr Q]
    have e : diagG ψ μ (schr ψ (Sum.elim (P ∘ Sum.inl) (P ∘ Sum.inr), Sum.elim (Q ∘ Sum.inl) (Q ∘ Sum.inr)) φ) =
        fun w => ψ (-((P ∘ Sum.inr) ⬝ᵥ w.2) + (w.1 - P ∘ Sum.inr) ⬝ᵥ (Q ∘ Sum.inl) - (P ∘ Sum.inr) ⬝ᵥ (Q ∘ Sum.inr) +
          ⅟(2 : Fv F v) * ((P ∘ Sum.inl) ⬝ᵥ (Q ∘ Sum.inl) + (P ∘ Sum.inr) ⬝ᵥ (Q ∘ Sum.inr))) *
          diagG ψ μ φ (w + (P ∘ Sum.inl - P ∘ Sum.inr, Q ∘ Sum.inl + Q ∘ Sum.inr)) :=
      funext fun w => diagG_schr ψ μ hμ φ _ _ _ _ w
    rw [e]
    refine sb_mul_translate (hlc.comp_continuous ?_) hφ2 _
    fun_prop

  have hUcl : IsClopen U := ⟨hUc.isClosed, hUo⟩
  have hW₀ : diagW ψ μ Φ₀ ∈ SB ((κ → Fv F v) × (κ → Fv F v)) := by
    rw [show diagW ψ μ Φ₀ = U.indicator (fun _ => c) from funext hU]
    exact ⟨isLocallyConstant_indicator hUcl c,
      HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx _⟩
  have hG : ∀ Φ : (κ ⊕ κ → Fv F v) → ℂ, diagG ψ μ Φ =
      fun w => ψ (-⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * diagW ψ μ Φ w := by
    intro Φ
    funext w
    rw [diagW_eq, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  have h0N : Φ₀ ∈ N := ⟨hΦ₀, by rw [hG]; exact sb_mul (hph _) hW₀⟩
  have hne : Φ₀ ≠ 0 := by
    rintro rfl
    have h := hU 0
    rw [Set.indicator_of_mem h0U, diagW_zero] at h
    simp at h
    exact hc h.symm
  have hN := GlobalTheory.SchrIrred.schr_irreducible v ψ hψ h1 N hNle hS Φ₀ h0N hne
  have hΦN : Φ ∈ N := hN ▸ hΦ
  rw [show diagW ψ μ Φ = fun w => ψ (⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * diagG ψ μ Φ w from funext (diagW_eq ψ μ Φ)]
  exact sb_mul (hph _) hΦN.2

end GlobalTheory.DiagWSB

end
