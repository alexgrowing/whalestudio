import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNhdsAvoidingImagesOfSpecializationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionSplitRegularDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtIffForallSpecializesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep.LiftFn

variable {Y : Scheme.{0}}

theorem eq_of_specializes_of_coheight {v w : Y} (h : v ⤳ w) (hv : Order.coheight v = 1)
    (hw : Order.coheight w = 1) : v = w := by
  by_contra hne
  have hlt : w < v := lt_of_le_not_ge h fun e => hne (Specializes.antisymm h e).eq
  have h₃ := Order.coheight_add_one_le hlt
  rw [hv, hw] at h₃
  exact absurd h₃ (by decide)

variable [IsIntegral Y] [IsLocallyNoetherian Y]

theorem mult_neg (F : CartierDiv Y) (z : Y) : (-F).mult z = -F.mult z := by
  have e := CartierDiv.mult_add F (-F) z
  rw [add_neg_cancel, (CartierDiv.isEqn_zero (X := Y) z).mult_eq, Units.val_one, (unitAt_one z).ord_eq_zero] at e
  omega

end GlobalTheory.PairStep.LiftFn

namespace GlobalTheory.PairStep

open LiftFn in

theorem exists_lifted_fn : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), IsLogRes p n η m G s K B → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → F.mult v ≤ 0) → s σ ⤳ y → Order.coheight σ = 1 → ∃ h : Y.functionField, (-F).RegularAt σ (h - 1) ∧ ∀ v : Y, v ≠ σ → Order.coheight v = 1 → s v ⤳ y → (-F).RegularAt v h := by
  intro X _ _ p n hp _ η m G N Y _ _ s _ K B F hres hcoh y σ hF hσy hσ
  have hpr : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have hspr : IsProper (s ≫ p) :=
    ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hres.proj).1
  haveI : IsProper s := IsProper.of_comp s p
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (s ≫ p)
  haveI := hres.smooth
  haveI := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth (s ≫ p)

  set T : Set Y := {v | v ≠ σ ∧ 0 < F.mult v} with hTdef
  have hT : T.Finite := F.finite_support_mult.subset fun v hv => hv.2.ne'
  obtain ⟨U, e, hUa, hyU, hNe, hav⟩ := GlobalTheory.T.exists_affine_nhds_avoiding_images_of_specializations X Y s T σ y N hT
    fun v hv w hvw hσw hwy => not_le.2 hv.2 (hF v w hv.1 hvw hσw hwy)
  have hTc : IsClosed (⋃ v ∈ T, closure ({v} : Set Y)) :=
    hT.isClosed_biUnion fun _ _ => isClosed_closure
  set W₁ : Y.Opens := s ⁻¹ᵁ U ⊓ ⟨_, hTc.isOpen_compl⟩ with hW₁
  set W₂ : Y.Opens := s ⁻¹ᵁ U ⊓ ⟨_, (isClosed_closure (s := ({σ} : Set Y))).isOpen_compl⟩ with hW₂
  have hW : W₁ ⊔ W₂ = s ⁻¹ᵁ U := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun w hw => ?_
    by_cases hwσ : w ∈ closure ({σ} : Set Y)
    · refine Or.inl ⟨hw, fun hwT => ?_⟩
      obtain ⟨v, hv, hwv⟩ := Set.mem_iUnion₂.1 hwT
      exact hav v hv w (specializes_iff_mem_closure.2 hwv) (specializes_iff_mem_closure.2 hwσ) hw
    · exact Or.inr ⟨hw, hwσ⟩
  have hc := hcoh U hUa
  rw [← hW] at hc
  set e' : Y.functionFieldˣ := fnPull s e with he'
  have key : ∀ w ∈ s ⁻¹ᵁ U, ∀ f : Y.functionField,
      (pullCart s N - F).RegularAt w f ↔ (-F).RegularAt w (f * e') := by
    intro w hw f
    obtain ⟨g, hg⟩ := F.exists_isEqn w
    rw [((isEqn_pullCart s (hNe _ hw)).sub hg).regularAt_iff, hg.neg.regularAt_iff]
    have : f * ((fnPull s e / g : Y.functionFieldˣ) : Y.functionField) =
        f * (e' : Y.functionField) * ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
      rw [Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, he']
      ring
    rw [this]
  have hinv : ∀ x ∈ W₁ ⊓ W₂, (pullCart s N - F).RegularAt x (e' : Y.functionField)⁻¹ := by
    intro x hx
    rw [key x hx.1.1, inv_mul_cancel₀ e'.ne_zero]
    have h1 := (GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg Y (-F) x 1).2
    rw [Units.val_one] at h1
    refine h1 fun z hzx => ?_
    rw [(unitAt_one z).ord_eq_zero, zero_add, mult_neg]
    refine neg_nonneg.2 (not_lt.1 fun hz => ?_)
    by_cases hzσ : z = σ
    · subst hzσ
      exact hx.2.2 (specializes_iff_mem_closure.1 hzx)
    · exact hx.1.2 (Set.mem_iUnion₂.2 ⟨z, ⟨hzσ, hz⟩, specializes_iff_mem_closure.1 hzx⟩)
  obtain ⟨h₁, h₂, hsplit, hh₁, hh₂⟩ :=
    GlobalTheory.T.rational_function_split_regular_divisor Y (pullCart s N - F) W₁ W₂ hc (e' : Y.functionField)⁻¹ hinv
  have hσU : σ ∈ s ⁻¹ᵁ U := hσy.mem_open U.isOpen hyU
  refine ⟨h₂ * e', ?_, fun v hvσ hv hvy => ?_⟩
  · have hσW : σ ∈ W₁ := ⟨hσU, fun hσT => by
      obtain ⟨v, hv, hσv⟩ := Set.mem_iUnion₂.1 hσT
      exact hv.1 (eq_of_specializes_of_coheight (specializes_iff_mem_closure.2 hσv)
        (CartierDiv.coheight_eq_one_of_mult_ne_zero hv.2.ne') hσ)⟩
    have e₁ : h₂ * (e' : Y.functionField) - 1 = h₁ * e' := by
      rw [show h₂ = (e' : Y.functionField)⁻¹ + h₁ by rw [hsplit]; ring, add_mul,
        inv_mul_cancel₀ e'.ne_zero]
      ring
    rw [e₁]
    exact (key σ hσU h₁).1 (hh₁ σ hσW)
  · have hvU : v ∈ s ⁻¹ᵁ U := hvy.mem_open U.isOpen hyU
    have hvW : v ∈ W₂ := ⟨hvU, fun hvσ' =>
      hvσ (eq_of_specializes_of_coheight (specializes_iff_mem_closure.2 hvσ') hσ hv).symm⟩
    exact (key v hvU h₂).1 (hh₂ v hvW)

end GlobalTheory.PairStep
