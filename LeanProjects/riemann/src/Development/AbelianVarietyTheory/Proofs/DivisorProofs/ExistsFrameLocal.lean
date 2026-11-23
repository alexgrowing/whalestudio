import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionOfFrameIsFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprMapOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombAtGSubIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentOfChartFrameStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ChainPts
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ChainPts.SummandLat

theorem valF_zero_fun {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) : valF x U 0 = 0 := by
  unfold valF
  split_ifs <;> simp

theorem isLocalRing_intO (C : Type) [NormedField C] [IsUltrametricDist C] : IsLocalRing ↥(intO C) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  have key : ∀ c : ↥(intO C), ‖(c : C)‖ = 1 → IsUnit c := by
    intro c hc
    have h0 : (c : C) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hc
      exact zero_ne_one hc
    refine IsUnit.of_mul_eq_one (⟨(c : C)⁻¹, show ‖(c : C)⁻¹‖ ≤ 1 by rw [norm_inv, hc, inv_one]⟩ : ↥(intO C)) ?_
    exact Subtype.ext (mul_inv_cancel₀ h0)
  have ha : ‖(a : C)‖ ≤ 1 := a.2
  rcases ha.eq_or_lt with h | h
  · exact Or.inl (key a h)
  · refine Or.inr (key _ ?_)
    have : ‖(1 : C) + -(a : C)‖ = max ‖(1 : C)‖ ‖-(a : C)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one, norm_neg]; exact h.ne')
    rw [norm_one, norm_neg, max_eq_left h.le] at this
    simpa [sub_eq_add_neg] using this

theorem exists_frame_local {X : Scheme.{0}} {F : X.Modules} {r : ℕ} (hF : GlobalTheory.VB.IsVB F r) {R : Type} [CommRing R]
    [IsLocalRing R] (w : Sp R ⟶ X) :
    ∃ (V : X.Opens) (f : Fin r → Γ(F, V)), GlobalTheory.VB.IsFrame f ∧ ⊤ ≤ w ⁻¹ᵁ V := by
  obtain ⟨V, f, hV, hf⟩ := hF (w (closedPoint R))
  exact ⟨V, f, hf, ((IsLocalRing.closedPoint_mem_iff (w ⁻¹ᵁ V)).1 hV).ge⟩

theorem isLat_summand : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : LocM.Mdl Y i₀) {X : Scheme.{0}} (h : X ⟶ Z.X) {F F₁ : X.Modules} (i : F₁ ⟶ F) (q : F ⟶ F₁), i ≫ q = 𝟙 F₁ → ∀ {r r' : ℕ} (σ : Fin r' → Fin r), Function.Injective σ → GlobalTheory.VB.IsVB F r → ∀ (x : Fin r → Letter Dw) (d b : Bool) (s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)), IsLat Z h x d b F s → (∀ a k, i.app _ (q.app _ (s a (σ k))) = s a (σ k)) → (∀ a j, j ∉ Set.range σ → q.app _ (s a j) = 0) → IsLat Z h (fun k => x (σ k)) d b F₁ (fun a k => q.app _ (s a (σ k))) := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z X h F F₁ i q hiq r r' σ hσ hF x d b s hL hin hout
  have hfr : ∀ a, GlobalTheory.VB.IsFrame (fun k => q.app _ (s a (σ k))) := fun a =>
    GlobalTheory.T.projection_of_frame_is_frame i q hiq σ hσ (s a) (hL.frame a) (hin a) (hout a)
  refine ⟨hfr, ?_, ?_⟩
  · intro k _ w a a' φ φ' hφ hφ' l
    have hg := hL.glue k w a a' φ φ' hφ hφ' (σ l)
    have hc := GlobalTheory.ChainPts.AdaptedCoef.coef_adapted i q hiq σ hσ (s a) (s a') (hL.frame a) (hL.frame a') (hin a) (hout a) (hin a') (hout a')
      (hfr a) (hfr a') d l
    have ht : ∀ j, IsTanAtG (Y Z.i).t (w ≫ h ≫ Z.π) ((Z.fr a).bc φ (x j).1 (x j).2) := fun j => by
      have := GlobalTheory.T.tangent_of_chart_frame Z a k φ (w ≫ h) hφ (x j)
      rwa [Category.assoc] at this
    have h2 := (GlobalTheory.CombSub.isCombAtG_sub_iff (Y Z.i).t (w ≫ h ≫ Z.π) σ hσ _ ht _
      (fun j hj => by rw [hc.2 j hj]; exact valF_zero_fun _ _) _).1 hg
    have e : (fun m => valF w _ (coef d (hfr a) (hfr a') m l)) =
        fun m => valF w _ (coef d (hL.frame a) (hL.frame a') (σ m) (σ l)) := funext fun m => by rw [hc.1 m]
    rw [e]
    exact h2
  · intro y w hw a φ hφ V e he hV cf v hv
    haveI := isLocalRing_intO ↥y.C.S
    obtain ⟨V₀, f, hf, hV₀⟩ := exists_frame_local hF w
    have ht : ∀ j, IsTanAtG (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ (x j).1 (x j).2) := fun j =>
      GlobalTheory.T.tangent_of_chart_frame Z a _ φ y.gen hφ (x j)
    have hz : ∀ j, j ∉ Set.range σ → Function.extend σ cf 0 j = 0 := fun j hj =>
      Function.extend_apply' _ _ _ (by simpa using hj)
    have e1 : (fun k => Function.extend σ cf 0 (σ k)) = cf := funext fun k => hσ.extend_apply _ _ k
    have hv' := (GlobalTheory.CombSub.isCombAtG_sub_iff (Y Z.i).t (y.gen ≫ Z.π) σ hσ _ ht (Function.extend σ cf 0) hz v).2 (by rw [e1]; exact hv)
    rw [hL.norm y w hw a φ hφ V₀ f hf hV₀ _ v hv']
    exact GlobalTheory.ChainPts.SummandNorm.norm_le_one_iff i q hiq σ hσ (s a) (hL.frame a) (hin a) (hout a) (hfr a) f hf e he d _ w hV₀ hV cf

end GlobalTheory.ChainPts.SummandLat

end
