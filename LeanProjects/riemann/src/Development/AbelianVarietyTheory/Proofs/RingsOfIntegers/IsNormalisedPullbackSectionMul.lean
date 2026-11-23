import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullMulValue

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PullComp

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A)

theorem isNormPull_comp (φ ψ : A ⟶ A) [IsMonHom ψ] (a b c : ℤ) {T : Over S} {s : LB.Sec (LPow A L.L a T)}
    {s' : LB.Sec (LPow A L.L b T)} {s'' : LB.Sec (LPow A L.L c T)} (h : IsNormPull A L φ b a s s')
    (h' : IsNormPull A L ψ c b s' s'') : IsNormPull A L (ψ ≫ φ) c a s s'' := by
  have hL := L.isLB
  have he : eSec A ≫ ψ.left = eSec A := by simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨β₀, β, hβ₀, nβ, cβ, tβ⟩ := h
  obtain ⟨δ₀, δ, hδ₀, nδ, cδ, tδ⟩ := h'
  obtain ⟨α₀, hα₀, hv₀⟩ := exists_gen hL (φ' := ![𝟙 A.left, (ψ ≫ φ).left]) (ε' := ![c, -a])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, Over.comp_left, zpow_neg]
      rw [_root_.mul_assoc, inv_mul_cancel_left])
    (LB.mulGen L.L _ _ _ _ δ₀ (LB.pullGen L.L _ _ β₀ ψ.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hδ₀ (DVR.pullGen_isGen _ _ _ _ hβ₀ _))
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ≫ ψ ≫ φ).left]) (ε' := ![c, -a])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ c) (Category.comp_id _)
      · rfl)
    (LB.pullGen L.L ![𝟙 A.left, (ψ ≫ φ).left] ![c, -a] α₀ (snd T A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  refine ⟨α₀, α, hα₀, corr_of_val hL fun y J hJ => ?_, corr_of_val hL fun y J hJ => hv _ _ y J hJ,
    ThetaLin.isTwistPull_of_sval A hL hα fun y J hJ => ?_⟩
  · have e₁ := val_corr hJ nβ (𝟙 _)
    have e₂ := val_corr hJ nδ (𝟙 _)
    rw [val_pull hJ, val_mul hJ, UT.PullMul.val_rigPow, UT.PullMul.val_rigPow] at e₁ e₂
    rw [val_pull hJ, hv₀ _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, he, e₁, e₂, val_mul hJ,
      UT.PullMul.val_rigPow, UT.PullMul.val_rigPow, zpow_neg _ b, _root_.mul_assoc, inv_mul_cancel_left]
  · have e₁ : (endOver A T ψ).left ≫ (snd T A).left = (snd T A).left ≫ ψ.left := by
      rw [← Over.comp_left, lift_snd, Over.comp_left]
    have e₂ : (endOver A T ψ).left ≫ (endOver A T φ).left = (endOver A T (ψ ≫ φ)).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc]
    rw [ThetaLin.sval_of_isTwistPull A tδ _ y hJ, ThetaLin.sval_of_isTwistPull A tβ _ y hJ, val_corr hJ cδ,
      val_corr hJ cβ, hv _ _ y J hJ, val_pull hJ, val_pull hJ, val_pull hJ, hv₀ _ _ y J hJ, val_mul hJ, val_pull hJ,
      Units.val_mul, _root_.mul_assoc]
    simp only [Category.assoc, e₁, e₂]

theorem pulls_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (a b : 𝓞 E) (k k' k'' : ℕ) (F : SecN Xo x k) (F' : SecN Xo x k') (F'' : SecN Xo x k''), Pulls Xo a F F' → Pulls Xo b F' F'' → Pulls Xo (a * b) F F'' := by
  intro E _ _ _ H Dw l Xo S _ x a b k k' k'' F F' F'' h h'
  have := Xo.univ.t.act.hom b
  unfold Pulls
  rw [_root_.mul_comm a b, Xo.univ.t.act.mul]
  exact isNormPull_comp _ _ _ _ _ _ h h'

end GlobalTheory.PullComp
