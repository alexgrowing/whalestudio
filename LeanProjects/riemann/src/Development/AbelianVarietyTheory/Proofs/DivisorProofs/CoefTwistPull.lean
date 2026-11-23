import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphism
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

noncomputable section

namespace GlobalTheory.Poinc.Tors

def LiesOver {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (w₀ : W0 U) (g : GtPtF D.toPre F) (w : Frm D.toPre F 1 g.b)
    (x : TFK (R := R) F ⟶ A.A) (fr : FrAt x) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ wk : Frm D.toPre F k g.b,
    (∀ z J, Good D.toPre.P.L z J → val wk (𝟙 _) z J = val w (𝟙 _) z J ^ k) → wk.IsGen →
    ∀ (s : SecA A F k) (s' : Fam D.toPre F k) (v : F),
      U.ExpandsF F k w₀ s s' → ValAt s x fr v → SumF I F (coef s' g wk) v

section
open GlobalTheory.UT.PullExp GlobalTheory.FieldBaseChange

theorem coef_twistPull : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∀ (E : EndU U.toUnifPre), Function.Injective E.h → ∀ (k' k : ℕ), 1 ≤ k → 1 ≤ k' → (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen) → (∃ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ) ∧ ∀ (w₀ : W0 U.toUnifPre) (ρ), NormW U.toUnifPre w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') s s', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w' : Frm D.toPre F k' g.b) (w : Frm D.toPre F k g'.b), w'.IsGen → w.IsGen → (∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J) → (∀ χ, coef s' g w' (E.h χ) = coef s g' w χ) ∧ ∀ β, β ∉ Set.range E.h → coef s' g w' β = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ E hh k' k hk hk' ⟨β₀, hβ₀⟩
  have hGF := hL.1.globalFns
  have := hI.1
  have := hI.2.2.2
  have := E.homG
  obtain ⟨β, hβ, hβ'⟩ := exists_normalised U.LG.isLB E.aG k' k β₀ hβ₀
  obtain ⟨κ₀, hκ₀, hrel⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL R I hI D A G hG U E k' k β hβ hβ'
  refine ⟨⟨κ₀, hκ₀⟩, ?_⟩
  intro w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' s s' ⟨v, hv, n, c, σ, f, h₁, h₂, h₃⟩ ⟨v', hv', hs'⟩ htw κ hκ g g' hg w' w hw' hw₁ hww
  choose σ' f' p₁ p₂ p₃ p₄ using fun i => GlobalTheory.T.pullback_section_endomorphism_expansion R I D A G U.toUnifPre E hh k' k β hβ κ₀ hκ₀.1 hrel (σ i) (f i) (h₁ i)
  have tw := GlobalTheory.T.endU_twist_of_iso hGF R I D A G U.toUnifPre E F k' k β hβ hβ' w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' v v' hv hv' htw
  have H := secLin_of_expandsG U.toUnifPre (IsAdicComplete.le_jacobson_bot I) F k' v' s' hs' n c σ' f' p₁
    ((secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => by
      rw [tw y J hJ, GlobalTheory.BoxExpansion.secLin_val h₂ _ y hJ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e₁ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
        rw [← Over.comp_left, whiskerLeft_fst]
      have e₂ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫ UnifPre.gFK (G := G) F =
          UnifPre.gFK (G := G) F ≫ E.aG.left := by
        rw [UnifPre.gFK, ← Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left, Category.assoc,
          Category.assoc]
        exact congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)
      rw [p₂ i _ _ y J hJ, gs_scal, gs_scal, e₁, e₂, Category.id_comp, Category.id_comp, _root_.mul_assoc])
  refine ⟨fun χ => CoefBasic.coef_eq fun z J hJ => ?_, fun b hb => CoefBasic.coef_eq fun z J hJ => ?_⟩
  · have a := CoefBasic.isCoef_coef g' hw₁ χ s z J hJ
    have e : g.b.left ≫ D.toPre.P.A.hom = (TF (R := R) F).hom := Over.w g.b
    have e' : g'.b.left = g.b.left ≫ E.aB.left := congrArg (fun q => q.left) hg.1
    rw [sval_comb (h₃ χ) _ z hJ, hg.2 χ z J hJ, ← hww z J hJ, e', normd_val_eq hGF hκ hκ₀ _ z J hJ] at a
    rw [sval_comb (H (E.h χ)) _ z hJ]
    simp only [p₃ _ χ _ _ z J hJ, e, ← _root_.mul_assoc, ← Finset.sum_mul]
    have e₃ : (rigV D.toPre (TF (R := R) F).hom z J).val ^ k' =
        (rigV D.toPre (TF (R := R) F).hom z J).val ^ k * (rigV D.toPre (TF (R := R) F).hom z J ^ ((k' : ℤ) - k)).val := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_natCast,
        ← zpow_add, add_sub_cancel]
    rw [e₃, ← _root_.mul_assoc, a]
    simp only [Units.val_mul]
    ring
  · rw [sval_comb (H b) _ z hJ, CoefBasic.cst_eq, map_zero, zero_mul, Finset.sum_eq_zero, zero_mul, zero_mul]
    intro i _
    exact (congrArg _ ((congrArg (gs _ z _) (p₄ i b hb _)).trans (gs_zero' _ z _ (hJ.mem _ _)))).trans (mul_zero _)

end

section
open GlobalTheory.UT.EvalZero GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

theorem sumF_origin : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∃ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen) ∧ (∀ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen → ∃ w₀, NormW U.toUnifPre w₀ ρ) ∧ ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (k : ℕ) (t : SecA A F k) s, U.ExpandsF F k w₀ t s → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b), g.IsZero → FrmOne w → ∀ c : F, (∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val) → SumF I F (coef s g w) c := by
  intro _ R _ _ _ I hI D A G _ _ _ U F _ _
  refine ⟨exists_gen_pt (Y := Spec (CommRingCat.of (FractionRing R))) A.isLB
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
      (fun y => Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _) _ _,
    exists_normW U.toUnifPre, ?_⟩
  rintro w₀ ρ h k t s ⟨σ', hR, n, c, σ, f, hE, hσ, hs⟩ g w hg hw b hb
  choose a ha using fun i α => exists_value D.toPre k α (f i α)
  choose x hx using fun i => exists_coeff (A := R) U.LG.isLB (σ i) (eSec G) (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig k)
    (powGen_isGen _ _ _ _ U.LG.rigGen k) (fun W _ f => by simp)
  have hx' : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good U.LG.L z J →
      sval (σ i) (r ≫ eSec G) z J = Geo.Tor.cst r z (x i) * (val (L := U.LG.L) U.LG.rig r z J ^ k).val :=
    fun i Z r z J hJ => (hx i Z r z J hJ).trans (by rw [val_pow])
  rw [value_comb U.toUnifPre F h t σ' hR c σ hσ x hx' b hb,
    funext fun α => coef_comb F s c f α (hs α) (fun i => a i α) (fun i => ha i α) g w hg hw]
  exact sumF_comb hI F _ c _ _ fun i => sumF_map I F (a i) (x i) fun e =>
    value_sub_sum_mem U.toUnifPre e k (σ i) (f i) (hE i e) (x i) (hx' i) (a i) (ha i)

end

end GlobalTheory.Poinc.Tors
end
