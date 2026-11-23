import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNMul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ParTranslate
open GlobalTheory.UT GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar GlobalTheory.ThetaTranslate ReciprocityTheory.ChartRestriction.G.DVR

theorem toStk_onto {F : Type} [Field F] (z : Sp F) : Function.Surjective (toStk z) := fun a => by
  obtain ⟨U, hU, f, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => (Subsingleton.elim (α := PrimeSpectrum F) z y) ▸ hU
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 f
  exact ⟨x, rfl⟩

theorem isAdd_comm {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {g g' g'' : GtPtF D F} (h : g.IsAdd g' g'') : g'.IsAdd g g'' := by
  rw [isAdd_iff] at h ⊢
  refine ⟨h.1.trans (mul_comm _ _), fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  rw [C.s12, h.2 χ y J hJ, mul_comm]

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
  (w : W0 U)

abbrev Carries (t : SecA A F k) (σ : U.SecGF F k) : Prop :=
  GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w
    (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k
    (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) σ

theorem exists_carries (hw : w.IsGen) (σ : U.SecGF F k) : ∃ t, Carries U F k w t σ := by
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have hn' : U.genF F ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  obtain ⟨-, i₂⟩ := isoRelM_bijective (k := k) (m := (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left)
    (g₁ := (snd (TFK (R := R) F) A.A).left) (h₁ := (U.genF F).left) A.isLB U.LG.isLB hw
    (congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')
  exact (i₂ σ).exists

theorem exists_unit_carries (a : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (l : U.LG.L.ι)
    (hl : ⊤ ≤ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l) (y : Sp F)
    (J : (Sp F ⟶ A.A.left) → A.L.ι) (hJ : Good A.L y J) :
    ∃ c : ((Sp F).presheaf.stalk y)ˣ, ∀ t σ, Carries U F k w t σ →
      toStk y (valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a).left) _ (σ.f (fun _ => l))) =
        c.val * secVal t (show Sp F ⟶ _ from (ptSecT A.A (a ≫ U.gen.hom)).left) y J := by
  let r : Sp F ⟶ (UnifPre.GF (G := G) F).left := (lift (𝟙 (TFK (R := R) F)) a).left
  let r' : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e₀ : r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = a.left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) a)
  have e₁ : r ≫ (U.genF F).left = r' := by
    have : lift (𝟙 (TFK (R := R) F)) a ≫ U.genF F = ptSecT A.A (a ≫ U.gen.hom) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
    exact congrArg (fun q => q.left) this
  have e₂ : r' ≫ (snd (TFK (R := R) F) A.A).left =
      (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ U.gen.hom.left := by
    rw [e₀]
    exact congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) (a ≫ U.gen.hom))
  have m₂ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R)) y ∈
      U.LG.L.U l := by
    rw [e₀]
    exact (top_le_iff_mem _ _ y).1 hl
  have m₁ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ U.gen.hom.left) y ∈
      A.L.U (J (r' ≫ (snd (TFK (R := R) F) A.A).left)) := by
    rw [← e₂]
    exact hJ _
  refine ⟨isoVal w (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) y l
    (J (r' ≫ (snd (TFK (R := R) F) A.A).left)) ^ (k : ℤ), fun t σ h => ?_⟩
  have H := (isoRelM_iff w _ k _ h.1 _ h.2.1 t σ).1 h (Sp F) r y l _ m₂ m₁
  rw [Category.comp_id, e₁] at H
  exact (toStk_valF_gs r _ y (mem_wchart.2 fun _ => m₂) _).trans H

theorem exists_const_actVal (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F))
    (a a' : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (h : a' ≫ U.gen.hom = θ.pt * (a ≫ U.gen.hom))
    (l l' : U.LG.L.ι)
    (hl : ⊤ ≤ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l)
    (hl' : ⊤ ≤ (show Sp F ⟶ G.left from a'.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l') :
    ∃ c : F, c ≠ 0 ∧ ∀ t t' σ σ', Carries U F k w t σ → Carries U F k w t' σ' → ActVal θ t t' →
      valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a).left) _ (σ'.f (fun _ => l)) =
        c * valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a').left) _ (σ.f (fun _ => l')) := by
  let y : Sp F := IsLocalRing.closedPoint F
  obtain ⟨J, hJ⟩ := GlobalTheory.UT.CoefBasic.exists_good' A.isLB y
  obtain ⟨c, hc⟩ := exists_unit_carries U F k w a l hl y J hJ
  obtain ⟨c', hc'⟩ := exists_unit_carries U F k w a' l' hl' y J hJ
  let r : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e : r ≫ (translT A.A θ.pt).left = (ptSecT A.A (a' ≫ U.gen.hom)).left := by
    rw [h]
    exact congrArg (fun q => q.left) (ptSecT_translT (a ≫ U.gen.hom) θ.pt)
  obtain ⟨d, hd⟩ := toStk_onto y (c * thetaVal θ r y J * c'⁻¹).val
  refine ⟨d, fun h0 => ?_, fun t t' σ σ' h₁ h₂ h₃ => (toStk y).injective ?_⟩
  · have : Nontrivial ((Sp F).presheaf.stalk y) := inferInstance
    rw [h0, map_zero] at hd
    exact Units.ne_zero _ hd.symm
  · have a₁ := h₃ (Sp F) r y J hJ
    rw [e] at a₁
    rw [map_mul, hd, hc t' σ' h₂, hc' t σ h₁, Units.val_mul, Units.val_mul, _root_.mul_assoc,
      Units.inv_mul_cancel_left, _root_.mul_assoc]
    exact congrArg _ a₁

end

theorem parAt_translate : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) k) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (a a' : u.PtC) (g g' : GtPtF u.D.toPre (PadicAlgCl p)), 1 ≤ k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → a' ≫ u.U.gen.hom = x * (a ≫ u.U.gen.hom) → GtPtF.IsAdd pk.g g g' → u.ParAt k a g → u.ParAt k a' g' := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u k pk x a a' g g' hk hx ha hg hpar w' hw' l' hl'
  have hG := hL.1.globalFns
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  obtain ⟨w₀, hw₀⟩ := u.U.toUnifPre.ext
  obtain ⟨v, hv⟩ := exists_normalisation (D := u.D.toPre) (F := PadicAlgCl p) k pk.g.b
  obtain ⟨ω₀, h₀⟩ := exists_normalisation (D := u.D.toPre) (F := PadicAlgCl p) k g.b
  obtain ⟨ω₁, h₁, -, hco⟩ := CoefPhi.coef_phi hL u.V _ hA u.D (PadicAlgCl p) k hk pk v hv g g' (isAdd_comm hg) ω₀ h₀
  replace hco := hco 1 k le_rfl (mul_one k).symm pk (one_smul _ _).symm rfl v ω₀ ω₁
    ⟨hv, fun _ _ _ => (pow_one _).symm⟩ ⟨h₀, fun _ _ _ => (pow_one _).symm⟩ ⟨h₁, fun _ _ _ => (pow_one _).symm⟩
  obtain ⟨c₁, hc₁, -, hfr⟩ := ((CoefBasic.coef_basic u.V u.D.toPre (PadicAlgCl p) k g').2.2 ω₁ h₁).2.2.1 w' hw'
  obtain ⟨θ, rfl, hθ⟩ := exists_theta_actVal u.U (PadicAlgCl p) hG hL.1.kerPow hk pk x hx w₀ hw₀ v hv
  obtain ⟨l, hl⟩ := exists_chart u.U.LG.isLB (u.toG a (IsLocalRing.closedPoint (PadicAlgCl p)))
  replace hl := (top_le_iff_mem _ _ _).2 hl
  obtain ⟨κ, hκ, hsum⟩ := hpar ω₀ h₀ l hl
  obtain ⟨c₂, hc₂, hval⟩ := exists_const_actVal u.U.toUnifPre (PadicAlgCl p) k w₀ θ a a' ha l l' hl hl'
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG u.U (PadicAlgCl p) hk w₀ hw₀
  refine ⟨c₁ * (κ * c₂), mul_ne_zero hc₁ (mul_ne_zero hκ hc₂), fun σ s hs => ?_⟩
  obtain ⟨t, ht⟩ := exists_carries u.U.toUnifPre (PadicAlgCl p) k w₀ hw₀ σ
  obtain ⟨t', ht'⟩ := exists_actVal u.A.isLB θ t
  have hE : u.U.toUnifPre.ExpandsF (PadicAlgCl p) k w₀ t' (e t') := (he _ _).2 rfl
  have hΦ := (hθ t t' s (e t') ⟨σ, ht, hs⟩ hE).2 ht'
  obtain ⟨σ', hσ', hs'⟩ := hE
  have H := hsum σ' _ hs'
  rw [hval t t' σ σ' ht hσ' ht', ← (Equiv.addRight pk.y).hasSum_iff] at H
  have H' := H.mul_left c₁
  rw [_root_.mul_assoc, _root_.mul_assoc]
  refine (congrArg (HasSum · _) (funext fun χ => ?_)).mp H'
  exact (congrArg (c₁ * ·) (hco s _ hΦ χ)).trans (hfr s χ).symm

end GlobalTheory.ZH.ParTranslate
end
