import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRangeOfCls
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFETranslateFeTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ScalCompSpecMap
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj
open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Bdy

section Transl

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def FERel (mu α : D.X) (s : SecFMod D (FractionRing R) 1 α) (t : SecFMod D (FractionRing R) 1 (α + 1 • mu)) : Prop :=
  ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (FractionRing R) 1 α mu) (DegPre.deltaε 1)), u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D (FractionRing R)).left)
      (DegPre.famMult D (FractionRing R) 1 mu α) →
    GeneratorPullback.SecRel D.P.L (DegPre.famφ D (FractionRing R) (α + 1 • mu)) (DegPre.famε 1) t
      (DegPre.famφ D (FractionRing R) α) (DegPre.famε 1) s (DegPre.trF D (FractionRing R) mu).left
      (DegPre.deltaφ D (FractionRing R) 1 α mu) (DegPre.deltaε 1) u

variable {D}

theorem feRel_iff {mu α : D.X} {s : SecFMod D (FractionRing R) 1 α} {t : SecFMod D (FractionRing R) 1 (α + 1 • mu)} :
    FERel D mu α s t ↔ ∀ y J, Good D.P.L y J → sval t (𝟙 _) y J =
      sval s (𝟙 _ ≫ (DegPre.trF D (FractionRing R) mu).left) y J *
        (uVal D (FractionRing R) 1 α (cP D _ mu) (𝟙 _) y J *
          val (DegPre.famMult D (FractionRing R) 1 mu α) (𝟙 _ ≫ fst (TF (R := R) (FractionRing R)) D.P.A).left y J).val := by
  obtain ⟨⟨u₀, hu₀, hc₀⟩, hv⟩ := gen_fe (D := D) (F := FractionRing R) GlobalTheory.globalFns_holds 1 mu α
  constructor
  · intro H y J hJ
    rw [← hv u₀ hu₀ hc₀ _ (𝟙 _) y J hJ]
    exact (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u₀).1 (H u₀ hu₀ hc₀) _ _ y J hJ
  · intro H u hu hc
    refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
    have := H y J hJ
    rw [← hv u hu hc _ (𝟙 _) y J hJ] at this
    exact this

theorem FERel.unique {mu α : D.X} {s : SecFMod D (FractionRing R) 1 α} {t t' : SecFMod D (FractionRing R) 1 (α + 1 • mu)}
    (h : FERel D mu α s t) (h' : FERel D mu α s t') : t = t' :=
  sec_ext' D.P.isLB fun y J hJ => (feRel_iff.1 h y J hJ).trans (feRel_iff.1 h' y J hJ).symm

theorem FERel.smul {mu α : D.X} {s : SecFMod D (FractionRing R) 1 α} {t : SecFMod D (FractionRing R) 1 (α + 1 • mu)}
    (h : FERel D mu α s t) (c : FractionRing R) : FERel D mu α (c • s) (c • t) := by
  refine feRel_iff.2 fun y J hJ => ?_
  have e : (DegPre.trF D (FractionRing R) mu).left ≫ strF D (FractionRing R) = strF D (FractionRing R) := by
    rw [← Over.comp_left, DegPre.trF, lift_fst]
  rw [sval_smul' hJ, sval_smul' hJ, feRel_iff.1 h y J hJ, Category.assoc, e, _root_.mul_assoc]

theorem exists_psi_val [IsLocalRing R] (D : DegPre R) (χ : D.X) {a₀ : R} (h : PsiCoord D χ a₀) :
    ∃ (e : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), e.IsGen ∧ ∃ b : Rˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        (val (D.psi χ) r z J).val = constVal (r ≫ jK R) z (a₀ * b) * (val e (r ≫ jK R) z J).val := by
  have hL := D.P.isLB
  obtain ⟨e, he⟩ := exists_gen_of_local (V := R) D.P.L hL (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  obtain ⟨j, hj, le', hψ⟩ := h
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j :=
    fun y hy => Set.mem_iInter.2 fun _ => hj hy
  have hx : D.xK χ = jK R ≫ (D.c χ).left := by
    simp [DegPre.xK, ptK]
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  let φ := RingEquiv.ofBijective _ (GlobalTheory.PsiCoordLocal.toOpen_top_bijective (R := R))
  let b : Rˣ := Units.map φ.symm.toMonoidHom (res le (e.s j))⁻¹
  have hb : DegPre.toOpen (R := R) ⊤ b = (res le (e.s j))⁻¹.val := φ.apply_symm_apply _
  refine ⟨e, he, b, fun Z r z J hJ => ?_⟩
  have m₁ : r z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := le' trivial
  have m₂ : (r ≫ jK R) z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j := le trivial
  have e₁ : val (D.psi χ) r z J = _ := gen_trans (D.psi_gen χ) r z (hJ.mem _ r) m₁
  have e₂ : val e (r ≫ jK R) z J = _ := gen_trans he (r ≫ jK R) z (hJ.mem _ _) m₂
  have e₃ : trF (L := D.P.L) (K := PUnit) (fun _ => D.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ D.xK χ)) j =
      trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j := by
    have hq : r ≫ D.xK χ = (r ≫ jK R) ≫ (D.c χ).left :=
      (congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm
    simp only [trF]
    rw [hq]
  have e₄ : (gm r z (LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j) ((D.psi χ).s j)).val = constVal (r ≫ jK R) z a₀ := by
    refine (gs_unit r z _ m₁ _).symm.trans ((gs_res r z le' trivial _).symm.trans ?_)
    refine (congrArg (gs r z _) hψ.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)
    rw [hto]; rfl
  have e₅ : constVal (r ≫ jK R) z b *
      (gm (r ≫ jK R) z (LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j) (e.s j)).val = 1 := by
    rw [constVal, ← hto, hb, gs_unit _ z ⊤ trivial, map_inv]
    exact (congrArg₂ (fun q c => q⁻¹.val * c) (gm_res (r ≫ jK R) z le trivial (e.s j)) rfl).trans (Units.inv_mul _)
  have e₆ : constVal (r ≫ jK R) z (a₀ * b) = constVal (r ≫ jK R) z a₀ * constVal (r ≫ jK R) z b := by
    rw [constVal, map_mul, gs_mul _ z ⊤ trivial]; rfl
  rw [e₁, e₂, e₆, Units.val_mul, Units.val_mul]
  erw [e₃, e₄]
  linear_combination (-(constVal (r ≫ jK R) z a₀ * (trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j).val)) * e₅

theorem trB_comp (a b : D.X) (h : a + b = 0) : (trB D a).left ≫ (trB D b).left = 𝟙 _ := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, comp_cP, trB, _root_.mul_assoc, ← cPoint_add, h, cPoint_zero,
    _root_.mul_one, Over.id_left]

theorem exists_equiv (mu α : D.X) (eB : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (α + 1 • mu))
        (fun i => (trB D mu).left ≫ D.famφB α i)) (DegPre.deltaε 1))) (heB : eB.IsGen) :
    ∃ Θ : SecBMod D 1 α ≃ₗ[R] SecBMod D 1 (α + 1 • mu), ∀ s (Z : Scheme.{0}) (ρ : Z ⟶ D.P.A.left) (z : Z) (J),
      Good D.P.L z J → sval (Θ s) ρ z J = sval s (ρ ≫ (trB D mu).left) z J * (val eB ρ z J).val := by
  have hL := D.P.isLB
  have h₁ : ∀ s : SecBMod D 1 α, ∃ t : SecBMod D 1 (α + 1 • mu), ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D.P.A.left) (z : Z) (J),
      Good D.P.L z J → sval t ρ z J = sval s (ρ ≫ (trB D mu).left) z J * (val eB ρ z J).val := fun s => by
    obtain ⟨t, ht⟩ := exists_sec hL (φ' := D.famφB (α + 1 • mu)) (ε' := DegPre.famε 1) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg,
        Finset.prod_inv_distrib]
      exact (mul_comm _ _).trans (inv_mul_cancel_right _ _)) (pullMulSec s (trB D mu).left eB heB)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullMulSec _ _ _ _ ρ z hJ)⟩
  have i₁ := trB_comp (D := D) (-mu) mu (neg_add_cancel mu)
  have i₂ := trB_comp (D := D) mu (-mu) (add_neg_cancel mu)
  have h₂ : ∀ t : SecBMod D 1 (α + 1 • mu), ∃ s : SecBMod D 1 α, ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D.P.A.left) (z : Z) (J),
      Good D.P.L z J → sval s ρ z J = sval t (ρ ≫ (trB D (-mu)).left) z J * (val eB (ρ ≫ (trB D (-mu)).left) z J)⁻¹.val :=
    fun t => by
    obtain ⟨s, hs⟩ := exists_sec hL (φ' := D.famφB α) (ε' := DegPre.famε 1) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, neg_neg,
        Finset.prod_inv_distrib, reassoc_of% i₁]
      rw [mul_inv, inv_inv, mul_inv_cancel_left])
      (pullMulSec t (trB D (-mu)).left (LB.pullGen D.P.L _ _ (LB.invGen D.P.L _ _ eB) (trB D (-mu)).left)
        (pullGen_isGen _ _ _ _ (invGen_isGen _ _ _ _ heB) _))
    refine ⟨s, fun Z ρ z J hJ => (hs Z ρ z J hJ).trans ((sval_pullMulSec _ _ _ _ ρ z hJ).trans ?_)⟩
    rw [val_pull hJ, val_inv]
  choose f hf using h₁
  choose g hg using h₂
  have w : (trB D mu).left ≫ D.P.A.hom = D.P.A.hom := Over.w _
  refine ⟨⟨⟨⟨f, fun s t => sec_ext' hL fun y J hJ => ?_⟩, fun c s => sec_ext' hL fun y J hJ => ?_⟩, g,
    fun s => sec_ext' hL fun y J hJ => ?_, fun t => sec_ext' hL fun y J hJ => ?_⟩, hf⟩
  · rw [sval_add' hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, sval_add' hJ, add_mul]
  · show sval (f (c • s)) _ _ _ = sval (c • f s : SecBMod D 1 _) _ _ _
    rw [sval_smul' hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, sval_smul' hJ, Category.assoc, w, _root_.mul_assoc]
  · show sval (g (f s)) _ _ _ = _
    rw [hg _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, Category.assoc, i₁, Category.comp_id, Units.mul_inv_cancel_right]
  · show sval (f (g t)) _ _ _ = _
    rw [hf _ _ _ _ _ hJ, hg _ _ _ _ _ hJ, Category.assoc, i₂, Category.comp_id, Units.inv_mul_cancel_right]

theorem constVal_mul {S : Type} [CommRing S] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of S)) (z : Z) (a b : S) :
    constVal q z (a * b) = constVal q z a * constVal q z b := by
  rw [constVal, map_mul, gs_mul _ z ⊤ trivial]; rfl

theorem unit_calc {S : Type} [CommRing S] {P₁ P₂ E₁ E₂ : Sˣ} {κ c₁ c₂ : S} (p₁ : P₁.val = c₁ * E₁.val)
    (p₂ : P₂.val = c₂ * E₂.val) (k : κ * c₂ = c₁) : κ * (E₁ * E₂⁻¹).val = (P₁ * P₂⁻¹).val := by
  rw [Units.val_mul, Units.val_mul, Units.eq_mul_inv_iff_mul_eq, p₁, p₂, ← k]
  linear_combination (κ * c₂ * E₁.val) * Units.inv_mul E₂

theorem exists_transl [IsLocalRing R] (Dg : DegData R (maximalIdeal R)) (mu α : Dg.toPre.X) :
    ∃ (Θ : SecBMod Dg.toPre 1 α ≃ₗ[R] SecBMod Dg.toPre 1 (α + 1 • mu)) (κ : (FractionRing R)ˣ),
      (κ : Cls R) = psiCls Dg (mu + α) * (psiCls Dg α)⁻¹ ∧
      ∀ s, FERel Dg.toPre mu α (resF Dg.toPre (FractionRing R) 1 α s)
        ((κ : FractionRing R) • resF Dg.toPre (FractionRing R) 1 _ (Θ s)) := by
  let D := Dg.toPre
  obtain ⟨e₁, he₁, b₁, h₁⟩ := exists_psi_val D (mu + α) (coord_spec Dg _)
  obtain ⟨e₂, he₂, b₂, h₂⟩ := exists_psi_val D α (coord_spec Dg _)
  have c₁ : ∀ χ, D.P.A.hom ≫ (D.c χ).left = (SectionScalarValuation.cQ D D.P.A χ).left := fun χ => by simp [SectionScalarValuation.cQ]
  obtain ⟨eB, heB, veB⟩ := SectionScalarValuation.exists_eB D 1 α mu (LB.mulGen D.P.L _ _ _ _ e₁ (LB.invGen D.P.L _ _ e₂))
    (mulGen_isGen _ _ _ _ _ _ _ he₁ (invGen_isGen _ _ _ _ he₂)) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c₁]
      rw [add_comm mu α, SectionScalarValuation.cQ_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, neg_neg]
      module)
  obtain ⟨Θ, hΘ⟩ := exists_equiv mu α eB heB
  have n₁ : coord Dg (mu + α) * b₁ ≠ 0 := mul_ne_zero (coord_ne Dg _) b₁.ne_zero
  have n₂ : coord Dg α * b₂ ≠ 0 := mul_ne_zero (coord_ne Dg _) b₂.ne_zero
  refine ⟨Θ, toK _ n₁ * (toK _ n₂)⁻¹, ?_, fun s => feRel_iff.2 fun y J hJ => ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← toK_cls_eq (coord_ne Dg _) n₁ ⟨b₁, rfl⟩,
      ← toK_cls_eq (coord_ne Dg _) n₂ ⟨b₂, rfl⟩]
    rfl
  · rw [sval_smul' hJ, sval_resF _ _ _ _ hJ, sval_resF _ _ _ _ hJ, hΘ _ _ _ _ _ hJ]
    simp only [Category.id_comp]
    rw [← Over.comp_left, ← Over.comp_left, trF_prB, mul_left_comm]
    congr 1
    have w₁ : ((fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R =
        (DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom :=
      (Category.assoc _ _ _).trans
        ((Over.w (fst (TF (R := R) (FractionRing R)) D.P.A)).trans (Over.w (DegPre.prB D (FractionRing R))).symm)
    have w₂ : (DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom = strF D (FractionRing R) ≫
      Spec.map (CommRingCat.ofHom (toF (R := R) (FractionRing R))) := (isPullback_prB D (FractionRing R)).w
    have v₁ := veB _ (DegPre.prB D (FractionRing R)) y J hJ
    have p₁ := h₁ _ ((fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R)) y J hJ
    have p₂ := h₂ _ ((fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R)) y J hJ
    rw [w₁] at p₁ p₂
    have fm : val (DegPre.famMult D (FractionRing R) 1 mu α) (fst (TF (R := R) (FractionRing R)) D.P.A).left y J =
        val (D.psi (mu + α)) ((fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R)) y J *
        (val (D.psi α) ((fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R)) y J)⁻¹ := by
      rw [val_famMult _ hJ, UUA.val_powGen', UUA.val_powGen']
      refine (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))) rfl).trans ?_
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, pow_one]
      abel
    have k : constVal (strF D (FractionRing R)) y ((toK _ n₁ * (toK _ n₂)⁻¹ : (FractionRing R)ˣ) : FractionRing R) *
        constVal ((DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom) y (coord Dg α * b₂) =
        constVal ((DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom) y (coord Dg (mu + α) * b₁) := by
      rw [w₂, constVal_specMap, constVal_specMap, ← constVal_mul]
      congr 1
      exact congrArg Units.val (inv_mul_cancel_right (toK _ n₁) (toK _ n₂))
    rw [val_mul hJ, val_inv] at v₁
    rw [fm, uVal_id, comp_cP]
    erw [v₁]
    have q : constVal (strF D (FractionRing R)) y ((toK _ n₁ * (toK _ n₂)⁻¹ : (FractionRing R)ˣ) : FractionRing R) *
        (val e₁ ((DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom) y J *
          (val e₂ ((DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom) y J)⁻¹).val =
        (val (D.psi (mu + α)) ((fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R)) y J *
        (val (D.psi α) ((fst (TF (R := R) (FractionRing R)) D.P.A).left ≫ jFK (R := R) (FractionRing R)) y J)⁻¹).val := by
      exact unit_calc p₁ p₂ k
    rw [Units.val_mul _ (_ * _), Units.val_mul _ (_ * _), ← q, mul_left_comm]
    rfl

end Transl

section Gen

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Dg : DegData R (maximalIdeal R))

theorem exists_secGen (χ : Dg.toPre.X) : ∃ e : SecBMod Dg.toPre 1 χ, ∀ s, ∃! a : R, s = a • e := by
  suffices H : ∃ e : SecBMod Dg.toPre 1 (0 + 1 • χ), ∀ s, ∃! a : R, s = a • e by rwa [zero_add, one_smul] at H
  obtain ⟨b, hb⟩ := GlobalTheory.IndivisibleSection.exists_generator Dg.toPre GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  obtain ⟨Θ, -⟩ := exists_transl Dg χ 0
  let b' : SecBMod Dg.toPre 1 0 := b
  have hb' : ∀ (a : R) (s : SecBMod Dg.toPre 1 0), SecIsMul Dg.toPre.P.A.hom a s b ↔ s = a • b' := fun a s =>
    ⟨fun h => SecOver.ext _ _ h, fun h _ => by rw [h]; rfl⟩
  refine ⟨Θ b', fun s => ?_⟩
  refine (existsUnique_congr fun a => ?_).1 (hb (Θ.symm s))
  rw [hb', LinearEquiv.symm_apply_eq, map_smul]

def secGen (χ : Dg.toPre.X) : SecBMod Dg.toPre 1 χ := (exists_secGen Dg χ).choose

theorem secGen_spec (χ : Dg.toPre.X) (s : SecBMod Dg.toPre 1 χ) : ∃! a : R, s = a • secGen Dg χ :=
  (exists_secGen Dg χ).choose_spec s

def secGenK (χ : Dg.toPre.X) : SecFMod Dg.toPre (FractionRing R) 1 χ := resF Dg.toPre (FractionRing R) 1 χ (secGen Dg χ)

theorem secGenK_ne (χ : Dg.toPre.X) : secGenK Dg χ ≠ 0 := fun h => by
  have h0 : secGen Dg χ = 0 := resF_injective Dg.toPre (FractionRing R) 1 χ (h.trans (map_zero _).symm)
  exact one_ne_zero ((secGen_spec Dg χ 0).unique (y₁ := (1 : R)) (y₂ := 0) (by rw [h0, smul_zero]) (by rw [zero_smul]))

theorem resF_smul_secGen (χ : Dg.toPre.X) (a : R) :
    resF Dg.toPre (FractionRing R) 1 χ (a • secGen Dg χ) = algebraMap R (FractionRing R) a • secGenK Dg χ :=
  map_smulₛₗ _ _ _

variable {Dg}

def IsTransUnit {O : Type} [Ring O] [Module O Dg.toPre.X] (t : Dg.toPre.X → Dg.toPre.X → (FractionRing R)ˣ) (w : O)
    (mu α : Dg.toPre.X) (u : Rˣ) : Prop :=
  FERel Dg.toPre mu α (secGenK Dg α)
    ((algebraMap R (FractionRing R) u * (t mu (w • mu) : FractionRing R) * (t mu α : FractionRing R)) • secGenK Dg (α + 1 • mu))

theorem existsUnique_transUnit [IsIntegrallyClosed R] {O : Type} [Ring O] [StarRing O] [Module O Dg.toPre.X]
    (ρ : Dg.toPre.OAct O) {t} (ht : IsReading Dg O t) {w : O} (hw : w + star w = 1) (mu α : Dg.toPre.X) :
    ∃! u, IsTransUnit t w mu α u := by
  refine existsUnique_of_exists_of_unique ?_ fun u u' h h' => ?_
  · obtain ⟨Θ, κ, hκ, hΘ⟩ := exists_transl Dg mu α
    obtain ⟨v, hv, -⟩ := secGen_spec Dg _ (Θ (secGen Dg α))
    obtain ⟨c, hc, -⟩ := secGen_spec Dg _ (Θ.symm (secGen Dg (α + 1 • mu)))
    rw [LinearEquiv.symm_apply_eq, map_smul, hv, smul_smul] at hc
    have hcv : c * v = 1 := (secGen_spec Dg _ _).unique hc (one_smul _ _).symm
    have e : ((t mu (w • mu) * t mu α : (FractionRing R)ˣ) : Cls R) = κ := by
      rw [QuotientGroup.mk_mul, ht.cls, ht.cls, tauCls_half Dg ρ hw, hκ, tauCls]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    obtain ⟨u₀, hu₀⟩ := cls_eq_iff.1 e
    refine ⟨u₀ * ⟨v, c, (mul_comm _ _).trans hcv, hcv⟩, ?_⟩
    have H := hΘ (secGen Dg α)
    rw [hv, resF_smul_secGen, smul_smul, ← hu₀] at H
    unfold IsTransUnit
    refine (congrArg (fun x : FractionRing R => FERel Dg.toPre mu α (secGenK Dg α) (x • secGenK Dg (α + 1 • mu))) ?_).mp H
    simp only [Units.val_mul, map_mul]
    ring
  · have e := smul_left_injective _ (secGenK_ne Dg _) (FERel.unique h h')
    have e' := mul_right_cancel₀ (Units.ne_zero _) (mul_right_cancel₀ (Units.ne_zero _) e)
    exact Units.ext (IsFractionRing.injective R _ e')

end Gen

section Sec

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif I D A G)

abbrev SecG : Type :=
  SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)))

def SecGK : Type :=
  SecOver (pullback.snd G.hom (jK R))
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)))

instance : AddCommGroup (SecGK U) := inferInstanceAs (AddCommGroup (SecOver _ _))
instance : Module (FractionRing R) (SecGK U) := inferInstanceAs (Module (FractionRing R) (SecOver _ _))
instance : Module R (SecGK U) := Module.compHom _ (algebraMap R (FractionRing R))
instance : IsScalarTower R (FractionRing R) (SecGK U) :=
  ⟨fun a b s => by rw [Algebra.smul_def, mul_smul]; rfl⟩

def resG : SecG U →ₗ[R] SecGK U where
  toFun s := pullOver U.LG.L _ (f := algebraMap R (FractionRing R)) (pullback.condition (f := G.hom) (g := jK R))
    (fun _ => (Category.comp_id _).symm) s
  map_add' s t := map_add _ s t
  map_smul' c s := map_smulₛₗ (pullOver U.LG.L _ (f := algebraMap R (FractionRing R))
    (pullback.condition (f := G.hom) (g := jK R)) (fun _ => (Category.comp_id _).symm)) c s

def secReg : Submodule R (SecGK U) := LinearMap.range (resG U)

def expandFun (s : SecGK U) : Fam D.toPre (FractionRing R) 1 := ((U.expand 1 le_rfl).1 s).choose

theorem expands_iff (s : SecGK U) (F : Fam D.toPre (FractionRing R) 1) : U.Expands 1 s F ↔ F = expandFun U s :=
  ⟨((U.expand 1 le_rfl).1 s).choose_spec.2 F, fun h => h ▸ ((U.expand 1 le_rfl).1 s).choose_spec.1⟩

def expand (hR : AdmBase R I) [GeometricallyConnected G.hom] : SecGK U →ₗ[FractionRing R] Fam D.toPre (FractionRing R) 1 where
  toFun := expandFun U
  map_add' s t := by
    have := GlobalTheory.expands_linear R I hR D A G U.toUnifPre 1 2 ![s, t] ![expandFun U s, expandFun U t] ![1, 1] (s + t : SecGK U)
      (fun i => by fin_cases i <;> exact (expands_iff U _ _).2 rfl) (fun j => by
        have e : s + t = (1 : FractionRing R) • s + (1 : FractionRing R) • t := by rw [one_smul, one_smul]
        rw [e, Fin.sum_univ_two]; rfl)
    rw [← (expands_iff U _ _).1 this, Fin.sum_univ_two]
    simp
  map_smul' c s := by
    have := GlobalTheory.expands_linear R I hR D A G U.toUnifPre 1 1 ![s] ![expandFun U s] ![c] (c • s : SecGK U)
      (fun i => by fin_cases i; exact (expands_iff U _ _).2 rfl) (fun j => by rw [Fin.sum_univ_one]; rfl)
    rw [← (expands_iff U _ _).1 this, Fin.sum_univ_one]
    simp

theorem expand_bijective (hR : AdmBase R I) [GeometricallyConnected G.hom] : Function.Bijective (expand U hR) :=
  (Function.bijective_iff_existsUnique _).2 fun F =>
    (existsUnique_congr fun s => (expands_iff U s F).trans eq_comm).1 ((U.expand 1 le_rfl).2 F)

end Sec

section Coef

open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif (maximalIdeal R) D A G) (hR : AdmBase R (maximalIdeal R)) [GeometricallyConnected G.hom]

theorem existsUnique_coef (s : SecGK U) (χ : D.toPre.X) :
    ∃! x : FractionRing R, famComp D.toPre (FractionRing R) 1 χ (expand U hR s) = x • secGenK D χ := by
  refine existsUnique_of_exists_of_unique ?_ fun x y hx hy => smul_left_injective _ (secGenK_ne D χ) (hx.symm.trans hy)
  obtain ⟨r, hr, σ, f, -, hf, -⟩ := (expands_iff U s _).2 rfl
  obtain ⟨a, ha, -⟩ := secGen_spec D χ (f χ)
  have h := (secScal_iff_resF D.toPre (FractionRing R) _ (f χ) r).1 (hf χ)
  rw [ha, resF_smul_secGen] at h
  have h0 : algebraMap R (FractionRing R) r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hr
  refine ⟨(algebraMap R (FractionRing R) r)⁻¹ * algebraMap R _ a, ?_⟩
  rw [mul_smul, h]
  exact (inv_smul_smul₀ h0 _).symm

def coef : SecGK U →ₗ[FractionRing R] (D.toPre.X → FractionRing R) where
  toFun s χ := (existsUnique_coef U hR s χ).choose
  map_add' s t := funext fun χ => ((existsUnique_coef U hR (s + t) χ).choose_spec.2 _ (by
    rw [map_add, map_add, (existsUnique_coef U hR s χ).choose_spec.1, (existsUnique_coef U hR t χ).choose_spec.1,
      Pi.add_apply]
    exact (add_smul _ _ _).symm)).symm
  map_smul' c s := funext fun χ => ((existsUnique_coef U hR (c • s) χ).choose_spec.2 _ (by
    rw [map_smul, map_smul, (existsUnique_coef U hR s χ).choose_spec.1, smul_smul]; rfl)).symm

theorem coef_spec (s : SecGK U) (χ : D.toPre.X) :
    famComp D.toPre (FractionRing R) 1 χ (expand U hR s) = coef U hR s χ • secGenK D χ :=
  (existsUnique_coef U hR s χ).choose_spec.1

end Coef

end GlobalTheory.LocM.Bdy
