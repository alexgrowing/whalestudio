import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KummerConj

open GlobalTheory.TorusExt GlobalTheory.UnramTorsion GlobalTheory.BXOf

attribute [local instance] gtGroup

theorem valuation_val_eq {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (O : ValuationSubring F) (φ : R →+* O)
    (hφ : ∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r))
    {X : Scheme.{0}} {L : LB X} (J₀ : X → L.ι) (h₀ : ∀ x, x ∈ L.U (J₀ x)) {J : (Sp F ⟶ X) → L.ι}
    (hJ : Good L (closedPoint F) J) (eJ : ∀ ψ : Sp O ⟶ X, J (spMap O.subtype ≫ ψ) = J₀ (ψ (closedPoint O)))
    {K : Type} [Fintype K] {φs : K → ((TK R).left ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φs ε))
    (ht : t.IsGen) (p : K → (Spec (CommRingCat.of R) ⟶ X)) (hp : ∀ k, φs k = jK R ≫ p k) (j : K → L.ι)
    (hj : ∀ k, ⊤ ≤ p k ⁻¹ᵁ L.U (j k)) (h : ⊤ ≤ (LB.LinComb L φs ε).U j) :
    O.valuation (sig F (val t (jFK (R := R) F) (closedPoint F) J) : F) =
      O.valuation (algebraMap (FractionRing R) F (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal t j h)) := by
  have hs : spMap O.subtype ≫ spMap φ = jFK (R := R) F ≫ jK R := by
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ
  have hr : ∀ k, jFK (R := R) F ≫ φs k = spMap O.subtype ≫ (spMap φ ≫ p k) := fun k => by
    rw [hp k, ← Category.assoc, ← Category.assoc, hs]
  obtain ⟨w, hw⟩ : ∃ w : ((Sp F).presheaf.stalk (closedPoint F))ˣ →* O.ValueGroupˣ,
      ∀ u, (w u : O.ValueGroup) = O.valuation (sig F u : F) :=
    ⟨(Units.map O.valuation.toMonoidWithZeroHom.toMonoidHom).comp (sig F), fun _ => rfl⟩
  have hunit : ∀ (ψ : Sp O ⟶ X) (U : X.Opens) (hU : ψ (closedPoint O) ∈ U) (a : Γ(X, U)ˣ),
      w (gm (spMap O.subtype ≫ ψ) (closedPoint F) U a) = 1 := fun ψ U hU a => by
    refine Units.ext ((hw _).trans ?_)
    rw [← sig_nat O.subtype ψ hU a]
    exact O.valuation_unit _
  have hz : jFK (R := R) F (closedPoint F) ∈ LB.wchart L φs j := h trivial
  have g := gen_trans ht (jFK (R := R) F) (closedPoint F) (hJ.mem φs (jFK (R := R) F)) hz
  have htr : w (trF φs ε (jFK (R := R) F) (closedPoint F) (fun k => J (jFK (R := R) F ≫ φs k)) j) = 1 := by
    show w (∏ k, gm (jFK (R := R) F ≫ φs k) (closedPoint F) (L.U (J (jFK (R := R) F ≫ φs k)) ⊓ L.U (j k))
      (L.g (J (jFK (R := R) F ≫ φs k)) (j k)) ^ ε k) = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [map_zpow]
    refine (congrArg (· ^ ε k) ?_).trans (one_zpow _)
    rw [hr k]
    apply hunit
    exact ⟨by rw [eJ]; exact h₀ _, hj k (show spMap φ (closedPoint O) ∈ ⊤ from trivial)⟩
  have hgv : (gm (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (closedPoint (FractionRing R)) ((LB.LinComb L φs ε).U j)
      (t.s j)).val = ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ (closedPoint (FractionRing R))
        trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
          (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal t j h).val) := by
    refine (gm_val (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (closedPoint (FractionRing R)) _ (h trivial) (t.s j)).trans ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal, Units.coe_map, MonoidHom.coe_coe, res, RingHom.toMonoidHom_eq_coe]
    rw [Iso.hom_inv_id_apply]
    exact (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of (FractionRing R))).presheaf (homOfLE h)
      (closedPoint (FractionRing R)) trivial _).symm
  have hsg : sig (FractionRing R) (gm (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (closedPoint (FractionRing R))
      (LB.wchart L φs j) (t.s j)) = GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal t j h := by
    refine Units.ext ((congrArg (stalkClosedPointIso (CommRingCat.of (FractionRing R))).hom.hom hgv).trans ?_)
    rw [← CommRingCat.comp_apply, germ_stalkClosedPointIso_hom, Iso.inv_hom_id_apply]
  have n := sig_nat (algebraMap (FractionRing R) F) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (h trivial) (t.s j)
  rw [Category.comp_id] at n
  have n2 := (congrArg (Units.map (algebraMap (FractionRing R) F).toMonoidHom) hsg).symm.trans n
  have e : w (val t (jFK (R := R) F) (closedPoint F) J) =
      w (gm (jFK (R := R) F) (closedPoint F) ((LB.LinComb L φs ε).U j) (t.s j)) := by
    refine (congrArg w g).trans ?_
    rw [map_mul, htr, _root_.one_mul]
    rfl
  rw [← hw, e, hw]
  exact congrArg (fun u : Fˣ => O.valuation (u : F)) n2.symm

theorem conj_eq_add_tor : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ) (σ : F →ₐ[FractionRing R] F) (p p' : QkPt D F k), QkExt σ.toRingHom p p' →
    spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left →
    ∃ (τ : Multiplicative D.X →* Fˣ) (q : QkPt D F k), τ ^ k = 1 ∧ q.y = 0 ∧ GlobalTheory.UT.IsTor τ q.g ∧ QkAdd p q p' ∧
      ∀ (χ : D.X) (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D p.y χ x →
        ∃ s : F, s ≠ 0 ∧ O.valuation s ^ k = O.valuation (algebraMap (FractionRing R) F x) ∧
          σ s = (τ (Multiplicative.ofAdd χ) : F) * s := by
  intro R _ _ D hB F _ _ O φ hφ k σ p p' hext hfix
  have hσ' : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F :=
    RingHom.ext fun a => σ.commutes a
  obtain rfl : p' = qkExt hB σ.toRingHom hσ' p := (qkExt_iff hB _ hσ' _ _).1 hext
  have hb : extMap σ.toRingHom hσ' ≫ p.g.b = p.g.b := Over.OverMorphism.ext hfix
  set d : GtPtF D F := gtExt D σ.toRingHom hσ' p.g - p.g with hd
  have hdb : d.b = 1 := by
    rw [hd, sub_eq_add_neg, add_b, neg_b, gtExt_b, hb, mul_inv_cancel]
  have hgd : gtExt D σ.toRingHom hσ' p.g = p.g + d := by rw [hd, add_sub_cancel]
  obtain ⟨τ, hτ⟩ := exists_torusPt_eq hdb
  have hkd : k • d = 0 := by
    rw [hd, nsmul_sub, ← map_nsmul, qk_nsmul hB, gtExt_iota, sub_self]
  have hτk : τ ^ k = 1 := by
    have e : torusPt D F (Additive.ofMul (τ ^ k)) = torusPt D F (Additive.ofMul 1) := by
      rw [ofMul_pow, map_nsmul, ← hτ, hkd, ofMul_one, map_zero]
    exact Additive.ofMul.injective (torusPt_injective e)
  let q : QkPt D F k := qkMk hB 0 d (by rw [hkd, map_zero])
  refine ⟨τ, q, hτk, rfl, (GlobalTheory.UT.isTor_iff _ _).2 ((isTorusPtF_iff_eq d τ).2 hτ), ?_, fun χ x hx => ?_⟩
  · refine (qkAdd_iff hB _ _ _).2 ?_
    have e : qkAdd hB p q = qkExt hB σ.toRingHom hσ' p := qk_ext (add_zero _) hgd.symm
    rw [e]
    exact qk_equiv_refl hB _

  have := D.P.isAb.proper
  have : D.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.P.A.hom]; infer_instance⟩
  choose J₀ h₀ using fun x : D.P.A.left => exists_chart D.P.isLB x
  obtain ⟨J, hJ, eJ⟩ := exists_good_ext D.P.isLB O.subtype Subtype.val_injective J₀ h₀
  let z : (TF (R := R) F).left := closedPoint F
  have hJ' : Good D.P.L z J := hJ
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ) := Over.homMk (spMap O.subtype) (by
    show spMap O.subtype ≫ spMap φ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ)
  obtain ⟨w, hw⟩ : ∃ w : ((TF (R := R) F).left.presheaf.stalk z)ˣ →* O.ValueGroupˣ,
      ∀ u, (w u : O.ValueGroup) = O.valuation (sig F u : F) :=
    ⟨(Units.map O.valuation.toMonoidWithZeroHom.toMonoidHom).comp (sig F), fun _ => rfl⟩
  have hint : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (ψ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L ψ ε)) (r : (Over.mk (spMap φ)).left ⟶ Y), w (val t (ρ.left ≫ r) z J) = 1 := by
    intro Y K _ ψ ε t r
    obtain ⟨u, hu⟩ := val_integral O.subtype h₀ eJ t r
    exact Units.ext ((hw _).trans ((congrArg O.valuation hu).trans (O.valuation_unit u)))
  obtain ⟨b, hb'⟩ := exists_extend O φ ρ rfl p.g.b
  have e₁ := w_nsmul ρ hJ' w hint p.g b hb' χ k
  rw [qk_nsmul hB, iota_val hB _ _ hJ'] at e₁
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ'
  refine ⟨(sig F (charVal p.g χ z J) : F), Units.ne_zero _, ?_, ?_⟩
  · have e₂ := congrArg Units.val e₁
    rw [Units.val_pow_eq_pow_val, hw, hw] at e₂
    rw [← e₂]
    obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
    have er : (𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F = jFK (R := R) F := by simp
    show O.valuation (sig F (val (D.tau p.y χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) z J) : F) = _
    rw [er]
    refine valuation_val_eq O φ hφ J₀ h₀ hJ eJ (D.tau p.y χ) (tau_isGen D _ _)
      (Sum.elim (Sum.elim (Sum.elim (fun _ => (D.c (p.y + χ)).left) (fun _ => (D.c p.y).left))
        (fun _ => (D.c χ).left)) (fun _ => (η[D.P.A] : _ ⟶ _).left)) ?_ j ?_ h
    · rintro (((_ | _) | _) | _)
      · rfl
      · rfl
      · rfl
      · show (toUnit (TK R)).left ≫ eSec D.P.A = jK R ≫ (η[D.P.A] : _ ⟶ _).left
        have e : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
        rw [e]
        rfl
    · rintro (((_ | _) | _) | _)
      exacts [i1, i2, i3, i4]
  · have key : σ (sig F (charVal p.g χ z J) : F) =
        (sig F (charVal (gtExt D σ.toRingHom hσ' p.g) χ z J) : F) := by
      have e := gtExt_val σ.toRingHom hσ' p.g χ hJ'
      have hφ' : ∀ i, (extMap σ.toRingHom hσ').left ≫ DegPre.gtφ D F p.g.b χ i =
          𝟙 _ ≫ DegPre.gtφ D F p.g.b χ i := by
        intro i
        rw [Category.id_comp]
        fin_cases i
        · show (extMap σ.toRingHom hσ' ≫ (cP D _ χ * p.g.b)).left = (cP D _ χ * p.g.b).left
          rw [MonObj.comp_mul, comp_cP, hb]
        · show (extMap σ.toRingHom hσ' ≫ cP D _ χ).left = (cP D _ χ).left
          rw [comp_cP]
        · show (extMap σ.toRingHom hσ' ≫ p.g.b).left = p.g.b.left
          rw [hb]
        · show (extMap σ.toRingHom hσ' ≫ (1 : TF (R := R) F ⟶ D.P.A)).left = (1 : TF (R := R) F ⟶ D.P.A).left
          rw [MonObj.comp_one]
      replace e := e.trans (val_of (p.g.s χ) _ _ J _ (fun i => congrArg J (hφ' i)))
      have n := sig_nat σ.toRingHom (𝟙 (Spec (CommRingCat.of F))) (hJ'.mem (DegPre.gtφ D F p.g.b χ) (𝟙 _))
        ((p.g.s χ).s fun i => J (𝟙 _ ≫ DegPre.gtφ D F p.g.b χ i))
      rw [Category.comp_id] at n
      exact (congrArg Units.val n).trans (congrArg (fun u => (sig F u : F)) e.symm)
    have hs : sig F (charVal d χ z J) = τ (Multiplicative.ofAdd χ) := by
      rw [hτ, torusPt_val τ χ hJ']
      refine Units.ext ?_
      show (stalkClosedPointIso (CommRingCat.of F)).hom.hom (((Sp F).presheaf.germ ⊤ (closedPoint F) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (τ (Multiplicative.ofAdd χ) : F))) = _
      rw [← CommRingCat.comp_apply, germ_stalkClosedPointIso_hom, Iso.inv_hom_id_apply]
    have e := add_val p.g d χ hJ'
    rw [hdb, C.face₃, _root_.mul_one] at e
    rw [key, hgd, e, map_mul, Units.val_mul, hs, mul_comm]

end GlobalTheory.KummerConj
