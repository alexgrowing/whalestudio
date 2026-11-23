import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.GaugeHom
open GlobalTheory.TorusExt GlobalTheory.ArcExt

section Val
variable {F : Type} [Field F] {X : Scheme.{0}} {L : LB X}
  {J J' : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (hJ' : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J' ψ))
include hJ hJ'

theorem exists_trans : ∃ T : (Sp F ⟶ X) → Fˣ, ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y), sF s r J = (∏ k, T (r ≫ φ k) ^ ε k : Fˣ) * sF s r J' := by
  let y : Sp F := IsLocalRing.closedPoint F
  have hm : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ (L.U (J ψ) ⊓ L.U (J' ψ)) := fun ψ z hz => ⟨hJ ψ hz, hJ' ψ hz⟩
  have hv : ∀ ψ : Sp F ⟶ X, (gm ψ y (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ))).val =
      stalkConst y (valF ψ (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)).val) := fun ψ =>
    (gs_unit ψ y _ (hm ψ trivial) _).symm.trans (gs_eq_stalkConst ψ y (hm ψ) _)
  have hne : ∀ ψ : Sp F ⟶ X, valF ψ (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)).val ≠ 0 := fun ψ h =>
    (((Units.isUnit _).map _).map _).ne_zero ((dif_pos (hm ψ)).symm.trans h)
  refine ⟨fun ψ => Units.mk0 _ (hne ψ), fun Y K _ φ ε s r => (stalkConst y).injective ?_⟩
  have e : ∀ ψ : Sp F ⟶ X, gm ψ y (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)) =
      Units.map (stalkConst y).toMonoidHom (Units.mk0 _ (hne ψ)) := fun ψ => Units.ext (hv ψ)
  have a := sec_trans s r y (top_le_chart hJ φ r trivial) (top_le_chart hJ' φ r trivial)
  rw [map_mul]
  refine (gs_eq_stalkConst r y (top_le_chart hJ φ r) _).symm.trans
    (a.trans (congrArg₂ (· * ·) ?_ (gs_eq_stalkConst r y (top_le_chart hJ' φ r) _)))
  show _ = (Units.map (stalkConst y).toMonoidHom _).val
  rw [map_prod, trF]
  refine congrArg Units.val (Finset.prod_congr rfl fun k _ => ?_)
  rw [map_zpow, e]

end Val

theorem exists_trans_ext {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {J : (Sp F ⟶ X) → L.ι} {J' : (Sp F' ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
    (hJ' : ∀ ψ : Sp F' ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J' ψ)) : ∃ T : (Sp F ⟶ X) → F'ˣ,
    (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y),
      sF s (spMap f ≫ r) J' = (∏ k, T (r ≫ φ k) ^ ε k : F'ˣ) * f (sF s r J)) ∧
    ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen → ∀ r : Sp F ⟶ Y,
      vF t (spMap f ≫ r) J' = (∏ k, T (r ≫ φ k) ^ ε k : F'ˣ) * f (vF t r J) := by
  obtain ⟨J₀, h₀, e₀⟩ := exists_gauge f hL hJ
  obtain ⟨T, hT⟩ := exists_trans hJ' h₀
  have k : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y),
      sF s (spMap f ≫ r) J' = (∏ k, T (spMap f ≫ r ≫ φ k) ^ ε k : F'ˣ) * f (sF s r J) := fun Y K _ φ ε s r => by
    rw [hT, sF_ext f hJ e₀]
    simp only [Category.assoc]
  exact ⟨fun ψ => T (spMap f ≫ ψ), k, fun Y K _ φ ε t ht r => k Y K φ ε (genSec t ht) r⟩

theorem exists_hom (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F]
    [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') (N : NumD F) (N' : NumD F')
    (ν : NumOf D F N) (ν' : NumOf D F' N') (hth : ν'.th = ν.th) :
    ∃ I : NumD.Hom f N N', I.lam = 1 ∧ (∀ y, ν'.eX (I.e y) = ν.eX y) ∧
      ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (q : N.QT k) (q' : N'.QT k), QkExt f p p' → ν.QPt p q →
        ν'.QPt p' q' → q'.1.1.toAdd = I.e q.1.1.toAdd ∧ I.Rel q.1.2 q'.1.2 := by
  obtain ⟨T, hs, hg⟩ := exists_trans_ext f D.P.isLB ν.good ν'.good
  have hr : rigVal ν' = T (1 : TF (R := R) F ⟶ D.P.A).left * f (rigVal ν) := by
    have := hg _ _ (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.rig_gen (TF (R := R) F).hom
    rw [Fintype.prod_unique, zpow_one] at this
    refine Eq.trans ?_ this
    exact congrArg (fun r => vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig r ν'.J)
      (Over.w (extMap (R := R) f hf)).symm
  have h0 : rigVal ν ≠ 0 := vF_ne_zero ν.good _ _
  let I : NumD.Hom f N N' :=
    { φ := ptHom f hf ν ν'
      h := fun x => T (ν.eA x).left / T (1 : TF (R := R) F ⟶ D.P.A).left
      h_one := by rw [map_one, div_self']
      θ_eq := fun x y u => by
        have e : N'.θ (ptHom f hf ν ν' x) (ptHom f hf ν ν' y) (ptHom f hf ν ν' u) =
            (∏ I : thK, T ((lift (ν.eA x) (lift (ν.eA y) (ν.eA u))).left ≫ thφ D.P.A (x3 D.P.A) I) ^ thε I) *
              Units.map f.toMonoidHom (N.θ x y u) := by
          refine Units.ext ?_
          show _ = _ * f (N.θ x y u : F)
          rw [ν'.θ_eq, ν.θ_eq, eA_ptHom, eA_ptHom, eA_ptHom, ← comp_lift, ← comp_lift]
          exact hg _ _ _ _ _ D.cub.isGen _
        rw [e, prod_cub]
        simp only [map_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel
      σ_eq := fun x => by
        have e : N'.σ (ptHom f hf ν ν' x) = (T (ν.eA x)⁻¹.left * (T (ν.eA x).left)⁻¹) *
            Units.map f.toMonoidHom (N.σ x) := by
          refine Units.ext ?_
          show _ = _ * f (N.σ x : F)
          rw [ν'.σ_eq, ν.σ_eq, eA_ptHom]
          refine (hg _ _ _ _ _ D.sym_gen _).trans (congrArg (fun z : F'ˣ => z.val * _) ?_)
          rw [Fin.prod_univ_two]
          show T ((ν.eA x)⁻¹).left ^ (1 : ℤ) * T ((ν.eA x).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
          rw [Category.comp_id, zpow_one, zpow_neg, zpow_one]
        rw [e, map_inv]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel
      lam := 1
      th_eq := fun x => by
        have a : N'.th (ptHom f hf ν ν' x) * rigVal ν' = _ := ν'.th_eq _
        have b : N.th x * rigVal ν = _ := ν.th_eq _
        have c := hs _ _ _ _ ν.th (ν.eA x).left
        rw [Fintype.prod_unique, Category.comp_id, ← b, zpow_natCast, pow_one, map_mul] at c
        rw [eA_ptHom, hth, hr] at a
        have d := a.trans c
        have h1 : f (rigVal ν) ≠ 0 := (map_ne_zero f).2 h0
        rw [← _root_.mul_assoc, ← _root_.mul_assoc] at d
        have d' := mul_right_cancel₀ h1 d
        rw [_root_.one_mul, Units.val_div_eq_div_val, div_mul_eq_mul_div, ← d', mul_div_cancel_right₀ _ (Units.ne_zero _)]
      e := ν.eX.trans ν'.eX.symm
      c_eq := fun χ => ν'.eA.injective (by
        rw [ν'.c_eq, eA_ptHom, ν.c_eq, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
        exact (DVR.comp_cP D (extMap f hf) _).symm)
      ψ_eq := fun χ => by
        have e : N'.ψ (ν.eX.trans ν'.eX.symm χ) = ((T (ν.eA (N.c χ)).left)⁻¹ * T (1 : TF (R := R) F ⟶ D.P.A).left) *
            Units.map f.toMonoidHom (N.ψ χ) := by
          refine Units.ext ?_
          show _ = ((T (ν.eA (N.c χ)).left)⁻¹).val * (T (1 : TF (R := R) F ⟶ D.P.A).left).val * f (N.ψ χ : F)
          rw [ν'.ψ_eq, ν.ψ_eq, map_mul, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, _root_.mul_mul_mul_comm]
          refine congrArg₂ (· * ·) ?_ hr
          have c := hg _ _ _ _ _ (D.psi_gen (ν.eX χ)) (jFK (R := R) F)
          rw [Fintype.prod_unique, zpow_neg, zpow_one] at c
          refine (congrArg (fun r => vF (D.psi (ν.eX χ)) r ν'.J)
            ((extMap_jFK f hf).trans (Category.id_comp _)).symm).trans (c.trans ?_)
          refine congrArg (fun z => ((T z)⁻¹).val * _) ?_
          rw [ν.c_eq]
          exact congrArg (fun z => z.left) (DVR.comp_cP D
            (Over.homMk (jFK (R := R) F) rfl : TF (R := R) F ⟶ TK R) _)
        rw [e]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel }
  have hX : ∀ y, ν'.eX (I.e y) = ν.eX y := fun y => ν'.eX.apply_symm_apply _
  refine ⟨I, rfl, hX, fun k p p' q q' h hq hq' => ⟨ν'.eX.injective (hq'.1.trans (h.1.trans (hq.1.symm.trans (hX _).symm))),
    ν'.eA.injective (hq'.2.1.trans (Over.OverMorphism.ext ?_)), fun χ => ?_⟩⟩
  · rw [h.2.1, ← hq.2.1]
    exact (congrArg (fun z => z.left) (eA_ptHom f hf ν ν' _)).symm
  · have e : q'.1.2.s (I.e χ) = (∏ i, T (DegPre.gtφ D F p.g.b (ν.eX χ) i) ^ DegPre.gtε i) *
        Units.map f.toMonoidHom (q.1.2.s χ) := by
      refine Units.ext ?_
      show _ = _ * f (q.1.2.s χ : F)
      rw [hq'.2.2, hq.2.2, hX]
      have c := hg _ _ _ _ _ (p.g.isGen (ν.eX χ)) (𝟙 (Sp F))
      simp only [Category.id_comp, Category.comp_id] at c
      refine Eq.trans ?_ c
      let y : Sp F' := IsLocalRing.closedPoint F'
      have hJ : Good D.P.L y ν'.J := fun ψ => ν'.good ψ trivial
      refine (stalkConst y).injective ((val_eq_vF ν'.good _ _ y).symm.trans (Eq.trans ?_ (val_eq_vF ν'.good _ _ y)))
      refine congrArg Units.val ((val_corr hJ (h.2.2 _) _).trans ((val_pull hJ _ _ _).trans ?_))
      rw [Category.id_comp]
    rw [e, prod_gt]
    show _ * (T (ν.eA (N.c χ * q.1.2.b)).left / _) = _ * (T (ν.eA (N.c χ)).left / _) * (T (ν.eA q.1.2.b).left / _)
    rw [map_mul, hq.2.1, ν.c_eq]
    show _ * (T (DVR.cP D (TF (R := R) F) (ν.eX χ) * p.g.b).left / _) =
      _ * (T (DVR.cP D (TF (R := R) F) (ν.eX χ)).left / _) * _
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel

end GlobalTheory.GaugeHom
end
