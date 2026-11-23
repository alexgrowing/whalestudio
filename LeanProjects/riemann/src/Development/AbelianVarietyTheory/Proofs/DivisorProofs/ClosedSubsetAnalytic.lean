import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUniOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedMinorNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUnipotentTriangularizingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRegularAdaptedLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityCriterionNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodReductionPointAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveGenericFibreSectionRestrictionStatement
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieFilt.LocRegPf

section Mat
variable {κ : Type} [Fintype κ] (bl : κ → ℕ) {g : ℕ}

theorem minor_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (w : κ ≃ Fin g) (k : ℕ)
    (P : Matrix (Fin g) κ R) : minor bl w k (P.map f) = f (minor bl w k P) := by
  unfold minor
  rw [RingHom.map_det]
  rfl

theorem minor_eq_det {R : Type} [CommRing R] (w : κ ≃ Fin g) (k : ℕ) (hk : ∀ z, bl z < k)
    (P : Matrix (Fin g) κ R) : minor bl w k P = (P.submatrix w id).det := by
  unfold minor
  have e : (P.submatrix w id).toSquareBlockProp (fun z => bl z < k) =
      (P.submatrix w id).submatrix (Equiv.subtypeUnivEquiv hk) (Equiv.subtypeUnivEquiv hk) := by
    ext i j; rfl
  rw [e, Matrix.det_submatrix_equiv_self]

end Mat

theorem norm_io_eq_one_iff {F : Type} [Field F] [NumberField F] {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)}
    (ε : TrueGeo.Ext v) [Fact (resP v).Prime] (a : ε.O) :
    ‖ioOf (resP v) ε (a : AlgebraicClosure F)‖ = 1 ↔ IsUnit a := by
  have h := ioOf_le_one_iff (resP v) (residueCharacteristic_mem v) ε
  constructor
  · intro ha
    have ha0 : (a : AlgebraicClosure F) ≠ 0 := by
      intro h0; rw [h0, map_zero, norm_zero] at ha; exact zero_ne_one ha
    have hi : (a : AlgebraicClosure F)⁻¹ ∈ ε.O := by
      rw [← h, map_inv₀, norm_inv, ha, inv_one]
    exact IsUnit.of_mul_eq_one (b := (⟨_, hi⟩ : ε.O)) (Subtype.ext (mul_inv_cancel₀ ha0))
  · rintro ⟨u, rfl⟩
    have h1 := (h _).2 u.1.2
    have h2 := (h _).2 (u⁻¹ : ε.Oˣ).1.2
    have hm : ‖ioOf (resP v) ε ((u : ε.O) : AlgebraicClosure F)‖ *
        ‖ioOf (resP v) ε (((u⁻¹ : ε.Oˣ) : ε.O) : AlgebraicClosure F)‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← Subring.coe_mul, Units.mul_inv]
      simp
    have n1 := norm_nonneg (ioOf (resP v) ε ((u : ε.O) : AlgebraicClosure F))
    have n2 := norm_nonneg (ioOf (resP v) ε (((u⁻¹ : ε.Oˣ) : ε.O) : AlgebraicClosure F))
    nlinarith

section Pts
variable {F : Type} [Field F] [NumberField F] {X W : Scheme.{0}} {jB : W ⟶ X}

theorem top_le_of_int {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (ε : TrueGeo.Ext v)
    (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X) (hc : spMap ε.O.subtype ≫ xt = xg ≫ jB)
    (V : X.Opens) (ht : ⊤ ≤ xt ⁻¹ᵁ V) : ⊤ ≤ xg ⁻¹ᵁ (jB ⁻¹ᵁ V) := by
  have hx' : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ V := fun p _ => by
    change (xg ≫ jB) p ∈ V
    rw [← hc]
    exact ht (x := spMap ε.O.subtype p) trivial
  exact fun p hp => hx' hp

theorem evalPt_int {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (ε : TrueGeo.Ext v)
    (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X) (hc : spMap ε.O.subtype ≫ xt = xg ≫ jB)
    (V : X.Opens) (ht : ⊤ ≤ xt ⁻¹ᵁ V) (hx : ⊤ ≤ xg ⁻¹ᵁ (jB ⁻¹ᵁ V)) (f : Γ(X, V)) :
    TangentOrigin.evalPt xg (jB ⁻¹ᵁ V) hx (jB.app V f) = (TangentOrigin.evalPt xt V ht f : AlgebraicClosure F) := by
  have hx' : ⊤ ≤ (xg ≫ jB) ⁻¹ᵁ V := fun p hp => hx hp
  have e0 : TangentOrigin.evalPt (xg ≫ jB) V hx' f = TangentOrigin.evalPt xg (jB ⁻¹ᵁ V) hx (jB.app V f) := by
    unfold TangentOrigin.evalPt
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [← e0]
  have key : ∀ (y : Sp (AlgebraicClosure F) ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ V), spMap ε.O.subtype ≫ xt = y →
      TangentOrigin.evalPt y V hy f = (TangentOrigin.evalPt xt V ht f : AlgebraicClosure F) := by
    rintro y hy rfl
    exact TangentOrigin.evalPt_spMap_comp ε.O.subtype xt V ht hy f
  exact key _ hx' hc

end Pts

end GlobalTheory.LieFilt.LocRegPf

namespace GlobalTheory.LieFilt

open LocRegPf in

theorem exists_regular_blockUni_change : ∀ {F : Type} [Field F] [NumberField F] {X W : Scheme.{0}} {q : X ⟶ Sp (𝓞 F)} {s : W ⟶ Sp F} {jB : W ⟶ X} {d : ℕ},
    IsArithVar q d → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPullback jB s q (spMap (algebraMap (𝓞 F) F)) →
    ∀ {κ : Type} [Fintype κ] (bl : κ → ℕ) {g : ℕ} (V : X.Opens), IsAffineOpen V → ∀ x₀ ∈ V,
    ∀ A : Matrix (Fin g) κ Γ(W, jB ⁻¹ᵁ V),
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime) (ε : TrueGeo.Ext v)
      (xg : Sp (AlgebraicClosure F) ⟶ W) (xt : Sp ε.O ⟶ X), xg ≫ s = spMap (algebraMap F (AlgebraicClosure F)) →
      spMap ε.O.subtype ≫ xt = xg ≫ jB → ⊤ ≤ xt ⁻¹ᵁ V → ∀ hx : ⊤ ≤ xg ⁻¹ᵁ (jB ⁻¹ᵁ V),
      haveI : Fact (resP v).Prime := ⟨hp⟩
      IntAdapted bl (A.map ((ioOf (resP v) ε).comp (TangentOrigin.evalPt xg (jB ⁻¹ᵁ V) hx)))) →
    ∃ (V' : X.Opens) (hV' : V' ≤ V), x₀ ∈ V' ∧ Function.Injective (jB.app V') ∧
      ∃ (C : Matrix (Fin g) κ Γ(X, V')) (C' : Matrix κ (Fin g) Γ(X, V')) (Q : Matrix κ κ Γ(W, jB ⁻¹ᵁ V')),
        C * C' = 1 ∧ C' * C = 1 ∧ BlockUni bl Q ∧ C.map (jB.app V') = A.map (resG W (jB.preimage_mono hV')) * Q := by
  intro F _ _ X W q s jB d hq hn pb κ _ bl g V hV x₀ hx₀ A hA
  have hint := IntCritPf.intCrit F X W q s jB d hq hn pb
  obtain ⟨v₀, ε₀, xg₀, xt₀, ht₀, hs₀, hc₀, hcen⟩ := GlobalTheory.T.exists_good_reduction_point_affine_open hq pb V hV x₀ hx₀
  have hx0 := top_le_of_int ε₀ xg₀ xt₀ hc₀ V ht₀
  haveI : Fact (resP v₀).Prime := ⟨residueCharacteristic_prime v₀⟩
  obtain ⟨-, w, hw⟩ := GlobalTheory.T.integral_adapted_minor_norms bl _ (hA v₀ (residueCharacteristic_prime v₀) ε₀ xg₀ xt₀ hs₀ hc₀ ht₀ hx0)

  have hm : ∀ k, ∃ Δ : Γ(X, V), jB.app V Δ = minor bl w k A := by
    intro k
    refine hint V hV _ fun v ε xg xt hs hc ht hx => ?_
    haveI : Fact (resP v).Prime := ⟨residueCharacteristic_prime v⟩
    have h1 := (GlobalTheory.T.integral_adapted_minor_norms bl _ (hA v (residueCharacteristic_prime v) ε xg xt hs hc ht hx)).1 w k
    rw [minor_map, RingHom.comp_apply] at h1
    exact (ioOf_le_one_iff (resP v) (residueCharacteristic_mem v) ε _).1 h1
  choose Δ' hΔ' using hm
  set K₀ := Finset.univ.sup bl + 1 with hK₀
  have hbig : ∀ z, bl z < K₀ := fun z => Nat.lt_succ_of_le (Finset.le_sup (f := bl) (Finset.mem_univ z))
  have hmin : ∀ {R : Type} [CommRing R] (P : Matrix (Fin g) κ R) (k : ℕ), minor bl w (min k K₀) P = minor bl w k P := by
    intro R _ P k
    rcases le_total k K₀ with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, minor_eq_det bl w K₀ hbig, minor_eq_det bl w k fun z => (hbig z).trans_le h]
  set Δ : ℕ → Γ(X, V) := fun k => Δ' (min k K₀) with hΔdef
  have hΔ : ∀ k, jB.app V (Δ k) = minor bl w k A := fun k => by
    rw [hΔdef]; dsimp only; rw [hΔ', hmin]

  have hcu : ∀ k, IsUnit (TangentOrigin.evalPt xt₀ V ht₀ (Δ k)) := by
    intro k
    rw [← norm_io_eq_one_iff ε₀, ← evalPt_int ε₀ xg₀ xt₀ hc₀ V ht₀ hx0, hΔ, ← RingHom.comp_apply, ← minor_map]
    exact hw k
  set Pr₀ : Γ(X, V) := ∏ k ∈ Finset.range (K₀ + 1), Δ k with hPr₀
  set V' := X.basicOpen Pr₀ with hV'def
  have hV'le : V' ≤ V := X.basicOpen_le Pr₀
  have hV'aff : IsAffineOpen V' := hV.basicOpen Pr₀
  have hx₀' : x₀ ∈ V' := by
    refine hcen Pr₀ ?_
    rw [hPr₀, map_prod]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun k _ => hcu k
  have hunit : ∀ k, IsUnit (resG X hV'le (Δ k)) := by
    intro k
    have hk : Δ k = Δ (min k K₀) := by simp only [hΔdef, min_assoc, min_self]
    have hmem : min k K₀ ∈ Finset.range (K₀ + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le (min_le_right _ _))
    have hu : IsUnit (resG X hV'le Pr₀) := X.toRingedSpace.isUnit_res_basicOpen Pr₀
    rw [hk]
    exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ hmem)) hu

  set A' := A.map (resG W (jB.preimage_mono hV'le)) with hA'
  have hA'm : ∀ k, minor bl w k A' = jB.app V' (resG X hV'le (Δ k)) := by
    intro k
    rw [hA', minor_map, ← hΔ, GlobalTheory.GenericFibreInt.app_resG']
  obtain ⟨Q, hQ, hdet, htri⟩ := GlobalTheory.T.exists_block_unipotent_triangularizing bl A' w fun k => (hA'm k) ▸ (hunit k).map _
  have hC : ∀ b z, ∃ c : Γ(X, V'), jB.app V' c = (A' * Q) b z := by
    intro b z
    refine hint V' hV'aff _ fun v ε xg xt hs hc ht' hx' => ?_
    haveI : Fact (resP v).Prime := ⟨residueCharacteristic_prime v⟩
    have ht : ⊤ ≤ xt ⁻¹ᵁ V := ht'.trans (xt.preimage_mono hV'le)
    have hx := top_le_of_int ε xg xt hc V ht
    set φ' := (ioOf (resP v) ε).comp (TangentOrigin.evalPt xg (jB ⁻¹ᵁ V') hx') with hφ'
    have hAd := hA v (residueCharacteristic_prime v) ε xg xt hs hc ht hx
    have hP : A.map ((ioOf (resP v) ε).comp (TangentOrigin.evalPt xg (jB ⁻¹ᵁ V) hx)) = A'.map φ' := by
      ext i j
      simp only [hA', Matrix.map_apply, hφ', RingHom.comp_apply]
      rw [TangentOrigin.evalPt_res xg (jB.preimage_mono hV'le) hx hx']
    rw [hP] at hAd
    have hnm : ∀ k, ‖minor bl w k (A'.map φ')‖ = 1 := by
      intro k
      rw [minor_map, hA'm, hφ', RingHom.comp_apply, evalPt_int ε xg xt hc V' ht' hx']
      exact (norm_io_eq_one_iff ε _).2 ((hunit k).map _)
    have hQ' : BlockUni bl (Q.map φ') := by
      intro z z' h
      rw [Matrix.map_apply, hQ z z' h, ← Matrix.map_apply (f := φ'), Matrix.map_one _ (map_zero φ') (map_one φ')]
    have htri' : ∀ z z', bl z < bl z' → (A'.map φ' * Q.map φ') (w z) z' = 0 := by
      intro z z' h
      rw [← Matrix.map_mul, Matrix.map_apply, htri z z' h, map_zero]
    have h1 := GlobalTheory.T.integral_adapted_triangular_bounded bl (A'.map φ') w hAd hnm (Q.map φ') hQ' htri' b z
    rw [← Matrix.map_mul, Matrix.map_apply, hφ', RingHom.comp_apply] at h1
    exact (ioOf_le_one_iff (resP v) (residueCharacteristic_mem v) ε _).1 h1
  obtain ⟨C, hCe⟩ : ∃ C : Matrix (Fin g) κ Γ(X, V'), ∀ b z, jB.app V' (C b z) = (A' * Q) b z :=
    ⟨Matrix.of fun b z => (hC b z).choose, fun b z => (hC b z).choose_spec⟩

  have hinj := GlobalTheory.T.injective_generic_fibre_section_restriction hq pb V' hV'aff
  set D := C.submatrix w id with hD
  have hdetD : D.det = resG X hV'le (Δ K₀) := by
    apply hinj
    rw [RingHom.map_det, ← hA'm, minor_eq_det bl w K₀ hbig]
    have : (jB.app V').hom.mapMatrix D = (A' * Q).submatrix w id := by
      ext i j; exact hCe _ _
    rw [this]
    have e2 : (A' * Q).submatrix w id = A'.submatrix w id * Q := by
      ext i j; simp [Matrix.mul_apply]
    rw [e2, Matrix.det_mul, hdet, mul_one]
  have hDu : IsUnit D.det := hdetD ▸ hunit K₀
  refine ⟨V', hV'le, hx₀', hinj, C, (D⁻¹).submatrix id w.symm, Q, ?_, ?_, hQ, ?_⟩
  · have eC : C = D.submatrix w.symm id := by ext i j; simp [hD]
    rw [eC]
    refine (Matrix.submatrix_mul D D⁻¹ w.symm id w.symm Function.bijective_id).symm.trans ?_
    rw [Matrix.mul_nonsing_inv _ hDu]
    exact Matrix.submatrix_one_equiv _
  · have eC : C = D.submatrix w.symm id := by ext i j; simp [hD]
    rw [eC]
    refine (Matrix.submatrix_mul D⁻¹ D id w.symm id w.symm.bijective).symm.trans ?_
    rw [Matrix.nonsing_inv_mul _ hDu]
    exact Matrix.submatrix_id_id _
  · ext b z
    exact hCe b z

end GlobalTheory.LieFilt

end
