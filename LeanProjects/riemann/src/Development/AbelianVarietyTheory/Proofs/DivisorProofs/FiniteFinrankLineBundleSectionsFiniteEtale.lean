import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin
open H0

theorem eq_zero_of_forall_algHom_eq_zero {E A : Type} (Ω : Type) [Field E] [CommRing A]
    [Algebra E A] [Algebra.Etale E A] [Field Ω] [IsAlgClosed Ω] [Algebra E Ω] {a : A}
    (h : ∀ φ : A →ₐ[E] Ω, φ a = 0) : a = 0 := by
  have := Algebra.FormallyUnramified.finite_of_free E A
  have : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field E A
  have : IsArtinianRing A := .of_finite E A
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun J hJ => ?_)
  have hm : J.IsMaximal := IsArtinianRing.isMaximal_of_isPrime J
  let := Ideal.Quotient.field J
  let ψ : (A ⧸ J) →ₐ[E] Ω := IsAlgClosed.lift
  have := h (ψ.comp (Ideal.Quotient.mkₐ E J))
  rw [AlgHom.comp_apply, map_eq_zero_iff ψ ψ.toRingHom.injective] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 this

section Points

variable {k R : Type} [CommRing k] [CommRing R] {S : Scheme.{0}}

theorem evalPt_algX (q : S ⟶ Sp k) (x : Sp R ⟶ S) (U : S.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (c : k) :
    evalPt x U h (algX q U c) =
      evalPt (x ≫ q) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) :=
  congrArg (fun g => (g ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
    (Scheme.Hom.appLE_comp_appLE x q ⊤ U ⊤ le_top h)

theorem evalPt_algX_of_eq (q : S ⟶ Sp k) (x : Sp R ⟶ S) {φ : k →+* R} (hx : x ≫ q = spMap φ)
    (U : S.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (c : k) : evalPt x U h (algX q U c) = φ c := by
  rw [evalPt_algX, hx, evalPt_spMap]

theorem H0.val_smul {q : S ⟶ Sp k} {N : LB S} {O : S.Opens} (x : Sp R ⟶ S) {φ : k →+* R}
    (hx : x ≫ q = spMap φ) (i : N.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ N.U i) (c : k)
    (f : H0 q N O) : val x i hO hi (c • f) = φ c * val x i hO hi f := by
  rw [base_smul, val_fun_smul, evalPt_algX_of_eq q x hx]

variable (R) in

abbrev PtsOver [Algebra k R] (q : S ⟶ Sp k) : Type :=
  {x : Sp R ⟶ S // x ≫ q = spMap (algebraMap k R)}

def ptsOverEquiv [Algebra k R] [IsAffine S] (q : S ⟶ Sp k) :
    letI := (algX q ⊤).toAlgebra
    PtsOver R q ≃ (Γ(S, ⊤) →ₐ[k] R) :=
  letI := (algX q ⊤).toAlgebra
  Equiv.ofBijective
    (fun x => ⟨evalPt x.1 ⊤ le_top, fun c => evalPt_algX_of_eq q x.1 x.2 ⊤ le_top c⟩)
    ⟨fun x y e => Subtype.ext (ext_evalPt (isAffineOpen_top S) le_top le_top
      (congrArg AlgHom.toRingHom e)), fun ψ => by
      obtain ⟨x, h, e⟩ := exists_evalPt_eq (isAffineOpen_top S) ψ.toRingHom
      refine ⟨⟨x, eq_spMap_of_evalPt _ _ fun c => ?_⟩, AlgHom.ext fun a => DFunLike.congr_fun e a⟩
      rw [← evalPt_algX q x ⊤ h, e]
      exact ψ.commutes c⟩

end Points

section FiniteEtale

variable {E : Type} [Field E] {S : Scheme.{0}} (q : S ⟶ Sp E)

theorem etale_algX [IsAffine S] [Etale q] : (algX q ⊤).Etale :=
  RingHom.Etale.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of E)).symm.commRingCatIsoToRingEquiv
    (HasRingHomProperty.appLE @Etale q ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩ le_top)

variable {N : LB S}

theorem exists_generator [IsFinite q] [Etale q] (hN : N.IsLB) : ∃ e : H0 q N ⊤,
    (Function.Bijective fun a : Γ(S, ⊤) => a • e) ∧ ∀ i, IsUnit (e.loc i) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  have : IsArtinianRing Γ(S, ⊤) := .of_finite E _
  obtain ⟨t, ht⟩ := exists_isGen_of_subsingleton_pic_top hN
  refine ⟨H0.ofSec q ⊤ (DVR.genSec t ht), ?_, fun i => (Units.isUnit (t.s i)).map (resG S inf_le_right)⟩
  have := isQuasicoherent_toMod hN
  exact (isFrame_iff_bijective (isAffineOpen_top S) _).1 (isFrame_genSec hN ht ⊤)

variable (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra E Ω] [IsFinite q] [Etale q]

omit [IsAlgClosed Ω] in

theorem finite_ptsOver : Finite (PtsOver Ω q) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  exact Finite.of_equiv _ (ptsOverEquiv q).symm

theorem finite_finrank_lineBundleSections_finiteEtale (hN : N.IsLB) :
    Module.Finite E (H0 q N ⊤) ∧ Module.finrank E (H0 q N ⊤) = Nat.card (PtsOver Ω q) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  obtain ⟨e, he, -⟩ := exists_generator q hN
  let ψ : Γ(S, ⊤) →ₗ[E] H0 q N ⊤ :=
    { toFun a := a • e
      map_add' a b := add_smul a b e
      map_smul' c a := mul_smul (algX q ⊤ c) a e }
  let φ := LinearEquiv.ofBijective ψ he
  exact ⟨.equiv φ, by
    rw [← φ.finrank_eq, Nat.card_congr (ptsOverEquiv q), natCard_algHom_eq_finrank_of_etale]⟩

variable {q Ω}

theorem H0.eq_zero_of_forall_val_eq_zero (hN : N.IsLB) (i : PtsOver Ω q → N.ι)
    (hi : ∀ x : PtsOver Ω q, ⊤ ≤ x.1 ⁻¹ᵁ N.U (i x)) {g : H0 q N ⊤}
    (h : ∀ x : PtsOver Ω q, val x.1 (i x) le_top (hi x) g = 0) : g = 0 := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  obtain ⟨e, he, hu⟩ := exists_generator q hN
  obtain ⟨a, rfl⟩ := he.2 g
  have : a = 0 := eq_zero_of_forall_algHom_eq_zero (E := E) Ω fun ψ => by
    obtain ⟨x, rfl⟩ := (ptsOverEquiv q).surjective ψ
    have := (val_fun_smul x.1 (i x) le_top (hi x) a e).symm.trans (h x)
    exact (((hu (i x)).map (evalPt x.1 _ _)).mul_left_eq_zero).1 this
  simp only [this, zero_smul]

end FiniteEtale

section Subscheme

variable {E : Type} [Field E] {Y : Scheme.{0}} {p : Y ⟶ Sp E} {I : Y.IdealSheafData} {B : LB Y}

theorem exists_chart_of_field {F : Type} [Field F] (hB : B.IsLB) (x : Sp F ⟶ Y) :
    ∃ i, ⊤ ≤ x ⁻¹ᵁ B.U i := by
  obtain ⟨i, hi⟩ := exists_chart hB (x (default : PrimeSpectrum F))
  exact ⟨i, fun z _ => (Subsingleton.elim (α := PrimeSpectrum F) default z) ▸ hi⟩

theorem valOn_smul {k R : Type} [CommRing k] [CommRing R] {p : Y ⟶ Sp k}
    (x : Sp R ⟶ I.subscheme) {φ : k →+* R} (hx : x ≫ I.subschemeι ≫ p = spMap φ) (i : B.ι)
    (hi : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ B.U i) (c : k) (g : sectionsOnClosedSubscheme p B I) :
    valOn x i hi (c • g) = φ c * valOn x i hi g :=
  H0.val_smul x hx _ _ _ c g

variable [IsFinite (I.subschemeι ≫ p)] [Etale (I.subschemeι ≫ p)] (hB : B.IsLB)
  (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra E Ω]

include hB

theorem finite_H0On : Module.Finite E (sectionsOnClosedSubscheme p B I) :=
  (finite_finrank_lineBundleSections_finiteEtale _ (AlgebraicClosure E) (LB.isLB_pull hB _)).1

theorem finrank_H0On :
    Module.finrank E (sectionsOnClosedSubscheme p B I) = Nat.card (PtsOver Ω (I.subschemeι ≫ p)) :=
  (finite_finrank_lineBundleSections_finiteEtale _ Ω (LB.isLB_pull hB _)).2

variable {Ω} in

theorem eq_zero_of_forall_valOn_eq_zero (i : PtsOver Ω (I.subschemeι ≫ p) → B.ι)
    (hi : ∀ x : PtsOver Ω (I.subschemeι ≫ p), ⊤ ≤ (x.1 ≫ I.subschemeι) ⁻¹ᵁ B.U (i x))
    {g : sectionsOnClosedSubscheme p B I} (h : ∀ x : PtsOver Ω (I.subschemeι ≫ p), valOn x.1 (i x) (hi x) g = 0) : g = 0 :=
  H0.eq_zero_of_forall_val_eq_zero (LB.isLB_pull hB _) (fun x _ => i x) _ h

end Subscheme

example (D : ℕ) : Module.finrank ℚ (sectionsOnClosedSubscheme (CanonLB.affStr ℚ D) (AffineExample.triv ℚ D)
    (AffineExample.ideal MvPolynomial.X)) = 1 := by
  have := AffineExample.isIso_of_span (k := ℚ) (D := D) (g := MvPolynomial.X) rfl
  rw [finrank_H0On AffineExample.isLB_triv ℂ, Nat.card_eq_one_iff_exists]
  exact ⟨⟨spMap (algebraMap ℚ ℂ) ≫ inv _, by simp⟩, fun x => Subtype.ext
    ((IsIso.eq_comp_inv _).2 x.2)⟩

end GlobalTheory.Vanishing
