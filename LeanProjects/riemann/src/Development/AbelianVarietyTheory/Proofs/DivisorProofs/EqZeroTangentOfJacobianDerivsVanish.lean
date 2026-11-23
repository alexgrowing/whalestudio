import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TopForm

theorem derivation_eq_zero_of_jacobian {k B F : Type} [CommRing k] [CommRing B] [Field F]
    {D : ℕ} {α : k →+* B} (hα : α.IsStandardSmoothOfRelativeDimension D) {ω : Forms α D}
    (hω : IsFreeGen B ω) (g : Fin D → B) {J : B} (hJ : J • ω = dForm α g) (φ : B →+* F)
    (hJ0 : φ J ≠ 0) (δ : B → F) (hadd : ∀ x y, δ (x + y) = δ x + δ y)
    (hmul : ∀ x y, δ (x * y) = φ x * δ y + φ y * δ x) (hc : ∀ c, δ (α c) = 0)
    (hg : ∀ a, δ (g a) = 0) (b : B) : δ b = 0 := by
  classical
  letI := α.toAlgebra
  letI : Algebra B F := φ.toAlgebra
  letI : Algebra k F := (φ.comp α).toAlgebra
  haveI : IsScalarTower k B F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Nontrivial B := φ.domain_nontrivial
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k B := hα
  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth D (R := k) (S := B)
  have hr : Module.finrank B Ω[B⁄k] = D := Module.finrank_eq_of_rank_eq
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := B) D)
  let e := Module.finBasisOfFinrankEq B Ω[B⁄k] hr
  let δ' : Derivation k B F := Derivation.mk'
    { toFun := δ
      map_add' := hadd
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, hmul]
        rw [show δ (algebraMap k B c) = 0 from hc c, mul_zero, add_zero, Algebra.smul_def]
        rfl }
    (fun x y => hmul x y)
  let ℓ := δ'.liftKaehlerDifferential
  have hℓ (x : B) : ℓ (KaehlerDifferential.D k B x) = δ x :=
    Derivation.liftKaehlerDifferential_comp_D δ' x
  let m : Matrix (Fin D) (Fin D) B := Matrix.of fun a c => e.repr (KaehlerDifferential.D k B (g a)) c
  have hsum (a : Fin D) : KaehlerDifferential.D k B (g a) = ∑ c, m a c • e c :=
    (e.sum_repr _).symm
  obtain ⟨c, hc'⟩ := hω.2 (exteriorPower.ιMulti B D e)
  have h1 : dForm α g = m.det • exteriorPower.ιMulti B D e := by
    rw [dForm_eq, ← alternating_map_sum_smul_eq_det_smul]
    exact congrArg _ (funext hsum)
  have h2 : J = m.det * c := by
    apply hω.1
    change J • ω = (m.det * c) • ω
    rw [hJ, h1, mul_smul]
    exact congrArg _ hc'.symm
  have h3 : (φ.mapMatrix m).det ≠ 0 := by
    rw [← RingHom.map_det]
    intro h0
    exact hJ0 (by rw [h2, map_mul, h0, zero_mul])
  have h4 : (φ.mapMatrix m).mulVec (fun c => ℓ (e c)) = 0 := by
    funext a
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← hg a, ← hℓ, hsum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, Algebra.smul_def]
    rfl
  have h5 := Matrix.eq_zero_of_mulVec_eq_zero h3 h4
  have h6 : ℓ = 0 := e.ext fun c => congrFun h5 c
  rw [← hℓ, h6, LinearMap.zero_apply]

end GlobalTheory.TopForm

namespace GlobalTheory.CanonLB

open TopForm
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem spMap_fst_surjective_field (F : Type) [Field F] :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom F F F).toRingHom) := by
  intro p
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F), ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  change x.fst ∈ (⊥ : Ideal F) ↔ x ∈ PrimeSpectrum.asIdeal p
  rw [Ideal.mem_bot]
  constructor
  · intro hx
    apply p.isPrime.mem_of_pow_mem 2
    have : x ^ 2 = 0 := by
      rw [pow_two, show x = TrivSqZeroExt.inr x.snd from TrivSqZeroExt.ext hx rfl,
        TrivSqZeroExt.inr_mul_inr]
    rw [this]
    exact Ideal.zero_mem _
  · intro hx
    by_contra h0
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)

theorem eq_zero_tangent_of_jacobian {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k}
    {D : ℕ} [SmoothOfRelativeDimension D p] (K : GlobalTheory.CanonLB p D) (i : K.bundle.ι) {F : Type}
    [Field F] (z : Sp F ⟶ Y) (hz : ⊤ ≤ z ⁻¹ᵁ K.bundle.U i) (g : Fin D → Γ(Y, K.bundle.U i))
    (hJ : evalPt z _ hz (K.jacobian i le_rfl g) ≠ 0) (w : Sp (DualNumber F) ⟶ Y)
    (hw : ⊤ ≤ w ⁻¹ᵁ K.bundle.U i)
    (hfst : spMap (TrivSqZeroExt.fstHom F F F).toRingHom ≫ w = z)
    (hp : w ≫ p = spMap (TrivSqZeroExt.inlHom F F) ≫ z ≫ p)
    (hg : ∀ a, (evalPt w _ hw (g a)).snd = 0) : w = spMap (TrivSqZeroExt.inlHom F F) ≫ z := by
  classical
  have hU : IsAffineOpen (K.bundle.U i) := K.affine i
  haveI : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  let y0 : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  have hx : z y0 ∈ K.bundle.U i := hz (Set.mem_univ y0)
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨K.bundle.U i, hU⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, K.bundle.U i)), z y0 ∈ Y.basicOpen (t : Γ(Y, K.bundle.U i)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hU).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hU (t : Γ(Y, K.bundle.U i))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, K.bundle.U i))))
  have hVU : Y.basicOpen (t : Γ(Y, K.bundle.U i)) ≤ K.bundle.U i := Y.basicOpen_le _
  have h₂ : (algX p (Y.basicOpen (t : Γ(Y, K.bundle.U i)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p hVU]
    exact h₁
  have hV : IsAffineOpen (Y.basicOpen (t : Γ(Y, K.bundle.U i))) := hU.basicOpen _
  generalize Y.basicOpen (t : Γ(Y, K.bundle.U i)) = V at hxt hVU h₂ hV
  have hzV : ⊤ ≤ z ⁻¹ᵁ V := fun y _ => by
    obtain rfl : y = y0 := Subsingleton.elim _ _
    exact hxt
  have hwV : ⊤ ≤ w ⁻¹ᵁ V := fun y _ => by
    obtain ⟨y', rfl⟩ := spMap_fst_surjective_field F y
    have := hzV (Set.mem_univ y')
    rw [← hfst] at this
    exact this
  have hinlV : ⊤ ≤ (spMap (TrivSqZeroExt.inlHom F F) ≫ z) ⁻¹ᵁ V := fun y _ =>
    hzV (Set.mem_univ _)
  have key : ∀ (y : Sp F ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ V),
      spMap (TrivSqZeroExt.fstHom F F F).toRingHom ≫ w = y →
      ∀ b, (evalPt w V hwV b).fst = evalPt y V hy b := by
    rintro y hy rfl b
    exact (evalPt_spMap_comp _ w V hwV hy b).symm
  have hfstV := key z hzV hfst
  have hconst (c : k) : (evalPt w V hwV (algX p V c)).snd = 0 := by
    have e1 : evalPt w V hwV (algX p V c) = evalPt (w ≫ p) ⊤ le_rfl
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) := evalPt_constFn p w V hwV c
    have key2 : ∀ (q : Sp (DualNumber F) ⟶ Sp k), q = spMap (TrivSqZeroExt.inlHom F F) ≫ z ≫ p →
        (evalPt q ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)).snd = 0 := by
      rintro q rfl
      rw [evalPt_spMap_comp _ (z ≫ p) ⊤ le_rfl le_rfl]
      simp
    rw [e1]
    exact key2 _ hp
  have hJV : evalPt z V hzV (K.jacobian i hVU fun a => resG Y hVU (g a)) ≠ 0 := by
    rw [show (K.jacobian i hVU fun a => resG Y hVU (g a)) =
        resG Y hVU (K.jacobian i le_rfl g) from (K.resG_jacobian i le_rfl hVU g).symm,
      evalPt_res z hVU hz hzV]
    exact hJ
  have hδ := derivation_eq_zero_of_jacobian h₂ ((K.isFrame i).res hV hVU).gen
    (fun a => resG Y hVU (g a)) (K.jacobian_smul_om i hV hVU _) (evalPt z V hzV) hJV
    (fun b => (evalPt w V hwV b).snd) (fun x y => by simp)
    (fun x y => by
      simp only [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, hfstV]
      ring)
    hconst (fun a => by rw [evalPt_res w hVU hw hwV]; exact hg a)
  refine ext_evalPt hV hwV hinlV (RingHom.ext fun b => ?_)
  rw [evalPt_spMap_comp _ z V hzV hinlV]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [hfstV]
    rfl
  · rw [hδ b]
    rfl

end GlobalTheory.CanonLB
