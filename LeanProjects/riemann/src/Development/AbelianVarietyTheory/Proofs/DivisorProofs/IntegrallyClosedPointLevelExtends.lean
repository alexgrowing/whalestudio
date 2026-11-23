import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionMonoBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftToPrimeLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionSectionPullbackStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.WeilSpec

set_option maxHeartbeats 1000000 in
theorem weil_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ), (p : ℂ) ∈ W.nonunits → l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ (a : Dw.La)
      (κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ),
      (∀ (e σ : Over.mk y ⟶ Y.oF.t.G), e.left = y ≫ (Y.oF.etaA a).left → σ ^ (p ^ n) = 1 →
        Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
          (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ))))) →
    ∀ (f : R) (wf : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ ξ) ⟶ Y.t.G), wf ^ (p ^ n) = 1 →
    ∀ (g : Localization.Away f →+* FractionRing R), g.comp (algebraMap R _) = algebraMap R (FractionRing R) →
    ∀ (x0 : R →+* 𝓞_ℂ_[p]) (φ : Localization.Away f →+* ℂ_[p]),
      φ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0 →
    ∀ (yy : Sp ℂ_[p] ⟶ Xo'.XF c'), spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap x0 ≫ ξ = yy ≫ Y.j →
    ∀ (e σ : Over.mk yy ⟶ Y.oF.t.G), e.left = yy ≫ (Y.oF.etaA a).left → σ.left ≫ Y.m.φ = spMap φ ≫ wf.left →
      σ ^ (p ^ n) = 1 ∧ Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
        (unitOn (Units.map ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0).toMonoidHom (κ (spMap g ≫ wf.left)))) := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n hp hA R _ _ _ ξ y hy a κ hκ f wf hwf g hg x0 φ hφ yy hyy e σ he hσ
  set χ : R →+* ℂ_[p] := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0 with hχ
  set q : Ideal R := RingHom.ker χ with hq
  haveI : q.IsPrime := RingHom.ker_isPrime χ
  haveI hj : IsOpenImmersion Y.j := GlobalTheory.LocM.BaseMdl.isOpenImmersion_j (Fact.out) hp Y
  haveI hmono : Mono Y.j := GlobalTheory.PolArc.mono_j_of_valuationSubring _ Y
  have hyy' : spMap χ ≫ ξ = yy ≫ Y.j := by rw [← hyy, sp_sp]
  obtain ⟨yq, hyq⟩ := GlobalTheory.T.lift_to_prime_localization (Xo'.XF c') Y.X Y.j R ξ ℂ_[p] χ yy hyy' q rfl
  have hfq : f ∉ q := by
    intro hf
    have h1 : φ (algebraMap R (Localization.Away f) f) = χ f := by
      rw [← RingHom.comp_apply, hφ]
    have h2 : χ f = 0 := RingHom.mem_ker.1 hf
    have hu : IsUnit (algebraMap R (Localization.Away f) f) := IsLocalization.Away.algebraMap_isUnit f
    exact (hu.map φ).ne_zero (h1.trans h2)
  let Rq := Localization.AtPrime q
  let hf' : Localization.Away f →+* Rq :=
    IsLocalization.Away.lift f (g := algebraMap R Rq) (IsLocalization.map_units Rq (⟨f, hfq⟩ : q.primeCompl))
  have hhf' : hf'.comp (algebraMap R (Localization.Away f)) = algebraMap R Rq := IsLocalization.Away.lift_comp _ _
  have hχu : ∀ s : q.primeCompl, IsUnit (χ s) := fun s => by
    refine IsUnit.mk0 _ fun h0 => s.2 ?_
    exact RingHom.mem_ker.2 h0
  let ψq : Rq →+* ℂ_[p] := IsLocalization.lift (M := q.primeCompl) hχu
  have hψq : ψq.comp (algebraMap R Rq) = χ := IsLocalization.lift_comp _
  have hKu : ∀ s : q.primeCompl, IsUnit (algebraMap R (FractionRing R) s) := fun s => by
    refine IsUnit.mk0 _ fun h0 => s.2 ?_
    have : (s : R) = 0 := (IsFractionRing.injective R (FractionRing R)) (by rw [h0, map_zero])
    rw [this]; exact q.zero_mem
  let ιK : Rq →+* FractionRing R := IsLocalization.lift (M := q.primeCompl) hKu
  have hιK : ιK.comp (algebraMap R Rq) = algebraMap R (FractionRing R) := IsLocalization.lift_comp _
  have hιinj : Function.Injective ιK := by
    rw [IsLocalization.lift_injective_iff]
    intro u v
    rw [(IsLocalization.injective Rq q.primeCompl_le_nonZeroDivisors).eq_iff,
      (IsFractionRing.injective R (FractionRing R)).eq_iff]
  have hK : spMap ιK ≫ yq = y := by
    rw [← cancel_mono Y.j, Category.assoc, ← hyq, sp_sp, hιK, hy]
  have hC : spMap ψq ≫ yq = yy := by
    rw [← cancel_mono Y.j, Category.assoc, ← hyq, sp_sp, hψq, hyy']
  have hgK : ιK.comp hf' = g := IsLocalization.ringHom_ext (Submonoid.powers f) (by
    rw [RingHom.comp_assoc, hhf', hιK, hg])
  have hgC : ψq.comp hf' = φ := IsLocalization.ringHom_ext (Submonoid.powers f) (by
    rw [RingHom.comp_assoc, hhf', hψq, hφ])
  have hwq : (spMap hf' ≫ wf.left) ≫ Y.t.G.hom = yq ≫ Y.j := by
    rw [Category.assoc, Over.w wf]
    change spMap hf' ≫ spMap (algebraMap R (Localization.Away f)) ≫ ξ = _
    rw [sp_sp, hhf', hyq]
  let wq : Over.mk (yq ≫ Y.j) ⟶ Y.t.G := GlobalTheory.HTMap.mkPt (spMap hf' ≫ wf.left) hwq
  have hwqt : wq ^ (p ^ n) = 1 := GlobalTheory.HTMap.tors_of (g := spMap hf') (w := wf) rfl hwf
  obtain ⟨σq, hσq, htq⟩ := GlobalTheory.T.exists_torsion_section_pullback _ _ Y.oF.t.G Y.t.G _ Y.m.cm.F Y.m.cart (Over.mk yq) wq
  have hσqt : σq ^ (p ^ n) = 1 := htq _ hwqt
  let P := GlobalTheory.Obj.toPolAV Y.oF
  have tu : ∀ {T : Scheme.{0}} (z : T ⟶ Xo'.XF c'), (toUnit (Over.mk z)).left = z := fun z => by
    simpa using Over.w (toUnit (Over.mk z))
  let eq : Over.mk yq ⟶ Y.oF.t.G := toUnit _ ≫ Y.oF.etaA a
  have heq : eq ^ (p ^ n) = 1 := by
    rw [← MonObj.comp_pow, ← hA, GlobalTheory.ArcExt.etaA_pow_eq_one, MonObj.comp_one]
  obtain ⟨cq, hcq, -⟩ := GlobalTheory.LevelCompare.weil_existsUnique P (p ^ n) eq σq heq hσqt
  obtain ⟨uq, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 cq

  let hKo : Over.mk y ⟶ Over.mk yq := Over.homMk (spMap ιK) hK
  have hN := (GlobalTheory.LevelCompare.weil_skew_natural P (p ^ n) (Over.mk yq)).2 (Over.mk y) hKo eq σq (unitOn uq) hcq
  have hKl : hKo.left = spMap ιK := rfl
  rw [hKl, GlobalTheory.Ex.Specialise.map_unitOn] at hN
  have t1 : (hKo ≫ eq) ^ (p ^ n) = 1 := by rw [← MonObj.comp_pow, heq, MonObj.comp_one]
  have t2 : (hKo ≫ σq) ^ (p ^ n) = 1 := by rw [← MonObj.comp_pow, hσqt, MonObj.comp_one]
  have hKe : (hKo ≫ eq).left = y ≫ (Y.oF.etaA a).left := by
    simp only [eq, Over.comp_left, tu, hKo, Over.homMk_left]
    rw [← Category.assoc, hK]
  have hKσ : (hKo ≫ σq).left ≫ Y.m.φ = spMap g ≫ wf.left := by
    rw [Over.comp_left, Category.assoc]
    change spMap ιK ≫ σq.left ≫ Y.m.cm.F = _
    rw [hσq]
    change spMap ιK ≫ spMap hf' ≫ wf.left = _
    rw [sp_sp, hgK]
  have hκK := hκ (hKo ≫ eq) (hKo ≫ σq) hKe t2
  rw [hKσ] at hκK
  have huK := (GlobalTheory.LevelCompare.weil_existsUnique P (p ^ n) (hKo ≫ eq) (hKo ≫ σq) t1 t2).unique hN hκK
  have huK' := GlobalTheory.Ex.Specialise.unitOn_bijective.1 huK
  set κK := κ (spMap g ≫ wf.left) with hκKdef
  have huq : uq = Units.map (algebraMap R Rq).toMonoidHom κK := by
    ext
    apply hιinj
    have := congrArg (fun u : (FractionRing R)ˣ => (u : FractionRing R)) huK'
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe] at this ⊢
    rw [this, ← RingHom.comp_apply, hιK]

  let hCo : Over.mk yy ⟶ Over.mk yq := Over.homMk (spMap ψq) hC
  have hN2 := (GlobalTheory.LevelCompare.weil_skew_natural P (p ^ n) (Over.mk yq)).2 (Over.mk yy) hCo eq σq (unitOn uq) hcq
  have hCl : hCo.left = spMap ψq := rfl
  rw [hCl, GlobalTheory.Ex.Specialise.map_unitOn] at hN2
  have hCe : hCo ≫ eq = e := by
    ext1
    simp only [eq, Over.comp_left, tu, hCo, Over.homMk_left]
    rw [← Category.assoc, hC, he]
  have hCσ : hCo ≫ σq = σ := by
    ext1
    refine Y.m.cart.1.hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc]
      change spMap ψq ≫ σq.left ≫ Y.m.cm.F = σ.left ≫ Y.m.φ
      rw [hσq, hσ]
      change spMap ψq ≫ spMap hf' ≫ wf.left = _
      rw [sp_sp, hgC]
    · rw [Over.w (hCo ≫ σq), Over.w σ]
  refine ⟨?_, ?_⟩
  · rw [← hCσ, ← MonObj.comp_pow, hσqt, MonObj.comp_one]
  · rw [← hCe, ← hCσ]
    have hval : Units.map (ψq : Rq →* ℂ_[p]) uq = Units.map χ.toMonoidHom κK := by
      rw [huq]
      ext
      simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
      rw [← RingHom.comp_apply, hψq]
    have hN3 : Out.WeilIs P.A P.L ((p ^ n : ℕ) : ℤ) (hCo ≫ eq) (hCo ≫ σq) (unitOn (Units.map χ.toMonoidHom κK)) := by
      rw [← hval]; exact hN2
    exact hN3

end GlobalTheory.WeilSpec
