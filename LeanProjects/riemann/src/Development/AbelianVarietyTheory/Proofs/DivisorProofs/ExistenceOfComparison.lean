import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniformisedChartAfterValuationRingExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcFamilyFourthConditionInvertiblePushforward

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem exists_ext_of_integral {A B O C : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [CommRing O] [Field C] [IsAlgClosed C] [Algebra O C] (v : Valuation C ℝ≥0) (hv : v.Integers O)
    (φ : A →+* B) (hφ : Function.Injective φ) (hint : φ.IsIntegral) (j0 : A →+* O)
    (hj0 : Function.Injective ((algebraMap O C).comp j0)) :
    ∃ j1 : B →+* O, j1.comp φ = j0 ∧ Function.Injective ((algebraMap O C).comp j1) := by
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra A O := j0.toAlgebra
  letI : Algebra A C := ((algebraMap O C).comp j0).toAlgebra
  haveI : IsScalarTower A O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral A B := ⟨hint⟩
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hφ
  haveI : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).2 hj0
  let ψ : B →ₐ[A] C := IsAlgClosed.lift
  have hmem : ∀ b : B, ∃ o : O, algebraMap O C o = ψ b := fun b => by
    have h1 : IsIntegral A (ψ b) := (Algebra.IsIntegral.isIntegral (R := A) b).map ψ
    have h2 : IsIntegral O (ψ b) := h1.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral h2)
  choose f hf using hmem
  have hinj := hv.hom_inj
  let j1 : B →+* O :=
    { toFun := f
      map_one' := hinj (by rw [hf, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [map_mul, hf, hf, hf, map_mul])
      map_zero' := hinj (by rw [hf, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [map_add, hf, hf, hf, map_add]) }
  have hcomp : j1.comp φ = j0 := by
    ext a
    apply hinj
    change algebraMap O C (f (algebraMap A B a)) = algebraMap A C a
    rw [hf, ψ.commutes]
  refine ⟨j1, hcomp, ?_⟩
  have hψ : (algebraMap O C).comp j1 = ψ.toRingHom := RingHom.ext fun b => hf b
  rw [hψ, RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := A) ?_
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  have : ψ.toRingHom.comp (algebraMap A B) = algebraMap A C := ψ.comp_algebraMap
  rw [this]
  exact hj0

theorem exSt_of_cmpSt : CmpSt → ExSt := by
  intro hC E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hpq _hA _hgood Z la p _ Xw hcov yb hyb
  obtain ⟨⟨T, kO, yT, hfin, hkO, hyT⟩, hXw⟩ := hyb
  obtain ⟨hover, -, -, -, hjr, -, -, -, -⟩ := hcov
  have hiO : Function.Injective (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := (PadicComplexInt.integers p).hom_inj

  have hgXw : Set.range (spMap (algebraMap T.V T.Fr) ≫ yT) ⊆ (Xw : Set Y.X) := by
    rintro _ ⟨s, rfl⟩
    obtain rfl : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr) := Subsingleton.elim (α := PrimeSpectrum T.Fr) _ _
    have h1 := bot_map (IsFractionRing.injective T.V T.Fr) yT
    have h2 := bot_map (φ := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO) (hiO.comp hkO) yT
    have h3 : (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ_[p]) ∈ (Xw : Set Y.X) :=
      hXw ⟨_, rfl⟩
    rw [← hyT, sp_sp, h2] at h3
    rw [h1]
    exact h3
  obtain ⟨yyT, hyyT⟩ := GlobalTheory.LN.ArcClause.exists_lift (c'.V W) Y _ (hgXw.trans hjr)
  obtain ⟨io', hio'⟩ : ∃ io' : c'.F →+* T.Fr, yyT ≫ pullback.snd _ _ = spMap io' :=
    ⟨(Spec.preimage (yyT ≫ pullback.snd _ _)).hom, (Spec.map_preimage (yyT ≫ pullback.snd _ _)).symm⟩
  let io : c.F →+* T.Fr := io'.comp (IntermediateField.inclusion hle).toRingHom
  have hrs : yyT ≫ r ≫ pullback.snd _ _ = spMap io := by
    rw [hover, ← Category.assoc, hio', spMap_spMap]
  let x : Sp T.Fr ⟶ Xo.X := yyT ≫ r ≫ pullback.fst _ _
  have hx : (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) := by
    letI := io.toAlgebra
    show (yyT ≫ r ≫ pullback.fst _ _) ≫ Xo.s = _
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc r, ← Category.assoc yyT, hrs, sOf,
      spMap_spMap]
  obtain ⟨T', i, rr, hrr, hv, hfin', y₀, hy₀⟩ := GlobalTheory.AnyLevelFrame.intFrExt E H Dw l Xo c hpq T io hfin x hx
  obtain ⟨φ, hφ, hloc⟩ := GlobalTheory.GoodChartExt.exists_local_restrict T T' i rr hrr hv
  have hφi : Function.Injective φ := by
    intro a b h
    apply i.injective.comp (IsFractionRing.injective T.V T.Fr)
    have ha := RingHom.congr_fun hφ a
    have hb := RingHom.congr_fun hφ b
    simp only [RingHom.comp_apply] at ha hb
    simp only [Function.comp_apply, ← ha, ← hb, h]
  have hfinφ : φ.Finite := GlobalTheory.CompHS.finite_of_finRes hfin' φ hφi
  obtain ⟨kO', hkO', hinj'⟩ := exists_ext_of_integral (Valued.v : Valuation ℂ_[p] ℝ≥0) (PadicComplexInt.integers p)
    φ hφi hfinφ.to_isIntegral kO (hiO.comp hkO)
  let k : T'.Fr →+* ℂ_[p] := IsFractionRing.lift hinj'
  have hk : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = k (algebraMap T'.V T'.Fr a) := fun a =>
    (IsFractionRing.lift_algebraMap hinj' a).symm
  letI := (i.comp io).toAlgebra
  letI : Algebra c.F ℂ_[p] := (k.comp (i.comp io)).toAlgebra
  letI := H.starRing
  let kA : T'.Fr →ₐ[c.F] ℂ_[p] := { k with commutes' := fun _ => rfl }
  obtain ⟨y, hy⟩ := GlobalTheory.CompHt.exists_isHTFrame (p := p) (v := (Valued.v : Valuation ℂ_[p] ℝ≥0)) (O := 𝓞_ℂ_[p])
    (fun _ => rfl) (PadicComplexInt.integers p) y₀ hfin' kA kO' hk
  have hcomm : spMap (algebraMap T'.V T'.Fr) ≫ (spMap φ ≫ yT) = (spMap i ≫ yyT) ≫ Y.j := by
    rw [sp_sp, hφ, ← sp_sp, Category.assoc, hyyT]
  have hpt : (spMap i ≫ yyT) ≫ r = spMap (RingHom.id T'.Fr) ≫ GlobalTheory.AllWt.ptF y₀.1 := by
    rw [show spMap (RingHom.id T'.Fr) = 𝟙 _ from Spec.map_id _, Category.id_comp]
    apply pullback.hom_ext
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_fst, hy₀, Category.assoc, Category.assoc]
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_snd, Category.assoc, Category.assoc, hrs, spMap_spMap]
  obtain ⟨P, π, ψ, h⟩ := hC E H Dw l l' Xo Xo' c c' W Y r ν hle hover p T' T' (RingHom.id _) (RingHom.id _)
    (fun _ => rfl) (i.comp io) y₀ kA y hy k kO' hk (fun _ => rfl) (spMap φ ≫ yT) (spMap i ≫ yyT) hcomm hpt
  rw [sp_sp, hkO', hyT] at h
  exact ⟨_, _, y, P, π, ψ, h⟩

end GlobalTheory.FlatModel

end
