import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordinateSectionsOfWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierLogHeightFormula
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotIsBettiZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam.Descent

namespace GlobalTheory.DetHT.FlagNorm

theorem exists_place {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (σ : K' ≃+* K)
    (w : HeightOneSpectrum (𝓞 K)) : ∃ w' : HeightOneSpectrum (𝓞 K'), ∀ y, w'.valuation K' y = w.valuation K (σ y) := by
  let e := RingOfIntegers.mapRingEquiv σ
  let w' : HeightOneSpectrum (𝓞 K') := HeightOneSpectrum.comap (e : 𝓞 K' →+* 𝓞 K) e.surjective w
  have h : w'.asIdeal = w.asIdeal.comap e := rfl
  have hi : ∀ x, w'.intValuation x = w.intValuation (e x) := fun x => by
    refine GlobalTheory.QNorm.withZero_eq_of_le_exp_iff (w'.intValuation_le_one _) (w.intValuation_le_one _) ?_
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      h, ← Ideal.mem_comap, ← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]
  refine ⟨w', fun y => ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K') y
  have hc : ∀ x : 𝓞 K', σ (algebraMap (𝓞 K') K' x) = algebraMap (𝓞 K) K (e x) := fun x => rfl
  rw [map_div₀ σ, hc, hc, map_div₀, map_div₀]
  simp only [HeightOneSpectrum.valuation_of_algebraMap, hi]

theorem adicAbv_le_one_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    NumberField.HeightOneSpectrum.adicAbv K v x ≤ 1 ↔ v.valuation K x ≤ 1 := by
  rw [← WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v), ← NNReal.coe_le_coe]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem sum_lnStep {X : Scheme.{0}} (t : SAB H X) (p : ℕ) [Fact p.Prime] (x : Sp ℂ_[p] ⟶ X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (τ : Psi H) (a : ℕ → Bool) (ha : a p = true)
    (R : Option ℝ) :
    ∑ i : Fin (Dw.p + Dw.q), ((rootSym Dw a R τ.1 i).sum fun b n => (n : ℝ) * lnStep t x u p (b.1 p) b.2.2) =
      lnDet t p x u τ.1 - Dw.p * (vDiff E p * Real.log p) := by
  have hp : Dw.mult τ.1 = Dw.p := if_pos τ.2
  have hq : Dw.mult (conjEmb τ.1) = Dw.q := if_neg (conj_not_mem τ)
  rw [Fin.sum_univ_add, lnDet]
  have h1 : ∀ i : Fin Dw.p, ((rootSym Dw a R τ.1 (Fin.castAdd Dw.q i : Fin (Dw.p + Dw.q))).sum fun b n =>
      (n : ℝ) * lnStep t x u p (b.1 p) b.2.2) =
      Real.log (Pad.grNorm t x (latHT t p x) (u τ.1) (i.cast hp.symm)) - vDiff E p * Real.log p := fun i => by
    have hi : (i : ℕ) < Dw.mult τ.1 := by rw [hp]; exact i.2
    rw [rootSym, if_pos (by simp), Finsupp.sum_single_index (by simp)]
    simp only [lnStep, Fin.val_castAdd, dif_pos hi, ha, τ.2, and_self, if_true, Int.cast_one, one_mul, lat]
    rfl
  have h2 : ∀ j : Fin Dw.q, ((rootSym Dw a R τ.1 (Fin.natAdd Dw.p j : Fin (Dw.p + Dw.q))).sum fun b n =>
      (n : ℝ) * lnStep t x u p (b.1 p) b.2.2) =
      -Real.log (Pad.grNorm t x (latHT t p x) (u (conjEmb τ.1)) (j.rev.cast hq.symm)) := fun j => by
    have hj := j.2
    have e : Dw.p + Dw.q - 1 - (Dw.p + j) = Dw.q - (j + 1) := by omega
    have hi : Dw.q - (j + 1) < Dw.mult (conjEmb τ.1) := by rw [hq]; omega
    rw [rootSym, if_neg (by simp), Finsupp.sum_single_index (by simp)]
    simp only [lnStep, Fin.val_natAdd, e, dif_pos hi, ha, conj_not_mem τ, and_false, if_false, Int.cast_neg, Int.cast_one,
      neg_mul, one_mul, lat, sub_zero]
    rfl
  simp only [h1, h2, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← (finCongr hp.symm).sum_comp, ← (Fin.revPerm.trans (finCongr hq.symm)).sum_comp]
  simp only [finCongr_apply, Equiv.trans_apply, Fin.revPerm_apply]
  ring

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem exists_point {K k : Type} [Field K] [Field k] [Algebra F K] [Algebra c.F k] (y₀ : Y.Y.X)
    (sc : Y.Y.X.presheaf.stalk y₀ →+* K) (hy : spMap sc ≫ stalkPt Y.Y y₀ ≫ Y.Y.str = spMap (algebraMap F K)) (io : K →+* k)
    (hA : ∀ a, algebraMap c.F k a = io (algebraMap F K (e.symm a))) (hb : Y.π y₀ ∉ genBd Z)
    {φ : c.F →+* Y.Y.X.presheaf.stalk y₀} (fr : EigFrame Z φ (stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z))
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ}
    (h2 : fr.Tri (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) Y.f0 t)
    {ex : Ix Dw → ℤ} (hex : ex none = 0) {f : Rul Xo c} (hf : f ∈ secZ Xo c ex) (Zc : Formalism.L2.Pj.Comp Xo c)
    (hZ : letI := (constF e Y.Y).toAlgebra; GlobalTheory.AllWt.LiesOn Zc Y.y0) :
    ∃ (P : FrPt Xo c k) (z : Sp K ⟶ Xo.XF c) (r : Y.Y.X.presheaf.stalk y₀),
      GlobalTheory.AllWt.ptF P = spMap io ≫ z ∧ GlobalTheory.AllWt.LiesOn Zc P ∧
      GlobalTheory.AllWt.ptF P ≫ Z.j = spMap (io.comp sc) ≫ stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z ∧
      ((frameOf Z P).v = fun τ i => spMap (dualMap (io.comp sc)) ≫ fr.v τ i) ∧
      algebraMap _ Y.Y.X.functionField r = Y.val f * ((∏ z : Letter Dw, t z.1 z.2 ^ (-ex (some z)) : Y.Y.Fnˣ) : Y.Y.Fn) ∧
      evR Xo c f P = io (sc r) := by
  classical
  have hopen : Y.π y₀ ∈ Set.range Z.jQ := not_not.1 hb
  have hgen : spMap (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) ≫ stalkPt Y.Y y₀ = genericPt Y.Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Y.Y.X).specializes trivial)
  letI : Algebra c.F (Y.Y.X.presheaf.stalk y₀) := φ.toAlgebra
  letI : Algebra c.F Y.Y.X.functionField := (constF e Y.Y).toAlgebra
  haveI := Z.jQ_open
  have hr : Set.range (stalkPt Y.Y y₀ ≫ Y.π) ⊆ Set.range Z.jQ := by
    rintro _ ⟨q, rfl⟩
    have h1 : stalkPt Y.Y y₀ q ⤳ y₀ := by
      have : stalkPt Y.Y y₀ q ∈ Set.range (Y.Y.X.fromSpecStalk y₀) := ⟨q, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    exact (h1.map Y.π.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range hopen
  let xF := IsOpenImmersion.lift Z.jQ _ hr
  have hxF : xF ≫ Z.jQ = stalkPt Y.Y y₀ ≫ Y.π := IsOpenImmersion.lift_fac _ _ _
  have hpt0 : GlobalTheory.AllWt.ptF Y.y0 = spMap (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, ← Category.assoc, hgen]
    exact Y.y0_x
  have hc : constF e Y.Y = (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField).comp φ := h2.2.1
  have hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F (Y.Y.X.presheaf.stalk y₀)) := by
    obtain ⟨φ₂, h⟩ := Spec.map_surjective (xF ≫ pullback.snd _ _)
    have k1 : spMap (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) ≫ spMap φ₂.hom =
        spMap (constF e Y.Y) := by
      have h0 : GlobalTheory.AllWt.ptF Y.y0 ≫ pullback.snd _ _ = spMap (constF e Y.Y) := pullback.lift_snd _ _ _
      rw [← h0, hpt0, Category.assoc, ← h]
      rfl
    rw [sp_comp] at k1
    have k2 := sp_inj k1
    have k3 : φ₂.hom = φ := RingHom.ext fun r =>
      IsFractionRing.injective (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField
        ((RingHom.congr_fun k2 r).trans (RingHom.congr_fun hc r))
    rw [← h]
    exact congrArg spMap k3
  have hxj : xF ≫ Z.j = stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z := by
    show xF ≫ Z.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, hxF, Category.assoc]
  obtain ⟨P', hP', htie⟩ := exists_tie_point (Z := Z) hs hxj rfl fr
  have tie0 : Comparison₂ Y.y0 Y.f0 := ⟨rfl, by
    show _ ≫ Z.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, Y.y0_x, Category.assoc], Y.flagComponentFramedPoint_frame⟩
  let ι₀ : Y.Y.X.presheaf.stalk y₀ →ₐ[c.F] Y.Y.X.functionField :=
    { algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField with
      commutes' := fun r => (RingHom.congr_fun hc r).symm }
  have hx1 : Y.y0.x = spMap ι₀.toRingHom ≫ P'.x := by
    rw [← Descent.ptF_fst Y.y0, ← Descent.ptF_fst P', hpt0, hP', Category.assoc]
  obtain ⟨u, hu, hu'⟩ := Comparison₂.bm_of_tri htie tie0 (ψ := ι₀) hx1 h2
  have e1 := BM.evR hu hf
  have hK : (sc.comp φ).comp e.toRingHom = algebraMap F K := by
    apply sp_inj
    rw [← sp_comp, ← sp_comp, ← hy, ← Y.π_str, Category.assoc, ← Category.assoc (stalkPt _ _), ← hxF,
      Category.assoc, ← Category.assoc Z.jQ, Z.jQ_over, ← Category.assoc xF, hs]
  let ψa : Y.Y.X.presheaf.stalk y₀ →ₐ[c.F] k :=
    { io.comp sc with
      commutes' := fun r => by
        rw [hA, ← hK]
        show io (sc (φ r)) = io (sc (φ (e (e.symm r))))
        rw [e.apply_symm_apply] }
  obtain ⟨P, hP⟩ := GlobalTheory.FlagTan.exists_frMap ψa P'
  have hpt : GlobalTheory.AllWt.ptF P = spMap (io.comp sc) ≫ xF := by rw [Descent.ptF_map hP.1, hP']
  refine ⟨P, spMap sc ≫ xF, evR Xo c f P', by rw [hpt, ← Category.assoc, sp_comp], fun s => ?_,
    by rw [hpt, Category.assoc, hxj], ?_, ?_, GlobalTheory.FlagTan.evR_frMap hf.1 hP⟩
  · let s₀ : Sp Y.Y.X.functionField := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Y.Y.X.functionField)
    have h0 := hZ s₀
    rw [hpt0, Scheme.Hom.comp_apply] at h0
    rw [hpt, Scheme.Hom.comp_apply]
    have hsp : spMap (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) s₀ ⤳ spMap (io.comp sc) s := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
      intro a ha
      have h3 : algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField a = 0 := ha
      rw [(map_eq_zero_iff _ (IsFractionRing.injective (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField)).1 h3]
      exact zero_mem _
    exact (hsp.map xF.continuous).mem_closed (isClosed_of_mem_irreducibleComponents _ Zc.2) h0
  · funext τ i
    have k1 := (htie.2.2 τ i).map (io.comp sc)
    rw [hP', ← hpt] at k1
    obtain ⟨w, a1, a2, a3⟩ := k1
    obtain ⟨w', b1, b2, b3⟩ := (tie_frameOf Z P).2.2 τ i
    rw [hP.2.1] at b2
    rw [← a3, ← b3, Z.m0.toSABMap.cart.1.hom_ext (a2.trans b2.symm) (a1.trans b1.symm)]
  · have hchi : GlobalTheory.ShFam.Descent.chi ex u = ∏ z : Letter Dw, t z.1 z.2 ^ ex (some z) := by
      simp only [GlobalTheory.ShFam.Descent.chi, Fintype.prod_option, hex, zpow_zero, one_mul]
      exact Finset.prod_congr rfl fun z _ => by rw [← hu' z.1 z.2]
    have E1 : Y.val f = ((∏ z : Letter Dw, t z.1 z.2 ^ ex (some z) : Y.Y.Fnˣ) : Y.Y.Fn) *
        algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField (evR Xo c f P') := by
      rw [← hchi]
      exact e1
    have pn : (∏ z : Letter Dw, t z.1 z.2 ^ (-ex (some z))) = (∏ z : Letter Dw, t z.1 z.2 ^ ex (some z))⁻¹ := by
      simp only [zpow_neg, Finset.prod_inv_distrib]
    rw [E1, pn, mul_right_comm, Units.mul_inv, one_mul]

theorem log_quot {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (y : Sp K ⟶ X) (w : AbsoluteValue K ℝ)
    {ι : Type} [Fintype ι] (T G : ι → X.functionFieldˣ)
    (hu : ∀ i, UnitAt (below y) ((T i * G i : X.functionFieldˣ) : X.functionField)) (g : X.functionField)
    (r : X.presheaf.stalk (below y)) (hr0 : (Scheme.stalkClosedPointTo y).hom r ≠ 0)
    (hr : algebraMap _ X.functionField r = g * ((∏ i, T i : X.functionFieldˣ) : X.functionField)) :
    UnitAt (below y) (g / ∏ i, (G i : X.functionField)) ∧
      Real.log (w (TrueGeo.valAt y (g / ∏ i, (G i : X.functionField)))) +
        ∑ i, Real.log (w (TrueGeo.valAt y ((T i * G i : X.functionFieldˣ) : X.functionField))) =
      Real.log (w ((Scheme.stalkClosedPointTo y).hom r)) := by
  obtain ⟨Us, hs⟩ := GlobalTheory.CovolFin.log_valAt_prod y w Finset.univ _ fun i _ => hu i
  have hru : IsUnit r := (isUnit_map_iff (Scheme.stalkClosedPointTo y).hom r).1 (isUnit_iff_ne_zero.2 hr0)
  have Ur : UnitAt (below y) (algebraMap _ X.functionField r) := ⟨r, hru, rfl⟩
  have hq : g / ∏ i, (G i : X.functionField) =
      algebraMap _ X.functionField r * ((∏ i, (T i * G i) : X.functionFieldˣ) : X.functionField)⁻¹ := by
    rw [hr, Finset.prod_mul_distrib, Units.val_mul, mul_inv, ← mul_assoc,
      mul_inv_cancel_right₀ (Units.ne_zero _), div_eq_mul_inv, Units.coe_prod]
  rw [hq]
  refine ⟨Ur.mul Us.inv, ?_⟩
  rw [SmallSec.valAt_mul Ur.regAt Us.inv.regAt, GlobalTheory.LineNorm.Neg.valAt_inv Us, map_mul, map_inv₀,
    Real.log_mul (w.pos (SmallSec.valAt_ne_zero Ur)).ne' (inv_ne_zero (w.pos (SmallSec.valAt_ne_zero Us)).ne'),
    Real.log_inv, hs, Base.valAt_stalk]
  ring

theorem prod_flat {G : Type} [CommGroup G] (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → G) (τ : Psi H) (a : ℕ → Bool)
    (R : Option ℝ) : (∏ x : Letter Dw, t x.1 x.2 ^ (-exOf Dw (flatWt Dw τ) 0 (some x))) =
      ∏ i : Fin (Dw.p + Dw.q), ∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (rootSym Dw a R τ.1 i) x := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [← GlobalTheory.CovolFin.zpow_finsum, ← congrFun (expo_detSym_eq Dw τ a R) x, detSym, GlobalTheory.CovolFin.expo_sum,
    Finset.sum_apply, Finset.sum_range]

theorem lgOf_eq (w : Pad.Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime) (ε : TrueGeo.Ext v)
    (y : TrueGeo.AlgPt Y.Y) : haveI := Fact.mk hp
    lgOf Y w v ε y = Real.log (ε.w (TrueGeo.valAt y.1 (((∏ x : Letter Dw,
        (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose x.1 x.2 ^ expo Dw w x) *
        (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) * w.sum fun b n => (n : ℝ) * lnStep Z.t
          (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
          (fun τ i => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫
            (Y.gr_spec (below y.1)).choose_spec.choose.v τ i) (resP v) (b.1 (resP v)) b.2.2 :=
  dif_pos hp

theorem sum_lgOf (τ : Psi H) (a : ℕ → Bool) (R : Option ℝ) (v : HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime)
    (ha : a (resP v) = true) (ε : TrueGeo.Ext v) (y : TrueGeo.AlgPt Y.Y) : haveI := Fact.mk hp
    ∑ i : Fin (Dw.p + Dw.q), lgOf Y (rootSym Dw a R τ.1 i) v ε y =
      ∑ i : Fin (Dw.p + Dw.q), Real.log (ε.w (TrueGeo.valAt y.1 (((∏ x : Letter Dw,
        (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose x.1 x.2 ^ expo Dw (rootSym Dw a R τ.1 i) x) *
        (eqn (divOf Y (expo Dw (rootSym Dw a R τ.1 i))) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        (lnDet Z.t (resP v)
          (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
          (fun τ i => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫
            (Y.gr_spec (below y.1)).choose_spec.choose.v τ i) τ.1 - Dw.p * (vDiff E (resP v) * Real.log (resP v))) := by
  letI := Fact.mk hp
  rw [← sum_lnStep _ _ _ _ τ a ha R, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => lgOf_eq Y _ v hp ε y

theorem exists_coord {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} (Y : FlagCpt Z e) (Zc : Formalism.L2.Pj.Comp Xo c) (τ : Psi H)
    {f : Rul Xo c} (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (hZ : letI := (constF e Y.Y).toAlgebra; GlobalTheory.AllWt.LiesOn Zc Y.y0) (hD : DetConst Z Zc τ.1 f)
    (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) [Fact p.Prime] : ∃ ρ : ℝ, ∀ (io : AlgebraicClosure F →+* ℂ_[p]),
      (∀ b, ‖io (algebraMap F (AlgebraicClosure F) (e.symm b))‖ ≤ 1 ↔ la.valuation c.F b ≤ 1) →
      ∀ y : TrueGeo.AlgPt Y.Y, Y.π (below y.1) ∉ genBd Z → ∃ r : Y.Y.X.presheaf.stalk (below y.1),
        (Scheme.stalkClosedPointTo y.1).hom r ≠ 0 ∧
        algebraMap _ Y.Y.X.functionField r = Y.val f * ((∏ x : Letter Dw,
          (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose x.1 x.2 ^ (-exOf Dw (flatWt Dw τ) 0 (some x)) :
            Y.Y.Fnˣ) : Y.Y.Fn) ∧
        Real.log ‖io ((Scheme.stalkClosedPointTo y.1).hom r)‖ + lnDet Z.t p
          (spMap (io.comp (Scheme.stalkClosedPointTo y.1).hom) ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
          (fun τ i => spMap (dualMap (io.comp (Scheme.stalkClosedPointTo y.1).hom)) ≫
            (Y.gr_spec (below y.1)).choose_spec.choose.v τ i) τ.1 = ρ := by
  obtain ⟨ρ₀, hρ⟩ := hD la p
  refine ⟨ρ₀, fun io hind y hb => ?_⟩
  letI : Algebra c.F ℂ_[p] := ((io.comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom).toAlgebra
  have hA : ∀ b, algebraMap c.F ℂ_[p] b = io (algebraMap F (AlgebraicClosure F) (e.symm b)) := fun _ => rfl
  have hsc : spMap (Scheme.stalkClosedPointTo y.1).hom ≫ stalkPt Y.Y (below y.1) = y.1 :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk y.1
  obtain ⟨P, z, r, p1, p2, p3, p4, p5, p6⟩ := exists_point Y (below y.1) (Scheme.stalkClosedPointTo y.1).hom
    (by rw [← Category.assoc, hsc, y.2]) io hA hb _
    (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose_spec.1 (ex := exOf Dw (flatWt Dw τ) 0) rfl hf Zc hZ
  have halg : IsAlgFr P := by
    haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure F) := Algebra.IsAlgebraic.trans ℚ F _
    exact ⟨AlgebraicClosure F, inferInstance, io, z, fun b =>
      (IsFractionRing.isAlgebraic_iff ℤ ℚ _).2 (Algebra.IsAlgebraic.isAlgebraic b), p1⟩
  obtain ⟨hne, hval⟩ := hρ hind P halg p2
  rw [p4, p3, p6] at hval
  rw [p6] at hne
  exact ⟨r, fun h => hne (by rw [h, map_zero]), p5, hval⟩

theorem real_step {A B κ L D d ρ : ℝ} (h₁ : A + B = κ * L) (h₂ : L + D = ρ) : A + (B + κ * (D - d)) = κ * (ρ - d) := by
  rw [← h₂, ← add_assoc, h₁]
  ring

theorem flagSt_holds : FlagSt := by
  intro E _ _ _ H Dw l Xo c Z F _ _ e Y Zc τ f hf hZ hD N hN a R v ha
  subst hN
  have hp := residueCharacteristic_prime v
  letI := Fact.mk hp
  obtain ⟨la, hla⟩ := exists_place e.symm v
  obtain ⟨ρ₀, hρ⟩ := exists_coord Y Zc τ hf hZ hD la (resP v)
  refine ⟨(-Real.log (NumberField.HeightOneSpectrum.adicAbv F v (resP v)) / Real.log (resP v)) *
    (ρ₀ - Dw.p * (vDiff E (resP v) * Real.log (resP v))), fun ε y hb => ?_⟩
  have hio := ioOf_le_one_iff (resP v) (residueCharacteristic_mem v) ε
  have hκ : NumberField.HeightOneSpectrum.adicAbv F v (resP v) = ε.w (resP v) := by rw [← ε.w_alg, map_natCast]
  obtain ⟨r, hr0, hr, hval⟩ := hρ (ioOf (resP v) ε)
    (fun b => (hio _).trans (by rw [ε.mem_O, ε.w_alg, adicAbv_le_one_iff, hla])) y hb
  rw [prod_flat _ τ a R] at hr
  obtain ⟨U, hU⟩ := log_quot y.1 ε.w _ _
    (fun i : Fin (Dw.p + Dw.q) => GlobalTheory.CombInd.Tens.unitAt_prod Y (rootSym Dw a R τ.1 i) (below y.1)) (Y.val f) r hr0 hr
  refine ⟨U, ?_⟩
  rw [sum_lgOf Y τ a R v hp ha ε y, hκ]
  exact real_step (hU.trans (log_w_eq (resP v) ε _ hio _)) hval

end GlobalTheory.DetHT.FlagNorm

end
