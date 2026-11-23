import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumSectionValueCoeffEqFourierJacobi
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcNilpotent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterAnalyticVectorsIndependentBlockType
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TransvInOfHasPrinc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffEvREqFjAnLie
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjEqZeroIffOfSameExp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsEigAtIffOfIsDerivAt0

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.DerivativeDetermination

theorem linear_ext {T : Type} {g : ℕ} (e : Fin g ≃ T) {A B : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (h : ∀ t, A (Pi.single (e.symm t) 1) = B (Pi.single (e.symm t) 1)) : A = B := by
  refine (Pi.basisFun ℂ (Fin g)).ext fun j => ?_
  have := h (e j)
  rwa [Equiv.symm_apply_apply, ← Pi.basisFun_apply] at this

theorem exists_inverse_comb {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ)) (τ : T)
    (z : Fin (m τ) → Fin g → ℂ) (hz : LinearIndependent ℂ z) (ht : ∀ i j, z i j ≠ 0 → (e j).1 = τ) :
    ∃ X : Matrix (Fin (m τ)) (Fin (m τ)) ℂ, X.det ≠ 0 ∧
      ∀ i, ∑ k, X i k • z k = Pi.single (e.symm ⟨τ, i⟩) 1 := by
  classical
  let A : Matrix (Fin (m τ)) (Fin (m τ)) ℂ := Matrix.of fun k i => z k (e.symm ⟨τ, i⟩)
  have hcase : ∀ j, (∃ i, j = e.symm ⟨τ, i⟩) ∨ ∀ k, z k j = 0 := fun j => by
    by_cases h : (e j).1 = τ
    · subst h
      exact Or.inl ⟨(e j).2, (e.symm_apply_apply j).symm⟩
    · exact Or.inr fun k => by_contra fun h' => h (ht k j h')
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit, Fintype.linearIndependent_iff]
    intro c hc
    refine Fintype.linearIndependent_iff.1 hz c (funext fun j => ?_)
    rcases hcase j with ⟨i, rfl⟩ | h
    · simpa [A] using congrFun hc i
    · simp [h]
  have hd := (Matrix.isUnit_iff_isUnit_det A).1 hA
  refine ⟨A⁻¹, (Matrix.isUnit_nonsing_inv_det A hd).ne_zero, fun i => funext fun j => ?_⟩
  rcases hcase j with ⟨i', rfl⟩ | h
  · have := congrFun (congrFun (Matrix.nonsing_inv_mul A hd) i) i'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [Finset.sum_apply, Pi.single_apply]
    refine this.trans (if_congr ⟨fun h => by rw [h], fun h => ?_⟩ rfl rfl)
    exact (eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2).symm
  · rw [Finset.sum_apply, Finset.sum_eq_zero fun k _ => by rw [Pi.smul_apply, h, smul_zero]]
    by_contra hne
    obtain rfl : j = e.symm ⟨τ, i⟩ := by_contra fun h' => hne (by rw [Pi.single_eq_of_ne h'])
    have := congrFun (congrFun (Matrix.nonsing_inv_mul A hd) i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    exact zero_ne_one ((Finset.sum_eq_zero fun k _ => mul_eq_zero_of_right _ (h k)).symm.trans this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem ex_eq_of_deriv {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) {T : Type}
    (e : Fin g ≃ T) {i i' : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} {P' : (F.Di i').La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i') ty P') (hu : F.u i P = F.u i' P')
    (v : T → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
    (hv : ∀ t, IsDerivAt0 (fun z => (F.ex i P z).left) (Pi.single (e.symm t) 1) (v t))
    (hv' : ∀ t, IsDerivAt0 (fun z => (F.ex i' P' z).left) (Pi.single (e.symm t) 1) (v t)) (z : Fin g → ℂ) :
    (F.ex i P z).left = (F.ex i' P' z).left := by
  obtain rfl : i = i' := F.disj i i' P P' hP hP' hu
  obtain ⟨gam, h, h1, h2, h3, h4⟩ := (F.fibre i P P' hP hP').1 hu
  have hm : ∀ z, (LinearMap.toMatrix' h.toLinearMap).mulVec z = h z := fun z =>
    LinearMap.toMatrix'_mulVec _ z
  obtain ⟨-, -, h5⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo σ g ty F i P P' gam
    (LinearMap.toMatrix' h.toLinearMap) hP hP' h1 h2 h3 (fun a => by rw [hm, h4])
  simp only [hm] at h5
  obtain ⟨t1, -, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo σ g ty F i P' hP'
  have hid : h.toLinearMap = LinearMap.id := linear_ext e fun t =>
    (t3 _ (t1 _ _ (hv' t))).unique
      ((GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo σ g ty F i P hP i P' h.toLinearMap hP' h5 _ _).1 (hv t)) (hv' t)
  rw [← h5 z]
  exact congrArg (fun w => (F.ex i P' w).left) (LinearMap.congr_fun hid z)

theorem type_map {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    {i i' : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} {P' : (F.Di i').La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P)
    (hP' : IsPeriod (F.Di i') (fun j => relab c σ (e j).1) P') (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hL : ∀ z, (F.ex i' P' (L z)).left = (F.ex i P z).left) (τ : E →+* ℂ) (w : Fin g → ℂ)
    (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) : ∀ j, L w j ≠ 0 → (e j).1 = τ := by
  obtain ⟨v, hv, -⟩ := (GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F i P hP).2.1 w
  exact (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F i' P' hP' _ v τ
    ((GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F i P hP i' P' L hP' hL _ _).1 hv)).1
    ((GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F i P hP _ v τ hv).2 hw)

open GlobalTheory.ArcId in
set_option maxHeartbeats 1000000 in

theorem exists_cfOf_ne_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (em : K₁ →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Std d → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → Comparison₂ Uw d.a em s.ξ k ξ' x → ∀ F ∈ sec Xo c a' n, (∀ k', (U.X k').IsBddSec (laU U a' n k') (rdU U F k')) → (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 s.ν₀).re) (rdU U F k) x ≠ 0 → ∃ mo : ArcLt Dw →₀ ℕ, cfOf d.yF mo d.jj F ≠ 0 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s em _ _ r U Uw k ξ' x a' n hstd hgood hunf hprinc hdom hχ hiso hx
    htie F hF hbdd hfj
  have h1 := hK.laws
  have h2 := hK.laws2
  have hev := hK.ev E H Dw l Xo c
  obtain ⟨hover, ⟨y₀, hy₀, hc⟩, hpush⟩ := hstd
  obtain ⟨aC, p, ξC, hp, hξC, htie⟩ := htie
  letI : Algebra c.F ℂ⸨X⸩ := (cstL.comp (em.comp (algebraMap c.F K₁))).toAlgebra
  have hth : ThNZ d.th := s.th_nz
  have hp' : InBC em (d.a.restrict (c.V d.Wp).subtype) (aC.restrict (c.V d.Wp).subtype) p := ⟨rfl, hp.2⟩
  obtain ⟨hW, hlet, htan, hthx, hnz⟩ := (GlobalTheory.ArcQBC.baseChanges h1 h2 hK.ubc hK.laws5 E H Dw l Xo c _ _ d.Y K₁ ℂ _
    (d.a.restrict (c.V d.Wp).subtype) em em.injective ((em.comp (algebraMap c.F K₁)).comp (c.V d.Wp).subtype) rfl).2
    (aC.restrict (c.V d.Wp).subtype) p hp'
  obtain ⟨W₁, hW₁⟩ := hW d.χ d.W
  choose e₁ he₁ using fun τ k => (hlet (d.e τ k)).exists
  obtain ⟨th₁, hth₁⟩ := (hthx d.th).exists
  have hover₁ : (spMap (PowerSeries.map em) ≫ d.χ) ≫ d.Y.s = spMap (PowerSeries.C (R := ℂ)) ≫
      spMap ((em.comp (algebraMap c.F K₁)).comp (c.V d.Wp).subtype) := by
    rw [Category.assoc, hover, sp_comp, sp_comp, sp_comp]
    congr 1
    exact RingHom.ext fun x => PowerSeries.map_C _ _
  obtain ⟨Ha⟩ := hK.n5 E H Dw l Xo c _ _ d.Y (em.comp (algebraMap c.F K₁)) (aC.restrict (c.V d.Wp).subtype) _ W₁ Uw.g _
    Uw.F hgood ((GlobalTheory.Relab.relab_good E H l c _ hgood).2.2.2 Dw Uw.g Uw.e) (GlobalTheory.ArcInTest.exists_values c d.Wp) hover₁
    (generic_mem d em)
  obtain ⟨w₁, sf, hs, L₀, t, t', hw₁, ht, ht', hL₀t, hu, hex⟩ := htie _ _ d.Y _ W₁ Ha
  let f : aC.D₀.X ≃ₗ[𝓞 E] d.a.D₀.X := { p.xe with map_smul' := hp.2.1 }
  have hξf : ξC = s.ξ.comp (f.toLinearMap.restrictScalars ℤ) := LinearMap.ext hξC
  obtain ⟨k', ξ'', sE, C, hiso', -, -, -, hC, -, hmain⟩ := GlobalTheory.ArcCoeffAt.coeff_evR_eq_fj_anLie h1 h2 E H Dw l Xo c _ r
    U Uw _ _ d.Y (aC.restrict (c.V d.Wp).subtype) _ W₁ Ha th₁ ξC s.ν₀ d.jj a' n hev hgood hunf (fun _ => rfl) hover₁
    (mono_spMap_subtype _) hpush (hnz _ _ hth₁ hth) (f.finrank_eq.trans s.rk)
    (fun h => s.ξ_ne (LinearMap.ext fun y => by
      obtain ⟨y, rfl⟩ := f.surjective y
      exact (hξC y).symm.trans (LinearMap.congr_fun h y)))
    (hξf ▸ betaAt_comp f s.ξ hp.2.2.1 s.beta) hdom
    (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc E H Dw l Xo c _ r U a' n hprinc hχ) w₁ hw₁
  obtain ⟨v₁, v₂, -, v₄⟩ := GlobalTheory.ExpTan.anVec_bijective h1.globalFns E H Dw l Xo c _ _ _ d.Y
    (aC.restrict (c.V d.Wp).subtype) _ W₁ _ _ Uw.F Ha
  choose z₁ hz₁ using fun τ i => (v₁ (e₁ τ i) (htan _ _ (he₁ τ i) (s.tan τ i))).exists
  have key : ∀ X : ArcLt Dw → ℂ, InvBl X → ∃ e₂ y, (∀ τ i, AnVec Ha (e₂ τ i) (∑ j, X ⟨τ, (i, j)⟩ • z₁ τ j)) ∧
      IsArcFr W₁ e₂ th₁ (HahnSeries.ofPowerSeries ℤ ℂ) y ∧ ajAt d em F X = (evR Xo c F y).coeff d.jj := fun X hX => by
    choose e₂ he₂ using fun (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) => (v₂ (∑ j, X ⟨τ, (i, j)⟩ • z₁ τ j)).exists
    obtain ⟨-, y, hy, hval⟩ := exists_frPt_at h1 h2 hev d em (fun _ => rfl) hy₀ hc hth hp' hW₁ he₁ hth₁
      (hnz _ _ hth₁ hth) hX (fun τ i => (v₄ _ _ _ _ _ (hz₁ τ)).2 (he₂ τ i)) a' n
    exact ⟨e₂, y, he₂, hy, by rw [hval F hF, map_one, one_pow, _root_.one_mul]⟩
  have hP := Ha.period w₁ hw₁
  have hQ := Uw.period k ⟨_, hs⟩
  have hzt : ∀ τ, LinearIndependent ℂ (z₁ τ) ∧ ∀ i j, z₁ τ i j ≠ 0 → (Uw.e j).1 = τ := by
    obtain ⟨e₂, y, he₂, hy, -⟩ := key (fun v => (1 : Matrix (Fin (Dw.mult v.1)) (Fin (Dw.mult v.1)) ℂ) v.2.1 v.2.2)
      fun τ => (Matrix.det_one (n := Fin (Dw.mult τ)) (R := ℂ)).trans_ne one_ne_zero
    refine GlobalTheory.ArcType.main h1 h2 E H Dw l Xo c _ r U Uw _ _ d.Y _ _ W₁ Ha y e₂ th₁ z₁ hgood (fun _ => rfl)
      (GlobalTheory.ThetaShiftProofs.mono_j d.Y (mono_spMap_subtype _)) hy fun τ i => ?_
    simpa [Matrix.one_apply] using he₂ τ i
  choose Xm hXd hXm using fun τ => exists_inverse_comb Uw.e τ (fun i => L₀ (z₁ τ i))
    ((hzt τ).1.map' L₀.toLinearMap L₀.ker) fun i => type_map Uw.e Uw.F hP hQ L₀.toLinearMap hex τ _ ((hzt τ).2 i)
  obtain ⟨e₂, y, he₂, hy, hval⟩ := key (fun v => Xm v.1 v.2.1 v.2.2) hXd
  obtain ⟨x', κ, L, gm, hlie, hgm, -, hLz, ⟨t₂, ht₂, ht₂'⟩, hκ, hco⟩ := hmain e₂ _ y hy he₂
  have hL₀z : ∀ τ i, L₀ (∑ j, Xm τ i j • z₁ τ j) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1 := fun τ i => by
    rw [← hXm τ i, map_sum]
    simp only [map_smul]
  have hLL : ∀ z, L z = L₀ z := fun z => by
    have := linear_ext Uw.e (A := L.toLinearMap ∘ₗ L₀.symm.toLinearMap) (B := LinearMap.id) fun t => by
      change L (L₀.symm _) = Pi.single _ _
      rw [← hL₀z t.1 t.2, L₀.symm_apply_apply, hL₀z]
      exact hLz t.1 t.2
    simpa using LinearMap.congr_fun this (L₀ z)
  obtain ⟨-, -, -, -, -, -, huniq⟩ := GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c _ _ _ d.Y _ _ W₁ _ _ Uw.F Ha
  obtain rfl : t₂ = t := (huniq ξC).unique ht₂ ht
  have hu' : Uw.F.u (Uw.ik k) (Uw.Pm k ⟨_, hs⟩) = Uw.F.u (Uw.ik k') (Uw.Pm k' x') :=
    hu.symm.trans (hlie.1.symm.trans (Uw.lie k' x').1)
  have hex' := ex_eq_of_deriv Uw.F Uw.e hQ (Uw.period k' x') hu' (fun t => (U.un k' x').u t.1 t.2)
    (fun t => hL₀z t.1 t.2 ▸ (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ Uw.F _ _ hP _ _ L₀.toLinearMap hQ hex
      _ _).1 (hlie.2 t.1 t.2)) (fun t => (Uw.lie k' x').2 t.1 t.2)
  have hm := GlobalTheory.FrameMatch.fj_eq_zero_iff_of_same_exp hK E H Dw l Xo c _ r U Uw k k' ⟨_, hs⟩ x' t' (gm t₂) a' n s.ν₀ hgood hunf hprinc hdom hχ
    (ht' ▸ hiso) hu' hex' (by rw [hL₀t, hgm, hLL]) F hF
  rw [ht', ht₂', GlobalTheory.FjCauchy.fj_flow _ (hbdd k) hiso _ hx _ hs] at hm
  have hκ0 : κ ≠ 0 := norm_pos_iff.1 (by
    rw [hκ]
    exact mul_pos (Real.rpow_pos_of_pos (mul_pos hC (Finset.prod_pos fun τ _ =>
      inv_pos.2 (GlobalTheory.FjCauchy.tt_pos _ hiso' x'.2 τ))) _) (BoundedSectionAlgebra.nfac_pos _ x'.2 _))
  have hne := mul_ne_zero hκ0 (mt hm.2 (mul_ne_zero (Complex.exp_ne_zero _) hfj))
  rw [← hco F hF (hbdd k'), ← hval] at hne
  obtain ⟨mo, -, hmo⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hne)
  exact ⟨mo, fun h => left_ne_zero_of_mul hmo ((congrArg em h).trans (map_zero em))⟩

end GlobalTheory.DerivativeDetermination
