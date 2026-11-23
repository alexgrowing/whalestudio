import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFramesDifferByUnit
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
open ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace GlobalTheory.PtDeg.FrameEig

theorem dualMapR_epsScaleR {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (a : R) :
    spMap (Chart.dualMapR f) ≫ spMap (epsScaleR a) = spMap (epsMul (f a)) ≫ spMap (Chart.dualMapR f) := by
  rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
  congr 1
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, epsScaleR, Chart.dualMapR, mul_comm]

theorem epsScaleR_epsMul_comm {R : Type} [CommRing R] (a b : R) :
    spMap (epsScaleR a) ≫ spMap (epsMul b) = spMap (epsMul b) ≫ spMap (epsScaleR a) := by
  rw [GlobalTheory.IntLie.spMap_comp₂, GlobalTheory.IntLie.spMap_comp₂]
  congr 1
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, epsScaleR, mul_left_comm]

theorem scale_eig {R : Type} [CommRing R] {X : Scheme.{0}} (a b : R) (x : Sp (DualNumber R) ⟶ X) (g : X ⟶ X)
    (h : x ≫ g = spMap (epsMul b) ≫ x) :
    (spMap (epsScaleR a) ≫ x) ≫ g = spMap (epsMul b) ≫ spMap (epsScaleR a) ≫ x := by
  rw [Category.assoc, h, ← Category.assoc, epsScaleR_epsMul_comm, Category.assoc]

theorem epsScaleR_eq_epsMul {R : Type} [CommRing R] (a : R) : epsScaleR a = epsMul a := rfl

theorem sc_left {R : Type} [CommRing R] {G : Over (Sp R)} (a : R) (v : epsR R ⟶ G) :
    (GlobalTheory.CM.IntCoord.sc a ≫ v).left = spMap (epsScaleR a) ≫ v.left := rfl

end GlobalTheory.PtDeg.FrameEig

open GlobalTheory.PtDeg.FrameEig in

theorem GlobalTheory.PtDeg.frameCoord_mem_span_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ j, u j ∈ Submodule.span K (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu j
  obtain ⟨u₀, w, h₁, h₂, hc⟩ := hu j
  have h₂' : u₀ ≫ m2.cm.F = w.left ≫ F.φ := h₂
  have h₁' : u₀ ≫ m1.cm.F = y.u ρ j := h₁

  have hbase : u₀ ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
    apply GlobalTheory.IntLie.spMap_frac_cancel (V := 𝓞 K)
    rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, h₂', Category.assoc]
    have e := F.fib.2.1.1.w
    erw [e]
    rw [← Category.assoc, Over.w w]
    rfl

  have hact0 : ∀ a : 𝓞 E, u₀ ≫ (t₀.act.act a).left = spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ u₀ := by
    intro a
    apply m1.cart.1.hom_ext
    · rw [Category.assoc, m1.act a, ← Category.assoc, h₁', y.eig ρ j a, htt a, Category.assoc, h₁']
    · rw [Category.assoc, Over.w (t₀.act.act a), hbase, Category.assoc, hbase, GlobalTheory.IntLie.spMap_comp₂,
        GlobalTheory.IntLie.epsMul_alg]

  have hw : ∀ a : 𝓞 E, w.left ≫ F.φ ≫ (B.t.act.act a).left =
      spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ w.left ≫ F.φ := by
    intro a
    rw [← reassoc_of% h₂', ← m2.act a, ← Category.assoc, hact0, Category.assoc, h₂']

  have hc' : u j ∈ Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K)) := by
    rw [(GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K B.pol F).2]; trivial
  obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ (u j) hc'
  rw [Submodule.span_eq, Submonoid.smul_def] at hd
  obtain ⟨-, -, -, -, hlat, heig⟩ := GlobalTheory.CM.integral_tangent_coordinates K B.pol F
  obtain ⟨U, hUt, w₁, hUv, hw₁⟩ := (hlat _).1 hd
  have := F.P₀.isAb.comm
  have hK := GlobalTheory.LieComb.lieComb_algebra K F.P₀.A _ F.v F.basis.1
  set dK : K := algebraMap (𝓞 K) K (d : 𝓞 K) with hdK
  have hw₁' : w₁ = GlobalTheory.CM.IntCoord.sc dK ≫ w := by
    have h3 := hK.2.2.1 1 ![u j] ![w] ![dK] _ (fun i => by fin_cases i; exact hc)
      ((GlobalTheory.CM.IntCoord.isLieComb_one_iff _ _ _).2 rfl)
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Matrix.cons_val_fin_one,
      Finset.sum_singleton] at h3
    rw [← algebraMap_smul K (d : 𝓞 K) (u j)] at hw₁
    exact (hK.1 _).unique hw₁ h3
  have hw₁e : ∀ a : 𝓞 E, w₁.left ≫ F.φ ≫ (B.t.act.act a).left =
      spMap (epsMul ((tt a : 𝓞 K) : K)) ≫ w₁.left ≫ F.φ := by
    intro a
    rw [hw₁', sc_left, Category.assoc, Category.assoc]
    have := scale_eig dK ((tt a : 𝓞 K) : K) (w.left ≫ F.φ) (B.t.act.act a).left (by rw [Category.assoc, hw a])
    simpa only [Category.assoc] using this

  have := B.pol.isAb.proper
  have hmem : (d : 𝓞 K) • u j ∈ F.eigLat B.t.act tt := by
    rw [heig]
    refine ⟨U, ⟨hUt, w₁, hUv, hw₁⟩, fun a => ?_⟩
    rw [GlobalTheory.CM.IntCoord.isLieComb_one_iff]
    have hv1 : IsVecOver (algebraMap (𝓞 K) K) F.φ (U ≫ B.t.act.act a)
        (GlobalTheory.CM.IntCoord.sc ((tt a : 𝓞 K) : K) ≫ w₁) := by
      unfold IsVecOver at hUv ⊢
      rw [sc_left, Over.comp_left, ← Category.assoc, ← hUv, Category.assoc, Category.assoc, hw₁e a,
        epsScaleR_eq_epsMul]
    have hv2 : IsVecOver (algebraMap (𝓞 K) K) F.φ (GlobalTheory.CM.IntCoord.sc (tt a) ≫ U)
        (GlobalTheory.CM.IntCoord.sc ((tt a : 𝓞 K) : K) ≫ w₁) := by
      unfold IsVecOver at hUv ⊢
      rw [sc_left, sc_left, Category.assoc, hUv, epsScaleR_eq_epsMul]
      have e := dualMapR_epsScaleR (algebraMap (𝓞 K) K) (tt a)
      exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ U.left) e).trans (Category.assoc _ _ _))).symm
    exact GlobalTheory.CM.IntCoord.eq_of_isVecOver (IsFractionRing.injective (𝓞 K) K) hv1 hv2

  have hd0 : dK ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.coe_ne_zero d)
  have h₃ := Submodule.smul_mem (Submodule.span K (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K))) dK⁻¹
    (Submodule.subset_span hmem)
  rwa [← algebraMap_smul K (d : 𝓞 K) (u j), ← hdK, inv_smul_smul₀ hd0] at h₃
