import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem exists_isDef_lift_dualNumber : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {Q : FrPt Xo c K} (hz : z ≫ toFlag M = X.ptY Q) (zw : Sp (DualNumber K) ⟶ M.X) (hw : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ zw = z), ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧ zw ≫ toFlag M = X.ptY w := by
  intro E _ _ _ H Dw l Xo c Y X Z M K _ _ z ho Q hz zw hw
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hwU : ⊤ ≤ (zw ≫ M.σ) ⁻¹ᵁ U₀ X Z :=
    le_preimage_of_dualNumber (TrivSqZeroExt.fstHom K K K).toRingHom _ _ (by rw [← Category.assoc, hw]; exact hU)
  have hF : ⊤ ≤ (zw ≫ toFlag M) ⁻¹ᵁ flagOpen X := hwU
  have hr : Set.range (zw ≫ toFlag M) ⊆ Set.range X.inc := by
    rintro _ ⟨s, rfl⟩
    exact (opensRange_inc X).ge (hF (Set.mem_univ s))
  obtain ⟨w, hwi⟩ : ∃ w, w ≫ X.inc = zw ≫ toFlag M := ⟨_, IsOpenImmersion.lift_fac X.inc _ hr⟩
  have hred : spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ w = X.pt Q := by
    rw [← cancel_mono X.inc, Category.assoc, hwi, X.pt_inc, ← hz, ← Category.assoc]
    exact congrArg (· ≫ toFlag M) hw

  have hnil : IsNilpotent (RingHom.ker (GlobalTheory.FlagTan.red c K).toRingHom) := ⟨2, by
    rw [Ideal.zero_eq_bot, eq_bot_iff, pow_two]
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hb']⟩
  have hs : w ≫ pullback.snd _ _ ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) := by
    obtain ⟨φ, hφ⟩ : ∃ φ : c.F →+* DualNumber K, spMap φ = w ≫ pullback.snd _ _ ≫ pullback.snd _ _ :=
      ⟨(Spec.preimage (w ≫ pullback.snd _ _ ≫ pullback.snd _ _)).hom, by
        rw [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]⟩
    have h1 : spMap ((GlobalTheory.FlagTan.red c K).toRingHom.comp φ) = spMap (algebraMap c.F K) := by
      show Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom (GlobalTheory.FlagTan.red c K).toRingHom) = _
      rw [Spec.map_comp]
      change spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ spMap φ = _
      rw [hφ, ← Category.assoc, hred, ← Category.assoc, X.pt_snd, frX_snd]
    have h2 : (GlobalTheory.FlagTan.red c K).toRingHom.comp φ = algebraMap c.F K :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : Algebra.IsSeparable ℚ c.F := inferInstance
    haveI : Algebra.FormallyUnramified ℚ c.F := Algebra.FormallyUnramified.of_isSeparable ℚ c.F
    haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
    haveI : Algebra.FormallyUnramified ℤ c.F := Algebra.FormallyUnramified.comp ℤ ℚ c.F
    have h3 := Algebra.FormallyUnramified.ext' (R := ℤ) (A := c.F) (B := DualNumber K)
      (GlobalTheory.FlagTan.red c K).toRingHom hnil φ.toIntAlgHom (algebraMap c.F (DualNumber K)).toIntAlgHom
      (fun x => by
        show (GlobalTheory.FlagTan.red c K).toRingHom (φ x) =
          (GlobalTheory.FlagTan.red c K).toRingHom (algebraMap c.F (DualNumber K) x)
        exact (RingHom.congr_fun h2 x).trans ((GlobalTheory.FlagTan.red c K).commutes x).symm)
    rw [← hφ]
    exact congrArg spMap (congrArg AlgHom.toRingHom h3)
  obtain ⟨P', hP'⟩ := ((X.points (S := DualNumber K)).1 w).1 hs
  obtain ⟨P'', hP''⟩ := GlobalTheory.FlagMod.exists_frMap (GlobalTheory.FlagTan.red c K) P'
  have e1 : X.pt P'' = X.pt Q := by rw [← X.pt_frMap hP'', hP', hred]
  obtain ⟨t, ht⟩ := ((X.points (S := K)).2 P'' Q).1 e1
  obtain ⟨g, hgl, hgd, hc⟩ := (GlobalTheory.Frames.frBor_iff_frChg P'' Q t).1 ht
  have hdet : ∀ τ, IsUnit ((g τ).map (GlobalTheory.FlagTan.cst c K)).det := fun τ => by
    have h0 : IsUnit (g τ).det := by
      rw [Matrix.det_of_lowerTriangular (g τ) fun i j hij => hgl τ i j hij]
      exact IsUnit.prod_univ_iff.2 fun i => by rw [hgd]; exact Units.isUnit _
    have := h0.map (GlobalTheory.FlagTan.cst c K).toRingHom
    rwa [RingHom.map_det] at this
  obtain ⟨w', hW, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ P' (fun τ => (g τ).map (GlobalTheory.FlagTan.cst c K))
    (Units.map (GlobalTheory.FlagTan.cst c K).toRingHom.toMonoidHom (t none)) hdet
  have hdefQ : IsDef Q w' := by
    refine (GlobalTheory.FlagTan.frMap_iff_frChg hW hP'').2 ?_
    convert hc using 2 with τ
    · ext i j; simp
    · rfl
  have hB : FrBor (fun i => Units.map (GlobalTheory.FlagTan.cst c K).toRingHom.toMonoidHom (t i)) P' w' :=
    (GlobalTheory.Frames.frBor_iff_frChg P' w' _).2 ⟨fun τ => (g τ).map (GlobalTheory.FlagTan.cst c K),
      fun τ i j hij => by simp [hgl τ i j hij], fun τ i => by simp [hgd], hW⟩
  refine ⟨w', hdefQ, ?_⟩
  rw [← X.ptY_frBor hB, ← X.pt_inc, hP', hwi]

end GlobalTheory.CompHS
