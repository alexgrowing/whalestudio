import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSumsAtHalfCurveFraction
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqSpMapOfInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentConstantDirectionSpecialisesDerivStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTangentConstantCoordsGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelPointTangentVectorTransportIffStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcDeriv

open TrivSqZeroExt HolHom
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

theorem dual_inl (φ : R →+* R') (r : R) : dualMapR φ (inl r) = inl (φ r) := by
  ext <;> simp [dualMapR]

theorem dual_eps (φ : R →+* R') : dualMapR φ DualNumber.eps = DualNumber.eps := by
  ext <;> simp [dualMapR]

theorem snd_dual (φ : R →+* R') (a : DualNumber R) : (dualMapR φ a).snd = φ a.snd := by
  simp [dualMapR]

theorem fst_dual (φ : R →+* R') (a : DualNumber R) : (dualMapR φ a).fst = φ a.fst := by
  simp [dualMapR]

theorem dual_comp (φ : R →+* R') :
    (dualMapR φ).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp φ :=
  RingHom.ext fun a => dual_inl φ a

theorem dual_injective {φ : R →+* R'} (h : Function.Injective φ) : Function.Injective (dualMapR φ) := by
  intro a b e
  ext
  · exact h (by rw [← fst_dual, e, fst_dual])
  · exact h (by rw [← snd_dual, e, snd_dual])

theorem fst_alg {Z : Scheme.{0}} (y : Sp R ⟶ Z) :
    spMap (fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) ≫ y = y := by
  rw [← Category.assoc, ← Spec.map_comp]
  convert Category.id_comp y
  rw [← Spec.map_id]
  congr 1

theorem le_of_unit (ψ : R →+* ℂ) (hψ : ∀ a, ψ a ≠ 0 → IsUnit a) {Z : Scheme.{0}} (x : Sp R ⟶ Z) {U : Z.Opens}
    (hU : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  let p : PrimeSpectrum R := spMap ψ (default : PrimeSpectrum ℂ)
  have hp : p ∈ (show Set (PrimeSpectrum R) from (x ⁻¹ᵁ U).carrier) :=
    hU (x := (default : PrimeSpectrum ℂ)) trivial
  obtain ⟨_, ⟨r, rfl⟩, hr, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp (x ⁻¹ᵁ U).isOpen
  have hu : IsUnit r := hψ r fun h => hr (by
    change ψ r ∈ (default : PrimeSpectrum ℂ).asIdeal
    rw [h]; exact Ideal.zero_mem _)
  exact fun q _ => hle (a := q) fun hq => q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hu)

end Dual

section Core

variable {K F : Type} [CommRing K] [CommRing F] {GX GF Z : Scheme.{0}} {p : GF ⟶ GX} {q : GF ⟶ Sp F}
  {t : GX ⟶ Sp K} {κ : K →+* F}

theorem exists_lift (H : IsPullback p q t (spMap κ)) {A B : Type} [CommRing A] [CommRing B] (i : A →+* B)
    (hi : Function.Injective i) (x : Sp A ⟶ GX) (n : Sp B ⟶ GF) (ρ : F →+* A) (hx : spMap i ≫ x = n ≫ p)
    (hn : n ≫ q = spMap (i.comp ρ)) : ∃ x' : Sp A ⟶ GF, x' ≫ p = x ∧ x' ≫ q = spMap ρ ∧ spMap i ≫ x' = n := by
  have hover : x ≫ t = spMap ρ ≫ spMap κ := by
    rw [← spMap_comp]
    refine ArcPoint.eq_spMap_of_injective i hi _ _ ?_
    rw [reassoc_of% hx, H.w, reassoc_of% hn, ← spMap_comp, RingHom.comp_assoc]
  refine ⟨H.lift x _ hover, H.lift_fst _ _ _, H.lift_snd _ _ _, H.hom_ext ?_ ?_⟩
  · rw [Category.assoc, H.lift_fst, hx]
  · rw [Category.assoc, H.lift_snd, hn, spMap_comp]

theorem isDerivAt_of_fst (H : IsPullback p q t (spMap κ)) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {c : V → (Sp ℂ ⟶ GF)} {z w : V} {b : Sp ℂ ⟶ Sp F} (hc : ∀ s, c s ≫ q = b) (hol : HolAt (fun s => c s ≫ p) z)
    {v : Sp (DualNumber ℂ) ⟶ GF} (hv : IsDerivAt (fun s => c s ≫ p) z w (v ≫ p)) (hq : v ≫ q = constVec b) :
    IsDerivAt c z w v := by
  have e : (fun s => c s ≫ q) = fun _ => b := funext hc
  obtain ⟨u, hu⟩ := (holAt_of_isPullback H hol (e ▸ holAt_const b z)).exists_isDerivAt w
  have : v = u := H.hom_ext (hv.unique (hu.comp p)) (hq.trans ((isDerivAt_const b z w).unique (e ▸ hu.comp q)))
  exact this ▸ hu

theorem sumsAt_fderiv (H : IsPullback p q t (spMap κ)) (bF : F →+* ℂ) (φ : GF ⟶ Z) (U : Z.Opens) (f : Γ(Z, U))
    (Γ : Germs) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (z₀ : V) (n : Sp (DualNumber ℂ⸨X⸩) ⟶ GF)
    (hn : n ≫ q = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) ≫ spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF))
    (hU : ⊤ ≤ (n ≫ φ) ⁻¹ᵁ U) (S : ℂ⟦X⟧) (hS : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ S = snd (valR (n ≫ φ) U f))
    {T T₀ : ℝ} (o : Sp (Conv.halfRing T) ⟶ GX)
    (ho : spMap (Conv.halfRing T).val.toRingHom ≫ o = spMap (fstHom ℂ⸨X⸩ ℂ⸨X⸩ ℂ⸨X⸩).toRingHom ≫ n ≫ p)
    (e : ℂ → V → (Sp ℂ ⟶ GX))
    (he : ∀ (w : ℂ) (hw : T < w.im), T₀ < w.im → HolAt (e w) 0 ∧ e w 0 = spMap (Conv.ev T w hw).toRingHom ≫ o ∧
      ∃ ν : Sp (DualNumber (Γ.R w)) ⟶ GX, spMap (dualMapR (Γ.R w).val.toRingHom) ≫ ν = n ≫ p ∧
        IsDerivAt (e w) 0 z₀ (spMap (dualMapR (Γ.ev w).toRingHom) ≫ ν)) :
    ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∀ c : V → (Sp ℂ ⟶ GF), (∀ z, c z ≫ p = e w z ∧ c z ≫ q = spMap bF) →
      SumsAt S w (fderiv ℂ (fun z => valAt' (c z ≫ φ) U f) 0 z₀) := by
  obtain ⟨o', o1, o2, o3⟩ := exists_lift H (Conv.halfRing T).val.toRingHom Subtype.val_injective o
    (spMap (fstHom ℂ⸨X⸩ ℂ⸨X⸩ ℂ⸨X⸩).toRingHom ≫ n) ((algebraMap ℂ (Conv.halfRing T)).comp bF)
    (by rw [ho, Category.assoc]) (by rw [Category.assoc, hn, fst_alg]; rfl)
  obtain ⟨T₁, hT₁, h₁, -⟩ := Conv.exists_valAt'_halfCurve (yT := o' ≫ φ) (U := U) rfl (by
    intro x _
    have h1 : ⊤ ≤ (spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫
        spMap (Conv.halfIncl T : Conv.halfRing T →+* Conv.convLaurent) ≫ o' ≫ φ) ⁻¹ᵁ U := by
      rw [← Category.assoc, ← spMap_comp]
      erw [reassoc_of% o3]
      exact fun y _ => hU (x := spMap _ y) trivial
    obtain rfl : x = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
      Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
    exact h1 (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial)
  have key : ∀ w : ℂ, max T₀ T₁ < w.im → ∃ s : Γ.R w, (s : ℂ⸨X⸩) = algebraMap ℂ⟦X⟧ ℂ⸨X⸩ S ∧
      ∀ c : V → (Sp ℂ ⟶ GF), (∀ z, c z ≫ p = e w z ∧ c z ≫ q = spMap bF) →
        Γ.ev w s = fderiv ℂ (fun z => valAt' (c z ≫ φ) U f) 0 z₀ := by
    intro w hw
    have hw₁ : T₁ < w.im := (le_max_right _ _).trans_lt hw
    have hwT : T < w.im := hT₁.trans_lt hw₁
    obtain ⟨hol, e0, ν, ν1, ν2⟩ := he w hwT ((le_max_left _ _).trans_lt hw)
    obtain ⟨ν', a1, a2, a3⟩ := exists_lift H (dualMapR (Γ.R w).val.toRingHom) (dual_injective Subtype.val_injective)
      ν n ((algebraMap (Γ.R w) (DualNumber (Γ.R w))).comp ((algebraMap ℂ (Γ.R w)).comp bF)) ν1
      (by rw [hn, ← RingHom.comp_assoc, dual_comp, ← spMap_comp]; rfl)
    have hq : (spMap (dualMapR (Γ.ev w).toRingHom) ≫ ν') ≫ q = constVec (spMap bF) := by
      rw [Category.assoc, a2, ← spMap_comp, ← RingHom.comp_assoc, dual_comp, constVec, ← spMap_comp,
        RingHom.comp_assoc]
      congr 3
      exact RingHom.ext fun x => (Γ.ev w).commutes (bF x)
    have h0 : spMap (fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (dualMapR (Γ.ev w).toRingHom) ≫ ν' =
        spMap (Conv.ev T w hwT).toRingHom ≫ o' := by
      refine H.hom_ext ?_ ?_
      · simp only [Category.assoc]
        rw [a1, ν2.1, e0, o1]
      · rw [Category.assoc, hq, fst_constVec, Category.assoc, o2, ← spMap_comp]
        congr 2
        exact RingHom.ext fun x => ((Conv.ev T w hwT).commutes (bF x)).symm
    have hz : ⊤ ≤ (spMap (Conv.ev T w hwT).toRingHom ≫ o' ≫ φ) ⁻¹ᵁ U := by
      have := h₁ w hw₁
      rwa [Conv.halfCurve_eq _ hwT] at this
    have hν : ⊤ ≤ (ν' ≫ φ) ⁻¹ᵁ U := by
      refine le_of_unit ((fstHom ℂ ℂ ℂ).toRingHom.comp (dualMapR (Γ.ev w).toRingHom)) (fun a ha => ?_) _ ?_
      · exact isUnit_iff_isUnit_fst.2 (Γ.unit w _ fun h => ha ((fst_dual _ a).trans h))
      · rw [spMap_comp, Category.assoc, reassoc_of% h0]
        exact hz
    refine ⟨snd (valR (ν' ≫ φ) U f), ?_, fun c hc => ?_⟩
    · rw [hS, ← a3, Category.assoc, valR_spMap _ _ _ hν, snd_dual]
      rfl
    · have ec : (fun z => c z ≫ p) = e w := funext fun z => (hc z).1
      have hd := isDerivAt_of_fst H (fun z => (hc z).2) (ec ▸ hol) (w := z₀)
        (v := spMap (dualMapR (Γ.ev w).toRingHom) ≫ ν') (by rw [ec, Category.assoc, a1]; exact ν2) hq
      have := (hd.comp φ).2 U (by beta_reduce; rw [← hd.1, h0, Category.assoc]; exact hz) f
      rw [← this, Category.assoc, valR_spMap _ _ _ hν, snd_dual]
      rfl
  obtain ⟨T₂, h₂⟩ : ∃ T₂, algebraMap ℂ⟦X⟧ ℂ⸨X⸩ S ∈ Conv.halfRing T₂ := by
    obtain ⟨s, hs, -⟩ := key (((max T₀ T₁ + 1 : ℝ) : ℂ) * Complex.I) (by simp)
    obtain ⟨T₃, hw₃, a, b, hb, hab⟩ := Γ.frac _ s
    have hb0 : (b : ℂ⸨X⸩) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h, map_zero])
    rw [← Conv.mem_convLaurent_iff_halfRing, ← hs, ← (eq_inv_mul_iff_mul_eq₀ hb0).2 hab |>.symm]
    exact mul_mem (Conv.convLaurent.inv_mem (Conv.halfRing_le_convLaurent _ b.2))
      (Conv.halfRing_le_convLaurent _ a.2)
  refine ⟨max (max T₀ T₁) T₂, fun w hw c hc => ?_⟩
  have hw₂ : T₂ < w.im := (le_max_right _ _).trans_lt hw
  obtain ⟨s, hs, h⟩ := key w ((le_max_left _ _).trans_lt hw)
  rw [← h c hc, show s = Subalgebra.inclusion (Γ.le T₂ w hw₂) ⟨_, h₂⟩ from Subtype.ext hs, Γ.ev_eq]
  exact Conv.sumsAt_ev_of_eq hw₂ rfl

end Core

section Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {A : AnArc (𝓞 E)}

def IsTanPt {S : Scheme.{0}} {t : SAB H S} {y : Sp ℂ⸨X⸩ ⟶ S} (Φ : GenPts A t y) (z₀ : A.V)
    (n : Sp (DualNumber ℂ⸨X⸩) ⟶ t.G.left) : Prop :=
  ∃ ν, Φ.IsTan z₀ ν ∧ ν ≫ pullback.fst _ _ = n

theorem isTanPt_iff {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} {m : SABMap t' t f}
    {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} {y' : Sp ℂ⸨X⸩ ⟶ S'} {y : Sp ℂ⸨X⸩ ⟶ S} {Φ' : GenPts A t' y'}
    {Φ : GenPts A t y} (hw : w.IsGen) (h : GenPts.Rel m w Φ' Φ) (z₀ : A.V)
    {n : Sp (DualNumber ℂ⸨X⸩) ⟶ t'.G.left} (hn : n ≫ t'.G.hom = spMap (algebraMap ℂ⸨X⸩ _) ≫ y') :
    IsTanPt Φ' z₀ n ↔ IsTanPt Φ z₀ (n ≫ m.φ) := by
  have key := (T.arcLevelPoint_tangentVector_transport_iff E H S S' A t t' f m w y' y Φ' Φ hw h).2 z₀
  have hn' : (n ≫ m.φ) ≫ t.G.hom = spMap (algebraMap ℂ⸨X⸩ _) ≫ y := by
    rw [Category.assoc, m.cart.1.w, reassoc_of% hn, h.1]
  constructor
  · rintro ⟨ν, hν, rfl⟩
    exact ⟨pullback.lift _ _ hn', (key ν _ (by rw [pullback.lift_fst, Category.assoc]) (by rw [pullback.lift_snd, hν.1])).1 hν,
      pullback.lift_fst _ _ _⟩
  · rintro ⟨ν, hν, e⟩
    exact ⟨pullback.lift _ _ hn, (key _ ν (by rw [pullback.lift_fst_assoc, e]) (by rw [pullback.lift_snd, hν.1])).2 hν,
      pullback.lift_fst _ _ _⟩

end Move

theorem deriv_sumsAt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), AnFin Λ.A → C.Φ.Rational → ∀ (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR (PowerSeries ℂ) ⟶ W.t.G) (V : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, V)), DiffHyp W (fun z => Λ.ex0 (K.h.symm z)) z₀ ν v → ⊤ ≤ (v.left ≫ W.m.φ) ⁻¹ᵁ V → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∀ xF : (Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left), (∀ z, xF z ≫ Y.m0.toSABMap.φ = (Fu.ex K.i (K.Pw w) z).left ∧ xF z ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF) → SumsAt (TrivSqZeroExt.snd (valR (A := DualNumber (PowerSeries ℂ)) (v.left ≫ W.m.φ) V f)) w (fderiv ℂ (fun z => valAt' (xF z ≫ Y.m.φ) V f) 0 z₀) := by
  intro hL hL₂ E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ g ty Fu laA laM K hA hΦ z₀ ν v V f hd hV
  let ρ := dualMapR (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)
  have hW : (spMap ρ ≫ v.left) ≫ W.t.G.hom = spMap (algebraMap ℂ⸨X⸩ _) ≫ gen := by
    rw [Category.assoc, Over.w v]
    exact (spMap_comp _ _).symm.trans ((congrArg spMap (dual_comp _)).trans (spMap_comp _ _))
  have tW : IsTanPt C.ΦW (K.h.symm z₀) (spMap ρ ≫ v.left) :=
    ⟨pullback.lift _ _ hW, T.isTangent_constant_coords_generic_fibre hL hL₂ E H D l Xo c O β Y _ a χ W Λ C.Ξ C.ΦW g K.h z₀ ν v ρ _ C.isGen hd
      (dual_inl _) (dual_eps _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩
  have tY := (isTanPt_iff C.rig₂.1 C.rel₂ _ hW).1 tW
  have hY : ((spMap ρ ≫ v.left) ≫ W.m.φ) ≫ Y.t.G.hom = (spMap (algebraMap ℂ⸨X⸩ _) ≫ C.yF) ≫ Y.j := by
    rw [Category.assoc, W.m.cart.1.w, ← Category.assoc, hW, Category.assoc, Category.assoc, C.yF_j]
  obtain ⟨n, n1, n2⟩ : ∃ n : Sp (DualNumber ℂ⸨X⸩) ⟶ Y.oF.t.G.left, n ≫ Y.m.φ = (spMap ρ ≫ v.left) ≫ W.m.φ ∧
      n ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ⸨X⸩ _) ≫ C.yF :=
    ⟨Y.m.cart.1.lift _ _ hY, Y.m.cart.1.lift_fst _ _ _, Y.m.cart.1.lift_snd _ _ _⟩
  have tF := (isTanPt_iff C.rig₁.1 C.rel₁ _ n2).2 (n1 ▸ tY)
  obtain ⟨νU, tU, eU⟩ := (isTanPt_iff C.rig₀.1 C.rel₀ _ n2).1 tF
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  obtain ⟨T₀, -, h₀⟩ := T.tangent_constant_direction_specialises_deriv hL hL₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ Ψ hA hΦ _ νU tU
  have HP : IsPullback Y.m0.toSABMap.φ (Y.oF.t.G.hom ≫ pullback.snd _ _) (Xo.univ.t.G.hom ≫ Xo.s)
      (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    Y.m0.toSABMap.cart.1.paste_vert (IsPullback.of_hasPullback _ _)
  refine sumsAt_fderiv HP bF Y.m.φ V f Γ z₀ n (by rw [reassoc_of% n2, C.yF_over]) ?_ _ ?_ (T := Ψ.T)
    (T₀ := max T₀ K.T) (Ψ.yT ≫ eSec Xo.univ.t.G) ?_ (fun w z => (Fu.ex K.i (K.Pw w) z).left) fun w hw hw' => ?_
  · rw [n1, Category.assoc]
    exact fun x _ => hV (x := spMap ρ x) trivial
  · rw [n1, Category.assoc, valR_spMap _ _ _ hV, snd_dual]
  · rw [← eU, reassoc_of% tU.2.1, fib, pullback.lift_fst, map_zero_eq_one C.Φ.add, reassoc_of% Ψ.yT_gen]
    rfl
  have hK : K.T < w.im := (le_max_right _ _).trans_lt hw'
  have hP := K.period w hK
  obtain ⟨νt, -, b1, b2⟩ := h₀ w hw ((le_max_left _ _).trans_lt hw')
  obtain ⟨b2, b3⟩ := b2 (dualMapR (Γ.ev w).toRingHom) (dual_inl _) (dual_eps _)
  have ex : ∀ z, (Fu.ex K.i (K.Pw w) z).left = (Ψ.pi w (K.h.symm z)).left := fun z => by
    rw [← K.ex_eq w hK, K.h.apply_symm_apply]
  refine ⟨holAt_of_isHolTo (isHolTo_ex Fu K.i hP) trivial, ?_, νt, (b1 _ (dual_inl _) (dual_eps _)).trans eU, ?_,
    fun U hU k => ?_⟩
  · rw [map_zero_eq_one (Fu.ex_add K.i _ hP), ← Category.assoc, ← Ψ.yw_eq w hw, ← K.u_eq w hK]
    rfl
  · beta_reduce
    rw [b2, ex, map_zero]
  · simp only [ex, map_zero] at hU ⊢
    rw [b3 U k hU]
    have := K.h.symm.comp_right_fderiv (f := fun v => valAt' (Ψ.pi w v).left U k) (x := 0)
    rw [map_zero] at this
    exact (congrArg (· z₀) this).symm

end GlobalTheory.ArcDeriv
