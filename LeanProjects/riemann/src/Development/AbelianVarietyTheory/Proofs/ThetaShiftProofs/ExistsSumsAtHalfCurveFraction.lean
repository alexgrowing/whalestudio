import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallExistsLsumETwoPi
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

noncomputable section

open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom

namespace GlobalTheory.Conv

section Values

variable {A : Type} [CommRing A] {Z : Scheme.{0}}

theorem valR_id_top (a : A) :
    valR (𝟙 (Sp A)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = a := by
  rw [valR_eq _ _ le_top]
  have h : (𝟙 (Sp A) : Sp A ⟶ Sp A).appLE ⊤ ⊤ le_top = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    (((𝟙 (Sp A) : Sp A ⟶ Sp A).appLE ⊤ ⊤ le_top).hom _) = a
  rw [h]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply a

theorem valR_spMap_top {O : Type} [CommRing O] (β : O →+* A) (a : O) :
    valR (spMap β) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a) = β a := by
  have := valR_spMap β (𝟙 (Sp O)) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)
  rwa [Category.comp_id, valR_id_top] at this

theorem exists_point_of_ringHom {V : Z.Opens} (hV : IsAffineOpen V) (ψ : Γ(Z, V) →+* A) :
    ∃ x : Sp A ⟶ Z, ⊤ ≤ x ⁻¹ᵁ V ∧ ∀ f, valR x V f = ψ f := by
  let x₀ : Sp Γ(Z, V) ⟶ Z := hV.fromSpec
  have h₀ : ⊤ ≤ x₀ ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  refine ⟨spMap ψ ≫ x₀, fun p _ => h₀ (x := spMap ψ p) trivial, fun f => ?_⟩
  rw [valR_spMap ψ x₀ V h₀, valR_eq _ _ h₀]
  congr 1
  have h : hV.fromSpec.appLE V ⊤ h₀ = (Scheme.ΓSpecIso Γ(Z, V)).inv := by
    rw [Scheme.Hom.appLE, hV.fromSpec_app_self]
    simp [← Functor.map_comp]
  change (Scheme.ΓSpecIso Γ(Z, V)).hom.hom ((hV.fromSpec.appLE V ⊤ h₀).hom f) = f
  rw [h]
  exact (Scheme.ΓSpecIso Γ(Z, V)).inv_hom_id_apply f

end Values

variable {Z : Scheme.{0}}

theorem exists_halfRing_point {O : Type} [CommRing O] (s : Z ⟶ Sp O) [LocallyOfFiniteType s]
    (b : O →+* ℂ) (y : Sp convLaurent ⟶ Z)
    (hy : y ≫ s = spMap ((algebraMap ℂ convLaurent).comp b)) {V : Z.Opens} (hV : IsAffineOpen V)
    (hyV : ⊤ ≤ y ⁻¹ᵁ V) (T₀ : ℝ) :
    ∃ T ≥ T₀, ∃ yT : Sp (halfRing T) ⟶ Z, ⊤ ≤ yT ⁻¹ᵁ V ∧
      spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT = y ∧
      yT ≫ s = spMap ((algebraMap ℂ (halfRing T)).comp b) := by
  let ρ : O →+* Γ(Z, V) :=
    (s.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hρ : ρ.FiniteType := by
    refine (s.finiteType_appLE (isAffineOpen_top _) hV le_top).comp (RingHom.FiniteType.of_surjective _ ?_)
    exact (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.surjective
  have hval : ∀ {A : Type} [CommRing A] (x : Sp A ⟶ Z), ⊤ ≤ x ⁻¹ᵁ V → ∀ a : O,
      valR x V (ρ a) = valR (x ≫ s) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a) :=
    fun x hx a => valR_appLE x s ⊤ V le_top _ hx
  letI := ρ.toAlgebra
  haveI : Algebra.FiniteType O Γ(Z, V) := hρ
  obtain ⟨T, hT, ψ, hψ, hψb⟩ := exists_factor_halfRing_over (S := O) b (evalHom y V hyV)
    (RingHom.ext fun a => by
      have := hval y hyV a
      rw [hy, valR_spMap_top, valR_eq _ _ hyV] at this
      exact this) T₀
  obtain ⟨yT, hyT, hv⟩ := exists_point_of_ringHom hV ψ
  refine ⟨T, hT, yT, hyT, ?_, ?_⟩
  · refine point_ext hV (fun p _ => hyT (x := spMap _ p) trivial) hyV fun f => ?_
    rw [valR_spMap _ _ _ hyT, hv, valR_eq _ _ hyV, ← hψ]
    rfl
  · refine point_ext (isAffineOpen_top _) le_top le_top fun f => ?_
    obtain ⟨a, rfl⟩ :=
      (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.surjective f
    have := hval yT hyT a
    rw [hv] at this
    exact this.symm.trans ((DFunLike.congr_fun hψb a).trans (valR_spMap_top _ a).symm)

theorem exists_le_preimage_inclusion {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) {U : Z.Opens}
    (hU : ⊤ ≤ (spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT) ⁻¹ᵁ U) :
    ∃ T', ∃ h : T ≤ T', ⊤ ≤ (spMap (Subalgebra.inclusion (halfRing_mono h) :
      halfRing T →+* halfRing T') ≫ yT) ⁻¹ᵁ U := by
  let p : PrimeSpectrum (halfRing T) :=
    spMap (halfIncl T : halfRing T →+* convLaurent) (default : PrimeSpectrum convLaurent)
  have hp : p ∈ (show Set (PrimeSpectrum (halfRing T)) from (yT ⁻¹ᵁ U).carrier) :=
    hU (x := (default : PrimeSpectrum convLaurent)) trivial
  obtain ⟨_, ⟨r, rfl⟩, hr, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp (yT ⁻¹ᵁ U).isOpen
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr p.asIdeal.zero_mem
  obtain ⟨T', h, hu⟩ := exists_isUnit_halfRing hr0
  refine ⟨T', h, fun q _ => hle (a := spMap (Subalgebra.inclusion (halfRing_mono h) :
      halfRing T →+* halfRing T') q) fun hq => ?_⟩
  exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hu)

def halfCurve {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) (w : ℂ) : Sp ℂ ⟶ Z :=
  if hw : T < w.im then spMap (ev T w hw : halfRing T →+* ℂ) ≫ yT
  else spMap (ev T (((T + 1 : ℝ) : ℂ) * Complex.I) (by simp) : halfRing T →+* ℂ) ≫ yT

theorem halfCurve_eq {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) {w : ℂ} (hw : T < w.im) :
    halfCurve yT w = spMap (ev T w hw : halfRing T →+* ℂ) ≫ yT := dif_pos hw

theorem halfCurve_comp {T : ℝ} {Z' : Scheme.{0}} (yT : Sp (halfRing T) ⟶ Z) (j : Z ⟶ Z') (w : ℂ) :
    halfCurve (yT ≫ j) w = halfCurve yT w ≫ j := by
  unfold halfCurve
  split_ifs <;> rw [Category.assoc]

theorem halfCurve_inclusion {T T' : ℝ} (h : T ≤ T') (yT : Sp (halfRing T) ⟶ Z) {w : ℂ}
    (hw : T' < w.im) :
    halfCurve (spMap (Subalgebra.inclusion (halfRing_mono h) : halfRing T →+* halfRing T') ≫ yT) w =
      halfCurve yT w := by
  rw [halfCurve_eq _ hw, halfCurve_eq _ (h.trans_lt hw), ← Category.assoc, ← spMap_comp]
  rfl

theorem valAt'_halfCurve {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) {U : Z.Opens} (hU : ⊤ ≤ yT ⁻¹ᵁ U)
    {w : ℂ} (hw : T < w.im) :
    ⊤ ≤ halfCurve yT w ⁻¹ᵁ U ∧ ∀ f, valAt' (halfCurve yT w) U f = ev T w hw (valR yT U f) := by
  rw [halfCurve_eq _ hw]
  exact ⟨fun p _ => hU (x := spMap _ p) trivial, fun f => valR_spMap _ yT U hU f⟩

theorem isHolTo_halfCurve {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) :
    IsHolTo {w : ℂ | T < w.im} (halfCurve yT) := by
  have ho : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  refine isHolTo_of_holAt ho fun z hz => ?_
  have h : HolAt (halfCurve (𝟙 (Sp (halfRing T)))) z := by
    refine holAt_of_affine (isAffineOpen_top _) le_top (Eventually.of_forall fun _ => le_top)
      fun g => ?_
    exact (differentiableOn_of_eq_ev (valR (𝟙 (Sp (halfRing T))) ⊤ g)
      fun w hw => (valAt'_halfCurve (𝟙 _) le_top hw).2 g).differentiableAt (ho.mem_nhds hz)
  have := h.comp yT
  simpa only [← halfCurve_comp, Category.id_comp] using this

theorem exists_valAt'_halfCurve {T : ℝ} {yT : Sp (halfRing T) ⟶ Z} {y : Sp convLaurent ⟶ Z}
    (hy : spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT = y) {U : Z.Opens}
    (hU : ⊤ ≤ y ⁻¹ᵁ U) :
    ∃ T' ≥ T, (∀ w : ℂ, T' < w.im → ⊤ ≤ halfCurve yT w ⁻¹ᵁ U) ∧
      ∀ f : Γ(Z, U), ∃ hf : ((valR y U f : convLaurent) : ℂ⸨X⸩) ∈ halfRing T',
        ∀ (w : ℂ) (hw : T' < w.im), valAt' (halfCurve yT w) U f = ev T' w hw ⟨_, hf⟩ := by
  subst hy
  obtain ⟨T', h, hU'⟩ := exists_le_preimage_inclusion yT hU
  refine ⟨T', h, fun w hw => ?_, fun f => ?_⟩
  · rw [← halfCurve_inclusion h yT hw]
    exact (valAt'_halfCurve _ hU' hw).1
  · have e := valR_spMap (halfIncl T' : halfRing T' →+* convLaurent) _ U hU' f
    rw [← Category.assoc, ← spMap_comp] at e
    have e' : ((valR (spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT) U f : convLaurent) :
        ℂ⸨X⸩) = (valR (spMap (Subalgebra.inclusion (halfRing_mono h) :
          halfRing T →+* halfRing T') ≫ yT) U f : halfRing T') :=
      congrArg (fun x : convLaurent => (x : ℂ⸨X⸩)) e
    refine ⟨e' ▸ Subtype.property _, fun w hw => ?_⟩
    rw [← halfCurve_inclusion h yT hw, (valAt'_halfCurve _ hU' hw).2]
    exact ev_congr hw hw e'.symm

theorem exists_sumsAt_halfCurve {T : ℝ} {yT : Sp (halfRing T) ⟶ Z} {y : Sp convLaurent ⟶ Z}
    (hy : spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT = y) {χ : Sp ℂ⟦X⟧ ⟶ Z}
    {F : Type} [Field F] (ι : ℂ⸨X⸩ →+* F)
    (hχ : spMap (ι.comp (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)) ≫ χ =
      spMap (ι.comp (algebraMap convLaurent ℂ⸨X⸩)) ≫ y)
    {U : Z.Opens} (hU : ⊤ ≤ χ ⁻¹ᵁ U) :
    ∃ T' ≥ T, ∀ w : ℂ, T' < w.im → ⊤ ≤ halfCurve yT w ⁻¹ᵁ U ∧
      ∀ f : Γ(Z, U), SumsAt (valR χ U f) w (valAt' (halfCurve yT w) U f) := by
  have hyU : ⊤ ≤ y ⁻¹ᵁ U := by
    intro p _
    have h1 : ⊤ ≤ (spMap (ι.comp (algebraMap convLaurent ℂ⸨X⸩)) ≫ y) ⁻¹ᵁ U := by
      rw [← hχ]
      exact fun q _ => hU (x := spMap _ q) trivial
    obtain rfl : p = spMap (ι.comp (algebraMap convLaurent ℂ⸨X⸩)) (default : PrimeSpectrum F) :=
      Subsingleton.elim (α := PrimeSpectrum convLaurent) _ _
    exact h1 (x := (default : PrimeSpectrum F)) trivial
  obtain ⟨T', hT, h₁, h₂⟩ := exists_valAt'_halfCurve hy hyU
  refine ⟨T', hT, fun w hw => ⟨h₁ w hw, fun f => ?_⟩⟩
  obtain ⟨hf, hv⟩ := h₂ f
  rw [hv w hw]
  refine sumsAt_ev_of_eq hw (ι.injective ?_)
  have e := valR_spMap (ι.comp (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)) χ U hU f
  rw [hχ, valR_spMap _ y U hyU] at e
  exact e.symm

def laurentToFraction : ℂ⸨X⸩ ≃ₐ[ℂ⟦X⟧] FractionRing ℂ⟦X⟧ :=
  (FractionRing.algEquiv ℂ⟦X⟧ ℂ⸨X⸩).symm

def convToFraction : convLaurent →+* FractionRing ℂ⟦X⟧ :=
  (laurentToFraction : ℂ⸨X⸩ →+* FractionRing ℂ⟦X⟧).comp (algebraMap convLaurent ℂ⸨X⸩)

end GlobalTheory.Conv
