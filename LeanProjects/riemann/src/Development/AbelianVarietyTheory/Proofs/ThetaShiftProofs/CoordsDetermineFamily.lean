import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.CoordFamily

open Filter Topology GlobalTheory.Specialise GlobalTheory.AmpleSpan GlobalTheory.HolHom

variable {X Y : Scheme.{0}} {f : X ⟶ Y} {H : LB X} {I : Type} {t : I → LB.Sec H}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {x : V → (Sp ℂ ⟶ X)} {cf : I → V → ℂ}

theorem eq_of_proportional (ht : EmbedsBy f t) {p p' : Sp ℂ ⟶ X} (hf : p ≫ f = p' ≫ f) {c c' : I → ℂ}
    (h : HasCoords p t c) (h' : HasCoords p' t c') {ρ : ℂ} (e : ∀ i, c' i = ρ * c i) : p = p' := by
  obtain ⟨m, hm⟩ := h'.exists_isUnit ht.1
  have hρ : IsUnit ρ := isUnit_of_mul_isUnit_left (e m ▸ hm)
  have h₁ := h.mul_unit hρ
  have e' : (fun l => c l * ρ) = c' := funext fun l => by rw [e, mul_comm]
  rw [e'] at h₁
  exact h₁.ext ht hf h' hm

theorem holAt_of_coords (ht : EmbedsBy f t) {y : Sp ℂ ⟶ Y} (hy : ∀ v, x v ≫ f = y)
    (hc : ∀ v, HasCoords (x v) t fun i => cf i v) {z : V} (hd : ∀ i, DifferentiableAt ℂ (cf i) z) : HolAt x z := by
  obtain ⟨m, hm⟩ := (hc z).exists_isUnit ht.1
  obtain ⟨hD, ρ, hρ, hsurj⟩ := ht.2 m
  have hne : ∀ᶠ v in 𝓝 z, cf m v ≠ 0 := (hd m).continuousAt.eventually_ne hm.ne_zero
  have hev : ∀ᶠ v in 𝓝 z, ⊤ ≤ x v ⁻¹ᵁ Out.nonzeroLocus (t m) :=
    hne.mono fun v hv => (hc v).le_nonzeroLocus hv.isUnit
  refine holAt_of_affine hD hev.self_of_nhds hev fun g => ?_
  obtain ⟨q, rfl⟩ := hsurj g
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine (differentiableAt_const (valR y ⊤ a)).congr_of_eventuallyEq (hev.mono fun v hv => ?_)
    simp only [MvPolynomial.eval₂Hom_C, valAt'_eq_valR]
    exact (HolHom.valR_appLE (x v) f ⊤ _ le_top a hv).trans (by rw [hy])
  | add p q hp hq =>
    refine (hp.add hq).congr_of_eventuallyEq (hev.mono fun v hv => ?_)
    simp only [valAt'_eq_valR, HolHom.valR_eq _ _ hv, map_add, Pi.add_apply]
  | mul_X p l hp =>
    refine (hp.mul ((hd l).fun_mul ((hd m).fun_inv hm.ne_zero))).congr_of_eventuallyEq
      ((hev.and hne).mono fun v hv => ?_)
    have e := (hc v).valR_ratio hv.1 (hρ l)
    have e' : valR (x v) _ (ρ l) = cf l v * (cf m v)⁻¹ := by
      rw [← e, mul_inv_cancel_right₀ hv.2]
    simp only [valAt'_eq_valR, map_mul, MvPolynomial.eval₂Hom_X', Pi.mul_apply]
    rw [← e']
    simp only [HolHom.valR_eq _ _ hv.1, map_mul]

theorem hasCoords_deriv (hcov : ⨆ l, Out.nonzeroLocus (t l) = ⊤) (hc : ∀ v, HasCoords (x v) t fun i => cf i v)
    {z w : V} (hx : HolAt x z) (hd : ∀ i, DifferentiableAt ℂ (cf i) z) {ν : Sp (DualNumber ℂ) ⟶ X}
    (hν : IsDerivAt x z w ν) :
    HasCoords ν t fun i => TrivSqZeroExt.inl (cf i z) + TrivSqZeroExt.inr (fderiv ℂ (cf i) z w) := by
  obtain ⟨m, hm⟩ := (hc z).exists_isUnit hcov
  choose ρ hρ using fun l => exists_isRatio (t l) (t m)
  have hz := (hc z).le_nonzeroLocus hm
  have hν' := (le_preimage_dual_iff hν.1 _).2 hz
  have hu : IsUnit (TrivSqZeroExt.inl (cf m z) + TrivSqZeroExt.inr (fderiv ℂ (cf m) z w) : DualNumber ℂ) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by simpa using hm)
  have h₁ := (hasCoords_ratio hν' hρ).mul_unit hu
  convert h₁ using 2 with l
  have hev : cf l =ᶠ[𝓝 z] fun v => valAt' (x v) _ (ρ l) * cf m v :=
    (hx _ hz).1.mono fun v hv => ((hc v).valR_ratio hv (hρ l)).symm
  have h0 := hev.self_of_nhds
  beta_reduce at h0
  rw [hev.fderiv_eq, h0, fderiv_fun_mul ((hx _ hz).2 _) (hd m)]
  ext
  · simp [fst_valR hν.1 hz]
  · simp [fst_valR hν.1 hz, hν.2 _ hz, mul_comm]

theorem isDerivAt_of_coords (ht : EmbedsBy f t) {y : Sp ℂ ⟶ Y} (hy : ∀ v, x v ≫ f = y)
    (hc : ∀ v, HasCoords (x v) t fun i => cf i v) {z w : V} (hd : ∀ i, DifferentiableAt ℂ (cf i) z)
    {ν : Sp (DualNumber ℂ) ⟶ X} (hb : ν ≫ f = constVec y)
    (hν : HasCoords ν t fun i => TrivSqZeroExt.inl (cf i z) + TrivSqZeroExt.inr (fderiv ℂ (cf i) z w)) :
    IsDerivAt x z w ν := by
  have hx := holAt_of_coords ht hy hc hd
  obtain ⟨ν', hν'⟩ := hx.exists_isDerivAt w
  have h1 := hν'.comp f
  have h2 : (fun v => x v ≫ f) = fun _ => y := funext hy
  have h3 : ν' ≫ f = constVec y := (h2 ▸ h1).unique (isDerivAt_const y z w)
  rw [hν.ext_of_isLocalRing ht (hb.trans h3.symm) (hasCoords_deriv ht.1 hc hx hd hν')]
  exact hν'

theorem hasCoords_powOver {S : Scheme.{0}} {G : Over S} {L : LB G.left} (hL : L.IsLB) {U : S.Opens} {N : ℕ}
    {b : I → LB.Sec (Out.powOver G L U N)} {A : Type} [CommRing A] [IsLocalRing A]
    {p : Sp A ⟶ (G.hom ⁻¹ᵁ U).toScheme} {c : I → A}
    (h : ∀ j, ⊤ ≤ (p ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : Aˣ,
      ∀ i, valR p ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = c i * u) : HasCoords p b c := by
  obtain ⟨j, hj⟩ := Points.exists_le_preimage_of_iSup_eq_top (p ≫ (G.hom ⁻¹ᵁ U).ι) hL.cover
  exact ⟨fun _ => j, fun s hs => Set.mem_iInter.2 fun _ => hj hs, h j hj⟩

end GlobalTheory.CoordFamily

namespace GlobalTheory

open Specialise HolHom CoordFamily in

theorem coords_determine_family : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (U : S.Opens) (N n : ℕ) (b : Fin n → LB.Sec (Out.powOver G L U N)) (y : Sp ℂ ⟶ S) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (x : V → (Sp ℂ ⟶ (G.hom ⁻¹ᵁ U).toScheme)) (cf : Fin n → V → ℂ), L.IsLB → IsAffineOpen U → AmpleSpan.EmbedsBy (G.hom ∣_ U) b → (∀ v, x v ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y) → (∀ v j, ⊤ ≤ (x v ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : ℂ, u ≠ 0 ∧ ∀ i, valR (x v) ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = cf i v * u) → (∀ v v' (ρ : ℂ), (∀ i, cf i v' = ρ * cf i v) → x v' = x v) ∧ ((∀ i, Differentiable ℂ (cf i)) → IsHolTo Set.univ (fun v => x v ≫ (G.hom ⁻¹ᵁ U).ι) ∧ ∀ (z₀ : V) (ν : Sp (DualNumber ℂ) ⟶ (G.hom ⁻¹ᵁ U).toScheme), ν ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y → (∀ j, ⊤ ≤ (ν ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : (DualNumber ℂ)ˣ, ∀ i, valR ν ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = (TrivSqZeroExt.inl (cf i 0) + TrivSqZeroExt.inr (fderiv ℂ (cf i) 0 z₀)) * (u : DualNumber ℂ)) → ∀ (W : G.left.Opens) (f : Γ(G.left, W)), spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ ν = x 0 ∧ (⊤ ≤ (x 0 ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ W → TrivSqZeroExt.snd (valR (ν ≫ (G.hom ⁻¹ᵁ U).ι) W f) = fderiv ℂ (fun v => valAt' (x v ≫ (G.hom ⁻¹ᵁ U).ι) W f) 0 z₀)) := by
  intro S G _ L U N n b y V _ _ x cf hL _ hb hy hc
  have hc' : ∀ v, HasCoords (x v) b fun i => cf i v := fun v => hasCoords_powOver hL fun j hj => by
    obtain ⟨u, hu, e⟩ := hc v j hj
    exact ⟨Units.mk0 u hu, e⟩
  have hi : (G.hom ∣_ U) ≫ U.ι = (G.hom ⁻¹ᵁ U).ι ≫ G.hom := morphismRestrict_ι _ _
  have hy' : ∀ v, x v ≫ (G.hom ∣_ U) = x 0 ≫ (G.hom ∣_ U) := fun v => by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hi, hy, hy]
  refine ⟨fun v v' ρ e => (eq_of_proportional hb ((hy' v).trans (hy' v').symm) (hc' v) (hc' v') e).symm,
    fun hd => ⟨isHolTo_of_holAt isOpen_univ fun z _ => (holAt_of_coords hb hy' hc' fun i => hd i z).comp _,
      fun z₀ ν hν hνc W f => ?_⟩⟩
  have h := isDerivAt_of_coords (w := z₀) hb hy' hc' (fun i => hd i 0) (ν := ν)
    (by rw [← cancel_mono U.ι, Category.assoc, Category.assoc, Category.assoc, hi, hν, hy])
    (hasCoords_powOver hL hνc)
  exact ⟨h.1, fun hW => (h.comp (G.hom ⁻¹ᵁ U).ι).2 W hW f⟩

end GlobalTheory
