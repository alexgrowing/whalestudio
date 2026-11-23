import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

noncomputable section

namespace GlobalTheory.ShFam.BdArc

theorem exists_basicOpen_subset_of_pt {A : Type} [CommRing A] (f : A →+* ℂ) (U : Set (Sp A)) (hU : IsOpen U)
    (h : ∀ s, spMap f s ∈ U) :
    ∃ a : A, f a ≠ 0 ∧ Set.range (spMap (algebraMap A (Localization.Away a))) ⊆ U := by
  let s₀ : PrimeSpectrum ℂ := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨_, ⟨a, rfl⟩, h1, h2⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open (h s₀) hU
  refine ⟨a, ?_, ?_⟩
  · intro h0
    apply h1
    show f a ∈ (⊥ : Ideal ℂ)
    simp [h0]
  · have := PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
    rintro _ ⟨s, rfl⟩
    apply h2
    show _ ∈ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A))
    rw [← this]
    exact ⟨s, rfl⟩

theorem exists_hol_away {A : Type} [CommRing A] (ψ : ℂ → (A →+* ℂ)) (V : Set ℂ)
    (hψ : ∀ b, DifferentiableOn ℂ (fun u => ψ u b) V) (a : A) (ha : ∀ u ∈ V, ψ u a ≠ 0) (u₀ : ℂ) (h₀ : u₀ ∈ V) :
    ∃ ev : ℂ → (Localization.Away a →+* ℂ), (∀ u ∈ V, (ev u).comp (algebraMap A _) = ψ u) ∧
      ∀ t, DifferentiableOn ℂ (fun u => ev u t) V := by
  classical
  let ev : ℂ → (Localization.Away a →+* ℂ) := fun u =>
    if h : u ∈ V then IsLocalization.Away.lift a (g := ψ u) (Ne.isUnit (ha u h))
    else IsLocalization.Away.lift a (g := ψ u₀) (Ne.isUnit (ha u₀ h₀))
  have hev : ∀ u ∈ V, (ev u).comp (algebraMap A _) = ψ u := fun u hu => by
    simp only [ev, dif_pos hu]
    exact IsLocalization.Away.lift_comp a _
  refine ⟨ev, hev, fun t => ?_⟩
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj a t
  refine (((hψ b).div ((hψ a).pow n) fun u hu => pow_ne_zero n (ha u hu))).congr fun u hu => ?_
  have h1 := congrArg (ev u) hb
  have h2 : ∀ z, ev u (algebraMap A _ z) = ψ u z := fun z => RingHom.congr_fun (hev u hu) z
  rw [map_mul, map_pow, h2, h2] at h1
  show _ = ψ u b / ψ u a ^ n
  rw [eq_div_iff (pow_ne_zero n (ha u hu)), h1]

theorem spMap_comp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem dualMap_comp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun z => by ext <;> simp [dualMap]

theorem spMap_dualMap_sq {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    spMap (dualMap f) ≫ spMap (algebraMap A (DualNumber A)) = spMap (algebraMap B (DualNumber B)) ≫ spMap f := by
  rw [spMap_comp_comp, spMap_comp_comp]
  congr 1
  exact RingHom.ext fun z => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem arc_descends_to_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)), IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → ∀ u₀ ∈ Metric.ball (0 : ℂ) r, u₀ ≠ 0 → ∃ (R : Type) (_ : CommRing R) (xR : Sp R ⟶ Xo.X) (vR : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) (ev : ℂ → (R →+* ℂ)) (V : Set ℂ), IsOpen V ∧ u₀ ∈ V ∧ (∀ t, DifferentiableOn ℂ (fun u => ev u t) V) ∧ ∀ u ∈ V, (y u).x = spMap (show R →+* CAt σ from ev u) ≫ xR ∧ ∀ τ i, (y u).u τ i = spMap (dualMap (show R →+* CAt σ from ev u)) ≫ vR τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ r y harc hm u₀ hu₀ hne
  haveI := Z.jQ_open
  obtain ⟨a, ha, hsub⟩ := exists_basicOpen_subset_of_pt (ψ u₀) (x ⁻¹' Set.range Z.jQ)
    ((IsOpenImmersion.isOpen_range Z.jQ).preimage x.continuous) (fun s => by
      have h := (hm u₀ hu₀ hne).1
      refine ⟨GlobalTheory.AllWt.ptF (y u₀) s, ?_⟩
      exact (congrArg (fun g => g s) h :))
  have hopen : IsOpen {u | u ∈ Metric.ball (0 : ℂ) r ∧ ψ u a ≠ 0} :=
    ((harc.1.2 a).continuousOn).isOpen_inter_preimage Metric.isOpen_ball (isOpen_ne (x := (0 : ℂ)))
  let V : Set ℂ := {u | u ∈ Metric.ball (0 : ℂ) r ∧ ψ u a ≠ 0} ∩ {u | u ≠ 0}
  obtain ⟨ev, hev, hd⟩ := exists_hol_away ψ V (fun b => (harc.1.2 b).mono fun u hu => hu.1.1) a
    (fun u hu => hu.1.2) u₀ ⟨⟨hu₀, ha⟩, hne⟩
  let R := Localization.Away a
  let ι : A →+* R := algebraMap A R
  have hr : Set.range (spMap ι ≫ x) ⊆ Set.range Z.jQ := by
    rintro _ ⟨s, rfl⟩
    exact hsub ⟨s, rfl⟩
  let x' : Sp R ⟶ Xo.XF c := IsOpenImmersion.lift Z.jQ (spMap ι ≫ x) hr
  have hx' : x' ≫ Z.jQ = spMap ι ≫ x := IsOpenImmersion.lift_fac _ _ _
  have P : IsPullback Z.m.φ Z.oF.t.G.hom Z.t.G.hom (Z.jQ ≫ genι Z) := Z.m.cart.1
  have hw : ∀ τ i, (spMap (dualMap ι) ≫ fr.v τ i) ≫ Z.t.G.hom =
      (spMap (algebraMap R (DualNumber R)) ≫ x') ≫ Z.jQ ≫ genι Z := fun τ i => by
    rw [Category.assoc, (fr.tan τ i).1, ← Category.assoc, spMap_dualMap_sq, Category.assoc, Category.assoc,
      ← Category.assoc x', hx', Category.assoc]
  refine ⟨R, inferInstance, x' ≫ pullback.fst _ _, fun τ i => P.lift _ _ (hw τ i) ≫ Z.m0.toSABMap.φ, ev, V,
    hopen.inter isOpen_ne, ⟨⟨hu₀, ha⟩, hne⟩, hd, fun u hu => ?_⟩
  obtain ⟨h1, h2⟩ := hm u hu.1.1 hu.2
  let e : R →+* CAt σ := ev u
  have he : e.comp ι = (show A →+* CAt σ from ψ u) := hev u hu
  have hp : GlobalTheory.AllWt.ptF (y u) = spMap e ≫ x' := by
    rw [← cancel_mono Z.jQ, h1, Category.assoc, hx', ← Category.assoc, spMap_comp_comp, he]
  refine ⟨?_, fun τ i => ?_⟩
  · show _ = spMap e ≫ x' ≫ _
    rw [← Category.assoc, ← hp]
    exact (pullback.lift_fst _ _ _).symm
  · obtain ⟨w, hw1, hw2, hw3⟩ := h2 τ i
    show _ = spMap (dualMap e) ≫ P.lift _ _ (hw τ i) ≫ _
    rw [← hw2, ← Category.assoc]
    congr 1
    apply P.hom_ext
    · rw [hw3, Category.assoc, P.lift_fst, ← Category.assoc, spMap_comp_comp, dualMap_comp_comp, he]
    · rw [hw1, Category.assoc, P.lift_snd, ← Category.assoc, spMap_dualMap_sq, Category.assoc, hp]

end GlobalTheory.ShFam.BdArc
