import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HolHom

section Values

variable {A : Type} [CommRing A] {X : Scheme.{0}}

def evalHom (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

theorem valR_eq (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valR x U f = evalHom x U h f := by
  rw [valR, dif_pos h]; rfl

theorem valAt'_eq_valR (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valAt' x U f = valR x U f := rfl

theorem valR_appLE {Y : Scheme.{0}} (x : Sp A ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (h : V ≤ φ ⁻¹ᵁ U)
    (f : Γ(Y, U)) (hx : ⊤ ≤ x ⁻¹ᵁ V) : valR x V ((φ.appLE U V h).hom f) = valR (x ≫ φ) U f := by
  have hx' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := le_trans hx (x.preimage_mono h)
  rw [valR_eq _ _ hx, valR_eq _ _ hx', evalHom, evalHom, ← Scheme.Hom.appLE_comp_appLE x φ U V ⊤ h hx]
  rfl

theorem valR_comp {Y : Scheme.{0}} (x : Sp A ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valR (x ≫ φ) U f = valR x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  by_cases hx : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [Scheme.Hom.app_eq_appLE, valR_appLE x φ U _ le_rfl f hx]
  · have hx' : ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := hx
    rw [valR, valR, dif_neg hx, dif_neg hx']

theorem valR_res (x : Sp A ⟶ X) {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    valR x V ((X.presheaf.map (homOfLE h).op).hom f) = valR x U f := by
  have hx' : ⊤ ≤ x ⁻¹ᵁ U := le_trans hx (x.preimage_mono h)
  rw [valR_eq _ _ hx, valR_eq _ _ hx', evalHom, evalHom, ← Scheme.Hom.map_appLE x hx (homOfLE h).op]
  rfl

theorem valR_spMap {A' : Type} [CommRing A'] (ρ : A →+* A') (x : Sp A ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR (spMap ρ ≫ x) U f = ρ (valR x U f) := by
  have hx' : ⊤ ≤ (spMap ρ ≫ x) ⁻¹ᵁ U := fun p _ => hx (x := spMap ρ p) trivial
  rw [valR_eq _ _ hx, valR_eq _ _ hx', evalHom, evalHom,
    ← Scheme.Hom.appLE_comp_appLE (spMap ρ) x U ⊤ ⊤ hx le_rfl]
  have h3 : (spMap ρ).appLE ⊤ ⊤ le_rfl = (spMap ρ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [h3, Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl

theorem point_ext {x x' : Sp A ⟶ X} {U : X.Opens} (hU : IsAffineOpen U) (hx : ⊤ ≤ x ⁻¹ᵁ U) (hx' : ⊤ ≤ x' ⁻¹ᵁ U)
    (h : ∀ f, valR x U f = valR x' U f) : x = x' := by
  rw [← AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of A) x hx,
    ← AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of A) x' hx']
  congr 2
  ext1
  refine RingHom.ext fun f => ?_
  have := h f
  rwa [valR_eq _ _ hx, valR_eq _ _ hx'] at this

theorem le_preimage_iff (x : Sp ℂ ⟶ X) (U : X.Opens) : ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U := by
  refine ⟨fun h => h (x := (default : PrimeSpectrum ℂ)) trivial, fun h p _ => ?_⟩
  obtain rfl : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact h

theorem exists_affine (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ∃ P : X.Opens, IsAffineOpen P ∧ ⊤ ≤ x ⁻¹ᵁ P ∧ P ≤ U := by
  obtain ⟨P, hP, hp, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U) ((le_preimage_iff x U).1 h)
  exact ⟨P, hP, (le_preimage_iff x P).2 hp, hle⟩

theorem le_basicOpen_iff (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0 := by
  have h1 := Scheme.basicOpen_appLE x ⊤ U h f
  rw [top_inf_eq] at h1
  rw [← h1, valAt'_eq_valR, valR_eq _ _ h, top_le_iff, ← isUnit_iff_ne_zero]
  have h2 : IsUnit (evalHom x U h f) ↔ IsUnit ((x.appLE U ⊤ h).hom f) :=
    MulEquiv.isUnit_map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  rw [h2]
  exact ⟨fun H => (Sp ℂ).toRingedSpace.isUnit_of_isUnit_germ _ _ fun p hp =>
    ((Sp ℂ).mem_basicOpen _ p hp).1 (H.ge hp), fun H => (Sp ℂ).basicOpen_of_isUnit H⟩

theorem le_preimage_dual_iff {v : Sp (DualNumber ℂ) ⟶ X} {x : Sp ℂ ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x) (U : X.Opens) : ⊤ ≤ v ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  subst h
  refine ⟨fun hx p _ => hx (x := spMap _ p) trivial, fun hx => ?_⟩
  have hl : IsLocalHom (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).hom :=
    ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  refine (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of (DualNumber ℂ)) v ?_).ge
  have := hx (x := IsLocalRing.closedPoint ℂ) trivial
  rw [← Spec_closedPoint (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)]
  exact this

end Values

section Hol

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

def HolAt (c : V → (Sp ℂ ⟶ X)) (z : V) : Prop :=
  ∀ U : X.Opens, ⊤ ≤ c z ⁻¹ᵁ U →
    (∀ᶠ t in 𝓝 z, ⊤ ≤ c t ⁻¹ᵁ U) ∧ ∀ f : Γ(X, U), DifferentiableAt ℂ (fun t => valAt' (c t) U f) z

theorem holAt_of_isHolTo {B : Set V} {c : V → (Sp ℂ ⟶ X)} (h : IsHolTo B c) {z : V} (hz : z ∈ B) : HolAt c z := by
  intro U hU
  have hn : {b ∈ B | ⊤ ≤ c b ⁻¹ᵁ U} ∈ 𝓝 z := (h U 0).1.mem_nhds ⟨hz, hU⟩
  exact ⟨mem_of_superset hn fun t ht => ht.2, fun f => (h U f).2.differentiableAt hn⟩

theorem isOpen_of_isHolTo {B : Set V} {c : V → (Sp ℂ ⟶ X)} (h : IsHolTo B c) : IsOpen B := by
  simpa using (h ⊤ 0).1

theorem isHolTo_of_holAt {B : Set V} {c : V → (Sp ℂ ⟶ X)} (hB : IsOpen B) (h : ∀ z ∈ B, HolAt c z) :
    IsHolTo B c := by
  intro U f
  refine ⟨isOpen_iff_mem_nhds.2 fun z hz => ?_, fun z hz => ((h z hz.1 U hz.2).2 f).differentiableWithinAt⟩
  filter_upwards [hB.mem_nhds hz.1, (h z hz.1 U hz.2).1] with t h1 h2 using ⟨h1, h2⟩

theorem isHolTo_iff {B : Set V} {c : V → (Sp ℂ ⟶ X)} : IsHolTo B c ↔ IsOpen B ∧ ∀ z ∈ B, HolAt c z :=
  ⟨fun h => ⟨isOpen_of_isHolTo h, fun _ hz => holAt_of_isHolTo h hz⟩, fun h => isHolTo_of_holAt h.1 h.2⟩

theorem holAt_const (x : Sp ℂ ⟶ X) (z : V) : HolAt (fun _ => x) z :=
  fun _ hU => ⟨Eventually.of_forall fun _ => hU, fun _ => differentiableAt_const _⟩

theorem HolAt.comp {Y : Scheme.{0}} {c : V → (Sp ℂ ⟶ X)} {z : V} (h : HolAt c z) (φ : X ⟶ Y) :
    HolAt (fun t => c t ≫ φ) z := by
  intro U hU
  refine ⟨(h (φ ⁻¹ᵁ U) hU).1, fun f => ?_⟩
  simp only [valAt'_eq_valR, valR_comp]
  exact (h (φ ⁻¹ᵁ U) hU).2 _

theorem HolAt.precomp {V' : Type} [NormedAddCommGroup V'] [NormedSpace ℂ V'] {c : V → (Sp ℂ ⟶ X)} {k : V' → V} {z : V'}
    (h : HolAt c (k z)) (hk : DifferentiableAt ℂ k z) : HolAt (fun t => c (k t)) z :=
  fun U hU => ⟨hk.continuousAt.eventually (h U hU).1, fun f => ((h U hU).2 f).comp z hk⟩

theorem holAt_of_affine {c : V → (Sp ℂ ⟶ X)} {z : V} {P : X.Opens} (hP : IsAffineOpen P) (h₀ : ⊤ ≤ c z ⁻¹ᵁ P)
    (hev : ∀ᶠ t in 𝓝 z, ⊤ ≤ c t ⁻¹ᵁ P) (hd : ∀ g : Γ(X, P), DifferentiableAt ℂ (fun t => valAt' (c t) P g) z) :
    HolAt c z := by
  intro U hU
  obtain ⟨s, hsU, hs₀⟩ := hP.exists_basicOpen_le (V := U) ⟨_, (le_preimage_iff _ U).1 hU⟩ ((le_preimage_iff _ P).1 h₀)
  have hs : valAt' (c z) P s ≠ 0 := (le_basicOpen_iff _ h₀ s).1 ((le_preimage_iff _ _).2 hs₀)
  have hN : ∀ᶠ t in 𝓝 z, ⊤ ≤ c t ⁻¹ᵁ X.basicOpen s := by
    filter_upwards [hev, (hd s).continuousAt.eventually_ne hs] with t h1 h2 using (le_basicOpen_iff _ h1 s).2 h2
  refine ⟨hN.mono fun t ht => le_trans ht ((c t).preimage_mono hsU), fun f => ?_⟩
  obtain ⟨n, g, hg⟩ := exists_eq_pow_mul_of_isAffineOpen X P hP s ((X.presheaf.map (homOfLE hsU).op).hom f)
  have key : ∀ᶠ t in 𝓝 z, valAt' (c t) U f = valAt' (c t) P g / valAt' (c t) P s ^ n := by
    filter_upwards [hev, hN] with t hp ht
    have hne := (le_basicOpen_iff _ hp s).1 ht
    have h1 := valR_res (c t) (X.basicOpen_le s) g ht
    have h2 := valR_res (c t) (X.basicOpen_le s) s ht
    have h3 := valR_res (c t) hsU f ht
    have hg' : (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom g =
        (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom s ^ n * (X.presheaf.map (homOfLE hsU).op).hom f := hg
    rw [eq_div_iff (pow_ne_zero n hne)]
    simp only [valAt'_eq_valR]
    rw [← h1, ← h2, ← h3, hg', valR_eq _ _ ht, valR_eq _ _ ht, valR_eq _ _ ht, map_mul, map_pow, mul_comm]
  simp only [div_eq_mul_inv] at key
  exact ((hd g).fun_mul (((hd s).fun_pow n).fun_inv (pow_ne_zero n hs))).congr_of_eventuallyEq key

theorem holAt_of_isPullback {Y S Z : Scheme.{0}} {f : Y ⟶ S} {g : Z ⟶ X} {iX : X ⟶ S} {iY : Z ⟶ Y}
    (H : IsPullback g iY iX f) {c : V → (Sp ℂ ⟶ Z)} {z : V}
    (h₁ : HolAt (fun t => c t ≫ g) z) (h₂ : HolAt (fun t => c t ≫ iY) z) : HolAt c z := by
  obtain ⟨T, hT, hpT, -⟩ := exists_affine (c z ≫ g ≫ iX) (U := ⊤) le_top
  obtain ⟨U, hU, hpU, hUT⟩ := exists_affine (c z ≫ g) (U := iX ⁻¹ᵁ T) hpT
  obtain ⟨W, hW, hpW, hWT⟩ := exists_affine (c z ≫ iY) (U := f ⁻¹ᵁ T) (by rw [H.w] at hpT; exact hpT)
  have hmem : ∀ t, ⊤ ≤ c t ⁻¹ᵁ (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ W) ↔ ⊤ ≤ (c t ≫ g) ⁻¹ᵁ U ∧ ⊤ ≤ (c t ≫ iY) ⁻¹ᵁ W := by
    intro t
    rw [Scheme.Hom.preimage_inf, le_inf_iff]
    rfl
  have hP : IsAffineOpen (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ W) := by
    have : IsAffine _ := hU
    have : IsAffine _ := hW
    have : IsAffine _ := hT
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := T) (UT := W) (UX := U) hWT hUT rfl).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := T) (UT := W) (UX := U) hWT hUT rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hT hW hU)
  have hev : ∀ᶠ t in 𝓝 z, ⊤ ≤ c t ⁻¹ᵁ (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ W) := by
    filter_upwards [(h₁ U hpU).1, (h₂ W hpW).1] with t h1 h2 using (hmem t).2 ⟨h1, h2⟩
  refine holAt_of_affine hP ((hmem z).2 ⟨hpU, hpW⟩) hev fun r => ?_
  have hr := (CommRingCat.closure_range_union_range_eq_top_of_isPushout po).ge (Subring.mem_top r)
  induction hr using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact ((h₁ U hpU).2 a).congr_of_eventuallyEq (hev.mono fun t ht => valR_appLE _ _ _ _ _ _ ht)
    · exact ((h₂ W hpW).2 b).congr_of_eventuallyEq (hev.mono fun t ht => valR_appLE _ _ _ _ _ _ ht)
  | zero =>
    refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq (hev.mono fun t ht => ?_)
    simp only [valAt'_eq_valR, valR_eq _ _ ht, map_zero]
  | one =>
    refine (differentiableAt_const (1 : ℂ)).congr_of_eventuallyEq (hev.mono fun t ht => ?_)
    simp only [valAt'_eq_valR, valR_eq _ _ ht, map_one]
  | add x y _ _ hx hy =>
    refine (hx.add hy).congr_of_eventuallyEq (hev.mono fun t ht => ?_)
    simp only [valAt'_eq_valR, valR_eq _ _ ht, map_add, Pi.add_apply]
  | neg x _ hx =>
    refine hx.neg.congr_of_eventuallyEq (hev.mono fun t ht => ?_)
    simp only [valAt'_eq_valR, valR_eq _ _ ht, map_neg, Pi.neg_apply]
  | mul x y _ _ hx hy =>
    refine (hx.mul hy).congr_of_eventuallyEq (hev.mono fun t ht => ?_)
    simp only [valAt'_eq_valR, valR_eq _ _ ht, map_mul, Pi.mul_apply]

end Hol

section Deriv

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

def IsDerivAt (c : V → (Sp ℂ ⟶ X)) (z w : V) (v : Sp (DualNumber ℂ) ⟶ X) : Prop :=
  spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = c z ∧
    ∀ U : X.Opens, ⊤ ≤ c z ⁻¹ᵁ U → ∀ f : Γ(X, U),
      TrivSqZeroExt.snd (valR v U f) = fderiv ℂ (fun t => valAt' (c t) U f) z w

theorem isDerivAt0_iff {g : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 e w v ↔ IsDerivAt e 0 w v := by
  refine and_congr_right fun h => forall_congr' fun U => ?_
  constructor
  · intro H hU f
    have hv := (le_preimage_dual_iff h U).2 hU
    rw [valR_eq _ _ hv]
    exact H hv f
  · intro H hv f
    have := H ((le_preimage_dual_iff h U).1 hv) f
    rw [valR_eq _ _ hv] at this
    exact this

theorem fst_valR {v : Sp (DualNumber ℂ) ⟶ X} {x : Sp ℂ ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x) {U : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    TrivSqZeroExt.fst (valR v U f) = valAt' x U f := by
  have := valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom v U ((le_preimage_dual_iff h U).2 hU) f
  rw [h] at this
  exact this.symm

theorem tangent_ext {v v' : Sp (DualNumber ℂ) ⟶ X} {x : Sp ℂ ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x)
    (h' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' = x)
    (H : ∀ U : X.Opens, ⊤ ≤ x ⁻¹ᵁ U → ∀ f : Γ(X, U),
      TrivSqZeroExt.snd (valR v U f) = TrivSqZeroExt.snd (valR v' U f)) : v = v' := by
  obtain ⟨U, hU, hx, -⟩ := exists_affine x (U := ⊤) le_top
  refine point_ext hU ((le_preimage_dual_iff h U).2 hx) ((le_preimage_dual_iff h' U).2 hx) fun f => ?_
  exact TrivSqZeroExt.ext ((fst_valR h hx f).trans (fst_valR h' hx f).symm) (H U hx f)

theorem IsDerivAt.unique {c : V → (Sp ℂ ⟶ X)} {z w : V} {v v' : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt c z w v)
    (h' : IsDerivAt c z w v') : v = v' :=
  tangent_ext h.1 h'.1 fun U hU f => (h.2 U hU f).trans (h'.2 U hU f).symm

theorem IsDerivAt.comp {Y : Scheme.{0}} {c : V → (Sp ℂ ⟶ X)} {z w : V} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt c z w v) (φ : X ⟶ Y) : IsDerivAt (fun t => c t ≫ φ) z w (v ≫ φ) := by
  refine ⟨by rw [← Category.assoc, h.1], fun U hU f => ?_⟩
  simp only [valAt'_eq_valR, valR_comp]
  exact h.2 (φ ⁻¹ᵁ U) hU _

abbrev constVec (x : Sp ℂ ⟶ X) : Sp (DualNumber ℂ) ⟶ X := spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x

theorem fst_constVec (x : Sp ℂ ⟶ X) : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ constVec x = x := by
  rw [← Category.assoc, ← Spec.map_comp]
  convert Category.id_comp x
  rw [← Spec.map_id]
  congr 1

theorem isDerivAt_constVec_iff {c : V → (Sp ℂ ⟶ X)} {z w : V} : IsDerivAt c z w (constVec (c z)) ↔
    ∀ U : X.Opens, ⊤ ≤ c z ⁻¹ᵁ U → ∀ f : Γ(X, U), fderiv ℂ (fun t => valAt' (c t) U f) z w = 0 := by
  refine (and_iff_right (fst_constVec _)).trans (forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_)
  rw [valR_spMap _ _ _ hU, eq_comm, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]

theorem isDerivAt_const (x : Sp ℂ ⟶ X) (z w : V) : IsDerivAt (fun _ => x) z w (constVec x) :=
  (isDerivAt_constVec_iff (c := fun _ => x)).2 fun _ _ _ => by simp

def jetHom {c : V → (Sp ℂ ⟶ X)} {z : V} (h : HolAt c z) (w : V) (U : X.Opens) (hU : ⊤ ≤ c z ⁻¹ᵁ U) :
    Γ(X, U) →+* DualNumber ℂ where
  toFun f := TrivSqZeroExt.inl (valAt' (c z) U f) + TrivSqZeroExt.inr (fderiv ℂ (fun t => valAt' (c t) U f) z w)
  map_one' := by
    have : (fun t => valAt' (c t) U 1) =ᶠ[𝓝 z] fun _ => 1 := (h U hU).1.mono fun t ht => by
      simp only [valAt'_eq_valR, valR_eq _ _ ht, map_one]
    have h0 := this.self_of_nhds
    beta_reduce at h0
    rw [this.fderiv_eq, h0]
    simp
  map_zero' := by
    have : (fun t => valAt' (c t) U 0) =ᶠ[𝓝 z] fun _ => 0 := (h U hU).1.mono fun t ht => by
      simp only [valAt'_eq_valR, valR_eq _ _ ht, map_zero]
    have h0 := this.self_of_nhds
    beta_reduce at h0
    rw [this.fderiv_eq, h0]
    simp
  map_add' f f' := by
    have : (fun t => valAt' (c t) U (f + f')) =ᶠ[𝓝 z] fun t => valAt' (c t) U f + valAt' (c t) U f' :=
      (h U hU).1.mono fun t ht => by simp only [valAt'_eq_valR, valR_eq _ _ ht, map_add]
    have h0 := this.self_of_nhds
    beta_reduce at h0
    rw [this.fderiv_eq, h0, fderiv_fun_add ((h U hU).2 f) ((h U hU).2 f')]
    ext <;> simp
  map_mul' f f' := by
    have : (fun t => valAt' (c t) U (f * f')) =ᶠ[𝓝 z] fun t => valAt' (c t) U f * valAt' (c t) U f' :=
      (h U hU).1.mono fun t ht => by simp only [valAt'_eq_valR, valR_eq _ _ ht, map_mul]
    have h0 := this.self_of_nhds
    beta_reduce at h0
    rw [this.fderiv_eq, h0, fderiv_fun_mul ((h U hU).2 f) ((h U hU).2 f')]
    ext <;> simp [mul_comm]

theorem jetHom_res {c : V → (Sp ℂ ⟶ X)} {z : V} (h : HolAt c z) (w : V) {U U' : X.Opens} (hle : U' ≤ U)
    (hU : ⊤ ≤ c z ⁻¹ᵁ U) (hU' : ⊤ ≤ c z ⁻¹ᵁ U') (f : Γ(X, U)) :
    jetHom h w U' hU' ((X.presheaf.map (homOfLE hle).op).hom f) = jetHom h w U hU f := by
  have : (fun t => valAt' (c t) U' ((X.presheaf.map (homOfLE hle).op).hom f)) =ᶠ[𝓝 z] fun t => valAt' (c t) U f :=
    (h U' hU').1.mono fun t ht => valR_res _ hle f ht
  have h0 := this.self_of_nhds
  beta_reduce at h0
  simp only [jetHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [this.fderiv_eq, h0]

theorem HolAt.exists_isDerivAt {c : V → (Sp ℂ ⟶ X)} {z : V} (h : HolAt c z) (w : V) : ∃ v, IsDerivAt c z w v := by
  obtain ⟨P, hP, hz, -⟩ := exists_affine (c z) (U := ⊤) le_top
  let φ : Γ(X, P) ⟶ CommRingCat.of (DualNumber ℂ) := CommRingCat.ofHom (jetHom h w P hz)
  let v : Sp (DualNumber ℂ) ⟶ X := Spec.map φ ≫ hP.fromSpec
  have hvP : ⊤ ≤ v ⁻¹ᵁ P := fun p _ => hP.range_fromSpec.le ⟨_, rfl⟩
  have hval : ∀ f, valR v P f = jetHom h w P hz f := fun f => by
    rw [valR_eq _ _ hvP]
    exact congrArg (fun ψ => ψ.hom f) (AffinePointValues.appLE_specMap_fromSpec hP φ hvP)
  have h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = c z := by
    refine point_ext hP (fun p _ => hvP (x := spMap _ p) trivial) hz fun f => ?_
    rw [valR_spMap _ _ _ hvP, hval]
    simp [jetHom, valAt'_eq_valR]
  refine ⟨v, h1, fun U hU f => ?_⟩
  obtain ⟨s, hsU, hs₀⟩ := hP.exists_basicOpen_le (V := U) ⟨_, (le_preimage_iff _ U).1 hU⟩ ((le_preimage_iff _ P).1 hz)
  have hs : ⊤ ≤ c z ⁻¹ᵁ X.basicOpen s := (le_preimage_iff _ _).2 hs₀
  have hvs := (le_preimage_dual_iff h1 _).2 hs
  have := hP.isLocalization_basicOpen s
  have key : evalHom v _ hvs = jetHom h w _ hs := by
    refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun g => ?_)
    change evalHom v _ hvs ((X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom g) =
      jetHom h w _ hs ((X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom g)
    rw [jetHom_res h w _ hz, ← valR_eq, valR_res _ _ _ hvs, hval]
  rw [← valR_res v hsU f hvs, valR_eq _ _ hvs, key, jetHom_res h w _ hU]
  simp [jetHom]

theorem eq_of_isDerivAt_constVec {c : V → (Sp ℂ ⟶ X)} (h : ∀ z, HolAt c z)
    (h' : ∀ z w, IsDerivAt c z w (constVec (c z))) (z z' : V) : c z = c z' := by
  let : NormedSpace ℝ V := NormedSpace.restrictScalars ℝ ℂ V
  refine IsLocallyConstant.apply_eq_of_preconnectedSpace ((IsLocallyConstant.iff_eventually_eq c).2 fun x => ?_) z z'
  obtain ⟨P, hP, hx, -⟩ := exists_affine (c x) (U := ⊤) le_top
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h x P hx).1
  filter_upwards [Metric.ball_mem_nhds x hr] with t ht
  refine point_ext hP (hball t ht) hx fun f => ?_
  exact Metric.isOpen_ball.is_const_of_fderiv_eq_zero (𝕜 := ℂ) (f := fun t => valAt' (c t) P f)
    (convex_ball x r).isPreconnected (fun s hs => ((h s P (hball s hs)).2 f).differentiableWithinAt)
    (fun s hs => ContinuousLinearMap.ext fun w => isDerivAt_constVec_iff.1 (h' s w) P (hball s hs) f)
    ht (Metric.mem_ball_self hr)

end Deriv

section Group

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S : Scheme.{0}}

theorem holAt_lift {P : V → Over S} {G G' : Over S} (i : ∀ t, Sp ℂ ⟶ (P t).left) {a : ∀ t, P t ⟶ G}
    {b : ∀ t, P t ⟶ G'} {z : V} (ha : HolAt (fun t => i t ≫ (a t).left) z)
    (hb : HolAt (fun t => i t ≫ (b t).left) z) : HolAt (fun t => i t ≫ (lift (a t) (b t)).left) z := by
  have H : IsPullback (fst G G').left (snd G G').left G.hom G'.hom := IsPullback.of_hasPullback G.hom G'.hom
  refine holAt_of_isPullback H ?_ ?_
  · simpa only [Category.assoc, ← Over.comp_left, lift_fst] using ha
  · simpa only [Category.assoc, ← Over.comp_left, lift_snd] using hb

variable {G : Over S} [GrpObj G]

theorem isHolTo_mul {B : Set V} {y : V → (Sp ℂ ⟶ S)} {a b : ∀ t, Over.mk (y t) ⟶ G}
    (ha : IsHolTo B (fun t => (a t).left)) (hb : IsHolTo B (fun t => (b t).left)) :
    IsHolTo B (fun t => (a t * b t).left) := by
  refine isHolTo_of_holAt (isOpen_of_isHolTo ha) fun z hz => ?_
  have := (holAt_lift (P := fun t => Over.mk (y t)) (fun _ => 𝟙 (Sp ℂ)) (a := a) (b := b) (z := z)
    (by simpa using holAt_of_isHolTo ha hz) (by simpa using holAt_of_isHolTo hb hz)).comp μ[G].left
  simpa [Hom.mul_def] using this

theorem isHolTo_inv {B : Set V} {y : V → (Sp ℂ ⟶ S)} {a : ∀ t, Over.mk (y t) ⟶ G}
    (ha : IsHolTo B (fun t => (a t).left)) : IsHolTo B (fun t => ((a t)⁻¹).left) :=
  isHolTo_of_holAt (isOpen_of_isHolTo ha) fun _ hz => (holAt_of_isHolTo ha hz).comp (GrpObj.inv (X := G)).left

variable {y : Sp ℂ ⟶ S}

omit [GrpObj G] in

theorem IsDerivAt.over {a : V → (Over.mk y ⟶ G)} {z w : V} {v : Sp (DualNumber ℂ) ⟶ G.left}
    (h : IsDerivAt (fun t => (a t).left) z w v) : v ≫ G.hom = (epsPt y).hom := by
  have h1 := h.comp G.hom
  have h2 : (fun t => (a t).left ≫ G.hom) = fun _ => y := funext fun t => Over.w (a t)
  exact (h2 ▸ h1).unique (isDerivAt_const y z w)

omit [GrpObj G] in

theorem isDerivAt_lift {G' : Over S} {a : V → (Over.mk y ⟶ G)} {b : V → (Over.mk y ⟶ G')} {z w : V}
    (ha : HolAt (fun t => (a t).left) z) (hb : HolAt (fun t => (b t).left) z) {v : epsPt y ⟶ G} {v' : epsPt y ⟶ G'}
    (hv : IsDerivAt (fun t => (a t).left) z w v.left) (hv' : IsDerivAt (fun t => (b t).left) z w v'.left) :
    IsDerivAt (fun t => (lift (a t) (b t)).left) z w (lift v v').left := by
  have hl : HolAt (fun t => (lift (a t) (b t)).left) z := by
    simpa using holAt_lift (P := fun _ => Over.mk y) (fun _ => 𝟙 (Sp ℂ)) (a := a) (b := b) (z := z)
      (by simpa using ha) (by simpa using hb)
  obtain ⟨u, hu⟩ := hl.exists_isDerivAt w
  have h1 := hu.comp (fst G G').left
  have h2 := hu.comp (snd G G').left
  simp only [← Over.comp_left, lift_fst, lift_snd] at h1 h2
  have H : IsPullback (fst G G').left (snd G G').left G.hom G'.hom := IsPullback.of_hasPullback G.hom G'.hom
  have : (lift v v').left = u := by
    refine H.hom_ext ?_ ?_
    · rw [h1.unique hv, ← Over.comp_left, lift_fst]
    · rw [h2.unique hv', ← Over.comp_left, lift_snd]
  exact this ▸ hu

theorem isDerivAt_mul {a b : V → (Over.mk y ⟶ G)} {z w : V}
    (ha : HolAt (fun t => (a t).left) z) (hb : HolAt (fun t => (b t).left) z) {v v' : epsPt y ⟶ G}
    (hv : IsDerivAt (fun t => (a t).left) z w v.left) (hv' : IsDerivAt (fun t => (b t).left) z w v'.left) :
    IsDerivAt (fun t => (a t * b t).left) z w (v * v').left :=
  (isDerivAt_lift ha hb hv hv').comp μ[G].left

theorem isDerivAt_inv {a : V → (Over.mk y ⟶ G)} {z w : V} {v : epsPt y ⟶ G}
    (hv : IsDerivAt (fun t => (a t).left) z w v.left) : IsDerivAt (fun t => ((a t)⁻¹).left) z w (v⁻¹).left :=
  hv.comp (GrpObj.inv (X := G)).left

theorem map_zero_eq_one {A M : Type*} [AddMonoid A] [Group M] {e : A → M} (he : ∀ z w, e (z + w) = e z * e w) : e 0 = 1 := by
  have := he 0 0
  rw [add_zero] at this
  exact mul_eq_left.mp this.symm

theorem eq_of_fderiv_eq {e e' : V → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w)
    (he' : ∀ z w, e' (z + w) = e' z * e' w) (hol : IsHolTo Set.univ (fun z => (e z).left))
    (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (hd : ∀ U : G.left.Opens, ⊤ ≤ (e 0).left ⁻¹ᵁ U → ∀ f : Γ(G.left, U),
      fderiv ℂ (fun z => valAt' (e z).left U f) 0 = fderiv ℂ (fun z => valAt' (e' z).left U f) 0) : e = e' := by
  have h0 : e 0 = e' 0 := (map_zero_eq_one he).trans (map_zero_eq_one he').symm
  let j : epsPt y ⟶ Over.mk y := Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
  have hj : ∀ (x : Over.mk y ⟶ G) (z w : V), IsDerivAt (fun _ : V => x.left) z w (j ≫ x).left :=
    fun x z w => isDerivAt_const x.left z w
  have hc : ∀ x : Over.mk y ⟶ G, IsHolTo Set.univ (fun _ : V => x.left) :=
    fun x => isHolTo_of_holAt isOpen_univ fun z _ => holAt_const _ _
  have hdh := isHolTo_mul (y := fun _ => y) hol (isHolTo_inv (y := fun _ => y) hol')
  have at0 := fun {c : V → (Sp ℂ ⟶ G.left)} (h : IsHolTo Set.univ c) (z : V) => holAt_of_isHolTo h (Set.mem_univ z)
  have key : ∀ z w, IsDerivAt (fun t => (e t * (e' t)⁻¹).left) z w (constVec (e z * (e' z)⁻¹).left) := by
    intro z w
    obtain ⟨u, hu⟩ := (at0 hol 0).exists_isDerivAt w
    have hu' : IsDerivAt (fun t => (e' t).left) 0 w u :=
      ⟨hu.1.trans (congrArg (·.left) h0), fun U hU f => by
        have hU' : ⊤ ≤ (e 0).left ⁻¹ᵁ U := h0 ▸ hU
        rw [hu.2 U hU' f, hd U hU' f]⟩
    let v : epsPt y ⟶ G := Over.homMk u hu.over
    have h1 := isDerivAt_mul (at0 hol 0) (at0 (isHolTo_inv (y := fun _ => y) hol') 0) (v := v) hu
      (isDerivAt_inv (v := v) hu')
    have h2 := isDerivAt_mul (at0 (hc (e z)) 0) (at0 hdh 0) (hj _ 0 w) h1
    have h3 := isDerivAt_mul (at0 (isHolTo_mul (y := fun _ => y) (hc (e z)) hdh) 0) (at0 (hc (e' z)⁻¹) 0) h2 (hj _ 0 w)
    have h4 : ∀ t, e z * (e t * (e' t)⁻¹) * (e' z)⁻¹ = e (z + t) * (e' (z + t))⁻¹ := fun t => by
      rw [he, he', mul_inv_rev]; simp only [_root_.mul_assoc]
    rw [mul_inv_cancel, _root_.mul_one, ← MonObj.comp_mul] at h3
    simp only [h4] at h3
    have h5 : IsDerivAt (fun t => (e (z + t) * (e' (z + t))⁻¹).left) 0 w
        (constVec (e (z + 0) * (e' (z + 0))⁻¹).left) := by
      rw [add_zero]; exact h3
    refine (isDerivAt_constVec_iff (c := fun t => (e t * (e' t)⁻¹).left)).2 fun U hU f => ?_
    have h6 := (isDerivAt_constVec_iff (c := fun t => (e (z + t) * (e' (z + t))⁻¹).left)).1 h5 U
      (by simpa only [add_zero] using hU) f
    rwa [fderiv_comp_add_left (f := fun t => valAt' (e t * (e' t)⁻¹).left U f), add_zero] at h6
  funext z
  have := eq_of_isDerivAt_constVec (at0 hdh) key z 0
  rw [← mul_inv_eq_one]
  ext1
  rw [this, h0, mul_inv_cancel]

end Group

section Linear

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem IsDerivAt.snd_linear {X : Scheme.{0}} {c : V → (Sp ℂ ⟶ X)} {z w₁ w₂ : V} {a₁ a₂ : ℂ}
    {v₁ v₂ v : Sp (DualNumber ℂ) ⟶ X} (h₁ : IsDerivAt c z w₁ v₁) (h₂ : IsDerivAt c z w₂ v₂)
    (h : IsDerivAt c z (a₁ • w₁ + a₂ • w₂) v) (U : X.Opens) (hU : ⊤ ≤ c z ⁻¹ᵁ U) (f : Γ(X, U)) :
    TrivSqZeroExt.snd (valR v U f) = a₁ * TrivSqZeroExt.snd (valR v₁ U f) + a₂ * TrivSqZeroExt.snd (valR v₂ U f) := by
  rw [h.2 U hU, h₁.2 U hU, h₂.2 U hU, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

variable {S : Scheme.{0}} {G : Over S} {g : ℕ}

theorem eq_of_forall_fderiv_eq {y : Sp ℂ ⟶ S} {e' : (Fin g → ℂ) → (Over.mk y ⟶ G)}
    (hol' : HolAt (fun z => (e' z).left) 0)
    (hdiff : ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
      ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) {w w' : Fin g → ℂ}
    (h : ∀ U : G.left.Opens, ⊤ ≤ (e' 0).left ⁻¹ᵁ U → ∀ f : Γ(G.left, U),
      fderiv ℂ (fun z => valAt' (e' z).left U f) 0 w = fderiv ℂ (fun z => valAt' (e' z).left U f) 0 w') : w = w' := by
  obtain ⟨u, hu⟩ := hol'.exists_isDerivAt w
  exact (hdiff (Over.homMk u hu.over) hu.1).unique ((isDerivAt0_iff _ _ _).2 hu)
    ((isDerivAt0_iff _ _ _).2 ⟨hu.1, fun U hU f => (hu.2 U hU f).trans (h U hU f)⟩)

theorem existsUnique_linear [FiniteDimensional ℂ V] [GrpObj G] {y : Sp ℂ ⟶ S} {e : V → (Over.mk y ⟶ G)}
    {e' : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w)
    (he' : ∀ z w, e' (z + w) = e' z * e' w) (hol : IsHolTo Set.univ (fun z => (e z).left))
    (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (hdiff : ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
      ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) :
    ∃! h : V →ₗ[ℂ] (Fin g → ℂ), ∀ z, e z = e' (h z) := by
  have h0 : e 0 = e' 0 := (map_zero_eq_one he).trans (map_zero_eq_one he').symm
  have hA := holAt_of_isHolTo hol (Set.mem_univ 0)
  have hA' := holAt_of_isHolTo hol' (Set.mem_univ 0)
  have hex : ∀ z : V, ∃ w, ∀ U : G.left.Opens, ⊤ ≤ (e' 0).left ⁻¹ᵁ U → ∀ f : Γ(G.left, U),
      fderiv ℂ (fun t => valAt' (e' t).left U f) 0 w = fderiv ℂ (fun t => valAt' (e t).left U f) 0 z := by
    intro z
    obtain ⟨u, hu⟩ := hA.exists_isDerivAt z
    obtain ⟨w, hw, -⟩ := hdiff (Over.homMk u hu.over) (hu.1.trans (congrArg (·.left) h0))
    have hw' := (isDerivAt0_iff _ _ _).1 hw
    exact ⟨w, fun U hU f => (hw'.2 U hU f).symm.trans (hu.2 U (h0 ▸ hU :) f)⟩
  choose k hk using hex
  have chain : ∀ (h : V →ₗ[ℂ] (Fin g → ℂ)) (U : G.left.Opens), ⊤ ≤ (e' 0).left ⁻¹ᵁ U → ∀ (f : Γ(G.left, U)) (z : V),
      fderiv ℂ (fun t => valAt' (e' (h t)).left U f) 0 z = fderiv ℂ (fun t => valAt' (e' t).left U f) 0 (h z) := by
    intro h U hU f z
    have h1 : HasFDerivAt (fun t => valAt' (e' t).left U f) (fderiv ℂ (fun t => valAt' (e' t).left U f) 0)
        (LinearMap.toContinuousLinearMap h 0) := by
      rw [map_zero]; exact ((hA' U hU).2 f).hasFDerivAt
    exact congrArg (· z) (h1.comp 0 (LinearMap.toContinuousLinearMap h).hasFDerivAt).fderiv
  let h : V →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := k
      map_add' := fun z z' => eq_of_forall_fderiv_eq hA' hdiff fun U hU f => by
        rw [map_add, hk _ U hU, hk _ U hU, hk _ U hU, map_add]
      map_smul' := fun a z => eq_of_forall_fderiv_eq hA' hdiff fun U hU f => by
        rw [map_smul, hk _ U hU, hk _ U hU, map_smul, RingHom.id_apply] }
  refine ⟨h, congrFun (eq_of_fderiv_eq (e' := fun z => e' (h z)) he (fun z w => by rw [map_add, he']) hol ?_ ?_),
    fun h' hh' => LinearMap.ext fun z => eq_of_forall_fderiv_eq hA' hdiff fun U hU f => ?_⟩
  · exact isHolTo_of_holAt isOpen_univ fun z _ => (holAt_of_isHolTo hol' (Set.mem_univ (h z))).precomp
      (LinearMap.toContinuousLinearMap h).differentiableAt
  · intro U hU f
    ext z
    rw [chain h U (h0 ▸ hU :) f z]
    exact (hk z U (h0 ▸ hU :) f).symm
  · rw [← chain h' U hU f z]
    simp only [← hh']
    exact (hk z U hU f).symm

theorem differentiableAt_partial {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    [FiniteDimensional ℂ V] {F : P × V → ℂ} {s : Set (P × V)} (hs : IsOpen s) (hF : DifferentiableOn ℂ F s) {b : P}
    (hb : (b, 0) ∈ s) : DifferentiableAt ℂ (fun b => fderiv ℂ (fun z => F (b, z)) 0) b := by
  have h1 : DifferentiableAt ℂ (fderiv ℂ F) (b, 0) :=
    (SCV.differentiableOn_fderiv hs hF).differentiableAt (hs.mem_nhds hb)
  have h2 : DifferentiableAt ℂ (fun b : P => (fderiv ℂ F (b, 0)).comp (ContinuousLinearMap.inr ℂ P V)) b :=
    (h1.comp b (f := fun b : P => (b, (0 : V))) (by fun_prop)).clm_comp (differentiableAt_const _)
  refine h2.congr_of_eventuallyEq ?_
  have h3 : ContinuousAt (fun b : P => (b, (0 : V))) b := by fun_prop
  filter_upwards [h3.eventually (hs.mem_nhds hb)] with b' hb'
  exact ((hF.differentiableAt (hs.mem_nhds hb')).hasFDerivAt.comp 0 (hasFDerivAt_prodMk_right b' (0 : V))).fderiv

theorem differentiableOn_linear {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    [FiniteDimensional ℂ V] {B : Set P} {y : P → (Sp ℂ ⟶ S)} {e : ∀ b, V → (Over.mk (y b) ⟶ G)}
    {e' : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)}
    (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : P × V => (e bz.1 bz.2).left))
    (hol' : IsHolTo (B ×ˢ Set.univ) (fun bz : P × (Fin g → ℂ) => (e' bz.1 bz.2).left))
    (hdiff : ∀ b ∈ B, ∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' b 0).left →
      ∃! w, IsDerivAt0 (fun z => (e' b z).left) w v.left)
    {h : P → V →ₗ[ℂ] (Fin g → ℂ)} (hh : ∀ b ∈ B, ∀ z, e b z = e' b (h b z)) :
    DifferentiableOn ℂ (fun b => LinearMap.toContinuousLinearMap (h b)) B := by
  intro b₀ hb₀
  refine DifferentiableAt.differentiableWithinAt ?_
  have hslice : ∀ b ∈ B, HolAt (fun z => (e' b z).left) 0 := fun b hb =>
    (holAt_of_isHolTo hol' (z := (b, 0)) ⟨hb, trivial⟩).precomp (k := fun z => (b, z)) (by fun_prop)
  let s : Set ((Fin g → ℂ) →ₗ[ℂ] ℂ) := {l | ∃ (U : G.left.Opens) (_ : ⊤ ≤ (e' b₀ 0).left ⁻¹ᵁ U) (f : Γ(G.left, U)),
    l = (fderiv ℂ (fun z => valAt' (e' b₀ z).left U f) 0).toLinearMap}
  have hs : Submodule.span ℂ s = ⊤ := Submodule.span_eq_top_of_ne_zero fun w hw => by
    by_contra hne
    refine hw (eq_of_forall_fderiv_eq (hslice b₀ hb₀) (hdiff b₀ hb₀) fun U hU f => ?_)
    rw [map_zero]
    by_contra h0
    exact hne ⟨_, ⟨U, hU, f, rfl⟩, h0⟩
  have key : ∀ l ∈ Submodule.span ℂ s, ∃ (m : P → (Fin g → ℂ) →L[ℂ] ℂ) (n : P → V →L[ℂ] ℂ),
      DifferentiableAt ℂ m b₀ ∧ DifferentiableAt ℂ n b₀ ∧ (m b₀).toLinearMap = l ∧
        ∀ᶠ b in 𝓝 b₀, ∀ z, m b (h b z) = n b z := by
    intro l hl
    induction hl using Submodule.span_induction with
    | mem l hl =>
      obtain ⟨U, hU, f, rfl⟩ := hl
      have hU' : ⊤ ≤ (e b₀ 0).left ⁻¹ᵁ U := by rw [hh b₀ hb₀, map_zero]; exact hU
      refine ⟨fun b => fderiv ℂ (fun z => valAt' (e' b z).left U f) 0,
        fun b => fderiv ℂ (fun z => valAt' (e b z).left U f) 0,
        differentiableAt_partial (hol' U f).1 (hol' U f).2 ⟨⟨hb₀, trivial⟩, hU⟩,
        differentiableAt_partial (hol U f).1 (hol U f).2 ⟨⟨hb₀, trivial⟩, hU'⟩, rfl, ?_⟩
      have h3 : ContinuousAt (fun b : P => (b, (0 : Fin g → ℂ))) b₀ := by fun_prop
      filter_upwards [h3.eventually ((hol' U f).1.mem_nhds ⟨⟨hb₀, trivial⟩, hU⟩)] with b hb z
      have h1 : HasFDerivAt (fun t => valAt' (e' b t).left U f) (fderiv ℂ (fun t => valAt' (e' b t).left U f) 0)
          (LinearMap.toContinuousLinearMap (h b) 0) := by
        rw [map_zero]; exact ((hslice b hb.1.1 U hb.2).2 f).hasFDerivAt
      simp only [hh b hb.1.1]
      exact (congrArg (· z) (h1.comp 0 (LinearMap.toContinuousLinearMap (h b)).hasFDerivAt).fderiv).symm
    | zero => exact ⟨0, 0, differentiableAt_const _, differentiableAt_const _, rfl, .of_forall fun _ _ => rfl⟩
    | add l l' _ _ ih ih' =>
      obtain ⟨m, n, hm, hn, rfl, hmn⟩ := ih
      obtain ⟨m', n', hm', hn', rfl, hmn'⟩ := ih'
      refine ⟨m + m', n + n', hm.add hm', hn.add hn', rfl, ?_⟩
      filter_upwards [hmn, hmn'] with b h1 h2 z
      simp [h1 z, h2 z]
    | smul a l _ ih =>
      obtain ⟨m, n, hm, hn, rfl, hmn⟩ := ih
      refine ⟨a • m, a • n, hm.const_smul a, hn.const_smul a, rfl, ?_⟩
      filter_upwards [hmn] with b h1 z
      simp [h1 z]
  choose m n hm hn hm0 hmn using fun i : Fin g => key (LinearMap.proj i) (hs.ge trivial)
  let M : P → (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := fun b => ContinuousLinearMap.pi fun i => m i b
  let N : P → V →L[ℂ] (Fin g → ℂ) := fun b => ContinuousLinearMap.pi fun i => n i b
  have hM : DifferentiableAt ℂ M b₀ :=
    (ContinuousLinearMap.piEquivL ℂ (Fin g → ℂ) (fun _ : Fin g => ℂ)).differentiableAt.comp b₀
      (differentiableAt_pi.2 hm)
  have hN : DifferentiableAt ℂ N b₀ :=
    (ContinuousLinearMap.piEquivL ℂ V (fun _ : Fin g => ℂ)).differentiableAt.comp b₀ (differentiableAt_pi.2 hn)
  have hM0 : M b₀ = (ContinuousLinearEquiv.refl ℂ (Fin g → ℂ) : _ →L[ℂ] _) := by
    ext1 w
    funext i
    exact congrArg (· w) (congrArg DFunLike.coe (hm0 i))
  have hinv : ∀ᶠ b in 𝓝 b₀, (M b).IsInvertible :=
    hM.continuousAt.eventually (hM0 ▸ (ContinuousLinearEquiv.refl ℂ (Fin g → ℂ)).nhds :)
  have hI : DifferentiableAt ℂ (fun b => (M b).inverse) b₀ :=
    ((hinv.self_of_nhds.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero).comp b₀ hM
  refine (hI.clm_comp hN).congr_of_eventuallyEq ?_
  filter_upwards [hinv, eventually_all.2 hmn] with b hb hb'
  ext1 z
  have : M b (h b z) = N b z := funext fun i => hb' i z
  exact (hb.inverse_apply_eq.2 this.symm).symm

end Linear

section Family

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)

theorem isHolTo_ex (i : Fin Fu.n) {P : (Fu.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (Fu.Di i) ty P) :
    IsHolTo Set.univ (fun z => (Fu.ex i P z).left) := by
  have h := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  exact isHolTo_of_holAt isOpen_univ fun z _ =>
    (holAt_of_isHolTo h (z := (0, z)) ⟨trivial, trivial⟩).precomp (k := fun z => (0, z)) (by fun_prop)

theorem existsUnique_linear_ex {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (i : Fin Fu.n) {P : (Fu.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (Fu.Di i) ty P)
    {e : V → (Over.mk (Fu.u i P) ⟶ Xo.univ.t.G)} (he : ∀ z w, e (z + w) = e z * e w)
    (hol : IsHolTo Set.univ (fun z => (e z).left)) :
    ∃! h : V →ₗ[ℂ] (Fin g → ℂ), ∀ z, e z = Fu.ex i P (h z) :=
  existsUnique_linear he (Fu.ex_add i P hP) hol (isHolTo_ex Fu i hP) (Fu.ex_diff i P hP).2

end Family

end GlobalTheory.HolHom

namespace GlobalTheory

open HolHom in

theorem holomorphic_hom_determined (S : Scheme.{0}) (G : Over S) [GrpObj G] :
    (∀ (y : Sp ℂ ⟶ S) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (e e' : V → (Over.mk y ⟶ G)),
      (∀ z w, e (z + w) = e z * e w) → (∀ z w, e' (z + w) = e' z * e' w) →
      IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => (e' z).left) →
      (∀ U : G.left.Opens, ⊤ ≤ (e 0).left ⁻¹ᵁ U → ∀ f : Γ(G.left, U),
        fderiv ℂ (fun z => valAt' (e z).left U f) 0 = fderiv ℂ (fun z => valAt' (e' z).left U f) 0) → e = e') ∧
    (∀ (y : Sp ℂ ⟶ S) (n : ℕ) (e : (Fin n → ℂ) → (Over.mk y ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) →
      (∀ z₀, ∃! v : Sp (DualNumber ℂ) ⟶ G.left, IsDerivAt0 (fun z => (e z).left) z₀ v) ∧
      (∀ z₀ v, IsDerivAt0 (fun z => (e z).left) z₀ v → v ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) ∧
      ∀ (a₁ a₂ : ℂ) (z₁ z₂ : Fin n → ℂ) (v₁ v₂ v : Sp (DualNumber ℂ) ⟶ G.left),
        IsDerivAt0 (fun z => (e z).left) z₁ v₁ → IsDerivAt0 (fun z => (e z).left) z₂ v₂ →
        IsDerivAt0 (fun z => (e z).left) (a₁ • z₁ + a₂ • z₂) v →
        ∀ U : G.left.Opens, ⊤ ≤ (e 0).left ⁻¹ᵁ U → ⊤ ≤ v₁ ⁻¹ᵁ U ∧ ⊤ ≤ v₂ ⁻¹ᵁ U ∧ ⊤ ≤ v ⁻¹ᵁ U ∧ ∀ f : Γ(G.left, U),
          TrivSqZeroExt.snd (valR v U f) =
            a₁ * TrivSqZeroExt.snd (valR v₁ U f) + a₂ * TrivSqZeroExt.snd (valR v₂ U f)) ∧
    (∀ (y : Sp ℂ ⟶ S) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (g : ℕ)
      (e : V → (Over.mk y ⟶ G)) (e' : (Fin g → ℂ) → (Over.mk y ⟶ G)),
      (∀ z w, e (z + w) = e z * e w) → (∀ z w, e' (z + w) = e' z * e' w) →
      IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => (e' z).left) →
      (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
        ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) →
      ∃! h : V →ₗ[ℂ] (Fin g → ℂ), ∀ z, e z = e' (h z)) ∧
    ∀ (P V : Type) [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] [NormedAddCommGroup V]
      [NormedSpace ℂ V] [FiniteDimensional ℂ V] (g : ℕ) (B : Set P) (y : P → (Sp ℂ ⟶ S))
      (e : ∀ b, V → (Over.mk (y b) ⟶ G)) (e' : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G))
      (h : P → V →ₗ[ℂ] (Fin g → ℂ)),
      IsHolTo (B ×ˢ Set.univ) (fun bz : P × V => (e bz.1 bz.2).left) →
      IsHolTo (B ×ˢ Set.univ) (fun bz : P × (Fin g → ℂ) => (e' bz.1 bz.2).left) →
      (∀ b ∈ B, ∀ v : epsPt (y b) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' b 0).left →
        ∃! w, IsDerivAt0 (fun z => (e' b z).left) w v.left) →
      (∀ b ∈ B, ∀ z, e b z = e' b (h b z)) →
      DifferentiableOn ℂ (fun b => LinearMap.toContinuousLinearMap (h b)) B ∧
        ContinuousOn (fun b => LinearMap.toContinuousLinearMap (h b)) B ∧ ∀ z, ContinuousOn (fun b => h b z) B := by
  refine ⟨fun y V _ _ e e' he he' hol hol' hd => eq_of_fderiv_eq he he' hol hol' hd, fun y n e hol => ⟨fun z₀ => ?_,
    fun z₀ v hv => ((isDerivAt0_iff _ _ _).1 hv).over, fun a₁ a₂ z₁ z₂ v₁ v₂ v h₁ h₂ h U hU => ?_⟩,
    fun y V _ _ _ g e e' he he' hol hol' hd => existsUnique_linear he he' hol hol' hd,
    fun P V _ _ _ _ _ _ g B y e e' h hol hol' hd hh => ?_⟩
  · simp only [isDerivAt0_iff]
    obtain ⟨v, hv⟩ := (holAt_of_isHolTo hol (Set.mem_univ 0)).exists_isDerivAt z₀
    exact ⟨v, hv, fun _ hv' => hv'.unique hv⟩
  · exact ⟨(le_preimage_dual_iff h₁.1 U).2 hU, (le_preimage_dual_iff h₂.1 U).2 hU, (le_preimage_dual_iff h.1 U).2 hU,
      IsDerivAt.snd_linear ((isDerivAt0_iff _ _ _).1 h₁) ((isDerivAt0_iff _ _ _).1 h₂) ((isDerivAt0_iff _ _ _).1 h) U hU⟩
  · have H := differentiableOn_linear hol hol' hd hh
    exact ⟨H, H.continuousOn, fun z => H.continuousOn.clm_apply (continuousOn_const (c := z))⟩

end GlobalTheory
