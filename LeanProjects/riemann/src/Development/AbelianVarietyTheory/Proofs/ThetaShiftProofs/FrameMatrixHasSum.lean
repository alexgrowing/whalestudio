import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallExistsLsumETwoPi
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuli
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback

noncomputable section

namespace GlobalTheory.ArcLie

section Series

open Filter GlobalTheory.Conv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

variable {Ω : Type} (p : Ω → ℂ)

def high : Filter Ω := comap (fun ω => (p ω).im) atTop

def Cv (s : ℂ⸨X⸩) (x : Ω → ℂ) : Prop :=
  ∀ᶠ ω in high p, HasSum (fun m : ℤ => s.coeff m * eTwoPi (p ω) ^ m) (x ω)

variable {p}

theorem high_iff {q : Ω → Prop} : (∀ᶠ ω in high p, q ω) ↔ ∃ T : ℝ, ∀ ω, T < (p ω).im → q ω := by
  rw [high, eventually_comap, eventually_atTop]
  constructor
  · rintro ⟨T, h⟩
    exact ⟨T, fun ω hω => h _ hω.le ω rfl⟩
  · rintro ⟨T, h⟩
    exact ⟨T + 1, fun b hb ω hω => h ω (by rw [hω]; linarith)⟩

theorem Cv.congr {s : ℂ⸨X⸩} {x y : Ω → ℂ} (h : Cv p s x) (e : ∀ᶠ ω in high p, x ω = y ω) : Cv p s y := by
  filter_upwards [h, e] with ω h1 h2 using h2 ▸ h1

theorem Cv.unique {s : ℂ⸨X⸩} {x y : Ω → ℂ} (h : Cv p s x) (h' : Cv p s y) : ∀ᶠ ω in high p, x ω = y ω := by
  filter_upwards [h, h'] with ω h1 h2 using h1.unique h2

theorem Cv.mul {s t : ℂ⸨X⸩} {x y : Ω → ℂ} (h : Cv p s x) (h' : Cv p t y) : Cv p (s * t) (fun ω => x ω * y ω) := by
  filter_upwards [h, h'] with ω h1 h2
  have := hasSum_mul_laurent (eTwoPi_ne_zero (p ω)) h1.summable h2.summable
  rwa [lsum, lsum, h1.tsum_eq, h2.tsum_eq] at this

theorem Cv.sub {s t : ℂ⸨X⸩} {x y : Ω → ℂ} (h : Cv p s x) (h' : Cv p t y) : Cv p (s - t) (fun ω => x ω - y ω) := by
  filter_upwards [h, h'] with ω h1 h2
  simpa [sub_mul] using h1.sub h2

theorem Cv.sum {κ : Type} (I : Finset κ) {s : κ → ℂ⸨X⸩} {x : κ → Ω → ℂ} (h : ∀ i ∈ I, Cv p (s i) (x i)) :
    Cv p (∑ i ∈ I, s i) (fun ω => ∑ i ∈ I, x i ω) := by
  filter_upwards [(eventually_all_finset I).2 h] with ω h1
  simpa [Finset.sum_mul, HahnSeries.coeff_sum] using hasSum_sum h1

theorem cv_of_mem {s : ℂ⸨X⸩} (hs : s ∈ convLaurent) : Cv p s (fun ω => lsum s (eTwoPi (p ω))) := by
  obtain ⟨T, hT⟩ := mem_convLaurent_iff_halfRing.1 hs
  exact high_iff.2 ⟨T, fun ω hω => (hT _ hω).hasSum⟩

theorem cv_const (c : ℂ) : Cv p (algebraMap ℂ ℂ⸨X⸩ c) (fun _ => c) := by
  simpa only [lsum_algebraMap] using cv_of_mem (p := p) (convLaurent.algebraMap_mem c)

theorem Cv.mem [NeBot (high p)] {s : ℂ⸨X⸩} {x : Ω → ℂ} (h : Cv p s x) : s ∈ convLaurent := by
  obtain ⟨ω, hω⟩ := h.exists
  exact mem_convLaurent_of_summable (eTwoPi_ne_zero _) hω.summable

theorem Cv.inv {s : ℂ⸨X⸩} {x : Ω → ℂ} (h : Cv p s x) (h0 : s ≠ 0) :
    (∀ᶠ ω in high p, x ω ≠ 0) ∧ Cv p s⁻¹ (fun ω => (x ω)⁻¹) := by
  rcases eq_or_neBot (high p) with hb | hb
  · simp [Cv, hb]
  have h1 := cv_of_mem (p := p) (convLaurent.inv_mem h.mem)
  have h2 := h.mul h1
  rw [mul_inv_cancel₀ h0, ← map_one (algebraMap ℂ ℂ⸨X⸩)] at h2
  have h3 := h2.unique (cv_const 1)
  exact ⟨h3.mono fun ω e => left_ne_zero_of_mul_eq_one e, h1.congr (h3.mono fun ω e => eq_inv_of_mul_eq_one_right e)⟩

theorem cv_coeff {F : Type} {m : ℕ} {A : F → Fin m → ℂ⸨X⸩} {B : F → ℂ⸨X⸩} {G : Fin m → ℂ⸨X⸩}
    {Aw : F → Fin m → Ω → ℂ} {Bw : F → Ω → ℂ} {Gw : Fin m → Ω → ℂ}
    (hB : ∀ f, B f = ∑ k, G k * A f k) (hsep : ∀ a : Fin m → ℂ⸨X⸩, (∀ f, ∑ k, a k * A f k = 0) → a = 0)
    (cA : ∀ f k, Cv p (A f k) (Aw f k)) (cB : ∀ f, Cv p (B f) (Bw f))
    (hw : ∀ f, ∀ᶠ ω in high p, Bw f ω = ∑ k, Gw k ω * Aw f k ω) (k : Fin m) : Cv p (G k) (Gw k) := by
  classical
  rcases eq_or_neBot (high p) with hb | hb
  · simp [Cv, hb]
  let A₀ : F → Fin m → convLaurent := fun f k => ⟨A f k, (cA f k).mem⟩
  have hspan : Submodule.span convLaurent (Set.range A₀) = ⊤ := by
    by_contra hne
    obtain ⟨L, hL, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have h0 := hsep (fun k => (L (Pi.single k 1) : convLaurent)) fun f => by
      have h1 : L (A₀ f) = 0 := hle (Submodule.subset_span ⟨f, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      have h2 := congrArg (fun x : convLaurent => (x : ℂ⸨X⸩)) h1
      simp only [smul_eq_mul, IntermediateField.coe_sum, MulMemClass.coe_mul, ZeroMemClass.coe_zero, A₀] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm]
      congr 3
      ext j
      simp [Pi.single_apply, eq_comm]
    refine hL (LinearMap.pi_ext' fun k => LinearMap.ext_ring ?_)
    exact Subtype.ext (congrFun h0 k)
  obtain ⟨cf, hcf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1
    (hspan.ge (Submodule.mem_top (x := (Pi.single k 1 : Fin m → convLaurent))))
  have hδ : ∀ j, ∑ f ∈ cf.support, (cf f : ℂ⸨X⸩) * A f j = algebraMap ℂ ℂ⸨X⸩ (if j = k then 1 else 0) := by
    intro j
    have h2 := congrArg (fun x : Fin m → convLaurent => convLaurent.val (x j)) hcf
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at h2
    refine h2.trans ?_
    by_cases hj : j = k <;> simp [hj]
  have hG : G k = ∑ f ∈ cf.support, (cf f : ℂ⸨X⸩) * B f := by
    simp only [hB, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_left_comm _ (G _), ← Finset.mul_sum, hδ]
    simp [apply_ite]
  have cc : ∀ f, Cv p (cf f) (fun ω => lsum (cf f) (eTwoPi (p ω))) := fun f => cv_of_mem (cf f).2
  have hδw : ∀ j, ∀ᶠ ω in high p, ∑ f ∈ cf.support, lsum (cf f) (eTwoPi (p ω)) * Aw f j ω = if j = k then 1 else 0 := by
    intro j
    have h1 := Cv.sum cf.support fun f _ => (cc f).mul (cA f j)
    rw [hδ] at h1
    exact h1.unique (cv_const _)
  rw [hG]
  refine (Cv.sum cf.support fun f _ => (cc f).mul (cB f)).congr ?_
  filter_upwards [eventually_all.2 hδw, (eventually_all_finset cf.support).2 fun f _ => hw f] with ω h1 h2
  rw [Finset.sum_congr rfl fun f hf => by rw [h2 f hf]]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_left_comm _ (Gw _ ω), ← Finset.mul_sum, h1]
  simp

end Series

section Local

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.HolHom

variable {A : Type} [CommRing A] {X : Scheme.{0}}

theorem le_basicOpen_iff_isUnit (x : Sp A ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ IsUnit (valR x U f) := by
  have h1 := Scheme.basicOpen_appLE x ⊤ U h f
  rw [top_inf_eq] at h1
  rw [← h1, valR_eq _ _ h, top_le_iff]
  have h2 : IsUnit (evalHom x U h f) ↔ IsUnit ((x.appLE U ⊤ h).hom f) :=
    MulEquiv.isUnit_map (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
  rw [h2]
  exact ⟨fun H => (Sp A).toRingedSpace.isUnit_of_isUnit_germ _ _ fun p hp =>
    ((Sp A).mem_basicOpen _ p hp).1 (H.ge hp), fun H => (Sp A).basicOpen_of_isUnit H⟩

theorem exists_frac (W : Sp A ⟶ X) (V : X.Opens) (f : Γ(X, V)) {K : Type} [Field K] (φ : A →+* K)
    (h : ⊤ ≤ (spMap φ ≫ W) ⁻¹ᵁ V) : ∃ H r : A, φ H ≠ 0 ∧ ∀ (B : Type) [CommRing B] (ψ : A →+* B), IsUnit (ψ H) →
      ⊤ ≤ (spMap ψ ≫ W) ⁻¹ᵁ V ∧ valR (spMap ψ ≫ W) V f * ψ H = ψ r := by
  have hP := isAffineOpen_top (Sp A)
  obtain ⟨s, hsU, hs₀⟩ := hP.exists_basicOpen_le (V := W ⁻¹ᵁ V)
    ⟨spMap φ (default : PrimeSpectrum K), h (x := (default : PrimeSpectrum K)) trivial⟩ trivial
  have hv : ∀ (B : Type) [CommRing B] (ψ : A →+* B) (g : Γ(Sp A, ⊤)), valR (spMap ψ) ⊤ g = ψ (valR (𝟙 _) ⊤ g) := by
    intro B _ ψ g
    rw [← valR_spMap ψ (𝟙 _) ⊤ le_top, Category.comp_id]
  have hs : IsUnit (φ (valR (𝟙 _) ⊤ s)) := by
    rw [← hv, ← le_basicOpen_iff_isUnit _ le_top]
    intro q _
    obtain rfl : q = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    exact hs₀
  obtain ⟨n, g, hg⟩ := exists_eq_pow_mul_of_isAffineOpen (Sp A) ⊤ hP s
    (((Sp A).presheaf.map (homOfLE hsU).op).hom ((W.app V).hom f))
  refine ⟨valR (𝟙 _) ⊤ s ^ (n + 1), valR (𝟙 _) ⊤ g * valR (𝟙 _) ⊤ s, ?_, fun B _ ψ hu => ?_⟩
  · rw [map_pow]
    exact (hs.pow _).ne_zero
  rw [map_pow, isUnit_pow_succ_iff, ← hv, ← le_basicOpen_iff_isUnit _ le_top] at hu
  refine ⟨le_trans hu ((spMap ψ).preimage_mono hsU), ?_⟩
  have h1 := valR_res (spMap ψ) ((Sp A).basicOpen_le s) g hu
  have h2 := valR_res (spMap ψ) ((Sp A).basicOpen_le s) s hu
  have h3 := valR_res (spMap ψ) hsU ((W.app V).hom f) hu
  have hg' : ((Sp A).presheaf.map (homOfLE ((Sp A).basicOpen_le s)).op).hom g =
      ((Sp A).presheaf.map (homOfLE ((Sp A).basicOpen_le s)).op).hom s ^ n *
        ((Sp A).presheaf.map (homOfLE hsU).op).hom ((W.app V).hom f) := hg
  rw [valR_comp, map_pow, map_mul, ← hv, ← hv, ← h1, ← h2, ← h3, hg', valR_eq _ _ hu, valR_eq _ _ hu, valR_eq _ _ hu,
    map_mul, map_pow]
  ring

theorem fst_comp_dualMap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) :
    (TrivSqZeroExt.fstHom S S S).toRingHom.comp (dualMap φ) = φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
  RingHom.ext fun x => by simp [dualMap]

theorem dualMap_comp_algebraMap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) :
    (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp φ :=
  RingHom.ext fun x => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem le_iff_fst {S : Type} [CommRing S] (v : Sp (DualNumber S) ⟶ X) (U : X.Opens) :
    ⊤ ≤ v ⁻¹ᵁ U ↔ ⊤ ≤ (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v) ⁻¹ᵁ U := by
  refine ⟨TanDeriv.comp_top_le _ _ _, TanDeriv.top_le_of_comp _ ?_ ?_ _ _⟩
  · intro y
    exact ⟨TrivSqZeroExt.inl y, rfl⟩
  · intro x hx
    have h1 : x.fst = 0 := hx
    ext <;> simp [h1]

open scoped LaurentSeries in

theorem cv_chart {Ω : Type} {p : Ω → ℂ} {R : Type} [CommRing R] (W : Sp (DualNumber R) ⟶ X) (V : X.Opens)
    (f : Γ(X, V)) (φ : R →+* ℂ⸨X⸩) (ψ : Ω → (R →+* ℂ)) (hc : ∀ r, Cv p (φ r) (fun ω => ψ ω r))
    (h : ⊤ ≤ (spMap (dualMap φ) ≫ W) ⁻¹ᵁ V) :
    (∀ᶠ ω in high p, ⊤ ≤ (spMap (dualMap (ψ ω)) ≫ W) ⁻¹ᵁ V) ∧
      Cv p (valR (spMap (dualMap φ) ≫ W) V f).snd (fun ω => (valR (spMap (dualMap (ψ ω)) ≫ W) V f).snd) := by
  rw [le_iff_fst, ← Category.assoc, TanMod.spMap_comp'] at h
  obtain ⟨H, r, h0, hr⟩ := exists_frac W V f _ h
  have h0' : φ H.fst ≠ 0 := by simpa [dualMap] using h0
  have key : ∀ (L : Type) [Field L] (χ : R →+* L), χ H.fst ≠ 0 → ⊤ ≤ (spMap (dualMap χ) ≫ W) ⁻¹ᵁ V ∧
      (valR (spMap (dualMap χ) ≫ W) V f).snd = (χ r.snd - χ r.fst * (χ H.fst)⁻¹ * χ H.snd) * (χ H.fst)⁻¹ := by
    intro L _ χ hχ
    obtain ⟨h1, h2⟩ := hr _ (dualMap χ) (by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simpa [dualMap] using hχ)
    refine ⟨h1, ?_⟩
    have h3 := congrArg TrivSqZeroExt.fst h2
    have h4 := congrArg TrivSqZeroExt.snd h2
    generalize valR (spMap (dualMap χ) ≫ W) V f = x at h3 h4
    simp [dualMap] at h3 h4
    rw [← h3, ← h4]
    field_simp
    ring
  obtain ⟨hne, hinv⟩ := (hc H.fst).inv h0'
  refine ⟨hne.mono fun ω hω => (key ℂ _ hω).1, ?_⟩
  rw [(key _ φ h0').2]
  exact (((hc _).sub (((hc _).mul hinv).mul (hc _))).mul hinv).congr (hne.mono fun ω hω => (key ℂ _ hω).2.symm)

end Local

section Group

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.HolHom GlobalTheory.TanMod

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} {f : X' ⟶ X} {φ : G'.left ⟶ G.left}

theorem isDerivAt0_lift (h : IsPullback φ G'.hom G.hom f) {g : ℕ} (x' : Sp ℂ ⟶ X')
    (e : (Fin g → ℂ) → (Sp ℂ ⟶ G'.left)) (he : ∀ z, e z ≫ G'.hom = x') (hol : IsHolTo Set.univ (fun z => e z ≫ φ))
    {w : Fin g → ℂ} (v : Sp (DualNumber ℂ) ⟶ G'.left) (hv : v ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x')
    (hd : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ)) : IsDerivAt0 e w v := by
  have H : IsPullback (pullback.fst G'.hom x' ≫ φ) (pullback.snd G'.hom x') G.hom (x' ≫ f) :=
    (IsPullback.of_hasPullback G'.hom x').paste_horiz h
  have h1 := FibreDeriv.isDerivAt0_of_isPullback H
    (e := fun z => pullback.lift (e z) (𝟙 _) (by rw [he, Category.id_comp])) (fun z => pullback.lift_snd _ _ _)
    (by simpa only [pullback.lift_fst_assoc] using hol) (w := w) (v := pullback.lift v _ hv)
    (pullback.lift_snd _ _ _) (by simpa only [pullback.lift_fst_assoc] using hd)
  simpa only [pullback.lift_fst] using FibreDeriv.isDerivAt0_comp h1 (pullback.fst G'.hom x')

variable [GrpObj G] [GrpObj G'] (h : IsGrpPullback G' G f φ)

def push (T : Over X') (t : T.left ⟶ X) (ht : T.hom ≫ f = t) : (T ⟶ G') →* (Over.mk t ⟶ G) :=
  MonoidHom.mk' (fun x => Over.homMk (x.left ≫ φ) (by
    change (x.left ≫ φ) ≫ G.hom = t
    rw [Category.assoc, h.1.w, ← ht, ← Category.assoc, Over.w])) fun x y => by
    subst ht
    exact Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

variable {S : Type} [CommRing S] {x' : Sp S ⟶ X'} {x : Sp S ⟶ X} (hx : x' ≫ f = x)
include h hx

theorem fst_lift (v : Sp (DualNumber S) ⟶ G'.left) (hv : v ≫ G'.hom = spMap (algebraMap S (DualNumber S)) ≫ x')
    (h1 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v ≫ φ = (1 : Over.mk x ⟶ G).left) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v = (1 : Over.mk x' ⟶ G').left := by
  refine h.1.hom_ext ?_ ?_
  · rw [Category.assoc, h1]
    exact (congrArg (fun z => z.left) (map_one (push h (Over.mk x') x hx))).symm
  · have hid : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S :=
      RingHom.ext fun r => by simp
    rw [Category.assoc, hv, ← Category.assoc, spMap_comp', hid]
    refine Eq.trans ?_ (Over.w (1 : Over.mk x' ⟶ G')).symm
    simp [spMap]

variable [IsCommMonObj G']

theorem snd_comb_lift {m : ℕ} (v : Fin m → (Sp (DualNumber S) ⟶ G'.left))
    (hv : ∀ i, v i ≫ G'.hom = spMap (algebraMap S (DualNumber S)) ≫ x')
    (h1 : ∀ i, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v i ≫ φ = (1 : Over.mk x ⟶ G).left)
    (a : Fin m → S) (w : Sp (DualNumber S) ⟶ G'.left) (hw : w ≫ G'.hom = spMap (algebraMap S (DualNumber S)) ≫ x')
    (u : Fin m → (Over.mk (spMap (algebraMap S (DualNumber S)) ≫ x) ⟶ G))
    (hu : ∀ i, (u i).left = spMap (epsMul (a i)) ≫ v i ≫ φ) (hp : (List.ofFn u).prod.left = w ≫ φ)
    (U : G'.left.Opens) (hU : ⊤ ≤ (show Sp S ⟶ G'.left from (1 : Over.mk x' ⟶ G').left) ⁻¹ᵁ U) (r : Γ(G'.left, U)) :
    (valR w U r).snd = ∑ i, a i * (valR (v i) U r).snd := by
  let b : Fin m → TanSp x' G' := fun i =>
    TanSp.mk (Over.homMk (v i) (hv i)) (smT_zero_of x' _ (fst_lift h hx _ (hv i) (h1 i)))
  have hw' : w = (∑ i, a i • b i).pt.left := by
    refine h.1.hom_ext ?_ (hw.trans (Over.w (∑ i, a i • b i).pt).symm)
    let Φ := push h (overAt x' (DualNumber S)) (spMap (algebraMap S (DualNumber S)) ≫ x)
      (by rw [← hx]; exact Category.assoc _ _ _)
    have hub : u = fun i => Φ (a i • b i).pt := funext fun i => Over.OverMorphism.ext
      ((hu i).trans (Category.assoc _ _ _).symm)
    have := map_list_prod Φ (List.ofFn fun i => (a i • b i).pt)
    rw [List.map_ofFn, List.prod_ofFn, ← TanSp.pt_sum] at this
    rw [← hp, hub]
    exact (congrArg (fun z => z.left) this).symm
  have h2 : ⊤ ≤ w ⁻¹ᵁ U := hw' ▸ TanDeriv.tan_top_le U hU _
  have h3 : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U := fun i => TanDeriv.tan_top_le U hU (b i)
  rw [valR_eq _ _ h2]
  simp only [fun i => valR_eq _ _ (h3 i) r]
  exact TanDeriv.derivAt_sum b a w hw' U h2 h3 r

end Group

section Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.HolHom GlobalTheory.TanMod GlobalTheory.ArcQ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
variable {S : Type} [CommRing S] [Algebra c.F S]

def ptF (y : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by rw [y.x_over, spMap_comp']; rfl)

theorem ptF_fst (y : FrPt Xo c S) : ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _

theorem ptF_snd (y : FrPt Xo c S) : ptF y ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _

theorem ptF_congr {y y' : FrPt Xo c S} (h : y'.x = y.x) : ptF y' = ptF y :=
  pullback.hom_ext (by rw [ptF_fst, ptF_fst, h]) (by rw [ptF_snd, ptF_snd])

def lf (y : FrPt Xo c S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (hw : IsTanAt y.x w) :
    Sp (DualNumber S) ⟶ Y.oF.t.G.left :=
  Y.m0.toSABMap.cart.1.lift w (spMap (algebraMap S (DualNumber S)) ≫ ptF y) (by rw [hw.1, Category.assoc, ptF_fst])

theorem lf_fst (y : FrPt Xo c S) (w) (hw : IsTanAt y.x w) : lf Y y w hw ≫ Y.m0.toSABMap.φ = w :=
  IsPullback.lift_fst _ _ _ _

theorem lf_snd (y : FrPt Xo c S) (w) (hw : IsTanAt y.x w) :
    lf Y y w hw ≫ Y.oF.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ ptF y :=
  IsPullback.lift_snd _ _ _ _

theorem eq_lf (y : FrPt Xo c S) (w) (hw : IsTanAt y.x w) (v : Sp (DualNumber S) ⟶ Y.oF.t.G.left)
    (h1 : v ≫ Y.m0.toSABMap.φ = w)
    (h2 : v ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap (algebraMap S (DualNumber S)) ≫ spMap (algebraMap c.F S)) :
    v = lf Y y w hw := by
  refine Y.m0.toSABMap.cart.1.hom_ext (h1.trans (lf_fst Y y w hw).symm) ?_
  rw [lf_snd]
  refine pullback.hom_ext ?_ (by rw [Category.assoc, h2, Category.assoc, ptF_snd])
  rw [Category.assoc, ← Y.m0.toSABMap.cart.1.w, ← Category.assoc]
  erw [h1]
  rw [hw.1, Category.assoc, ptF_fst]

def unitAt (z : Sp S ⟶ Xo.XF c) : Sp S ⟶ Y.t.G.left :=
  (show Sp S ⟶ Y.oF.t.G.left from (1 : Over.mk z ⟶ Y.oF.t.G).left) ≫ Y.m.φ

theorem lf_le_iff (y : FrPt Xo c S) (w) (hw : IsTanAt y.x w) (V : Y.t.G.left.Opens) :
    ⊤ ≤ (lf Y y w hw ≫ Y.m.φ) ⁻¹ᵁ V ↔ ⊤ ≤ unitAt Y (ptF y) ⁻¹ᵁ V := by
  rw [le_iff_fst, ← Category.assoc, fst_lift Y.m0.toSABMap.cart (ptF_fst y) _ (lf_snd Y y w hw)
    (by erw [lf_fst]; exact hw.2)]
  rfl

theorem snd_lf_comb (y : FrPt Xo c S) (τ : E →+* ℂ) (a : Fin (Dw.mult τ) → S) (w) (hw : IsTanAt y.x w)
    (hc : IsCombAt y.x (y.u τ) a w) (V : Y.t.G.left.Opens) (hV : ⊤ ≤ unitAt Y (ptF y) ⁻¹ᵁ V) (f : Γ(Y.t.G.left, V)) :
    (valR (lf Y y w hw ≫ Y.m.φ) V f).snd = ∑ k, a k * (valR (lf Y y _ (y.tan τ k) ≫ Y.m.φ) V f).snd := by
  obtain ⟨u, hu, hp⟩ := hc
  have e1 : ∀ k, lf Y y _ (y.tan τ k) ≫ Y.m0.toSABMap.φ = y.u τ k := fun k => lf_fst Y y _ _
  have h1 : ∀ k, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ lf Y y _ (y.tan τ k) ≫ Y.m0.toSABMap.φ =
      (1 : Over.mk y.x ⟶ Xo.univ.t.G).left := fun k => by rw [e1]; exact (y.tan τ k).2
  have h2 : ∀ k, (u k).left = spMap (epsMul (a k)) ≫ lf Y y _ (y.tan τ k) ≫ Y.m0.toSABMap.φ :=
    fun k => by rw [e1]; exact hu k
  have h3 : (List.ofFn u).prod.left = lf Y y w hw ≫ Y.m0.toSABMap.φ := hp.trans (lf_fst Y y w hw).symm
  have key := snd_comb_lift (φ := Y.m0.toSABMap.φ) Y.m0.toSABMap.cart (ptF_fst y) (fun k => lf Y y _ (y.tan τ k))
    (fun k => lf_snd Y y _ _) h1 a (lf Y y w hw) (lf_snd Y y w hw) u h2 h3 (Y.m.φ ⁻¹ᵁ V) hV ((Y.m.φ.app V).hom f)
  rw [valR_comp _ Y.m.φ, key]
  exact Finset.sum_congr rfl fun k _ => by rw [valR_comp _ Y.m.φ]

theorem lf_congr {y y' : FrPt Xo c S} (h : y'.x = y.x) (w) (hw : IsTanAt y.x w) (hw' : IsTanAt y'.x w) :
    lf Y y' w hw' = lf Y y w hw :=
  eq_lf Y y w hw _ (lf_fst Y _ _ _) (by rw [← Category.assoc, lf_snd, Category.assoc, ptF_snd])

theorem lf_map {T : Type} [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {y' : FrPt Xo c T}
    (h : FrMap φ y y') (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) :
    lf Y y' _ (y'.tan τ k) = spMap (dualMap φ.toRingHom) ≫ lf Y y _ (y.tan τ k) := by
  refine (eq_lf Y y' _ _ _ (by rw [Category.assoc, lf_fst, h.2.1]) ?_).symm
  rw [Category.assoc, ← Category.assoc (lf _ _ _ _), lf_snd, Category.assoc, ptF_snd]
  simp only [spMap_comp']
  rw [← RingHom.comp_assoc, dualMap_comp_algebraMap, RingHom.comp_assoc]
  congr 2
  exact φ.comp_algebraMap

theorem sep (y : FrPt Xo c S) (τ : E →+* ℂ) {V : Y.t.G.left.Opens} (hA : IsAffineOpen V)
    (hV : ⊤ ≤ unitAt Y (ptF y) ⁻¹ᵁ V) (a : Fin (Dw.mult τ) → S)
    (ha : ∀ f : Γ(Y.t.G.left, V), ∑ k, a k * (valR (lf Y y _ (y.tan τ k) ≫ Y.m.φ) V f).snd = 0) : a = 0 := by
  obtain ⟨N, _, _, ν, ρ, hinj, hr, hc, hρ, hs⟩ := exists_tangent_module E H Dw l Xo S y.x
  choose b hb using fun k => (hr _).1 (y.tan τ k)
  have hu : y.u τ = fun k => ν (b k) := funext fun k => (hb k).symm
  have ht : ∀ n, IsTanAt y.x (ν n) := fun n => (hr _).2 ⟨n, rfl⟩
  have hcomb : ∀ a', IsCombAt y.x (y.u τ) a' (ν (∑ k, a' k • b k)) := fun a' => by rw [hu, hc]
  have hle := (lf_le_iff Y y _ (ht (∑ k, a k • b k)) V).2 hV
  have h1 : spMap (epsMul (0 : S)) ≫ lf Y y _ (ht (∑ k, a k • b k)) = lf Y y _ (ht (∑ k, a k • b k)) := by
    refine Y.m.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc]
      refine point_ext hA (TanDeriv.comp_top_le _ _ _ hle) hle fun f => ?_
      have h2 := (snd_lf_comb Y y τ a _ (ht _) (hcomb a) V hV f).trans (ha f)
      refine (valR_spMap _ _ _ hle f).trans ?_
      refine TrivSqZeroExt.ext ?_ (Eq.trans ?_ h2.symm) <;> simp [epsMul]
    · rw [Category.assoc, lf_snd, ← Category.assoc, spMap_comp']
      congr 2
      refine RingHom.ext fun r => ?_
      ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have h2 : ∑ k, a k • b k = 0 := by
    have h3 := congrArg (· ≫ Y.m0.toSABMap.φ) h1
    simp only [Category.assoc, lf_fst] at h3
    rw [← hs, zero_smul] at h3
    exact (hinj h3).symm
  have he : IsEigAt c τ (ν 0) := fun x => by rw [← hρ, ← hs, map_zero, smul_zero]
  refine (y.basis τ _ (ht 0) he).unique (h2 ▸ hcomb a) ?_
  simpa using hcomb 0

end Frames

section ThetaShiftProofs

open AlgebraicGeometry CategoryTheory Limits NumberField Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.HolHom GlobalTheory.TanMod GlobalTheory.ArcQ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem thick_base {R : Type} [CommRing R] (I : Ideal R) (n : ℕ) {G : Over (Sp R)} (v : epsR R ⟶ G)
    (ρ : DualNumber R →+* DualNumber (R ⧸ I ^ (n + 1)))
    (vn : Sp (DualNumber (R ⧸ I ^ (n + 1))) ⟶ (Out.thickObj R I n G).left)
    (hρ : ∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Ideal.Quotient.mk _ r))
    (h : vn ≫ (Out.fstG I n G).left = spMap ρ ≫ v.left) :
    vn ≫ (Out.thickObj R I n G).hom = spMap (algebraMap (R ⧸ I ^ (n + 1)) (DualNumber (R ⧸ I ^ (n + 1)))) := by
  have : IsClosedImmersion (Out.thick R I n) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  rw [← cancel_mono (Out.thick R I n)]
  have h1 : (Out.thickObj R I n G).hom ≫ Out.thick R I n = (Out.fstG I n G).left ≫ G.hom := pullback.condition.symm
  have h2 : v.left ≫ G.hom = spMap (algebraMap R (DualNumber R)) := Over.w v
  rw [Category.assoc, h1, ← Category.assoc, h, Category.assoc, h2, spMap_comp']
  refine Eq.trans ?_ (spMap_comp' _ _).symm
  congr 1
  exact RingHom.ext hρ

theorem arc_lf {A : Type} [CommRing A] [IsDomain A] (s : c.F →+* A) {a : ArcIn Dw l β A (s.comp β)}
    {χ : Sp (PowerSeries A) ⟶ Y.X} {W : Wit Y a χ} {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    {th : a.D₀.P.L.Sec} {S : Type} [CommRing S] [Algebra c.F S] {ι : PowerSeries A →+* S} {y : FrPt Xo c S}
    (hι : ∀ x : c.F, algebraMap c.F S x = ι (PowerSeries.C (R := A) (s x)))
    (hχ : χ ≫ Y.s = spMap (PowerSeries.C (R := A)) ≫ spMap (s.comp β)) [Mono (spMap β)]
    (h : IsArcFr W e th ι y) (τ : E →+* ℂ) (k : Fin (Dw.mult τ)) :
    ∃ v : epsR (PowerSeries A) ⟶ W.t.G, LieImg W (e τ k) v ∧
      lf Y y _ (y.tan τ k) ≫ Y.m.φ = spMap (dualMap ι) ≫ (show Sp _ ⟶ _ from v.left) ≫ W.m.φ := by
  obtain ⟨z, t', m1, m2, φ, -, -, -, h1, h2, h3, -⟩ := h
  obtain ⟨v, u', hv, hu1, hu2, -⟩ := h3 τ k
  have e1 : (u' ≫ φ) ≫ Y.m.φ = spMap (dualMap ι) ≫ (show Sp _ ⟶ _ from v.left) ≫ W.m.φ := by
    rw [Category.assoc, h2, ← Category.assoc, hu2, Category.assoc]
  refine ⟨v, hv, ?_⟩
  rw [← e1]
  congr 1
  refine (eq_lf Y y _ _ _ (by rw [Category.assoc, h1, hu1]) ?_).symm
  rw [← cancel_mono (spMap β)]
  have e2 : Y.m.φ ≫ Y.t.G.hom ≫ Y.s = Y.oF.t.G.hom ≫ pullback.snd _ _ ≫ spMap β := by
    rw [← Category.assoc]
    erw [Y.m.cart.1.w]
    rw [Category.assoc, Category.assoc, pullback.condition (f := Y.s), ← Category.assoc Y.jQ, Y.jQ_over]
  have e3 : W.m.φ ≫ Y.t.G.hom = W.t.G.hom ≫ χ := W.m.cart.1.w
  have e4 : (show Sp _ ⟶ _ from v.left) ≫ W.t.G.hom = spMap (algebraMap _ (DualNumber (PowerSeries A))) := Over.w v
  rw [Category.assoc, Category.assoc Y.oF.t.G.hom, ← e2, ← Category.assoc, e1]
  simp only [Category.assoc]
  rw [← Category.assoc W.m.φ, e3, Category.assoc, hχ, ← Category.assoc (show Sp _ ⟶ _ from v.left), e4]
  simp only [spMap_comp']
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap, hι, TrivSqZeroExt.algebraMap_eq_inl]

theorem isHolTo_slice {X : Scheme.{0}} {g : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : IsHolTo (Set.univ ×ˢ Set.univ) (fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => e bz.2)) : IsHolTo Set.univ e := by
  refine isHolTo_of_holAt isOpen_univ fun w _ => ?_
  have h4 : DifferentiableAt ℂ (fun w : Fin g → ℂ => ((0 : Fin 0 → ℂ), w)) w := by fun_prop
  have h5 := holAt_of_isHolTo h (z := ((0 : Fin 0 → ℂ), w)) ⟨trivial, trivial⟩
  exact HolAt.precomp (c := fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => e bz.2)
    (k := fun w : Fin g → ℂ => ((0 : Fin 0 → ℂ), w)) h5 h4

theorem exists_exp_lift (Y : Model Xo c β) {σ : c.F →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty P) (y : FrPt Xo c (CAt σ))
    (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)) (h : AnLie Fu i P y z) :
    ∃ xF : (Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left), (∀ w, xF w ≫ Y.m0.toSABMap.φ = (Fu.ex i P w).left ∧
      xF w ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ) ∧
      ∀ τ k, IsDerivAt0 xF (z τ k) (lf (S := CAt σ) Y y _ (y.tan τ k)) := by
  let x' : Sp ℂ ⟶ Xo.XF c := ptF (S := CAt σ) y
  have hx : x' ≫ pullback.fst _ _ = Fu.u i P := (ptF_fst (S := CAt σ) y).trans h.1
  have hx2 : x' ≫ pullback.snd _ _ = spMap σ := ptF_snd (S := CAt σ) y
  let xF : (Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left) := fun w =>
    Y.m0.toSABMap.cart.1.lift (Fu.ex i P w).left x' ((Over.w (Fu.ex i P w)).trans hx.symm)
  have h1 : ∀ w, xF w ≫ Y.m0.toSABMap.φ = (Fu.ex i P w).left := fun w => IsPullback.lift_fst _ _ _ _
  have h2 : ∀ w, xF w ≫ Y.oF.t.G.hom = x' := fun w => IsPullback.lift_snd _ _ _ _
  have hol : IsHolTo Set.univ (fun w => (show Sp ℂ ⟶ _ from (Fu.ex i P w).left)) :=
    isHolTo_slice (fun w => (Fu.ex i P w).left) (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
      ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  refine ⟨xF, fun w => ⟨h1 w, by rw [← Category.assoc, h2, hx2]⟩, fun τ k => ?_⟩
  have h4 : (fun w => xF w ≫ Y.m0.toSABMap.φ) = fun w => (show Sp ℂ ⟶ _ from (Fu.ex i P w).left) := funext h1
  refine isDerivAt0_lift (φ := Y.m0.toSABMap.φ) Y.m0.toSABMap.cart.1 x' xF h2 (h4 ▸ hol) _ (lf_snd (S := CAt σ) Y y _ _) ?_
  rw [h4]
  exact (lf_fst (S := CAt σ) Y y _ (y.tan τ k)).symm ▸ h.2 τ k

end ThetaShiftProofs

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem frame_matrix_hasSum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)) (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R) (φ : p.R →ₐ[c.F] ℂ⸨X⸩) (y₁ : FrPt Xo c ℂ⸨X⸩) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ⸨X⸩) (s : ℂ⸨X⸩), (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ k, AnVec Ha (e τ k) (z τ k)) → OpenChart j y₀ → FrMap φ y₀ y₁ → FrChg G s y₁ y → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ (ψ : p.R →ₐ[c.F] CAt σ) (yw₁ yw : FrPt Xo c (CAt σ)) (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ), (∀ f : p.R, HasSum (fun m : ℤ => (φ f).coeff m * eTwoPi w ^ m) (toC (ψ f))) → FrMap ψ y₀ yw₁ → AnLie Fu Ha.i (Ha.Pw w) yw z → FrChg Gw sw yw₁ yw → ∀ τ i k, HasSum (fun m : ℤ => (G τ i k).coeff m * eTwoPi w ^ m) (toC (Gw τ i k)) := by
  intro _ _ E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ y e th z p j y₀ φ y₁ G s halg hχ hβ hy hz _ hφ hG
  let Ω : Type := {q : ℂ × (p.R →ₐ[c.F] CAt σ) × FrPt Xo c (CAt σ) × FrPt Xo c (CAt σ) ×
      (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) × CAt σ //
    (∀ f : p.R, HasSum (fun m : ℤ => (φ f).coeff m * eTwoPi q.1 ^ m) (toC (q.2.1 f))) ∧ FrMap q.2.1 y₀ q.2.2.1 ∧
      AnLie Fu Ha.i (Ha.Pw q.1) q.2.2.2.1 z ∧ FrChg q.2.2.2.2.1 q.2.2.2.2.2 q.2.2.1 q.2.2.2.1}
  let pw : Ω → ℂ := fun ω => ω.1.1
  suffices hs : ∀ τ i k, Cv pw (G τ i k) (fun ω => toC (ω.1.2.2.2.2.1 τ i k)) by
    obtain ⟨T, hT⟩ := high_iff.1 (Filter.eventually_all.2 fun τ => Filter.eventually_all.2 fun i =>
      Filter.eventually_all.2 fun k => hs τ i k)
    exact ⟨T, fun w hw ψ yw₁ yw Gw sw h1 h2 h3 h4 => hT ⟨(w, ψ, yw₁, yw, Gw, sw), h1, h2, h3, h4⟩ hw⟩
  intro τ i
  obtain ⟨v, hv, hvy⟩ := arc_lf σ halg hχ hy τ i
  let v' : Sp (DualNumber (PowerSeries ℂ)) ⟶ Y.t.G.left := (show Sp _ ⟶ _ from v.left) ≫ W.m.φ
  obtain ⟨V, hV, hpV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y.t.G.left) (U := ⊤)
    (x := (spMap (TrivSqZeroExt.fstHom (PowerSeries ℂ) (PowerSeries ℂ) (PowerSeries ℂ)).toRingHom ≫ v') (IsLocalRing.closedPoint (PowerSeries ℂ))) trivial
  have hvV : ⊤ ≤ v' ⁻¹ᵁ V := (le_iff_fst v' V).2
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of (PowerSeries ℂ)) _ hpV).ge
  have hyV : ⊤ ≤ unitAt Y (ptF y₁) ⁻¹ᵁ V := by
    rw [← ptF_congr hG.1, ← lf_le_iff Y y _ (y.tan τ i), hvy]
    exact TanDeriv.comp_top_le _ _ _ hvV
  let ψ : Ω → (p.R →+* ℂ) := fun ω => ω.1.2.1.toRingHom
  have hψ : ∀ r, Cv pw (φ.toRingHom r) (fun ω => ψ ω r) := fun r => Filter.Eventually.of_forall fun ω => ω.2.1 r
  have e₁ : ∀ k, lf Y y₁ _ (y₁.tan τ k) ≫ Y.m.φ = spMap (dualMap φ.toRingHom) ≫ lf Y y₀ _ (y₀.tan τ k) ≫ Y.m.φ :=
    fun k => by rw [lf_map Y hφ, Category.assoc]
  have e₂ : ∀ (ω : Ω) k, (show Sp (DualNumber ℂ) ⟶ _ from lf (S := CAt σ) Y ω.1.2.2.1 _ (ω.1.2.2.1.tan τ k) ≫ Y.m.φ) =
      spMap (dualMap (ψ ω)) ≫ lf Y y₀ _ (y₀.tan τ k) ≫ Y.m.φ :=
    fun ω k => (congrArg (· ≫ Y.m.φ) (lf_map Y ω.2.2.1 τ k)).trans (Category.assoc _ _ _)
  have hch := fun (f : Γ(Y.t.G.left, V)) k => cv_chart (lf Y y₀ _ (y₀.tan τ k) ≫ Y.m.φ) V f φ.toRingHom ψ hψ
    (e₁ k ▸ (lf_le_iff Y y₁ _ (y₁.tan τ k) V).2 hyV)
  have hwV : ∀ᶠ ω in high pw, ⊤ ≤ unitAt Y (ptF ω.1.2.2.1) ⁻¹ᵁ V :=
    (hch 0 i).1.mono fun ω hω => (lf_le_iff Y _ _ (ω.1.2.2.1.tan τ i) V).1 (by rw [← e₂] at hω; exact hω)
  refine cv_coeff (F := Γ(Y.t.G.left, V))
    (A := fun f k => (valR (lf Y y₁ _ (y₁.tan τ k) ≫ Y.m.φ) V f).snd)
    (B := fun f => (valR (lf Y y _ (y.tan τ i) ≫ Y.m.φ) V f).snd)
    (Aw := fun f k ω => toC (valR (lf Y ω.1.2.2.1 _ (ω.1.2.2.1.tan τ k) ≫ Y.m.φ) V f).snd)
    (Bw := fun f ω => toC (valR (lf Y ω.1.2.2.2.1 _ (ω.1.2.2.2.1.tan τ i) ≫ Y.m.φ) V f).snd)
    (fun f => ?_) (sep Y y₁ τ hV hyV) (fun f k => ?_) (fun f => ?_) (fun f => ?_)
  · rw [lf_congr Y hG.1 _ (hG.1 ▸ y.tan τ i)]
    exact snd_lf_comb Y y₁ τ _ _ _ (hG.2.1 τ i) V hyV f
  · have h1 := (hch f k).2
    rw [← e₁] at h1
    refine h1.congr (Filter.Eventually.of_forall fun ω => ?_)
    rw [← e₂]
    rfl
  · obtain ⟨T, hT⟩ := Ha.diff (z τ i) (e τ i) v V f (hz τ i).1 (hz τ i).2
      (fun n ρ κ vn h1 h2 h3 h4 h5 => hv n ρ κ vn h1 h2 h3 h4 (thick_base _ n v ρ vn h1 h5) h5) hvV
    have hB : (valR (lf Y y _ (y.tan τ i) ≫ Y.m.φ) V f).snd = HahnSeries.ofPowerSeries ℤ ℂ (valR v' V f).snd := by
      rw [hvy, HolHom.valR_spMap _ _ _ hvV]
      simp [dualMap]
    rw [hB]
    filter_upwards [high_iff.2 ⟨T, fun _ h => h⟩, high_iff.2 ⟨Ha.T, fun _ h => h⟩, hwV] with ω h1 h2 h3
    obtain ⟨xF, hx, hd⟩ := exists_exp_lift Y Fu Ha.i _ (Ha.period _ h2) _ z ω.2.2.2.1
    have h4 : ⊤ ≤ (lf Y ω.1.2.2.2.1 _ (ω.1.2.2.2.1.tan τ i) ≫ Y.m.φ) ⁻¹ᵁ V := by
      rw [lf_le_iff, ptF_congr ω.2.2.2.2.1]
      exact h3
    have h5 := (FibreDeriv.isDerivAt0_comp (hd τ i) Y.m.φ).2 V h4 f
    have h6 := Conv.sumsAt_iff.1 (hT _ h1 xF hx)
    rw [← h5] at h6
    rw [HolHom.valR_eq _ _ h4]
    exact h6
  · filter_upwards [hwV] with ω h3
    have hGw := ω.2.2.2.2
    rw [lf_congr Y hGw.1 _ (hGw.1 ▸ ω.1.2.2.2.1.tan τ i)]
    exact snd_lf_comb Y ω.1.2.2.1 τ _ _ _ (hGw.2.1 τ i) V h3 f

end GlobalTheory.ArcLie
