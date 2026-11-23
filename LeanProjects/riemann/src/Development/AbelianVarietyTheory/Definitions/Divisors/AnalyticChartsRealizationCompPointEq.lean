import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer

open CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

theorem isDPMorphism_of_rat {C C' : Type} [CommRing C] [CommRing C'] [Algebra ℚ C'] {J : Ideal C} {J' : Ideal C'}
    (δ : DividedPowers J) (δ' : DividedPowers J') (φ : C →+* C') (h : ∀ c ∈ J, φ c ∈ J') : IsDPMorphism δ δ' φ := by
  refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 h, fun n _ a ha ↦ ?_⟩
  have hu : IsUnit ((n.factorial : ℕ) : C') := by
    have := (IsUnit.mk0 (n.factorial : ℚ) (by exact_mod_cast n.factorial_ne_zero)).map (algebraMap ℚ C')
    simpa using this
  refine hu.mul_left_cancel ?_
  rw [δ'.factorial_mul_dpow_eq_pow (h a ha), ← map_pow, ← δ.factorial_mul_dpow_eq_pow ha, map_mul, map_natCast]

theorem isPDNilpotent_of_rat {C : Type} [CommRing C] [Algebra ℚ C] {J : Ideal C} (δ : DividedPowers J)
    (h : IsNilpotent J) : IsNilDP δ := by
  obtain ⟨N, hN⟩ := h
  have key : ∀ l : List (ℕ × C), (∀ p ∈ l, p.2 ∈ J) →
      (l.map fun p ↦ δ.dpow p.1 p.2).prod ∈ J ^ (l.map Prod.fst).sum := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      intro hl
      have hp : p.2 ∈ J := hl p (by simp)
      simp only [List.map_cons, List.sum_cons, List.prod_cons, pow_add]
      refine Ideal.mul_mem_mul ?_ (ih fun q hq ↦ hl q (by simp [hq]))
      have hu : IsUnit ((p.1.factorial : ℕ) : C) := by
        have := (IsUnit.mk0 (p.1.factorial : ℚ) (by exact_mod_cast p.1.factorial_ne_zero)).map (algebraMap ℚ C)
        simpa using this
      rw [← Ideal.unit_mul_mem_iff_mem _ hu, δ.factorial_mul_dpow_eq_pow hp]
      exact Ideal.pow_mem_pow hp _
  refine ⟨N, fun l hl hs ↦ ?_⟩
  have := Ideal.pow_le_pow_right hs (key l hl)
  rwa [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
  {B : Type} [CommRing B] {X : Scheme.{0}}

@[reducible] def Charts.Obj.ratAlg {K : Charts F} (T : K.Obj) : Algebra ℚ T.C :=
  ((algebraMap (Hol F.V) T.C).comp ((algebraMap ℂ (Hol F.V)).comp (algebraMap ℚ ℂ))).toAlgebra

open Classical in

def Charts.Obj.δ {K : Charts F} (T : K.Obj) : DividedPowers T.J :=
  letI := T.ratAlg
  RatAlgebra.dividedPowers T.J

structure Unif (F : Fam I g Λ) (s : X ⟶ Sp B) (σ : B →+* Hol F.V) where

  E : Tot I g → (Sp ℂ ⟶ X)
  w : ∀ (p : Tot I g) (hp : p.1 ∈ F.V), E p ≫ s = spMap ((Hol.ev p.1 hp).toRingHom.comp σ)
  per : ∀ (l : Λ) (p : Tot I g), p.1 ∈ F.V → E (F.shift l p) = E p
  hol : ∀ (U : X.Opens) (f : Γ(X, U)), IsOpen {p : Tot I g | p.1 ∈ F.V ∧ ⊤ ≤ E p ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun p ↦ valAt' (E p) U f) {p : Tot I g | p.1 ∈ F.V ∧ ⊤ ≤ E p ⁻¹ᵁ U}

def Unif.Based {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) : Prop :=
  ∃ U : X.Opens, IsAffineOpen U ∧ ∀ z ∈ F.V, ⊤ ≤ u.E (z, 0) ⁻¹ᵁ U

structure Real (K : Charts F) (s : X ⟶ Sp B) (σ : B →+* Hol F.V) where

  x : ∀ k, Sp (Hol (K.W k)) ⟶ X
  w : ∀ k, x k ≫ s = spMap ((K.cst k).comp σ)
  compat : ∀ {l k k'} (h : K.le l k' k), spMap (Charts.sh h) ≫ x k = x k'

namespace Real

variable {K : Charts F} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (r : Real K s σ)

def IsFor (u : Unif F s σ) : Prop :=
  ∀ k (p : Tot I g) (hp : p ∈ K.W k), spMap (Hol.ev p hp).toRingHom ≫ r.x k = u.E p

def obj (T : K.Obj) : Thick (dp0 B) s where
  B := T.C
  alg := ((algebraMap (Hol F.V) T.C).comp σ).toAlgebra
  J := T.J
  δ := T.δ
  nil := letI := T.ratAlg; isPDNilpotent_of_rat _ T.nil
  dp := isDPMorphism_of_eq_bot _ rfl _ _
  B₀ := T.C ⧸ T.J
  π := Ideal.Quotient.mk T.J
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ r.x T.k
  w := by
    rw [Category.assoc, r.w, ← Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun b ↦ congrArg (Ideal.Quotient.mk T.J) (T.ρ_cst (σ b))

theorem analyticChartsRealization_comp_point_eq {T T' : K.Obj} (f : T ⟶ T') :
    spMap (Ideal.quotientMap T'.J (f.φ : T.C →+* T'.C) f.mem) ≫ spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ r.x T.k =
      spMap ((Ideal.Quotient.mk T'.J).comp T'.ρ) ≫ r.x T'.k := by
  have e : (Ideal.quotientMap T'.J (f.φ : T.C →+* T'.C) f.mem).comp ((Ideal.Quotient.mk T.J).comp T.ρ) =
      ((Ideal.Quotient.mk T'.J).comp T'.ρ).comp (Charts.sh (Charts.Hom.le f)) :=
    RingHom.ext fun h ↦ Ideal.Quotient.eq.2 (f.close.sub_mem h)
  rw [← r.compat (Charts.Hom.le f), ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp, e]

def functor : K.Obj ⥤ Thick (dp0 B) s where
  obj := r.obj
  map {T T'} f :=
    { φ := { (f.φ : T.C →+* T'.C) with commutes' := fun b ↦ f.φ.commutes (σ b) }
      φ₀ := Ideal.quotientMap T'.J (f.φ : T.C →+* T'.C) f.mem
      comm := fun _ ↦ rfl
      dp := letI := T'.ratAlg; isDPMorphism_of_rat T.δ T'.δ (f.φ : T.C →+* T'.C) f.mem
      pt := r.analyticChartsRealization_comp_point_eq f }

def coef : CoefMap σ (O (dp0 B) s) K.Oc where
  G := r.functor
  α T := RingHom.id T.C
  naturality _ _ := rfl
  smul T b c := (Algebra.smul_def (A := T.C) (σ b) c).symm

end Real

def IsPeriod {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) (c : FirstDeRham s) (per : Λ →+ Hol F.V) : Prop :=
  ∀ (K : Charts F) (r : Real K s σ), r.IsFor u → r.coef.pull1 c = K.perCl per

namespace MulGrp

open ReciprocityTheory.ChartRestriction.G.TB.ValAt Polynomial

theorem top_le_preimage {Y : Scheme.{0}} {x : Sp ℂ ⟶ Y} {U : Y.Opens} {p : Sp ℂ} (h : x p ∈ U) : ⊤ ≤ x ⁻¹ᵁ U :=
  fun q _ ↦ by
    rw [show q = p from Subsingleton.elim (α := PrimeSpectrum ℂ) q p]
    exact h

theorem isHolTo_affine {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {T : Scheme.{0}} [IsAffine T] {D : Set V}
    (hD : IsOpen D) {z : V → (Sp ℂ ⟶ T)}
    (hz : ∀ r : Γ(T, ⊤), DifferentiableOn ℂ (fun b ↦ valAt' (z b) ⊤ r) D) : IsHolTo D z := by
  intro U f
  let p : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have key : ∀ b₀ ∈ {b ∈ D | ⊤ ≤ z b ⁻¹ᵁ U}, ∃ N ∈ 𝓝 b₀, N ⊆ {b ∈ D | ⊤ ≤ z b ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun b ↦ valAt' (z b) U f) N := by
    rintro b₀ ⟨hb₀, hU⟩
    obtain ⟨r, hrU, hr0⟩ := (isAffineOpen_top T).exists_basicOpen_le (V := U) ⟨z b₀ p, hU (Set.mem_univ _)⟩ trivial
    have htop : ∀ b, ⊤ ≤ z b ⁻¹ᵁ (⊤ : T.Opens) := fun b p _ ↦ trivial
    have hNo : IsOpen {b ∈ D | valAt' (z b) ⊤ r ≠ 0} := (hz r).continuousOn.isOpen_inter_preimage hD isOpen_ne
    have hm : ∀ b, valAt' (z b) ⊤ r ≠ 0 → ⊤ ≤ z b ⁻¹ᵁ T.basicOpen r := fun b hb ↦
      top_le_preimage ((valAt'_ne_zero_iff (z b) ⊤ (htop b) r p).1 hb)
    obtain ⟨⟨a, s⟩, hk⟩ := IsLocalization.surj (Submonoid.powers r) (T.presheaf.map (homOfLE hrU).op f)
    obtain ⟨k, hks⟩ := s.2
    dsimp only at hk
    refine ⟨_, hNo.mem_nhds ⟨hb₀, (valAt'_ne_zero_iff (z b₀) ⊤ (htop b₀) r p).2 hr0⟩,
      fun b hb ↦ ⟨hb.1, (hm b hb.2).trans (Scheme.Hom.preimage_mono _ hrU)⟩, ?_⟩
    have hs : {b ∈ D | valAt' (z b) ⊤ r ≠ 0} ⊆ D := fun _ hb ↦ hb.1
    have hq : DifferentiableOn ℂ (fun b ↦ valAt' (z b) ⊤ a * (valAt' (z b) ⊤ r ^ k)⁻¹) {b ∈ D | valAt' (z b) ⊤ r ≠ 0} :=
      ((hz a).mono hs).mul ((((hz r).mono hs).pow k).inv fun b hb ↦ pow_ne_zero _ hb.2)
    refine hq.congr fun b hb ↦ ?_
    have e := congrArg (valAt' (z b) (T.basicOpen r)) hk
    have e2 : ∀ x : Γ(T, ⊤), valAt' (z b) (T.basicOpen r) (algebraMap Γ(T, ⊤) Γ(T, T.basicOpen r) x) =
        valAt' (z b) ⊤ x := fun x ↦ valAt'_res (z b) le_top (hm b hb.2) x
    have e3 : valAt' (z b) ⊤ (r ^ k) = valAt' (z b) ⊤ r ^ k := map_pow (valHom (z b) ⊤ (htop b)) r k
    rw [valAt'_mul, valAt'_res (z b) hrU (hm b hb.2), e2, e2, ← hks, e3] at e
    exact (eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hb.2)).2 e
  refine ⟨isOpen_iff_mem_nhds.2 fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · obtain ⟨N, hN, hs, -⟩ := key b hb
    exact mem_of_superset hN hs
  · obtain ⟨N, hN, -, hd⟩ := key b hb
    exact (hd.differentiableAt hN).differentiableWithinAt

theorem valAt'_spMap {R : Type} [CommRing R] (ψ : R →+* ℂ) (t : R) :
    valAt' (spMap ψ) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t) = ψ t := by
  have h : ⊤ ≤ (spMap ψ) ⁻¹ᵁ ⊤ := le_top
  rw [valAt', dif_pos h, valAt]
  have e : (spMap ψ).appLE ⊤ ⊤ h = (spMap ψ).appTop := (spMap ψ).appLE_eq_app
  have n := congrArg (fun φ ↦ φ.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  rw [e]
  erw [← n]
  exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply _

theorem perCl_injective (F : Fam I g Λ) : Function.Injective F.allCharts.perCl := by
  intro per per' h
  obtain ⟨G, hG⟩ := H1.mk_eq_mk.1 h
  let G₀ : Hol (F.allCharts.W F.totChart) := G (F.allCharts.triv F.totChart)
  have hd : ∀ a (p : Tot I g) (hp : p ∈ F.allCharts.W F.totChart), (dw a G₀).fn p = 0 := fun a p hp ↦ by
    have h0 := congrFun (congrFun (congrFun hG _) _)
      (Charts.ptHom (F.allCharts.dualAt F.totChart p hp) (F.allCharts.le_refl F.totChart))
    have h1 := congrFun (congrFun (congrFun hG _) _) (F.allCharts.tangentHom F.totChart a p hp)
    have h2 : (TrivSqZeroExt.inl (Hol.ev p hp (Charts.sh (F.allCharts.le_refl F.totChart) G₀)) : DualNumber ℂ) =
        tangentAt a p hp G₀ :=
      sub_right_injective (G := F.allCharts.Oc.obj (F.allCharts.dualAt F.totChart p hp)) (h0.trans h1.symm)
    have h3 := congrArg TrivSqZeroExt.snd h2
    rw [← Hol.ev_apply p hp]
    simpa [tangentAt] using h3.symm
  have hc : ∀ z ∈ F.V, ∀ w w', G₀.fn (z, w) = G₀.fn (z, w') := fun z hz w w' ↦ by
    have hf : ∀ w, HasFDerivAt (fun w ↦ G₀.fn (z, w)) (0 : (Fin g → ℂ) →L[ℂ] ℂ) w := fun w ↦ by
      have k := (G₀.analytic (z, w) hz).differentiableAt.hasFDerivAt.comp w (hasFDerivAt_prodMk_right (𝕜 := ℂ) z w)
      refine k.congr_fderiv ?_
      apply ContinuousLinearMap.coe_injective
      refine LinearMap.pi_ext' fun a ↦ LinearMap.ext_ring ?_
      have := (Hol.fn_der ((0, Pi.single a 1) : Tot I g) G₀ (p := (z, w)) hz).symm.trans (hd a (z, w) hz)
      simpa using this
    exact is_const_of_fderiv_eq_zero (𝕜 := ℂ) (fun w ↦ (hf w).differentiableAt) (fun w ↦ (hf w).fderiv) w w'
  refine AddMonoidHom.ext fun l ↦ Hol.ext_fn fun z hz ↦ ?_
  have h3 := congrFun (congrFun (congrFun hG _) _) (F.transl l)
  have hl : F.allCharts.le l F.totChart F.totChart := fun _ h ↦ h
  change G₀ - Charts.sh hl G₀ = F.allCharts.cst F.totChart (per l) - F.allCharts.cst F.totChart (per' l) at h3
  have hp : ((z, 0) : Tot I g) ∈ F.allCharts.W F.totChart := hz
  have h4 := congrArg (Hol.ev _ hp) h3
  simp only [map_sub, Hol.ev_apply, Charts.fn_cst _ _ _ hp] at h4
  rw [Charts.fn_sh _ _ hp, Fam.shift, hc z hz 0 (0 + F.τ l z), sub_self] at h4
  exact sub_eq_zero.1 h4.symm

variable (I) in

def fam : Fam I 1 ℤ where
  V := ⊤
  τ := { toFun l := fun _ _ ↦ l * (2 * Real.pi * Complex.I)
         map_zero' := by funext _ _; simp
         map_add' l m := by funext _ _; simp [add_mul] }
  hol _ := analyticOnNhd_const

variable (B) in

abbrev Ring : Type := Localization.Away (Polynomial.X : B[X])

variable (B) in

abbrev str : Sp (Ring B) ⟶ Sp B := spMap (algebraMap B (Ring B))

variable (B) in

def coord : Ring B := algebraMap B[X] (Ring B) Polynomial.X

def pt {C : Type} [CommRing C] (σ : B →+* C) (e : C) (h : IsUnit e) : Ring B →+* C :=
  IsLocalization.Away.lift (Polynomial.X : B[X]) (g := eval₂RingHom σ e) (by simpa using h)

theorem pt_const {C : Type} [CommRing C] (σ : B →+* C) (e : C) (h : IsUnit e) :
    (pt σ e h).comp (algebraMap B (Ring B)) = σ := RingHom.ext fun b ↦ by
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply B B[X] (Ring B), pt, IsLocalization.Away.lift_eq]
  simp

theorem pt_coord {C : Type} [CommRing C] (σ : B →+* C) (e : C) (h : IsUnit e) : pt σ e h (coord B) = e :=
  (IsLocalization.Away.lift_eq _ _ _).trans (eval₂_X _ _)

theorem comp_pt {C C' : Type} [CommRing C] [CommRing C'] (φ : C →+* C') {σ : B →+* C} {e : C} (h : IsUnit e)
    {σ' : B →+* C'} {e' : C'} (h' : IsUnit e') (hσ : ∀ b, φ (σ b) = σ' b) (he : φ e = e') :
    φ.comp (pt σ e h) = pt σ' e' h' :=
  IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : B[X])) (Polynomial.ringHom_ext
    (fun b ↦ by simp [pt, hσ]) (by simp [pt, he]))

theorem analyticAt_fibre (p : Tot I 1) : AnalyticAt ℂ (fun p : Tot I 1 ↦ p.2 0) p :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt _).comp analyticAt_snd

def expFn (W : Opens (Tot I 1)) : Hol W :=
  Hol.mk (fun p ↦ Complex.exp (p.2 0)) fun p _ ↦ (analyticAt_fibre p).cexp'

theorem isUnit_expFn (W : Opens (Tot I 1)) : IsUnit (expFn W) :=
  IsUnit.of_mul_eq_one (Hol.mk (fun p ↦ Complex.exp (-p.2 0)) fun p _ ↦ (analyticAt_fibre p).neg.cexp')
    (Subtype.ext (funext fun p ↦ by
      change Complex.exp _ * Complex.exp _ = 1
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]))

variable (σ : B →+* Hol (fam I).V)

def real (K : Charts (fam I)) : Real K (str B) σ where
  x k := spMap (pt ((K.cst k).comp σ) (expFn (K.W k)) (isUnit_expFn _))
  w _ := by rw [← Cris.spMap_comp, pt_const]
  compat {l k k'} h := by
    rw [← Cris.spMap_comp]
    refine congrArg spMap (comp_pt _ _ _ (fun b ↦ Charts.sh_cst h _) (Subtype.ext (funext fun p ↦ ?_)))
    change Complex.exp (p.1.2 0 + l * (2 * Real.pi * Complex.I)) = Complex.exp (p.1.2 0)
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

def expPt (p : Tot I 1) : Ring B →+* ℂ :=
  pt ((Hol.ev (W := (fam I).V) p.1 trivial).toRingHom.comp σ) (Complex.exp (p.2 0)) (Complex.exp_ne_zero _).isUnit

theorem ev_comp_pt (K : Charts (fam I)) (k : K.K) (p : Tot I 1) (hp : p ∈ K.W k) :
    (Hol.ev p hp).toRingHom.comp (pt ((K.cst k).comp σ) (expFn (K.W k)) (isUnit_expFn _)) = expPt σ p :=
  comp_pt _ _ _ (fun _ ↦ rfl) rfl

def unif : Unif (fam I) (str B) σ where
  E p := spMap (expPt σ p)
  w p hp := by rw [← Cris.spMap_comp, expPt, pt_const]
  per l p _ := by
    have : Complex.exp (((fam I).shift l p).2 0) = Complex.exp (p.2 0) := by
      change Complex.exp (p.2 0 + l * (2 * Real.pi * Complex.I)) = Complex.exp (p.2 0)
      rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    simp only [expPt, this]
    rfl
  hol := isHolTo_affine (D := {p : Tot I 1 | p.1 ∈ (fam I).V}) isOpen_univ fun r ↦ by
    obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (Ring B))).inv).2 r
    refine (pt (((fam I).allCharts.cst (fam I).totChart).comp σ) (expFn _) (isUnit_expFn _) a).analytic.differentiableOn.congr
      fun p hp ↦ (valAt'_spMap _ a).trans ?_
    rw [← ev_comp_pt σ (fam I).allCharts (fam I).totChart p hp]
    exact Hol.ev_apply p hp _

theorem isFor (K : Charts (fam I)) : (real σ K).IsFor (unif σ) := fun k p hp ↦
  (Cris.spMap_comp _ _).symm.trans (congrArg spMap (ev_comp_pt σ K k p hp))

theorem based : (unif σ).Based := ⟨⊤, isAffineOpen_top _, fun _ _ ↦ le_top⟩

theorem unif_ne (z : I → ℂ) : (unif σ).E (z, 0) ≠ (unif σ).E (z, fun _ ↦ Real.pi * Complex.I) := fun h ↦ by
  have e := congrArg (fun φ ↦ φ.hom (coord B)) (Spec.map_injective h)
  simp only [CommRingCat.hom_ofHom, expPt, pt_coord] at e
  simp at e
  norm_num at e

theorem isPeriod_unique {c : FirstDeRham (str B)} {per per' : ℤ →+ Hol (fam I).V} (h : IsPeriod (unif σ) c per)
    (h' : IsPeriod (unif σ) c per') : per = per' :=
  perCl_injective _ ((h _ _ (isFor σ _)).symm.trans (h' _ _ (isFor σ _)))

end MulGrp

theorem isPeriod_zero_zero {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) : IsPeriod u 0 0 := fun K r _ ↦ by
  rw [map_zero]
  refine (H1.mk_eq_zero.2 ⟨0, ?_⟩).symm
  rw [map_zero]
  funext T T' f
  exact (@map_zero _ _ _ _ _ _ _ (@algebraMap _ T'.C _ _ T'.alg)).symm

example (σ : B →+* Hol (MulGrp.fam I).V) (per : ℤ →+ Hol (MulGrp.fam I).V) :
    IsPeriod (MulGrp.unif σ) 0 per ↔ per = 0 :=
  ⟨fun h ↦ MulGrp.isPeriod_unique σ h (isPeriod_zero_zero _), fun e ↦ e ▸ isPeriod_zero_zero _⟩

example : ∃ (u : Unif (MulGrp.fam Unit) (MulGrp.str ℂ) (algebraMap ℂ _)) (K : Charts (MulGrp.fam Unit))
    (r : Real K (MulGrp.str ℂ) (algebraMap ℂ _)), u.Based ∧ K.Rich ∧ K.Based ∧ r.IsFor u ∧ ∃ p q, u.E p ≠ u.E q :=
  ⟨MulGrp.unif _, _, MulGrp.real _ _, MulGrp.based _, Fam.allCharts_rich _, Fam.allCharts_based _, MulGrp.isFor _ _,
    _, _, MulGrp.unif_ne _ 0⟩

end GlobalTheory.AnPer
