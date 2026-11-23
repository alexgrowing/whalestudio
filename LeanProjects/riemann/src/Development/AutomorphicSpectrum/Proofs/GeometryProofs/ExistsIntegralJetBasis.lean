import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecMapCompAppLE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationHolUnifTangentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IteratedDerivativeFactorStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionRatioOverlapStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.JetMain

open Filter

theorem L_an : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp ℂ)) [GrpObj A] (z : Sp ℂ ⟶ Sp R) (φ : A.left ⟶ G.left) (_ : IsGrpPullback A G z φ) (g : ℕ) (Lb : LB A.left) (u : HolUnif A Lb g) (v₀ : epsAt (𝟙 (Sp R)) ⟶ G) (hv₀ : IsTanAt G (𝟙 (Sp R)) v₀) (c : Fin g → ℂ) (v' : epsR ℂ ⟶ A), v'.left ≫ φ = spMap (dualMap (bmap z)) ≫ v₀.left → u.IsDiff c v' → ∀ (V : G.left.Opens) (hV : IsAffineOpen V) (f : Γ(G.left, V)), ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ V → AnalyticAt ℂ (fun τ : ℂ => valAt' ((u.ex (τ • c)).left ≫ φ) V f) 0 ∧ ∀ k : ℕ, iteratedDeriv k (fun τ : ℂ => valAt' ((u.ex (τ • c)).left ≫ φ) V f) 0 = valAt' ((u.ex 0).left ≫ φ) V ((der v₀ hv₀ hV)^[k] f) := by
  intro R _ G _ A _ z φ cart g Lb u v₀ hv₀ c v' hl hd V hV f h0
  let Z : Set (Fin g → ℂ) := {x | ⊤ ≤ ((u.ex x).left ≫ φ) ⁻¹ᵁ V}
  have hopen : IsOpen Z := (u.hol (φ ⁻¹ᵁ V) (φ.app V f)).1
  have hdiff : ∀ a : Γ(G.left, V), DifferentiableOn ℂ (fun x => valAt' ((u.ex x).left ≫ φ) V a) Z := fun a => by
    have := (u.hol (φ ⁻¹ᵁ V) (φ.app V a)).2
    simp only [ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_comp] at this
    exact this
  have hcont : Continuous (fun τ : ℂ => τ • c) := continuous_id.smul continuous_const
  have hZ' : IsOpen ((fun τ : ℂ => τ • c) ⁻¹' Z) := hopen.preimage hcont
  have h00 : (0 : ℂ) ∈ (fun τ : ℂ => τ • c) ⁻¹' Z := by
    show (0 : ℂ) • c ∈ Z
    rw [zero_smul]; exact h0
  have hder : ∀ (a : Γ(G.left, V)) (τ : ℂ), τ ∈ (fun τ : ℂ => τ • c) ⁻¹' Z →
      HasDerivAt (fun τ : ℂ => valAt' ((u.ex (τ • c)).left ≫ φ) V a)
        (valAt' ((u.ex (τ • c)).left ≫ φ) V (der v₀ hv₀ hV a)) τ := by
    intro a τ hτ
    have h1 : DifferentiableAt ℂ (fun x => valAt' ((u.ex x).left ≫ φ) V a) (τ • c) :=
      (hdiff a _ hτ).differentiableAt (hopen.mem_nhds hτ)
    have h3 : HasDerivAt (fun τ : ℂ => τ • c) c τ := by
      simpa using (hasDerivAt_id τ).smul_const c
    have h4 := h1.hasFDerivAt.comp_hasDerivAt τ h3
    rw [GlobalTheory.T.derivation_hol_unif_tangent R G A z φ cart g Lb u v₀ hv₀ c v' hl hd V hV a (τ • c) hτ] at h4
    exact h4
  have hanal : ∀ a : Γ(G.left, V), AnalyticAt ℂ (fun τ : ℂ => valAt' ((u.ex (τ • c)).left ≫ φ) V a) 0 := fun a =>
    DifferentiableOn.analyticAt (s := (fun τ : ℂ => τ • c) ⁻¹' Z)
      (fun τ hτ => (hder a τ hτ).differentiableAt.differentiableWithinAt) (hZ'.mem_nhds h00)
  refine ⟨hanal f, fun k => ?_⟩
  have hit : ∀ (k : ℕ) (a : Γ(G.left, V)), iteratedDeriv k (fun τ : ℂ => valAt' ((u.ex (τ • c)).left ≫ φ) V a) 0 =
      valAt' ((u.ex 0).left ≫ φ) V ((der v₀ hv₀ hV)^[k] a) := by
    intro k
    induction k with
    | zero =>
      intro a
      simp
    | succ k ih =>
      intro a
      have e : deriv (fun τ : ℂ => valAt' ((u.ex (τ • c)).left ≫ φ) V a) =ᶠ[𝓝 0]
          (fun τ : ℂ => valAt' ((u.ex (τ • c)).left ≫ φ) V (der v₀ hv₀ hV a)) := by
        filter_upwards [hZ'.mem_nhds h00] with τ hτ
        exact (hder a τ hτ).deriv
      rw [iteratedDeriv_succ', e.iteratedDeriv_eq k, ih, Function.iterate_succ_apply]
  exact hit k f

theorem ev_app {C : Type} [CommRing C] {X Y : Scheme.{0}} (y : Sp C ⟶ Y) (φ : Y ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ (φ ⁻¹ᵁ U))
    (h' : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ U) (a : Γ(X, U)) : ev y (φ ⁻¹ᵁ U) h (φ.app U a) = ev (y ≫ φ) U h' a := by
  simp only [ev, RingHom.comp_apply]
  congr 1

theorem ev_resU {C : Type} [CommRing C] {X : Scheme.{0}} (y : Sp C ⟶ X) {V V' : X.Opens} (le : V' ≤ V) (h : ⊤ ≤ y ⁻¹ᵁ V)
    (h' : ⊤ ≤ y ⁻¹ᵁ V') (u : Γ(X, V)ˣ) : ev y V' h' (res le u : Γ(X, V')ˣ).val = ev y V h u.val :=
  ev_res y le h h' u.val

theorem ev_pullU {C : Type} [CommRing C] {X Y : Scheme.{0}} (y : Sp C ⟶ Y) (φ : Y ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ (φ ⁻¹ᵁ U)) (h' : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    ev y (φ ⁻¹ᵁ U) h (pullU φ U u).val = ev (y ≫ φ) U h' u.val :=
  ev_app y φ U h h' u.val

theorem ev_g {C : Type} [CommRing C] {X Y : Scheme.{0}} (L : LB X) {κ : Type} [Fintype κ] (φ : κ → (Y ⟶ X)) (ε : κ → ℤ)
    (j j' : κ → L.ι) (y : Sp C ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j'))
    (h' : ∀ k, ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k))) :
    Units.map (ev y _ h).toMonoidHom ((LB.LinComb L φ ε).g j j') =
      ∏ k, Units.map (ev (y ≫ φ k) _ (h' k)).toMonoidHom (L.g (j k) (j' k)) ^ ε k := by
  dsimp only [LB.LinComb]
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  congr 1
  refine Units.ext ?_
  have hk : ⊤ ≤ y ⁻¹ᵁ (φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k))) := h' k
  exact (ev_resU y _ hk h _).trans (ev_pullU y (φ k) _ hk (h' k) _)

theorem res_res {X : Scheme.{0}} {a b c : X.Opens} (h1 : a ≤ b) (h2 : b ≤ c) (f : Γ(X, c)) :
    (X.presheaf.map (homOfLE h1).op).hom ((X.presheaf.map (homOfLE h2).op).hom f) =
      (X.presheaf.map (homOfLE (h1.trans h2)).op).hom f := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem L_int : ∀ (R K A : Type) [CommRing R] [Field K] [CommRing A] [IsLocalRing A] [Algebra R K] [Algebra R A] [Algebra A K] [IsScalarTower R A K] (G : Over (Sp R)) [GrpObj G] (P : RigLB G) (v₀ : epsAt (𝟙 (Sp R)) ⟶ G) (hv₀ : IsTanAt G (𝟙 (Sp R)) v₀) (n r : ℕ) (s : Fin r → Out.H0 P.L n) (i₀ : P.L.ι) (V : G.left.Opens) (hV : IsAffineOpen V) (hle : V ≤ LB.wchart P.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₀)) (h₀ : ⊤ ≤ (spMap (algebraMap R K) ≫ (eSec G : Sp R ⟶ G.left)) ⁻¹ᵁ V) (hr : ⊤ ≤ (spMap (algebraMap R K)) ⁻¹ᵁ (P.L.pull (eSec G)).U (fun _ => i₀)) (i : ℕ) (c : Fin r → R), (∀ k < i, ∑ j, algebraMap R K (c j) * ev (spMap (algebraMap R K) ≫ (eSec G : Sp R ⟶ G.left)) V h₀ ((der v₀ hv₀ hV)^[k] ((G.left.presheaf.map (homOfLE hle).op).hom ((s j).f fun _ => i₀))) = 0) → ∃ b : A, algebraMap A K b * ev (spMap (algebraMap R K)) _ hr (P.rig.s fun _ => i₀).val ^ n = ∑ j, algebraMap R K (c j) * ev (spMap (algebraMap R K) ≫ (eSec G : Sp R ⟶ G.left)) V h₀ ((der v₀ hv₀ hV)^[i] ((G.left.presheaf.map (homOfLE hle).op).hom ((s j).f fun _ => i₀))) := by
  intro R K A _ _ _ _ _ _ _ _ G _ P v₀ hv₀ n r s i₀ V hV hle h₀ hr i c hvan
  have hfac : spMap (algebraMap R K) = spMap (algebraMap A K) ≫ spMap (algebraMap R A) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact IsScalarTower.algebraMap_eq R A K
  let e : Sp R ⟶ G.left := eSec G
  let ym : Sp A ⟶ G.left := spMap (algebraMap R A) ≫ e
  let y : Sp K ⟶ G.left := spMap (algebraMap R K) ≫ e
  have hy : y = spMap (algebraMap A K) ≫ ym := by
    show spMap (algebraMap R K) ≫ e = _
    rw [hfac, Category.assoc]
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, ym (IsLocalRing.closedPoint A) ∈ P.L.U i₁ := by
    have h : ym (IsLocalRing.closedPoint A) ∈ (⨆ i, P.L.U i) := by rw [P.isLB.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 h
  have hm1 : ym (IsLocalRing.closedPoint A) ∈ LB.wchart P.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₁) :=
    Set.mem_iInter.2 fun _ => hi₁
  obtain ⟨V₁, hV₁, hmV₁, hsub⟩ := exists_isAffineOpen_mem_and_subset hm1
  have hle1 : V₁ ≤ LB.wchart P.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₁) := hsub
  have t1A : ⊤ ≤ ym ⁻¹ᵁ V₁ := fun p _ =>
    ((IsLocalRing.specializes_closedPoint p).map ym.continuous).mem_open V₁.isOpen hmV₁
  have t₁ : ⊤ ≤ y ⁻¹ᵁ V₁ := by
    rw [hy]; exact top_comp _ _ _ t1A
  have t : ⊤ ≤ y ⁻¹ᵁ (V ⊓ V₁) := fun p hp => ⟨h₀ hp, t₁ hp⟩
  have leW : V ⊓ V₁ ≤ LB.wchart P.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₀) ⊓
      LB.wchart P.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i₁) := inf_le_inf hle hle1
  let gL := (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (n : ℤ))).g (fun _ => i₀) (fun _ => i₁)
  let uu : Γ(G.left, V ⊓ V₁) := (res leW gL).val
  have huu : ev y _ t uu ≠ 0 := ((Units.isUnit (res leW gL)).map (ev y _ t)).ne_zero
  have hcompat : ∀ j, (G.left.presheaf.map (homOfLE (inf_le_left : V ⊓ V₁ ≤ V)).op).hom
      ((G.left.presheaf.map (homOfLE hle).op).hom ((s j).f fun _ => i₀)) =
      uu * (G.left.presheaf.map (homOfLE (inf_le_right : V ⊓ V₁ ≤ V₁)).op).hom
        ((G.left.presheaf.map (homOfLE hle1).op).hom ((s j).f fun _ => i₁)) := by
    intro j
    have h := congrArg (G.left.presheaf.map (homOfLE leW).op).hom ((s j).compat (fun _ => i₀) (fun _ => i₁))
    refine (res_res (X := G.left) (inf_le_left : V ⊓ V₁ ≤ V) hle ((s j).f fun _ => i₀)).trans ?_
    refine Eq.trans ?_ (congrArg (uu * ·)
      (res_res (X := G.left) (inf_le_right : V ⊓ V₁ ≤ V₁) hle1 ((s j).f fun _ => i₁)).symm)
    refine (res_res leW inf_le_left _).symm.trans (h.trans ?_)
    refine (map_mul (G.left.presheaf.map (homOfLE leW).op).hom _ _).trans ?_
    exact congrArg (uu * ·) (res_res leW inf_le_right _)
  have hb : bmap (y ≫ G.hom) = algebraMap R K := by
    have h1 : y ≫ G.hom = spMap (algebraMap R K) := by
      show (spMap (algebraMap R K) ≫ e) ≫ G.hom = _
      have : e ≫ G.hom = 𝟙 _ := Over.w η[G]
      rw [Category.assoc, this, Category.comp_id]
    rw [h1, bmap_spMap]
  have key := GlobalTheory.T.section_ratio_overlap R K G v₀ hv₀ y V V₁ hV hV₁ h₀ t₁ t r _ _ uu huu hcompat i c (by
    simpa only [hb] using hvan)
  simp only [hb] at key

  have hr1 : ⊤ ≤ (spMap (algebraMap R K)) ⁻¹ᵁ (P.L.pull (eSec G)).U (fun _ => i₁) := fun p hp =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (hle1 (t₁ hp)) 0
  have hr1A : ⊤ ≤ (spMap (algebraMap R A)) ⁻¹ᵁ (P.L.pull (eSec G)).U (fun _ => i₁) := fun p hp =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (hle1 (t1A hp)) 0
  have hU : ⊤ ≤ y ⁻¹ᵁ (P.L.U i₀ ⊓ P.L.U i₁) := fun p hp =>
    ⟨Set.mem_iInter.1 (hle (h₀ hp)) 0, Set.mem_iInter.1 (hle1 (t₁ hp)) 0⟩
  have hover : ⊤ ≤ (spMap (algebraMap R K)) ⁻¹ᵁ
      ((P.L.pull (eSec G)).U (fun _ => i₀) ⊓ (P.L.pull (eSec G)).U (fun _ => i₁)) := fun p hp => ⟨hr hp, hr1 hp⟩
  have hgen := congrArg Units.val (P.rigGen (fun _ => i₀) (fun _ => i₁))
  have hγ := congrArg Units.val (ev_g P.L (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => i₀) (fun _ => i₁)
    (spMap (algebraMap R K)) hover (fun _ => hU))
  have hu := congrArg Units.val (ev_g P.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (n : ℤ)) (fun _ => i₀) (fun _ => i₁)
    y (fun p hp => leW (t hp)) (fun _ => by rw [Category.comp_id]; exact hU))
  have hr0 : ev (spMap (algebraMap R K)) _ hr (P.rig.s fun _ => i₀).val =
      ev (spMap (algebraMap R K)) _ hover ((P.L.pull (eSec G)).g (fun _ => i₀) (fun _ => i₁)).val *
        ev (spMap (algebraMap R K)) _ hr1 (P.rig.s fun _ => i₁).val := by
    refine (ev_resU _ inf_le_left hr hover _).symm.trans ?_
    refine (congrArg (ev _ _ hover) hgen).trans ?_
    refine (map_mul (ev _ _ hover) _ _).trans ?_
    exact congrArg (_ * ·) (ev_resU _ inf_le_right hr1 hover _)
  simp only [Fintype.prod_unique, zpow_one, zpow_natCast, Units.val_pow_eq_pow_val] at hγ hu
  have hγ' : ev (spMap (algebraMap R K)) _ hover ((P.L.pull (eSec G)).g (fun _ => i₀) (fun _ => i₁)).val =
      ev y _ hU (P.L.g i₀ i₁).val := hγ
  have huu' : ev y _ t uu = ev y _ hU (P.L.g i₀ i₁).val ^ n := by
    refine (ev_resU y leW (fun p hp => leW (t hp)) t gL).trans ?_
    refine Eq.trans hu ?_
    exact congrArg (· ^ n) (congrFun (congrArg DFunLike.coe (ev_congr (Category.comp_id y) _ _ hU)) _)
  let a : A := ∑ j, algebraMap R A (c j) * ev ym V₁ t1A ((der v₀ hv₀ hV₁)^[i]
    ((G.left.presheaf.map (homOfLE hle1).op).hom ((s j).f fun _ => i₁)))
  have ha : algebraMap A K a = ∑ j, algebraMap R K (c j) * ev y V₁ t₁ ((der v₀ hv₀ hV₁)^[i]
      ((G.left.presheaf.map (homOfLE hle1).op).hom ((s j).f fun _ => i₁))) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← IsScalarTower.algebraMap_apply R A K]
    congr 1
    have hcomp : ⊤ ≤ (spMap (algebraMap A K) ≫ ym) ⁻¹ᵁ V₁ := top_comp _ _ _ t1A
    exact (ev_comp (algebraMap A K) ym V₁ t1A hcomp _).symm.trans
      (congrFun (congrArg DFunLike.coe (ev_congr hy.symm V₁ hcomp t₁)) _)
  obtain ⟨ru, hru⟩ : IsUnit (ev (spMap (algebraMap R A)) _ hr1A (P.rig.s fun _ => i₁).val) :=
    (Units.isUnit _).map (ev (spMap (algebraMap R A)) _ hr1A)
  have hr1K : ev (spMap (algebraMap R K)) _ hr1 (P.rig.s fun _ => i₁).val = algebraMap A K ru := by
    rw [hru]
    have hcomp : ⊤ ≤ (spMap (algebraMap A K) ≫ spMap (algebraMap R A)) ⁻¹ᵁ (P.L.pull (eSec G)).U (fun _ => i₁) :=
      top_comp _ _ _ hr1A
    exact (congrFun (congrArg DFunLike.coe (ev_congr hfac _ hr1 hcomp)) _).trans (ev_comp _ _ _ hr1A hcomp _)
  refine ⟨a * ((ru⁻¹ : Aˣ) : A) ^ n, ?_⟩
  have hxw : algebraMap A K ((ru⁻¹ : Aˣ) : A) * algebraMap A K ru = 1 := by
    rw [← map_mul]; simp
  have hxw' : algebraMap A K ((ru⁻¹ : Aˣ) : A) ^ n * algebraMap A K ru ^ n = 1 := by
    rw [← mul_pow, hxw, one_pow]
  refine Eq.trans ?_ key.symm
  rw [hr0, hγ', hr1K, huu', ← ha, map_mul, map_pow, mul_pow]
  linear_combination (algebraMap A K a * ev y _ hU (P.L.g i₀ i₁).val ^ n) * hxw'

theorem int_of_loc (L : Type) [Field L] [NumberField L] (x : L)
    (h : ∀ v : MaximalSpectrum (𝓞 L), x ∈ Localization.subalgebra.ofField L v.asIdeal.primeCompl
      v.asIdeal.primeCompl_le_nonZeroDivisors) : IsIntegral ℤ x := by
  have hx : x ∈ (⊥ : Subalgebra (𝓞 L) L) := by
    rw [← MaximalSpectrum.iInf_localization_eq_bot (𝓞 L) L]
    exact Algebra.mem_iInf.2 h
  obtain ⟨b, rfl⟩ := Algebra.mem_bot.1 hx
  exact NumberField.RingOfIntegers.isIntegral_coe b

theorem top_of_closed {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (y : Sp A ⟶ X) (U : X.Opens)
    (h : y (IsLocalRing.closedPoint A) ∈ U) : ⊤ ≤ y ⁻¹ᵁ U := fun p _ =>
  ((IsLocalRing.specializes_closedPoint p).map y.continuous).mem_open U.isOpen h

theorem pt_zero {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ}
    (a : ArchFrame P z g) : a.pt 0 = z ≫ (eSec G : S ⟶ G.left) := by
  have h1 : a.u.ex 0 = 1 := by
    have h := a.u.ex_add 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  have e := congrArg (fun m => m.left) (map_one (pushHom a.cart (𝟙_ (Over (Sp ℂ)))))
  show (a.u.ex 0).left ≫ a.φ = _
  rw [h1]
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem valF_eq {F : Type} [Field F] {X : Scheme.{0}} (y : Sp F ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (g : Γ(X, U)) :
    valF y U g = ev y U h g := dif_pos h

theorem valAt'_eq {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (g : Γ(X, U)) :
    valAt' y U g = ev y U h g := dif_pos h

theorem jets : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (x : D.B.carrier) (n r : ℕ) (s : Fin r → Out.H0 D.t.PP.L n), ∃ J : ℕ → Fin r → L, (∀ (i : ℕ) (c : Fin r → 𝓞 L), (∀ k < i, ∑ j, (c j : L) * J k j = 0) → IsIntegral ℤ (∑ j, (c j : L) * J i j)) ∧ ∀ (σ : L →+* ℂ) (a : D.Frame σ) (f : Fin r → (Fin D.g → ℂ) → ℂ) (v : Fin D.g → ℂ), (∀ j, a.IsFn (s j) (f j)) → D.IsVec a x v → ∀ (i : ℕ) (c : Fin r → ℂ), ((∀ k < i, ∑ j, c j * σ (J k j) = 0) ↔ ∀ k < i, iteratedDeriv k (fun τ : ℂ => ∑ j, c j * f j (τ • v)) 0 = 0) ∧ ((∀ k < i, ∑ j, c j * σ (J k j) = 0) → ∑ j, c j * σ (J i j) = iteratedDeriv i (fun τ : ℂ => ∑ j, c j * f j (τ • v)) 0) := by
  intro E _ _ _ H L _ _ D x n r s
  have hv₀ : IsTanAt D.t.G (𝟙 (Sp (𝓞 L))) (D.MB.pt x) := D.MB.tan x
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, (spMap (algebraMap (𝓞 L) L) ≫ (eSec D.t.G : Sp (𝓞 L) ⟶ D.t.G.left))
      (IsLocalRing.closedPoint L) ∈ D.t.PP.L.U i₀ := by
    have h : (spMap (algebraMap (𝓞 L) L) ≫ (eSec D.t.G : Sp (𝓞 L) ⟶ D.t.G.left)) (IsLocalRing.closedPoint L) ∈
        (⨆ i, D.t.PP.L.U i) := by rw [D.t.PP.isLB.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 h
  have hm : (spMap (algebraMap (𝓞 L) L) ≫ (eSec D.t.G : Sp (𝓞 L) ⟶ D.t.G.left)) (IsLocalRing.closedPoint L) ∈
      LB.wchart D.t.PP.L (fun _ : Fin 1 => 𝟙 D.t.G.left) (fun _ => i₀) := Set.mem_iInter.2 fun _ => hi₀
  obtain ⟨V, hV, hmV, hsub⟩ := exists_isAffineOpen_mem_and_subset hm
  have hle : V ≤ LB.wchart D.t.PP.L (fun _ : Fin 1 => 𝟙 D.t.G.left) (fun _ => i₀) := hsub
  have h₀ : ⊤ ≤ (spMap (algebraMap (𝓞 L) L) ≫ (eSec D.t.G : Sp (𝓞 L) ⟶ D.t.G.left)) ⁻¹ᵁ V := top_of_closed _ _ hmV
  have hr : ⊤ ≤ (spMap (algebraMap (𝓞 L) L)) ⁻¹ᵁ (D.t.PP.L.pull (eSec D.t.G)).U (fun _ => i₀) := fun p hp =>
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (hle (h₀ hp)) 0
  have hr0 : ev (spMap (algebraMap (𝓞 L) L)) _ hr (D.t.PP.rig.s fun _ => i₀).val ≠ 0 :=
    ((Units.isUnit _).map (ev (spMap (algebraMap (𝓞 L) L)) _ hr)).ne_zero
  refine ⟨fun k j => ev (spMap (algebraMap (𝓞 L) L) ≫ (eSec D.t.G : Sp (𝓞 L) ⟶ D.t.G.left)) V h₀
      ((der (D.MB.pt x) hv₀ hV)^[k] ((D.t.G.left.presheaf.map (homOfLE hle).op).hom ((s j).f fun _ => i₀))) /
      ev (spMap (algebraMap (𝓞 L) L)) _ hr (D.t.PP.rig.s fun _ => i₀).val ^ n, ?_, ?_⟩
  · intro i c hvan
    refine int_of_loc L _ fun v => ?_
    haveI : IsLocalRing (Localization.subalgebra.ofField L v.asIdeal.primeCompl
        v.asIdeal.primeCompl_le_nonZeroDivisors) :=
      IsLocalization.AtPrime.isLocalRing _ v.asIdeal
    obtain ⟨b, hb⟩ := L_int (𝓞 L) L (Localization.subalgebra.ofField L v.asIdeal.primeCompl
        v.asIdeal.primeCompl_le_nonZeroDivisors) D.t.G D.t.PP (D.MB.pt x) hv₀ n r s i₀ V hV hle h₀ hr i c (fun k hk => by
      have h := hvan k hk
      simp only [mul_div_assoc', ← Finset.sum_div] at h
      exact (div_eq_zero_iff.1 h).resolve_right (pow_ne_zero _ hr0))
    have hx : ∑ j, ((c j : 𝓞 L) : L) * (ev (spMap (algebraMap (𝓞 L) L) ≫ (eSec D.t.G : Sp (𝓞 L) ⟶ D.t.G.left)) V h₀
        ((der (D.MB.pt x) hv₀ hV)^[i] ((D.t.G.left.presheaf.map (homOfLE hle).op).hom ((s j).f fun _ => i₀))) /
        ev (spMap (algebraMap (𝓞 L) L)) _ hr (D.t.PP.rig.s fun _ => i₀).val ^ n) = (b : L) := by
      simp only [mul_div_assoc', ← Finset.sum_div]
      rw [div_eq_iff (pow_ne_zero _ hr0)]
      exact hb.symm
    rw [hx]
    exact b.2
  · intro σ a f v hf hvec i c
    obtain ⟨vv, hlift, v', hv'1, hv'2⟩ := hvec
    have hl : v'.left ≫ a.φ = spMap (dualMap (bmap (emb σ))) ≫ (D.MB.pt x).left := by
      have h1 : vv.left ≫ 𝟙 D.t.G.left = _ := hlift
      rw [Category.comp_id] at h1
      rw [hv'1, h1, bmap_spMap]
    have hemb : emb σ = spMap σ ≫ spMap (algebraMap (𝓞 L) L) := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have pt0 : (a.u.ex 0).left ≫ a.φ =
        spMap σ ≫ spMap (algebraMap (𝓞 L) L) ≫ (eSec D.t.G : Sp (𝓞 L) ⟶ D.t.G.left) := by
      refine (pt_zero a).trans ?_
      rw [hemb, Category.assoc]
    have h0 : ⊤ ≤ ((a.u.ex 0).left ≫ a.φ) ⁻¹ᵁ V := by
      rw [pt0]; exact top_comp σ _ V h₀
    have AN := fun j => L_an (𝓞 L) D.t.G a.A (emb σ) a.φ a.cart D.g _ a.u (D.MB.pt x) hv₀ v v' hl hv'2 V hV
      ((D.t.G.left.presheaf.map (homOfLE hle).op).hom ((s j).f fun _ => i₀)) h0
    have hval : ∀ (k : ℕ) (j : Fin r), iteratedDeriv k (fun τ : ℂ => valAt' ((a.u.ex (τ • v)).left ≫ a.φ) V
        ((D.t.G.left.presheaf.map (homOfLE hle).op).hom ((s j).f fun _ => i₀))) 0 =
        σ (ev (spMap (algebraMap (𝓞 L) L) ≫ (eSec D.t.G : Sp (𝓞 L) ⟶ D.t.G.left)) V h₀
          ((der (D.MB.pt x) hv₀ hV)^[k] ((D.t.G.left.presheaf.map (homOfLE hle).op).hom ((s j).f fun _ => i₀)))) := by
      intro k j
      rw [(AN j).2 k, valAt'_eq _ _ h0]
      have hc : ⊤ ≤ (spMap σ ≫ spMap (algebraMap (𝓞 L) L) ≫ (eSec D.t.G : Sp (𝓞 L) ⟶ D.t.G.left)) ⁻¹ᵁ V :=
        top_comp σ _ V h₀
      exact (congrFun (congrArg DFunLike.coe (ev_congr pt0 V h0 hc)) _).trans (ev_comp σ _ V h₀ hc _)
    let Z : Set (Fin D.g → ℂ) := {w | ⊤ ≤ ((a.u.ex w).left ≫ a.φ) ⁻¹ᵁ V}
    have hZo : IsOpen Z := (a.u.hol (a.φ ⁻¹ᵁ V) (a.φ.app V 0)).1
    have hcont : Continuous (fun τ : ℂ => τ • v) := continuous_id.smul continuous_const
    have hZ' : IsOpen ((fun τ : ℂ => τ • v) ⁻¹' Z) := hZo.preimage hcont
    have h00 : (0 : ℂ) ∈ (fun τ : ℂ => τ • v) ⁻¹' Z := by
      show (0 : ℂ) • v ∈ Z
      rw [zero_smul]; exact h0
    have hZU : ∀ w ∈ Z, ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ (D.t.PP.L.pull a.φ).U (fun _ => i₀) := fun w hw p hp =>
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (hle (hw hp)) 0
    have hfrd : DifferentiableOn ℂ (fun τ : ℂ => a.u.fr (fun _ => i₀) (τ • v)) ((fun τ : ℂ => τ • v) ⁻¹' Z) := by
      refine DifferentiableOn.comp (t := {w | ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ (D.t.PP.L.pull a.φ).U (fun _ => i₀)})
        (a.u.fr_hol _) ?_ (fun τ hτ => hZU _ hτ)
      exact (differentiable_id.smul_const v).differentiableOn
    have hFan : AnalyticAt ℂ (fun τ : ℂ => a.u.fr (fun _ => i₀) (τ • v) ^ n) 0 :=
      DifferentiableOn.analyticAt (s := (fun τ : ℂ => τ • v) ⁻¹' Z) (hfrd.pow n) (hZ'.mem_nhds h00)
    have hF0 : a.u.fr (fun _ => i₀) ((0 : ℂ) • v) ^ n =
        σ (ev (spMap (algebraMap (𝓞 L) L)) _ hr (D.t.PP.rig.s fun _ => i₀).val) ^ n := by
      have hU0 : ⊤ ≤ ((a.u.ex 0).left ≫ a.φ) ⁻¹ᵁ D.t.PP.L.U i₀ := fun p hp =>
        Set.mem_iInter.1 (hle (h0 hp)) 0
      have hrig := a.rig i₀ hU0
      have hc : ⊤ ≤ (spMap σ ≫ spMap (algebraMap (𝓞 L) L)) ⁻¹ᵁ (D.t.PP.L.pull (eSec D.t.G)).U (fun _ => i₀) :=
        top_comp σ _ _ hr
      have hc' : ⊤ ≤ (emb σ) ⁻¹ᵁ (D.t.PP.L.pull (eSec D.t.G)).U (fun _ => i₀) := by
        rw [hemb]; exact hc
      rw [valF_eq _ _ hc'] at hrig
      rw [zero_smul, hrig]
      exact congrArg (· ^ n) ((congrFun (congrArg DFunLike.coe (ev_congr hemb _ hc' hc)) _).trans
        (ev_comp σ _ _ hr hc _))
    have hσr : σ (ev (spMap (algebraMap (𝓞 L) L)) _ hr (D.t.PP.rig.s fun _ => i₀).val) ^ n ≠ 0 :=
      pow_ne_zero _ ((map_ne_zero σ).2 hr0)
    have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), ∑ j, c j * (fun τ : ℂ => valAt' ((a.u.ex (τ • v)).left ≫ a.φ) V
        ((D.t.G.left.presheaf.map (homOfLE hle).op).hom ((s j).f fun _ => i₀))) τ =
        (fun τ : ℂ => ∑ j, c j * f j (τ • v)) τ * (fun τ : ℂ => a.u.fr (fun _ => i₀) (τ • v) ^ n) τ := by
      filter_upwards [hZ'.mem_nhds h00] with τ hτ
      have hτ' : ⊤ ≤ ((a.u.ex (τ • v)).left ≫ a.φ) ⁻¹ᵁ V := hτ
      simp only [Finset.sum_mul, _root_.mul_assoc]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      have hW : ⊤ ≤ ((a.u.ex (τ • v)).left ≫ a.φ) ⁻¹ᵁ
          LB.wchart D.t.PP.L (fun _ : Fin 1 => 𝟙 D.t.G.left) (fun _ => i₀) := fun p hp => hle (hτ' hp)
      have hU : ⊤ ≤ a.pt (τ • v) ⁻¹ᵁ D.t.PP.L.U i₀ := fun p hp => Set.mem_iInter.1 (hW hp) 0
      rw [valAt'_eq _ _ hτ']
      refine (ev_res _ hle hW hτ' _).trans ?_
      refine (valF_eq _ _ hW _).symm.trans ?_
      exact hf j i₀ (τ • v) hU
    have key := GlobalTheory.T.iterated_derivative_factor r _ c _ _ (fun j => (AN j).1) hFan (by rw [hF0]; exact hσr) hev i
    have hJ : ∀ k : ℕ, ∑ j, c j * σ (ev (spMap (algebraMap (𝓞 L) L) ≫ (eSec D.t.G : Sp (𝓞 L) ⟶ D.t.G.left)) V h₀
        ((der (D.MB.pt x) hv₀ hV)^[k] ((D.t.G.left.presheaf.map (homOfLE hle).op).hom ((s j).f fun _ => i₀))) /
        ev (spMap (algebraMap (𝓞 L) L)) _ hr (D.t.PP.rig.s fun _ => i₀).val ^ n) =
        (∑ j, c j * iteratedDeriv k (fun τ : ℂ => valAt' ((a.u.ex (τ • v)).left ≫ a.φ) V
          ((D.t.G.left.presheaf.map (homOfLE hle).op).hom ((s j).f fun _ => i₀))) 0) /
          σ (ev (spMap (algebraMap (𝓞 L) L)) _ hr (D.t.PP.rig.s fun _ => i₀).val) ^ n := by
      intro k
      simp only [hval, map_div₀, map_pow, mul_div_assoc', Finset.sum_div]
    simp only [hJ]
    rw [hF0] at key
    constructor
    · rw [← key.1]
      refine forall₂_congr fun k _ => ?_
      rw [div_eq_zero_iff, or_iff_left hσr]
    · intro h
      have h' : ∀ k < i, ∑ j, c j * iteratedDeriv k (fun τ : ℂ => valAt' ((a.u.ex (τ • v)).left ≫ a.φ) V
          ((D.t.G.left.presheaf.map (homOfLE hle).op).hom ((s j).f fun _ => i₀))) 0 = 0 := fun k hk =>
        (div_eq_zero_iff.1 (h k hk)).resolve_right hσr
      rw [key.2 h', mul_div_cancel_left₀ _ hσr]

end GlobalTheory.CompanionTheory.Ar.JetMain
