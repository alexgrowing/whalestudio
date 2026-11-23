import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicAffinePolydiscChartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartFrameGrowthStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.VectorsAtComplexPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBdryChartOfHol
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMapStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open GlobalTheory.CompanionTheory.Ar.Flat.BdryModel

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily

theorem exists_tied_chart {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    (Xo : Moduli D l) (σ : KA l →+* ℂ) (Z : Scheme.{0}) (T : SAB H Z) (U₀ : Scheme.{0}) (j₀ : U₀ ⟶ Z) (k₀ : U₀ ⟶ Xo.X)
    (To : SAB H U₀) (n a : ℕ) (y : (Fin n → ℂ) → (Sp ℂ ⟶ Z)) (han : a ≤ n) (hj : IsOpenImmersion j₀)
    (n₁ : SABMap To T j₀) (n₂ : SABMap To Xo.univ.t k₀) (hy : IsHolTo (Metric.ball 0 1) y)
    (hp : ∀ z ∈ punct n a 1, ∃ p : Sp ℂ ⟶ U₀, p ≫ j₀ = y z ∧ p ≫ k₀ ≫ Xo.s = spMap σ) :
    ∃ (ρ : ℝ) (C : BdryChart Xo σ n a) (i : Sp C.R ⟶ Z) (e : C.V ⟶ U₀) (mi : SABMap C.t T i) (me : SABMap C.tV To e),
      0 < ρ ∧ ρ ≤ 1 ∧ e ≫ j₀ = C.j ≫ i ∧ e ≫ k₀ = C.k ∧
      (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ i = y ((ρ : ℂ) • z)) ∧
      C.m₂.φ = me.φ ≫ n₂.φ ∧ C.m₁.φ ≫ mi.φ = me.φ ≫ n₁.φ := by
  classical
  have := T.semi.smooth
  obtain ⟨U, hU, hx, -, n', v₀, hv₀⟩ := GlobalTheory.exists_affine_lieBasis_baseChange Z T.G
    (y 0 (default : PrimeSpectrum ℂ)) ⊤ trivial
  have h0 : ⊤ ≤ y 0 ⁻¹ᵁ U := fun p _ => by
    have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [this]; exact hx
  obtain ⟨ρ₀, hρ₀, hB₀⟩ := Metric.isOpen_iff.1 (hy U 0).1 0 ⟨Metric.mem_ball_self one_pos, h0⟩
  obtain ⟨ρ, hρ, hρ1, hB⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      Metric.ball (0 : Fin n → ℂ) ρ ⊆ {b ∈ Metric.ball 0 1 | ⊤ ≤ y b ⁻¹ᵁ U} :=
    ⟨min ρ₀ 1, lt_min hρ₀ one_pos, min_le_right _ _, (Metric.ball_subset_ball (min_le_left _ _)).trans hB₀⟩
  have hin : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (ρ : ℂ) • z ∈ Metric.ball (0 : Fin n → ℂ) ρ := fun z hz => by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    exact mul_lt_of_lt_one_right hρ hz
  obtain ⟨t, ⟨m⟩⟩ := exists_sab hU.fromSpec T
  have hdim : SmoothOfRelativeDimension n' t.G.hom := HolChart.smoothDim_of_fibres t n' fun κ _ f t₀ m₀ => by
    obtain ⟨q, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m m₀
    obtain ⟨v', -, hv'⟩ := hv₀ κ f t₀.G _ q.cart
    exact ⟨v', hv'⟩
  obtain ⟨v', -, hv'⟩ := hv₀ Γ(Z, U) (RingHom.id _) t.G m.cm.F (by
    have : spMap (RingHom.id Γ(Z, U)) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]; exact m.cart)
  obtain ⟨M⟩ := lieModel_of_isLieBasis v' hv'
  let ψ : (Fin n → ℂ) → (Γ(Z, U) →+* ℂ) := fun z =>
    if h : ⊤ ≤ y ((ρ : ℂ) • z) ⁻¹ᵁ U then evalHom _ U h else evalHom _ U h0
  have hψ : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (ψ z) ≫ hU.fromSpec = y ((ρ : ℂ) • z) := fun z hz => by
    simp only [ψ, dif_pos (hB (hin z hz)).2]
    exact spMap_evalHom _ _ _ _
  obtain ⟨tV, ⟨q⟩⟩ := exists_sab (pullback.snd hU.fromSpec j₀) To
  obtain ⟨m₂, e₂⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₂ q
  obtain ⟨q₁, e₁⟩ : ∃ q₁ : SABMap tV T (pullback.fst hU.fromSpec j₀ ≫ hU.fromSpec), q₁.φ = q.φ ≫ n₁.φ := by
    rw [pullback.condition]
    exact GlobalTheory.ObjMaps.exists_sab_comp n₁ q
  obtain ⟨m₁, e₃⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m q₁
  have hpt : ∀ z ∈ punct n a 1, ∃ p : Sp ℂ ⟶ pullback hU.fromSpec j₀,
      p ≫ pullback.fst _ _ = spMap (ψ z) ∧ p ≫ (pullback.snd _ _ ≫ k₀) ≫ Xo.s = spMap σ := fun z hz => by
    obtain ⟨p, hp₁, hp₂⟩ := hp ((ρ : ℂ) • z) ⟨(hB (hin z hz.1)).1, fun i hi => by
      simpa using ⟨hρ.ne', hz.2 i hi⟩⟩
    refine ⟨pullback.lift (spMap (ψ z)) p ((hψ z hz.1).trans hp₁.symm), pullback.lift_fst _ _ _, ?_⟩
    rw [Category.assoc, pullback.lift_snd_assoc, hp₂]
  obtain ⟨p₀, -⟩ := hpt _ (half_mem_punct n a)
  have : Nonempty (Sp ℂ ⟶ pullback hU.fromSpec j₀) := ⟨p₀⟩
  choose! pt hpt using hpt
  refine ⟨ρ, { a_le := han, R := Γ(Z, U), t := t, g := n', dim := hdim
               M := M, ψ := ψ, hol := ⟨Metric.isOpen_ball, fun r => ?_⟩
               V := pullback hU.fromSpec j₀, j := pullback.fst _ _, j_open := inferInstance
               k := pullback.snd _ _ ≫ k₀, tV := tV, m₁ := m₁, m₂ := m₂, pt := pt, pt_eq := hpt },
    hU.fromSpec, pullback.snd _ _, m, q, hρ, hρ1, pullback.condition.symm, rfl, hψ, e₂, e₃.symm.trans e₁⟩
  refine (((hy U r).2.comp (f := fun z => (ρ : ℂ) • z) (by fun_prop) (fun z hz => hB (hin z hz)))).congr
    fun z hz => ?_
  simp only [ψ, Function.comp, valAt', dif_pos (hB (hin z hz)).2]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem exists_lift_of_centre_mem {X : Scheme.{0}} (W : X.Opens) (w : Sp ℂ ⟶ X) (h : centre w ∈ W) :
    ∃ w' : Sp ℂ ⟶ W.toScheme, w' ≫ W.ι = w := by
  have hr : Set.range w ⊆ Set.range W.ι := by
    rintro _ ⟨p, rfl⟩
    have e : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [Scheme.Opens.range_ι, e]
    exact h
  exact ⟨IsOpenImmersion.lift W.ι w hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_model_chart (Y : Model Xo c β) (σ : c.F →+* ℂ) {X' : Scheme.{0}} (π : X' ⟶ Y.X) (s' : X' ⟶ Sp c.F)
    (d : ℕ) (W' : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c) (h1 : jW ≫ Y.j = W'.ι ≫ π)
    (h2 : jW ≫ pullback.snd _ _ = W'.ι ≫ s') (V : X'.Opens) (hV : IsAffineOpen V) (a : ℕ)
    (ψ : (Fin d → ℂ) → (Γ(X', V) →+* ℂ)) (ha : a ≤ d) (hol : IsHolPts (ball 0 1) ψ)
    (hpt : ∀ z ∈ punct d a 1, spMap (ψ z) ≫ hV.fromSpec ≫ s' = spMap σ ∧ centre (spMap (ψ z) ≫ hV.fromSpec) ∈ W') :
    ∃ (ρ : ℝ) (C : BdryChart Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) d a)
      (i₀ : Sp C.R ⟶ Sp Γ(X', V)) (mR : SABMap C.t Y.t (i₀ ≫ hV.fromSpec ≫ π)) (k' : C.V ⟶ Xo.XF c)
      (φ₀ : C.tV.G.left ⟶ Y.oF.t.G.left), 0 < ρ ∧ ρ ≤ 1 ∧
      (∀ z ∈ ball (0 : Fin d → ℂ) 1, spMap (C.ψ z) ≫ i₀ = spMap (ψ ((ρ : ℂ) • z))) ∧
      k' ≫ pullback.fst _ _ = C.k ∧ k' ≫ Y.j = C.j ≫ i₀ ≫ hV.fromSpec ≫ π ∧
      k' ≫ pullback.snd _ _ = C.j ≫ i₀ ≫ hV.fromSpec ≫ s' ∧ φ₀ ≫ Y.oF.t.G.hom = C.tV.G.hom ≫ k' ∧
      φ₀ ≫ Y.m0.toSABMap.φ = C.m₂.φ ∧ φ₀ ≫ Y.m.φ = C.m₁.φ ≫ mR.φ := by
  obtain ⟨T, ⟨m⟩⟩ := exists_sab (hV.fromSpec ≫ π) Y.t
  let U₀ := pullback hV.fromSpec W'.ι
  let j₀ : U₀ ⟶ Sp Γ(X', V) := pullback.fst _ _
  let g₀ : U₀ ⟶ Xo.XF c := pullback.snd hV.fromSpec W'.ι ≫ jW
  have hcond : j₀ ≫ hV.fromSpec = pullback.snd hV.fromSpec W'.ι ≫ W'.ι := pullback.condition
  obtain ⟨tU, ⟨n₃⟩⟩ := exists_sab g₀ Y.oF.t
  obtain ⟨n₂, e₂⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m0.toSABMap n₃
  have hj : g₀ ≫ Y.jQ ≫ pullback.fst _ _ = j₀ ≫ hV.fromSpec ≫ π := by
    have : g₀ ≫ Y.j = j₀ ≫ hV.fromSpec ≫ π := by
      simp only [g₀, Category.assoc, h1]
      rw [← Category.assoc j₀, hcond, Category.assoc]
    exact this
  obtain ⟨q₁, eq₁⟩ : ∃ q₁ : SABMap tU Y.t (j₀ ≫ hV.fromSpec ≫ π), q₁.φ = n₃.φ ≫ Y.m.φ := by
    rw [← hj]
    exact GlobalTheory.ObjMaps.exists_sab_comp Y.m n₃
  obtain ⟨n₁, e₁⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m q₁
  have hp : ∀ z ∈ punct d a 1, ∃ p : Sp ℂ ⟶ U₀, p ≫ j₀ = spMap (ψ z) ∧
      p ≫ (g₀ ≫ pullback.fst _ _) ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    intro z hz
    obtain ⟨w', hw'⟩ := exists_lift_of_centre_mem W' _ (hpt z hz).2
    refine ⟨pullback.lift (spMap (ψ z)) w' hw'.symm, pullback.lift_fst _ _ _, ?_⟩
    have e : (pullback.lift (spMap (ψ z)) w' hw'.symm : Sp ℂ ⟶ U₀) ≫ g₀ = w' ≫ jW := by
      simp only [g₀]
      rw [← Category.assoc, pullback.lift_snd]
    have ec : pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s =
        pullback.snd _ _ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := pullback.condition
    calc _ = ((pullback.lift (spMap (ψ z)) w' hw'.symm : Sp ℂ ⟶ U₀) ≫ g₀) ≫ pullback.fst _ _ ≫ Xo.s := by
            simp only [Category.assoc]
      _ = (w' ≫ jW) ≫ pullback.snd _ _ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by rw [e, ec]
      _ = w' ≫ (jW ≫ pullback.snd _ _) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
            simp only [Category.assoc]
      _ = (w' ≫ W'.ι) ≫ s' ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
            rw [h2]; simp only [Category.assoc]
      _ = _ := by
            rw [hw', spMap_comp', ← (hpt z hz).1]; simp only [Category.assoc]
  obtain ⟨ρ, C, i₀, e, mi, me, hρ, hρ1, hej, hek, hψ, hm₂, hm₁⟩ := exists_tied_chart Xo _ _ T U₀ j₀
    (g₀ ≫ pullback.fst _ _) tU d a (fun z => spMap (ψ z)) ha inferInstance n₁ n₂
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_spMap hol.1 hol.2) hp
  obtain ⟨mR, eR⟩ := GlobalTheory.ObjMaps.exists_sab_comp m mi
  refine ⟨ρ, C, i₀, mR, e ≫ g₀, me.φ ≫ n₃.φ, hρ, hρ1, hψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact hek
  · have w2 : g₀ ≫ Y.j = j₀ ≫ hV.fromSpec ≫ π := hj
    rw [Category.assoc, w2, ← Category.assoc, hej]
    simp only [Category.assoc]
  · have w2 : g₀ ≫ pullback.snd _ _ = j₀ ≫ hV.fromSpec ≫ s' := by
      simp only [g₀, Category.assoc, h2]
      rw [← Category.assoc j₀, hcond, Category.assoc]
    rw [Category.assoc, w2, ← Category.assoc, hej]
    simp only [Category.assoc]
  · have w3 : n₃.φ ≫ Y.oF.t.G.hom = tU.G.hom ≫ g₀ := n₃.cart.1.w
    have w4 : me.φ ≫ tU.G.hom = C.tV.G.hom ≫ e := me.cart.1.w
    rw [Category.assoc, w3, ← Category.assoc, w4, Category.assoc]
  · rw [hm₂, e₂, Category.assoc]
  · have e5 : C.m₁.φ ≫ mR.φ = me.φ ≫ n₁.φ ≫ m.φ := by rw [eR, ← Category.assoc, hm₁, Category.assoc]
    rw [e5, ← e₁, eq₁, Category.assoc]

theorem exists_coord {S : Scheme.{0}} {A R L : Type} [CommRing A] [CommRing R] [AddCommGroup L] [Module R L]
    {G : Over S} [GrpObj G] {G' : Over (Sp R)} [GrpObj G'] (xA : Sp A ⟶ S) (fR : A →+* R) (f : Sp R ⟶ S)
    (hf : spMap fR ≫ xA = f) (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G f φ) (M : LieModel G' (𝟙 (Sp R)) L)
    (v : epsAt xA ⟶ G) (hv : IsTanAt G xA v) :
    ∃ u : L, (M.pt u).left ≫ φ = spMap (dualMap fR) ≫ v.left := by
  have hx : Spec.map (CommRingCat.ofHom fR) ≫ xA = 𝟙 _ ≫ f := by rw [Category.id_comp]; exact hf
  have t := LiePull.tan_pull fR xA _ hx v hv
  obtain ⟨u, hu⟩ := M.onto (LieMove.liftEps h (LieCarrier.epsHom fR xA _ hx ≫ v))
    ((LieMove.tan_iff h _).2 (by rw [LieMove.push_lift]; exact t))
  exact ⟨u, by rw [hu, LieMove.liftEps_left]; rfl⟩

theorem indep_of_frame {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (hs : Smooth G.hom) {R : Type}
    [CommRing R] (ψ : R →+* ℂ) (xR : Sp R ⟶ S) (y : Sp ℂ ⟶ S) (hy : spMap ψ ≫ xR = y) {g n : ℕ}
    (M : LieModel G xR (Fin g → R)) (u : Fin n → Fin g → R) {O : Type} [CommRing O] (act : OAct O G) (τ : O →+* ℂ)
    (v : Fin n → (epsAt y ⟶ G)) (hv : IsEigFrame act y τ v)
    (hu : ∀ i, (v i).left = spMap (dualMap ψ) ≫ (M.pt (u i)).left) :
    LinearIndependent ℂ (fun i b => ψ (u i b)) := by
  classical
  subst hy
  letI := ψ.toAlgebra
  obtain ⟨E', i1, i2, ⟨M'⟩⟩ := GlobalTheory.T.exists_lie_model S G ℂ (spMap ψ ≫ xR)
  obtain ⟨j, hj, hlin, hb⟩ := GlobalTheory.T.lie_model_base_change_map S G R ℂ xR (Fin g → R) E' M M'
  have hv' : v = fun i => M'.pt (j (u i)) :=
    funext fun i => Over.OverMorphism.ext ((hu i).trans (hj _).symm)
  have hcomb := (GlobalTheory.T.lie_model_eigenvectors_action S ℂ G _ E' M').1
  have hind : LinearIndependent ℂ (fun i => j (u i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have c1 : IsComb (Pi.single i 1) v (v i) := by
      rw [hv']
      exact (hcomb _ _ _ _).2 (by simp [Pi.single_apply])
    have c2 : IsComb (Pi.single i 1 + c) v (v i) := by
      rw [hv']
      exact (hcomb _ _ _ _).2 (by simp [Pi.single_apply, add_smul, Finset.sum_add_distrib, hc])
    obtain ⟨c0, -, hun⟩ := (hv.2 (v i) (hv.1 i))
    have e := congrFun ((hun _ c1).trans (hun _ c2).symm) i
    simpa using e
  have hbas := (hb hs g (Pi.basisFun R (Fin g))).1
  let L : (Fin g → ℂ) →ₗ[ℂ] E' := Fintype.linearCombination ℂ (fun k => j (Pi.basisFun R (Fin g) k))
  have hL : ∀ x : Fin g → R, L (fun k => ψ (x k)) = j x := by
    intro x
    have ex : x = ∑ k, x k • Pi.basisFun R (Fin g) k := ((Pi.basisFun R (Fin g)).sum_repr x).symm
    conv_rhs => rw [ex, map_sum]
    simp only [L, Fintype.linearCombination_apply, hlin]
    rfl
  refine LinearIndependent.of_comp L ?_
  have : L ∘ (fun i b => ψ (u i b)) = fun i => j (u i) := funext fun i => hL (u i)
  rw [this]
  exact hind

theorem exists_vec (Y : Model Xo c β) {σ' : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ' n a) (k' : C.V ⟶ Xo.XF c)
    (φ₀ : C.tV.G.left ⟶ Y.oF.t.G.left) {f : Sp C.R ⟶ Y.X} (mR : SABMap C.t Y.t f)
    (hk : k' ≫ pullback.fst _ _ = C.k) (h₁ : φ₀ ≫ Y.oF.t.G.hom = C.tV.G.hom ≫ k')
    (h₂ : φ₀ ≫ Y.m0.toSABMap.φ = C.m₂.φ) (h₃ : φ₀ ≫ Y.m.φ = C.m₁.φ ≫ mR.φ)
    (p : Sp ℂ ⟶ C.V) (ψz : C.R →+* ℂ) (hp : p ≫ C.j = spMap ψz) (u : Fin C.g → C.R) :
    ∃ (v : epsAt (under (p ≫ k')) ⟶ Xo.univ.t.G) (v₀ : epsAt ((p ≫ k') ≫ Y.j) ⟶ Y.t.G)
      (uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left), SameVec Y (p ≫ k') v v₀ ∧ uu ≫ C.m₂.φ = v.left ∧
      uu ≫ C.m₁.φ = spMap (dualMap ψz) ≫ (C.M.pt u).left ∧
      v₀.left = spMap (dualMap ψz) ≫ (C.M.pt u).left ≫ mR.φ := by
  have hq : IsPullback C.m₁.φ C.tV.G.hom C.t.G.hom C.j := C.m₁.cart.1
  have hsq : spMap (dualMap ψz) ≫ spMap (algebraMap C.R (DualNumber C.R)) =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap ψz := by
    rw [← spMap_comp', ← spMap_comp']
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have w : (spMap (dualMap ψz) ≫ (C.M.pt u).left) ≫ C.t.G.hom =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p) ≫ C.j := by
    have w₀ : (C.M.pt u).left ≫ C.t.G.hom = spMap (algebraMap C.R (DualNumber C.R)) ≫ 𝟙 _ := Over.w (C.M.pt u)
    rw [Category.assoc, w₀, Category.comp_id, hsq, Category.assoc, hp]
  have l₁ : hq.lift _ _ w ≫ C.m₁.φ = _ := hq.lift_fst _ _ w
  have l₂ : hq.lift _ _ w ≫ C.tV.G.hom = _ := hq.lift_snd _ _ w
  have w₂ : C.m₂.φ ≫ Xo.univ.t.G.hom = C.tV.G.hom ≫ C.k := C.m₂.cart.1.w
  have hu₁ : (hq.lift _ _ w ≫ φ₀) ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p ≫ k' := by
    rw [Category.assoc, h₁, ← Category.assoc, l₂]
    simp only [Category.assoc]
  refine ⟨Over.homMk (hq.lift _ _ w ≫ C.m₂.φ) ?_, Over.homMk (hq.lift _ _ w ≫ φ₀ ≫ Y.m.φ) ?_, hq.lift _ _ w,
    ⟨hq.lift _ _ w ≫ φ₀, hu₁, ?_, ?_⟩, rfl, l₁, ?_⟩
  · show (hq.lift _ _ w ≫ C.m₂.φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (p ≫ k') ≫ pullback.fst _ _
    rw [Category.assoc, w₂, ← Category.assoc, l₂, ← hk]
    simp only [Category.assoc]
  · have w₃ : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j := Y.m.cart.1.w
    show (hq.lift _ _ w ≫ φ₀ ≫ Y.m.φ) ≫ Y.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (p ≫ k') ≫ Y.j
    simp only [Category.assoc]
    rw [w₃, ← Category.assoc φ₀, h₁, ← Category.assoc, ← Category.assoc, l₂]
    simp only [Category.assoc]
  · rw [Category.assoc, h₂]; rfl
  · rw [Category.assoc]; rfl
  · show hq.lift _ _ w ≫ φ₀ ≫ Y.m.φ = _
    rw [h₃, ← Category.assoc, l₁, Category.assoc]

theorem spMap_dual {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← LiePull.dualMap_comp, spMap_comp']

theorem chart_unit (Y : Model Xo c β) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (A : Y.X.Opens) (hA : IsAffineOpen A)
    {EB : Type} [AddCommGroup EB] [Module Γ(Y.X, A) EB] (MB : LieModel Y.t.G hA.fromSpec EB) (e₁ : Fin D.p → EB)
    (e₂ : Fin D.q → EB) (h1 : 1 ≤ D.p + D.q) (hr1 : τ (H.rt : E) = H.rt0) (hr2 : σ (tauIn c τ H.rt) = H.rt0)
    (hU : IsUnitAn τ σ Φ) {d a : ℕ} (C : BdryChart Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) d a)
    (fR : Γ(Y.X, A) →+* C.R) (f : Sp C.R ⟶ Y.X) (hf : spMap fR ≫ hA.fromSpec = f) (mR : SABMap C.t Y.t f)
    (k' : C.V ⟶ Xo.XF c) (φ₀ : C.tV.G.left ⟶ Y.oF.t.G.left) (hk : k' ≫ pullback.fst _ _ = C.k)
    (hkj : k' ≫ Y.j = C.j ≫ f) (h₁ : φ₀ ≫ Y.oF.t.G.hom = C.tV.G.hom ≫ k') (h₂ : φ₀ ≫ Y.m0.toSABMap.φ = C.m₂.φ)
    (h₃ : φ₀ ≫ Y.m.φ = C.m₁.φ ≫ mR.φ)
    (hover : ∀ z ∈ ball (0 : Fin d → ℂ) 1, (spMap ((C.ψ z).comp fR) ≫ hA.fromSpec) ≫ Y.s = spMap (σ.comp β))
    (hsnd : ∀ z ∈ punct d a 1, (C.pt z ≫ k') ≫ pullback.snd _ _ = spMap σ)
    (hframe : ∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G))
      (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → y ≫ Y.s = spMap (σ.comp β) →
      (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) →
      (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) →
      IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) v ∧
        IsEigFrame Y.t.act y (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w) :
    ∃ (ρ' : ℝ) (h₀ : (Fin d → ℂ) → ℂ), 0 < ρ' ∧ ρ' ≤ 1 ∧ DifferentiableOn ℂ h₀ (ball 0 ρ') ∧
      (∀ z ∈ ball (0 : Fin d → ℂ) ρ', h₀ z ≠ 0) ∧ ∀ z ∈ punct d a ρ', ∀ (v : Vecs (C.pt z ≫ k') D.p)
        (w : Vecs (C.pt z ≫ k') D.q) (v₀ : Fin D.p → (epsAt ((C.pt z ≫ k') ≫ Y.j) ⟶ Y.t.G))
        (w₀ : Fin D.q → (epsAt ((C.pt z ≫ k') ≫ Y.j) ⟶ Y.t.G)),
        (∀ i, SameVec Y (C.pt z ≫ k') (v i) (v₀ i)) → (∀ j, SameVec Y (C.pt z ≫ k') (w j) (w₀ j)) →
        (∀ i, (v₀ i).left = spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₁ i)).left) →
        (∀ j, (w₀ j).left = spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₂ j)).left) →
        h₀ z = Φ (C.pt z ≫ k') v w := by
  classical
  have hs : Smooth Y.t.G.hom := Y.t.semi.smooth
  choose u₁ hu₁ using fun i => exists_coord hA.fromSpec fR f hf mR.φ mR.cart C.M (MB.pt (e₁ i)) (MB.tan _)
  choose u₂ hu₂ using fun j => exists_coord hA.fromSpec fR f hf mR.φ mR.cart C.M (MB.pt (e₂ j)) (MB.tan _)
  have hy0 : spMap (C.ψ 0) ≫ 𝟙 _ ≫ f = spMap ((C.ψ 0).comp fR) ≫ hA.fromSpec := by
    rw [Category.id_comp, ← hf, spMap_comp', Category.assoc]
  have hfr0 := hframe ((C.ψ 0).comp fR) _
    (fun i => LieCarrier.epsHom ((C.ψ 0).comp fR) hA.fromSpec _ rfl ≫ MB.pt (e₁ i))
    (fun j => LieCarrier.epsHom ((C.ψ 0).comp fR) hA.fromSpec _ rfl ≫ MB.pt (e₂ j)) rfl
    (hover 0 (mem_ball_self one_pos)) (fun _ => rfl) (fun _ => rfl)
  have ind₁ := indep_of_frame hs (C.ψ 0) (𝟙 _ ≫ f) _ hy0 (LieMove.pushModel mR.cart C.M) u₁ Y.t.act _ _ hfr0.1
    (fun i => by
      show spMap (dualMap ((C.ψ 0).comp fR)) ≫ (MB.pt (e₁ i)).left =
        spMap (dualMap (C.ψ 0)) ≫ (C.M.pt (u₁ i)).left ≫ mR.φ
      rw [hu₁, spMap_dual, Category.assoc])
  have ind₂ := indep_of_frame hs (C.ψ 0) (𝟙 _ ≫ f) _ hy0 (LieMove.pushModel mR.cart C.M) u₂ Y.t.act _ _ hfr0.2
    (fun j => by
      show spMap (dualMap ((C.ψ 0).comp fR)) ≫ (MB.pt (e₂ j)).left =
        spMap (dualMap (C.ψ 0)) ≫ (C.M.pt (u₂ j)).left ≫ mR.φ
      rw [hu₂, spMap_dual, Category.assoc])
  have key : ∀ z ∈ punct d a 1, ∃ (v : Vecs (C.pt z ≫ k') D.p) (w : Vecs (C.pt z ≫ k') D.q)
      (v₀ : Fin D.p → (epsAt ((C.pt z ≫ k') ≫ Y.j) ⟶ Y.t.G))
      (w₀ : Fin D.q → (epsAt ((C.pt z ≫ k') ≫ Y.j) ⟶ Y.t.G)),
      IsFramed Set.univ τ σ (C.pt z ≫ k') v w ∧ (∀ i, SameVec Y (C.pt z ≫ k') (v i) (v₀ i)) ∧
      (∀ j, SameVec Y (C.pt z ≫ k') (w j) (w₀ j)) ∧
      (∀ i, (v₀ i).left = spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₁ i)).left) ∧
      (∀ j, (w₀ j).left = spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₂ j)).left) ∧
      (∀ i, ∃ uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left, uu ≫ C.m₂.φ = (v i).left ∧
        uu ≫ C.m₁.φ = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (u₁ i)).left) ∧
      (∀ j, ∃ uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left, uu ≫ C.m₂.φ = (w j).left ∧
        uu ≫ C.m₁.φ = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (u₂ j)).left) := by
    intro z hz
    have hp := (C.pt_eq z hz).1
    choose v v₀ uu a1 a2 a3 a4 using fun i =>
      exists_vec Y C k' φ₀ mR hk h₁ h₂ h₃ (C.pt z) (C.ψ z) hp (u₁ i)
    choose w w₀ uw b1 b2 b3 b4 using fun j =>
      exists_vec Y C k' φ₀ mR hk h₁ h₂ h₃ (C.pt z) (C.ψ z) hp (u₂ j)
    have c1 : ∀ i, (v₀ i).left = spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₁ i)).left := fun i => by
      have e₁' := a4 i
      rw [hu₁ i] at e₁'
      have q : spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₁ i)).left =
          spMap (dualMap (C.ψ z)) ≫ spMap (dualMap fR) ≫ (MB.pt (e₁ i)).left := by
        rw [spMap_dual, Category.assoc]
      exact e₁'.trans q.symm
    have c2 : ∀ j, (w₀ j).left = spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₂ j)).left := fun j => by
      have e₂' := b4 j
      rw [hu₂ j] at e₂'
      have q : spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₂ j)).left =
          spMap (dualMap (C.ψ z)) ≫ spMap (dualMap fR) ≫ (MB.pt (e₂ j)).left := by
        rw [spMap_dual, Category.assoc]
      exact e₂'.trans q.symm
    have hy : (C.pt z ≫ k') ≫ Y.j = spMap ((C.ψ z).comp fR) ≫ hA.fromSpec := by
      rw [Category.assoc, hkj, ← Category.assoc, hp, spMap_comp', Category.assoc, hf]
    have hf2 := hframe ((C.ψ z).comp fR) ((C.pt z ≫ k') ≫ Y.j) v₀ w₀ hy (by rw [hy]; exact hover z hz.1) c1 c2
    exact ⟨v, w, v₀, w₀, GlobalTheory.T.vectors_at_complex_point E H D l Xo c O β Y τ σ _ v w v₀ w₀ (hsnd z hz) a1 b1 hf2.1 hf2.2, a1, b1,
      c1, c2, fun i => ⟨uu i, a2 i, a3 i⟩, fun j => ⟨uw j, b2 j, b3 j⟩⟩
  choose v w v₀ w₀ hF hS₁ hS₂ hc₁ hc₂ hl₁ hl₂ using key
  let φ : (Fin d → ℂ) → ℂ := fun z => if hz : z ∈ punct d a 1 then Φ (C.pt z ≫ k') (v z hz) (w z hz) else 0
  obtain ⟨ρ', h₀, hρ', hρ1, hd, hne, hφ⟩ := GlobalTheory.T.boundary_chart_frame_growth E H D l Xo c τ σ Φ d a C k' u₁ u₂ φ h1 hr2 hr1 hU hk ind₁ ind₂
    (fun z hz => ⟨v z hz, w z hz, hF z hz, hl₁ z hz, hl₂ z hz, by simp only [φ, dif_pos hz]⟩)
  refine ⟨ρ', h₀, hρ', hρ1, hd, hne, ?_⟩
  intro z hz vv ww vv₀ ww₀ s1 s2 t1 t2
  have hz1 : z ∈ punct d a 1 := ⟨ball_subset_ball hρ1 hz.1, hz.2⟩
  have e₀ : vv₀ = v₀ z hz1 := funext fun i => Over.OverMorphism.ext ((t1 i).trans (hc₁ z hz1 i).symm)
  have f₀ : ww₀ = w₀ z hz1 := funext fun j => Over.OverMorphism.ext ((t2 j).trans (hc₂ z hz1 j).symm)
  have e₁' : vv = v z hz1 := funext fun i => SameVec.unique_left (s1 i) (by rw [e₀]; exact hS₁ z hz1 i)
  have f₁ : ww = w z hz1 := funext fun j => SameVec.unique_left (s2 j) (by rw [f₀]; exact hS₂ z hz1 j)
  rw [hφ z hz]
  simp only [φ, dif_pos hz1, e₁', f₁]

end GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily

theorem GlobalTheory.CompanionTheory.Ar.Flat.flat_unit_along_families : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (s' : X' ⟶ Sp c.F) (d : ℕ) (W' : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c) (A : Y.X.Opens) (hA : IsAffineOpen A) (EB : Type) [AddCommGroup EB] [Module Γ(Y.X, A) EB] (MB : LieModel Y.t.G hA.fromSpec EB) (e₁ : Fin D.p → EB) (e₂ : Fin D.q → EB) (x : Sp ℂ ⟶ X'), 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → IsUnitAn τ σ Φ → π ≫ Y.s = s' ≫ spMap β → SmoothOfRelativeDimension d s' → Geo.ResK.HasSncCoords s' d (W' : Set X')ᶜ → jW ≫ Y.j = W'.ι ≫ π → jW ≫ pullback.snd _ _ = W'.ι ≫ s' → x ≫ s' = spMap σ → ⊤ ≤ x ⁻¹ᵁ (π ⁻¹ᵁ A) → (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → y ≫ Y.s = spMap (σ.comp β) → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) v ∧ IsEigFrame Y.t.act y (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w) → ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X')), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s' = spMap σ) → ∀ b₀ ∈ B, y b₀ = x → ∃ (ε : ℝ) (h : (Fin m → ℂ) → ℂ), 0 < ε ∧ DifferentiableOn ℂ h (Metric.ball b₀ ε) ∧ h b₀ ≠ 0 ∧ ∀ b ∈ B ∩ Metric.ball b₀ ε, ∃ f : Γ(Y.X, A) →+* ℂ, spMap f ≫ hA.fromSpec = y b ≫ π ∧ (⊤ ≤ y b ⁻¹ᵁ W' → ∀ (yy : Sp ℂ ⟶ Xo.XF c) (v : Vecs yy D.p) (w : Vecs yy D.q) (v₀ : Fin D.p → (epsAt (yy ≫ Y.j) ⟶ Y.t.G)) (w₀ : Fin D.q → (epsAt (yy ≫ Y.j) ⟶ Y.t.G)), yy ≫ Y.j = y b ≫ π → yy ≫ pullback.snd _ _ = spMap σ → (∀ i, SameVec Y yy (v i) (v₀ i)) → (∀ j, SameVec Y yy (w j) (w₀ j)) → (∀ i, (v₀ i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w₀ j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → h b = Φ yy v w) := by
  intro E _ _ _ H D l Xo c O _ β Y τ σ Φ X' π s' d W' jW A hA EB _ _ MB e₁ e₂ x h1 hr1 hr2 hU hπ hsm hsnc hj1 hj2 hxs hxA
    hframe m B y hB hy hyσ b₀ hb₀ hyb
  obtain ⟨V, hV, a, ψ, hVA, ha, hol, h0, -, hpts, hfam⟩ :=
    GlobalTheory.T.holomorphic_affine_polydisc_chart c.F σ X' s' d ((W' : Set X')ᶜ) hsm hsnc x (π ⁻¹ᵁ A) hxs hxA
  have hpt : ∀ z ∈ punct d a 1, spMap (ψ z) ≫ hV.fromSpec ≫ s' = spMap σ ∧
      centre (spMap (ψ z) ≫ hV.fromSpec) ∈ W' := fun z hz =>
    ⟨(hpts z hz.1).1, not_not.1 ((hpts z hz.1).2.2 hz)⟩
  obtain ⟨ρ, C, i₀, mR, k', φ₀, hρ, hρ1, hψ, hk, hkj, hks, h₁, h₂, h₃⟩ :=
    GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.exists_model_chart Y σ π s' d W' jW hj1 hj2 V hV a ψ ha hol hpt
  let aV : Γ(Y.X, A) →+* Γ(X', V) := (π.appLE A V hVA).hom
  have haV : spMap aV ≫ hA.fromSpec = hV.fromSpec ≫ π := IsAffineOpen.SpecMap_appLE_fromSpec π hA hV hVA
  let g : Γ(X', V) →+* C.R := (Spec.preimage i₀).hom
  have hg : spMap g = i₀ := Spec.map_preimage i₀
  have hfR : spMap (g.comp aV) ≫ hA.fromSpec = i₀ ≫ hV.fromSpec ≫ π := by
    rw [GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.spMap_comp', Category.assoc, haV, hg]
  have hin : ∀ z ∈ ball (0 : Fin d → ℂ) 1, (ρ : ℂ) • z ∈ ball (0 : Fin d → ℂ) 1 := fun z hz => by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    nlinarith [norm_nonneg z]
  have hover : ∀ z ∈ ball (0 : Fin d → ℂ) 1,
      (spMap ((C.ψ z).comp (g.comp aV)) ≫ hA.fromSpec) ≫ Y.s = spMap (σ.comp β) := fun z hz => by
    have e : spMap ((C.ψ z).comp (g.comp aV)) ≫ hA.fromSpec = spMap (C.ψ z) ≫ i₀ ≫ hV.fromSpec ≫ π := by
      rw [GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.spMap_comp', Category.assoc, hfR]
    rw [e]
    calc (spMap (C.ψ z) ≫ i₀ ≫ hV.fromSpec ≫ π) ≫ Y.s = (spMap (C.ψ z) ≫ i₀) ≫ hV.fromSpec ≫ s' ≫ spMap β := by
          simp only [Category.assoc, hπ]
      _ = (spMap (ψ ((ρ : ℂ) • z)) ≫ hV.fromSpec ≫ s') ≫ spMap β := by
          rw [hψ z hz]; simp only [Category.assoc]
      _ = _ := by rw [(hpts _ (hin z hz)).1, GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.spMap_comp']
  have hsnd : ∀ z ∈ punct d a 1, (C.pt z ≫ k') ≫ pullback.snd _ _ = spMap σ := fun z hz => by
    rw [Category.assoc, hks, ← Category.assoc, (C.pt_eq z hz).1, ← Category.assoc, hψ z hz.1]
    exact (hpts _ (hin z hz.1)).1
  obtain ⟨ρ', h₀, hρ', hρ'1, hd, hne, hφ⟩ := GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.chart_unit Y τ σ Φ A hA MB e₁ e₂ h1 hr1 hr2 hU C
    (g.comp aV) _ hfR mR k' φ₀ hk (by rw [hkj]) h₁ h₂ h₃ hover hsnd hframe
  obtain ⟨ε₁, κ, hε₁, hsub, hκd, hκ0, hκ⟩ := hfam m B y hB hy hyσ b₀ hb₀ hyb
  have hκc : ContinuousAt κ b₀ := hκd.continuousOn.continuousAt (ball_mem_nhds _ hε₁)
  obtain ⟨ε₂, hε₂, hb⟩ := Metric.continuousAt_iff.1 hκc (ρ * ρ') (mul_pos hρ hρ')
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hn : ∀ b ∈ ball b₀ (min ε₁ ε₂), (ρ : ℂ)⁻¹ • κ b ∈ ball (0 : Fin d → ℂ) ρ' := fun b hbε => by
    have h3 := hb (ball_subset_ball (min_le_right _ _) hbε)
    rw [hκ0, dist_zero_right] at h3
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le, inv_mul_lt_iff₀ hρ]
    exact h3
  refine ⟨min ε₁ ε₂, fun b => h₀ ((ρ : ℂ)⁻¹ • κ b), lt_min hε₁ hε₂, ?_, ?_, ?_⟩
  · have hdk : DifferentiableOn ℂ (fun b => (ρ : ℂ)⁻¹ • κ b) (ball b₀ (min ε₁ ε₂)) :=
      ((hκd.mono (ball_subset_ball (min_le_left ε₁ ε₂))).const_smul ((ρ : ℂ)⁻¹)).congr fun _ _ => rfl
    exact hd.comp hdk hn
  · exact hne _ (hn b₀ (mem_ball_self (lt_min hε₁ hε₂)))
  rintro b ⟨hbB, hbε⟩
  have hbε₁ : b ∈ ball b₀ ε₁ := ball_subset_ball (min_le_left _ _) hbε
  obtain ⟨hκb, hyb'⟩ := hκ b hbε₁
  refine ⟨(ψ (κ b)).comp aV, ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.spMap_comp', Category.assoc, haV, hyb', Category.assoc]
  intro hW yy v w v₀ w₀ hyj hys hv hw hv₀ hw₀
  have hρz : (ρ : ℂ) • ((ρ : ℂ)⁻¹ • κ b) = κ b := smul_inv_smul₀ hρc _
  have hcen : centre (spMap (ψ (κ b)) ≫ hV.fromSpec) ∉ ((W' : Set X')ᶜ) := by
    rw [← hyb']
    exact not_not.2 (hW (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial))
  have hκp : κ b ∈ punct d a 1 := (hpts _ hκb).2.1 hcen
  have hz : (ρ : ℂ)⁻¹ • κ b ∈ punct d a ρ' := ⟨hn b hbε, fun i hi => by
    simpa [hρ.ne'] using hκp.2 i hi⟩
  have hz1 : (ρ : ℂ)⁻¹ • κ b ∈ punct d a 1 := ⟨ball_subset_ball hρ'1 hz.1, hz.2⟩
  have hpz := (C.pt_eq _ hz1).1
  have hpψ : spMap (C.ψ ((ρ : ℂ)⁻¹ • κ b)) ≫ i₀ = spMap (ψ (κ b)) := by
    rw [hψ _ hz1.1, hρz]
  have hyy : yy = C.pt ((ρ : ℂ)⁻¹ • κ b) ≫ k' := by
    have : IsOpenImmersion Y.jQ := Y.jQ_open
    rw [← cancel_mono Y.jQ]
    apply pullback.hom_ext
    · have e1 : yy ≫ Y.j = (C.pt ((ρ : ℂ)⁻¹ • κ b) ≫ k') ≫ Y.j := by
        rw [hyj, hyb', Category.assoc _ k', hkj, ← Category.assoc, hpz, ← Category.assoc (spMap _), hpψ]
        simp only [Category.assoc]
      simpa only [Model.j, Category.assoc] using e1
    · rw [Category.assoc, Category.assoc, Y.jQ_over, hys]
      exact (hsnd _ hz1).symm
  subst hyy
  have hf : (ψ (κ b)).comp aV = (C.ψ ((ρ : ℂ)⁻¹ • κ b)).comp (g.comp aV) := by
    have e : spMap ((ψ (κ b)).comp aV) = spMap ((C.ψ ((ρ : ℂ)⁻¹ • κ b)).comp (g.comp aV)) := by
      rw [← cancel_mono hA.fromSpec, GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.spMap_comp', GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.spMap_comp',
        Category.assoc, Category.assoc, hfR, haV, ← Category.assoc (spMap _) i₀, hpψ]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  rw [hf] at hv₀ hw₀
  exact hφ _ hz v w v₀ w₀ hv hw hv₀ hw₀
