import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsUnitExtensionOfLogGrowth
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramPullbackIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramBoundNearBoundaryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

theorem spMap_comp' {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : A →+* B) (g : B →+* C') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem dualMap_comp' {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : A →+* B) (g : B →+* C') :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

theorem dualMap_comp_algebraMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (dualMap f).comp (algebraMap A (DualNumber A)) = (algebraMap B (DualNumber B)).comp f := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem eq_of_cart {P Q A B T : Scheme.{0}} {φ : P ⟶ Q} {p : P ⟶ A} {q : Q ⟶ B} {j : A ⟶ B} [Mono j]
    (hp : IsPullback φ p q j) {x y : T ⟶ P} (h : x ≫ φ = y ≫ φ) : x = y := by
  refine hp.hom_ext h ?_
  rw [← cancel_mono j, Category.assoc, Category.assoc, ← hp.w, ← Category.assoc, h, Category.assoc]

theorem le_of_sq_le {y A L : ℝ} {N N' : ℕ} (hA : 0 ≤ A) (hL : 1 ≤ L) (h : y ^ 2 ≤ A * L ^ N) :
    y ≤ (1 + A) * L ^ (N + N') := by
  have h1 : (1 : ℝ) ≤ L ^ (N + N') := one_le_pow₀ hL
  have h2 : L ^ N ≤ L ^ (N + N') := pow_le_pow_right₀ hL (Nat.le_add_right _ _)
  have h3 : y ≤ 1 + y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have h4 : A * L ^ N ≤ A * L ^ (N + N') := mul_le_mul_of_nonneg_left h2 hA
  nlinarith

theorem norm_bounds_of_gram {x g d K₁ K₂ L : ℝ} {N₁ N₂ : ℕ} (hx : 0 < x) (hg : 0 ≤ g) (hd : 0 ≤ d) (hL : 1 ≤ L)
    (h : x ^ 2 * g = d) (g1 : g ≤ K₁) (g2 : 1 ≤ K₁ * L ^ N₁ * g) (d1 : d ≤ K₂) (d2 : 1 ≤ K₂ * L ^ N₂ * d) :
    x ≤ (1 + |K₁ * K₂|) * L ^ (N₁ + N₂) ∧ x⁻¹ ≤ (1 + |K₁ * K₂|) * L ^ (N₁ + N₂) := by
  have hLp : 0 < L := by linarith
  have hK₁ : 0 ≤ K₁ := hg.trans g1
  have hK₂ : 0 ≤ K₂ := hd.trans d1
  have hA : |K₁ * K₂| = K₁ * K₂ := abs_of_nonneg (mul_nonneg hK₁ hK₂)
  rw [hA]
  have hA0 : 0 ≤ K₁ * K₂ := mul_nonneg hK₁ hK₂
  have hx2 : 0 < x ^ 2 := by positivity
  constructor
  · refine le_of_sq_le hA0 hL ?_
    have e : x ^ 2 * (K₁ * L ^ N₁ * g) = K₁ * L ^ N₁ * d := by rw [← h]; ring
    have p1 : x ^ 2 ≤ x ^ 2 * (K₁ * L ^ N₁ * g) := le_mul_of_one_le_right hx2.le g2
    have p2 : K₁ * L ^ N₁ * d ≤ K₁ * L ^ N₁ * K₂ := mul_le_mul_of_nonneg_left d1 (by positivity)
    calc x ^ 2 ≤ _ := p1
      _ = _ := e
      _ ≤ _ := p2
      _ = _ := by ring
  · rw [Nat.add_comm N₁ N₂]
    refine le_of_sq_le hA0 hL ?_
    have hi : x⁻¹ ^ 2 * x ^ 2 = 1 := by field_simp
    have hi0 : 0 < x⁻¹ ^ 2 := by positivity
    have p1 : x⁻¹ ^ 2 ≤ x⁻¹ ^ 2 * (K₂ * L ^ N₂ * d) := le_mul_of_one_le_right hi0.le d2
    have e : x⁻¹ ^ 2 * (K₂ * L ^ N₂ * d) = K₂ * L ^ N₂ * g := by
      rw [← h]; calc _ = (x⁻¹ ^ 2 * x ^ 2) * (K₂ * L ^ N₂ * g) := by ring
        _ = _ := by rw [hi, _root_.one_mul]
    have p2 : K₂ * L ^ N₂ * g ≤ K₂ * L ^ N₂ * K₁ := mul_le_mul_of_nonneg_left g1 (by positivity)
    calc x⁻¹ ^ 2 ≤ _ := p1
      _ = _ := e
      _ ≤ _ := p2
      _ = _ := by ring

theorem exists_away_family {R : Type} [CommRing R] {n : ℕ} (ψ : (Fin n → ℂ) → (R →+* ℂ)) (r : R)
    {B : Set (Fin n → ℂ)} {b₀ : Fin n → ℂ} (hb₀ : b₀ ∈ B) (hr : ∀ b ∈ B, ψ b r ≠ 0)
    (hd : ∀ x : R, DifferentiableOn ℂ (fun b => ψ b x) B) :
    ∃ ψ' : (Fin n → ℂ) → (Localization.Away r →+* ℂ),
      (∀ b ∈ B, (ψ' b).comp (algebraMap R (Localization.Away r)) = ψ b) ∧
      ∀ x, DifferentiableOn ℂ (fun b => ψ' b x) B := by
  classical
  have hu : ∀ b ∈ B, IsUnit (ψ b r) := fun b hb => isUnit_iff_ne_zero.2 (hr b hb)
  let ψ' : (Fin n → ℂ) → (Localization.Away r →+* ℂ) := fun b =>
    if h : b ∈ B then IsLocalization.Away.lift r (hu b h) else IsLocalization.Away.lift r (hu b₀ hb₀)
  have hc : ∀ b ∈ B, (ψ' b).comp (algebraMap R (Localization.Away r)) = ψ b := by
    intro b hb
    ext x
    simp only [ψ', dif_pos hb, RingHom.comp_apply]
    exact IsLocalization.Away.lift_eq r (hu b hb) x
  refine ⟨ψ', hc, fun x => ?_⟩
  obtain ⟨k, a, hx⟩ := IsLocalization.Away.surj r x
  have e : ∀ b ∈ B, ψ' b x = ψ b a / ψ b r ^ k := by
    intro b hb
    have h1 := congrArg (ψ' b) hx
    have h2 : ∀ y, ψ' b (algebraMap R _ y) = ψ b y := fun y => by
      rw [← hc b hb]; rfl
    rw [map_mul, map_pow, h2, h2] at h1
    rw [eq_div_iff (pow_ne_zero _ (hr b hb))]
    exact h1
  have hp : DifferentiableOn ℂ (fun b => ψ b r ^ k) B := fun b hb => ((hd r) b hb).pow k
  have hi : DifferentiableOn ℂ (fun b => (ψ b r ^ k)⁻¹) B :=
    fun b hb => (hp b hb).inv (pow_ne_zero _ (hr b hb))
  have hq : DifferentiableOn ℂ (fun b => ψ b a * (ψ b r ^ k)⁻¹) B := fun b hb => (hd a b hb).mul (hi b hb)
  exact hq.congr fun b hb => by rw [e b hb, div_eq_mul_inv]

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σK : KA l →+* ℂ} {n a : ℕ}

theorem BdryChart.pt_w (C : BdryChart Xo σK n a) {R' : Type} [CommRing R'] (f : C.R →+* R') (e : Fin C.g → C.R) :
    (spMap (dualMap f) ≫ (C.M.pt e).left) ≫ C.t.G.hom =
      spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
  have h : (C.M.pt e).left ≫ C.t.G.hom = spMap (algebraMap C.R (DualNumber C.R)) ≫ 𝟙 _ := Over.w (C.M.pt e)
  rw [Category.assoc, h, Category.comp_id, spMap_comp', spMap_comp', dualMap_comp_algebraMap]

def BdryChart.val (C : BdryChart Xo σK n a) (z : Fin n → ℂ) (e : Fin C.g → C.R) :
    epsAt (spMap (C.ψ z)) ⟶ C.t.G :=
  Over.homMk (spMap (dualMap (C.ψ z)) ≫ (C.M.pt e).left) (C.pt_w _ e)

theorem BdryChart.isVal_val (C : BdryChart Xo σK n a) (z : Fin n → ℂ) {m : ℕ} (u : Fin m → Fin C.g → C.R) :
    C.IsVal z u (fun i => C.val z (u i)) := fun _ => rfl

theorem BdryChart.tan_w (C : BdryChart Xo σK n a) {z : Fin n → ℂ} (hz : z ∈ punct n a 1) {e : Fin C.g → C.R}
    {uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left} (h : uu ≫ C.m₁.φ = spMap (dualMap (C.ψ z)) ≫ (C.M.pt e).left) :
    uu ≫ C.tV.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ C.pt z := by
  haveI := C.j_open
  rw [← cancel_mono C.j, Category.assoc, Category.assoc, (C.pt_eq z hz).1]
  have hw := C.m₁.cart.1.w
  rw [← hw, ← Category.assoc, h]
  exact C.pt_w _ e

theorem BdryChart.hodgeGram_iff (C : BdryChart Xo σK n a) {z : Fin n → ℂ} (hz : z ∈ punct n a 1)
    {x : Sp ℂ ⟶ Xo.X} (hx : x = C.pt z ≫ C.k) {m : ℕ} (u : Fin m → Fin C.g → C.R)
    (v : Fin m → (epsAt x ⟶ Xo.univ.t.G))
    (hv : ∀ i, ∃ uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left, uu ≫ C.m₂.φ = (v i).left ∧
      uu ≫ C.m₁.φ = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (u i)).left)
    (v' : Fin m → (epsAt (spMap (C.ψ z)) ⟶ C.t.G)) (hv' : C.IsVal z u v') (Γ : Matrix (Fin m) (Fin m) ℂ) :
    IsHodgeGram C.t.G C.t.PP.L (spMap (C.ψ z)) v' Γ ↔
      IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L x v Γ := by
  choose uu h₂ h₁ using hv
  let t : Fin m → (epsAt (C.pt z) ⟶ C.tV.G) := fun i => Over.homMk (uu i) (C.tan_w hz (h₁ i))
  have A := hodgeGram_iff_of_sabMap E H _ _ C.t C.tV C.j C.m₁ (C.pt z) (spMap (C.ψ z)) m t v' Γ
    (C.pt_eq z hz).1.symm (fun i => (h₁ i).trans (hv' i).symm)
  have B := hodgeGram_iff_of_sabMap E H _ _ Xo.univ.t C.tV C.k C.m₂ (C.pt z) x m t v Γ hx h₂
  exact A.symm.trans B

def BdryChart.liftVec (C : BdryChart Xo σK n a) {R' : Type} [CommRing R'] (f : C.R →+* R') (i : Sp R' ⟶ C.V)
    (hi : i ≫ C.j = spMap f) (e : Fin C.g → C.R) : Sp (DualNumber R') ⟶ C.tV.G.left :=
  C.m₁.cart.1.lift (spMap (dualMap f) ≫ (C.M.pt e).left) (spMap (algebraMap R' (DualNumber R')) ≫ i)
    (by rw [C.pt_w f e, Category.assoc, hi])

theorem BdryChart.liftVec_fst (C : BdryChart Xo σK n a) {R' : Type} [CommRing R'] (f : C.R →+* R') (i : Sp R' ⟶ C.V)
    (hi : i ≫ C.j = spMap f) (e : Fin C.g → C.R) :
    C.liftVec f i hi e ≫ C.m₁.φ = spMap (dualMap f) ≫ (C.M.pt e).left :=
  C.m₁.cart.1.lift_fst _ _ _

theorem BdryChart.liftVec_snd (C : BdryChart Xo σK n a) {R' : Type} [CommRing R'] (f : C.R →+* R') (i : Sp R' ⟶ C.V)
    (hi : i ≫ C.j = spMap f) (e : Fin C.g → C.R) :
    C.liftVec f i hi e ≫ C.tV.G.hom = spMap (algebraMap R' (DualNumber R')) ≫ i :=
  C.m₁.cart.1.lift_snd _ _ _

theorem BdryChart.exists_away (C : BdryChart Xo σK n a) {z : Fin n → ℂ} (hz : z ∈ punct n a 1) :
    ∃ r : C.R, C.ψ z r ≠ 0 ∧ ∃ i : Sp (Localization.Away r) ⟶ C.V,
      i ≫ C.j = spMap (algebraMap C.R (Localization.Away r)) := by
  haveI := C.j_open
  have hopen : IsOpen (Set.range C.j) := C.j.isOpenEmbedding.isOpen_range
  obtain ⟨x⟩ : Nonempty (Sp ℂ) := inferInstance
  have hmem : (spMap (C.ψ z)) x ∈ Set.range C.j := by
    rw [← (C.pt_eq z hz).1]
    exact ⟨(C.pt z) x, by simp⟩
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := ((spMap (C.ψ z)) x : PrimeSpectrum C.R)) hmem hopen
  refine ⟨r, ?_, ?_⟩
  · intro h0
    apply hr
    show C.ψ z r ∈ x.asIdeal
    rw [h0]
    exact Ideal.zero_mem _
  · have hrange : Set.range (spMap (algebraMap C.R (Localization.Away r))) ⊆ Set.range C.j := by
      refine subset_trans ?_ hsub
      have := PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
      exact this.le
    exact ⟨IsOpenImmersion.lift C.j _ hrange, IsOpenImmersion.lift_fac _ _ _⟩

end Chart

theorem punct_mono {n a : ℕ} {ρ ρ' : ℝ} (h : ρ ≤ ρ') : punct n a ρ ⊆ punct n a ρ' :=
  fun _ hz => ⟨Metric.ball_subset_ball h hz.1, hz.2⟩

theorem isOpen_punct_set (n a : ℕ) (ρ : ℝ) : IsOpen (punct n a ρ) := by
  have e : punct n a ρ = Metric.ball 0 ρ ∩ ⋂ i : Fin n, {z : Fin n → ℂ | i.val < a → z i ≠ 0} := by
    ext z
    simp [punct]
  rw [e]
  refine Metric.isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases h : i.val < a
  · simpa [h] using isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [h]

section Hol

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem isFramed_congr {U : Set (Xo.XF c)} {τ : E →+* ℂ} {F : Type} [Field F] {β : c.F →+* F}
    {y y' : Sp F ⟶ Xo.XF c} (h : y = y') {v : Vecs y D.p} {w : Vecs y D.q} {v' : Vecs y' D.p} {w' : Vecs y' D.q}
    (hv : ∀ i, (v i).left = (v' i).left) (hw : ∀ i, (w i).left = (w' i).left)
    (hf : IsFramed U τ β y v w) : IsFramed U τ β y' v' w' := by
  subst h
  have e₁ : v = v' := funext fun i => Over.OverMorphism.ext (hv i)
  have e₂ : w = w' := funext fun i => Over.OverMorphism.ext (hw i)
  rw [← e₁, ← e₂]
  exact hf

theorem cfn_congr (Φ : CFn Xo c) {y y' : Sp ℂ ⟶ Xo.XF c} (h : y = y') {v : Vecs y D.p} {w : Vecs y D.q}
    {v' : Vecs y' D.p} {w' : Vecs y' D.q}
    (hv : ∀ i, (v i).left = (v' i).left) (hw : ∀ i, (w i).left = (w' i).left) : Φ y v w = Φ y' v' w' := by
  subst h
  have e₁ : v = v' := funext fun i => Over.OverMorphism.ext (hv i)
  have e₂ : w = w' := funext fun i => Over.OverMorphism.ext (hw i)
  rw [e₁, e₂]

theorem differentiableAt_of_chart {τ : E →+* ℂ} {σ : c.F →+* ℂ} {Φ : CFn Xo c} {n a : ℕ}
    (C : BdryChart Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) n a) (k' : C.V ⟶ Xo.XF c)
    (u₁ : Fin D.p → Fin C.g → C.R) (u₂ : Fin D.q → Fin C.g → C.R) (φ : (Fin n → ℂ) → ℂ)
    (hU : IsUnitAn τ σ Φ) (hk : k' ≫ pullback.fst _ _ = C.k)
    (hz : ∀ z ∈ punct n a 1, ∃ (v : Vecs (C.pt z ≫ k') D.p) (w : Vecs (C.pt z ≫ k') D.q),
      IsFramed Set.univ τ σ (C.pt z ≫ k') v w ∧
      (∀ i, ∃ uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left, uu ≫ C.m₂.φ = (v i).left ∧
        uu ≫ C.m₁.φ = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (u₁ i)).left) ∧
      (∀ j, ∃ uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left, uu ≫ C.m₂.φ = (w j).left ∧
        uu ≫ C.m₁.φ = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (u₂ j)).left) ∧ φ z = Φ (C.pt z ≫ k') v w)
    {z₀ : Fin n → ℂ} (hz₀ : z₀ ∈ punct n a 1) : DifferentiableAt ℂ φ z₀ := by
  haveI := C.j_open
  obtain ⟨r, hr, i, hi⟩ := C.exists_away hz₀
  set B : Set (Fin n → ℂ) := punct n a 1 ∩ (Metric.ball 0 1 ∩ (fun b => C.ψ b r) ⁻¹' {0}ᶜ) with hB
  have hBo : IsOpen B := (isOpen_punct_set n a 1).inter
    ((C.hol.2 r).continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton)
  have hb₀ : z₀ ∈ B := ⟨hz₀, hz₀.1, hr⟩
  have hsub : B ⊆ Metric.ball 0 1 := fun b hb => hb.1.1
  obtain ⟨ψ', hψ', hd⟩ := exists_away_family C.ψ r hb₀ (fun b hb => hb.2.2)
    (fun x => (C.hol.2 x).mono hsub)
  let f := algebraMap C.R (Localization.Away r)
  let lv : (Fin C.g → C.R) → (Sp (DualNumber (Localization.Away r)) ⟶ C.tV.G.left) := C.liftVec f i hi
  let x : Sp (Localization.Away r) ⟶ Xo.XF c := i ≫ k'
  have hvw : ∀ e, (lv e ≫ C.m₂.φ) ≫ Xo.univ.t.G.hom =
      spMap (algebraMap (Localization.Away r) (DualNumber (Localization.Away r))) ≫ under x := by
    intro e
    have hw := C.m₂.cart.1.w
    rw [Category.assoc, hw, ← Category.assoc, C.liftVec_snd f i hi e]
    simp only [under, x, Category.assoc, hk]
  have hvb : ∀ b e, (spMap (dualMap (ψ' b)) ≫ lv e ≫ C.m₂.φ) ≫ Xo.univ.t.G.hom =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ under (spMap (ψ' b) ≫ x) := by
    intro b e
    rw [Category.assoc, hvw e, ← Category.assoc, spMap_comp', dualMap_comp_algebraMap, ← spMap_comp']
    simp only [under, Category.assoc]
  let vR : Fin D.p → (epsAt (under x) ⟶ Xo.univ.t.G) := fun a => Over.homMk (lv (u₁ a) ≫ C.m₂.φ) (hvw _)
  let wR : Fin D.q → (epsAt (under x) ⟶ Xo.univ.t.G) := fun a => Over.homMk (lv (u₂ a) ≫ C.m₂.φ) (hvw _)
  let v : ∀ b, Vecs (spMap (ψ' b) ≫ x) D.p := fun b a =>
    Over.homMk (spMap (dualMap (ψ' b)) ≫ lv (u₁ a) ≫ C.m₂.φ) (hvb b _)
  let w : ∀ b, Vecs (spMap (ψ' b) ≫ x) D.q := fun b a =>
    Over.homMk (spMap (dualMap (ψ' b)) ≫ lv (u₂ a) ≫ C.m₂.φ) (hvb b _)
  have hy : ∀ b ∈ B, C.pt b ≫ k' = spMap (ψ' b) ≫ x := by
    intro b hb
    have : C.pt b = spMap (ψ' b) ≫ i := by
      rw [← cancel_mono C.j, (C.pt_eq b hb.1).1, Category.assoc, hi, spMap_comp', hψ' b hb]
    rw [this, Category.assoc]
  have huu : ∀ b ∈ B, ∀ (e : Fin C.g → C.R) (uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left),
      uu ≫ C.m₁.φ = spMap (dualMap (C.ψ b)) ≫ (C.M.pt e).left →
      uu ≫ C.m₂.φ = spMap (dualMap (ψ' b)) ≫ lv e ≫ C.m₂.φ := by
    intro b hb e uu h
    have : uu = spMap (dualMap (ψ' b)) ≫ lv e := by
      refine eq_of_cart C.m₁.cart.1 ?_
      rw [h, Category.assoc, C.liftVec_fst f i hi e, ← Category.assoc, spMap_comp', dualMap_comp', hψ' b hb]
    rw [this, Category.assoc]
  have key : ∀ b ∈ B, IsFramed Set.univ τ σ (spMap (ψ' b) ≫ x) (v b) (w b) ∧
      φ b = Φ (spMap (ψ' b) ≫ x) (v b) (w b) := by
    intro b hb
    obtain ⟨v₀, w₀, hf, hv, hw, he⟩ := hz b hb.1
    have ev : ∀ a, (v₀ a).left = (v b a).left := fun a => by
      obtain ⟨uu, h₂, h₁⟩ := hv a
      rw [← h₂]
      exact huu b hb _ uu h₁
    have ew : ∀ a, (w₀ a).left = (w b a).left := fun a => by
      obtain ⟨uu, h₂, h₁⟩ := hw a
      rw [← h₂]
      exact huu b hb _ uu h₁
    exact ⟨isFramed_congr (hy b hb) ev ew hf, he.trans (cfn_congr Φ (hy b hb) ev ew)⟩
  have hD := hU.hol (Localization.Away r) x vR wR n B ψ' v w hBo hd
    (fun b hb => ⟨(key b hb).1, fun _ => rfl, fun _ => rfl⟩)
  have hφ : DifferentiableOn ℂ φ B := hD.congr fun b hb => (key b hb).2
  exact hφ.differentiableAt (hBo.mem_nhds hb₀)

end Hol

theorem exists_unit_extension_of_bdryChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (n a : ℕ) (C : BdryChart Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) n a) (k' : C.V ⟶ Xo.XF c) (u₁ : Fin D.p → Fin C.g → C.R) (u₂ : Fin D.q → Fin C.g → C.R) (φ : (Fin n → ℂ) → ℂ), 1 ≤ D.p + D.q → σ (tauIn c τ H.rt) = H.rt0 → τ (H.rt : E) = H.rt0 → IsUnitAn τ σ Φ → k' ≫ pullback.fst _ _ = C.k → LinearIndependent ℂ (fun i b => C.ψ 0 (u₁ i b)) → LinearIndependent ℂ (fun i b => C.ψ 0 (u₂ i b)) → (∀ z ∈ punct n a 1, ∃ (v : Vecs (C.pt z ≫ k') D.p) (w : Vecs (C.pt z ≫ k') D.q), IsFramed Set.univ τ σ (C.pt z ≫ k') v w ∧ (∀ i, ∃ uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left, uu ≫ C.m₂.φ = (v i).left ∧ uu ≫ C.m₁.φ = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (u₁ i)).left) ∧ (∀ j, ∃ uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left, uu ≫ C.m₂.φ = (w j).left ∧ uu ≫ C.m₁.φ = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (u₂ j)).left) ∧ φ z = Φ (C.pt z ≫ k') v w) → ∃ (ρ : ℝ) (h : (Fin n → ℂ) → ℂ), 0 < ρ ∧ ρ ≤ 1 ∧ DifferentiableOn ℂ h (ball 0 ρ) ∧ (∀ z ∈ ball (0 : Fin n → ℂ) ρ, h z ≠ 0) ∧ ∀ z ∈ punct n a ρ, h z = φ z := by
  intro E _ _ _ H D l Xo c τ σ Φ n a C k' u₁ u₂ φ hpq hσ hτ hU hk h1 h2 hz
  have hρ : (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := by
    have e : (IntermediateField.inclusion c.le).toRingHom (baseKA l).ρ = tauIn c τ H.rt :=
      Subtype.ext hτ.symm
    rw [RingHom.comp_apply, e]
    exact hσ
  obtain ⟨ρ₁, K₁, N₁, hρ₁, hρ₁', b₁⟩ := GlobalTheory.T.hodge_gram_bound_near_boundary E H D l Xo _ n a C hpq hρ D.p u₁ h1
  obtain ⟨ρ₂, K₂, N₂, hρ₂, hρ₂', b₂⟩ := GlobalTheory.T.hodge_gram_bound_near_boundary E H D l Xo _ n a C hpq hρ D.q u₂ h2
  have hρ0 : 0 < min ρ₁ ρ₂ := lt_min hρ₁ hρ₂
  have hρ1 : min ρ₁ ρ₂ ≤ 1 := (min_le_left _ _).trans hρ₁'
  have hset : ∀ z, z ∈ punct n a (min ρ₁ ρ₂) ↔ z ∈ ball (0 : Fin n → ℂ) (min ρ₁ ρ₂) ∧
      ∀ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), z i ≠ 0 := by
    intro z
    simp [punct]
  obtain ⟨h, hh, hne, heq⟩ := exists_unit_extension_of_log_growth n
    (Finset.univ.filter (fun i : Fin n => i.val < a)) φ (min ρ₁ ρ₂) (1 + |K₁ * K₂|) (N₁ + N₂) hρ0
    (fun z hz' => (differentiableAt_of_chart C k' u₁ u₂ φ hU hk hz
      (punct_mono hρ1 ((hset z).2 hz'))).differentiableWithinAt)
    (fun z hz₁ hz₂ => by
      have hp : z ∈ punct n a (min ρ₁ ρ₂) := (hset z).2 ⟨hz₁, hz₂⟩
      have hp1 : z ∈ punct n a 1 := punct_mono hρ1 hp
      obtain ⟨v, w, hf, hv, hw, he⟩ := hz z hp1
      have hx : under (C.pt z ≫ k') = C.pt z ≫ C.k := by
        simp only [under, Category.assoc, hk]
      obtain ⟨⟨Γ, hΓ⟩, bΓ⟩ := b₁ z (punct_mono (min_le_left _ _) hp) _ (C.isVal_val z u₁)
      obtain ⟨⟨Δ, hΔ⟩, bΔ⟩ := b₂ z (punct_mono (min_le_right _ _) hp) _ (C.isVal_val z u₂)
      have gΓ := (C.hodgeGram_iff hp1 hx u₁ v hv _ (C.isVal_val z u₁) Γ).1 hΓ
      have gΔ := (C.hodgeGram_iff hp1 hx u₂ w hw _ (C.isVal_val z u₂) Δ).1 hΔ
      have hn := hU.norm _ v w Γ Δ hf gΓ gΔ
      have hne := hU.ne _ v w hf
      rw [← he] at hn hne
      have hL : (1 : ℝ) ≤ logSize a z := by
        have : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| :=
          Finset.sum_nonneg fun _ _ => abs_nonneg _
        simp only [logSize]
        linarith
      obtain ⟨g1, g2⟩ := bΓ Γ hΓ
      obtain ⟨d1, d2⟩ := bΔ Δ hΔ
      have := norm_bounds_of_gram (norm_pos_iff.2 hne) (norm_nonneg _) (norm_nonneg _) hL hn g1 g2 d1 d2
      refine ⟨hne, this.1, ?_⟩
      rw [norm_inv]
      exact this.2)
  refine ⟨min ρ₁ ρ₂, h, hρ0, hρ1, hh, hne, fun z hz' => ?_⟩
  obtain ⟨a1, a2⟩ := (hset z).1 hz'
  exact heq z a1 a2

end

end GlobalTheory.CompanionTheory.Ar.Flat
