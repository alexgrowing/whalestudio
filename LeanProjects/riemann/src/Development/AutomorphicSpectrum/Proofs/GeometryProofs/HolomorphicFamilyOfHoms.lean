import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AnChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.ChartRing

open MvPolynomial

theorem anChart_span {k A : Type} [Field k] [CommRing A] [Algebra k A] (D : ℕ) [h : Algebra.IsStandardSmoothOfRelativeDimension D k A]
    (σ : k →+* ℂ) (ψ₀ : A →+* ℂ) (h₀ : ψ₀.comp (algebraMap k A) = σ) :
    ∃ (N : ℕ) (g : Fin N → A) (f : Fin D → A) (B : Set (Fin D → ℂ)) (ε : ℝ) (Ψ : (Fin D → ℂ) → (A →+* ℂ)),
      0 < ε ∧ IsOpen B ∧ (∀ b ∈ B, (Ψ b).comp (algebraMap k A) = σ ∧ ∀ i, Ψ b (f i) = b i) ∧
      (∀ a, DifferentiableOn ℂ (fun b => Ψ b a) B) ∧
      (∀ ψ : A →+* ℂ, ψ.comp (algebraMap k A) = σ → (∀ j, ‖ψ (g j) - ψ₀ (g j)‖ < ε) →
        (fun i => ψ (f i)) ∈ B ∧ Ψ (fun i => ψ (f i)) = ψ) ∧
      Submodule.span A (Set.range fun i => KaehlerDifferential.D k A (f i)) = ⊤ := by
  classical
  obtain ⟨I, J, _, _, P, hd⟩ := h.out
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  have e : Fin D ≃ {i : I // i ∉ Set.range P.map} := (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype_compl, ← hd, Algebra.Presentation.dimension, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Set.card_range_of_injective P.map_inj])).symm
  let ev := fun (x : I → ℂ) => eval₂Hom σ x
  have pt : ∀ ψ : A →+* ℂ, ψ.comp (algebraMap k A) = σ → ∀ p, ψ (algebraMap P.Ring A p) = ev (fun i => ψ (P.val i)) p := fun ψ hψ p => by
    rw [P.algebraMap_apply, aeval_def, ← coe_eval₂Hom, map_eval₂Hom, hψ]
  let q : I → MvPolynomial I k := fun i => if h : i ∈ Set.range P.map then P.relation h.choose else X i
  have q₁ : ∀ j, q (P.map j) = P.relation j := fun j => (dif_pos ⟨j, rfl⟩).trans
    (congrArg _ (P.map_inj (⟨j, rfl⟩ : P.map j ∈ Set.range P.map).choose_spec))
  have q₂ : ∀ i : {i : I // i ∉ Set.range P.map}, q i = X i.1 := fun i => dif_neg i.2
  let Φ : (I → ℂ) → I → ℂ := fun x i => eval x (map σ (q i))
  have Φe : ∀ x i, Φ x i = ev x (q i) := fun x i => MvPolynomial.eval_map _ _ _
  let x₀ : I → ℂ := fun i => ψ₀ (P.val i)
  let F : (I → ℂ) →L[ℂ] (I → ℂ) := ContinuousLinearMap.pi fun i =>
    ∑ i', eval x₀ (pderiv i' (map σ (q i))) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i'
  have hF : HasFDerivAt Φ F x₀ := hasFDerivAt_pi.2 fun i => hasFDerivAt_eval _ _
  have Fv : ∀ v i, F v i = ∑ i', ev x₀ (pderiv i' (q i)) * v i' := fun v i => by
    simp [F, ev, pderiv_map, MvPolynomial.eval_map]
  have inj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun v hv => by
    have z₁ : ∀ i, i ∉ Set.range P.map → v i = 0 := fun i hi => by
      have := congrFun hv i
      rw [Fv, q₂ ⟨i, hi⟩] at this
      simpa [pderiv_X, Pi.single_apply, apply_ite] using this
    have dt : ((ev x₀).mapMatrix P.jacobiMatrix).det ≠ 0 := by
      rw [← RingHom.map_det, ← pt ψ₀ h₀, ← P.jacobian_eq_jacobiMatrix_det]
      exact (P.jacobian_isUnit.map ψ₀).ne_zero
    have z₂ : (fun j => v (P.map j)) = 0 := Matrix.eq_zero_of_vecMul_eq_zero dt (funext fun j => by
      have := congrFun hv (P.map j)
      rw [Fv, q₁, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.image P.map)) (fun i _ hi => by
        rw [z₁ i (by simpa using hi), mul_zero]), Finset.sum_image fun a _ b _ h => P.map_inj h] at this
      simpa [Matrix.vecMul, dotProduct, P.jacobiMatrix_apply, mul_comm] using this)
    funext i
    by_cases hi : i ∈ Set.range P.map
    · obtain ⟨j, rfl⟩ := hi; exact congrFun z₂ j
    · exact z₁ i hi
  let F' : (I → ℂ) ≃L[ℂ] (I → ℂ) := (LinearEquiv.ofInjectiveEndo F.toLinearMap inj).toContinuousLinearEquiv
  have cd : ContDiffAt ℂ 1 Φ x₀ := contDiffAt_pi.2 fun i =>
    (AnalyticOnNhd.eval_mvPolynomial (map σ (q i)) x₀ trivial).contDiffAt
  let T := cd.toOpenPartialHomeomorph Φ (f' := F') hF one_ne_zero
  let O := T.target ∩ interior {w | ContDiffAt ℂ 1 T.symm w}
  have oO : IsOpen O := T.open_target.inter isOpen_interior
  have mO : Φ x₀ ∈ O := ⟨cd.image_mem_toOpenPartialHomeomorph_target (f' := F') hF one_ne_zero,
    mem_interior_iff_mem_nhds.2 ((cd.to_localInverse (f' := F') hF one_ne_zero).eventually (by simp))⟩
  let em : (Fin D → ℂ) →L[ℂ] (I → ℂ) := ContinuousLinearMap.pi fun i =>
    if h : i ∈ Set.range P.map then 0 else ContinuousLinearMap.proj (e.symm ⟨i, h⟩)
  have m₁ : ∀ b j, em b (P.map j) = 0 := fun b j => by simp [em]
  have m₂ : ∀ b i, em b (e i) = b i := fun b i => by simp only [em, ContinuousLinearMap.pi_apply, dif_neg (e i).2]; simp
  have lf : ∀ x : I → ℂ, (∀ j, ev x (P.relation j) = 0) → ∃ ψ : A →+* ℂ, ∀ p, ψ (algebraMap P.Ring A p) = ev x p := fun x hx =>
    ⟨(algebraMap P.Ring A).liftOfSurjective P.algebraMap_surjective ⟨ev x, by
      show P.ker ≤ _
      rw [← P.span_range_relation_eq_ker, Ideal.span_le]
      rintro _ ⟨j, rfl⟩; exact hx j⟩, fun p => RingHom.liftOfRightInverse_comp_apply _ _ _ _ p⟩
  choose Ψ hΨ using lf
  have rel : ∀ b, em b ∈ O → ∀ j, ev (T.symm (em b)) (P.relation j) = 0 := fun b hb j => by
    rw [← q₁, ← Φe, show Φ (T.symm (em b)) = em b from T.right_inv hb.1, m₁]
  obtain ⟨ε, ε0, hε⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (T.open_source.mem_nhds
    (cd.mem_toOpenPartialHomeomorph_source (f' := F') hF one_ne_zero)) (hF.continuousAt.preimage_mem_nhds (oO.mem_nhds mO)))
  let n := Fintype.equivFin I
  refine ⟨_, fun j => P.val (n.symm j), fun i => P.val (e i), em ⁻¹' O, ε, fun b => if h : em b ∈ O then Ψ _ (rel b h) else ψ₀, ε0,
    oO.preimage em.continuous, fun b hb => ?_, fun a => ?_, fun ψ hψ hg => ?_, ?_⟩
  · simp only [dif_pos (show em b ∈ O from hb)]
    refine ⟨RingHom.ext fun r => ?_, fun i => ?_⟩
    · rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k P.Ring A, hΨ]; exact eval₂Hom_C _ _ _
    · rw [show P.val (e i) = algebraMap P.Ring A (X (e i).1) by simp, hΨ, ← q₂, ← Φe,
        show Φ (T.symm (em b)) = em b from T.right_inv hb.1, m₂]
  · obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
    refine DifferentiableOn.congr (f := fun b => eval (T.symm (em b)) (map σ p)) (fun b hb => ?_) fun b hb => ?_
    · have c₁ : ContDiffAt ℂ 1 T.symm (em b) := interior_subset hb.2
      have c₂ : DifferentiableAt ℂ (fun x : I → ℂ => eval x (map σ p)) (T.symm (em b)) := (hasFDerivAt_eval _ _).differentiableAt
      exact (c₂.comp b ((c₁.differentiableAt one_ne_zero).comp b em.differentiableAt)).differentiableWithinAt
    · simp only [dif_pos (show em b ∈ O from hb)]; rw [hΨ, MvPolynomial.eval_map]; rfl
  · have hx := hε (show (fun i => ψ (P.val i)) ∈ Metric.ball x₀ ε from (dist_pi_lt_iff ε0).2 fun i => by
      simpa [dist_eq_norm] using hg (n i))
    have e₁ : em (fun i => ψ (P.val (e i))) = Φ fun i => ψ (P.val i) := funext fun i => by
      by_cases hi : i ∈ Set.range P.map
      · obtain ⟨j, rfl⟩ := hi
        rw [m₁, Φe, q₁, ← pt ψ hψ, P.algebraMap_apply, P.aeval_val_relation, map_zero]
      · obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
        obtain rfl : (e j).1 = i := congrArg Subtype.val hj
        rw [m₂, Φe, q₂]
        simp only [ev, eval₂Hom_X']
    have mB : em (fun i => ψ (P.val (e i))) ∈ O := by rw [e₁]; exact hx.2
    refine ⟨mB, (dif_pos mB).trans (RingHom.ext fun a => ?_)⟩
    obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
    rw [hΨ, pt ψ hψ, e₁, show T.symm (Φ fun i => ψ (P.val i)) = _ from T.left_inv hx.1]
  · rw [eq_top_iff, ← P.basisKaehler.span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := e.surjective ⟨i.1, i.2⟩
    exact ⟨j, by simp [hj, P.basisKaehler_apply]⟩

theorem exists_dvd_polynomial {k A : Type} [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    {D : ℕ} (f : Fin D → A) (hspan : Submodule.span A (Set.range fun i => KaehlerDifferential.D k A (f i)) = ⊤)
    (hinj : Function.Injective (aeval f : MvPolynomial (Fin D) k →ₐ[k] A)) {a : A} (ha : a ≠ 0) :
    ∃ c : MvPolynomial (Fin D) k, c ≠ 0 ∧ a ∣ aeval f c := by
  let S := MvPolynomial (Fin D) k
  letI : Algebra S A := (aeval f : S →ₐ[k] A).toRingHom.toAlgebra
  have hal : ∀ c : S, algebraMap S A c = aeval f c := fun _ => rfl
  haveI : IsScalarTower k S A := .of_algebraMap_eq fun r => by
    rw [hal, MvPolynomial.algebraMap_eq, aeval_C]
  haveI : Algebra.FiniteType S A := .of_restrictScalars_finiteType k S A
  haveI : FaithfulSMul S A := (faithfulSMul_iff_algebraMap_injective S A).2 hinj
  have hz : KaehlerDifferential.map k S A A = 0 := LinearMap.ext_on hspan (by
    rintro _ ⟨i, rfl⟩
    have : f i = algebraMap S A (X i) := by simp [hal]
    simp only [KaehlerDifferential.map_D, LinearMap.zero_apply]
    rw [this]
    simp)
  haveI : Subsingleton Ω[A⁄S] := ⟨fun x y => by
    obtain ⟨x, rfl⟩ := KaehlerDifferential.map_surjective k S A x
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective k S A y
    simp [hz]⟩
  haveI : Algebra.FormallyUnramified S A := ⟨inferInstance⟩
  let K := FractionRing S
  let L := FractionRing A
  letI : Algebra K L := FractionRing.liftAlgebra S L
  haveI : IsScalarTower S K L := FractionRing.isScalarTower_liftAlgebra S L
  haveI : Algebra.FormallyEtale A L := .of_isLocalization (nonZeroDivisors _)
  haveI : Algebra.FormallyUnramified S L := Algebra.FormallyUnramified.comp S A L
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_restrictScalars S K L
  haveI : Algebra.EssFiniteType A L := .of_isLocalization L (nonZeroDivisors _)
  haveI : Algebra.EssFiniteType S L := Algebra.EssFiniteType.comp S A L
  haveI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp S K L
  haveI : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L
  haveI : Algebra.IsAlgebraic K L := inferInstance
  haveI : Algebra.IsAlgebraic S L := (IsFractionRing.comap_isAlgebraic_iff (A := S) (K := K)).2 inferInstance
  haveI : Algebra.IsAlgebraic S A := Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom S A L)
    (IsFractionRing.injective A L)
  exact (Algebra.IsAlgebraic.isAlgebraic a).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ha)

theorem eq_zero_of_eval_polydisc {D : ℕ} (Q : MvPolynomial (Fin D) ℂ) (b₀ : Fin D → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) 1, eval (b₀ + (ρ : ℂ) • z) Q = 0) : Q = 0 := by
  have hs : ∀ i, (Metric.ball (b₀ i) ρ).Infinite := fun i =>
    infinite_of_mem_nhds (b₀ i) (Metric.ball_mem_nhds _ hρ)
  refine MvPolynomial.funext_set (s := fun i => Metric.ball (b₀ i) ρ) hs fun x hx => ?_
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hx' : x = b₀ + (ρ : ℂ) • ((ρ : ℂ)⁻¹ • (x - b₀)) := by
    rw [smul_smul, mul_inv_cancel₀ hρ', one_smul]; abel
  rw [map_zero, hx']
  refine h _ ?_
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro i
  have := hx i (Set.mem_univ i)
  rw [Metric.mem_ball, dist_eq_norm] at this
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
  rw [inv_mul_lt_iff₀ hρ]
  simpa using this

theorem apply_aeval {k A : Type} [Field k] [CommRing A] [Algebra k A] {D : ℕ} (f : Fin D → A) (σ : k →+* ℂ)
    (φ : A →+* ℂ) (hφ : φ.comp (algebraMap k A) = σ) (c : MvPolynomial (Fin D) k) :
    φ (aeval f c) = eval (fun i => φ (f i)) (map σ c) := by
  rw [MvPolynomial.eval_map, aeval_def, ← coe_eval₂Hom, map_eval₂Hom, hφ]
  rfl

theorem exists_polydisc_chart : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (D : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension D k A] (σ : k →+* ℂ) (ψ₀ : A →+* ℂ), ψ₀.comp (algebraMap k A) = σ → ∃ Ψ : (Fin D → ℂ) → (A →+* ℂ), IsHolPts (ball 0 1) Ψ ∧ Ψ 0 = ψ₀ ∧ (∀ z ∈ ball (0 : Fin D → ℂ) 1, (Ψ z).comp (algebraMap k A) = σ) ∧ ∀ a : A, (∀ z ∈ ball (0 : Fin D → ℂ) 1, Ψ z a = 0) → a = 0 := by
  intro k A _ _ _ _ D hsm σ ψ₀ h₀
  haveI : Algebra.FiniteType k A := by
    obtain ⟨I, J, _, _, P, -⟩ := hsm.out
    exact P.finiteType
  obtain ⟨N, g, f, B, ε, Ψ₁, ε0, hB, hch, hhol, hlast, hspan⟩ := anChart_span D σ ψ₀ h₀
  obtain ⟨hb₀, hΨ₀⟩ := hlast ψ₀ h₀ fun j => by simpa using ε0
  obtain ⟨r, r0, hr⟩ := Metric.isOpen_iff.1 hB _ hb₀
  set b₀ : Fin D → ℂ := fun i => ψ₀ (f i) with hb₀def
  have hρ : 0 < r / 2 := by positivity
  set ρ : ℝ := r / 2 with hρdef
  let c : (Fin D → ℂ) → Fin D → ℂ := fun z => b₀ + (ρ : ℂ) • z
  have hc : ∀ z ∈ ball (0 : Fin D → ℂ) 1, c z ∈ B := fun z hz => hr (by
    rw [mem_ball_zero_iff] at hz
    rw [Metric.mem_ball, dist_eq_norm]
    have : c z - b₀ = (ρ : ℂ) • z := by simp [c]
    rw [this, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    nlinarith [norm_nonneg z])
  have hv : ∀ q : MvPolynomial (Fin D) k, (∀ z ∈ ball (0 : Fin D → ℂ) 1, Ψ₁ (c z) (aeval f q) = 0) → q = 0 := fun q hq => by
    have : map σ q = 0 := eq_zero_of_eval_polydisc _ b₀ hρ fun z hz => by
      have h₁ := apply_aeval f σ (Ψ₁ (c z)) (hch _ (hc z hz)).1 q
      have h₂ : (fun i => Ψ₁ (c z) (f i)) = c z := funext (hch _ (hc z hz)).2
      rw [hq z hz, h₂] at h₁
      exact h₁.symm
    exact map_injective σ σ.injective (by simpa using this)
  refine ⟨fun z => Ψ₁ (c z), ⟨Metric.isOpen_ball, fun a => ?_⟩, ?_, fun z hz => (hch _ (hc z hz)).1, fun a ha => ?_⟩
  · have hd : DifferentiableOn ℂ c (ball 0 1) := by
      simp only [c]; fun_prop
    exact (hhol a).comp hd hc
  · simp only [c, smul_zero, add_zero]; exact hΨ₀
  · by_contra ha0
    have hinj : Function.Injective (aeval f : MvPolynomial (Fin D) k →ₐ[k] A) :=
      (injective_iff_map_eq_zero _).2 fun q hq => hv q fun z _ => by simp [hq]
    obtain ⟨q, hq0, w, hw⟩ := exists_dvd_polynomial f hspan hinj ha0
    exact hq0 (hv q fun z hz => by rw [hw, map_mul, ha z hz, zero_mul])

end GlobalTheory.CompanionTheory.ChartRing
