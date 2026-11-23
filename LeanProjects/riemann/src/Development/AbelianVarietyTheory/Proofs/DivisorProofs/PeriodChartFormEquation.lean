import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpressionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCubicalStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsMapHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartDifferentiableExponentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartHolomorphicOnCoverStatement
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TotalPos
open GlobalTheory

variable {n m : ℕ}

theorem eval₂_I (α : CxForm.Alt n) (ξ : V n) :
    eval₂ α ξ (Complex.I • ξ) = 2 * HermFrame.form (hermMat α) ξ ξ := by
  simp only [eval₂, HermFrame.form, WithLp.ofLp_smul]
  simp only [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, Complex.star_def, Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]

theorem form_mul_mul_conjTranspose {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ) (K : Matrix (Fin b) (Fin b) ℂ)
    (w : Fin a → ℂ) : HermFrame.form (M * K * Mᴴ) w w = HermFrame.form K (w ᵥ* M) (w ᵥ* M) := by
  rw [HermFrame.form, HermFrame.form, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_vecMul]

theorem hermMat_add (α β : CxForm.Alt n) : hermMat (α + β) = hermMat α + hermMat β := by
  ext a b; simp [hermMat, mul_add]

open GlobalTheory.CxForm in
theorem pair_inj {a b a' b' : Fin n} (e : ({a.castAdd n, b.natAdd n} : Finset (Fin (n + n))) = {a'.castAdd n, b'.natAdd n}) :
    a = a' ∧ b = b' := by
  have h1 : a.castAdd n ∈ ({a'.castAdd n, b'.natAdd n} : Finset (Fin (n + n))) := e ▸ by simp
  have h2 : b.natAdd n ∈ ({a'.castAdd n, b'.natAdd n} : Finset (Fin (n + n))) := e ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at h1 h2
  constructor
  · rcases h1 with h1 | h1
    · exact Fin.ext h1
    · have := a.2; omega
  · rcases h2 with h2 | h2
    · have := a'.2; omega
    · exact Fin.ext (by omega)

open GlobalTheory.CxForm in
theorem eq_sum_of_isType {β : CxForm.Alt n} (h : IsType 1 1 β) :
    β = ∑ a, ∑ b, (bas n).repr β {a.castAdd n, b.natAdd n} • (CxForm.dz a * CxForm.dzb b) := by
  apply (bas n).repr.injective
  ext S
  simp only [← bas_pair, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, MulOneClass.mul_one, MulZeroClass.mul_zero]
  by_cases hS : (bas n).repr β S = 0
  · rw [hS]
    refine (Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_).symm
    split_ifs with e
    · rw [e, hS]
    · rfl
  · obtain ⟨h1, h2⟩ := h S hS
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h1
    obtain ⟨j, hj⟩ := Finset.card_eq_one.1 h2
    have hi' : i.val < n := by
      have : i ∈ S.filter (·.val < n) := hi ▸ Finset.mem_singleton_self i
      exact (Finset.mem_filter.1 this).2
    have hj' : n ≤ j.val := by
      have : j ∈ S.filter (n ≤ ·.val) := hj ▸ Finset.mem_singleton_self j
      exact (Finset.mem_filter.1 this).2
    have hSij : S = {(⟨i.val, hi'⟩ : Fin n).castAdd n, (⟨j.val - n, by omega⟩ : Fin n).natAdd n} := by
      ext t
      simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
      constructor
      · intro ht
        by_cases htn : t.val < n
        · left
          have : t ∈ S.filter (·.val < n) := Finset.mem_filter.2 ⟨ht, htn⟩
          rw [hi, Finset.mem_singleton] at this
          rw [this]
        · right
          have : t ∈ S.filter (n ≤ ·.val) := Finset.mem_filter.2 ⟨ht, by omega⟩
          rw [hj, Finset.mem_singleton] at this
          rw [this]; omega
      · rintro (ht | ht)
        · have : i ∈ S.filter (·.val < n) := hi ▸ Finset.mem_singleton_self i
          have e : t = i := Fin.ext ht
          exact e ▸ (Finset.mem_filter.1 this).1
        · have : j ∈ S.filter (n ≤ ·.val) := hj ▸ Finset.mem_singleton_self j
          have e : t = j := Fin.ext (by omega)
          exact e ▸ (Finset.mem_filter.1 this).1
    rw [Finset.sum_eq_single (⟨i.val, hi'⟩ : Fin n), Finset.sum_eq_single (⟨j.val - n, by omega⟩ : Fin n)]
    · rw [if_pos hSij.symm, ← hSij]
    · intro b _ hb
      rw [if_neg]
      intro e
      exact hb (pair_inj (e.trans hSij)).2
    · simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro e
      exact ha (pair_inj (e.trans hSij)).1
    · simp

open GlobalTheory.CxForm in
theorem repr_pair_sum (x : Fin n → Fin n → ℂ) (c0 d0 : Fin n) :
    (bas n).repr (∑ c, ∑ d, x c d • (CxForm.dz c * CxForm.dzb d)) {c0.castAdd n, d0.natAdd n} = x c0 d0 := by
  simp only [← bas_pair, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, MulOneClass.mul_one, MulZeroClass.mul_zero]
  rw [Finset.sum_eq_single c0, Finset.sum_eq_single d0]
  · simp
  · intro b _ hb; rw [if_neg]; intro e; exact hb (pair_inj e).2
  · simp
  · intro a _ ha; refine Finset.sum_eq_zero fun b _ => ?_; rw [if_neg]; intro e; exact ha (pair_inj e).1
  · simp

open GlobalTheory.CxForm in
theorem hermMat_isHermitian {α : CxForm.Alt n} (ht : IsType 1 1 α) (hr : IsReal α) : (hermMat α).IsHermitian := by
  set co := fun a b : Fin n => (bas n).repr α {a.castAdd n, b.natAdd n} with hco
  have hsw : swap α = ∑ c, ∑ d, (-co d c) • (CxForm.dz c * CxForm.dzb d) := by
    conv_lhs => rw [eq_sum_of_isType ht]
    simp only [map_sum, map_smul, map_mul, (swap_dz _).1, (swap_dz _).2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [CxForm.dz, CxForm.dzb, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _), neg_smul, smul_neg]
  have key : ∀ c d, -co d c = (starRingEnd ℂ) (co c d) := by
    intro c d
    have := hr {c.castAdd n, d.natAdd n}
    rw [hsw, repr_pair_sum] at this
    exact this
  ext c d
  simp only [conjTranspose_apply, hermMat, of_apply, star_mul', Complex.star_def, map_neg, Complex.conj_I]
  have e : (starRingEnd ℂ) ((bas n).repr α {d.castAdd n, c.natAdd n}) = -co c d := (key d c).symm
  rw [e]
  ring

open GlobalTheory.CxForm in
theorem pull_pair (L : V n →L[ℂ] V m) (a b : Fin m) :
    pull L (CxForm.dz a * CxForm.dzb b) = ∑ c, ∑ d, (L (GoodMetric.coordVec c) a *
      (starRingEnd ℂ) (L (GoodMetric.coordVec d) b)) • (CxForm.dz c * CxForm.dzb d) := by
  rw [map_mul, (pull_dz L a).1, (pull_dz L b).2, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [smul_mul_smul_comm]

open GlobalTheory.CxForm in
theorem hermMat_pull (L : V n →L[ℂ] V m) {β : CxForm.Alt m} (h : IsType 1 1 β) :
    hermMat (pull L β) = (Matrix.of fun c a => L (GoodMetric.coordVec c) a) * hermMat β *
      (Matrix.of fun c a => L (GoodMetric.coordVec c) a)ᴴ := by
  ext c d
  have hr : (bas n).repr (pull L β) {c.castAdd n, d.natAdd n} = ∑ a, ∑ b, (bas m).repr β {a.castAdd m, b.natAdd m} *
      (L (GoodMetric.coordVec c) a * (starRingEnd ℂ) (L (GoodMetric.coordVec d) b)) := by
    conv_lhs => rw [eq_sum_of_isType h]
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [pull_pair, repr_pair_sum]
  rw [hermMat, of_apply, hr]
  simp only [mul_apply, of_apply, conjTranspose_apply, hermMat, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem om0_nonneg {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} (FP : IndefiniteRowSideFullHecke.SiegelReframe.FlatFormProps B τ) {P : Pt E g} (hP : P ∈ cov B g)
    (u : Pt E g) :
    0 ≤ om0 τ P ![u, Complex.I • u] ∧ (u.1 = 0 → u.2 ≠ 0 → 0 < om0 τ P ![u, Complex.I • u]) := by
  obtain ⟨-, -, -, -, -, -, -, -, hpos, -, -, -, -, -, -, hker⟩ := FP
  have hom : ∀ a b : Pt E g, om0 τ P ![a, b] =
      IndefiniteRowSideFullHecke.SiegelReframe.riem (IndefiniteRowSideFullHecke.SiegelReframe.dflat τ P a) (IndefiniteRowSideFullHecke.SiegelReframe.dflat τ P b) := fun a b => rfl
  obtain ⟨w0, hw0, huniq⟩ := (hker P hP).2 u.1
  set hor : Pt E g := (u.1, w0) with hhor
  set vert : Pt E g := (0, u.2 - w0) with hvert
  have hu : u = hor + vert := Prod.ext (by simp [hhor, hvert]) (by simp [hhor, hvert])
  have hd : IndefiniteRowSideFullHecke.SiegelReframe.dflat τ P hor = 0 := hw0
  have hdI : IndefiniteRowSideFullHecke.SiegelReframe.dflat τ P (Complex.I • hor) = 0 := (hker P hP).1 hor hd
  have key : om0 τ P ![u, Complex.I • u] = om0 τ P ![vert, Complex.I • vert] := by
    rw [hom, hom, hu, smul_add, map_add, map_add, hd, hdI, zero_add, zero_add]
  have hIv : Complex.I • vert = (0, Complex.I • (u.2 - w0)) := by simp [hvert]
  have hv0 : ∀ t : Fin g → ℂ, t ≠ 0 → 0 < om0 τ P ![((0 : E), t), (0, Complex.I • t)] := fun t ht => hpos P hP t ht
  refine ⟨?_, fun h1 h2 => ?_⟩
  · rw [key, hIv]
    by_cases ht : u.2 - w0 = 0
    · have hv : vert = 0 := by rw [hvert, ht]; rfl
      rw [ht, hv, hom]; simp [IndefiniteRowSideFullHecke.SiegelReframe.riem]
    · exact (hv0 _ ht).le
  · have hw : w0 = 0 := by
      have := huniq 0 (by rw [h1]; exact map_zero _)
      exact huniq w0 hw0 |>.trans this.symm
    rw [key, hIv, hvert, hw, sub_zero]
    exact hv0 _ h2

theorem fibForm_posDef : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (A : Over S) [GrpObj A] (D' : ℕ) (h' : IsRegVar (A.hom ≫ p) D') (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ w : VMetric p (omega A) g, (∀ σ (y : CxPts p σ), ∃ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), y ∈ c.e.source ∧ IsPeriodChart w c τ ex) → ∀ (σ : k →+* ℂ) (Ω₀ : (h'.atlas σ).Fld) (κ : (h.atlas σ).Fld), (h'.atlas σ).IsRealForm 1 Ω₀ → (h.atlas σ).IsRealForm 1 κ → (∀ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex → IsFlatOn h' Ω₀ c.e.target τ ex) → (∀ x, (hermMat (κ x)).PosDef) → ∀ x, (hermMat (fibForm h h' Ω₀ κ x)).PosDef := by
  intro k _ S p D h A _ D' h' g hab hsm w hch σ Ω₀ κ hΩ hκ hflat hpos x
  set f := GlobalTheory.Points.PtsOver.map A.hom (rfl : A.hom ≫ p = A.hom ≫ p) (spMap σ) with hf
  obtain ⟨c, τ, ex, hy, hP⟩ := hch σ (f x.pt)
  set v := c.e (f x.pt) with hvdef
  have hv : v ∈ c.e.target := c.e.map_source hy
  have hsv : c.e.symm v = f x.pt := c.e.left_inv hy
  obtain ⟨z, hz⟩ := ((hP.isUnifChart).2.2 v hv).2.1 x.pt (by rw [hsv]; rfl)
  set P : Pt (V D) g := (v, z) with hPdef
  have hPc : P ∈ cov c.e.target g := ⟨hv, trivial⟩
  have hF := hflat c τ ex hP P hPc x hz.symm
  have FP := ((GlobalTheory.T.flat_cubical_statement g).1 (V D) c.e.target τ hP.1).1
  obtain ⟨hcont, hdiff⟩ := GlobalTheory.T.period_chart_differentiable_exponential k S p A D' h' D g w σ c τ ex hP P hPc x hz.symm
  have honto := GlobalTheory.T.periodChart_fderiv_surjective_on_cover k S p D h A D' h' g hab hsm w σ c τ ex hP P hPc x hz.symm
  have : IsIntegral S := h.isIntegral
  have hholo : (h.atlas σ).IsHolo (h'.atlas σ) f :=
    GlobalTheory.LineForm.isHolo_ptsOver_map k S p D h σ A.left (A.hom ≫ p) D' h' A.hom rfl
  have hpb := GlobalTheory.T.holAtlas_pullback_eq_chart_expression _ _ _ _ (h.atlas σ) (h'.atlas σ) f κ hholo hκ.1 x c hy
  set L := fderiv ℂ ((c.e : CxPts p σ → V D) ∘ f ∘ x.ch.symm) x.crd with hL
  set dφ := fderiv ℂ (x.ch ∘ ex) P with hdφ
  have hxs : ex P ∈ x.ch.source := by rw [hz]; exact x.2
  have hbase : ∀ u, L (dφ u) = u.1 := by
    have hG : DifferentiableAt ℂ ((c.e : CxPts p σ → V D) ∘ f ∘ x.ch.symm) x.crd := by
      have hopen : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' (f ⁻¹' c.e.source)) :=
        x.ch.isOpen_inter_preimage_symm (c.e.open_source.preimage hholo.1)
      have hmem : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' (f ⁻¹' c.e.source) :=
        ⟨x.ch.map_source x.2, by simp only [mem_preimage, x.ch.left_inv x.2]; exact hy⟩
      exact (hholo.2 x.1.1 c).differentiableAt (hopen.mem_nhds hmem)
    have heq : (((c.e : CxPts p σ → V D) ∘ f ∘ x.ch.symm) ∘ (x.ch ∘ ex)) =ᶠ[nhds P] fun Q => Q.1 := by
      have h1 : ∀ᶠ Q in nhds P, ex Q ∈ x.ch.source := hcont.preimage_mem_nhds (x.ch.open_source.mem_nhds hxs)
      have h2 : ∀ᶠ Q in nhds P, Q ∈ cov c.e.target g :=
        (c.e.open_target.prod isOpen_univ).mem_nhds hPc
      filter_upwards [h1, h2] with Q hQ1 hQ2
      have e1 : f (ex Q) = c.e.symm Q.1 := Subtype.ext ((hP.2.2 Q.1 hQ2.1).1 Q.2)
      simp only [Function.comp_apply, x.ch.left_inv hQ1]
      rw [e1, c.e.right_inv hQ2.1]
    have hφP : x.crd = (x.ch ∘ ex) P := by show x.ch x.pt = x.ch (ex P); rw [hz]
    have hG' : HasFDerivAt ((c.e : CxPts p σ → V D) ∘ f ∘ x.ch.symm) L ((x.ch ∘ ex) P) := hφP ▸ hG.hasFDerivAt
    have d1 := hG'.comp P hdiff.hasFDerivAt
    have d2 := (d1.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_fst)
    intro u
    exact congrArg (fun T => T u) d2

  have hfib : fibForm h h' Ω₀ κ x = Ω₀ x + (h.atlas σ).pullback (h'.atlas σ) f κ x := rfl
  set y : (h.atlas σ).Pt := ⟨(c, f x.pt), hy⟩ with hydef
  set M : Matrix (Fin D') (Fin D) ℂ := Matrix.of fun c a => L (GoodMetric.coordVec c) a with hM
  have hmat : hermMat (fibForm h h' Ω₀ κ x) = hermMat (Ω₀ x) + M * hermMat (κ y) * Mᴴ := by
    rw [hfib, hpb, hermMat_add, hermMat_pull _ (hκ.2 y).1]
    rfl
  have herm : (hermMat (Ω₀ x) + M * hermMat (κ y) * Mᴴ).IsHermitian :=
    (hermMat_isHermitian (hΩ.2 x).1 (hΩ.2 x).2).add (Matrix.isHermitian_mul_mul_conjTranspose _ (hpos y).1)
  have hK : ∀ t : Fin D → ℂ, t ≠ 0 → 0 < HermFrame.form (hermMat (κ y)) t t := by
    intro t ht
    have := ((Matrix.posDef_iff_dotProduct_mulVec.1 (hpos y)).2 (x := star t) (by simpa using ht))
    simpa [HermFrame.form, star_star] using this
  rw [hmat, Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨herm, fun ξ hξ => ?_⟩
  set wv : V D' := WithLp.toLp 2 (star ξ) with hwvdef
  have hform : star ξ ⬝ᵥ (hermMat (Ω₀ x) + M * hermMat (κ y) * Mᴴ) *ᵥ ξ =
      HermFrame.form (hermMat (Ω₀ x)) (star ξ) (star ξ) + HermFrame.form (M * hermMat (κ y) * Mᴴ) (star ξ) (star ξ) := by
    simp [HermFrame.form, add_mulVec, dotProduct_add, star_star]
  obtain ⟨u, hu⟩ := honto wv
  have hΩpart : HermFrame.form (hermMat (Ω₀ x)) (star ξ) (star ξ) = (om0 τ P ![u, Complex.I • u] : ℂ) / 2 := by
    have e1 := eval₂_I (Ω₀ x) wv
    have e2 := hF u (Complex.I • u)
    rw [ContinuousLinearMap.map_smul, hu] at e2
    have e3 : HermFrame.form (hermMat (Ω₀ x)) (star ξ) (star ξ) = HermFrame.form (hermMat (Ω₀ x)) wv wv := rfl
    rw [e3]
    linear_combination (1/2 : ℂ) * e2 - (1/2 : ℂ) * e1
  have hwsum : wv = ∑ c, (star ξ) c • GoodMetric.coordVec c := by
    ext i; simp [GoodMetric.coordVec, EuclideanSpace.single_apply, hwvdef, Pi.single_apply]
  have hvm : star ξ ᵥ* M = (u.1 : Fin D → ℂ) := by
    rw [← hbase u, hu, hwsum]
    ext a
    simp [vecMul, dotProduct, hM, map_sum, map_smul]
  have hκpart : HermFrame.form (M * hermMat (κ y) * Mᴴ) (star ξ) (star ξ) =
      HermFrame.form (hermMat (κ y)) (u.1 : Fin D → ℂ) (u.1 : Fin D → ℂ) := by
    rw [form_mul_mul_conjTranspose, hvm]
  rw [hform, hΩpart, hκpart]
  have hon := om0_nonneg FP hPc u
  by_cases hu1 : u.1 = 0
  · have hu2 : u.2 ≠ 0 := by
      intro hu2
      have h0 : u = 0 := Prod.ext hu1 hu2
      apply hξ
      have : wv = 0 := by rw [← hu, h0, map_zero]
      have : star ξ = 0 := congrArg (fun t : V D' => (t : Fin D' → ℂ)) this
      simpa using this
    have hp := hon.2 hu1 hu2
    rw [hu1]
    simp only [WithLp.ofLp_zero, HermFrame.form, zero_dotProduct, add_zero]
    have : (0 : ℂ) < ((om0 τ P ![u, Complex.I • u] / 2 : ℝ) : ℂ) := Complex.zero_lt_real.2 (by linarith)
    simpa using this
  · have hne : (u.1 : Fin D → ℂ) ≠ 0 := fun e => hu1 (by simpa using congrArg (WithLp.toLp 2) e)
    refine add_pos_of_nonneg_of_pos ?_ (hK _ hne)
    have : (0 : ℂ) ≤ ((om0 τ P ![u, Complex.I • u] / 2 : ℝ) : ℂ) := Complex.zero_le_real.2 (by linarith [hon.1])
    simpa using this

end GlobalTheory.TotalPos
