import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormsCommensurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericProductInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealEmbeddingOrdering
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalAppellHumbertRealMultStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeTraceImaginaryPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionalTraceRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHermitianTraceFormIntegralStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.PolScale

open GlobalTheory.AbDual

theorem nat_mul_polForm_eq_of_smul_eq (H : GlobalTheory.Published.AbelianDeRham) {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (c c₀ : 𝔠.elt) (n : ℕ) (t : 𝓞 F) (e : (n : 𝓞 F) • c = t • c₀)
    (ψ ψ₀ : LinearMap.BilinForm R (HdR X.A)) (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ)
    (hψ₀ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c₀) ψ₀) :
    ∀ x y, (n : R) * ψ x y = ψ₀ x (act (dp0 R) (𝟙 _) X.rm t y) := by
  have C := cupSquare_of_free H.1 X.ab X.dim
  have hD : ∀ d : 𝔠.elt, (X.diag d).IsLB := fun d ↦ pull_isLB (X.isLB d) _
  obtain ⟨φ, hφ⟩ := exists_corrForm H.1 X c
  obtain ⟨φ₀, hφ₀⟩ := exists_corrForm H.1 X c₀
  obtain ⟨φn, hφn, kn⟩ := exists_corrForm_smul X (n : 𝓞 F) c hφ
  obtain ⟨φt, hφt, kt⟩ := exists_corrForm_smul X t c₀ hφ₀
  rw [e] at hφn
  have u := Published.AbelianDualCrystal.polForm_unique C (hD _) (isPolForm_diag X _ hφn) (isPolForm_diag X _ hφt)
  have u₁ := Published.AbelianDualCrystal.polForm_unique C (hD c) hψ (isPolForm_diag X c hφ)
  have u₂ := Published.AbelianDualCrystal.polForm_unique C (hD c₀) hψ₀ (isPolForm_diag X c₀ hφ₀)
  intro x y
  have v := LinearMap.congr_fun (LinearMap.congr_fun u x) y
  rw [u₁, u₂]
  simp only [LinearMap.sub_apply, LinearMap.flip_apply, kn, kt, act_natCast, map_smul, LinearMap.smul_apply,
    smul_eq_mul] at v ⊢
  have a₁ := corrForm_antisymm H.1 X _ hφt y x
  have a₂ := corrForm_antisymm H.1 X c₀ hφ₀ (act (dp0 R) (𝟙 _) X.rm t y) x
  rw [kt, kt] at a₁
  linear_combination v + a₂ - a₁

end GlobalTheory.RealMult.PolScale

namespace GlobalTheory.RatioForm

set_option maxHeartbeats 1000000 in

theorem form_ratio : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (c₀ : 𝔠.elt)
      (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (FR E)), n.Coprime l ∧ n • c = t • c₀) →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) (2 • ψ₀) →
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) →
      (∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x)) →
    ∀ (D : R) (cv : ℚ), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D)) = (cv : WithTop ℚ) → (cv : ℝ) = c_vp 𝔣 l →
    ∀ (e' f' : I → (Fin n → R)), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) e' f' →
      (∀ i, 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ∧ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (ψ₀ (eH.symm (e' i)) (eH.symm (f' i)))) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) (D))) →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap R ℂ) (spMap (algebraMap R ℂ)) p), m.IsBC → ∀ (ψ : LinearMap.BilinForm ℂ (HdR X.A)), IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ →
    ∀ (yv ev : I → HdR X.A) (w : I → ℂ), (∀ i, U.IsCMVec i (yv i) (w i)) →
      (∀ i, m.Corr (eH.symm (f' i)) (yv i)) → (∀ i, m.Corr (eH.symm (e' i)) (ev i)) →
      (∀ i, ((e i (hL.toLie X₀.rm (eH.symm (f' i))) : R) : ℂ) = a i * w i) →
    ∃ ξ : E, GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.GenAt l (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y)) ξ ∧
      ∀ i, U.h i ≠ 0 ∧ ψ (ev i) (yv i) * (2 * Complex.I * φ i ξ) = (U.h i : ℂ) * ((ψ₀ (eH.symm (e' i)) (eH.symm (f' i)) : R) : ℂ) := by
  intro hPer hAdR hAdC hPM E _ _ _ _ I _ d φ hFD 𝔣 hB l _ Q hQ hQl y hy lam 𝔠 R _ hPR X₀ X U p cm hPB hcm hα j hj φK hφK e a hea hL n eH c₀ ψ₀ hc₀ hgen hpol hCM hdual D cv hD hcv e' f' hGens hval m hBC ψ hψ yv ev w hCMv hf he hw
  classical
  have hφ : IsCMType φ := hFD.2.2.2.2.2.2.1
  have hcQ : condQ 𝔣 Q ≠ ⊥ := by
    unfold condQ
    refine mul_ne_zero hB.1 ?_
    rw [Finset.prod_ne_zero_iff]
    intro q _
    exact q.ne_bot
  have hUc : ((U.c : FR E)) ≠ 0 := by
    intro h0
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace (FR E)))
    have hw : w.IsReal := NumberField.IsTotallyReal.isReal w
    have := U.pos (NumberField.InfinitePlace.embedding_of_isReal hw)
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨eR, heR⟩ := GlobalTheory.CMTypeRestrict.exists_equiv_realEmbeddings E I φ hφ U.e
  have hact : ∀ (a : 𝓞 (FR E)) w, U.u.ex (fun j ↦ (eR j (a : FR E) : ℂ) * w j) = U.u.ex w ≫ X.rm.act a := by
    intro a w
    have := U.act a w
    simpa [heR] using this
  obtain ⟨χ, hχ⟩ := U.ah
  obtain ⟨P, hPanti, hPadd, hPsmul, hPim, hPdual, hPspan⟩ :=
    GlobalTheory.T.diagonal_appell_humbert_real_mult (FR E) 𝔠 X U.c U.pos U.u eR hact (fun j ↦ U.h (U.e j)) χ hχ

  let co : E → (Fin (Module.finrank ℚ (FR E)) → ℂ) := fun x j ↦ φ (U.e j) x
  have hcoΛ : ∀ x ∈ lattice (condQ 𝔣 Q) y, co x ∈ U.u.Λ := fun x hx ↦
    (U.lat _).2 ⟨x, hx, by funext j; simp [co, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  have hΛco : ∀ w ∈ U.u.Λ, ∃ x ∈ lattice (condQ 𝔣 Q) y, w = co x := fun w hw ↦ by
    obtain ⟨x, hx, rfl⟩ := (U.lat w).1 hw
    exact ⟨x, hx, by funext j; simp [co, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  let toΛ : E → U.u.Λ := fun x ↦ if hx : co x ∈ U.u.Λ then ⟨co x, hx⟩ else 0
  have htoΛ : ∀ x ∈ lattice (condQ 𝔣 Q) y, (toΛ x : Fin (Module.finrank ℚ (FR E)) → ℂ) = co x := fun x hx ↦ by
    simp [toΛ, hcoΛ x hx]
  let Qf : E → E → FR E := fun x x' ↦ P (toΛ x) (toΛ x')

  let fR : E → ℝ := fun z ↦ ∑ i, U.h i * (φ i z).im
  have hsum : ∀ x x' : E, (∑ j, ((U.h (U.e j) : ℝ) : ℂ) * (co x j * starRingEnd ℂ (co x' j))).im =
      fR (x * IsCMField.complexConj E x') := by
    intro x x'
    simp only [fR, co, Complex.im_sum, map_mul, IsCMField.complexEmbedding_complexConj, Complex.im_ofReal_mul]
    exact Equiv.sum_comp U.e (fun i ↦ U.h i * (φ i x * starRingEnd ℂ (φ i x')).im)
  have hfrel : ∀ x ∈ lattice (condQ 𝔣 Q) y, ∀ x' ∈ lattice (condQ 𝔣 Q) y, fR (x * IsCMField.complexConj E x') =
      2 * ((Algebra.trace ℚ (FR E) ((U.c : FR E) * Qf x x') : ℚ) : ℝ) := by
    intro x hx x' hx'
    rw [← hsum, ← hPim (toΛ x) (toΛ x'), htoΛ x hx, htoΛ x' hx']

  let gR : E →ₗ[ℚ] ℝ :=
    { toFun := fR
      map_add' := fun z z' ↦ by
        simp only [fR, map_add, Complex.add_im, mul_add, Finset.sum_add_distrib]
      map_smul' := fun q z ↦ by
        simp only [fR, RingHom.id_apply]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Rat.smul_def, map_mul, map_ratCast, ← Complex.ofReal_ratCast, Complex.im_ofReal_mul, Rat.smul_def]
        ring }
  have hgR : ∀ z, gR z = fR z := fun z ↦ rfl
  obtain ⟨N, hN0, hNL, -⟩ := GlobalTheory.CMVal.LatBound.lattice_between E (condQ 𝔣 Q) hcQ y
  have hrat : ∀ z, ∃ q : ℚ, gR z = q := by
    intro z
    obtain ⟨b, k, hk, hb⟩ : ∃ (b : 𝓞 E) (k : ℤ), k ≠ 0 ∧ (k : E) * z = algebraMap (𝓞 E) E b := by
      obtain ⟨k, hk, hi⟩ := IsAlgebraic.exists_integral_multiple
        ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z))
      exact ⟨⟨k • z, hi⟩, k, hk, by simp [zsmul_eq_mul]⟩
    have hx : (N : E) * algebraMap (𝓞 E) E b ∈ lattice (condQ 𝔣 Q) y := hNL b
    have hx' : (N : E) * algebraMap (𝓞 E) E 1 ∈ lattice (condQ 𝔣 Q) y := hNL 1
    have e1 := hfrel _ hx _ hx'
    have e2 : (N : E) * algebraMap (𝓞 E) E b * IsCMField.complexConj E ((N : E) * algebraMap (𝓞 E) E 1) =
        (((N : ℚ) * N * k : ℚ) : E) * z := by
      rw [map_one, _root_.mul_one, map_natCast]; push_cast; rw [← hb]; ring
    rw [e2] at e1
    have e3 : gR ((((N : ℚ) * N * k : ℚ) : E) * z) = (((N : ℚ) * N * k : ℚ) : ℝ) * gR z := by
      rw [← Rat.smul_def, map_smul, Rat.smul_def]
    refine ⟨2 * Algebra.trace ℚ (FR E) ((U.c : FR E) * Qf ((N : E) * algebraMap (𝓞 E) E b) ((N : E) * algebraMap (𝓞 E) E 1)) /
      ((N : ℚ) * N * k), ?_⟩
    have hne : (((N : ℚ) * N * k : ℚ) : ℝ) ≠ 0 := by
      have : ((N : ℚ) * N * k : ℚ) ≠ 0 := by
        have : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
        have : (k : ℚ) ≠ 0 := by exact_mod_cast hk
        positivity
      exact_mod_cast this
    rw [← hgR, e3] at e1
    rw [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
    exact eq_div_of_mul_eq hne (by rw [mul_comm]; exact e1)
  obtain ⟨mu, hmu⟩ := GlobalTheory.T.rational_functional_trace_representation E gR hrat
  have hmu' : ∀ z : E, ((Algebra.trace ℚ E (mu * z) : ℚ) : ℝ) = ∑ i, U.h i * (φ i z).im := fun z ↦ (hmu z).symm
  have hmuh := GlobalTheory.T.cm_type_trace_imaginary_part E I φ hφ U.h mu hmu'

  have hIne : Nonempty I := by
    have : 2 ≤ Fintype.card I := hFD.2.2.2.2.2.1
    exact Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀⟩ := hIne
  have hbar : IsCMField.complexConj E mu = -mu := by
    apply (φ i₀).injective
    have h1 := hmuh i₀
    rw [IsCMField.complexEmbedding_complexConj, map_neg]
    have h2 : starRingEnd ℂ (2 * Complex.I * φ i₀ mu) = starRingEnd ℂ (U.h i₀ : ℂ) := by rw [h1]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat] at h2
    have h3 : (2 : ℂ) * Complex.I ≠ 0 := by simp
    apply mul_left_cancel₀ h3
    linear_combination -h2 + h1
  have hQa : ∀ (a : OF E), ∀ x ∈ lattice (condQ 𝔣 Q) y, ∀ x' ∈ lattice (condQ 𝔣 Q) y,
      Qf (algebraMap (OF E) E a * x) x' = (a : FR E) * Qf x x' := by
    intro a x hx x' hx'
    have hax : algebraMap (OF E) E a * x ∈ lattice (condQ 𝔣 Q) y := by
      have : algebraMap (OF E) E a ∈ orderC (condQ 𝔣 Q) := GlobalTheory.CMVal.algebraMap_mem_orderC _ a
      exact GlobalTheory.CMVal.mul_mem_lattice this hx
    refine hPsmul a (toΛ x) (toΛ x') (toΛ (algebraMap (OF E) E a * x)) ?_
    rw [htoΛ _ hax, htoΛ _ hx]
    funext k
    simp only [co, map_mul, heR]
    rfl
  have htr : ∀ x ∈ lattice (condQ 𝔣 Q) y, ∀ x' ∈ lattice (condQ 𝔣 Q) y, Algebra.trace ℚ E (mu * x * IsCMField.complexConj E x') =
      2 * Algebra.trace ℚ (FR E) ((U.c : FR E) * Qf x x') := by
    intro x hx x' hx'
    have h1 := hmu (x * IsCMField.complexConj E x')
    rw [hgR, hfrel x hx x' hx', ← _root_.mul_assoc] at h1
    exact_mod_cast h1.symm
  have hdl : ∀ x ∈ lattice (condQ 𝔣 Q) y, ∀ x' ∈ lattice (condQ 𝔣 Q) y, Qf x x' ∈ dualLat 𝔠 := fun x _ x' _ ↦ hPdual _ _
  have hsp : ∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 (FR E)) {t | ∃ x ∈ lattice (condQ 𝔣 Q) y, ∃ x' ∈ lattice (condQ 𝔣 Q) y, t = Qf x x'} := by
    intro t ht
    refine Submodule.span_mono ?_ (hPspan t ht)
    rintro s ⟨l₁, l₂, rfl⟩
    obtain ⟨x, hx, hx1⟩ := hΛco l₁ l₁.2
    obtain ⟨x', hx', hx2⟩ := hΛco l₂ l₂.2
    refine ⟨x, hx, x', hx', ?_⟩
    have e1 : toΛ x = l₁ := Subtype.ext (by rw [htoΛ x hx, ← hx1])
    have e2 : toΛ x' = l₂ := Subtype.ext (by rw [htoΛ x' hx', ← hx2])
    simp only [Qf, e1, e2]
  obtain ⟨hmu0, hGen⟩ := GlobalTheory.T.cm_hermitian_trace_form_integral E (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.latMod (condQ 𝔣 Q) y) 𝔠 mu (U.c : FR E) Qf l c₀ hUc hbar
    hQa htr hdl hsp hgen

  obtain ⟨n₁, t, hn₁, het⟩ := GlobalTheory.RealMult.PolScale.exists_nat_smul_eq c₀ U.c hUc
  obtain ⟨ψc, hψc, hcorr⟩ := GlobalTheory.LowerCx.polForm_bc' (algebraMap R ℂ) hPB m c₀ hpol
  have hsc := GlobalTheory.RealMult.PolScale.nat_mul_polForm_eq_of_smul_eq hAdR X c₀ U.c n₁ t het ψc ψ hψc hψ
  have hty : ∀ i, act (dp0 ℂ) (𝟙 _) X.rm t (yv i) = φ i ((t : FR E) : E) • yv i := by
    intro i
    haveI := X.rm.hom t
    rw [act_apply]
    exact (hCMv i).1 ((t : FR E) : E) (X.rm.act t) (fun w' ↦ U.act t w')
  have hkey : ∀ i, φ i ((t : FR E) : E) * ψ (ev i) (yv i) =
      (n₁ : ℂ) * (2 * ((ψ₀ (eH.symm (e' i)) (eH.symm (f' i)) : R) : ℂ)) := by
    intro i
    have h1 := hsc (ev i) (yv i)
    rw [hty i, map_smul, smul_eq_mul, hcorr _ _ _ _ (he i) (hf i)] at h1
    rw [← h1, two_smul, LinearMap.add_apply, LinearMap.add_apply, map_add, two_mul]
    rfl
  have hcF : ((c₀ : FR E)) * (n₁ : FR E) = ((t : FR E)) * (U.c : FR E) := by
    have := congrArg (fun z : 𝔠.elt ↦ (z : FR E)) het
    simp only [Submodule.coe_smul, Algebra.smul_def, map_natCast] at this
    rw [mul_comm]; exact this
  refine ⟨(((c₀ : FR E) / (2 * (U.c : FR E)) : FR E) : E) * mu, hGen, fun i ↦ ⟨?_, ?_⟩⟩
  · intro h0
    have h1 := hmuh i
    rw [h0, Complex.ofReal_zero] at h1
    have h2 : φ i mu = 0 := by
      have h3 : (2 : ℂ) * Complex.I ≠ 0 := by simp
      exact (mul_eq_zero.1 h1).resolve_left h3
    exact hmu0 ((map_eq_zero (φ i)).1 h2)
  · have hc : φ i ((c₀ : FR E) : E) * n₁ = φ i ((t : FR E) : E) * φ i ((U.c : FR E) : E) := by
      have := congrArg (fun z : FR E ↦ φ i (z : E)) hcF
      simpa using this
    have hC1 : φ i ((U.c : FR E) : E) ≠ 0 := by
      intro h0
      exact hUc (by simpa using h0)
    have hn₁' : (n₁ : ℂ) ≠ 0 := by exact_mod_cast hn₁
    have hk := hkey i
    have hm := hmuh i
    have hdiv : φ i ((((c₀ : FR E) / (2 * (U.c : FR E)) : FR E) : E)) =
        φ i ((c₀ : FR E) : E) / (2 * φ i ((U.c : FR E) : E)) := by
      change (φ i).comp (algebraMap (FR E) E) (_ / (2 * _)) = (φ i).comp (algebraMap (FR E) E) _ / (2 * (φ i).comp (algebraMap (FR E) E) _)
      rw [map_div₀, map_mul, map_ofNat]
    rw [map_mul, hdiv]
    set A := ψ (ev i) (yv i)
    set B := ((ψ₀ (eH.symm (e' i)) (eH.symm (f' i)) : R) : ℂ)
    have e1 : A * (2 * Complex.I * (φ i ((c₀ : FR E) : E) / (2 * φ i ((U.c : FR E) : E)) * φ i mu)) =
        A * φ i ((c₀ : FR E) : E) * (2 * Complex.I * φ i mu) / (2 * φ i ((U.c : FR E) : E)) := by ring
    rw [e1, hm, div_eq_iff (mul_ne_zero two_ne_zero hC1)]
    apply mul_left_cancel₀ hn₁'
    linear_combination (A * (U.h i : ℂ)) * hc + (φ i ((U.c : FR E) : E) * (U.h i : ℂ)) * hk

end GlobalTheory.RatioForm
