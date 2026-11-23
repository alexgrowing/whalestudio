import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantCharactersSeparateStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFlipMatchSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterNontrivialAtFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrix
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)
namespace GlobalTheory.DisjOrth

theorem det_ne_zero_of_hasSig {n : ℕ} {N : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig N r s) : N.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin n ≃ Fin r ⊕ Fin s := (finCongr hrs.symm).trans finSumFinEquiv.symm
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    simp
  have h1 : ((Aᵀ * N * A.map star).submatrix e e).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self, hA]; exact hD
  have h2 : (Aᵀ * N * A.map star).submatrix e e =
      Aᵀ.submatrix e (Equiv.refl _) * N.submatrix (Equiv.refl _) (Equiv.refl _) * (A.map star).submatrix (Equiv.refl _) e := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rw [h2, Matrix.det_mul, Matrix.det_mul] at h1
  intro h0
  apply h1
  have : (N.submatrix (Equiv.refl (Fin n)) (Equiv.refl (Fin n))).det = 0 := by
    rw [Matrix.det_submatrix_equiv_self]; exact h0
  rw [this]; ring

theorem det_ne_zero_of_map {E : Type} [Field E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ)
    (h : (J.map f).det ≠ 0) : J.det ≠ 0 := by
  intro h0; apply h; have := RingHom.map_det f J; rw [RingHom.mapMatrix_apply] at this; rw [← this, h0, map_zero]

theorem pairM_single {k A C : Type} [CommRing k] [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]
    (X : Matrix A C k) (i : A) (j : C) (a : k) : GlobalTheory.FlipMatch.pairM X (Matrix.single i j a) = X i j * a := by
  unfold GlobalTheory.FlipMatch.pairM
  simp only [Matrix.single_apply, mul_ite, mul_zero, ite_and]
  simp

end GlobalTheory.DisjOrth

open GlobalTheory.DisjOrth in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.DisjOrth.disj_orth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r₁ s₁ : ℕ),
    IsPair B M χX χW om r s r₁ s₁ →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ (v : Pl F) (ρ : Fn F n d), (∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ) →
    ∀ (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) ι, M.IsLinW B.ψ t b c ι →
    ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v), (∀ Y, ι φ₁ Y * ι φ₂ Y = 0) →
      ∫ x, tens (evFin F v) φ₁ ρ x * starRingEnd ℂ (tens (evFin F v) φ₂ ρ x) ∂m = 0 := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r₁ s₁ hP mS bS m hm v ρ hR t b c ι hι φ₁ hφ₁ φ₂ hφ₂ hdis
  obtain ⟨rfl⟩ := bS
  have hstd := hP.base.std
  have hcm := hP.base.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have detX : X.J.det ≠ 0 := det_ne_zero_of_map X.J _ (det_ne_zero_of_hasSig (hP.herm.sig w))
  have detW : W.J.det ≠ 0 := by
    have h := det_ne_zero_of_hasSig (hP.skew.sig w)
    rw [Matrix.det_smul] at h
    exact det_ne_zero_of_map W.J _ (right_ne_zero_of_mul h)
  have hbij : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _) := by
    unfold Model.IsLinW at hι; exact hι.bij
  set j : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) → ((Fin n × Fin d → Fv F v) → ℂ) :=
    Function.invFunOn ι (SB (Fin n × Fin d → Fv F v) : Set _) with hjdef
  have hj : ∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), j f ∈ SB (Fin n × Fin d → Fv F v) ∧ ι (j f) = f := by
    intro f hf
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hf
    exact ⟨Function.invFunOn_mem ⟨φ, hφ, rfl⟩, Function.invFunOn_eq ⟨φ, hφ, rfl⟩⟩
  have hjι : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), j (ι φ) = φ := fun φ hφ =>
    hbij.injOn (hj _ (hbij.mapsTo hφ)).1 hφ (hj _ (hbij.mapsTo hφ)).2
  have hjadd : ∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), ∀ f' ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
      j (f + f') = j f + j f' := by
    intro f hf f' hf'
    have e : f + f' = ι (j f + j f') := by rw [map_add, (hj f hf).2, (hj f' hf').2]
    rw [e, hjι _ (add_mem (hj f hf).1 (hj f' hf').1)]
  have hjsmul : ∀ (a : ℂ), ∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), j (a • f) = a • j f := by
    intro a f hf
    have e : a • f = ι (a • j f) := by rw [map_smul, (hj f hf).2]
    rw [e, hjι _ (Submodule.smul_mem _ a (hj f hf).1)]
  have hL : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), MemLp (tens (evFin F v) φ ρ) 2 m := fun φ hφ =>
    GlobalTheory.WeilM.schA_memLp_two F _ m hm _ (hR φ hφ).2
  have hint : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ' ∈ SB (Fin n × Fin d → Fv F v),
      Integrable (fun x => tens (evFin F v) φ ρ x * starRingEnd ℂ (tens (evFin F v) φ' ρ x)) m := by
    intro φ hφ φ' hφ'
    haveI : ENNReal.HolderTriple 2 2 1 := ⟨by norm_num [ENNReal.inv_two_add_inv_two]⟩
    exact MemLp.integrable_mul (p := 2) (q := 2) (hL φ hφ) (hL φ' hφ').star
  have hTadd : ∀ φ φ' : (Fin n × Fin d → Fv F v) → ℂ,
      tens (evFin F v) (φ + φ') ρ = fun x => tens (evFin F v) φ ρ x + tens (evFin F v) φ' ρ x := by
    intro φ φ'
    have := tens_lin (evFin F v) 1 1 φ φ' ρ
    simp only [one_smul] at this
    rw [this]; rfl
  have hTsmul : ∀ (a : ℂ) (φ : (Fin n × Fin d → Fv F v) → ℂ),
      tens (evFin F v) (a • φ) ρ = fun x => a * tens (evFin F v) φ ρ x := by
    intro a φ
    have := tens_lin (evFin F v) a 0 φ 0 ρ
    simp only [zero_smul, add_zero] at this
    rw [this]; rfl
  let β : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) → (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) → ℂ := fun f g =>
    ∫ x, tens (evFin F v) (j f) ρ x * starRingEnd ℂ (tens (evFin F v) (j g) ρ x) ∂m
  have hadd1 : ∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), ∀ f' ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
      ∀ g ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), β (f + f') g = β f g + β f' g := by
    intro f hf f' hf' g hg
    simp only [β]
    rw [hjadd f hf f' hf', hTadd, ← integral_add (hint _ (hj f hf).1 _ (hj g hg).1) (hint _ (hj f' hf').1 _ (hj g hg).1)]
    congr 1; ext x; ring
  have hadd2 : ∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), ∀ g ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
      ∀ g' ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), β f (g + g') = β f g + β f g' := by
    intro f hf g hg g' hg'
    simp only [β]
    rw [hjadd g hg g' hg', hTadd, ← integral_add (hint _ (hj f hf).1 _ (hj g hg).1) (hint _ (hj f hf).1 _ (hj g' hg').1)]
    congr 1; ext x; simp only [map_add]; ring
  have hsm : ∀ (a : ℂ), ∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), ∀ g ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
      β (a • f) g = a * β f g ∧ β f (a • g) = starRingEnd ℂ a * β f g := by
    intro a f hf g hg
    simp only [β]
    rw [hjsmul a f hf, hjsmul a g hg, hTsmul, hTsmul, ← integral_const_mul, ← integral_const_mul]
    constructor
    · congr 1; ext x; ring
    · congr 1; ext x; simp only [map_mul]; ring

  have hpsi : ∀ x : Fv F v, psiLoc B.ψ v x = GlobalTheory.LatVac.psiAt B.ψ v x := fun x => rfl
  have hnorm : ∀ x : Fv F v, ‖GlobalTheory.LatVac.psiAt B.ψ v x‖ = 1 := fun x => GlobalTheory.StdCharFromIsStd.norm_psi hstd _
  have hsep : ∀ x y : Matrix (Fin n) (Fin d) (Fv F v), x ≠ y → ∃ χ : Matrix (Fin n) (Fin d) (Fv F v) → ℂ,
      IsLocallyConstant χ ∧ (∀ z, ‖χ z‖ = 1) ∧ χ x ≠ χ y ∧ ∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
        ∀ g ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), β (χ * f) (χ * g) = β f g := by
    intro x y hxy
    obtain ⟨i, k, hik⟩ : ∃ i k, x i k ≠ y i k := by
      by_contra h; simp only [not_exists, not_not] at h; exact hxy (Matrix.ext h)
    obtain ⟨t₀, ht₀⟩ := GlobalTheory.PsiLocNontriv.exists_psiLoc_ne_one F B.ψ hstd v
    set a : Fv F v := t₀ / (x i k - y i k) with ha
    set Q : Matrix (Fin n) (Fin d) (Fv F v) := Matrix.single i k a with hQ
    have hsub : x i k - y i k ≠ 0 := sub_ne_zero.mpr hik
    refine ⟨fun Z => psiLoc B.ψ v (GlobalTheory.FlipMatch.pairM Z Q), ?_, ?_, ?_, ?_⟩
    · have hc : Continuous (fun Z : Matrix (Fin n) (Fin d) (Fv F v) => GlobalTheory.FlipMatch.pairM Z Q) := by
        unfold GlobalTheory.FlipMatch.pairM
        exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
          (continuous_id.matrix_elem i j).mul continuous_const))
      exact (GlobalTheory.SympUnip.psiAt_isLocallyConstant B.ψ hstd.1 v).comp_continuous (f := fun Z : Matrix (Fin n) (Fin d) (Fv F v) => GlobalTheory.FlipMatch.pairM Z Q) hc
    · intro z; exact hnorm _
    · intro h
      simp only [hQ, pairM_single, hpsi] at h
      apply ht₀
      have e : t₀ = x i k * a - y i k * a := by rw [ha]; field_simp
      rw [hpsi, e, AddChar.map_sub_eq_div, h, div_self]
      intro h0
      have := hnorm (y i k * a)
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    · intro f hf g hg
      obtain ⟨u, hu, hux, huy⟩ := GlobalTheory.T.local_flip_match_surjective hcm X W detX detW t b c 0 Q
      have hpu : partFin v u = u := partFin_of_at hu
      have hpair : GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coX t b c u) (GlobalTheory.FlipMatch.coY σ X W t b c u) = 0 := by
        rw [hux]; unfold GlobalTheory.FlipMatch.pairM; simp
      have key : ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
          Acts (evFin F v) (M.co.rho B.ψ u) φ (locOp v (M.co.rho B.ψ u) φ) ∧
          ι (locOp v (M.co.rho B.ψ u) φ) = (fun Z => psiLoc B.ψ v (GlobalTheory.FlipMatch.pairM Z Q)) * ι φ := by
        intro φ hφ
        have h := (locOp_rho M.co hstd.1 v u hφ).1
        rw [hpu] at h
        refine ⟨h, ?_⟩
        funext Z
        have := (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hcm X W hP.herm.herm hP.skew.skew detX detW M B.ψ hstd t b c u hu hpair φ hφ _
          (locOp_mem v _ φ) h).1 ι hι Z
        rw [this, hux, huy, add_zero]; rfl
      have hjχ : ∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
          j ((fun Z => psiLoc B.ψ v (GlobalTheory.FlipMatch.pairM Z Q)) * f) = locOp v (M.co.rho B.ψ u) (j f) := by
        intro f hf
        have e : (fun Z => psiLoc B.ψ v (GlobalTheory.FlipMatch.pairM Z Q)) * f = ι (locOp v (M.co.rho B.ψ u) (j f)) := by
          rw [(key _ (hj f hf).1).2, (hj f hf).2]
        rw [e, hjι _ (locOp_mem _ _ _)]
      simp only [β]
      rw [hjχ f hf, hjχ g hg, ← (key _ (hj f hf).1).1 ρ (hR _ (hj f hf).1), ← (key _ (hj g hg).1).1 ρ (hR _ (hj g hg).1)]
      set Fφ := tens (evFin F v) (j f) ρ
      set Gφ := tens (evFin F v) (j g) ρ
      have hpt : ∀ x, M.co.rho B.ψ u Fφ x * starRingEnd ℂ (M.co.rho B.ψ u Gφ x) =
          Fφ (x + (M.co.e u).1) * starRingEnd ℂ (Gφ (x + (M.co.e u).1)) := by
        intro x
        simp only [Darboux.rho, schr, map_mul]
        have h1 := GlobalTheory.StdCharFromIsStd.norm_psi hstd (x ⬝ᵥ (M.co.e u).2 + ⅟2 * (M.co.e u).1 ⬝ᵥ (M.co.e u).2)
        have h2 : B.ψ (x ⬝ᵥ (M.co.e u).2 + ⅟2 * (M.co.e u).1 ⬝ᵥ (M.co.e u).2) *
            starRingEnd ℂ (B.ψ (x ⬝ᵥ (M.co.e u).2 + ⅟2 * (M.co.e u).1 ⬝ᵥ (M.co.e u).2)) = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
        linear_combination (Fφ (x + (M.co.e u).1) * starRingEnd ℂ (Gφ (x + (M.co.e u).1))) * h2
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
      haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
      haveI : MeasurableAdd (Fin n × Fin d → AF F) := inferInstance
      exact integral_add_right_eq_self (fun x => Fφ x * starRingEnd ℂ (Gφ x)) _
  have key := GlobalTheory.T.locally_constant_characters_separate (Matrix (Fin n) (Fin d) (Fv F v)) β hadd1 hadd2 hsm hsep (ι φ₁) (hbij.mapsTo hφ₁) (ι φ₂)
    (hbij.mapsTo hφ₂) hdis
  simp only [β, hjι _ hφ₁, hjι _ hφ₂] at key
  exact key
