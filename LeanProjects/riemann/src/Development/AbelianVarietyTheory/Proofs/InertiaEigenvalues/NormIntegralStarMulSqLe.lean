import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSumFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermitiStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormIntegralStarMulSqLeMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteLocalDoubleCosetRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalHeckeSumPreservesPrincipalLevelFormsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetHeckeSumPreservesPrincipalFormsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLiftTrans

theorem norm_integral_star_mul_sq_le {X : Type} [MeasurableSpace X] (μ : Measure X) (f h : X → ℂ)
    (hf : AEStronglyMeasurable f μ) (hh : AEStronglyMeasurable h μ)
    (hf2 : Integrable (fun x => star (f x) * f x) μ) (hh2 : Integrable (fun x => star (h x) * h x) μ) :
    ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ (∫ x, star (f x) * f x ∂μ).re * (∫ x, star (h x) * h x ∂μ).re :=
  GlobalTheory.T.norm_integral_star_mul_sq_le_mul μ f h hf hh hf2 hh2

theorem exists_cosetRep_levG {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D) (hf : IsFinIdem D v f) (α : GA D V) (hα : SuppF V f α) :
    ∃ C : Finset (GA D V), (∀ γ ∈ C, SuppF V f γ) ∧ IsCosetRep V {k | k ∈ levG V β L ∧ SuppF V f k} α C :=
  GlobalTheory.T.exists_finite_local_double_coset_representatives V β L v f hf α hα

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}

theorem heckeOn_mem_wall (hLP : LevProd R i) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D) (hf : IsFinIdem D v f)
    (α : GA D (Wc D i)) (hα : SuppF (Wc D i) f α) (C : Finset (GA D (Wc D i))) (hC : ∀ γ ∈ C, SuppF (Wc D i) f γ)
    (hR : IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) (T : MMap (R.MW i (sg0 D A)))
    (hT : T ∈ R.Wall i (sg0 D A)) : heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) :=
  GlobalTheory.T.local_hecke_sum_preserves_principal_level_forms hLP v f hf α hα C hC hR T hT

theorem exists_doubleCoset_sum (hLP : LevProd R i) (γ : GA D (Wc D i)) (hγ : γ ∈ GfC (Wc D i)) :
    ∃ C : Finset (GA D (Wc D i)), C.Nonempty ∧ (∀ δ ∈ C, ∃ k ∈ levW R i, δ = k * γ) ∧
      ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) :=
  GlobalTheory.T.exists_finset_levW_mul_heckeOn_mem_wall hLP γ hγ

theorem wall_props {T : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A)) :
    IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) T :=
  (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hT

theorem rinv (hLP : LevProd R i) {T : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A)) (v : (R.MW i (sg0 D A)).Vec)
    {k : GA D (Wc D i)} (hk : k ∈ levW R i) (g : GA D (Wc D i)) : T v (g * k) = T v g := by
  rw [(wall_props hT).lev v k hk g, hLP.2.1 k hk, one_mul]

theorem linv {T : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A)) (v : (R.MW i (sg0 D A)).Vec)
    {δ : GA D (Wc D i)} (hδ : δ ∈ GQ (Wc D i)) (g : GA D (Wc D i)) : T v (δ * g) = T v g :=
  ((wall_props hT).aut v).left δ hδ g

theorem cont {T : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A)) (v : (R.MW i (sg0 D A)).Vec) :
    Continuous (T v) := ((wall_props hT).aut v).cont

theorem heckeOn_single_apply (T : MMap (R.MW i (sg0 D A))) (γ : GA D (Wc D i)) (v : (R.MW i (sg0 D A)).Vec)
    (g : GA D (Wc D i)) : heckeOn (R.MW i (sg0 D A)) {γ} T v g = T v (g * γ) := by
  simp [heckeOn, postOn_apply, heckeLin_apply]

theorem heckeOn_apply (T : MMap (R.MW i (sg0 D A))) (C : Finset (GA D (Wc D i))) (v : (R.MW i (sg0 D A)).Vec)
    (g : GA D (Wc D i)) : heckeOn (R.MW i (sg0 D A)) C T v g = ∑ δ ∈ C, T v (g * δ) := by
  simp [heckeOn, postOn_apply, heckeLin_apply]

theorem hecke_one (T : MMap (R.MW i (sg0 D A))) : heckeOn (R.MW i (sg0 D A)) {1} T = T := by
  ext v g; simp [heckeOn, postOn_apply, heckeLin_apply]

theorem shift {F : Face D A} (hL : Laws R F) (u : GA D (Wc D i) → ℂ)
    (hu : ∀ δ ∈ GQ (Wc D i), ∀ h, u (δ * h) = u h) (y : GA D (Wc D i)) :
    ∫ h in R.fdW i, u (h * y) ∂(R.νW i) = ∫ h in R.fdW i, u h ∂(R.νW i) := by
  haveI : IsTopologicalGroup (GA D (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  haveI := (hL.models.νW i).1.1
  haveI := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D (Wc D i) (R.νW i) (hL.models.νW i).1.1
  exact GlobalTheory.DoubleCosetAdjoint.setIntegral_mul_right (R.νW i) (GQ (Wc D i)) (R.fdW i) (hL.models.νW i).2 u hu y

theorem sq_int {F : Face D A} (hL : Laws R F) {T : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A))
    (v : (R.MW i (sg0 D A)).Vec) : IntegrableOn (fun g => star (T v g) * T v g) (R.fdW i) (R.νW i) := by
  have hHW := hL.models.HW i (sg0 D A)
  obtain ⟨x, rfl⟩ : T ∈ LinearMap.range (R.HW i (sg0 D A)).e := by rw [hHW.2.1]; exact hT
  obtain ⟨c, hc⟩ := GlobalTheory.HeckeParts.exists_isMultIP hHW x x
  exact (hc v v).1

theorem sq_int_tr {F : Face D A} (hL : Laws R F) {T : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A))
    (v : (R.MW i (sg0 D A)).Vec) (δ : GA D (Wc D i)) :
    IntegrableOn (fun g => star (T v (g * δ)) * T v (g * δ)) (R.fdW i) (R.νW i) := by
  haveI : IsTopologicalGroup (GA D (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  haveI := (hL.models.νW i).1.1
  haveI := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D (Wc D i) (R.νW i) (hL.models.νW i).1.1
  exact GlobalTheory.DoubleCosetAdjoint.integrableOn_mul_right (R.νW i) (GQ (Wc D i)) (R.fdW i) (hL.models.νW i).2
    (fun g => star (T v g) * T v g) (fun δ' hδ' g => by simp only [linv hT v hδ' g]) δ (sq_int hL hT v)

theorem int_tr {F : Face D A} (hL : Laws R F) {T T' : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A))
    (hT' : T' ∈ R.Wall i (sg0 D A)) (v v' : (R.MW i (sg0 D A)).Vec) (δ : GA D (Wc D i)) :
    IntegrableOn (fun g => star (T v g) * T' v' (g * δ)) (R.fdW i) (R.νW i) := by
  haveI : IsTopologicalGroup (GA D (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
  exact GlobalTheory.DoubleCosetAdjoint.integrableOn_star_mul (R.νW i) (R.fdW i) (T v) (fun g => T' v' (g * δ))
    (cont hT v) ((cont hT' v').comp (continuous_mul_right δ)) (sq_int hL hT v) (sq_int_tr hL hT' v' δ)

theorem exists_ip {F : Face D A} (hL : Laws R F) (hLP : LevProd R i) {γ : GA D (Wc D i)} (hγ : γ ∈ GfC (Wc D i))
    {T T' : MMap (R.MW i (sg0 D A))} (hT : T ∈ R.Wall i (sg0 D A)) (hT' : T' ∈ R.Wall i (sg0 D A)) :
    ∃ c, IsMultIP (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) T (heckeOn (R.MW i (sg0 D A)) {γ} T') c := by
  have hHW := hL.models.HW i (sg0 D A)
  obtain ⟨C, hCne, hCk, hCW⟩ := exists_doubleCoset_sum hLP γ hγ
  obtain ⟨x, rfl⟩ : T ∈ LinearMap.range (R.HW i (sg0 D A)).e := by rw [hHW.2.1]; exact hT
  obtain ⟨y, hy⟩ : heckeOn (R.MW i (sg0 D A)) C T' ∈ LinearMap.range (R.HW i (sg0 D A)).e := by
    rw [hHW.2.1]; exact hCW T' hT'
  obtain ⟨c, hc⟩ := GlobalTheory.HeckeParts.exists_isMultIP hHW x y
  have hn : (C.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hCne)
  refine ⟨c / C.card, fun v v' => ⟨?_, ?_⟩⟩
  · simpa only [heckeOn_single_apply] using int_tr hL hT hT' v v' γ
  · have key : ∀ δ ∈ C, ∫ g in R.fdW i, star ((R.HW i (sg0 D A)).e x v g) * T' v' (g * δ) ∂(R.νW i) =
        ∫ g in R.fdW i, star ((R.HW i (sg0 D A)).e x v g) * T' v' (g * γ) ∂(R.νW i) := by
      intro δ hδ
      obtain ⟨k, hk, rfl⟩ := hCk δ hδ
      have hs := shift hL (fun g => star ((R.HW i (sg0 D A)).e x v (g * k⁻¹)) * T' v' (g * γ))
        (fun δ' hδ' g => by simp only [mul_assoc, linv hT v hδ', linv hT' v' hδ']) k
      simp only [mul_inv_cancel_right, rinv hLP hT v (inv_mem hk)] at hs
      simp only [← mul_assoc]
      exact hs
    have h2 := (hc v v').2
    rw [hy] at h2
    simp only [heckeOn_apply, Finset.mul_sum] at h2
    rw [integral_finset_sum _ fun δ _ => int_tr hL hT hT' v v' δ, Finset.sum_congr rfl key, Finset.sum_const,
      nsmul_eq_mul] at h2
    simp only [heckeOn_single_apply]
    rw [div_mul_eq_mul_div, eq_div_iff hn, mul_comm, h2]

set_option maxHeartbeats 1600000 in
theorem transLaws_of {F : Face D A} (hL : Laws R F) (hLP : LevProd R i) : TransLaws R i := by
  classical
  have hHW := hL.models.HW i (sg0 D A)
  have hW : ∀ x, (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := fun x => by
    rw [← hHW.2.1]; exact LinearMap.mem_range_self _ x
  have hfin : ∀ k ∈ levW R i, k ∈ GfC (Wc D i) := fun k hk => hLP.1 hk
  have ha : ∀ v f, IsFinIdem D v f → ∀ α, SuppF (Wc D i) f α → ∃ C : Finset (GA D (Wc D i)),
      (∀ γ ∈ C, SuppF (Wc D i) f γ) ∧ IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C :=
    fun v f hf α hα => exists_cosetRep_levG _ _ _ v f hf α hα
  have h1 : ∀ x y, trPair R i 1 x y = ⟪x, y⟫_ℂ := fun x y => by
    unfold trPair; rw [hecke_one]; exact (hHW.2.2 x y).symm
  by_cases hv : ∃ v0 : (R.MW i (sg0 D A)).Vec,
      ∏ τ, ⟪((v0 τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ), (v0 τ : (R.MW i (sg0 D A)).H τ)⟫_ℂ ≠ 0
  swap
  · push_neg at hv
    have hz : ∀ T : MMap (R.MW i (sg0 D A)), T = 0 := by
      intro T; ext v g
      obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 (hv v)
      have : v τ = 0 := Subtype.ext (inner_self_eq_zero.1 hτ)
      simp [T.map_coord_zero τ this]
    have hx0 : ∀ x : (R.HW i (sg0 D A)).H, x = 0 := fun x =>
      hHW.1 (by rw [hz ((R.HW i (sg0 D A)).e x), map_zero])
    have ht0 : ∀ γ x y, trPair R i γ x y = 0 := by
      intro γ x y
      rw [hx0 x, hx0 y, ← inner_zero_left (𝕜 := ℂ) (0 : (R.HW i (sg0 D A)).H)]
      unfold trPair
      rw [map_zero, map_zero, hHW.2.2 0 0, map_zero]
    refine ⟨ha, fun v f hf α hα C hC hR y => ⟨0, by rw [hz ((R.HW i _).e 0), hz (heckeOn _ C _)], fun γ _ x => by
      simp [ht0]⟩, fun γ _ => ⟨0, by simp, fun x y => by simp [ht0]⟩, fun γ _ k _ k' _ x y => by simp [ht0],
      fun γ _ x y => by simp [ht0], h1⟩

  obtain ⟨v0, hv0⟩ := hv
  set P := ∏ τ, ⟪((v0 τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ), (v0 τ : (R.MW i (sg0 D A)).H τ)⟫_ℂ
    with hP
  set cst : ℂ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ) with hcst
  set e := (R.HW i (sg0 D A)).e with he
  have hI : ∀ x y γ, IntegrableOn (fun g => star (e x v0 g) * e y v0 (g * γ)) (R.fdW i) (R.νW i) :=
    fun x y γ => int_tr hL (hW x) (hW y) v0 v0 γ
  have htp : ∀ γ ∈ GfC (Wc D i), ∀ x y, trPair R i γ x y =
      cst * (∫ g in R.fdW i, star (e x v0 g) * e y v0 (g * γ) ∂(R.νW i)) / P := by
    intro γ hγ x y
    have h := ipM_spec _ _ _ _ _ (exists_ip hL hLP hγ (hW x) (hW y)) v0 v0
    simp only [heckeOn_single_apply] at h
    rw [eq_div_iff hv0]
    show cst * ipM _ _ _ _ _ * P = _
    rw [mul_assoc, ← h.2]
  have hb : ∀ v f, IsFinIdem D v f → ∀ α, SuppF (Wc D i) f α → ∀ C : Finset (GA D (Wc D i)),
      (∀ γ ∈ C, SuppF (Wc D i) f γ) → IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C →
      ∀ y, ∃ y', e y' = heckeOn (R.MW i (sg0 D A)) C (e y) ∧
        ∀ γ ∈ GfC (Wc D i), ∀ x, trPair R i γ x y' = ∑ δ ∈ C, trPair R i (γ * δ) x y := by
    intro v f hf α hα C hC hR y
    obtain ⟨y', hy'⟩ : heckeOn (R.MW i (sg0 D A)) C (e y) ∈ LinearMap.range e := by
      rw [he, hHW.2.1]; exact heckeOn_mem_wall hLP v f hf α hα C hC hR _ (hW y)
    refine ⟨y', hy', fun γ hγ x => ?_⟩
    have hCf : ∀ δ ∈ C, δ ∈ GfC (Wc D i) := fun δ hδ => (hR.1 δ hδ).1
    rw [htp γ hγ, Finset.sum_congr rfl fun δ hδ => htp (γ * δ) (mul_mem hγ (hCf δ hδ)) x y, ← Finset.sum_div,
      ← Finset.mul_sum, ← integral_finset_sum _ fun δ _ => hI x y (γ * δ)]
    congr 3
    funext g
    rw [hy', heckeOn_apply, Finset.mul_sum]
    simp only [mul_assoc]
  have hd : ∀ γ ∈ GfC (Wc D i), ∀ k ∈ levW R i, ∀ k' ∈ levW R i, ∀ x y,
      trPair R i (k * γ * k') x y = trPair R i γ x y := by
    intro γ hγ k hk k' hk' x y
    rw [htp _ (mul_mem (mul_mem (hfin k hk) hγ) (hfin k' hk')), htp _ hγ]
    have e1 : ∀ g, e y v0 (g * (k * γ * k')) = e y v0 (g * k * γ) := fun g => by
      rw [show g * (k * γ * k') = g * k * γ * k' by group, rinv hLP (hW y) v0 hk']
    simp only [e1]
    have hs := shift hL (fun g => star (e x v0 (g * k⁻¹)) * e y v0 (g * γ))
      (fun δ hδ g => by simp only [mul_assoc, linv (hW x) v0 hδ, linv (hW y) v0 hδ]) k
    simp only [mul_inv_cancel_right, rinv hLP (hW x) v0 (inv_mem hk)] at hs
    rw [hs]
  have hcs : (starRingEnd ℂ) cst = cst := by rw [hcst, map_prod]; simp
  have hPs : (starRingEnd ℂ) P = P := by
    rw [hP, map_prod]; exact Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _
  have hsym : ∀ γ ∈ GfC (Wc D i), ∀ x y, trPair R i γ⁻¹ x y = star (trPair R i γ y x) := by
    intro γ hγ x y
    rw [htp _ (inv_mem hγ), htp _ hγ, Complex.star_def, map_div₀, map_mul, hcs, hPs]
    congr 2
    have hs := shift hL (fun g => star (e x v0 g) * e y v0 (g * γ⁻¹))
      (fun δ hδ g => by simp only [mul_assoc, linv (hW x) v0 hδ, linv (hW y) v0 hδ]) γ
    simp only [mul_inv_cancel_right, Complex.star_def] at hs
    rw [← hs, ← integral_conj]
    congr 1; funext g
    simp only [map_mul, Complex.star_def, Complex.conj_conj]; ring
  refine ⟨ha, hb, ?_, hd, hsym, h1⟩

  intro γ hγ
  haveI : IsTopologicalGroup (GA D (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
  have hn2 : ∀ z : (R.HW i (sg0 D A)).H, ‖⟪z, z⟫_ℂ‖ = ‖z‖ ^ 2 := fun z => by
    rw [inner_self_eq_norm_sq_to_K]; simp
  have hsq : ∀ x, ‖x‖ ^ 2 = ‖cst‖ * ‖∫ g in R.fdW i, star (e x v0 g) * e x v0 g ∂(R.νW i)‖ / ‖P‖ := fun x => by
    rw [← hn2, ← h1, htp 1 (one_mem _), norm_div, norm_mul]; simp only [mul_one]
  have hab : ∀ x y, ‖∫ g in R.fdW i, star (e x v0 g) * e y v0 (g * γ) ∂(R.νW i)‖ ^ 2 ≤
      ‖∫ g in R.fdW i, star (e x v0 g) * e x v0 g ∂(R.νW i)‖ * ‖∫ g in R.fdW i, star (e y v0 g) * e y v0 g ∂(R.νW i)‖ := by
    intro x y
    have hcs' := norm_integral_star_mul_sq_le ((R.νW i).restrict (R.fdW i)) (e x v0) (fun g => e y v0 (g * γ))
      (cont (hW x) v0).aestronglyMeasurable ((cont (hW y) v0).comp (continuous_mul_right γ)).aestronglyMeasurable
      (sq_int hL (hW x) v0) (sq_int_tr hL (hW y) v0 γ)
    have hsh := shift hL (fun g => star (e y v0 g) * e y v0 g)
      (fun δ hδ g => by simp only [linv (hW y) v0 hδ]) γ
    rw [hsh] at hcs'
    refine hcs'.trans ((le_abs_self _).trans ?_)
    rw [abs_mul]
    exact mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _) (abs_nonneg _) (norm_nonneg _)
  have hbd : ∀ x y, ‖trPair R i γ x y‖ ≤ 1 * ‖x‖ * ‖y‖ := by
    intro x y
    have key : (‖cst‖ * ‖∫ g in R.fdW i, star (e x v0 g) * e y v0 (g * γ) ∂(R.νW i)‖ / ‖P‖) ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
      rw [mul_pow, hsq x, hsq y, div_pow, mul_pow]
      rw [div_mul_div_comm, ← mul_pow, mul_mul_mul_comm, ← sq]
      gcongr
      all_goals first
        | positivity
        | exact (sq _).ge
        | (rw [mul_pow]; exact mul_le_mul_of_nonneg_left (hab x y) (by positivity))
    rw [htp γ hγ, norm_div, norm_mul, one_mul]
    have h0 : 0 ≤ ‖cst‖ * ‖∫ g in R.fdW i, star (e x v0 g) * e y v0 (g * γ) ∂(R.νW i)‖ / ‖P‖ := by positivity
    nlinarith [norm_nonneg x, norm_nonneg y, mul_nonneg (norm_nonneg x) (norm_nonneg y)]

  have hadd1 : ∀ x1 x2 y : (R.HW i (sg0 D A)).H, trPair R i γ (x1 + x2) y = trPair R i γ x1 y + trPair R i γ x2 y := by
    intro x1 x2 y
    have hf : ∀ g : GA D (Wc D i), star (e (x1 + x2) v0 g) * e y v0 (g * γ) =
        star (e x1 v0 g) * e y v0 (g * γ) + star (e x2 v0 g) * e y v0 (g * γ) := fun g => by
      simp only [map_add, MultilinearMap.add_apply, Pi.add_apply, Complex.star_def, add_mul]
    rw [htp γ hγ, htp γ hγ, htp γ hγ]
    simp only [hf]
    rw [integral_add (hI x1 y γ) (hI x2 y γ)]
    ring
  have hsm1 : ∀ (c : ℂ) (x y : (R.HW i (sg0 D A)).H), trPair R i γ (c • x) y = (starRingEnd ℂ) c • trPair R i γ x y := by
    intro c x y
    have hf : ∀ g : GA D (Wc D i), star (e (c • x) v0 g) * e y v0 (g * γ) = (starRingEnd ℂ) c * (star (e x v0 g) * e y v0 (g * γ)) :=
      fun g => by
        simp only [map_smul, MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Complex.star_def, map_mul]; ring
    rw [htp γ hγ, htp γ hγ]
    simp only [hf]
    rw [integral_const_mul (μ := (R.νW i).restrict (R.fdW i)) ((starRingEnd ℂ) c)
      (fun g => star (e x v0 g) * e y v0 (g * γ)), smul_eq_mul]
    ring
  have hadd2 : ∀ x y1 y2 : (R.HW i (sg0 D A)).H, trPair R i γ x (y1 + y2) = trPair R i γ x y1 + trPair R i γ x y2 := by
    intro x y1 y2
    have hf : ∀ g : GA D (Wc D i), star (e x v0 g) * e (y1 + y2) v0 (g * γ) =
        star (e x v0 g) * e y1 v0 (g * γ) + star (e x v0 g) * e y2 v0 (g * γ) := fun g => by
      simp only [map_add, MultilinearMap.add_apply, Pi.add_apply, mul_add]
    rw [htp γ hγ, htp γ hγ, htp γ hγ]
    simp only [hf]
    rw [integral_add (hI x y1 γ) (hI x y2 γ)]
    ring
  have hsm2 : ∀ (c : ℂ) (x y : (R.HW i (sg0 D A)).H), trPair R i γ x (c • y) = (RingHom.id ℂ) c • trPair R i γ x y := by
    intro c x y
    have hf : ∀ g : GA D (Wc D i), star (e x v0 g) * e (c • y) v0 (g * γ) = c * (star (e x v0 g) * e y v0 (g * γ)) := fun g => by
      simp only [map_smul, MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [htp γ hγ, htp γ hγ]
    simp only [hf]
    rw [integral_const_mul (μ := (R.νW i).restrict (R.fdW i)) c
      (fun g => star (e x v0 g) * e y v0 (g * γ)), smul_eq_mul, RingHom.id_apply]
    ring
  let Bs : (R.HW i (sg0 D A)).H →ₗ⋆[ℂ] (R.HW i (sg0 D A)).H →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => trPair R i γ x y) hadd1 hsm1 hadd2 hsm2
  let Bc := Bs.mkContinuous₂ 1 hbd
  have hrep : ∀ x y, trPair R i γ x y = ⟪x, ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin Bc) y⟫_ℂ := fun x y => by
    rw [ContinuousLinearMap.adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]; rfl
  refine ⟨ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin Bc), ?_, hrep⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  have h2 := hbd (ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin Bc) y) y
  rw [hrep, hn2, one_mul] at h2
  nlinarith [norm_nonneg (ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin Bc) y), norm_nonneg y]

theorem transLaws : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i, TransLaws R i := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F hL hFull i
  exact transLaws_of hL (GlobalTheory.T.level_subgroup_restricted_product_of_laws D G Pl0 T A Ks R F hL hFull i)

end GlobalTheory.RawLiftTrans
