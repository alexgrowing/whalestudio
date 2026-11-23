import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplMapSplitProj
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherExtra
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG (cT bc)
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.BlockForms.CuspGrowth

section Esum

variable {m k p : Type} [Fintype m] [Fintype k] [Fintype p]

def esum (M : Matrix m k ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖

theorem esum_nonneg (M : Matrix m k ℂ) : 0 ≤ esum M := by unfold esum; positivity

theorem esum_add_le (M N : Matrix m k ℂ) : esum (M + N) ≤ esum M + esum N := by
  unfold esum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => norm_add_le _ _

theorem esum_sub_le (M N : Matrix m k ℂ) : esum (M - N) ≤ esum M + esum N := by
  unfold esum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => norm_sub_le _ _

theorem esum_mul_le (M : Matrix m k ℂ) (N : Matrix k p ℂ) : esum (M * N) ≤ esum M * esum N := by
  first
  | exact @_root_.GlobalTheory.SpectralLemmaSecond.main
  | exact _root_.GlobalTheory.SpectralLemmaSecond.main
  | (apply _root_.GlobalTheory.SpectralLemmaSecond.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpectralLemmaSecond.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpectralLemmaSecond.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpectralLemmaSecond.main ..)

theorem esum_le_of_entry (M : Matrix m k ℂ) {c : ℝ} (h : ∀ i j, ‖M i j‖ ≤ c) :
    esum M ≤ Fintype.card m * (Fintype.card k * c) := by
  unfold esum
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j).trans ?_
  simp

theorem esum_one_le [DecidableEq m] : esum (1 : Matrix m m ℂ) ≤ Fintype.card m * (Fintype.card m * 1) :=
  esum_le_of_entry _ fun i j => by
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]

theorem opNorm_le_esum [DecidableEq m] (A : Matrix m m ℂ) : (GlobalTheory.AdelicU.opNorm A : ℝ) ≤ esum A := by
  change ‖Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A‖ ≤ _
  refine ContinuousLinearMap.opNorm_le_bound _ (esum_nonneg A) fun x => ?_
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨mul_nonneg (esum_nonneg A) (norm_nonneg _), ?_⟩
  refine (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _).trans ?_
  unfold esum
  gcongr
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have : (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) A x) i = ∑ j, A i j * x j := rfl
  rw [this, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  gcongr
  exact PiLp.norm_apply_le x j

end Esum

end GlobalTheory.BlockForms.CuspGrowth

namespace GlobalTheory.BlockForms.CuspGrowth

open GlobalTheory.CuspRep (Ad Cinf sInf infEq continuous_infEq infGL toL)

section Entries

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem exists_bound_sInf (f : Ad E →+* ℂ) (hf : Continuous f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z : Cinf E, ‖f (sInf E z)‖ ≤ L * ‖z‖ := by
  let g : Cinf E →+ ℂ :=
    { toFun := fun z => f (sInf E z)
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hg : Continuous g := hf.comp ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × GlobalTheory.CuspRep.Af E))
  let L := g.toRealLinearMap hg
  exact ⟨‖L‖, norm_nonneg _, fun z => L.le_opNorm z⟩

theorem exists_entry_bound (f : Ad E →+* ℂ) (hf : Continuous f) (d : ℕ) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (y : GL (Fin d) (Cinf E)) (a b : Fin d), ‖f ((infGL E d y).1 a b)‖ ≤ c * GlobalTheory.CuspRep.height y := by
  obtain ⟨L, hL0, hL⟩ := exists_bound_sInf f hf
  refine ⟨1 + L, by linarith, fun y a b => ?_⟩
  have e : (infGL E d y).1 a b =
      (1 : Matrix (Fin d) (Fin d) (Ad E)) a b - sInf E ((1 : Matrix (Fin d) (Fin d) (Cinf E)) a b) + sInf E (y.1 a b) := rfl
  have h1 : ‖f ((1 : Matrix (Fin d) (Fin d) (Ad E)) a b)‖ ≤ 1 := by
    by_cases h : a = b
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have h2 : ‖((1 : Matrix (Fin d) (Fin d) (Cinf E)) a b)‖ ≤ 1 := by
    by_cases h : a = b
    · subst h
      rw [Matrix.one_apply_eq]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => by simp
    · simp [Matrix.one_apply_ne h]
  have h3 : ‖y.1 a b‖ ≤ ‖toL y.val‖ :=
    (norm_le_pi_norm (toL y.val a) b).trans (norm_le_pi_norm (toL y.val) a)
  have h4 : 0 ≤ ‖toL (y⁻¹).val‖ := norm_nonneg _
  rw [e, map_add, map_sub]
  calc ‖f ((1 : Matrix (Fin d) (Fin d) (Ad E)) a b) - f (sInf E ((1 : Matrix (Fin d) (Fin d) (Cinf E)) a b)) +
        f (sInf E (y.1 a b))‖
      ≤ 1 + L * 1 + L * ‖toL y.val‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add h1 ?_)) ?_)
        · exact (hL _).trans (mul_le_mul_of_nonneg_left h2 hL0)
        · exact (hL _).trans (mul_le_mul_of_nonneg_left h3 hL0)
    _ ≤ (1 + L) * GlobalTheory.CuspRep.height y := by
        unfold GlobalTheory.CuspRep.height
        nlinarith [norm_nonneg (toL y.val)]

theorem height_inv' {d : ℕ} (y : GL (Fin d) (Cinf E)) : GlobalTheory.CuspRep.height y⁻¹ = GlobalTheory.CuspRep.height y := by
  unfold GlobalTheory.CuspRep.height; rw [inv_inv]; ring

end Entries

end GlobalTheory.BlockForms.CuspGrowth

namespace GlobalTheory.BlockForms.CuspGrowth

open GlobalTheory.CuspRep (Ad Cinf sInf infEq continuous_infEq infGL toL pFin_infGL)
open GlobalTheory.BlockForms.LeviLoc (gl_entry fin_symm compFin_eq_zero compFin_sigR map_formula)

section Block

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]

theorem map_one_add_two_rank_perturbation {R T : Type} [CommRing R] [CommRing T] (p : R →+* T) {n d : ℕ}
    (A C : Matrix (Fin n) (Fin d) R) (B D : Matrix (Fin d) (Fin n) R) (P Q : Matrix (Fin d) (Fin d) R) :
    (1 + A * (P - 1) * B + C * (Q - 1) * D).map p =
      1 + A.map p * (P.map p - 1) * B.map p + C.map p * (Q.map p - 1) * D.map p := by
  simp [Matrix.map_add, Matrix.map_mul, Matrix.map_sub, Matrix.map_one]

variable {Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E} {j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E}
  (hΦ : ∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z)))
include hΦ

theorem map_compFin_infGL (u : HeightOneSpectrum (𝓞 F)) {d : ℕ} (y : GL (Fin d) (Cinf E)) :
    ((infGL E d y).1.map Φ.symm).map (compFin F E u) = 1 := by
  refine Matrix.ext fun a b => ?_
  have h1 := compFin_eq_zero u (Φ.symm ((infGL E d y).1 a b) - (1 : Matrix (Fin d) (Fin d) _) a b)
    fun w' _ => by
      have h2 : GlobalTheory.CuspRep.pFin E ((infGL E d y).1 a b) = (1 : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Af E)) a b :=
        gl_entry (pFin_infGL y) a b
      rw [map_sub, map_sub, map_sub, fin_symm hΦ, h2, sub_eq_zero]
      by_cases e : a = b
      · subst e; simp only [Matrix.one_apply_eq, map_one]
      · simp only [Matrix.one_apply_ne e, map_zero]
  rw [map_sub, sub_eq_zero] at h1
  refine h1.trans ?_
  by_cases e : a = b
  · subst e; simp only [Matrix.one_apply_eq, map_one]
  · simp only [Matrix.one_apply_ne e, map_zero]

end Block

end GlobalTheory.BlockForms.CuspGrowth

namespace GlobalTheory.BlockForms.CuspGrowth

open GlobalTheory.CuspRep (Ad Cinf sInf infEq continuous_infEq infGL toL pFin_infGL)
open GlobalTheory.BlockForms.LeviLoc (gl_entry fin_symm compFin_eq_zero compFin_sigR map_formula)

section Emb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {Xf Yf : Matrix (Fin n) (Fin r) E} {l d : ℕ}
  {h : l + d ≤ r} {ι : GlobalTheory.CuspRep.GA E d →* GAd σ J}

theorem htFin_blockEmb_infGL (hι : IsBlockEmb σ J Xf Yf h ι) (v : HeightOneSpectrum (𝓞 F))
    (y : GL (Fin d) (Cinf E)) : htFin F v (bc (compFin F E v) (matHom (AF F) σ J (ι (infGL E d y)))) = 1 := by
  obtain ⟨Φ, j, -, -, -, hΦ, hM⟩ := hι
  have hM' := hM (infGL E d y)
  rw [← map_inv] at hM'
  have hQ : (((infGL E d y⁻¹).1.map Φ.symm).map ((compFin F E v).comp (sigR (AF F) σ))) = 1 := by
    have e : (compFin F E v).comp (sigR (AF F) σ) = (sigR _ σ).comp (compFin F E v) :=
      RingHom.ext (compFin_sigR σ v)
    rw [e, RingHom.coe_comp, ← Matrix.map_map, map_compFin_infGL hΦ, Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : bc (compFin F E v) (matHom (AF F) σ J (ι (infGL E d y))) = 1 := by
    refine Units.ext ?_
    change (matHom (AF F) σ J (ι (infGL E d y))).1.map (compFin F E v) = 1
    rw [hM', map_formula _ _ _ _ _ _ _ _ hQ, map_compFin_infGL hΦ]
    simp
  rw [e1]
  exact htOf_eq_one.2 ⟨normFin_one_le F v, by rw [inv_one]; exact normFin_one_le F v⟩

end Emb

end GlobalTheory.BlockForms.CuspGrowth

namespace GlobalTheory.BlockForms.CuspGrowth

open GlobalTheory.CuspRep (Ad Cinf sInf infEq continuous_infEq infGL toL pFin_infGL)

section Inf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {Xf Yf : Matrix (Fin n) (Fin r) E} {l d : ℕ}
  {h : l + d ≤ r} {ι : GlobalTheory.CuspRep.GA E d →* GAd σ J}

theorem exists_opNorm_blockEmb_infGL_le (hι : IsBlockEmb σ J Xf Yf h ι) (w : InfinitePlace F) (τ : EmbOver E w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : GL (Fin d) (Cinf E),
      (opNorm ((matHom (AF F) σ J (ι (infGL E d y))).1.map ((infEmb τ).comp (compInf F E w))) : ℝ) ≤
        K * GlobalTheory.CuspRep.height y := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨Φ, j, -, hΦc, -, -, hM⟩ := hι
  set θ := (infEmb τ).comp (compInf F E w) with hθ
  have hθc : Continuous θ := GlobalTheory.Grow.continuous_infEmb_compInf F w τ
  obtain ⟨c1, hc1, hb1⟩ := exists_entry_bound (θ.comp Φ.symm.toRingHom) (hθc.comp hΦc) d
  obtain ⟨c2, hc2, hb2⟩ := exists_entry_bound (θ.comp ((sigR (AF F) σ).comp Φ.symm.toRingHom))
    (hθc.comp ((GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ).comp hΦc)) d
  set A := (adMat F (blkCols h Xf)).map θ
  set B := (adMat F (cT (σ : E →+* E) (blkCols h Yf) * J)).map θ
  set C := (adMat F (blkCols h Yf)).map θ
  set D := (adMat F (cT (σ : E →+* E) (blkCols h Xf) * J)).map θ
  set a1 : ℝ := d * (d * c1) + d * (d * 1)
  set a2 : ℝ := d * (d * c2) + d * (d * 1)
  have ha1 : 0 ≤ a1 := add_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by linarith)))
    (by positivity)
  have ha2 : 0 ≤ a2 := add_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by linarith)))
    (by positivity)
  refine ⟨n * (n * 1) + esum A * a1 * esum B + esum C * a2 * esum D,
    add_nonneg (add_nonneg (by positivity) (mul_nonneg (mul_nonneg (esum_nonneg A) ha1) (esum_nonneg B)))
      (mul_nonneg (mul_nonneg (esum_nonneg C) ha2) (esum_nonneg D)), fun y => ?_⟩
  set hh := GlobalTheory.CuspRep.height y
  have h1 : 1 ≤ hh := GlobalTheory.CuspRep.one_le_height y
  set P' := ((infGL E d y).1.map Φ.symm).map θ
  set Q' := (cT (sigR (AF F) σ) (((infGL E d y)⁻¹).1.map Φ.symm)).map θ
  have eM : (matHom (AF F) σ J (ι (infGL E d y))).1.map θ = 1 + A * (P' - 1) * B + C * (Q' - 1) * D := by
    rw [hM, map_one_add_two_rank_perturbation]
  have hP : ∀ a b, ‖P' a b‖ ≤ c1 * hh := fun a b => hb1 y a b
  have hQ : ∀ a b, ‖Q' a b‖ ≤ c2 * hh := fun a b => by
    have := hb2 y⁻¹ b a
    rw [map_inv, height_inv'] at this
    exact this
  have e1d : esum (1 : Matrix (Fin d) (Fin d) ℂ) ≤ d * (d * 1) := by simpa using esum_one_le (m := Fin d)
  have e1n : esum (1 : Matrix (Fin n) (Fin n) ℂ) ≤ n * (n * 1) := by simpa using esum_one_le (m := Fin n)
  have eP : esum P' ≤ d * (d * (c1 * hh)) := by simpa using esum_le_of_entry P' hP
  have eQ : esum Q' ≤ d * (d * (c2 * hh)) := by simpa using esum_le_of_entry Q' hQ
  have hd1 : (d : ℝ) * (d * 1) ≤ d * (d * 1) * hh := le_mul_of_one_le_right (by positivity) h1
  have k1 : esum P' + esum (1 : Matrix (Fin d) (Fin d) ℂ) ≤ a1 * hh :=
    calc esum P' + esum (1 : Matrix (Fin d) (Fin d) ℂ) ≤ d * (d * (c1 * hh)) + d * (d * 1) * hh :=
          add_le_add eP (e1d.trans hd1)
      _ = a1 * hh := by ring
  have k2 : esum Q' + esum (1 : Matrix (Fin d) (Fin d) ℂ) ≤ a2 * hh :=
    calc esum Q' + esum (1 : Matrix (Fin d) (Fin d) ℂ) ≤ d * (d * (c2 * hh)) + d * (d * 1) * hh :=
          add_le_add eQ (e1d.trans hd1)
      _ = a2 * hh := by ring
  have t1 : esum (A * (P' - 1) * B) ≤ esum A * (a1 * hh) * esum B :=
    (esum_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((esum_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ((esum_sub_le _ _).trans k1) (esum_nonneg A))) (esum_nonneg B))
  have t2 : esum (C * (Q' - 1) * D) ≤ esum C * (a2 * hh) * esum D :=
    (esum_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((esum_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ((esum_sub_le _ _).trans k2) (esum_nonneg C))) (esum_nonneg D))
  have t0 : esum (1 : Matrix (Fin n) (Fin n) ℂ) ≤ n * (n * 1) * hh :=
    e1n.trans (le_mul_of_one_le_right (by positivity) h1)
  have s1 := esum_add_le (1 : Matrix (Fin n) (Fin n) ℂ) (A * (P' - 1) * B)
  have s2 := esum_add_le (1 + A * (P' - 1) * B) (C * (Q' - 1) * D)
  calc (opNorm ((matHom (AF F) σ J (ι (infGL E d y))).1.map θ) : ℝ)
      ≤ esum ((matHom (AF F) σ J (ι (infGL E d y))).1.map θ) := opNorm_le_esum _
    _ = esum (1 + A * (P' - 1) * B + C * (Q' - 1) * D) := by rw [eM]
    _ ≤ n * (n * 1) * hh + esum A * (a1 * hh) * esum B + esum C * (a2 * hh) * esum D := by linarith
    _ = (n * (n * 1) + esum A * a1 * esum B + esum C * a2 * esum D) * hh := by ring

end Inf

end GlobalTheory.BlockForms.CuspGrowth

namespace GlobalTheory.BlockForms.CuspGrowth

open GlobalTheory.CuspRep (Ad Cinf sInf infEq continuous_infEq infGL toL pFin_infGL)

section Ht

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {Xf Yf : Matrix (Fin n) (Fin r) E} {l d : ℕ}
  {h : l + d ≤ r} {ι : GlobalTheory.CuspRep.GA E d →* GAd σ J}

theorem exists_htInf_blockEmb_infGL_le (hι : IsBlockEmb σ J Xf Yf h ι) (w : InfinitePlace F) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ y : GL (Fin d) (Cinf E),
      (htInf F w (bc (compInf F E w) (matHom (AF F) σ J (ι (infGL E d y)))) : ℝ) ≤ c * GlobalTheory.CuspRep.height y := by
  choose K hK0 hK using exists_opNorm_blockEmb_infGL_le hι w
  have hS : 0 ≤ ∑ τ, K τ := Finset.sum_nonneg fun τ _ => hK0 τ
  refine ⟨1 + ∑ τ, K τ, by linarith, fun y => ?_⟩
  have hh1 := GlobalTheory.CuspRep.one_le_height y
  have hpos : 0 ≤ (1 + ∑ τ, K τ) * GlobalTheory.CuspRep.height y := by nlinarith
  have hs : ∀ τ, K τ ≤ 1 + ∑ τ, K τ := fun τ =>
    (Finset.single_le_sum (f := K) (fun τ _ => hK0 τ) (Finset.mem_univ τ)).trans (by linarith)
  have key : ∀ y' : GL (Fin d) (Cinf E), GlobalTheory.CuspRep.height y' = GlobalTheory.CuspRep.height y →
      normInf F w ((bc (compInf F E w) (matHom (AF F) σ J (ι (infGL E d y')))).1) ≤
        Real.toNNReal ((1 + ∑ τ, K τ) * GlobalTheory.CuspRep.height y) := by
    intro y' hy'
    refine (normInf_le_iff F w).2 fun τ => ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hpos]
    change (opNorm (((matHom (AF F) σ J (ι (infGL E d y'))).1.map (compInf F E w)).map (infEmb τ)) : ℝ) ≤ _
    rw [Matrix.map_map]
    refine (hK τ y').trans ?_
    rw [hy']
    exact mul_le_mul_of_nonneg_right (hs τ) (by linarith)
  have e : (bc (compInf F E w) (matHom (AF F) σ J (ι (infGL E d y))))⁻¹ =
      bc (compInf F E w) (matHom (AF F) σ J (ι (infGL E d y⁻¹))) := by simp only [map_inv]
  have h1 : (1 : ℝ≥0) ≤ Real.toNNReal ((1 + ∑ τ, K τ) * GlobalTheory.CuspRep.height y) := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hpos, NNReal.coe_one]; nlinarith
  have hle : htInf F w (bc (compInf F E w) (matHom (AF F) σ J (ι (infGL E d y)))) ≤
      Real.toNNReal ((1 + ∑ τ, K τ) * GlobalTheory.CuspRep.height y) := by
    refine max_le h1 (max_le (key y rfl) ?_)
    rw [e]
    exact key y⁻¹ (height_inv' y)
  exact (NNReal.coe_le_coe.2 hle).trans (le_of_eq (Real.coe_toNNReal _ hpos))

theorem exists_height_blockEmb_infGL_le (hι : IsBlockEmb σ J Xf Yf h ι) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : GL (Fin d) (Cinf E),
      (height σ J (ι (infGL E d y)) : ℝ) ≤ K * GlobalTheory.CuspRep.height y ^ Fintype.card (InfinitePlace F) := by
  choose c hc1 hc using exists_htInf_blockEmb_infGL_le hι
  refine ⟨∏ w, c w, Finset.prod_nonneg fun w _ => by linarith [hc1 w], fun y => ?_⟩
  have e : height σ J (ι (infGL E d y)) =
      ∏ w, htInf F w (bc (compInf F E w) (matHom (AF F) σ J (ι (infGL E d y)))) := by
    unfold GlobalTheory.AdelicU.height heightGL
    simp only [htFin_blockEmb_infGL hι, finprod_one, mul_one]
  rw [e, NNReal.coe_prod]
  calc ∏ w, (htInf F w (bc (compInf F E w) (matHom (AF F) σ J (ι (infGL E d y)))) : ℝ)
      ≤ ∏ w, (c w * GlobalTheory.CuspRep.height y) :=
        Finset.prod_le_prod (fun w _ => NNReal.coe_nonneg _) fun w _ => hc w y
    _ = (∏ w, c w) * GlobalTheory.CuspRep.height y ^ Fintype.card (InfinitePlace F) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end Ht

end GlobalTheory.BlockForms.CuspGrowth

open GlobalTheory.BlockForms.CuspGrowth in

theorem GlobalTheory.BlockForms.growth_comp_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        ∀ g : GlobalTheory.CuspRep.GA E d, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ (ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ K _ S l d h ι hι _ _ _ _ ψ hψ g₀ _ g
  obtain ⟨N, hN⟩ := hψ.1.growth
  obtain ⟨C0, hC0⟩ := hN [] (by simp)
  obtain ⟨K', hK'0, hK'⟩ := exists_height_blockEmb_infGL_le hι
  set a : ℝ := (height σ J (ι g) : ℝ)
  set b : ℝ := (height σ J g₀ : ℝ)
  have ha : 0 ≤ a := NNReal.coe_nonneg _
  have hb : 0 ≤ b := NNReal.coe_nonneg _
  refine ⟨max C0 0 * (a * K' * b) ^ N, Fintype.card (InfinitePlace F) * N, fun y => ?_⟩
  set c := Fintype.card (InfinitePlace F)
  have hx : ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀ = ι g * ι (GlobalTheory.CuspRep.infGL E d y) * g₀ := by rw [map_mul]
  have hH : (height σ J (ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀) : ℝ) ≤
      a * (K' * GlobalTheory.CuspRep.height y ^ c) * b := by
    rw [hx]
    have e1 : (height σ J (ι g * ι (GlobalTheory.CuspRep.infGL E d y) * g₀) : ℝ) ≤
        height σ J (ι g * ι (GlobalTheory.CuspRep.infGL E d y)) * b := by
      exact_mod_cast height_mul_le σ J (ι g * ι (GlobalTheory.CuspRep.infGL E d y)) g₀
    have e2 : (height σ J (ι g * ι (GlobalTheory.CuspRep.infGL E d y)) : ℝ) ≤
        a * height σ J (ι (GlobalTheory.CuspRep.infGL E d y)) := by
      exact_mod_cast height_mul_le σ J (ι g) (ι (GlobalTheory.CuspRep.infGL E d y))
    exact e1.trans (mul_le_mul_of_nonneg_right (e2.trans (mul_le_mul_of_nonneg_left (hK' y) ha)) hb)
  have h0 := hC0 (ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀)
  simp only [List.foldr_nil] at h0
  have hHn : 0 ≤ (height σ J (ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀) : ℝ) := NNReal.coe_nonneg _
  calc ‖ψ (ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀)‖
      ≤ C0 * (height σ J (ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀) : ℝ) ^ N := h0
    _ ≤ max C0 0 * (height σ J (ι (g * GlobalTheory.CuspRep.infGL E d y) * g₀) : ℝ) ^ N :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hHn _)
    _ ≤ max C0 0 * (a * (K' * GlobalTheory.CuspRep.height y ^ c) * b) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hHn hH _) (le_max_right _ _)
    _ = max C0 0 * (a * K' * b) ^ N * GlobalTheory.CuspRep.height y ^ (c * N) := by ring
