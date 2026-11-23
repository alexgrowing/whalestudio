import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.IntegrableChart
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.ContinuousLev
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.GoodSmul
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.CuspUmg
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RapidDecay

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW.SliceClasses

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} {S : Set (Pl E)}

theorem ct_le (n r N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : GA E n → ℂ) (B : ℝ), (∀ g, ‖φ g‖ ≤ B * AutomorphicForm.height g ^ N) →
    ∀ g, ‖AutomorphicForm.constantTerm r φ g‖ ≤ C * B * AutomorphicForm.height g ^ N := by
  obtain ⟨D, hD, hsub⟩ := AutomorphicForm.exists_isCompact_superset_unipFundamentalDomain (K := E) (n := n) (r := r)
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact (hD.image AutomorphicForm.continuous_unipGL)
  have hc0 : 0 ≤ AutomorphicForm.heightConst E n := le_trans zero_le_one AutomorphicForm.one_le_heightConst
  have hfin : AutomorphicForm.unipMeasure E n r (AutomorphicForm.unipFundamentalDomain E n r) < ⊤ :=
    (measure_mono hsub).trans_lt hD.measure_lt_top
  refine ⟨(AutomorphicForm.heightConst E n * |M|) ^ N *
    (AutomorphicForm.unipMeasure E n r).real (AutomorphicForm.unipFundamentalDomain E n r), by positivity, fun φ B hφ g => ?_⟩
  have hg := (AutomorphicForm.height_pos g).le
  have hB : 0 ≤ B := by simpa [AutomorphicForm.height_one] using (norm_nonneg _).trans (hφ 1)
  have hb : ∀ X ∈ AutomorphicForm.unipFundamentalDomain E n r, ‖φ (AutomorphicForm.unipGL X * g)‖ ≤
      B * (AutomorphicForm.heightConst E n * |M| * AutomorphicForm.height g) ^ N := by
    intro X hX
    have h1 : AutomorphicForm.height (AutomorphicForm.unipGL X * g) ≤
        AutomorphicForm.heightConst E n * |M| * AutomorphicForm.height g :=
      (AutomorphicForm.height_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((hM _ ⟨X, hsub hX, rfl⟩).trans (le_abs_self M)) hc0) hg)
    exact (hφ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le h1 N) hB)
  refine (norm_setIntegral_le_of_norm_le_const hfin hb).trans (le_of_eq ?_)
  rw [mul_pow (AutomorphicForm.heightConst E n * |M|)]
  ring

theorem ct_rt {n : ℕ} (r : ℕ) (φ : Sm E n) (h g : GA E n) :
    AutomorphicForm.constantTerm r (rt E n h φ).1 g = AutomorphicForm.constantTerm r φ.1 (g * h) := by
  unfold AutomorphicForm.constantTerm
  simp only [rt_apply, mul_assoc]

def IsCt (r s : ℕ) (F : Sm E (r + s)) : Prop := ∃ φ : Sm E (r + s), Umg φ ∧ F.1 = AutomorphicForm.constantTerm r φ.1

theorem ct_uC {φ F : Sm E (r + s)} (hφ : Umg φ) (hF : F.1 = AutomorphicForm.constantTerm r φ.1) (u : UC E (r + s)) :
    (uC E (r + s) u F).1 = AutomorphicForm.constantTerm r (uC E (r + s) u φ).1 := by
  obtain ⟨F', hF', -, -, hu⟩ := ctOps E r s φ hφ
  obtain rfl : F = F' := Subtype.ext (hF.trans hF'.symm)
  exact hu u

theorem IsCt.uC {F : Sm E (r + s)} (h : IsCt r s F) (u : UC E (r + s)) : IsCt r s (uC E (r + s) u F) := by
  obtain ⟨φ, hφ, hF⟩ := h
  exact ⟨_, ((umgOps E (r + s)).2 φ hφ).2.2.2.1 u, ct_uC hφ hF u⟩

theorem IsCt.continuous {F : Sm E (r + s)} (h : IsCt r s F) : Continuous F.1 := by
  obtain ⟨φ, hφ, hF⟩ := h
  refine ContAut.continuous_of_isOpen_stab E _ F (isOpen_stab_of_mem_nhds _ _
    (Filter.mem_of_superset (hφ.level.mem_nhds (by simp)) fun k hk => Subtype.ext (funext fun g => ?_)))
  have hk' : rt E (r + s) (finGL E (r + s) k) φ = φ := hk
  change F.1 (g * finGL E (r + s) k) = F.1 g
  rw [hF, ← ct_rt, hk']

theorem zt_comm (n : ℕ) (t : ℝ) (g : GA E n) : zt E n t * g = g * zt E n t := centralSection_mul_comm _ g

theorem ct_left {φ : GA E (r + s) → ℂ} (hφ : AutomorphicForm.IsLeftInvariant φ) (hs : φ ∈ Sm E (r + s))
    (hU : Umg ⟨φ, hs⟩) (t : ℝ) (g : GA E (r + s)) :
    AutomorphicForm.IsLeftInvariant fun x : GA E r =>
      AutomorphicForm.constantTerm r φ (lev (Ad E) r s (zt E r t * x, 1) * g) := by
  intro γ x
  obtain ⟨F, hF, -, hM, -⟩ := ctOps E r s ⟨φ, hs⟩ hU
  have := hM (γ, 1) (lev (Ad E) r s (zt E r t * x, 1) * g)
  rw [hF, ← mul_assoc, ← map_mul, Prod.mk_mul_mk, map_one, one_mul, ← mul_assoc, ← zt_comm, mul_assoc] at this
  exact this

abbrev pt (r s : ℕ) (t : ℝ) (y : RightCosetSpace (rationalGLOne E r)) : GA E (r + s) :=
  lev (Ad E) r s (zt E r t * ((Quotient.out y : normOneGL E r) : GA E r), 1)

abbrev wt (f : GA E r → ℂ) (y : RightCosetSpace (rationalGLOne E r)) : ℂ :=
  starRingEnd ℂ (f ((Quotient.out y : normOneGL E r) : GA E r))

abbrev nu (E : Type) [Field E] [NumberField E] (r : ℕ) : Measure (RightCosetSpace (rationalGLOne E r)) :=
  quotientMeasure (rationalGLOne E r) (mu1 E r)

instance : IsFiniteMeasure (nu E r) := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := r) (mu1 E r)

def big (s : ℕ) (f : GA E r → ℂ) (t : ℝ) (φ : GA E (r + s) → ℂ) : GA E (r + s) → ℂ :=
  avg (nu E r) (pt r s t) (wt f) (AutomorphicForm.constantTerm r φ)

theorem slice_eq (f : GA E r → ℂ) (t : ℝ) (φ : GA E (r + s) → ℂ) (m : GA E s) :
    slice f t φ m = big s f t φ (lev (Ad E) r s (1, m)) := by
  unfold slice big avg
  simp only [pt, wt, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

theorem integrand_le (b : Blo S r) (s : ℕ) (t : ℝ) (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Sm E (r + s)) (B : ℝ), Umg φ →
    (∀ g, ‖φ.1 g‖ ≤ B * AutomorphicForm.height g ^ N) → ∀ y g,
      ‖AutomorphicForm.constantTerm r φ.1 (pt r s t y * g) * wt b.f.1 y‖ ≤ C * B * AutomorphicForm.height g ^ N := by
  obtain ⟨C, hC0, hC⟩ := ct_le (E := E) (r + s) r N
  obtain ⟨hf, hfc⟩ := cuspUmg E r b.f b.cusp
  obtain ⟨D, hD⟩ := rapidDecay E r b.f hf hfc N
  have hD0 : 0 ≤ D := le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (zero_le_one.trans (Pair.one_le_qht 1)) _)) (hD 1)
  have h1 : 0 ≤ AutomorphicForm.heightConst E (r + s) := le_trans zero_le_one AutomorphicForm.one_le_heightConst
  have h2 : 0 ≤ AutomorphicForm.heightConst E r := le_trans zero_le_one AutomorphicForm.one_le_heightConst
  have h3 := (AutomorphicForm.height_pos (zt E r t)).le
  set A := AutomorphicForm.heightConst E (r + s) * (AutomorphicForm.heightConst E (r + s) *
    (AutomorphicForm.heightConst E r * AutomorphicForm.height (zt E r t))) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨C * A ^ N * 2 ^ N * D, by positivity, fun φ B hφ hB y g => ?_⟩
  have hB0 : 0 ≤ B := by simpa [AutomorphicForm.height_one] using (norm_nonneg _).trans (hB 1)
  have hg := (AutomorphicForm.height_pos g).le
  refine (Pair.pair_le (B := C * B * (A * AutomorphicForm.height g) ^ N) (ct_left hφ.left φ.2 hφ t g) (by positivity)
    (fun x => (hC φ.1 B hB _).trans ?_) hD _).trans (le_of_eq (by rw [mul_pow]; ring))
  rw [mul_assoc (C * B), ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le ?_ N) (by positivity)
  have e1 := Pair.height_lev (E := E) (r := r) (s := s) (zt E r t * x) 1
  rw [AutomorphicForm.height_one, mul_one] at e1
  have e2 := e1.trans (mul_le_mul_of_nonneg_left (AutomorphicForm.height_mul_le (zt E r t) x) h1)
  refine (AutomorphicForm.height_mul_le _ _).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 h1) hg).trans (le_of_eq ?_))
  rw [hA]; ring

theorem big_le (b : Blo S r) (s : ℕ) (t : ℝ) (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Sm E (r + s)) (B : ℝ), Umg φ →
    (∀ g, ‖φ.1 g‖ ≤ B * AutomorphicForm.height g ^ N) → ∀ g,
      ‖big s b.f.1 t φ.1 g‖ ≤ C * B * AutomorphicForm.height g ^ N := by
  obtain ⟨C, hC0, hC⟩ := integrand_le b s t N
  refine ⟨C * (nu E r).real Set.univ, by positivity, fun φ B hφ hB g => ?_⟩
  exact (norm_integral_le_of_norm_le_const (.of_forall fun y => hC φ B hφ hB y g)).trans (le_of_eq (by ring))

theorem cls (b : Blo S r) (s : ℕ) (t : ℝ) : Cls (nu E r) (pt r s t) (wt b.f.1) (IsCt r s) where
  lie F X h := by rw [← uC_ιC]; exact h.uC _
  meas F h g := by
    have hc := h.continuous
    obtain ⟨φ, hφ, hF⟩ := h
    obtain ⟨hf, -⟩ := cuspUmg E r b.f b.cusp
    have hl : AutomorphicForm.IsLeftInvariant fun x : GA E r =>
        F.1 (lev (Ad E) r s (zt E r t * x, 1) * g) * starRingEnd ℂ (b.f.1 x) := fun γ x => by
      have := ct_left hφ.left φ.2 hφ t g γ x
      beta_reduce at this ⊢
      rw [hF, this, hf.left γ]
    have hcc : Continuous fun x : GA E r => F.1 (lev (Ad E) r s (zt E r t * x, 1) * g) * starRingEnd ℂ (b.f.1 x) :=
      (hc.comp ((Pair.continuous_lev.comp ((continuous_const.mul continuous_id).prodMk continuous_const)).mul
        continuous_const)).mul (Complex.continuous_conj.comp ((umgOps E r).2 b.f hf).1)
    exact (continuous_cuspQuot hl hcc).aestronglyMeasurable.congr (.of_forall fun y => (Pair.out_eq hl y).symm)
  bdd F h K hK := by
    obtain ⟨φ, hφ, hF⟩ := h
    obtain ⟨N, hN⟩ := hφ.growth
    obtain ⟨B, hB⟩ := hN 1
    rw [map_one] at hB
    obtain ⟨C, hC0, hC⟩ := integrand_le b s t N
    obtain ⟨M, hM⟩ := exists_height_le_of_isCompact hK
    have hB0 : 0 ≤ B := by simpa [AutomorphicForm.height_one] using (norm_nonneg _).trans (hB 1)
    refine ⟨C * B * M ^ N, fun y g hg => ?_⟩
    rw [hF]
    exact (hC φ B hφ hB y g).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le (hM g hg) N) (by positivity))

theorem big_mem_Sm (b : Blo S r) (t : ℝ) {φ : Sm E (r + s)} (hφ : Umg φ) : big s b.f.1 t φ.1 ∈ Sm E (r + s) := by
  obtain ⟨F, hF, -⟩ := ctOps E r s φ hφ
  rw [big, ← hF]
  exact (cls b s t).mem_Sm ⟨φ, hφ, hF⟩

private def passAlg (b : Blo S r) (s : ℕ) (t : ℝ) : Subalgebra ℂ (UC E (r + s)) where
  carrier := {u | ∀ F G : Sm E (r + s), IsCt r s F → G.1 = avg (nu E r) (pt r s t) (wt b.f.1) F.1 →
    (uC E (r + s) u G).1 = avg (nu E r) (pt r s t) (wt b.f.1) (uC E (r + s) u F).1}
  mul_mem' {u v} hu hv F G hF hG := by
    rw [map_mul]
    exact hu _ _ (hF.uC v) (hv F G hF hG)
  add_mem' {u v} hu hv F G hF hG := by
    funext g
    rw [map_add]
    change (uC E (r + s) u G).1 g + (uC E (r + s) v G).1 g = _
    rw [hu F G hF hG, hv F G hF hG, avg, avg, avg,
      ← integral_add ((cls b s t).integrable (hF.uC u) g) ((cls b s t).integrable (hF.uC v) g)]
    exact integral_congr_ae (.of_forall fun y => (add_mul _ _ _).symm)
  algebraMap_mem' c F G hF hG := by
    funext g
    rw [AlgHom.commutes]
    change c * G.1 g = _
    rw [hG, avg, avg, ← integral_const_mul]
    exact integral_congr_ae (.of_forall fun y => (mul_assoc _ _ _).symm)

theorem uC_big (b : Blo S r) (t : ℝ) {φ : Sm E (r + s)} (hφ : Umg φ) (u : UC E (r + s)) :
    (uC E (r + s) u ⟨_, big_mem_Sm b t hφ⟩).1 = big s b.f.1 t (uC E (r + s) u φ).1 := by
  obtain ⟨F, hF, -, -, hu⟩ := ctOps E r s φ hφ
  have h : ∀ X, ιC E (r + s) X ∈ passAlg b s t := fun X F G hF hG => by
    funext g
    rw [uC_ιC, lie_apply, hG]
    exact (cls b s t).lieD_avg hF X g
  have hT : (⊤ : Subalgebra ℂ (UC E (r + s))) ≤ passAlg b s t := by
    rw [← adjoin_genC]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, i, j, rfl⟩
    exact (passAlg b s t).smul_mem ((passAlg b s t).sub_mem (h _) ((passAlg b s t).smul_mem (h _) _)) _
  have := hT (x := u) trivial F ⟨_, big_mem_Sm b t hφ⟩ ⟨φ, hφ, hF⟩ (by rw [hF]; rfl)
  rw [this, hu]
  rfl

theorem big_rt (f : GA E r → ℂ) (t : ℝ) (φ : Sm E (r + s)) (h g : GA E (r + s)) :
    big s f t (rt E (r + s) h φ).1 g = big s f t φ.1 (g * h) := by
  unfold big avg
  simp only [ct_rt, mul_assoc]

end UpperTheory.ConvolutionTheory.BW.SliceClasses
