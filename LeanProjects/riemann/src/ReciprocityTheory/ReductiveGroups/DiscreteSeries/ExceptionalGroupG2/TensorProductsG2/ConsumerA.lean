import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CcARatioZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Decomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Weighted
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Transported
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PsiPos
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeExpK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import Formalism.PeriodIntegrals.ZuckTensor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

theorem cns_data {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam)
    {h : ℝ} (hh : GapAtLeast ε lam h) (hth : thrS ε < h) :
    ∃ (T : S7.KType ε (lowK ε lam)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)),
      StdGap ε lam ∧ IsPsiFor ε lam T Ψ ∧ T.w ≠ 0 ∧
      (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
      (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε)) ∧
      HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)) := by
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨Ψ, h1, h2, h3, h4, -, h6, h7, h8⟩ := S7.psiAll ε lam h T hlam hh hq
  have hmax := hth
  unfold thrS at hmax
  rw [max_lt_iff] at hmax
  have hsq : (0 : ℝ) ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  have hnq : (0 : ℝ) ≤ (n : ℝ) * S7.q0 ε := by positivity
  have hL2 : 8 * (n : ℝ) * S7.q0 ε < h := by nlinarith [hmax.2]
  have hw2 : 8 * (n : ℝ) * S7.q0 ε + 4 * 2 * Real.sqrt (2 * S7.q0 ε) < h := by nlinarith [hmax.2]
  have hgap : StdGap ε lam := ⟨hlam.1, h, hh, hmax.1⟩
  have hP : IsPsiFor ε lam T Ψ := ⟨h1, h2, h3, h4, fun μ hμ => (h6 μ hμ).2.1 hL2⟩
  have hv₀ : T.w ≠ 0 := by
    intro h0
    have := T.w_norm
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨m, hm⟩ := S7.exists_mu hlam
  refine ⟨T, Ψ, hgap, hP, hv₀, psi_exp_isPositive T Ψ m hm (h8 m hm), ?_, hasGelfandChar_sigLam hgap hP hv₀ h7⟩
  exact weighted_datum hgap hP hv₀ (fun μ hμ => (h6 μ hμ).2.2 2 (by norm_num) hw2)

end ReciprocityTheory.ChartRestriction.DS.G2

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

section Kfin

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem cns_gen_mem_Hlam {y : smD ε (rreg ε)} (hy : y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) :
    (y : L2 ε) ∈ Hlam ε Ψ v₀ :=
  Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hy)

theorem cns_kfin (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {y : smD ε (rreg ε)}
    (hy : y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (x : Hlam ε Ψ v₀) (hx : (x : L2 ε) = y) :
    PI.UpqRep.IsKFin ε (sigLam ε Ψ v₀) x := by
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hE := hD.glRep
  have hV := datumV_isKIrrHW hP hv₀
  rw [genSub_eq_iSup_layer hE hV.2.1] at hy
  have hdir : Directed (· ≤ ·) (fun k => layer ε (smE ε (rreg ε)) (datumV ε Ψ v₀) k) :=
    fun i j => ⟨max i j, layer_mono (le_max_left i j), layer_mono (le_max_right i j)⟩
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hy
  set S0 := layer ε (smE ε (rreg ε)) (datumV ε Ψ v₀) k with hS0
  haveI hS0f : FiniteDimensional ℂ S0 := finiteDimensional_layer hV.1 k
  have hS0K := kStable_of_isKStableSub hσ hD S0 hS0f (layer_kStable hE hV.2.1 k)
  set S : Submodule ℂ (Hlam ε Ψ v₀) := (S0.map (smD ε (rreg ε)).subtype).comap (Hlam ε Ψ v₀).subtype with hS
  have hSf : FiniteDimensional ℂ S := by
    have hinj : Function.Injective (Hlam ε Ψ v₀).subtype := Subtype.val_injective
    have hle : S.map (Hlam ε Ψ v₀).subtype ≤ S0.map (smD ε (rreg ε)).subtype := by
      rintro _ ⟨a, ha, rfl⟩
      exact ha
    haveI : FiniteDimensional ℂ (S0.map (smD ε (rreg ε)).subtype) := Module.Finite.map _ _
    haveI := Submodule.finiteDimensional_of_le hle
    exact (Submodule.equivMapOfInjective _ hinj S).symm.finiteDimensional
  refine ⟨S, hSf, ⟨y, hk, hx.symm⟩, ?_⟩
  intro g hg v hv
  obtain ⟨u, hu, huv⟩ := hv
  have hgU : g ∈ UJset ε := cf_kset_sub hg
  obtain ⟨w, hw, hwe⟩ := hS0K g hg u hu
  refine ⟨w, hw, ?_⟩
  show (w : L2 ε) = ((sigLam ε Ψ v₀ g v : Hlam ε Ψ v₀) : L2 ε)
  rw [sigLam_coe hgap hP hv₀ hgU, hwe]
  simp only [Submodule.coe_subtype] at huv
  rw [huv]

end Kfin

section Term

variable {ε : Fin n → Bool}

theorem cns_term (dual : Bool) {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {T' : S7.KType ε (lowK ε lam')} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)} {v₀ : T.V} {v₀' : T'.V}
    (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    {h h' : ℝ} (hh : GapAtLeast ε lam h) (hth : thrS ε < h) (hh' : GapAtLeast ε lam' h') (hth' : thrS ε < h')
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (hW : (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε)))
    (hW' : (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε)))
    (hG : HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hG' : HasGelfandChar (smE ε (rreg ε)) lam' (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')))
    (s : Fin n) (hlam' : lam' = shiftF dual lam s)
    {f : Fin n → smD ε (rreg ε)} (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (he : eeF dual (smE ε (rreg ε)) f = poleF dual lam s • f)
    {η : Fin n → smD ε (rreg ε)} (hη : η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))) :
    ∃ x z : Hlam ε Ψ' v₀', PI.UpqRep.IsKFin ε (sigLam ε Ψ' v₀') x ∧ PI.UpqRep.IsKFin ε (sigLam ε Ψ' v₀') z ∧
      ∀ g ∈ UJset ε, ∑ c, inner ℂ ((η c : smD ε (rreg ε)) : L2 ε)
          (tensGrp dual (rreg ε) g (fun d => ((f d : smD ε (rreg ε)) : L2 ε)) c) =
        inner ℂ z (sigLam ε Ψ' v₀' g x) := by
  haveI := Hlam_nontrivial hgap hP hv₀
  haveI := Hlam_nontrivial hgap' hP' hv₀'
  obtain ⟨w, hw⟩ := exists_ne (0 : Hlam ε Ψ v₀)
  obtain ⟨w', hw'⟩ := exists_ne (0 : Hlam ε Ψ' v₀')
  obtain ⟨⟨ι, hι, -, hsurj⟩, -⟩ := cc_gk dual hgap hP hv₀ hgap' hP' hv₀' hh hth hh' hth' hpos hpos' hW hW' hG hG'
    s hlam' hw hw'
  obtain ⟨x', hx', rfl⟩ := hsurj f hf he
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  obtain ⟨z, hz, hzeq⟩ := (coef_of_emb dual hσ hD hgap (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
    (datumV_kStable hP v₀) hgap' (datumV_isKIrrHW hP' hv₀') (datumV_casimir hP' v₀')
    (datumV_kStable hP' v₀') hι).1 η hη x' hx'
  refine ⟨⟨(x' : L2 ε), cns_gen_mem_Hlam hx'⟩, ⟨(z : L2 ε), cns_gen_mem_Hlam hz⟩,
    cns_kfin hgap' hP' hv₀' hx' _ rfl, cns_kfin hgap' hP' hv₀' hz _ rfl, fun g hg => ?_⟩
  rw [hzeq g hg, Submodule.coe_inner, sigLam_coe hgap' hP' hv₀' hg]

end Term

end ReciprocityTheory.ChartRestriction.DS.G2

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

theorem cns_single_bd (s x : Fin n) : 0 ≤ (Pi.single s (1 : ℝ) : Fin n → ℝ) x ∧
    (Pi.single s (1 : ℝ) : Fin n → ℝ) x ≤ 1 := by
  rw [Pi.single_apply]
  split_ifs <;> norm_num

theorem cns_single_01 (s x : Fin n) : (Pi.single s (1 : ℝ) : Fin n → ℝ) x = 0 ∨
    (Pi.single s (1 : ℝ) : Fin n → ℝ) x = 1 := by
  rw [Pi.single_apply]
  split_ifs <;> simp

theorem cns_shift_gap (dual : Bool) {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hh : GapAtLeast ε μ h)
    (s : Fin n) : GapAtLeast ε (shiftF dual μ s) (h - 1) := by
  intro a b hab
  have h1 := hh a b hab
  obtain ⟨ha0, ha1⟩ := cns_single_bd s a
  obtain ⟨hb0, hb1⟩ := cns_single_bd s b
  have key : ∀ Y : ℝ, |Y| ≤ 1 → h - 1 ≤ |(μ a - μ b) + Y| := by
    intro Y hY
    have h2 := abs_sub_abs_le_abs_sub (μ a - μ b) (-Y)
    rw [abs_neg, sub_neg_eq_add] at h2
    linarith
  cases dual
  · have e : shiftF false μ s a - shiftF false μ s b =
        (μ a - μ b) + ((Pi.single s (1 : ℝ) : Fin n → ℝ) a - (Pi.single s (1 : ℝ) : Fin n → ℝ) b) := by
      simp only [shiftF, cond_false, Pi.add_apply]
      ring
    rw [e]
    exact key _ (abs_le.mpr ⟨by linarith, by linarith⟩)
  · have e : shiftF true μ s a - shiftF true μ s b =
        (μ a - μ b) + -((Pi.single s (1 : ℝ) : Fin n → ℝ) a - (Pi.single s (1 : ℝ) : Fin n → ℝ) b) := by
      simp only [shiftF, cond_true, Pi.sub_apply]
      ring
    rw [e]
    exact key _ (abs_le.mpr ⟨by linarith, by linarith⟩)

theorem cns_sing (dual : Bool) {μ : Fin n → ℝ} (hμ : S7.IsHCParam μ) {s : Fin n}
    (hns : ¬ S7.IsHCParam (shiftF dual μ s)) : ¬ Function.Injective (shiftF dual μ s) := by
  intro hinj
  apply hns
  obtain ⟨hanti, hint⟩ := hμ
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · obtain ⟨ma, hma⟩ := hint a
    obtain ⟨mb, hmb⟩ := hint b
    have hlt : μ b < μ a := hanti hab
    have hgap : 1 ≤ μ a - μ b := by
      have e : μ a - μ b = ((ma - mb : ℤ) : ℝ) := by push_cast; linarith
      have hpos : (0 : ℤ) < ma - mb := by
        have h0 : (0 : ℝ) < ((ma - mb : ℤ) : ℝ) := by rw [← e]; linarith
        exact_mod_cast h0
      rw [e]
      exact_mod_cast (show (1 : ℤ) ≤ ma - mb by omega)
    have hne : shiftF dual μ s a ≠ shiftF dual μ s b := fun h => (ne_of_lt hab) (hinj h)
    obtain ⟨ha0, ha1⟩ := cns_single_bd s a
    obtain ⟨hb0, hb1⟩ := cns_single_bd s b
    have hle : shiftF dual μ s b ≤ shiftF dual μ s a := by
      cases dual <;> simp only [shiftF, cond_false, cond_true, Pi.add_apply, Pi.sub_apply] <;> linarith
    exact lt_of_le_of_ne hle (Ne.symm hne)
  · obtain ⟨m, hm⟩ := hint a
    rcases cns_single_01 s a with h0 | h1
    · refine ⟨m, ?_⟩
      cases dual <;> simp only [shiftF, cond_false, cond_true, Pi.add_apply, Pi.sub_apply, h0] <;> linarith
    · cases dual
      · refine ⟨m + 1, ?_⟩
        simp only [shiftF, cond_false, Pi.add_apply, h1]
        push_cast
        linarith
      · refine ⟨m - 1, ?_⟩
        simp only [shiftF, cond_true, Pi.sub_apply, h1]
        push_cast
        linarith

theorem cns_shift_inj (dual : Bool) (μ : Fin n → ℝ) {s s' : Fin n} (h : shiftF dual μ s = shiftF dual μ s') :
    s = s' := by
  by_contra hne
  have h1 := congrFun h s
  cases dual <;> simp [shiftF, Pi.single_apply, hne, Ne.symm hne] at h1

theorem cns_coefV {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (a b : H) (x y : Fin n → ℂ) :
    inner ℂ b (σ g a) * (star y ⬝ᵥ (g *ᵥ x)) =
      ∑ c, inner ℂ (y c • b) (tensGrp false σ g (fun d => x d • a) c) := by
  simp only [tensGrp, cond_false, map_smul, inner_sum, inner_smul_left, inner_smul_right, dotProduct,
    Matrix.mulVec, Finset.mul_sum, Finset.sum_mul, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
  ring

theorem cns_coefVd {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (a b : H) (x y : Fin n → ℂ) :
    inner ℂ b (σ g a) * (star y ⬝ᵥ (g⁻¹ *ᵥ x)) =
      ∑ c, inner ℂ (star (x c) • b) (tensGrp true σ g (fun d => star (y d) • a) c) := by
  simp only [tensGrp, cond_true, map_smul, inner_sum, inner_smul_left, inner_smul_right, dotProduct,
    Matrix.mulVec, Finset.mul_sum, Finset.sum_mul, Pi.star_apply, Complex.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
  ring

theorem cns_single_coef (g : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) :
    star (Pi.single c (1 : ℂ) : Fin n → ℂ) ⬝ᵥ (g *ᵥ Pi.single d 1) = g c d := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, Pi.star_apply]

theorem cns_expandV {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (f F : Fin n → H) :
    ∑ c, inner ℂ (f c) (tensGrp false σ g F c) = ∑ p : Fin n × Fin n, inner ℂ (f p.1) (σ g (F p.2)) *
      (star (Pi.single p.1 (1 : ℂ) : Fin n → ℂ) ⬝ᵥ (g *ᵥ Pi.single p.2 1)) := by
  simp only [cns_single_coef, tensGrp, cond_false, inner_sum, inner_smul_right]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
  ring

theorem cns_expandVd {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (f F : Fin n → H) :
    ∑ c, inner ℂ (f c) (tensGrp true σ g F c) = ∑ p : Fin n × Fin n, inner ℂ (f p.1) (σ g (F p.2)) *
      (star (Pi.single p.2 (1 : ℂ) : Fin n → ℂ) ⬝ᵥ (g⁻¹ *ᵥ Pi.single p.1 1)) := by
  simp only [cns_single_coef, tensGrp, cond_true, inner_sum, inner_smul_right]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
  ring

theorem cns_tens_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (dual : Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) {D : Submodule ℂ H}
    (η : Fin n → H) {β : Type*} (B : Finset β) (F : β → Fin n → D) :
    ∑ c, inner ℂ (η c) (tensGrp dual σ g (fun d => (((∑ b ∈ B, F b) d : D) : H)) c) =
      ∑ b ∈ B, ∑ c, inner ℂ (η c) (tensGrp dual σ g (fun d => ((F b d : D) : H)) c) := by
  simp only [tensGrp, Finset.sum_apply, Submodule.coe_sum, map_sum, Finset.smul_sum, inner_sum]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]
  exact Finset.sum_comm

theorem cns_kfin_map {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] {ε : Fin n → Bool} {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)}
    {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (hU : ∀ g ∈ UJset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x)) {x : H₁} (hx : PI.UpqRep.IsKFin ε σ₁ x) :
    PI.UpqRep.IsKFin ε σ₂ (U x) := by
  obtain ⟨S, hfin, hxS, hst⟩ := hx
  haveI := hfin
  have hK : ∀ g ∈ PI.UpqRep.Kset ε, g ∈ UJset ε := by
    rintro g ⟨hu, hc⟩
    show inUJ ε g
    unfold inUJ
    have h1 : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
    rw [Matrix.star_eq_conjTranspose] at h1
    have hJ : ReciprocityTheory.ChartRestriction.DS.Jm ε = PI.UpqRep.Jm ε := rfl
    rw [hJ, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨S.map U.toLinearEquiv.toLinearMap, inferInstance, Submodule.mem_map_of_mem hxS, ?_⟩
  rintro g hg _ ⟨v, hv, rfl⟩
  refine ⟨σ₁ g v, hst g hg v hv, ?_⟩
  simp [hU g (hK g hg) v]

theorem cns_symm_intertw {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] {ε : Fin n → Bool} {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)}
    {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} (U : H₁ ≃ₗᵢ[ℂ] H₂)
    (hU : ∀ g ∈ UJset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x)) :
    ∀ g ∈ UJset ε, ∀ y, U.symm (σ₂ g y) = σ₁ g (U.symm y) := by
  intro g hg y
  apply U.injective
  rw [LinearIsometryEquiv.apply_symm_apply, hU g hg, LinearIsometryEquiv.apply_symm_apply]

section abelian₂

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem cns_kfin_gen (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {x : Hlam ε Ψ v₀}
    (hx : PI.UpqRep.IsKFin ε (sigLam ε Ψ v₀) x) :
    ∃ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), (y : L2 ε) = x := by
  obtain ⟨S, hSf, hxS, hSK⟩ := hx
  have := sigLam_kfin hgap hP hv₀ S hSf hSK hxS
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 this)
  exact ⟨y, hy, hyx⟩

theorem cns_inner_tr (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (U : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ x, U (sigLam ε Ψ v₀ g x) = σ g (U x))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (a b : Hlam ε Ψ v₀) :
    inner ℂ (U b) (σ g (U a)) = inner ℂ (b : L2 ε) (rreg ε g (a : L2 ε)) := by
  rw [← hU g hg a, LinearIsometryEquiv.inner_map_map]
  simp only [sigLam, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left b _

end abelian₂

end ReciprocityTheory.ChartRestriction.DS.G2
