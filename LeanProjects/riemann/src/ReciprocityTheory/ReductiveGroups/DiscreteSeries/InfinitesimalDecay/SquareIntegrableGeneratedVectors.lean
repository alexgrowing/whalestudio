import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.ProjectionSquareIntegrable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.PsiForPosGelfand

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

def PmProp (ε : Fin n → Bool) (m : ℕ) {lam : Fin n → ℝ} (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V) : Prop :=
  ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ g ∈ UJset ε, ∀ idx : Fin m → Fin n × Fin n,
        ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖ *
            ∏ t, ‖g (idx t).1 (idx t).2‖ ≤
          C * NE (smE ε (rreg ε)) (m * (n - 1)) x * NE (smE ε (rreg ε)) (m * (n - 1)) y

theorem one_le_q_zero {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) : 1 ≤ S7.q0 ε := by
  unfold S7.q0; exact le_min hp hq

theorem square_integrable_generated_vectors {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (hlam : S7.IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (hth : thrStar ε < h) (hq : 1 ≤ S7.q0 ε) (hP : IsPsiFor ε lam T Ψ)
    (hv₀ : v₀ ≠ 0) :
    ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
        (Formalism.REAL.muG ε) := by
  obtain ⟨Ψ', h1, h2, h3, h4, -, h6, -, -⟩ := S7.psiAll (n := n) ε lam h T hlam hgap hq
  have hmax := hth
  unfold thrStar at hmax
  rw [max_lt_iff] at hmax
  have hsq : (0 : ℝ) ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  have hnq : (0 : ℝ) ≤ (n : ℝ) * S7.q0 ε := by positivity
  have hL2 : 8 * (n : ℝ) * S7.q0 ε < h := by nlinarith [hmax.2]
  have hw2 : 8 * (n : ℝ) * S7.q0 ε + 4 * 2 * Real.sqrt (2 * S7.q0 ε) < h := by nlinarith [hmax.2]
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, hmax.1⟩
  have hP' : IsPsiFor ε lam T Ψ' := ⟨h1, h2, h3, h4, fun μ hμ => (h6 μ hμ).2.1 hL2⟩
  have heq : ∀ g ∈ UJset ε, Ψ' g = Ψ g := puniq_psi_eq hstd hP hP' hv₀
  refine weighted_datum hstd hP hv₀ (fun μ hμ => ?_)
  refine ((h6 μ hμ).2.2 2 (by norm_num) hw2).congr (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [heq _ g.2]

theorem standard_gap_data {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (hlam : S7.IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (hth : thrStar ε < h) (hq : 1 ≤ S7.q0 ε) (hP : IsPsiFor ε lam T Ψ)
    (hv₀ : v₀ ≠ 0) :
    StdGap ε lam ∧ (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
      (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε)) ∧
      HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := by
  have hT1 : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 ≤ thrStar ε := le_max_left _ _
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, by linarith⟩
  obtain ⟨hpos, hGel⟩ := psiFor_pos_gelfand hlam hgap hth hq hP
  exact ⟨hstd, hpos, square_integrable_generated_vectors hlam hgap hth hq hP hv₀, hasGelfandChar_sigLam hstd hP hv₀ hGel⟩

theorem tensor_inner_single_coef {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) {D : Submodule ℂ H}
    (a b : Fin n) (x y : D) :
    ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ ((((Pi.single a y : Fin n → D) c) : D) : H)
        (tensGrp false σ g (fun d => ((((Pi.single b x : Fin n → D) d) : D) : H)) c) =
      (if ε a then (1 : ℂ) else -1) * (g a b * inner ℂ (y : H) (σ g (x : H))) := by
  rw [Finset.sum_eq_single a (fun c _ hc => by simp [Pi.single_eq_of_ne hc]) (by simp)]
  congr 1
  simp only [Pi.single_eq_same, tensGrp, cond_false, inner_sum, inner_smul_right]
  rw [Finset.sum_eq_single b (fun d _ hd => by simp [Pi.single_eq_of_ne hd]) (by simp)]
  simp

theorem tensor_inner_sum_eq {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) {D : Submodule ℂ H}
    (η : Fin n → H) {β : Type*} (B : Finset β) (F : β → Fin n → D) :
    ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ (η c) (tensGrp false σ g (fun d => (((∑ b ∈ B, F b) d : D) : H)) c) =
      ∑ b ∈ B, ∑ c, (if ε c then (1 : ℂ) else -1) * inner ℂ (η c) (tensGrp false σ g (fun d => ((F b d : D) : H)) c) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  simp only [tensGrp, Finset.sum_apply, Submodule.coe_sum, map_sum, Finset.smul_sum, inner_sum]
  rw [Finset.sum_comm]

theorem pmProp_zero {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V) : PmProp ε 0 T Ψ v₀ := by
  refine ⟨1, fun x _ y _ g hg idx => ?_⟩
  rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one, zero_mul, NE_zero_eq, NE_zero_eq, one_mul]
  calc ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖
      ≤ ‖((y : smD ε (rreg ε)) : L2 ε)‖ * ‖rreg ε g ((x : smD ε (rreg ε)) : L2 ε)‖ := norm_inner_le_norm _ _
    _ = _ := by rw [(rreg_isURepOn ε).2.1 g hg, mul_comm]

theorem regular_term_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (hstd : StdGap ε lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hth : thrStar ε < h) (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε))
    (hG : HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (s : Fin n) {P : Module.End ℂ (Fin n → smD ε (rreg ε))}
    (hPG : IsGKEndo false ε (rreg ε) (smE ε (rreg ε)) (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) P)
    (hPz : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      eeF false (smE ε (rreg ε)) (P f) = poleF false lam s • P f)
    (hP1 : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      eeF false (smE ε (rreg ε)) f = poleF false lam s • f → P f = f)
    (hP0 : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∀ z' : ℂ, z' ≠ poleF false lam s →
      eeF false (smE ε (rreg ε)) f = z' • f → P f = 0)
    (hPN : ∀ j : ℕ, ∃ C : ℝ, ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      NT (smE ε (rreg ε)) j (P f) ≤ C * NT (smE ε (rreg ε)) (j + (n - 1)) f)
    {T' : S7.KType ε (lowK ε (shiftF false lam s))}
    {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
    (hok : ReciprocityTheory.ChartRestriction.DS.cns_Ok ε (shiftF false lam s) T' Ψ') (m : ℕ) (IH : PmProp ε m T' Ψ' T'.w) :
    ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ g ∈ UJset ε, ∀ a b : Fin n, ∀ idx : Fin m → Fin n × Fin n,
        ‖∑ c, (if ε c then (1 : ℂ) else -1) *
            inner ℂ ((((Pi.single a y : Fin n → smD ε (rreg ε)) c) : smD ε (rreg ε)) : L2 ε)
            (tensGrp false (rreg ε) g (fun d => ((P (Pi.single b x) d : smD ε (rreg ε)) : L2 ε)) c)‖ *
          ∏ t, ‖g (idx t).1 (idx t).2‖ ≤
        C * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y := by
  obtain ⟨⟨h', hh', hth'⟩, hgap', hP', hv', hpos', hW', hG'⟩ := hok
  have := Hlam_nontrivial hstd hP hv₀
  have := Hlam_nontrivial hgap' hP' hv'
  obtain ⟨w, hw⟩ := exists_ne (0 : Hlam ε Ψ v₀)
  obtain ⟨w', hw'⟩ := exists_ne (0 : Hlam ε Ψ' T'.w)
  obtain ⟨⟨ι, hι, hιe, hιs⟩, -⟩ := cc_gk false hstd hP hv₀ hgap' hP' hv' hh hth hh' hth' hpos hpos' hW hW' hG hG'
    s rfl hw hw'
  obtain ⟨ka, q, hka, -, hqm, hT2, hT3, hT1⟩ :=
    form_cc false hstd hP hv₀ hgap' hP' hv' hW s hι hιe hιs hPG hPz hP1 hP0
  obtain ⟨K, hK⟩ := NE_q_le ε (smE ε (rreg ε)) (smE ε (rreg ε)) (tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (fun a b f hf => tensSub_stable false a b f hf) q P (n - 1) hPN ka hka (fun a b f hf => hT2 a b f hf) hT3
    (m * (n - 1))
  obtain ⟨C', hC'⟩ := IH
  refine ⟨|ka| * max C' 0 * max K 0 * max K 0, fun x hx y hy g hg a b idx => ?_⟩
  have hfx : (Pi.single b x : Fin n → smD ε (rreg ε)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := by
    rw [tset_mem]; intro c; by_cases hc : c = b
    · subst hc; simpa using hx
    · simp [Pi.single_eq_of_ne hc]
  have hfy : (Pi.single a y : Fin n → smD ε (rreg ε)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := by
    rw [tset_mem]; intro c; by_cases hc : c = a
    · subst hc; simpa using hy
    · simp [Pi.single_eq_of_ne hc]
  rw [hT1 _ hfx _ hfy g hg]
  have hidx : m * (n - 1) + (n - 1) = (m + 1) * (n - 1) := by ring
  have hX := (hqm _ hfx).1
  have hY := (hqm _ hfy).1
  have h1 := hC' _ hX _ hY g hg idx
  have h2 : NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single b x)) ≤
      max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x := by
    refine (hK _ hfx).trans ?_
    rw [NT_single, hidx]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (NE_nonneg _ _ _)
  have h3 : NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single a y)) ≤
      max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y := by
    refine (hK _ hfy).trans ?_
    rw [NT_single, hidx]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (NE_nonneg _ _ _)
  have hA := NE_nonneg (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single b x))
  have hB := NE_nonneg (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single a y))
  have hC0 : (0 : ℝ) ≤ max C' 0 := le_max_right _ _
  have hK0 : (0 : ℝ) ≤ max K 0 := le_max_right _ _
  have h4 : C' * NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single b x)) *
      NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single a y)) ≤
      max C' 0 * (max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x) *
        (max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y) := by
    calc _ ≤ max C' 0 * NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single b x)) *
          NE (smE ε (rreg ε)) (m * (n - 1)) (q (Pi.single a y)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hA) hB
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h2 hC0) h3 hB (mul_nonneg hC0 (mul_nonneg hK0 (NE_nonneg _ _ _)))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
  calc |ka| * (‖inner ℂ ((q (Pi.single a y) : smD ε (rreg ε)) : L2 ε)
          (rreg ε g ((q (Pi.single b x) : smD ε (rreg ε)) : L2 ε))‖ * ∏ t, ‖g (idx t).1 (idx t).2‖)
      ≤ |ka| * (max C' 0 * (max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x) *
        (max K 0 * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y)) :=
        mul_le_mul_of_nonneg_left (h1.trans h4) (abs_nonneg _)
    _ = _ := by ring

theorem single_mem_tensSub {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (b : Fin n) {x : smD ε (rreg ε)}
    (hx : x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) :
    (Pi.single b x : Fin n → smD ε (rreg ε)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := by
  rw [tset_mem]; intro c; by_cases hc : c = b
  · subst hc; simpa using hx
  · simp [Pi.single_eq_of_ne hc]

theorem pmProp_succ_of_gap {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) (m : ℕ)
    (IH : ∀ {lam : Fin n → ℝ}, S7.IsHCParam lam → ∀ {h : ℝ}, GapAtLeast ε lam h → thrStar ε + m < h →
      ∀ (T : S7.KType ε (lowK ε lam)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V),
        IsPsiFor ε lam T Ψ → v₀ ≠ 0 → PmProp ε m T Ψ v₀)
    {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) {h : ℝ} (hgap : GapAtLeast ε lam h)
    (hm : thrStar ε + ((m + 1 : ℕ) : ℝ) < h) {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    PmProp ε (m + 1) T Ψ v₀ := by
  have hq0 := one_le_q_zero hp hq
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  push_cast at hm
  have hth : thrStar ε < h := by linarith
  obtain ⟨hstd, hpos, hW, hG⟩ := standard_gap_data hlam hgap hth hq0 hP hv₀
  obtain ⟨P, hPG, hPz, hP1, hP0, hsum, hPN⟩ := projection_square_integrable hlam hstd hP hv₀ hW hG
  have hσ := rreg_isURepOn ε
  have hD : IsDerivedOn ε (rreg ε) (smD ε (rreg ε)) (smE ε (rreg ε)) := isDerivedOn_smE hσ
  have hsm : ∀ v : smD ε (rreg ε), IsSmoothVecU ε (rreg ε) (v : _) := fun v => (mem_smD_iff ε (rreg ε) _).1 v.2
  have hterm : ∀ s, ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ g ∈ UJset ε, ∀ a b : Fin n,
      ∀ idx : Fin m → Fin n × Fin n,
        ‖∑ c, (if ε c then (1 : ℂ) else -1) *
            inner ℂ ((((Pi.single a y : Fin n → smD ε (rreg ε)) c) : smD ε (rreg ε)) : L2 ε)
            (tensGrp false (rreg ε) g (fun d => ((P s (Pi.single b x) d : smD ε (rreg ε)) : L2 ε)) c)‖ *
          ∏ t, ‖g (idx t).1 (idx t).2‖ ≤
        C * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y := by
    intro s
    by_cases hs : S7.IsHCParam (shiftF false lam s)
    · have hg' := ReciprocityTheory.ChartRestriction.DS.cns_shift_gap false hgap s
      obtain ⟨T', Ψ', hok⟩ := ReciprocityTheory.ChartRestriction.DS.cns_data' hq0 hs hg' (by linarith)
      exact regular_term_bound hP hv₀ hstd hgap hth hpos hW hG s (hPG s) (hPz s) (hP1 s) (hP0 s) (hPN s) hok m
        (IH hs hg' (by linarith) T' Ψ' T'.w hok.2.2.1 hok.2.2.2.1)
    · refine ⟨0, fun x hx y hy g hg a b idx => ?_⟩
      have hfx := single_mem_tensSub b hx
      have h0 : P s (Pi.single b x) = 0 :=
        cc_gk_singular false hσ hD hsm hstd (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
          (datumV_kStable hP v₀) hW hG s (ReciprocityTheory.ChartRestriction.DS.cns_sing false hlam hs) _ ((hPG s).1 _ hfx)
          (hPz s _ hfx)
      rw [h0]
      simp [tensGrp]
  choose Cs hCs using hterm
  refine ⟨∑ s, Cs s, fun x hx y hy g hg idx => ?_⟩
  have hfx := single_mem_tensSub (idx 0).2 hx
  have key := tensor_inner_single_coef (ε := ε) (rreg ε) g (idx 0).1 (idx 0).2 x y
  rw [hsum _ hfx, tensor_inner_sum_eq] at key
  have hsgn : ‖(if ε (idx 0).1 then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp
  rw [Fin.prod_univ_succ]
  calc ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖ *
        (‖g (idx 0).1 (idx 0).2‖ * ∏ t : Fin m, ‖g (idx t.succ).1 (idx t.succ).2‖)
      = ‖(if ε (idx 0).1 then (1 : ℂ) else -1) * (g (idx 0).1 (idx 0).2 *
          inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε)))‖ *
          ∏ t : Fin m, ‖g (idx t.succ).1 (idx t.succ).2‖ := by
        rw [norm_mul, norm_mul, hsgn]; ring
    _ ≤ (∑ s, ‖∑ c, (if ε c then (1 : ℂ) else -1) *
            inner ℂ ((((Pi.single (idx 0).1 y : Fin n → smD ε (rreg ε)) c) : smD ε (rreg ε)) : L2 ε)
            (tensGrp false (rreg ε) g
              (fun d => ((P s (Pi.single (idx 0).2 x) d : smD ε (rreg ε)) : L2 ε)) c)‖) *
          ∏ t : Fin m, ‖g (idx t.succ).1 (idx t.succ).2‖ := by
        rw [← key]
        exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (prod_nonneg fun _ _ => norm_nonneg _)
    _ = ∑ s, ‖∑ c, (if ε c then (1 : ℂ) else -1) *
            inner ℂ ((((Pi.single (idx 0).1 y : Fin n → smD ε (rreg ε)) c) : smD ε (rreg ε)) : L2 ε)
            (tensGrp false (rreg ε) g
              (fun d => ((P s (Pi.single (idx 0).2 x) d : smD ε (rreg ε)) : L2 ε)) c)‖ *
          ∏ t : Fin m, ‖g (idx t.succ).1 (idx t.succ).2‖ := Finset.sum_mul _ _ _
    _ ≤ ∑ s, Cs s * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) x * NE (smE ε (rreg ε)) ((m + 1) * (n - 1)) y :=
        Finset.sum_le_sum fun s _ => hCs s x hx y hy g hg (idx 0).1 (idx 0).2 (fun t => idx t.succ)
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

theorem pmProp_of_gap {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) (m : ℕ) :
    ∀ {lam : Fin n → ℝ}, S7.IsHCParam lam → ∀ {h : ℝ}, GapAtLeast ε lam h → thrStar ε + m < h →
      ∀ (T : S7.KType ε (lowK ε lam)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (v₀ : T.V),
        IsPsiFor ε lam T Ψ → v₀ ≠ 0 → PmProp ε m T Ψ v₀ := by
  induction m with
  | zero => intro lam _ h _ _ T Ψ v₀ _ _; exact pmProp_zero T Ψ v₀
  | succ m ih => intro lam hlam h hgap hm T Ψ v₀ hP hv₀; exact pmProp_succ_of_gap hp hq m ih hlam hgap hm hP hv₀

end ReciprocityTheory.ChartRestriction.DS.DecInf
