import Formalism.HermitianCurvature.StatementTBB
import Formalism.FormalDegreeBessel.FinalG

namespace Formalism.FourierDecayAlt.P.TBBx2

open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal

noncomputable section

open Classical in
theorem choose_dite_congr {α E : Type*} [Zero E] (P Q : α → Prop) (hPQ : P = Q) (f g : α → E)
    [Decidable (∃ θ, P θ)] [Decidable (∃ θ, Q θ)]
    (hfg : ∀ θ, P θ → f θ = g θ) :
    (if h : ∃ θ, P θ then f h.choose else 0) = (if h : ∃ θ, Q θ then g h.choose else 0) := by
  subst hPQ
  split_ifs with h1 <;> first | rfl | exact hfg _ h1.choose_spec

open Classical in
theorem orbJ_congr {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Ds : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (μR : Measure (Mt k r)) (F G : B.Mat k r → (Wq →L[ℂ] Wp))
    (hae : ∀ᵐ q ∂Ds.μSS, D.orbIntegrand Ds γ F q = D.orbIntegrand Ds γ G q) :
    D.orbJ Ds γ μR F = D.orbJ Ds γ μR G := by
  unfold D.orbJ
  exact choose_dite_congr
    (fun θ => D.IsNormCut Ds γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Ds γ F q) Ds.μSS)
    (fun θ => D.IsNormCut Ds γ μR θ ∧ Integrable (fun q => θ q • D.orbIntegrand Ds γ G q) Ds.μSS)
    (funext fun θ => propext (and_congr_right fun _ =>
      integrable_congr (hae.mono fun q hq => by simp only [hq])))
    (fun θ => ∫ q, θ q • D.orbIntegrand Ds γ F q ∂Ds.μSS)
    (fun θ => ∫ q, θ q • D.orbIntegrand Ds γ G q ∂Ds.μSS)
    (fun θ _ => integral_congr_ae (hae.mono fun q hq => by simp only [hq]))

theorem one_mem_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
  simp only [UWset, Set.mem_setOf_eq]
  refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  simp only [UH, Set.mem_setOf_eq, Matrix.conjTranspose_one, one_mul, mul_one]

theorem Gf_sgs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Ds : B.RealPlaceData k r Wp Wq) (q : B.SS k r)
    (hq : Ds.inSS q) (g : B.Mat k r) :
    Gf k r Ds.z Ds.z' (B.sgs q g) = Gf k r Ds.z Ds.z' g := by
  obtain ⟨hh, hn, hh', hn'⟩ := hq
  have SG := sGroup k r Ds.z Ds.z_mem
  have SG' := sGroup k r Ds.z' Ds.z'_mem
  have hS1 : Matrix.of q.1.1 ∈ Sset k r Ds.z := ⟨_, hh, 1, (nSubgroup k r).1, by simp⟩
  have hS2 : Matrix.of q.1.2 ∈ Sset k r Ds.z := ⟨1, one_mem_UW _ _ _, _, hn, by simp⟩
  have hS3 : Matrix.of q.2.1 ∈ Sset k r Ds.z' := ⟨_, hh', 1, (nSubgroup k r).1, by simp⟩
  have hS4 : Matrix.of q.2.2 ∈ Sset k r Ds.z' := ⟨1, one_mem_UW _ _ _, _, hn', by simp⟩
  have hs : (Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ ∈ Sset k r Ds.z :=
    SG.2.1 _ (SG.2.2 _ hS1) _ (SG.2.2 _ hS2)
  have hs' : Matrix.of q.2.2 * Matrix.of q.2.1 ∈ Sset k r Ds.z' := SG'.2.1 _ hS4 _ hS3
  have e : B.sgs q g = ((Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹) * g *
      (Matrix.of q.2.2 * Matrix.of q.2.1) := by
    unfold B.sgs; simp only [mul_assoc]
  rw [e]
  exact gInv k r Ds.z Ds.z' Ds.z_mem Ds.z'_mem _ hs _ hs' g

theorem ae_inSS {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Ds : B.RealPlaceData k r Wp Wq) :
    ∀ᵐ q ∂Ds.μSS, Ds.inSS q := by
  have key : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
      (P : α → Prop), (∀ᵐ x ∂μ, P x) → ∀ᵐ p ∂(μ.prod ν), P p.1 := by
    intro α β _ _ μ ν P h
    rw [ae_iff] at h ⊢
    refine le_antisymm ?_ zero_le
    calc (μ.prod ν) {p | ¬P p.1} = (μ.prod ν) ({x | ¬P x} ×ˢ Set.univ) := by
          congr 1
          ext p
          simp
      _ ≤ μ {x | ¬P x} * ν Set.univ := Measure.prod_prod_le _ _
      _ = 0 := by rw [h, zero_mul]
  have key2 : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
      (P : β → Prop), (∀ᵐ y ∂ν, P y) → ∀ᵐ p ∂(μ.prod ν), P p.2 := by
    intro α β _ _ μ ν P h
    rw [ae_iff] at h ⊢
    refine le_antisymm ?_ zero_le
    calc (μ.prod ν) {p | ¬P p.2} = (μ.prod ν) (Set.univ ×ˢ {y | ¬P y}) := by
          congr 1
          ext p
          simp
      _ ≤ μ Set.univ * ν {y | ¬P y} := Measure.prod_prod_le _ _
      _ = 0 := by rw [h, mul_zero]
  have h1 : ∀ᵐ x ∂Ds.μW, Matrix.of x ∈ UWset k r Ds.z := ae_iff.mpr Ds.haarW.conc
  have h2 : ∀ᵐ x ∂Ds.μN, Matrix.of x ∈ Nset k r := ae_iff.mpr Ds.haarN.conc
  have h3 : ∀ᵐ x ∂Ds.μW', Matrix.of x ∈ UWset k r Ds.z' := ae_iff.mpr Ds.haarW'.conc
  show ∀ᵐ q ∂((Ds.μW.prod Ds.μN).prod (Ds.μW'.prod Ds.μN)), Ds.inSS q
  filter_upwards [key _ _ _ (key _ _ _ h1), key _ _ _ (key2 _ _ _ h2), key2 _ _ _ (key _ _ _ h3),
    key2 _ _ _ (key2 _ _ _ h2)] with q a b c d
  exact And.intro a (And.intro b (And.intro c d))

theorem Gf_of_Zhat {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (pt : C.LPt)
    (h : Zhat k r z z' g = D.ptMatN pt (r + 1)) :
    Gf k r z z' g = D.ptG (Tz k r z * Tz k r z') r pt := by
  have e1 : Dmin k r z z' g (Fin.last (r + 1)) = (D.ptMatN pt (r + 1)).det := by
    unfold Dmin
    rw [h]
    try rfl
  have e2 : Dmin k r z z' g ⟨r, by omega⟩ = (D.ptMatN pt r).det := by
    unfold Dmin
    rw [h]
    try rfl
  unfold Gf D.ptG
  rw [e1, e2]

end

end Formalism.FourierDecayAlt.P.TBBx2

open Formalism.FourierDecayAlt in
theorem Formalism.FourierDecayAlt.P.vector_truncation_all_places : TBB.VecCutAll := by
  intro Wp Wq _ _ _ _ _ _ P p χ F hχ ε hε γ hγ hG
  unfold KB.Pl.V D.vecV
  split_ifs with h h'
  · apply Formalism.FourierDecayAlt.P.TBBx2.orbJ_congr
    filter_upwards [Formalism.FourierDecayAlt.P.TBBx2.ae_inSS p.T.base] with q hq
    have hχ1 : χ (Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' (B.sgs q h'.choose) / ε) = 1 := by
      apply hχ.2.2
      rw [Formalism.FourierDecayAlt.P.TBBx2.Gf_sgs p.T.base q hq h'.choose,
        Formalism.FourierDecayAlt.P.TBBx2.Gf_of_Zhat _ _ _ γ h'.choose_spec.2.1, le_div_iff₀ hε, one_mul]
      exact hG
    simp only [D.orbIntegrand, B.rho, D.cutF, hχ1, Complex.ofReal_one, one_smul]
  all_goals rfl

namespace Formalism.FourierDecayAlt.P.TBBx2

open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal

noncomputable section

theorem finite_words {α : Type*} (A : Set α) (hA : A.Finite) (N : ℕ) :
    {w : List α | w.length ≤ N ∧ ∀ l ∈ w, l ∈ A}.Finite := by
  have : Finite A := hA.to_subtype
  refine ((List.finite_length_le A N).image (List.map Subtype.val)).subset ?_
  rintro w ⟨hw, hwA⟩
  refine ⟨w.attach.map (fun x => (⟨x.1, hwA x.1 x.2⟩ : A)), ?_, ?_⟩
  · simpa using hw
  · simp

section one

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem RR_top (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : C.LPt)
    (hγ : D.IsLocPt γ (P.r + 1)) :
    p.RR G (P.r + 1) [] γ γ = B.hsInner (p.V G γ) (p.V G γ) := by
  have h1 : ¬ (P.r + 1 ≤ P.r) := by omega
  unfold KB.Pl.RR KB.Pl.V D.RRplace
  rw [dif_pos (And.intro hγ hγ), dif_neg h1, if_pos rfl, if_pos rfl]

theorem Ew_nil (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ) (γ : C.LPt) :
    TBB.Ew p nn G i [] γ = TBB.Ew p (fun _ => 1) G i [] γ := by
  simp only [TBB.Ew, TBB.NP, TBB.normC, List.map_nil, List.prod_nil]

theorem Ew_cut (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hV : TBB.VecCutAt p χ F) (ε : ℝ) (hε : 0 < ε) (γ : C.LPt) (hγ : D.IsLocPt γ (P.r + 1))
    (hG : ε ≤ TBB.Gp p γ) :
    TBB.Ew p nn (D.cutF p.T.base χ F ε) (P.r + 1) [] γ = TBB.Ew p nn F (P.r + 1) [] γ := by
  unfold TBB.Ew TBB.NP
  rw [RR_top p (D.cutF p.T.base χ F ε) γ hγ, RR_top p F γ hγ, hV ε hε γ hγ hG]

end one

end

end Formalism.FourierDecayAlt.P.TBBx2

open Formalism.FourierDecayAlt Filter Topology in
theorem Formalism.FourierDecayAlt.P.point_bound_of_corollary_s : TBB.PtBoundOfCorS := by
  intro Wp Wq _ _ _ _ _ _ P p nn χ F Y Λ K N C₂ κ₀ hC₂ hκ hnn hCorS hV hLim γ hγ hG
  obtain ⟨ε₀, hε₀, hCS⟩ := hCorS
  have hc0 : 0 ≤ (C₂ * Λ ^ 2) ^ (P.r + 1) := pow_nonneg (mul_nonneg hC₂ (sq_nonneg _)) _
  have hSfin : ({w | TBB.AdmW P p.l0 Y w ∧ w.length ≤ N} : Set (List C.Letter)).Finite := by
    have hA : ((fun y => ((true, y) : C.Letter)) '' (Y : Set ℝ) ∪
        (fun y => ((false, y + 1) : C.Letter)) '' (Y : Set ℝ)).Finite :=
      (Y.finite_toSet.image _).union (Y.finite_toSet.image _)
    refine (Formalism.FourierDecayAlt.P.TBBx2.finite_words _ hA N).subset ?_
    rintro w ⟨⟨_, hw⟩, hlen⟩
    refine ⟨hlen, fun l hl => ?_⟩
    obtain ⟨y, hy, h | h⟩ := hw l hl
    · exact Or.inl ⟨y, hy, h.symm⟩
    · exact Or.inr ⟨y, hy, h.symm⟩
  have hδ : 0 < min ε₀ (TBB.Gp p γ) := lt_min hε₀ hG
  have hclaim : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ w ∈ ({w | TBB.AdmW P p.l0 Y w ∧ w.length ≤ N} : Set (List C.Letter)), TBB.Ew p (fun _ => 1) F (P.r + 1) [] γ ≤ (C₂ * Λ ^ 2) ^ (P.r + 1) * TBB.Ew p nn (D.cutF p.T.base χ F ε) 0 w [] := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with ε h1 h2
    have h1' : 0 < ε := h1
    have h2' : ε < min ε₀ (TBB.Gp p γ) := h2
    obtain ⟨w', hext, hle⟩ := hCS ε h1' (le_of_lt (lt_of_lt_of_le h2' (min_le_left _ _))) γ hγ
    refine ⟨w', And.intro (And.intro hext.1 ?_) hext.2.1, ?_⟩
    · obtain ⟨L, hL, -, hLl⟩ := hext.2.2
      rw [hL, List.append_nil]
      exact hLl
    · rw [Formalism.FourierDecayAlt.P.TBBx2.Ew_cut p nn χ F hV ε h1' γ hγ
        (le_of_lt (lt_of_lt_of_le h2' (min_le_right _ _)))] at hle
      rw [Formalism.FourierDecayAlt.P.TBBx2.Ew_nil p nn F (P.r + 1) γ] at hle
      exact hle
  have hfreq : ∃ w ∈ ({w | TBB.AdmW P p.l0 Y w ∧ w.length ≤ N} : Set (List C.Letter)), ∃ᶠ ε in 𝓝[>] (0 : ℝ), TBB.Ew p (fun _ => 1) F (P.r + 1) [] γ ≤ (C₂ * Λ ^ 2) ^ (P.r + 1) * TBB.Ew p nn (D.cutF p.T.base χ F ε) 0 w [] := by
    by_contra hcon
    push_neg at hcon
    have hall := (Filter.eventually_all_finite hSfin).mpr hcon
    obtain ⟨ε, ⟨w, hw, hle⟩, hall'⟩ := (hclaim.and hall).exists
    first
      | exact absurd hle (not_le.mpr (hall' w hw))
      | exact hall' w hw hle
  obtain ⟨w, hw, hfw⟩ := hfreq
  have hlim := hLim w hw.1 hw.2
  rcases eq_or_lt_of_le hc0 with hc | hc
  · obtain ⟨ε, hε⟩ := hfw.exists
    rw [← hc, zero_mul] at hε
    rw [ENNReal.ofReal_of_nonpos hε]
    exact zero_le
  · have hcne : (C₂ * Λ ^ 2) ^ (P.r + 1) ≠ 0 := hc.ne'
    have h3 : ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] γ / (C₂ * Λ ^ 2) ^ (P.r + 1)) ≤
        Filter.limsup (fun ε : ℝ => ENNReal.ofReal (TBB.Ew p nn (D.cutF p.T.base χ F ε) 0 w [])) (𝓝[>] 0) := by
      apply Filter.le_limsup_of_frequently_le'
      refine hfw.mono fun ε hε => ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ hc]
      linarith
    calc ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] γ) = ENNReal.ofReal ((C₂ * Λ ^ 2) ^ (P.r + 1)) * ENNReal.ofReal (TBB.Ew p (fun _ => 1) F (P.r + 1) [] γ / (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
          rw [← ENNReal.ofReal_mul hc0]
          congr 1
          field_simp
      _ ≤ ENNReal.ofReal ((C₂ * Λ ^ 2) ^ (P.r + 1)) * (ENNReal.ofReal κ₀ * TBB.jN2 p F) := by
          gcongr
          exact h3.trans hlim
      _ = ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) * TBB.jN2 p F := by
          rw [ENNReal.ofReal_mul hκ.le]
          ring

namespace Formalism.FourierDecayAlt.P.TBBx2.Tri

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal

noncomputable section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

lemma hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  ext i
  simp [B.hsVec]

lemma hsVec_add (A A' : Wq →L[ℂ] Wp) : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
  ext i
  simp [B.hsVec]

lemma hsVec_zero : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  ext i
  simp [B.hsVec]

lemma hsVec_sum {n : ℕ} (A : Fin n → Wq →L[ℂ] Wp) (s : Finset (Fin n)) :
    B.hsVec (∑ i ∈ s, A i) = ∑ i ∈ s, B.hsVec (A i) := by
  induction s using Finset.induction_on with
  | empty => simp [hsVec_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hsVec_add, ih]

lemma hsInner_self (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  simp [B.hsInner, inner_self_eq_norm_sq_to_K]

variable {P : M.Par}

lemma RR_top (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : D.IsLocPt γ (P.r + 1)) : p.RR F (P.r + 1) [] γ γ = B.hsInner (p.V F γ) (p.V F γ) := by
  exact Formalism.FourierDecayAlt.P.TBBx2.RR_top p F γ hγ

lemma Ew_top (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : D.IsLocPt γ (P.r + 1)) :
    Ew p (fun _ => 1) F (P.r + 1) [] γ =
      (Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ)) * ‖B.hsVec (p.V F γ)‖ ^ 2 := by
  unfold Ew NP
  rw [RR_top p F hγ, hsInner_self]
  simp only [normC, List.map_nil, List.prod_nil, div_one]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

lemma cs_bound {n : ℕ} (a x : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i * x i) ^ 2 ≤ (∑ i, a i) * ∑ i, a i * x i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (a i))
    (fun i => Real.sqrt (a i) * x i)
  have e1 : ∀ i, Real.sqrt (a i) * (Real.sqrt (a i) * x i) = a i * x i := fun i => by
    rw [← mul_assoc, Real.mul_self_sqrt (ha i)]
  have e2 : ∀ i, Real.sqrt (a i) ^ 2 = a i := fun i => Real.sq_sqrt (ha i)
  have e3 : ∀ i, (Real.sqrt (a i) * x i) ^ 2 = a i * x i ^ 2 := fun i => by
    rw [mul_pow, e2]
  simp only [e1, e2, e3] at h
  exact h

end

end Formalism.FourierDecayAlt.P.TBBx2.Tri

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.FourierDecayAlt.P.TBBx2.Tri in
theorem Formalism.FourierDecayAlt.P.triangle_inequality_at_place : Formalism.FourierDecayAlt.TBB.TriAt := by
  intro Wp Wq _ _ _ _ _ _ P p f n fi a b C₁ C₄ n₀ p₀ γ Qγ hb ha hj hB hγ hG hQ
  have hb0 : 0 < b := by linarith
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ,
      S = Real.sqrt (nPt P.k P.r (TTp p) γ) * Real.sqrt (nPt P.k P.r (TTp p) γ) := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hA0 : 0 ≤ ∑ i, ‖a i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (a i))
  have hEf : Ew p (fun _ => 1) f (P.r + 1) [] γ = S * ‖B.hsVec (p.V f γ)‖ ^ 2 := by rw [hSdef]; exact Ew_top p f hγ
  have hEi : ∀ i, Ew p (fun _ => 1) (fi i) (P.r + 1) [] γ = S * ‖B.hsVec (p.V (fi i) γ)‖ ^ 2 := fun i => by
    rw [hSdef]; exact Ew_top p (fi i) hγ
  have hEi0 : ∀ i, 0 ≤ Ew p (fun _ => 1) (fi i) (P.r + 1) [] γ := fun i => by
    rw [hEi i]; exact mul_nonneg hS0 (sq_nonneg _)
  have hvec : (Qγ : ℂ) • B.hsVec (p.V f γ) = ∑ i, a i • B.hsVec (p.V (fi i) γ) := by
    rw [← hsVec_smul, hQ, hsVec_sum]
    simp only [hsVec_smul]
  have hnorm : ‖Qγ‖ * ‖B.hsVec (p.V f γ)‖ ≤ ∑ i, ‖a i‖ * ‖B.hsVec (p.V (fi i) γ)‖ := by
    have h1 := congrArg norm hvec
    rw [norm_smul, Complex.norm_real] at h1
    rw [h1]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_smul (a i) _).le)
  have hcs := cs_bound (fun i => ‖a i‖) (fun i => ‖B.hsVec (p.V (fi i) γ)‖) (fun i => norm_nonneg (a i))
  have hQ2 : Qγ ^ 2 * ‖B.hsVec (p.V f γ)‖ ^ 2 ≤ (∑ i, ‖a i‖) * ∑ i, ‖a i‖ * ‖B.hsVec (p.V (fi i) γ)‖ ^ 2 := by
    have h0 : 0 ≤ ‖Qγ‖ * ‖B.hsVec (p.V f γ)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc Qγ ^ 2 * ‖B.hsVec (p.V f γ)‖ ^ 2 = (‖Qγ‖ * ‖B.hsVec (p.V f γ)‖) ^ 2 := by
          rw [mul_pow, Real.norm_eq_abs, sq_abs]
      _ ≤ (∑ i, ‖a i‖ * ‖B.hsVec (p.V (fi i) γ)‖) ^ 2 := pow_le_pow_left₀ h0 hnorm 2
      _ ≤ _ := hcs
  have hreal : Qγ ^ 2 * Ew p (fun _ => 1) f (P.r + 1) [] γ ≤ (∑ i, ‖a i‖) * ∑ i, ‖a i‖ * Ew p (fun _ => 1) (fi i) (P.r + 1) [] γ := by
    rw [hEf]
    simp only [hEi]
    have h2 := mul_le_mul_of_nonneg_left hQ2 hS0
    have e3 : ∑ i, ‖a i‖ * (S * ‖B.hsVec (p.V (fi i) γ)‖ ^ 2) = S * ∑ i, ‖a i‖ * ‖B.hsVec (p.V (fi i) γ)‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e3]
    nlinarith [h2]
  have hstep : ∀ i, ENNReal.ofReal (Ew p (fun _ => 1) (fi i) (P.r + 1) [] γ) ≤ ENNReal.ofReal (b ^ (C₄ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) * jN2 p f := fun i =>
    (hB i γ hγ hG).trans (by gcongr; exact hj i)
  calc ENNReal.ofReal (Qγ ^ 2 * Ew p (fun _ => 1) f (P.r + 1) [] γ)
      ≤ ENNReal.ofReal ((∑ i, ‖a i‖) * ∑ i, ‖a i‖ * Ew p (fun _ => 1) (fi i) (P.r + 1) [] γ) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (∑ i, ‖a i‖) * ∑ i, ENNReal.ofReal ‖a i‖ * ENNReal.ofReal (Ew p (fun _ => 1) (fi i) (P.r + 1) [] γ) := by
        rw [ENNReal.ofReal_mul hA0,
          ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hEi0 i))]
        congr 1
        exact Finset.sum_congr rfl fun i _ => ENNReal.ofReal_mul (norm_nonneg _)
    _ ≤ ENNReal.ofReal (∑ i, ‖a i‖) * ∑ i, ENNReal.ofReal ‖a i‖ * (ENNReal.ofReal (b ^ (C₄ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) * jN2 p f) := by
        gcongr with i hi
        exact hstep i
    _ = ENNReal.ofReal (∑ i, ‖a i‖) * ENNReal.ofReal (∑ i, ‖a i‖) * ENNReal.ofReal (b ^ (C₄ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) * jN2 p f := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg (a i))]
        ring
    _ ≤ ENNReal.ofReal (b ^ ((2 * C₁ + C₄) * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) * jN2 p f := by
        gcongr ?_ * _
        rw [← ENNReal.ofReal_mul hA0, ← ENNReal.ofReal_mul (mul_nonneg hA0 hA0)]
        apply ENNReal.ofReal_le_ofReal
        have hU : b ^ (C₁ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * b ^ (C₁ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * b ^ (C₄ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) = b ^ ((2 * C₁ + C₄) * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) := by
          rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]
          congr 1
          ring
        calc (∑ i, ‖a i‖) * (∑ i, ‖a i‖) * (b ^ (C₄ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀))
            ≤ b ^ (C₁ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * b ^ (C₁ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (b ^ (C₄ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) := by gcongr
          _ = b ^ ((2 * C₁ + C₄) * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀) := by rw [← hU]; ring

namespace Formalism.FourierDecayAlt.P.TBBx2.Bp

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB MeasureTheory
open scoped ENNReal

lemma expo_le (C₃ CΛ C₀ L K : ℝ) (r n₀ p₀ : ℕ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀)
    (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hn₀ : n₀ ≤ 30 * (r + 1) ^ 2 + 6) (hp₀ : (p₀ : ℝ) ≤ C₀ * (3 * ((r : ℝ) + 1)) + 1) :
    1 + ((4 * n₀ : ℕ) : ℝ) + K * ((2 * r + 2 : ℕ) : ℝ) ^ 2 +
        (L + 2 * (CΛ * ((2 * r + 2 : ℕ) : ℝ))) * ((r + 1 : ℕ) : ℝ) +
        2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ) ≤
      (40 + CΛ + L + K + 2 * C₃ * (3 * C₀ + 10)) * ((2 * r + 2 : ℕ) : ℝ) ^ 4 := by
  push_cast
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = (r : ℝ) + 1 := ⟨_, rfl⟩
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hs : 1 ≤ s := by rw [hs_def]; linarith
  have hn : (n₀ : ℝ) ≤ 30 * s ^ 2 + 6 := by
    rw [hs_def]; exact_mod_cast hn₀
  have hp : (p₀ : ℝ) ≤ C₀ * (3 * s) + 1 := by rw [hs_def]; exact hp₀
  have hr : (r : ℝ) = s - 1 := by rw [hs_def]; ring
  rw [hr]
  have hs2 : 1 ≤ s ^ 2 := by nlinarith
  have hs12 : s ≤ s ^ 2 := by nlinarith
  have hs24 : s ^ 2 ≤ s ^ 4 := by nlinarith
  have hs14 : s ≤ s ^ 4 := hs12.trans hs24
  have hs4 : 0 ≤ s ^ 4 := by positivity
  have hA : 1 + 4 * (n₀ : ℝ) ≤ 40 * (2 * s) ^ 4 := by nlinarith
  have hB : K * (2 * s) ^ 2 ≤ K * (2 * s) ^ 4 :=
    mul_le_mul_of_nonneg_left (by nlinarith) hK
  have hC1 : L * s ≤ L * s ^ 4 := mul_le_mul_of_nonneg_left hs14 hL
  have hC2 : CΛ * s ^ 2 ≤ CΛ * s ^ 4 := mul_le_mul_of_nonneg_left hs24 hCΛ
  have hC3 : 0 ≤ L * s ^ 4 := mul_nonneg hL hs4
  have hC4 : 0 ≤ CΛ * s ^ 4 := mul_nonneg hCΛ hs4
  have hC0 : 0 ≤ C₀ := by linarith
  have hq1 : C₀ * s ≤ C₀ * s ^ 2 := mul_le_mul_of_nonneg_left hs12 hC0
  have hq2 : 0 ≤ C₀ * s ^ 2 := mul_nonneg hC0 (by positivity)
  have hq : 2 * (p₀ : ℝ) + n₀ ≤ (3 * C₀ + 10) * (4 * s ^ 2) := by nlinarith
  have hD : 2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀) ≤ 2 * C₃ * (3 * C₀ + 10) * (2 * s) ^ 4 := by
    calc 2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀)
        ≤ 2 * C₃ * (2 * s) ^ 2 * ((3 * C₀ + 10) * (4 * s ^ 2)) :=
          mul_le_mul_of_nonneg_left hq (mul_nonneg (mul_nonneg (by norm_num) hC₃) (sq_nonneg _))
      _ = 2 * C₃ * (3 * C₀ + 10) * (2 * s) ^ 4 := by ring
  linarith [hA, hB, hC1, hC2, hC3, hC4, hD]

lemma constant_le_rpow_of_three_le (C₂ b : ℝ) (hC₂ : 0 < C₂) (hb : 3 ≤ b) : C₂ ≤ b ^ (max 0 (Real.log C₂ / Real.log 3)) := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  rcases le_total (Real.log C₂ / Real.log 3) 0 with h | h
  · rw [max_eq_left h, Real.rpow_zero]
    have hl : Real.log C₂ ≤ 0 := by
      have := (div_le_iff₀ h3).mp h
      linarith
    calc C₂ = Real.exp (Real.log C₂) := (Real.exp_log hC₂).symm
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hl
      _ = 1 := Real.exp_zero
  · rw [max_eq_right h]
    have h3' : Real.log 3 ≠ 0 := h3.ne'
    have e3 : (3 : ℝ) ^ (Real.log C₂ / Real.log 3) = C₂ := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
      rw [show Real.log 3 * (Real.log C₂ / Real.log 3) = Real.log C₂ by field_simp]
      exact Real.exp_log hC₂
    calc C₂ = (3 : ℝ) ^ (Real.log C₂ / Real.log 3) := e3.symm
      _ ≤ b ^ (Real.log C₂ / Real.log 3) := Real.rpow_le_rpow (by norm_num) hb h

lemma const_le (C₃ CΛ C₀ C₂ Cκ b Λ κ₀ : ℝ) (r n₀ p₀ : ℕ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀)
    (hC₂ : 0 < C₂) (hb : 3 ≤ b) (hΛ : 1 ≤ Λ) (hΛb : Λ ≤ b ^ (CΛ * ((2 * r + 2 : ℕ) : ℝ)))
    (hκ : 0 < κ₀) (hκb : κ₀ ≤ b ^ (Cκ * ((2 * r + 2 : ℕ) : ℝ) ^ 2))
    (hn₀ : n₀ ≤ 30 * (r + 1) ^ 2 + 6) (hp₀ : (p₀ : ℝ) ≤ C₀ * (3 * ((r : ℝ) + 1)) + 1) :
    2 * (3 * b) ^ (2 * n₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (r + 1)) *
        b ^ (2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) ≤
      b ^ ((40 + CΛ + max 0 (Real.log C₂ / Real.log 3) + |Cκ| + 2 * C₃ * (3 * C₀ + 10)) *
        ((2 * r + 2 : ℕ) : ℝ) ^ 4) := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hc0 : (0 : ℝ) ≤ max 0 (Real.log C₂ / Real.log 3) := le_max_left _ _
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  have f1 : (2 : ℝ) ≤ b ^ (1 : ℝ) := by rw [Real.rpow_one]; linarith
  have f2 : (3 * b) ^ (2 * n₀) ≤ b ^ ((4 * n₀ : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    calc (3 * b) ^ (2 * n₀) ≤ (b * b) ^ (2 * n₀) :=
          pow_le_pow_left₀ (by positivity) (by nlinarith) _
      _ = b ^ (4 * n₀) := by ring
  have f3 : κ₀ ≤ b ^ (|Cκ| * ((2 * r + 2 : ℕ) : ℝ) ^ 2) :=
    hκb.trans (Real.rpow_le_rpow_of_exponent_le hb1
      (mul_le_mul_of_nonneg_right (le_abs_self Cκ) (sq_nonneg _)))
  have f4 : C₂ * Λ ^ 2 ≤ b ^ (max 0 (Real.log C₂ / Real.log 3) + 2 * (CΛ * ((2 * r + 2 : ℕ) : ℝ))) := by
    rw [Real.rpow_add hb0]
    refine mul_le_mul (constant_le_rpow_of_three_le C₂ b hC₂ hb) ?_ (sq_nonneg _) (by positivity)
    calc Λ ^ 2 ≤ (b ^ (CΛ * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 := pow_le_pow_left₀ hΛ0 hΛb 2
      _ = b ^ (2 * (CΛ * ((2 * r + 2 : ℕ) : ℝ))) := by
        rw [← Real.rpow_mul_natCast hb0.le]
        congr 1
        push_cast
        ring
  have f5 : (C₂ * Λ ^ 2) ^ (r + 1) ≤ b ^ ((max 0 (Real.log C₂ / Real.log 3) + 2 * (CΛ * ((2 * r + 2 : ℕ) : ℝ))) * ((r + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_mul_natCast hb0.le]
    exact pow_le_pow_left₀ (mul_nonneg hC₂.le (sq_nonneg _)) f4 _
  have hE := expo_le C₃ CΛ C₀ (max 0 (Real.log C₂ / Real.log 3)) |Cκ| r n₀ p₀ hC₃ hCΛ hC₀ hc0 (abs_nonneg _) hn₀ hp₀
  calc 2 * (3 * b) ^ (2 * n₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (r + 1)) * b ^ (2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))
      ≤ b ^ (1 : ℝ) * b ^ ((4 * n₀ : ℕ) : ℝ) *
          (b ^ (|Cκ| * ((2 * r + 2 : ℕ) : ℝ) ^ 2) * b ^ ((max 0 (Real.log C₂ / Real.log 3) + 2 * (CΛ * ((2 * r + 2 : ℕ) : ℝ))) * ((r + 1 : ℕ) : ℝ))) *
          b ^ (2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul f1 f2 (by positivity) (by positivity))
            (mul_le_mul f3 f5 (by positivity) (by positivity)) (by positivity) (by positivity))
          (by positivity)
    _ = b ^ (1 + ((4 * n₀ : ℕ) : ℝ) + |Cκ| * ((2 * r + 2 : ℕ) : ℝ) ^ 2 +
          (max 0 (Real.log C₂ / Real.log 3) + 2 * (CΛ * ((2 * r + 2 : ℕ) : ℝ))) * ((r + 1 : ℕ) : ℝ) + 2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) := by
        rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0]
        ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hb1 hE

end Formalism.FourierDecayAlt.P.TBBx2.Bp

namespace Formalism.FourierDecayAlt.P.TBBx2.Bp

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB MeasureTheory
open scoped ENNReal

lemma jacobi_norm_sq_bound {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (f F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (n₀ p₀ : ℕ) (hT : 1 ≤ Tq p)
    (h : ∀ c : Fin (P.r + 1) → ℂ, Ew p (fun _ => 1) F (P.r + 1) [] (bigPt P.r c) ≤
      ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c)) :
    jN2 p F ≤ ENNReal.ofReal ((Tq p)⁻¹ ^ n₀) * bigCellDetWeightedEnergyIntegral p f (2 * p₀ + n₀) := by
  have hnn : 0 ≤ (Tq p)⁻¹ ^ n₀ := pow_nonneg (inv_nonneg.mpr (by linarith)) _
  unfold jN2 bigCellDetWeightedEnergyIntegral
  rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply MeasureTheory.lintegral_mono
  intro c
  dsimp only
  rw [← ENNReal.ofReal_mul hnn]
  apply ENNReal.ofReal_le_ofReal
  exact (h c).trans (le_of_eq (by ring))

end Formalism.FourierDecayAlt.P.TBBx2.Bp

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB MeasureTheory in
theorem Formalism.FourierDecayAlt.P.theorem_b_of_parts : Formalism.FourierDecayAlt.TBB.ThmBpOfParts := by
  intro C₃ CΛ C₀ C₂ Cκ hC₃ hCΛ hC₀ hC₂
  refine ⟨40 + CΛ + max 0 (Real.log C₂ / Real.log 3) + |Cκ| + 2 * C₃ * (3 * C₀ + 10), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f Fp Fm b Λ κ₀ n₀ p₀ hb hΛ hΛb hκ hκb hT hn₀ hp₀ hN hPp hPm hR γ hγ hG
  have hb0 : 0 < b := by linarith
  have hT0 : 0 < Tq p := by linarith
  have hX0 : 0 ≤ (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) := by positivity
  have hK0 : 0 ≤ κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) := by positivity
  have hTn0 : 0 ≤ (Tq p)⁻¹ ^ n₀ := by positivity
  have hBq0 : 0 ≤ b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) := by positivity
  have hZ0 : 0 ≤ κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) := mul_nonneg (mul_nonneg hK0 hTn0) hBq0
  have hD := hR (2 * p₀ + n₀) le_rfl
  have hFb : ∀ F, F ∈ ({Fp, Fm} : Set (B.Mat P.k P.r → (Wq →L[ℂ] Wp))) →
      PtBound p F (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) →
      ENNReal.ofReal (Ew p (fun _ => 1) F (P.r + 1) [] γ) ≤ ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) * jN2 p f := by
    intro F hF hP
    have hj := Formalism.FourierDecayAlt.P.TBBx2.Bp.jacobi_norm_sq_bound p f F n₀ p₀ hT (fun c => hN.2 c F hF)
    calc ENNReal.ofReal (Ew p (fun _ => 1) F (P.r + 1) [] γ)
        ≤ ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) * jN2 p F := hP γ hγ hG
      _ ≤ ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) * (ENNReal.ofReal ((Tq p)⁻¹ ^ n₀) * (ENNReal.ofReal (b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) * jN2 p f)) := by
          gcongr
          exact hj.trans (by gcongr)
      _ = ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) * jN2 p f := by
          rw [ENNReal.ofReal_mul (mul_nonneg hK0 hTn0), ENNReal.ofReal_mul hK0]
          ring
  have hEp := hFb Fp (Set.mem_insert _ _) hPp
  have hEm := hFb Fm (Set.mem_insert_of_mem _ (Set.mem_singleton Fm)) hPm
  have hTG : (Tq p / Gp p γ) ^ n₀ * (Tq p)⁻¹ ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) = (Gp p γ)⁻¹ ^ (2 * p₀ + n₀) := by
    have e : Tq p / Gp p γ * (Tq p)⁻¹ = (Gp p γ)⁻¹ := by
      rw [div_mul_eq_mul_div, mul_inv_cancel₀ hT0.ne', one_div]
    rw [← mul_pow, e, ← pow_add, add_comm]
  calc ENNReal.ofReal (Ew p (fun _ => 1) f (P.r + 1) [] γ)
      ≤ ENNReal.ofReal ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) * (Ew p (fun _ => 1) Fp (P.r + 1) [] γ + Ew p (fun _ => 1) Fm (P.r + 1) [] γ)) := ENNReal.ofReal_le_ofReal (hN.1 γ hγ hG)
    _ ≤ ENNReal.ofReal ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀)) * (ENNReal.ofReal (Ew p (fun _ => 1) Fp (P.r + 1) [] γ) + ENNReal.ofReal (Ew p (fun _ => 1) Fm (P.r + 1) [] γ)) := by
        rw [ENNReal.ofReal_mul hX0]
        gcongr
        exact ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀)) * (ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) * jN2 p f + ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) * jN2 p f) := by
        gcongr
    _ = ENNReal.ofReal ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) + (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)))) * jN2 p f := by
        rw [ENNReal.ofReal_add (mul_nonneg hX0 hZ0) (mul_nonneg hX0 hZ0), ENNReal.ofReal_mul hX0]
        ring
    _ ≤ ENNReal.ofReal (b ^ ((40 + CΛ + max 0 (Real.log C₂ / Real.log 3) + |Cκ| + 2 * C₃ * (3 * C₀ + 10)) * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) * jN2 p f := by
        gcongr ?_ * _
        apply ENNReal.ofReal_le_ofReal
        have key : (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) + (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * (Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) =
            (2 * (3 * b) ^ (2 * n₀) * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀) := by
          rw [← hTG]; ring
        rw [key]
        exact mul_le_mul_of_nonneg_right
          (Formalism.FourierDecayAlt.P.TBBx2.Bp.const_le C₃ CΛ C₀ C₂ Cκ b Λ κ₀ P.r n₀ p₀ hC₃ hCΛ hC₀ hC₂ hb hΛ hΛb hκ hκb
            hn₀ hp₀) (by positivity)
