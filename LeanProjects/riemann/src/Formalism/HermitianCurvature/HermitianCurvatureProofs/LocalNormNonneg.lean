import Formalism.HermitianCurvature.StatementKB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfCauchySchwarz
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockEstimatesSumForm

open Finset Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt NumberField

section defeq
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
  (RR : Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)

example : (KB.withRR S RR).W = S.W := rfl
example : (KB.withRR S RR).base.Wall = S.base.Wall := rfl
example : (KB.withRR S RR).base.cnt = S.base.cnt := rfl
example : (KB.withRR S RR).base.K = S.base.K := rfl
example : (KB.withRR S RR).base.Ntop = S.base.Ntop := rfl
example : (KB.withRR S RR).base.av = S.base.av := rfl
example : (KB.withRR S RR).base.vol = S.base.vol := rfl
example : (KB.withRR S RR).base.La = S.base.La := rfl
example : (KB.withRR S RR).base.wt = S.base.wt := rfl
example : (KB.withRR S RR).base.f = S.base.f := rfl
example : (KB.withRR S RR).base.r = S.base.r := rfl
example (v : Fin S.f) ε i a p q : (KB.withRR S RR).gramLoc v ε i a p q =
    ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G p) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G q) : ℝ) : ℂ) *
      RR v ε i a p q := rfl
end defeq

theorem extract_prob {ι X : Type} [Fintype ι] (U : Finset X) (θ : ℕ → ι → X → ℝ)
    (hθ : ∀ n A, TB.IsProb U (θ n A)) :
    ∃ (φ : ℕ → ℕ) (θ' : ι → X → ℝ), StrictMono φ ∧ (∀ A, TB.IsProb U (θ' A)) ∧
      ∀ A, ∀ x ∈ U, Tendsto (fun n => θ (φ n) A x) atTop (𝓝 (θ' A x)) := by
  classical
  let x : ℕ → (ι × U) → ℝ := fun n p => θ n p.1 p.2.1
  have hK : IsCompact (Set.Icc (0 : ι × U → ℝ) 1) := isCompact_Icc
  have hmem : ∀ n, x n ∈ Set.Icc (0 : ι × U → ℝ) 1 := by
    intro n
    refine ⟨fun p => (hθ n p.1).1 _, fun p => ?_⟩
    have h := Finset.single_le_sum (fun y _ => (hθ n p.1).1 y) p.2.2
    rw [(hθ n p.1).2.2] at h
    exact h
  obtain ⟨y, _, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hl : ∀ A z (h : z ∈ U), Tendsto (fun n => θ (φ n) A z) atTop (𝓝 (y (A, ⟨z, h⟩))) := fun A z h =>
    ((continuous_apply (A, (⟨z, h⟩ : U))).tendsto y).comp hlim
  refine ⟨φ, fun A z => if h : z ∈ U then y (A, ⟨z, h⟩) else 0, hφ, ?_, ?_⟩
  · intro A
    refine ⟨fun z => ?_, fun z hz => by simp [hz], ?_⟩
    · by_cases h : z ∈ U
      · simp only [h, dite_true]
        exact ge_of_tendsto' (hl A z h) fun n => (hθ (φ n) A).1 z
      · simp [h]
    · have hs : Tendsto (fun n => ∑ z ∈ U, θ (φ n) A z) atTop
          (𝓝 (∑ z ∈ U, if h : z ∈ U then y (A, ⟨z, h⟩) else 0)) := by
        apply tendsto_finsetSum
        intro z hz
        simp only [hz, dite_true]
        exact hl A z hz
      have h1 : (fun n => ∑ z ∈ U, θ (φ n) A z) = fun _ => (1 : ℝ) := funext fun n => (hθ (φ n) A).2.2
      rw [h1] at hs
      exact tendsto_nhds_unique hs tendsto_const_nhds
  · intro A z hz
    simp only [hz, dite_true]
    exact hl A z hz

section conv
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
  (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)

theorem gram_withRR (n : ℕ) (ε : ℝ) (i : ℕ) (w : C.Word S.f) (p q : TB.Pt E) :
    (KB.withRR S (RR n)).gram ε i w p q = if i ≤ S.G.r + 1 then ∏ v, ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G
      (C.loc (S.σ v) p)) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) q)) : ℝ) : ℂ) *
        RR n v ε i (w v) (C.loc (S.σ v) p) (C.loc (S.σ v) q) else 0 := rfl

theorem gram_S (ε : ℝ) (i : ℕ) (w : C.Word S.f) (p q : TB.Pt E) :
    S.gram ε i w p q = if i ≤ S.G.r + 1 then ∏ v, ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G
      (C.loc (S.σ v) p)) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) q)) : ℝ) : ℂ) *
        (S.pd v).RR ε i (w v) (C.loc (S.σ v) p) (C.loc (S.σ v) q) else 0 := rfl

variable {S RR}

theorem gram_tendsto
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    {ε : ℝ} (hε : 0 < ε) (i : ℕ) (w : S.W) (p q : TB.Pt E) :
    Tendsto (fun n => (KB.withRR S (RR n)).gram ε i w.1 p q) atTop (𝓝 (S.gram ε i w.1 p q)) := by
  simp only [gram_withRR, gram_S]
  split_ifs
  · apply tendsto_finsetProd
    intro v _
    exact tendsto_const_nhds.mul (hconv v ε hε i _ ⟨w, rfl⟩ _ _)
  · exact tendsto_const_nhds

theorem nst_tendsto
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    {ε : ℝ} (hε : 0 < ε) (i s : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (t t' : E) :
    Tendsto (fun n => (KB.withRR S (RR n)).base.Nst ε i s w Y κ t t') atTop
      (𝓝 (S.base.Nst ε i s w Y κ t t')) := by
  have e1 : ∀ n, (KB.withRR S (RR n)).base.Nst ε i s w Y κ t t' = (∑ h ∈ Y, ∑ h' ∈ Y,
      κ h h' * (KB.withRR S (RR n)).gram ε i w.1 (TB.join h s t) (TB.join h' s t')) / (S.base.wt w : ℂ) :=
    fun n => rfl
  have e2 : S.base.Nst ε i s w Y κ t t' = (∑ h ∈ Y, ∑ h' ∈ Y,
      κ h h' * S.gram ε i w.1 (TB.join h s t) (TB.join h' s t')) / (S.base.wt w : ℂ) := rfl
  rw [e2]; simp only [e1]
  apply Tendsto.div_const
  apply tendsto_finsetSum; intro h _
  apply tendsto_finsetSum; intro h' _
  exact tendsto_const_nhds.mul (gram_tendsto hconv hε i w _ _)

theorem base_count_tendsto
    (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
      Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) :
    Tendsto (fun n => (KB.withRR S (RR n)).base.N0 ε k w Y κ) atTop (𝓝 (S.base.N0 ε k w Y κ)) := by
  have e1 : ∀ n, (KB.withRR S (RR n)).base.N0 ε k w Y κ = (∑ h ∈ Y, ∑ h' ∈ Y,
      κ h h' * (KB.withRR S (RR n)).gram ε k w.1 h h').re / S.base.wt w := fun n => rfl
  have e2 : S.base.N0 ε k w Y κ = (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε k w.1 h h').re / S.base.wt w := rfl
  rw [e2]; simp only [e1]
  apply Tendsto.div_const
  apply (Complex.continuous_re.tendsto _).comp
  apply tendsto_finsetSum; intro h _
  apply tendsto_finsetSum; intro h' _
  exact tendsto_const_nhds.mul (gram_tendsto hconv hε k w _ _)

theorem gram_psd {S : C.HidaSetting E Wp Wq} (hP : C.ThmPPos S) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : S.W)
    (Y : Finset (TB.Pt E)) : TB.PSDOn Y (fun h h' => S.gram ε k w.1 h h') := by
  classical
  by_cases hk : k ≤ S.G.r + 1
  · have : ∀ v ∈ (univ : Finset (Fin S.f)), TB.PSDOn Y
        (fun h h' => S.gramLoc v ε k (w.1 v) (C.loc (S.σ v) h) (C.loc (S.σ v) h')) := by
      intro v _
      exact JCx1.decay.psd_pull (Y.image (C.loc (S.σ v))) _ (hP v ε hε k hk w _) Y _
        (fun h hh => Finset.mem_image_of_mem _ hh)
    refine Jx7.psd_congr ?_ (Jx7.psd_prod univ _ this)
    intro x _ y _
    simp only [C.HidaSetting.gram, hk, if_true]
  · refine Jx7.psd_congr ?_ (Jx7.psd_zero (F := Y))
    intro x _ y _
    simp only [C.HidaSetting.gram, hk, if_false]

theorem local_norm_nonneg_alt {S : C.HidaSetting E Wp Wq} (hP : C.ThmPPos S) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : S.W)
    (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (hκ : TB.PSDOn Y κ) : 0 ≤ S.base.N0 ε k w Y κ := by
  have e2 : S.base.N0 ε k w Y κ = (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε k w.1 h h').re / S.base.wt w := rfl
  rw [e2]
  apply div_nonneg (BaseGramNonnegativity.sum_re_nonneg Y κ _ hκ (gram_psd hP hε k w Y))
  show 0 ≤ C.Word.size S.P w.1
  unfold C.Word.size
  exact Finset.prod_nonneg fun v _ => List.prod_nonneg fun x hx => by
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _

end conv

theorem limit_closed : KB.LimitClosed := by
  intro E _ _ _ Wp Wq _ _ _ _ S RR hconv
  refine ⟨?_, ?_, ?_⟩
  · intro Λ hL ε hε i s hs hsi hir w hw hcnt
    choose θn hθn hbd using fun n => hL n ε hε i s hs hsi hir w hw hcnt
    obtain ⟨φ, θ, hφ, hθ, hlim⟩ := extract_prob (ι := Finset (Fin S.f)) (X := S.W × S.W)
      (S.base.Wb (S.base.cnt w + S.base.K) ×ˢ S.base.Wb (S.base.cnt w + S.base.K)) (fun n => θn n) hθn
    refine ⟨θ, hθ, ?_⟩
    intro Y T κ hY hκ t ht t' ht' h0 h0' ho A
    have h1 : ∀ n, (∏ v ∈ A, S.base.av v (t⁻¹ - t'⁻¹) ^ S.base.K) *
        ‖(KB.withRR S (RR (φ n))).base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ ≤
        (∏ v ∈ A, Λ (i - s + 1) s v ^ S.base.K) *
          ∑ x ∈ S.base.Wb (S.base.cnt w + S.base.K) ×ˢ S.base.Wb (S.base.cnt w + S.base.K), θn (φ n) A x *
            ((((KB.withRR S (RR (φ n))).base.Nst ε i s x.1 Y (TB.blk κ s t t) t t).re +
              ((KB.withRR S (RR (φ n))).base.Nst ε i s x.2 Y (TB.blk κ s t' t') t' t').re) / 2) :=
      fun n => hbd (φ n) Y T κ hY hκ t ht t' ht' h0 h0' ho A
    refine le_of_tendsto_of_tendsto' (b := (atTop : Filter ℕ)) ?_ ?_ h1
    · exact tendsto_const_nhds.mul ((nst_tendsto hconv hε i s w Y _ t t').comp hφ.tendsto_atTop).norm
    · refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun x hx => (hlim A x hx).mul ?_)
      refine Tendsto.div_const (Tendsto.add ?_ ?_) _
      · exact (Complex.continuous_re.tendsto _).comp ((nst_tendsto hconv hε i s x.1 Y _ t t).comp hφ.tendsto_atTop)
      · exact (Complex.continuous_re.tendsto _).comp
          ((nst_tendsto hconv hε i s x.2 Y _ t' t').comp hφ.tendsto_atTop)
  · intro Λ' hL ε hε s hs hsr w hw hcnt
    choose θn hθn hbd using fun n => hL n ε hε s hs hsr w hw hcnt
    obtain ⟨φ, θ, hφ, hθ, hlim⟩ := extract_prob (ι := Finset (Fin S.f)) (X := S.W)
      (S.base.Wb (S.base.cnt w + S.base.K)) (fun n => θn n) hθn
    refine ⟨θ, hθ, ?_⟩
    intro Y hY κ hκ t ht B
    have h1 : ∀ n, ((KB.withRR S (RR (φ n))).base.Nst ε (S.G.r + 1) s w Y κ t t).re ≤
        (∏ v ∈ B, (S.base.av v t * Λ' (S.G.r + 2 - s) s v) ^ (2 * S.base.K)) *
          ∑ w' ∈ S.base.Wb (S.base.cnt w + S.base.K), θn (φ n) B w' *
            ((KB.withRR S (RR (φ n))).base.Nst ε (S.G.r + 1) s w' Y κ t t).re :=
      fun n => hbd (φ n) Y hY κ hκ t ht B
    refine le_of_tendsto_of_tendsto' (b := (atTop : Filter ℕ)) ?_ ?_ h1
    · exact (Complex.continuous_re.tendsto _).comp
        ((nst_tendsto hconv hε (S.G.r + 1) s w Y κ t t).comp hφ.tendsto_atTop)
    · refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun x hx => (hlim B x hx).mul ?_)
      exact (Complex.continuous_re.tendsto _).comp
        ((nst_tendsto hconv hε (S.G.r + 1) s x Y κ t t).comp hφ.tendsto_atTop)
  · intro C₄ hP _ hSF ε hε i s hs hsi hir w hw hcnt hvol
    set Bd := C₄ ^ (S.base.f * s) * (∏ s' ∈ Ico 1 s, S.base.vol (i - s + 1) s')
    have H : ∀ n, ∃ θ : Unit → S.W → ℝ, (∀ u, TB.IsProb (S.base.Wb (S.base.cnt w + s * S.base.K)) (θ u)) ∧
        ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - s) → ∀ κ, TB.PSDOn Y κ →
          ∀ (t₀ : E) (T : Finset E), (∀ t ∈ T, t ≠ 0 ∧ t - t₀ ∈ S.base.La (i - s + 1) s) →
            ∑ t ∈ T, ((KB.withRR S (RR n)).base.Nst ε i s w Y κ t t).re ≤
              Bd * ∑ w' ∈ S.base.Wb (S.base.cnt w + s * S.base.K), θ () w' *
                (KB.withRR S (RR n)).base.N0 ε (i - s) w' Y κ := by
      intro n
      obtain ⟨Mv, hMv, θ, hθ, hb⟩ := hSF n ε hε i s hs hsi hir w hw hcnt hvol
      refine ⟨fun _ => θ, fun _ => hθ, ?_⟩
      intro Y hY κ hκ t₀ T hT
      refine (hb Y hY κ hκ t₀ T hT).trans ?_
      apply mul_le_mul_of_nonneg_right hMv
      exact Finset.sum_nonneg fun w' _ => mul_nonneg (hθ.1 w') (local_norm_nonneg_alt (hP n) hε _ w' Y κ hκ)
    choose θn hθn hbd using H
    obtain ⟨φ, θ, hφ, hθ, hlim⟩ := extract_prob _ θn hθn
    refine ⟨Bd, le_refl _, θ (), hθ (), ?_⟩
    intro Y hY κ hκ t₀ T hT
    have h1 : ∀ n, ∑ t ∈ T, ((KB.withRR S (RR (φ n))).base.Nst ε i s w Y κ t t).re ≤
        Bd * ∑ w' ∈ S.base.Wb (S.base.cnt w + s * S.base.K), θn (φ n) () w' *
          (KB.withRR S (RR (φ n))).base.N0 ε (i - s) w' Y κ := fun n => hbd (φ n) Y hY κ hκ t₀ T hT
    refine le_of_tendsto_of_tendsto' (b := (atTop : Filter ℕ)) ?_ ?_ h1
    · exact tendsto_finsetSum _ fun t _ => (Complex.continuous_re.tendsto _).comp
        ((nst_tendsto hconv hε i s w Y κ t t).comp hφ.tendsto_atTop)
    · refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun x hx => (hlim () x hx).mul ?_)
      exact (base_count_tendsto hconv hε (i - s) x Y κ).comp hφ.tendsto_atTop

end Formalism.FourierDecayAlt.P.PBA
