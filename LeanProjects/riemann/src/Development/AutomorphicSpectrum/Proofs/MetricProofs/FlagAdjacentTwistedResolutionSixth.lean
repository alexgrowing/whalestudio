import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticProjectionBijective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PluckerNonvanishingOrbitInvariant
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PlkFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentPluckerOrbitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartHolomorphicCompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietyFirstStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietySecondStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricVectorLogResolutionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensW

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fst_orbit {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k), fun k => hc _, rfl⟩

theorem snd_orbit {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => by dsimp only; split_ifs <;> exact hc _, ?_⟩
  funext ⟨k, m⟩
  by_cases e : k = k₀
  · subst e
    simp [sndPt, v₁_self]
  · simp [sndPt, v₁_ne (p := ⟨k, m⟩) e, e]

theorem same_block {N j : ℕ} {a b ca cb : Fin N} (hj : j ≤ N) (hb : (b : ℕ) = a + 1)
    (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) :
    ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) := by
  have := b.2
  have := cb.2
  unfold lastCol at hca
  split_ifs at hca <;> omega

theorem blockDiag_transv {N j : ℕ} {ca cb : Fin N} (h : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t) := by
  intro r s hrs
  have hne : r ≠ s := fun e => hrs (by rw [e])
  rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.single_apply]
  split_ifs with e
  · obtain ⟨rfl, rfl⟩ := e
    exact absurd h hrs
  · rfl

theorem lowerUni_transv {N : ℕ} {ca cb : Fin N} (h : ca < cb) (t : ℂ) :
    IsLowerUni (1 + Matrix.single cb ca t) := by
  refine ⟨fun r => ?_, fun r s hrs => ?_⟩
  · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, e⟩
    exact h.ne e
  · rw [Matrix.add_apply, Matrix.one_apply_ne hrs.ne, zero_add, Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact absurd h (not_lt.2 hrs.le)

theorem minor_analytic {m N : ℕ} {V : Set (Fin m → ℂ)} {A : (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hA : ∀ r s, AnalyticOnNhd ℂ (fun u => A u r s) V) (I J : Finset (Fin N)) :
    AnalyticOnNhd ℂ (fun u => minorIJ (A u) I J) V := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply]
    refine Finset.analyticOnNhd_fun_sum _ fun σ _ => ?_
    simp only [Units.smul_def, zsmul_eq_mul]
    exact analyticOnNhd_const.mul (Finset.analyticOnNhd_fun_prod _ fun i _ => hA _ _)
  · simp only [dif_neg e]
    exact analyticOnNhd_const

theorem mul_analytic {m N : ℕ} {V : Set (Fin m → ℂ)} {A : (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hA : ∀ r s, AnalyticOnNhd ℂ (fun u => A u r s) V) (C : Matrix (Fin N) (Fin N) ℂ) (r s : Fin N) :
    AnalyticOnNhd ℂ (fun u => (A u * C) r s) V := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun i _ => (hA r i).mul analyticOnNhd_const

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem wVec_some (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (t : ℂ) (k : K) (m : ι k) :
    wVec M F b h τ a k₀ ca cb t ⟨some k, m⟩ = flagPt M F b h ⟨k, m⟩ := rfl

theorem plk_ne_zero (M : FlagModel y Ψ N j) {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) {b : BM.Rb.X} (hb : b ∈ BM.O l)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (hh : ∀ τ', IsBlockDiag j (h τ'))
    (hm : ∀ (τ' : Ψ) (i : Fin N), IsProperStep N j i → minorIJ (h τ') (stepCols N j i) (stepCols N j i) ≠ 0)
    (p : Ψ × Fin N) : plk M (BM.F l) (bvec BM l b) (flagPt M (BM.F l) (bvec BM l b) h) p ≠ 0 := by
  have hg := bvec_good K ι Φ y Ψ N j M n BM l b hb
  cases hp : M.blk p with
  | none => simp [plk, hp]
  | some k =>
    rw [plk_flagPt K ι Φ y Ψ N j M (BM.F l) _ h p k (BM.isFrame l) hg.1 hg.2.1 hh hp]
    refine hm _ _ ?_
    by_contra hn
    rw [(M.blk_none p).2 hn] at hp
    cases hp

theorem not_mem_top (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  have := h.2 1 trivial
  simp at this

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensW

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_w : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ (l : Fin BM.q) (x : RW.X), FA.pr (q 0 x) ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, FA.pr (q 0 x') ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x'))) (fstPt k₀ (RW.lift x' x')) p ≠ 0 ∧ FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x'))) (sndPt k₀ (RW.lift x' x')) p ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hab hblk hca hcb RW q _ h0 _ _ l x hx V hV hxV
  have harith : IsArithVar (mCoordIdeal y) (d + 2) := FA.Re.arith
  have hsb := FC.DensW.same_block M.j_le hb hab hca hcb
  have hlt : ca < cb := Fin.lt_def.2 (by omega)
  have hbase : ∀ w : RW.X, SameOrbit (basePart M.blk (fstPt k₀ (RW.lift w w)))
      (BM.Rb.lift (FA.pr (q 0 w)) (FA.pr (q 0 w))) := by
    intro w
    obtain ⟨x₀, hx₀⟩ := (FC.re_pi_bijective K ι Φ y Ψ N j M n d BM FA).2 (q 0 w)
    have e1 := h0 w x₀ hx₀
    have e2 := FA.pr_eq x₀
    rw [hx₀] at e2
    exact orbit_trans (orbit_symm (FibreCount.basePart_orbit M.blk e1)) e2
  obtain ⟨h₀, t, hh₀, ho⟩ := GlobalTheory.T.flag_adjacent_arith_variety_second K ι Φ y Ψ N j M n BM d τ a b k₀ ca cb hb hab hblk hca hcb harith l _ hx _
    (RW.mem x x (RW.mem_U x)) (hbase x)
  have hT : ∀ τ', IsLowerUni ((Function.update (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) τ
      (1 + Matrix.single cb ca t)) τ') := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact FC.DensW.lowerUni_transv hlt t
    · rw [Function.update_of_ne e]
      exact ⟨fun r => Matrix.one_apply_eq r, fun r s h => Matrix.one_apply_ne h.ne⟩
  have han : ∀ (m : ℕ) (V : Set (Fin m → ℂ)) (bp : (Fin m → ℂ) → BM.Rb.X) (hh : Ψ → (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ),
      IsOpen V → ContinuousOn bp V → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) →
      (∀ u ∈ V, bp u ∈ BM.O l) → (∀ τ' r s, AnalyticOnNhd ℂ (fun u => hh τ' u r s) V) →
      (∀ u ∈ V, ∀ τ', IsBlockDiag j (hh τ' u) ∧ (hh τ' u).det ≠ 0) →
      ∀ q, AnalyticOnNhd ℂ (fun u => FC.wVec M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) τ a k₀ ca cb t q) V := by
    intro m V bp hh hV hc hch hO hhan _ qq
    obtain ⟨hbv, hval⟩ := GlobalTheory.T.base_chart_holomorphic_composition K ι Φ y Ψ N j M n BM l m V bp hV hc hch hO
    have hreg : ∀ qq I, AnalyticOnNhd ℂ (fun u => valAt M.x ((BM.F l).u qq I) (FC.bvec BM l (bp u))) V := fun qq I =>
      hval _ fun c hcO => ((FC.bvec_good K ι Φ y Ψ N j M n BM l c hcO).2.1.2.1 qq I).1
    obtain ⟨o, mm⟩ := qq
    cases o with
    | none =>
      exact Finset.analyticOnNhd_fun_sum _ fun I _ => (hreg _ I).mul
        (FC.DensW.minor_analytic (FC.DensW.mul_analytic (hhan τ) _) _ _)
    | some k =>
      by_cases hk : ∀ p, M.blk p ≠ some k
      · have e : ∀ u, FC.wVec M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) τ a k₀ ca cb t ⟨some k, mm⟩ =
            FC.bvec BM l (bp u) ⟨⟨k, hk⟩, mm⟩ := fun u => (FC.DensW.wVec_some M (BM.F l) _ _ τ a k₀ ca cb t k mm).trans (dif_pos hk)
        simp only [e]
        exact hbv _
      · obtain ⟨p, hp⟩ := not_forall.1 hk
        have hp' : M.blk p = some k := not_not.1 hp
        have e : ∀ u, FC.wVec M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) τ a k₀ ca cb t ⟨some k, mm⟩ =
            ∑ I, valAt M.x ((BM.F l).u ⟨k, mm⟩ I) (FC.bvec BM l (bp u)) * minorIJ (hh p.1 u) I (stepCols N j p.2) :=
          fun u => (FC.DensW.wVec_some M (BM.F l) _ _ τ a k₀ ca cb t k mm).trans (FC.flagPt_step M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) hp' mm)
        simp only [e]
        exact Finset.analyticOnNhd_fun_sum _ fun I _ => (hreg _ I).mul (FC.DensW.minor_analytic (hhan p.1) _ _)
  obtain ⟨x', hx'V, b', hb', h', hh', ho', hmin⟩ := GlobalTheory.T.base_metric_vector_log_resolution K ι Φ y Ψ N j M n BM (Option K)
    (fun o => ι (o.getD k₀)) _ ⊤ (d + 2) RW rfl l
    (fun c h => FC.wVec M (BM.F l) (FC.bvec BM l c) h τ a k₀ ca cb t) _ hT han
    (fun c hc h hh => GlobalTheory.T.flag_adjacent_arith_variety_first K ι Φ y Ψ N j M n BM d τ a b k₀ ca cb hb hab hblk hca hcb harith l c hc h t hh)
    x _ hx h₀ hh₀ ho V hV hxV
  have hw := GlobalTheory.T.flag_adjacent_plucker_orbit K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hblk hca hcb (BM.F l) (FC.bvec BM l b') h' t
  have hb'O : b' ∈ BM.O l := hb'.1
  have hg := FC.bvec_good K ι Φ y Ψ N j M n BM l b' hb'O
  have o₀ := FC.DensW.fst_orbit ho'
  have o₁ := FC.DensW.snd_orbit ho'
  rw [hw.1] at o₀
  rw [hw.2] at o₁
  have hpr : FA.pr (q 0 x') = b' := by
    refine BM.Rb.inj _ _ (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensW.not_mem_top _) (orbit_trans (orbit_symm (hbase x')) ?_)
    have o₂ := FibreCount.basePart_orbit M.blk o₀
    rw [FC.basePart_flagPt] at o₂
    exact orbit_trans o₂ hg.2.2.2
  refine ⟨x', hx'V, by rw [hpr]; exact hb', fun p => ?_⟩
  rw [hpr]
  refine ⟨(FC.plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p o₀).2
    (FC.DensW.plk_ne_zero M BM l hb'O h' (fun τ' => (hh' τ').1) (fun τ' i hi => (hmin τ' i hi).1) p),
    (FC.plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p o₁).2
    (FC.DensW.plk_ne_zero M BM l hb'O _ (fun τ' => ?_) (fun τ' i hi => ?_) p)⟩
  · by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact (hh' τ').1.mul (FC.DensW.blockDiag_transv hsb t)
    · rw [Function.update_of_ne e]
      exact (hh' τ').1
  · have hm := (hmin τ' i hi).2
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self] at hm ⊢
      exact hm
    · rw [Function.update_of_ne e] at hm ⊢
      rwa [Matrix.mul_one] at hm
