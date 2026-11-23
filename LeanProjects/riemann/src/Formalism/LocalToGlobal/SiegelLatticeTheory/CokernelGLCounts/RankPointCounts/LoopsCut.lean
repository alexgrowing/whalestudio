import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyGenusBoundOfSiegelRatio

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc
  Formalism.FourierDecayAlt

namespace Formalism.L2.SG.LoopsCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)

def bigS (s : ℕ) : Set (τ × τ) := {p | p ∈ X.allPairs X.nzSet ∧ X.s0 p.1 p.2 = s}

def rowS (C : ℝ) (k r f s : ℕ) (b g v Gam : ℝ) (Xi : ℕ → ℝ) : ℝ :=
  Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k (2 * r + 2) f s b g v Gam Xi +
    Gam ^ 2 * Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v Gam Xi

def oneT (C : ℝ) (k r f : ℕ) (b g Gam : ℝ) : ℝ :=
  C ^ f * Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C (2 * r + 2) f b ^ (C * ((2 * r + 2 : ℕ) : ℝ) ^ 3) * Gam *
    Real.exp (C * ((2 * r + 2 : ℕ) : ℝ) ^ 6 * f * Real.log b) *
    Real.sqrt ((C * g⁻¹ ^ (2 * r + 1) * ((k : ℝ) ^ r)⁻¹) ^ (k * f))

def ClassLe (Q : Set (τ × τ)) (B : ℝ) : Prop := X.Gam1 * RowsOther.ampSum X Q ≤ B

theorem ind_le_cover {f : τ × τ → ℝ} (hf : ∀ p, 0 ≤ f p) (S : Finset ℕ) (P : ℕ → Set (τ × τ))
    (P' Q : Set (τ × τ)) (hQ : Q ⊆ (⋃ s ∈ S, P s) ∪ P') (p : τ × τ) :
    Q.indicator f p ≤ ∑ s ∈ S, (P s).indicator f p + P'.indicator f p := by
  have hnn : ∀ (R : Set (τ × τ)), 0 ≤ R.indicator f p := fun R => Set.indicator_nonneg (fun q _ => hf q) p
  have hsum : 0 ≤ ∑ s ∈ S, (P s).indicator f p := Finset.sum_nonneg (fun i _ => hnn (P i))
  by_cases hp : p ∈ Q
  · rw [Set.indicator_of_mem hp]
    rcases (Set.mem_union _ _ _).1 (hQ hp) with h | h
    · obtain ⟨s, hsS, hps⟩ := Set.mem_iUnion₂.1 h
      have h1 : (P s).indicator f p = f p := Set.indicator_of_mem hps f
      have h2 : (P s).indicator f p ≤ ∑ s ∈ S, (P s).indicator f p :=
        Finset.single_le_sum (f := fun s => (P s).indicator f p) (fun i _ => hnn (P i)) hsS
      have h3 := hnn P'
      linarith
    · have h1 : P'.indicator f p = f p := Set.indicator_of_mem h f
      linarith
  · rw [Set.indicator_apply, if_neg hp]
    exact add_nonneg hsum (hnn P')

theorem amp_summable (hv : Summable (fun t => ‖X.vec t‖)) (Q : Set (τ × τ)) :
    Summable (Q.indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖)) := by
  exact (Summable.mul_of_nonneg hv hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).indicator Q

theorem ampSum_cover (hv : Summable (fun t => ‖X.vec t‖)) (S : Finset ℕ) (P : ℕ → Set (τ × τ))
    (P' Q : Set (τ × τ)) (hQ : Q ⊆ (⋃ s ∈ S, P s) ∪ P') :
    RowsOther.ampSum X Q ≤ ∑ s ∈ S, RowsOther.ampSum X (P s) + RowsOther.ampSum X P' := by
  have hs : ∀ R : Set (τ × τ), Summable (R.indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖)) :=
    fun R => amp_summable X hv R
  have hsum : Summable (fun p => ∑ s ∈ S, (P s).indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖) p +
      P'.indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖) p) :=
    (summable_sum fun s _ => hs (P s)).add (hs P')
  have hle := Summable.tsum_le_tsum
    (fun p => ind_le_cover (fun p => mul_nonneg (norm_nonneg (X.vec p.1)) (norm_nonneg (X.vec p.2))) S P P' Q hQ p)
    (hs Q) hsum
  unfold RowsOther.ampSum
  rw [Summable.tsum_add (summable_sum fun s _ => hs (P s)) (hs P'),
    Summable.tsum_finsetSum (fun s _ => hs (P s))] at hle
  exact hle

theorem pp_cover (k : ℕ) (hk : ∀ t t', X.s0 t t' ≤ k) :
    RowsOther.PP X ⊆ (⋃ s ∈ Finset.Icc 2 k, bigS X s) ∪ X.nsc X.genSet := by
  intro p hp
  unfold RowsOther.PP at hp
  rcases (Set.mem_union _ _ _).1 hp with h | h
  · have h' : p ∈ X.allPairs X.nzSet ∧ 2 ≤ X.s0 p.1 p.2 := h
    left
    refine Set.mem_iUnion₂.2 ⟨X.s0 p.1 p.2, Finset.mem_Icc.2 ⟨h'.2, hk p.1 p.2⟩, ?_⟩
    show p ∈ X.allPairs X.nzSet ∧ X.s0 p.1 p.2 = X.s0 p.1 p.2
    exact ⟨h'.1, rfl⟩
  · right
    exact h

theorem loopsAmp_of_classes (A C : ℝ) (k r f : ℕ) (b g v Gam : ℝ) (Xi : ℕ → ℝ) (dd : ℝ)
    (hG : 0 ≤ X.Gam1) (hv : Summable (fun t => ‖X.vec t‖)) (hk : ∀ t t', X.s0 t t' ≤ k)
    (hS : ∀ s, 2 ≤ s → s ≤ k → ClassLe X (bigS X s) (A * rowS C k r f s b g v Gam Xi * dd))
    (h1 : ClassLe X (X.nsc X.genSet) (A * oneT C k r f b g Gam * dd)) :
    RowsOther.LoopsAmp X A C k r f b g v Gam Xi dd := by
  refine ⟨amp_summable X hv _, ?_⟩
  have hc := ampSum_cover X hv (Finset.Icc 2 k) (bigS X) (X.nsc X.genSet) (RowsOther.PP X) (pp_cover X k hk)
  have hsum : ∑ s ∈ Finset.Icc 2 k, X.Gam1 * RowsOther.ampSum X (bigS X s) ≤
      ∑ s ∈ Finset.Icc 2 k, A * rowS C k r f s b g v Gam Xi * dd :=
    Finset.sum_le_sum fun s hs => hS s (Finset.mem_Icc.1 hs).1 (Finset.mem_Icc.1 hs).2
  have e : ∑ s ∈ Finset.Icc 2 k, A * rowS C k r f s b g v Gam Xi * dd =
      A * (∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k (2 * r + 2) f s b g v Gam Xi +
        Gam ^ 2 * ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v Gam Xi) * dd := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold rowS; ring
  calc X.Gam1 * RowsOther.ampSum X (RowsOther.PP X)
      ≤ X.Gam1 * (∑ s ∈ Finset.Icc 2 k, RowsOther.ampSum X (bigS X s) + RowsOther.ampSum X (X.nsc X.genSet)) :=
        mul_le_mul_of_nonneg_left hc hG
    _ = ∑ s ∈ Finset.Icc 2 k, X.Gam1 * RowsOther.ampSum X (bigS X s) +
          X.Gam1 * RowsOther.ampSum X (X.nsc X.genSet) := by rw [mul_add, Finset.mul_sum]
    _ ≤ ∑ s ∈ Finset.Icc 2 k, A * rowS C k r f s b g v Gam Xi * dd + A * oneT C k r f b g Gam * dd :=
        add_le_add hsum h1
    _ = _ := by rw [e]; unfold oneT; ring

end Gen

section Sizes

variable (D : D7) (large₂ : SizeData₂ D)

def unitM : ℝ := (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L

def gamCap (C : ℝ) : ℝ := Real.exp (min large₂.CGam C * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)

theorem unitM_nonneg : 0 ≤ unitM D large₂ := by
  unfold unitM
  have hL : 0 ≤ large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _
  exact mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)) hL

theorem gamCap_pos (C : ℝ) : 0 < gamCap D large₂ C := Real.exp_pos _

theorem gam_ratio (C : ℝ) :
    GamS D large₂ / gamCap D large₂ C = Real.exp ((large₂.CGam - min large₂.CGam C) * unitM D large₂) := by
  unfold Formalism.MainNotions.S.GamS gamCap unitM
  rw [← Real.exp_sub]
  congr 1
  ring

end Sizes

theorem params_at {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 C K₀ : ℝ}
    (h : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (X : HidaSetting D) (u : D.what₂.Word) (hCl : 4 ≤ Cl) (hCT : CT ≤ C)
    (hC : 1 ≤ C) (hK : K₀ ≤ C') :
    Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b (X.B.g : ℝ) D.host.v (NT D u) (gamCap D large₂ C) := by
  obtain ⟨_, h2, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h23, h24, _⟩ := h.1
  have h2' : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := h2
  have h23' : Formalism.MainNotions.S.Tr D u ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) := (h23 u).2
  have h24' : Cl ≤ (D.R.m : ℝ) := h24
  have hm : 4 ≤ D.R.m := by
    have : (4 : ℝ) ≤ D.R.m := by linarith
    exact_mod_cast this
  have hL := Formalism.MainNotions.BridgeLemma.d_one_le_L D large₂
  have hM : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
  have hK' : K₀ * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := by
    have := mul_le_mul_of_nonneg_right hK hM
    nlinarith
  have P := Formalism.MainNotions.BridgeLemma.parameters_of_hypotheses D large₂ h u hm (by linarith) (le_max_of_le_left hCT : CT ≤ max C large₂.CGam)
    (le_max_right _ _) hK'
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, _, _, _⟩ := P
  have hg : (X.B.g : ℝ) = gg D := by rw [X.g_eq]; unfold gg; push_cast; ring
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b D large₂
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith
  rw [← Formalism.MainNotions.BridgeLemma.d_m_eq D, hg]
  refine ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, ?_, ?_, ?_⟩
  · unfold NT
    have h1 : ((D.mem u).A.T : ℝ) ≤ large₂.sc.b ^ (C * (D.R.m : ℝ)) :=
      h23'.trans (Real.rpow_le_rpow_of_exponent_le hb1 (by gcongr))
    calc ((D.mem u).A.T : ℝ) ^ D.R.f ≤ (large₂.sc.b ^ (C * (D.R.m : ℝ))) ^ D.R.f := by
          have : (0 : ℝ) ≤ ((D.mem u).A.T : ℝ) := Nat.cast_nonneg _
          gcongr
      _ = large₂.sc.b ^ (C * (D.R.m : ℝ) * D.R.f) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  · unfold gamCap
    have := large₂.CGam_pos
    have h0 : 0 ≤ min large₂.CGam C := le_min this.le (by linarith)
    exact Real.one_le_exp (by positivity)
  · unfold gamCap
    rw [Formalism.MainNotions.BridgeLemma.d_log_b]
    exact Real.exp_le_exp.2 (by
      have := min_le_right large₂.CGam C
      have h5 : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := hM
      nlinarith)

theorem xi_nonneg {C : ℝ} {k m f : ℕ} {b v NT : ℝ} {Xi : ℕ → ℝ} (h : Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C k m f b v NT Xi)
    (s : ℕ) (h2 : 2 ≤ s) (hk : s ≤ k) : 0 ≤ Xi s := by
  obtain ⟨hA, hB⟩ := h
  by_cases hs : s + 2 ≤ k
  · exact (hA s h2 hs).1
  · exact (hB s (by omega)).1

theorem ndRow_nonneg {C : ℝ} {k m f s : ℕ} {b g v Gam : ℝ} {Xi : ℕ → ℝ} (hC : 0 ≤ C) (hb : 0 < b) (hg : 0 < g)
    (hv : 0 ≤ v) (hG : 0 ≤ Gam) (hX : 0 ≤ Xi s) : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k m f s b g v Gam Xi := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow
  have hH : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
    exact Real.rpow_nonneg hb.le _
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) hX) ?_)
    (Real.rpow_nonneg hH _)) ?_) hG
  · exact pow_nonneg (div_nonneg (by norm_num) hg.le) _
  · exact pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hv) _
  · exact pow_nonneg hC _
  · exact pow_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) _

theorem degRow_nonneg {C : ℝ} {k m f s : ℕ} {b g v Gam : ℝ} {Xi : ℕ → ℝ} (hC : 0 ≤ C) (hb : 0 < b) (hg : 0 < g)
    (hv : 0 ≤ v) (hG : 0 ≤ Gam) (hX : 0 ≤ Xi s) : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k m f s b g v Gam Xi := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow
  have hH : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
    exact Real.rpow_nonneg hb.le _
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) hX) ?_)
    (Real.rpow_nonneg hH _)) ?_) hG) (Real.exp_pos _).le) ?_
  · exact pow_nonneg (div_nonneg (by norm_num) hg.le) _
  · exact pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hv) _
  · exact pow_nonneg hC _
  · exact pow_nonneg (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) _
  · exact pow_nonneg (div_nonneg hC (Nat.cast_nonneg _)) _

theorem oneT_nonneg {C : ℝ} {k r f : ℕ} {b g Gam : ℝ} (hC : 0 ≤ C) (hb : 0 < b) (hG : 0 ≤ Gam) :
    0 ≤ oneT C k r f b g Gam := by
  unfold oneT
  have hH : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C (2 * r + 2) f b := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
    exact Real.rpow_nonneg hb.le _
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hC _) (Real.rpow_nonneg hH _)) hG)
    (Real.exp_pos _).le) (Real.sqrt_nonneg _)

theorem rho_le_cube {ρ : ℝ} (hρ : 1 ≤ ρ) : ρ ≤ ρ ^ 3 := by
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ ρ) (sub_nonneg.2 hρ)) (by linarith : (0:ℝ) ≤ ρ + 1)]

theorem scale_le {A₁ A₀ ρ R R' dd : ℝ} (h1 : 1 ≤ A₁) (hA : A₁ ≤ A₀) (hdd : 0 ≤ dd) (hR : R' ≤ ρ ^ 3 * R)
    (hR0 : 0 ≤ R) (hρ : 0 ≤ ρ) : A₁ * R' * dd ≤ A₀ * ρ ^ 3 * R * dd := by
  have hρ3 : 0 ≤ ρ ^ 3 * R := mul_nonneg (pow_nonneg hρ 3) hR0
  have h2 : A₁ * R' ≤ A₀ * (ρ ^ 3 * R) :=
    le_trans (mul_le_mul_of_nonneg_left hR (by linarith)) (mul_le_mul_of_nonneg_right hA hρ3)
  calc A₁ * R' * dd ≤ A₀ * (ρ ^ 3 * R) * dd := mul_le_mul_of_nonneg_right h2 hdd
    _ = A₀ * ρ ^ 3 * R * dd := by ring

theorem log_size {k f lk Cl L A₀ ρ : ℝ} (hk1 : 1 ≤ k) (hL : 1 ≤ L) (hCl0 : 0 < Cl) (hfl : Cl * L ≤ f * lk)
    (hClA : 3 + 6 * Real.log (3 * A₀) ≤ Cl) (hA : 1 ≤ A₀) (hρ1 : 1 ≤ ρ) (hlogρ : Real.log ρ ≤ k / 8) :
    6 * Real.log (3 * (A₀ * ρ ^ 3)) ≤ k * f * lk := by
  have hA3 : 0 < 3 * A₀ := by linarith
  have hρpos : 0 < ρ := by linarith
  have hlog : Real.log (3 * (A₀ * ρ ^ 3)) = Real.log (3 * A₀) + 3 * Real.log ρ := by
    rw [← mul_assoc, Real.log_mul hA3.ne' (pow_pos hρpos 3).ne', Real.log_pow]
    push_cast
    ring
  have hlA : 0 ≤ Real.log (3 * A₀) := Real.log_nonneg (by linarith)
  have hfl2 : Cl ≤ f * lk := le_trans (le_mul_of_one_le_right hCl0.le hL) hfl
  have h3 : 3 + 6 * Real.log (3 * A₀) ≤ f * lk := le_trans hClA hfl2
  have h4 : k * (3 + 6 * Real.log (3 * A₀)) ≤ k * (f * lk) := mul_le_mul_of_nonneg_left h3 (by linarith)
  rw [hlog]
  nlinarith [mul_nonneg (sub_nonneg.2 hk1) hlA, h4, hlogρ]

theorem hyp_nums {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 : ℝ} (h : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) :
    large₂.CGam * unitM D large₂ ≤ (D.R.k : ℝ) / 8 ∧ Cl * large₂.sc.L ≤ (D.R.f : ℝ) * Real.log D.R.k ∧ 0 < Cl := by
  have hS := h.1
  have h1 : 8 * large₂.CGam ≤ C' := hS.1
  have h2 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := hS.2.1
  have h6 : Cl * large₂.sc.L ≤ (D.R.f : ℝ) * Real.log D.R.k := hS.2.2.2.2.2.1
  have hp := h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hCl : 0 < Cl := hp.2.2.2.2
  have hU := unitM_nonneg D large₂
  refine ⟨?_, h6, hCl⟩
  have h8 : large₂.CGam * unitM D large₂ * 8 ≤ C' * unitM D large₂ := by
    nlinarith [mul_le_mul_of_nonneg_right h1 hU]
  have e : C' * unitM D large₂ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
    unfold unitM
    ring
  linarith

theorem ite_le {P : Prop} [h : Decidable P] {a n : ℕ} (ha : a ≤ n) : @ite ℕ P h a 0 ≤ n := by
  split <;> omega

theorem rowS_scale (C : ℝ) (k r f s : ℕ) (b g v Gc ρ : ℝ) (Xi : ℕ → ℝ) (hρ : 1 ≤ ρ)
    (h0 : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k (2 * r + 2) f s b g v Gc Xi) :
    rowS C k r f s b g v (ρ * Gc) Xi ≤ ρ ^ 3 * rowS C k r f s b g v Gc Xi := by
  have e1 : Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k (2 * r + 2) f s b g v (ρ * Gc) Xi =
      ρ * Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k (2 * r + 2) f s b g v Gc Xi := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow
    ring
  have e2 : Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v (ρ * Gc) Xi =
      ρ * Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k (2 * r + 2) f s b g v Gc Xi := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow
    ring
  have h3 := mul_le_mul_of_nonneg_right (rho_le_cube hρ) h0
  unfold rowS
  rw [e1, e2]
  nlinarith [h3]

theorem oneT_scale (C : ℝ) (k r f : ℕ) (b g Gc ρ : ℝ) (hρ : 1 ≤ ρ) (h0 : 0 ≤ oneT C k r f b g Gc) :
    oneT C k r f b g (ρ * Gc) ≤ ρ ^ 3 * oneT C k r f b g Gc := by
  have e : oneT C k r f b g (ρ * Gc) = ρ * oneT C k r f b g Gc := by
    unfold oneT
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (rho_le_cube hρ) h0

theorem corank_le_k {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) :
    ∀ t t', (Y.tO u u').s0 t t' ≤ D.R.k := by
  intro t t'
  exact ite_le (Nat.sub_le _ _)

section Closed

def RowsSC : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ A₀ C₀ : ℝ, 1 ≤ A₀ ∧ 1 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ,
    ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A → ConcTie X Y → (Y.tO u u').AbsConv →
      ∀ s, 2 ≤ s → s ≤ D.R.k →
        ClassLe (Y.tO u u') (bigS (Y.tO u u') s)
          (A₀ * rowS C D.R.k D.R.rS D.R.f s large₂.sc.b (X.B.g : ℝ) D.host.v (GamS D large₂)
            (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C) * ddC X Y u u')

def OneSC : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ A₀ C₀ : ℝ, 1 ≤ A₀ ∧ 1 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ,
    ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A → ConcTie X Y → (Y.tO u u').AbsConv →
        ClassLe (Y.tO u u') ((Y.tO u u').nsc (Y.tO u u').genSet)
          (A₀ * oneT C D.R.k D.R.rS D.R.f large₂.sc.b (X.B.g : ℝ) (GamS D large₂) * ddC X Y u u')

def XiSizesC : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ,
    ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cw cT CT C0 A →
        Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v (NT D u) (Formalism.MainNotions.BridgeLemma.XiB D large₂ u C)

end Closed

end Formalism.L2.SG.LoopsCut

namespace Formalism.L2.SG.LoopsCut

theorem xiSizesC_of (hS : Formalism.HermitianLatticesTheory.SiegelMassRatio) : XiSizesC := by
  intro Cg cb Cw cT CT C0 A
  have he : (1 : ℝ) ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    nlinarith
  refine ⟨408 * (Real.exp 1 * Real.pi), by linarith, fun C hC => ⟨0, 1, fun C' Cl _ hCl D large₂ u u' hH => ?_⟩⟩
  have hmax : max 1 (1 / Cl) ≤ 1 := max_le le_rfl (by rw [div_le_one (by linarith)]; exact hCl)
  have hM2 := Formalism.MainNotions.BridgeLemma₂.plane_mass_bound_parameters D large₂ u u' C' Cl Cg cb Cw cT CT C0 A 8
    (le_trans (mul_le_mul_of_nonneg_left hmax (by norm_num)) (by norm_num))
  have hX := Formalism.MainNotions.BridgeLemma.first_bound_of_mass_ratio D large₂ u u' C' Cl Cg cb Cw cT CT C0 A 8 408
    (Formalism.MainNotions.BridgeLemma.lattice_count_first_of_siegel hS D) hM2 (by norm_num) le_rfl hCl
  have hCX : |(408 : ℝ)| * max 1 |Real.exp 1 * Real.pi| ≤ C := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 408), abs_of_pos (by positivity), max_eq_right he]; exact hC
  have hXi := Formalism.MainNotions.BridgeLemma.xiHyp_of_stX D large₂ hH hX hCX (by linarith)
  rw [← Formalism.MainNotions.BridgeLemma.d_m_eq D]
  exact hXi

end Formalism.L2.SG.LoopsCut
