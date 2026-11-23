import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvectorMemSpanTwistedTraceImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDomainWeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLevelCharacterBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastWeightPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToNatFloorCast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds
import Formalism.LocalRingCardinality.NFLeTwoMulTSq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.NormAtAddLe

set_option synthInstance.maxHeartbeats 400000

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.LevDesc
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

namespace GlobalTheory.CovGminTop

section Abstract

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

theorem norm_sum_le_of_gram {N : (K →+* ℂ) → V → ℝ} (hG : HasGram N) (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    {ι : Type} (s : Finset ι) (f : ι → V) (σ : K →+* ℂ) : N σ (∑ i ∈ s, f i) ≤ ∑ i ∈ s, N σ (f i) := by
  letI : StarRing K := starRingOfComm
  obtain ⟨n, ⟨b, X⟩, h⟩ := hG
  have e : ∀ x, N σ x = Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk σ) x := fun x => by
    rw [(h _).2]
    rcases InfinitePlace.embedding_mk_eq σ with e | e
    · rw [e]
    · rw [e]; exact (hc σ x).symm
  simp only [e]
  exact PI.Dv.Tr.normAt_sum_le' b X _ s f

theorem char_val {H : Type} [Group H] [Finite H] (χ : H →* Kˣ) (h : H) :
    IsIntegral ℤ ((χ h : Kˣ) : K) ∧ ∀ σ : K →+* ℂ, ‖σ ((χ h : Kˣ) : K)‖ = 1 := by
  have hn : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h1 : ((χ h : Kˣ) : K) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  refine ⟨IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (h1 ▸ isIntegral_one), fun σ => ?_⟩
  have : ‖σ ((χ h : Kˣ) : K)‖ ^ Nat.card H = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_short_eigen {H : Type} [Group H] [Finite H] (st : H → V →ₗ[K] V)
    (hst : ∀ h h' x, st (h * h') x = st h' (st h x)) (χ : H →* Kˣ) (Λ : Submodule (𝓞 K) V) (hΛ : ∀ h, ∀ x ∈ Λ, st h x ∈ Λ)
    {N : (K →+* ℂ) → V → ℝ} (hG : HasGram N) (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (hs : ∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) (hi : ∀ h σ x, N σ (st h x) = N σ x)
    (s : Set V) (hsΛ : s ⊆ Λ) (hsp : Submodule.span K s = ⊤) (B : ℝ) (hB : ∀ y ∈ s, ∀ σ, N σ y ≤ B) :
    ∃ s' : Set V, (∀ y ∈ s', (y ∈ Λ ∧ ∀ h, st h y = ((χ h : Kˣ) : K) • y) ∧ ∀ σ, N σ y ≤ Nat.card H * B) ∧
      ∀ x, (∀ h, st h x = ((χ h : Kˣ) : K) • x) → x ∈ Submodule.span K s' := by
  classical
  letI := Fintype.ofFinite H
  refine ⟨_, ?_, GlobalTheory.eigenvector_mem_span_twistedTrace_image H K V st hst χ s hsp⟩
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨⟨Λ.sum_mem fun h _ => ?_, fun g => ?_⟩, fun σ => ?_⟩
  · rw [← map_inv]
    let a : 𝓞 K := ⟨_, (char_val χ h⁻¹).1⟩
    have := Λ.smul_mem a (hΛ h y (hsΛ hy))
    rwa [← algebraMap_smul K a] at this
  · beta_reduce
    rw [map_sum, Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulRight g) fun h => _ • _ • st h y]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [map_smul, ← hst, smul_smul, Equiv.coe_mulRight, map_mul, mul_inv, ← Units.val_mul, mul_left_comm, mul_inv_cancel, mul_one]
  · refine (norm_sum_le_of_gram hG hc _ _ σ).trans ?_
    rw [Nat.card_eq_fintype_card, ← nsmul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun h _ => ?_
    rw [hs, hi, ← map_inv, (char_val χ h⁻¹).2, one_mul]
    exact hB y hy σ

end Abstract

section Point

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem half_lt_laOf (τ : Psi p.T.Q.H) (k : Fin ((dat p i).p + (dat p i).q)) (hk : (k : ℕ) < (dat p i).p) :
    (((p.κ i).n / 2 : ℕ) : ℤ) < laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k := by
  have h := GlobalTheory.HolRead.lastPos_wtA_of_kapIs D p.T p.κ p.fw.laws p.fw.kap i τ.1 τ.2
  have hm : (dat p i).mult τ.1 = (dat p i).p := by
    unfold Datum.mult
    exact if_pos τ.2
  rw [hm] at h
  have h2 : wtA (p.κ i) (τ.1, (dat p i).p - 1) ≤ wtA (p.κ i) (τ.1, k) := (dom_wtA (p.κ i)).1 τ.1 (show (k : ℕ) ≤ _ by omega)
  have h3 := h (by omega)
  unfold laOf weightOf
  rw [if_pos hk]
  beta_reduce
  omega

theorem one_le_kap (hp : 1 ≤ (dat p i).p) : 1 ≤ kap p i := by
  have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hne : Nonempty (Psi p.T.Q.H) := (Nat.card_pos_iff.1 (by rw [WtShape.card_psi p]; exact hf)).1
  obtain ⟨τ⟩ := hne
  have h := half_lt_laOf p i τ ⟨0, by omega⟩ hp
  have h1 : (1 : ℤ) ≤ laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ ⟨0, by omega⟩ := by omega
  have h2 : (1 : ℝ) ≤ laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ ⟨0, by omega⟩ := by exact_mod_cast h1
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  exact (h2.trans (le_abs_self _)).trans (Finset.single_le_sum (f := fun k => |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ _))

theorem gminAt_of_gens (Y : Cov p i) (hpq : 1 ≤ (dat p i).p + (dat p i).q) (hA : Y.d.l₂.A.Coprime Y.d.l₂.M)
    (hC : KeepsCusp Y.U (Gk p i))
    (hk : ∀ (γ : LevelAut (dat p i) Y.d.l₂) (f g : Y.V (Gk p i)), (g : Rul Y.d.Xo₂ Y.d.c₂) = pull Y.d.Xo₂ Y.d.c₂ γ f →
      (f ∈ latW Y.U (Gk p i) → g ∈ latW Y.U (Gk p i)) ∧ ∀ σ, Y.nrm (Gk p i) σ g = Y.nrm (Gk p i) σ f)
    (hG : Y.GoodAt (Gk p i)) (S : Subgroup (LevelAut (dat p i) Y.d.l₂)) (χ : S →* (Y.d.c₂.F)ˣ)
    (hN : latDeep p i Y = chiLat S Y.U (Gk p i) χ) (s : Set (Y.V (Gk p i))) (hs : s ⊆ latW Y.U (Gk p i))
    (hsp : Submodule.span Y.d.c₂.F s = ⊤) (B PP : ℝ) (hB : ∀ y ∈ s, ∀ σ, Y.nrm (Gk p i) σ y ≤ Real.exp B)
    (hPP : Real.log (Nat.card S) + B ≤ PP * kap p i) : GminAt p i Y PP := by
  let st : S → Y.V (Gk p i) →ₗ[Y.d.c₂.F] Y.V (Gk p i) := fun h =>
    (pull Y.d.Xo₂ Y.d.c₂ (h : LevelAut (dat p i) Y.d.l₂)).toLinearMap.restrict (hC h)
  obtain ⟨s', h1, h2⟩ := exists_short_eigen st
    (fun h h' x => Subtype.ext ((isRightAct_pull (Xo := Y.d.Xo₂) (c := Y.d.c₂) hpq hA).2 h h' x)) χ (latW Y.U (Gk p i))
    (fun h x hx => (hk h x _ rfl).1 hx) hG.1
    (fun σ f => by rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ])
    (fun σ a x => petW_smul _ _ _ _ _ σ a _) (fun h σ x => (hk h x _ rfl).2 σ) s hs hsp _ hB
  refine ⟨s', fun y hy => ?_, fun y hy σ => ((h1 y hy).2 σ).trans ?_, fun x hx => h2 x fun h => Subtype.ext ?_⟩
  · rw [hN]
    exact (mem_chiLat S Y.U _).2 ⟨(h1 y hy).1.1, fun h => congrArg Subtype.val ((h1 y hy).1.2 h)⟩
  · have hc : (0 : ℝ) < Nat.card S := by exact_mod_cast Nat.card_pos
    rw [← Real.exp_log hc, ← Real.exp_add]
    exact Real.exp_le_exp.2 hPP
  · rw [hN] at hx
    exact ((mem_chiLat S Y.U _).1 hx).2 h

end Point

theorem num_step {C Z l k PP : ℝ} (hC : 0 ≤ C) (hl : C + 45 ≤ Z) (hk : 1 ≤ k) (hPP : Z ^ 12 ≤ PP) (h : l ≤ 45 * Z ^ 2) :
    l + C * Z ^ 2 * k ≤ PP * k := by
  have h1 : 1 ≤ Z := by linarith
  have h2 : Z ^ 3 ≤ Z ^ 12 := pow_le_pow_right₀ h1 (by norm_num)
  have h3 : (C + 45) * Z ^ 2 ≤ Z ^ 3 := by
    rw [pow_succ' Z 2]; exact mul_le_mul_of_nonneg_right hl (by positivity)
  have h4 : (C + 45) * Z ^ 2 * k ≤ PP * k := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h5 : 45 * Z ^ 2 ≤ 45 * Z ^ 2 * k := le_mul_of_one_le_right (by positivity) hk
  linarith

theorem gmin : Hypotheses2 → Gram → DeepGood → Size → Gmin := by
  intro hP hGr hDG hS
  obtain ⟨C, hC, hg⟩ := GlobalTheory.T.even_domain_weight_bound hP
  refine Closed.imp (((GlobalTheory.T.weight_parameter_strict_antitone hS).and (GlobalTheory.T.size_bounds_for_family hS)).and ((GlobalTheory.T.lattice_level_character_bound hP hGr hDG).and hDG)) ?_
  rintro eps Fm CH - ⟨⟨⟨_, -, h1⟩, _, -, h2⟩, ⟨_, -, h3⟩, _, -, h4⟩
  obtain ⟨x1, h5⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (C + 45)
  obtain ⟨x0, h⟩ := (h1.and h2).and (h3.and h4)
  refine ⟨0, le_rfl, max x0 x1, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := h x hx ((le_max_left _ _).trans hle) ι p hp
  obtain ⟨b1, b2, b3, -⟩ := a1 i hi
  obtain ⟨c1, c2, c3, c4, c5, c6, -, -, c7, c8, -, c9, c10, -⟩ := a2 i hi Y hY
  obtain ⟨fr, ψ, -, d1, d2, d3⟩ := a3 i hi Y hY
  have hL := (h5 x ((le_max_right _ _).trans hle) ι).2.2.1
  have hn : 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 4 ≤ (p.κ i).n := by
    rw [WtShape.cols_eq]; exact (Fm.parT x hx ι).nV_ge
  obtain ⟨s, e1, e2, e3⟩ := hg _ p.T c1 _ b1 b2 b3 c2 Y _ _ hY.1 _ c3 c4 c5 c6 le_rfl (wtA (p.κ i)) (p.κ i).n
    (dom_wtA _) (p.κ i).n_even hn (half_lt_laOf p i) (c9.trans (by linarith))
  obtain ⟨k1, k2⟩ := GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm _ p.T c1 _ b1 b2 b3 c2 Y _ _ hY.1 (Gk p i)
    ((Int.even_coe_nat _).2 (p.κ i).n_even)
  refine gminAt_of_gens p i Y (by omega) d1.coprime k1 k2 (a4 i hi Y hY).1 _ _ d2 s e1 e2 _ _ (fun y hy σ => (e3 y hy σ).1)
    (num_step hC (hL.trans ?_) (one_le_kap p i b1) c10 d3)
  have f1 : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.f)
  have f2 : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r)
  exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le f1 f2)

end GlobalTheory.CovGminTop
