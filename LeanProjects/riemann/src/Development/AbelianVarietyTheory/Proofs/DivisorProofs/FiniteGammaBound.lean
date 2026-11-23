import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NotLossLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardFiniteSubgroupGLIntDvd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.LocalToGlobal.Divisibility.LinkDef

open NumberField

namespace GlobalTheory.GamLoss
variable {E : Type} [Field E] [NumberField E]

theorem card_dvd_of_inj {N : ℕ} {H : Type} [Group H] [Finite H] (ρ : H →* Matrix (Fin N) (Fin N) E)
    (hρ : Function.Injective ρ) :
    Nat.card H ∣ 8 ^ (Module.finrank ℚ E * N) * (2 * (Module.finrank ℚ E * N)).factorial := by
  classical
  let S : Set (Fin N → E) := Set.range fun p : H × Fin N => (ρ p.1).mulVec (Pi.single p.2 1)
  let L : Submodule (𝓞 E) (Fin N → E) := Submodule.span (𝓞 E) S
  have hfg : L.FG := ⟨(Set.finite_range _).toFinset, by rw [Set.Finite.coe_toFinset]⟩
  have hS1 : ∀ i : Fin N, (Pi.single i 1 : Fin N → E) ∈ L := fun i =>
    Submodule.subset_span ⟨(1, i), by
      show (ρ 1).mulVec _ = _
      rw [map_one, Matrix.one_mulVec]⟩
  have hspan : Submodule.span E (L : Set (Fin N → E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun E (Fin N)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (by simpa using hS1 i)
  have hL : ∀ h, ∀ x ∈ L, (ρ h).mulVec x ∈ L := by
    intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g, i⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(h * g, i), by
        show (ρ (h * g)).mulVec _ = (ρ h).mulVec ((ρ g).mulVec _)
        rw [map_mul, Matrix.mulVec_mulVec]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StabOrder.exists_faithful L hfg hspan ρ hρ hL
  have e := (MonoidHom.ofInjective hψ).toEquiv
  have := GlobalTheory.card_finite_subgroup_GL_int_dvd _ ψ.range (Finite.of_equiv _ e)
  rwa [← Nat.card_congr e] at this

end GlobalTheory.GamLoss

namespace GlobalTheory.GamLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FunObj

variable {D : D7}

theorem incA_inj' : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem bc_incA_injective (n : ℕ) : Function.Injective (Formalism.UG.bc (n := Fin n) (incA D)) := by
  intro a b e
  exact Units.ext (Matrix.ext fun i j => incA_inj' (by simpa [Formalism.UG.bc] using congrArg (fun g => (Units.val g) i j) e))

theorem exists_rat (V : HSp D) (q : GQ V) : ∃ u : GL (Fin V.rank) D.host.E, Formalism.UG.bc (incA D) u = matHom V q.1 := by
  obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 q.2)
  exact ⟨u, hu⟩

theorem gamOrd_zero_or_dvd (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (x : GfC V) :
    gamOrd V K x = 0 ∨ gamOrd V K x ∣ 8 ^ (Module.finrank ℚ D.host.E * V.rank) *
      (2 * (Module.finrank ℚ D.host.E * V.rank)).factorial := by
  rw [← GlobalTheory.ClassRegroup.card_stab]
  set H := Formalism.IndefR.Bridge.stab ((GlobalTheory.ClassRegroup.finPt V).comp (GQ V).subtype) (K.comap (finG V)) x
  by_cases hf : Finite H
  swap
  · left
    haveI : Infinite H := not_finite_iff_infinite.1 hf
    exact Nat.card_eq_zero_of_infinite
  right
  let φ := Formalism.UG.bc (n := Fin V.rank) (incA D)
  have hφ : Function.Injective φ := bc_incA_injective V.rank
  let ι : GQ V →* φ.range := ((matHom V).comp (GQ V).subtype).codRestrict φ.range fun q => by
    obtain ⟨u, hu⟩ := exists_rat V q
    exact ⟨u, hu⟩
  have hι : Function.Injective ι := by
    intro a b e
    have e1 := congrArg (fun z : φ.range => z.1) e
    exact Subtype.ext (Subtype.val_injective e1)
  let ρ0 : GQ V →* GL (Fin V.rank) D.host.E := (MonoidHom.ofInjective hφ).symm.toMonoidHom.comp ι
  let ρ : H →* Matrix (Fin V.rank) (Fin V.rank) D.host.E := (Units.coeHom _).comp (ρ0.comp H.subtype)
  have hρ : Function.Injective ρ := by
    intro a b e
    have e1 : ρ0 a.1 = ρ0 b.1 := Units.ext e
    have e2 : ι a.1 = ι b.1 := (MonoidHom.ofInjective hφ).symm.injective e1
    exact Subtype.ext (hι e2)
  exact card_dvd_of_inj ρ hρ

end GlobalTheory.GamLoss

namespace GlobalTheory.GamLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

variable {D : D7}

noncomputable def rk (D : D7) : ℕ := Module.finrank ℚ D.host.E * bigN D

noncomputable def mk (D : D7) : ℕ := 8 ^ rk D * (2 * rk D).factorial

theorem mk_pos (D : D7) : 0 < mk D := Nat.mul_pos (pow_pos (by norm_num) _) (Nat.factorial_pos _)

theorem rankX_le (D : D7) {j : ℕ} (hj : j ≤ D.R.m) : rankX D j ≤ bigN D := by
  have h1 : j * (D.R.t + 1) ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_right _ hj
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hs : sLen D = D.R.r + 6 := rfl
  simp only [rankX, rankP, nRk, bigN]
  rw [hs] at *
  have e : D.R.m * (D.R.t + (D.R.r + 6) + 1) = D.R.m * (D.R.r + 6 - 1) + D.R.m * (D.R.t + 1) + D.R.m := by
    rw [show D.R.r + 6 - 1 = D.R.r + 5 by omega]; ring
  rw [e]
  have : D.R.r + 1 = D.R.k + D.R.m := by omega
  omega

theorem rankV_le (D : D7) {i : ℕ} (hi : i ≤ D.R.m) : rankV D i D.R.m ≤ bigN D := by
  have h1 : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  simp only [rankV, bigN]
  have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
  rw [e]
  omega

theorem dvd_mk {n : ℕ} (hn : n ≤ bigN D) :
    8 ^ (Module.finrank ℚ D.host.E * n) * (2 * (Module.finrank ℚ D.host.E * n)).factorial ∣ mk D := by
  have h : Module.finrank ℚ D.host.E * n ≤ rk D := Nat.mul_le_mul_left _ hn
  exact mul_dvd_mul (Nat.pow_dvd_pow _ h) (Nat.factorial_dvd_factorial (by omega))

theorem gamOrd_zero_or_dvd_mk (V : HSp D) (hV : V.rank ≤ bigN D) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)))
    (x : GfC V) : gamOrd V K x = 0 ∨ gamOrd V K x ∣ mk D :=
  (gamOrd_zero_or_dvd V K x).imp_right fun h => h.trans (dvd_mk hV)

theorem lossLe_inv (w : PlL D) {g : ℕ} (hg : g = 0 ∨ g ∣ mk D) :
    LossLe w ((g : ℂ)⁻¹) (vw w (mk D : D.what₂.LL)) := by
  rcases hg with rfl | hg
  · exact ⟨0, by simp, Or.inl rfl⟩
  refine ⟨(g : D.what₂.LL)⁻¹, by simp, Or.inr ?_⟩
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_inv]
  have := Formalism.L2.DIV.vw_nat_le_of_dvd (K := D.what₂.LL) w (mk_pos D) hg
  push_cast
  exact_mod_cast neg_le_neg this

theorem lossLe_one (w : PlL D) : LossLe w 1 0 :=
  ⟨1, map_one _, Or.inr (by rw [Formalism.DivisionValues.ValuationRepresentative.vw_one]; simp)⟩

theorem lossLe_prod (w : PlL D) {ι : Type} (s : Finset ι) (z : ι → ℂ) {a : ℝ} (h : ∀ i ∈ s, LossLe w (z i) a) :
    LossLe w (∏ i ∈ s, z i) (s.card * a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lossLe_one w
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have := GlobalTheory.SumSize.Model.lossLe_mul (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    refine this.mono (le_of_eq ?_)
    push_cast; ring

theorem vw_mk_nonneg (w : PlL D) : (0 : ℝ) ≤ vw w (mk D : D.what₂.LL) := by
  have := Formalism.L2.DIV.vw_nat_le_of_dvd (K := D.what₂.LL) w (mk_pos D) (one_dvd _)
  rw [Nat.cast_one, Formalism.DivisionValues.ValuationRepresentative.vw_one] at this
  exact_mod_cast this

theorem loss_mk : Loss (fun w : PlL D => (2 * D.R.m + 1 : ℝ) * vw w (mk D : D.what₂.LL))
    ((2 * D.R.m + 1 : ℝ) * Real.log (mk D)) := by
  refine ⟨fun w => mul_nonneg (by positivity) (vw_mk_nonneg w), ?_, fun s => ?_⟩
  · have hf := FractionalIdeal.finite_factors (K := D.what₂.LL)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) (mk D : D.what₂.LL))
    rw [Filter.eventually_cofinite] at hf
    refine hf.subset fun w hw h0 => hw ?_
    change (2 * D.R.m + 1 : ℝ) * (vw w (mk D : D.what₂.LL) : ℝ) = 0
    rw [show vw w (mk D : D.what₂.LL) = 0 from h0]; simp
  · have := Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le (K := D.what₂.LL) s (mk D) (mk_pos D).ne'
    calc ∑ w ∈ s, lw w * ((2 * D.R.m + 1 : ℝ) * vw w (mk D : D.what₂.LL))
        = (2 * D.R.m + 1 : ℝ) * ∑ w ∈ s, lw w * vw w (mk D : D.what₂.LL) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)

end GlobalTheory.GamLoss

namespace GlobalTheory.GamLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SumSize GlobalTheory.RowTest
open Formalism.DivisionValues (vw lw)

variable {D : D7}

theorem f_le_bigN (D : D7) : D.R.f ≤ bigN D := by
  have h : D.R.f ≤ D.R.k := D.R.f_le_k
  unfold bigN; omega

theorem two_le_f (D : D7) : 2 ≤ D.R.f := by
  have : 0 < D.R.ord := D.R.ord_pos
  show 2 ≤ 2 * D.R.ord
  omega

theorem log_mk_le (D : D7) : Real.log (mk D) ≤ 30 * D.R.f * (bigN D : ℝ) ^ 2 := by
  have hd : Module.finrank ℚ D.host.E = 2 * D.R.f := by rw [GlobalTheory.StabOrder.finrank_host]; rfl
  have hfN := f_le_bigN D
  have hf2 := two_le_f D
  have hN : 1 ≤ bigN D := by omega
  have hrk : rk D = 2 * D.R.f * bigN D := by rw [rk, hd]
  set n := 2 * rk D with hn'
  have hn : n = 4 * D.R.f * bigN D := by rw [hn', hrk]; ring
  have hn1 : 1 ≤ n := by rw [hn]; exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have h8 : Real.log 8 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num); linarith
  have hfac : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    have h1 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    calc Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) :=
          Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) h1
      _ = n * Real.log n := by rw [Real.log_pow]
  have hfNr : (D.R.f : ℝ) ≤ bigN D := by exact_mod_cast hfN
  have hNr : (1 : ℝ) ≤ bigN D := by exact_mod_cast hN
  have hlog : Real.log n ≤ 4 * bigN D := by
    have h1 : (n : ℝ) ≤ (2 * bigN D : ℝ) ^ 2 := by
      rw [hn]; push_cast; nlinarith
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
    calc Real.log n ≤ Real.log ((2 * bigN D : ℝ) ^ 2) := Real.log_le_log hpos h1
      _ = 2 * Real.log (2 * bigN D : ℝ) := by rw [Real.log_pow]; push_cast; ring
      _ ≤ 2 * (2 * bigN D - 1) := by
          gcongr; exact Real.log_le_sub_one_of_pos (by positivity)
      _ ≤ 4 * bigN D := by linarith
  unfold mk
  push_cast
  rw [Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos _).ne'), Real.log_pow]
  have e1 : ((rk D : ℕ) : ℝ) = 2 * D.R.f * bigN D := by rw [hrk]; push_cast; ring
  have e2 : ((n : ℕ) : ℝ) = 4 * D.R.f * bigN D := by rw [hn]; push_cast; ring
  rw [← hn', e1]
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  have t1 : 2 * D.R.f * bigN D * Real.log 8 ≤ 2 * D.R.f * bigN D * 7 :=
    mul_le_mul_of_nonneg_left h8 (by positivity)
  have t2 : (n : ℝ) * Real.log n ≤ (n : ℝ) * (4 * bigN D) := mul_le_mul_of_nonneg_left hlog (by positivity)
  rw [e2] at t2
  have t3 : (D.R.f : ℝ) * bigN D ≤ D.R.f * (bigN D) ^ 2 := by nlinarith
  nlinarith

theorem sig_nonneg {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : Consts} (G : GridData L sc) : 0 ≤ sig G :=
  Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

theorem finGamAt_of {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : Formalism.IndefR.Links.RealDat D A Ks} (ch : Choice R)
    {C b : ℝ} (hC : 90 ≤ C) (hb : 1 ≤ b) (hlb : 1 ≤ Real.log b) : FinGamAt ch C b := by
  refine ⟨_, GlobalTheory.SumSize.Model.loss_mono loss_mk ?_, fun t w Φ β c => ?_⟩
  · have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
    have hs := sig_nonneg ch.G
    have hL := log_mk_le D
    have hP : (0 : ℝ) ≤ D.R.f * (bigN D : ℝ) ^ 2 := by positivity
    have hq : (1 : ℝ) ≤ (Real.log b + sig ch.G) * b := by nlinarith
    unfold bOne
    have hX : (1 : ℝ) ≤ D.R.m * ((Real.log b + sig ch.G) * b) := by nlinarith
    have h1 : (0 : ℝ) ≤ C * (D.R.f * (bigN D : ℝ) ^ 2) := by positivity
    have h3 : (2 * D.R.m + 1 : ℝ) * (D.R.f * (bigN D : ℝ) ^ 2) ≤ (3 * D.R.m) * (D.R.f * (bigN D : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) hP
    calc (2 * D.R.m + 1 : ℝ) * Real.log (mk D) ≤ (2 * D.R.m + 1 : ℝ) * (30 * D.R.f * (bigN D : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = 30 * ((2 * D.R.m + 1 : ℝ) * (D.R.f * (bigN D : ℝ) ^ 2)) := by ring
      _ ≤ 30 * ((3 * D.R.m) * (D.R.f * (bigN D : ℝ) ^ 2)) := by linarith
      _ = D.R.m * (90 * (D.R.f * (bigN D : ℝ) ^ 2)) := by ring
      _ ≤ D.R.m * (C * (D.R.f * (bigN D : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC hP) (by positivity)
      _ ≤ D.R.m * (C * (D.R.f * (bigN D : ℝ) ^ 2) * (D.R.m * ((Real.log b + sig ch.G) * b))) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right h1 hX) (by positivity)
      _ = _ := by ring
  · unfold GridChoice.invGam
    refine (GlobalTheory.SumSize.Model.lossLe_mul (lossLe_prod w Finset.univ _ (a := (vw w (mk D : D.what₂.LL) : ℝ)) ?_)
      (lossLe_prod w Finset.univ _ (a := (vw w (mk D : D.what₂.LL) : ℝ)) ?_)).mono (le_of_eq ?_)
    · intro j _
      exact lossLe_inv w (gamOrd_zero_or_dvd_mk _ (by rw [rank_top ch.G j.2.le]; exact rankX_le D j.2.le) _ _)
    · intro i _
      exact lossLe_inv w (gamOrd_zero_or_dvd_mk _
        (by rw [rank_grid ch.G (Nat.le_of_lt_succ i.2)]; exact rankV_le D (Nat.le_of_lt_succ i.2)) _ _)
    simp only [Finset.card_univ, Fintype.card_fin]
    push_cast; ring

end GlobalTheory.GamLoss

namespace GlobalTheory.GamLoss
open GlobalTheory.SumSize GlobalTheory.RowClaim

theorem finGamK : GlobalTheory.FunPr.Hypotheses₂ → FinGamK := by
  intro _
  refine ⟨0, fun CF _ => ⟨90, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ _ => ?_⟩⟩⟩
  have hL : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hb : (1 : ℝ) ≤ large₂.sc.b := Real.one_le_exp (by linarith)
  have hlb : (1 : ℝ) ≤ Real.log large₂.sc.b := by
    show (1 : ℝ) ≤ Real.log (Real.exp large₂.sc.L)
    rw [Real.log_exp]; exact hL
  exact finGamAt_of ch hC hb hlb

end GlobalTheory.GamLoss
