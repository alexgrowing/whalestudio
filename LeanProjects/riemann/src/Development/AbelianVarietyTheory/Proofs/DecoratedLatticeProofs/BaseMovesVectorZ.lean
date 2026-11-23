import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRedIffIsPat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LamEqOfRed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselTranslateVector
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroUniformizerFrameUnipotentAndEmbedGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FunctionalValuesIntegralVectorsOfIntegerVectors
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.LocMod Matrix

noncomputable section

namespace GlobalTheory.MiTop.MoveZ

section Two

variable {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem pr_e (q : SplitPt D k) : q.pr q.e = 1 := by
  have h := q.sec_pr 1
  rw [map_one, mul_one] at h
  rw [← h, q.pr_sec]

theorem e_mul_sec (q : SplitPt D k) (x : k) : q.e * q.sec x = q.sec x := by
  rw [← q.sec_pr, q.pr_sec]

theorem sec_mul_sec (q : SplitPt D k) (x y : k) : q.sec (x * y) = q.sec x * q.sec y := by
  have h := q.sec_pr (q.sec x * q.sec y)
  rw [map_mul, q.pr_sec, q.pr_sec, ← mul_assoc, e_mul_sec] at h
  exact h

def chg (q : SplitPt D k) (q' : SplitPt D k') (h : q.e = q'.e) : k' →+* k where
  toFun x := q.pr (q'.sec x)
  map_one' := by
    have h1 := q'.sec_pr 1
    rw [map_one, mul_one] at h1
    rw [h1, ← h, pr_e]
  map_mul' x y := by rw [sec_mul_sec, map_mul]
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add, map_add]

theorem sec_chg (q : SplitPt D k) (q' : SplitPt D k') (h : q.e = q'.e) (x : k') : q.sec (chg q q' h x) = q'.sec x := by
  change q.sec (q.pr (q'.sec x)) = _
  rw [q.sec_pr, h, e_mul_sec]

theorem chg_pr (q : SplitPt D k) (q' : SplitPt D k') (h : q.e = q'.e) (a : AE D) : chg q q' h (q'.pr a) = q.pr a := by
  change q.pr (q'.sec (q'.pr a)) = _
  rw [q'.sec_pr, ← h, map_mul, pr_e, one_mul]

theorem chg_le (q : SplitPt D k) (q' : SplitPt D k') (h : q.e = q'.e) (x : k') :
    valuation k (chg q q' h x) ≤ 1 ↔ valuation k' x ≤ 1 := by
  have h1 := q.int_iff (chg q q' h x)
  rw [sec_chg, ← q'.int_iff] at h1
  exact h1

theorem chg_lt (q : SplitPt D k) (q' : SplitPt D k') (h : q.e = q'.e) (x : k') (hx : valuation k (chg q q' h x) < 1) :
    valuation k' x < 1 := by
  by_cases h0 : x = 0
  · subst h0; simp
  by_contra hn
  have h1 : valuation k' x⁻¹ ≤ 1 := by
    rw [map_inv₀]; exact inv_le_one_of_one_le₀ (not_lt.1 hn)
  have h2 := (chg_le q q' h x⁻¹).2 h1
  have h3 : chg q q' h x * chg q q' h x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ h0, map_one]
  have h4 : valuation k (chg q q' h x * chg q q' h x⁻¹) < 1 := by
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_left h2 zero_le').trans_lt (by rwa [mul_one])
  rw [h3, map_one] at h4
  exact lt_irrefl _ h4

theorem unif_ratio (q : SplitPt D k) (q' : SplitPt D k') {PP : Formalism.L2.DIV.Pl D.host.E}
    (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (h : q.e = q'.e) (Ψ) (ψ : AddChar k Circle)
    (ψ' : AddChar k' Circle) (hψ : (ofSplit q).IsChar Ψ ψ) (hψ' : (ofSplit q').IsChar Ψ ψ')
    (hc : GlobalTheory.SplitWeil.HasConductor ψ 1) (ϖ : kˣ) (ϖ' : k'ˣ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (hu' : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ')
    (hz : ∀ z : 𝓞 D.host.E, (ψ (((ϖ⁻¹ : kˣ) : k) * (ofSplit q).pr (z : D.host.E)) : ℂ) =
      ψ' (((ϖ'⁻¹ : k'ˣ) : k') * (ofSplit q').pr (z : D.host.E))) :
    valuation k ((ϖ : k) * chg q q' h ((ϖ'⁻¹ : k'ˣ) : k') - 1) < 1 := by
  have hϖ : valuation k (ϖ : k) < 1 := (hu _).2 le_rfl
  have hone : ∀ y : k, valuation k y ≤ 1 → ψ y = 1 := fun y hy => (hc 1).2 le_rfl y (by simpa using hy)
  have hcomp : ∀ x : k', ψ (chg q q' h x) = ψ' x := fun x => Subtype.ext (by
    have a := hψ (chg q q' h x)
    have b := hψ' x
    rw [show (ofSplit q).ι (chg q q' h x) = (ofSplit q').ι x from sec_chg q q' h x] at a
    exact a.trans b.symm)
  set a := chg q q' h ((ϖ'⁻¹ : k'ˣ) : k') with ha
  have hint : valuation k ((ϖ : k) * a) ≤ 1 := by
    have e1 : chg q q' h (chg q' q h.symm (ϖ : k)) = (ϖ : k) := by
      change chg q q' h (q'.pr (q.sec _)) = _
      rw [chg_pr, q.pr_sec]
    have h1 := (hu' _).1 (chg_lt q q' h (chg q' q h.symm (ϖ : k)) (by rw [e1]; exact hϖ))
    rw [← e1, ha, ← map_mul, chg_le, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    exact mul_inv_le_one_of_le₀ h1 zero_le'
  set d : k := a - ((ϖ⁻¹ : kˣ) : k) with hd
  have hdϖ : (ϖ : k) * d = (ϖ : k) * a - 1 := by rw [hd, mul_sub, Units.mul_inv]
  have hdint : valuation k ((ϖ : k) * d) ≤ 1 := by
    rw [hdϖ]; exact Valuation.map_sub_le _ hint (by simp)
  have hkill : ∀ y : k, valuation k y ≤ 1 → ψ (d * y) = 1 := fun y hy => by
    obtain ⟨z, hz1⟩ := q.exists_int_approx he (u := y) hy
    have h1 : ψ (d * q.pr (incA D (z : D.host.E))) = 1 := by
      have h2 : ψ (((ϖ⁻¹ : kˣ) : k) * q.pr (incA D (z : D.host.E))) = ψ (a * q.pr (incA D (z : D.host.E))) := by
        rw [ha, ← chg_pr q q' h, ← map_mul, hcomp, chg_pr]
        exact Subtype.ext (hz z)
      rw [hd, sub_mul, AddChar.map_sub_eq_div, h2, div_self']
    have h3 : ψ (d * (y - q.pr (incA D (z : D.host.E)))) = 1 := by
      refine hone _ ?_
      rw [map_mul]
      refine le_trans (mul_le_mul_of_nonneg_left ((hu _).1 hz1) zero_le') ?_
      rw [← map_mul, mul_comm]; exact hdint
    rw [show d * y = d * q.pr (incA D (z : D.host.E)) + d * (y - q.pr (incA D (z : D.host.E))) by ring,
      AddChar.map_add_eq_mul, h1, h3, mul_one]
  have hd1 : valuation k d ≤ 1 := by
    by_cases h0 : d = 0
    · rw [h0]; simp
    have := (hc d).1 fun y hy => by
      rw [show y = d * (y * d⁻¹) by field_simp]
      refine hkill _ ?_
      rw [map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ hy zero_le'
    simpa using this
  rw [← hdϖ, map_mul]
  exact (mul_le_mul_of_nonneg_left hd1 zero_le').trans_lt (by rwa [mul_one])

theorem exists_theta (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (t : k)
    (ht : valuation k (t - 1) < 1) :
    ∃ (θ : Formalism.IndefR.Lev.EAf D) (hθ : θ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
      Formalism.L2.DIV.resS D.host.F PP ⟨θ, hθ⟩ = 1 ∧ toEAf D q.e * θ = toEAf D (q.sec t) := by
  have h1 : toEAf D (q.sec (t - 1)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have := (q.pr_mem_iff (q.sec (t - 1))).1 (by rw [q.pr_sec]; exact ht.le)
    rwa [← map_mul, e_mul_sec] at this
  obtain ⟨s, hs⟩ : ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, s.1 = toEAf D (q.sec (t - 1)) := ⟨⟨_, h1⟩, rfl⟩
  refine ⟨(1 + s).1, (1 + s).2, ?_, ?_⟩
  · have h2 : Formalism.L2.DIV.resS D.host.F PP s = 0 :=
      (q.resS_eq_zero_iff he s).2 (by rw [hs, q.prF_toEAf, q.pr_sec]; exact ht)
    rw [Subtype.coe_eta, map_add, h2, map_one, add_zero]
  · have h1 := q.sec_pr 1
    rw [map_one, mul_one] at h1
    have h2 : q.e * (1 + q.sec (t - 1)) = q.sec t := by
      rw [mul_add, mul_one, e_mul_sec, ← h1, ← map_add, add_sub_cancel]
    have h3 : (1 + s).1 = toEAf D (1 + q.sec (t - 1)) := by
      rw [Subring.coe_add, OneMemClass.coe_one, hs]
      exact ((congrArg₂ (· + ·) (toEAf D).map_one rfl).symm).trans ((toEAf D).map_add _ _).symm
    exact (congrArg (toEAf D q.e * ·) h3).trans (((toEAf D).map_mul _ _).symm.trans (congrArg (toEAf D) h2))

theorem pow_sub_one_lt {t : k} (ht : valuation k (t - 1) < 1) (n : ℕ) : valuation k (t ^ n - 1) < 1 := by
  have h1 : valuation k t ≤ 1 := by
    rw [show t = (t - 1) + 1 by ring]
    exact Valuation.map_add_le _ ht.le (by simp)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show t ^ (n + 1) - 1 = t * (t ^ n - 1) + (t - 1) by ring]
    refine Valuation.map_add_lt _ ?_ ht
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right h1 zero_le').trans_lt (by rwa [one_mul])

theorem e_mul_of_prF (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (x y : Formalism.IndefR.Datum.EAf D) (s : k) (h : q.prF he x = s * q.prF he y) : toEAf D q.e * x = toEAf D (q.sec s) * y := by
  obtain ⟨a, rfl⟩ := GlobalTheory.ResLoc.toEAf_surj x
  obtain ⟨b, rfl⟩ := GlobalTheory.ResLoc.toEAf_surj y
  rw [q.prF_toEAf, q.prF_toEAf] at h
  rw [← map_mul, ← map_mul, ← q.sec_pr, h, sec_mul_sec, q.sec_pr, ← mul_assoc, mul_comm (q.sec s), e_mul_sec]

end Two

theorem map_inv_mulVec {R k n : Type} [CommRing R] [CommRing k] [Fintype n] [DecidableEq n] (π : R →+* k) (A : GL n R)
    (z col : n → R) (s : k) (h : ∀ r, π (z r) = s * π ((A.val *ᵥ col) r)) (r : n) :
    π (((A⁻¹).val *ᵥ z) r) = s * π (col r) := by
  have e : col = (A⁻¹).val *ᵥ (A.val *ᵥ col) := by rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  conv_rhs => rw [e]
  generalize A.val *ᵥ col = w at h
  simp only [mulVec, dotProduct, map_sum, map_mul, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

def elem {K : Type} [CommRing K] {r : ℕ} (a b : Fin r) (h : a ≠ b) (y : K) : GL (Fin r) K :=
  ⟨transvection a b y, transvection a b (-y), by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

theorem edgeSum_elem {K : Type} [CommRing K] {r κ : ℕ} (a b : Fin r) (h : a ≠ b) (hab : GlobalTheory.chainEdge κ a b) (y : K)
    [DecidableRel (GlobalTheory.chainEdge κ (r := r))] : Formalism.L2.DIV.edgeSum (GlobalTheory.chainEdge κ) (elem a b h y) = y := by
  have key : ∀ i j : Fin r, (if GlobalTheory.chainEdge κ i j then (elem a b h y).val i j else 0) = if i = a ∧ j = b then y else 0 := by
    intro i j
    change (if _ then transvection a b y i j else 0) = _
    by_cases hE : GlobalTheory.chainEdge κ i j
    · have hij : i ≠ j := fun e => by have := hE.1; omega
      rw [if_pos hE, transvection, Matrix.add_apply, one_apply_ne hij, zero_add, single_apply]
      simp only [eq_comm]
    · rw [if_neg hE, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hE hab
  unfold Formalism.L2.DIV.edgeSum
  simp only [key]
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem isPat_elem {K : Type} [CommRing K] {r ρ κ : ℕ} (a b : Fin r) (h : a ≠ b) (hab : GlobalTheory.SymRes.FreePos ρ κ a.val b.val)
    (y : K) : GlobalTheory.SymRes.IsPat ρ κ (elem a b h y) := by
  intro i j hij
  change transvection a b y i j = _
  rw [transvection, Matrix.add_apply, single_apply, if_neg, add_zero]
  rintro ⟨rfl, rfl⟩
  exact hij hab

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem exists_char (W : RealPack ex) (PP : (pk W).Pg) : ∃ χ : 𝓞 D.host.E → ℂ, ∀ u (f : FamCh W u) (v : VCom f.c) (n : ℕ)
    (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GRead f G pl → ∀ i, pl i = PP → ∀ z : 𝓞 D.host.E,
      ((G i).S.ψ ((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k) * (ofSplit (G i).q).pr (z : D.host.E)) : ℂ) = χ z := by
  classical
  have hr : 2 ≤ D.R.r := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hk : 2 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  let a : Fin D.R.r := ⟨0, by omega⟩
  let b : Fin D.R.r := ⟨1, by omega⟩
  have hab : a ≠ b := fun e => by have := congrArg Fin.val e; simp [a, b] at this
  let g : 𝓞 D.host.E → ∀ P : (pk W).Pg, GL (Fin D.R.r) (kP P.1) := fun z P =>
    elem a b hab (Ideal.Quotient.mk P.1.asIdeal (if P = PP then z else 0))
  refine ⟨fun z => if h : g z ∈ (lvP W).H then (((lvP W).chi ⟨g z, h⟩ : ℂˣ) : ℂ) else 0, ?_⟩
  intro u f v n G pl hG i hi z
  have hex : ∀ j, ∃ x, GlobalTheory.LevZero.Red (G j) (pl j).1 x (g z (pl j)) := fun j =>
    (GlobalTheory.LevZero.exists_red_iff_isPat (G j) (pl j).1 (hG.idem j).1 _).2
      (isPat_elem a b hab (Or.inl ⟨by simp only [a]; omega, by simp only [b]; omega, by simp [a, b]⟩) _)
  have hmem : g z ∈ (lvP W).H := (hG.lev (g z)).1.2 hex
  choose x hx using hex
  have hchi := (hG.lev (g z)).2 hmem x hx
  have hlam : ∀ j, (((G j).S.P.lam (x j) : ℂˣ) : ℂ) = (G j).S.ψ ((((G j).S.ϖ⁻¹ : (G j).kˣ) : (G j).k) *
      (ofSplit (G j).q).pr ((if pl j = PP then z else 0 : 𝓞 D.host.E) : D.host.E)) := fun j =>
    GlobalTheory.LevZero.lam_eq_of_red (G j) (pl j).1 (hG.idem j).1 (x j) _ (hx j) _
      (edgeSum_elem a b hab ⟨rfl, by simp only [a]; omega⟩ _).symm
  simp only [dif_pos hmem]
  rw [hchi, Units.coe_prod, Finset.prod_eq_single i (fun j _ hj => ?_) (by simp), hlam, if_pos hi]
  rw [hlam, if_neg (fun e => hj (pl.injective (e.trans hi.symm)))]
  simp [Place.pr]

theorem sc_even {c : Comm D} {v : VCom c} (G : GLoc v) (n : ℕ) : G.sc (2 * n) = G.sc 0 * (ofSplit G.q).xi ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, G.sc_step, ih, pow_succ, mul_assoc]

theorem sc_mul_mu {c : Comm D} {v : VCom c} (G : GLoc v) (μ lam : D.host.E) (hμ : μ * lam = -D.host.xi0 ^ (D.R.m / 2))
    (ζ₀ : Fin c.Lz.rank → D.host.E) (hτ : ∀ j h, v.τ j h *ᵥ ζ₀ = lam • (c.bes j 0 h).ζ)
    (hz : G.z₀ = fun r => (ofSplit G.q).pr (ζ₀ r)) : G.sc 0 * (ofSplit G.q).pr μ = 1 := by
  have hs := G.hs
  have hodd := G.S.odd
  have h : G.s + 2 * 0 + 2 = D.R.m := by omega
  let π : D.host.E →+* G.k := G.q.pr.comp (incA D)
  have hπ : (ofSplit G.q).pr = π := rfl
  have h1 := G.tau h
  rw [hz, hπ] at h1
  have h2 : ∀ i, π lam * π ((c.bes G.s 0 h).ζ i) = -((ofSplit G.q).xi * G.sc G.s) * π ((c.bes G.s 0 h).ζ i) := fun i => by
    have a := congrFun h1 i
    have b := π.map_mulVec (v.τ G.s h) ζ₀ i
    rw [hτ] at b
    exact ((map_mul π _ _).symm.trans b).trans a
  have h3 : ∃ i, (c.bes G.s 0 h).ζ i ≠ 0 := by
    by_contra hn
    push_neg at hn
    have a := G.hz_unit G.s 0 h
    have b : (c.B G.s 0 h).ζ = 0 := funext hn
    rw [Place.hz, b, hπ] at a
    simp at a
  obtain ⟨i, hi⟩ := h3
  have h4 := mul_right_cancel₀ ((map_ne_zero π).2 hi) (h2 i)
  have hxi : (ofSplit G.q).xi = π D.host.xi0 := rfl
  have hne : π D.host.xi0 ≠ 0 := (map_ne_zero π).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have h5 := congrArg π hμ
  have h6 : G.sc G.s = G.sc 0 * π D.host.xi0 ^ G.S.ρ := by
    have := sc_even G G.S.ρ
    rwa [show 2 * G.S.ρ = G.s by omega] at this
  rw [map_mul, h4, map_neg, map_pow, hxi, h6, show D.R.m / 2 = G.S.ρ + 1 by omega] at h5
  rw [hπ]
  refine mul_right_cancel₀ (pow_ne_zero (G.S.ρ + 1) hne) ?_
  linear_combination (-1 : G.k) * h5

set_option maxHeartbeats 1000000 in

theorem base_inv_alt (W : RealPack ex) {u : D.what₂.Word} (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg) (hG : GRead f G pl)
    (hB : BotTie f B v o G) (i : Fin n) : ∃ j₀ : Fin (Yc D 0).rank, j₀.val = D.R.k + D.R.rS ∧ ∀ r,
      toEAf D (G i).q.e * (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *ᵥ
        (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
          (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))))) r =
      toEAf D ((G i).q.sec (((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k)) ^ (D.R.rS + 1))) * ((pk W).βY 0).val r j₀ := by
  have hs := (G i).hs
  have hodd := (G i).S.odd
  have hρ : D.R.rS = (G i).S.ρ := by unfold Ranks.rS; omega
  have h₀ : 0 + 2 * D.R.rS + 2 = D.R.m := by omega
  have he := (hG.idem i).1
  obtain ⟨μ, lam, hμ, hv, hτ⟩ := hB.norm
  have hsc := sc_mul_mu (G i) μ lam hμ o.ζ₀ hτ (hB.last i)
  obtain ⟨e, hord, hM⟩ := hG.frame i 0 ((G i).s + 1) (Nat.zero_add _)
  let p : Fin ((G i).s + 1) := ⟨D.R.rS, by omega⟩
  refine ⟨e (.inl (.inr p)), hord _, fun r => ?_⟩
  refine e_mul_of_prF (G i).q he _ _ _ ?_
  refine map_inv_mulVec ((G i).q.prF he) _ _ (fun r => ((pk W).βY 0).val r (e (.inl (.inr p)))) _ (fun r => ?_) r
  choose lf hlf using fun x : Formalism.IndefR.Datum.EAf D => GlobalTheory.ResLoc.toEAf_surj x
  have h1 := congrFun (congrFun (hM (((pk W).βY 0).val.map lf) (Matrix.ext fun a b => hlf _)) r) (e (.inl (.inr p)))
  have h2 : (G i).q.prF he (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0)).val *ᵥ
      fun r => ((pk W).βY 0).val r (e (.inl (.inr p)))) r) =
      (ofSplit (G i).q).π ((Formalism.L2.Theta.mt (Yc D 0) (f.g.b 0) * ((pk W).βY 0).val.map lf) r (e (.inl (.inr p)))) := by
    rw [Matrix.mul_apply, map_sum, mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hlf (((pk W).βY 0).val a _)]
    exact (congrArg ((G i).q.prF he) ((toEAf D).map_mul _ _).symm).trans ((G i).q.prF_toEAf he _)
  have h3 : (ofSplit (G i).q).π ((Formalism.L2.Theta.mt (Yc D 0) (f.g.b 0) * ((pk W).βY 0).val.map lf) r (e (.inl (.inr p)))) =
      ((G i).FY 0 ((G i).s + 1) (Nat.zero_add _)).β r (.inr p) * ((G i).S.ϖ : (G i).k) ^ (D.R.rS + 1) := by
    refine h1.trans ?_
    rw [submatrix_apply, Equiv.symm_apply_apply, GlobalTheory.LevZeroUp.bas_val, mul_diagonal]
    rw [GlobalTheory.StepData.standardOrderExtendedBasis_apply_low_block (Fin D.R.k) (Fin D.R.t) (l := (G i).s + 1) 0 ((G i).s + 1) (Nat.zero_add _) p]
    rfl
  have h4 := ((G i).bes 0 D.R.rS h₀ ((G i).s + 1) (Nat.zero_add _)).2.2.2.1 p rfl r
  have h5 : B.d.i₀ *ᵥ vecB B.o B.ζ = (f.c.B 0 D.R.rS h₀).d.i₀ *ᵥ vecB (f.c.B 0 D.R.rS h₀).o (f.c.B 0 D.R.rS h₀).ζ :=
    eq_of_heq (congr_arg_heq (fun B' : BesLev D D.R.rS => B'.d.i₀ *ᵥ vecB B'.o B'.ζ) (hB.lev h₀))
  rw [← h5, hv r] at h4
  have h6 : (G i).q.prF he (algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
      (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) =
      (ofSplit (G i).q).pr (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) :=
    (G i).q.prF_toEAf he (incA D _)
  have h7 : ∀ x y, (ofSplit (G i).q).pr (x * y) = (ofSplit (G i).q).pr x * (ofSplit (G i).q).pr y := fun x y =>
    ((G i).q.pr.comp (incA D)).map_mul x y
  rw [h7, ← mul_assoc, hsc, one_mul] at h4
  rw [h6, h2, h3, h4, mul_comm, mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]

theorem adelic_embedding_inverse_vector (W : RealPack ex) (hW : PkHyp W) {u : D.what₂.Word} (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
    (g : GA D (D.sp.X 0)) :
    ((Formalism.IndefR.Lev.finE (D.sp.Y 0) (embA B.d B.o g))⁻¹).val *ᵥ (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D)
      (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) =
      fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) := by
  have h := GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hW.bot.idE (Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet W.S.X u) (W.S.X.zR u)
    (Or.inr rfl) (embA B.d B.o g)⁻¹ ((B.tieH _).1 ((embA B.d B.o).range.inv_mem ⟨g, rfl⟩))
  funext r
  rw [← map_inv]
  exact ((toEAf D).map_mulVec _ _ r).symm.trans (congrArg (toEAf D) (congrFun h r))

end GlobalTheory.MiTop.MoveZ

open GlobalTheory.MiTop.MoveZ in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.MiTop.base_moves_vector_z : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, ∃ Γ : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D, ∀ u (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), Placed f B → ∀ a₀ a, IsAt f B a₀ a → ∃ (θ : Formalism.IndefR.Lev.EAf D) (hθ : θ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.resS D.host.F PP ⟨θ, hθ⟩ = 1 ∧ ∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))) = toEAf D ei • (θ • Γ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr PP hPP
  obtain ⟨χ, hχ⟩ := exists_char W ⟨PP, hPP⟩
  by_cases hex : ∃ u, ∃ (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), Placed f B
  swap
  · exact ⟨0, fun u f B h => absurd ⟨u, f, B, h⟩ hex⟩
  obtain ⟨u₀, f₀, B₀, k₀, _, _, _, _, ι₀, v₀, o₀, n₀, G₀, pl₀, -, -, -, -, -, hG₀, hB₀⟩ := hex
  obtain ⟨i₀, hi₀⟩ := pl₀.surjective ⟨PP, hPP⟩
  have he₀ : Formalism.L2.NTheta.IsIdemAt (G₀ i₀).q.e PP := by have := (hG₀.idem i₀).1; rwa [hi₀] at this
  obtain ⟨j₀, hj₀, -⟩ := base_inv_alt W f₀ B₀ v₀ o₀ G₀ pl₀ hG₀ hB₀ i₀
  refine ⟨fun r => toEAf D ((G₀ i₀).q.sec (((((G₀ i₀).S.ϖ⁻¹ : (G₀ i₀).kˣ) : (G₀ i₀).k)) ^ (D.R.rS + 1))) *
    ((pk W).βY 0).val r j₀, ?_⟩
  rintro u f B ⟨k, _, _, _, _, ι, v, o, n, G, pl, -, -, -, -, -, hG, hB⟩ a₀ a -
  obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
  have he : Formalism.L2.NTheta.IsIdemAt (G i).q.e PP := by have := (hG.idem i).1; rwa [hi] at this
  have hee : (G₀ i₀).q.e = (G i).q.e := GlobalTheory.LocMod.PinInhab.idem_unique he₀ he
  obtain ⟨j, hj, hz⟩ := base_inv_alt W f B v o G pl hG hB i
  obtain rfl : j = j₀ := Fin.ext (hj.trans hj₀.symm)
  have hrat := unif_ratio (G₀ i₀).q (G i).q he₀ hee (pk W).ψ _ _ (G₀ i₀).char (G i).char (G₀ i₀).S.cond _ _
    (G₀ i₀).S.unif (G i).S.unif fun z => (hχ u₀ f₀ v₀ n₀ G₀ pl₀ hG₀ i₀ hi₀ z).trans (hχ u f v n G pl hG i hi z).symm
  obtain ⟨θ, hθ, h1, h2⟩ := exists_theta (G₀ i₀).q he₀ _ (pow_sub_one_lt hrat (D.R.rS + 1))
  refine ⟨θ, hθ, h1, fun ei hei => ?_⟩
  obtain rfl : ei = (G i).q.e := GlobalTheory.LocMod.PinInhab.idem_unique hei he
  have h3 : toEAf D ((G i).q.sec (((((G i).S.ϖ⁻¹ : (G i).kˣ) : (G i).k)) ^ (D.R.rS + 1))) = toEAf D (G i).q.e * θ *
      toEAf D ((G₀ i₀).q.sec (((((G₀ i₀).S.ϖ⁻¹ : (G₀ i₀).kˣ) : (G₀ i₀).k)) ^ (D.R.rS + 1))) := by
    rw [← hee, h2, ← RingHom.map_mul, ← sec_mul_sec, ← mul_pow, mul_right_comm, Units.mul_inv, one_mul, ← map_pow, sec_chg]
  have h4 : (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) *
      (show GA D (D.sp.Y 0) from f.g.b 0))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val =
      ((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *
        ((Formalism.IndefR.Lev.finE (Yc D 0) (embA B.d B.o (a₀ * a)))⁻¹).val := by
    have := (Formalism.IndefR.Lev.finE (D.sp.Y 0)).map_mul (embA B.d B.o (a₀ * a)) (f.g.b 0)
    exact congrArg Units.val ((congrArg Inv.inv this).trans (_root_.mul_inv_rev _ _))
  funext r
  rw [h4, ← mulVec_mulVec]
  have h5 := adelic_embedding_inverse_vector W hW B (a₀ * a)
  refine Eq.trans ?_ ((hz r).trans ?_)
  · exact congrArg (fun w => toEAf D (G i).q.e * (((Formalism.IndefR.Lev.finE (Yc D 0) (f.g.b 0))⁻¹).val *ᵥ w) r) h5
  · rw [h3, mul_assoc, mul_assoc]
    rfl

end
