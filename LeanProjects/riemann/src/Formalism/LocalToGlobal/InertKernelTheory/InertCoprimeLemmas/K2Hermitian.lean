import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.QuadraticBaseChangeGL3
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalLevelIsKOneAtT

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelHermitian

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelSeries
  Formalism.L2.KerInert.QuadraticBaseChangeGL3

section ChainPf

open Formalism.L2.G.Pend

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

theorem isWeightedHomogeneous_linearForm_of_blockDiagonal (A : X.ZA j → X.ZA j → Kc) (hA : BlockDiag X Kc j A) (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : X.ZA j) :
    MvPolynomial.IsWeightedHomogeneous (wB X j v s)
      (linP (fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (A x y)) x) (wB X j v s x) := by
  unfold linP
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun y _ => ?_
  beta_reduce
  by_cases h : A x y = 0
  · rw [h, map_zero, map_zero, zero_mul]
    exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
  · have h2 : wB X j v s x = wB X j v s y := by
      unfold wB
      rw [hA x y h]
    rw [h2]
    exact (MvPolynomial.isWeightedHomogeneous_X _ _ y).C_mul _

theorem mono_wh_A (A : X.ZA j → X.ZA j → Kc) (hA : BlockDiag X Kc j A) (v : X.Pl) (s : Fin (X.G.P.n' v)) (m : X.ZA j →₀ ℕ) :
    MvPolynomial.IsWeightedHomogeneous (wB X j v s)
      (MvPolynomial.aeval (linP fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (A x y))
        (MvPolynomial.monomial m (1 : XspC (X.Pj (j + 1)) Kc))) (Finsupp.weight (wB X j v s) m) := by
  rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.weight_apply]
  exact MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun x _ => (isWeightedHomogeneous_linearForm_of_blockDiagonal X Kc j A hA v s x).pow _

theorem hGd_A (A : X.ZA j → X.ZA j → Kc) (hA : BlockDiag X Kc j A) (m n : X.ZA j →₀ ℕ)
    (h : MvPolynomial.coeff n (MvPolynomial.aeval (linP fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (A x y))
        (MvPolynomial.monomial m (1 : XspC (X.Pj (j + 1)) Kc))) ≠ 0) : GoodDeg X j n ↔ GoodDeg X j m := by
  have key : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), ∑ a, ∑ b, n ⟨v, (s, a, b)⟩ = ∑ a, ∑ b, m ⟨v, (s, a, b)⟩ := by
    intro v s
    rw [← wt_eq, ← wt_eq]
    by_contra hne
    exact h ((mono_wh_A X Kc j A hA v s m).coeff_eq_zero n hne)
  unfold GoodDeg
  simp only [key]

end ChainPf

theorem chain_linear : ChainLin := by
  intro p _ X Kc _ _ j A hA P f
  classical
  exact Formalism.L2.G.Pend.pr_sub A (Formalism.L2.G.Pend.GoodDeg X j) (hGd_A X Kc j A hA) P f

theorem hasSubst_lin {ι R : Type} [Fintype ι] [CommRing R] (B : ι → ι → R) :
    MvPowerSeries.HasSubst (fun x : ι => ∑ y, MvPowerSeries.C (B x y) * MvPowerSeries.X y) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by
    rw [map_sum]
    exact Finset.sum_eq_zero fun y _ => by rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]

theorem subst_lin {σ τ R : Type} [Fintype σ] [CommRing R] {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a)
    (c : σ → R) :
    MvPowerSeries.subst a (∑ y, MvPowerSeries.C (c y) * MvPowerSeries.X y : MvPowerSeries σ R) =
      ∑ y, MvPowerSeries.C (c y) * a y := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_mul ha, MvPowerSeries.subst_C, MvPowerSeries.subst_X ha]

theorem rename_linear : RenameLin := by
  intro κ ι R _ _ _ e he B g
  classical
  have hr : MvPowerSeries.HasSubst (Formalism.L2.KerInert.Loc.resFam (R := R) e) := Formalism.L2.KerInert.Loc.hasSubst_resFam e
  have hB := hasSubst_lin B
  have hBe := hasSubst_lin (fun x y => B (e x) (e y))
  unfold linSub
  rw [Formalism.L2.KerInert.Loc.resV_eq_subst he.1, Formalism.L2.KerInert.Loc.resV_eq_subst he.1,
    MvPowerSeries.subst_comp_subst_apply hB hr, MvPowerSeries.subst_comp_subst_apply hr hBe]
  congr 1
  funext i
  obtain ⟨k, rfl⟩ := he.2 i
  rw [subst_lin hr, Formalism.L2.KerInert.Loc.resFam_apply he.1, MvPowerSeries.subst_X hBe]
  rw [← Equiv.sum_comp (Equiv.ofBijective e he)]
  refine Finset.sum_congr rfl fun k' _ => ?_
  simp only [Equiv.ofBijective_apply]
  rw [Formalism.L2.KerInert.Loc.resFam_apply he.1]

section Alg

open Formalism.L2.G.Pend

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

theorem trSub_mul (U V : X.ZA j → X.ZA j → Kc) (P : DA X Kc j) :
    trSub X Kc j V (trSub X Kc j U P) = trSub X Kc j (fun z y => ∑ x, V z x * U x y) P := by
  have h : (trSub X Kc j V).comp (trSub X Kc j U) = trSub X Kc j (fun z y => ∑ x, V z x * U x y) := by
    apply MvPolynomial.algHom_ext
    intro y
    rw [AlgHom.comp_apply]
    unfold trSub
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    unfold linT
    simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [← h]
  rfl

theorem blockDiag_mul {U V : X.ZA j → X.ZA j → Kc} (hV : BlockDiag X Kc j V) (hU : BlockDiag X Kc j U) :
    BlockDiag X Kc j (fun z y => ∑ x, V z x * U x y) := by
  intro z y h
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [hU x y (right_ne_zero_of_mul hx), hV z x (left_ne_zero_of_mul hx)]

theorem pairD_lin (τ : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] XspC (X.Pj (j + 1)) Kc) (P P' : DA X Kc j)
    (h : ∀ n, MvPolynomial.coeff n P' = τ (MvPolynomial.coeff n P)) (f : MvPowerSeries (X.ZA j) Kc) :
    pairD X Kc j P' f = τ (pairD X Kc j P f) := by
  classical
  rw [pairD_eq X Kc j P' f (P.support ∪ P'.support) Finset.subset_union_right,
    pairD_eq X Kc j P f (P.support ∪ P'.support) Finset.subset_union_left, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [h n, LinearMap.map_smul]

theorem glAt_glInv (B : ∀ v : X.Pl, GL (Fin ((X.Fl.Pj j).m + 1)) (X.G.P.Qq v)) : glAt X j (glInv X j B) = B := by
  cases j <;> rfl

theorem blockDiag_LkB [Algebra (Formalism.L2.G.Pend.K0 p) Kc] (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) :
    BlockDiag X Kc j (LkB X Kc j B) :=
  fun x y h => LkB_ne X Kc j B x y h

theorem linSub_LkB [Algebra (Formalism.L2.G.Pend.K0 p) Kc] (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (f : MvPowerSeries (X.ZA j) Kc) :
    linSub (LkB X Kc j B) f = SA X Kc j B f := by
  unfold linSub SA
  congr 1
  funext z
  exact linS_LkB X Kc j B z

theorem blockDiag_VOf [Algebra (Formalism.L2.G.Pend.K0 p) Kc] {D : D7} (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (c : Kc) (La' : X.Lt (j + 1)) :
    BlockDiag X Kc j (VOf Kc fd c j La') := by
  intro x y h
  unfold VOf at h
  by_contra hne
  exact h (if_neg fun hh => hne hh.1)

theorem chain_core [Algebra (Formalism.L2.G.Pend.K0 p) Kc] (V : X.ZA j → X.ZA j → Kc) (hV : BlockDiag X Kc j V)
    (A : ∀ v : Fin (X.Pj j).nV, GL (Fin ((X.Pj j).m + 1)) ((X.Pj j).Qq v))
    (Gm : (X.Pj j).Xsp) (hG : GoodG X Kc j Gm) (hO : OddDeg X j Gm)
    (τ : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] XspC (X.Pj (j + 1)) Kc)
    (hτ : ∀ n, MvPolynomial.coeff n (trSub X Kc j V (polDel X Kc j Gm)) = τ (MvPolynomial.coeff n (polDel X Kc j Gm)))
    (g : MvPowerSeries (X.ZA j) Kc) :
    pairD X Kc j (polDel X Kc j ((X.Pj j).natAct A Gm))
        (linSub (fun z y => ∑ x, V z x * LkB X Kc j (glAt X j A) x y) g) =
      cA X Kc j (glAt X j A) • τ (pairD X Kc j (polDel X Kc j Gm) g) := by
  rw [chain_linear p X Kc j _ (blockDiag_mul X Kc j hV (blockDiag_LkB X Kc j _)), ← trSub_mul,
    ← chain_linear p X Kc j V hV, ← chain_linear p X Kc j _ (blockDiag_LkB X Kc j _), linSub_LkB,
    ← delF_apply, (delEquivH X Kc j A Gm _ hG hO).2, delF_apply, chain_linear p X Kc j V hV, pairD_lin X Kc j τ _ _ hτ]

end Alg

theorem kapOf_bij {p : ℕ} [Fact p.Prime] (X : Sys p) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T) (j : ℕ) :
    Function.Bijective (Formalism.L2.G.Pend.kapOf X pos j) := by
  refine ⟨Formalism.L2.G.Pend.kapOf_injective X pos j, fun t => ?_⟩
  obtain ⟨τ, b, a⟩ := t
  refine ⟨⟨(pos.symm τ).1, ((pos.symm τ).2, Fin.cast (Formalism.L2.G.Pend.rank_eq X j) a,
    Fin.cast (Formalism.L2.G.Pend.rank_eq X (j + 1)) b)⟩, ?_⟩
  simp [Formalism.L2.G.Pend.kapOf]

theorem frGL_val {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7} (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (hFr : FrInv fd) (j : ℕ)
    (La : X.Lt j) (v : X.Pl) : ((frGL fd j La v : GL _ _) : Matrix _ _ _) = fd.frM j La v := by
  unfold frGL
  rw [dif_pos (hFr j La v)]
  rfl

theorem subBG_diag {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7} (E : Formalism.L2.G.Pend.CEmb X.G)
    (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (j : ℕ) (La : X.Lt j)
    (La' : X.Lt (j + 1)) (w : Σ v : X.Pl, Fin (X.G.P.n' v)) (b1 b2 : Fin ((X.Pj (j + 1)).m + 1))
    (a1 a2 : Fin ((X.Pj j).m + 1)) :
    Formalism.L2.PairingIndexBounds.F.subBG E pos fd j La La' (pos w, b1, a1) (pos w, b2, a2) =
      if IsOddPos w.2 then
        Formalism.L2.PairingIndexBounds.F.twG X E w.1 w.2 (fd.frM j La w.1 a1 a2) *
          Formalism.L2.PairingIndexBounds.F.twG X E w.1 w.2 ((fd.frM (j + 1) La' w.1)⁻¹ b2 b1)
      else
        Formalism.L2.PairingIndexBounds.F.twG X E w.1 w.2 (fd.frM (j + 1) La' w.1 b1 b2) *
          Formalism.L2.PairingIndexBounds.F.twG X E w.1 w.2 ((fd.frM j La w.1)⁻¹ a2 a1) := by
  unfold Formalism.L2.PairingIndexBounds.F.subBG
  rw [if_pos rfl]
  dsimp only
  generalize hw' : pos.symm (pos w) = w'
  obtain rfl : w' = w := by rw [← hw']; exact pos.symm_apply_apply w
  rfl

theorem substitution_split : SubBSplit := by
  intro p _ X D E pos fd c hFr j La La' x y
  let _ := Formalism.L2.G.Pend.wittFractionAlgebraCp p
  let _ := Formalism.L2.G.Pend.algKfC E
  classical
  obtain ⟨v, s, a, b⟩ := x
  obtain ⟨v', s', a', b'⟩ := y
  by_cases h : (⟨v', s'⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩
  · cases h
    rw [Finset.sum_eq_single (⟨v, (s, a, b')⟩ : X.ZA j)]
    · have hL : Formalism.L2.G.Pend.LkB X ℂ_[p] j (BOf fd j La) ⟨v, (s, a, b')⟩ ⟨v, (s, a', b')⟩ =
          Formalism.L2.G.Pend.cf X ℂ_[p] j (BOf fd j La) v s a a' := by
        unfold Formalism.L2.G.Pend.LkB
        rw [Finset.sum_eq_single a']
        · rw [if_pos rfl]
        · intro a'' _ hne
          rw [if_neg]
          intro hh
          exact hne (congrArg (fun z : X.ZA j => z.2.2.1) hh).symm
        · intro hh
          exact absurd (Finset.mem_univ _) hh
      rw [hL]
      have htw : Formalism.L2.PairingIndexBounds.F.twG X E v s = Formalism.L2.G.Pend.tw X ℂ_[p] v s := rfl
      have hB : ((BOf fd j La v : GL _ _) : Matrix _ _ _) = (fd.frM j La v)⁻¹ := by
        unfold BOf
        rw [Matrix.coe_units_inv, frGL_val fd hFr]
      have hBi : (((BOf fd j La v)⁻¹ : GL _ _) : Matrix _ _ _) = fd.frM j La v := by
        unfold BOf
        rw [inv_inv, frGL_val fd hFr]
      rw [show Formalism.L2.G.Pend.kapOf X pos j ⟨v, (s, a, b)⟩ = (pos ⟨v, s⟩, Fin.cast (Formalism.L2.G.Pend.rank_eq X (j + 1)).symm b,
          Fin.cast (Formalism.L2.G.Pend.rank_eq X j).symm a) from rfl,
        show Formalism.L2.G.Pend.kapOf X pos j ⟨v, (s, a', b')⟩ = (pos ⟨v, s⟩, Fin.cast (Formalism.L2.G.Pend.rank_eq X (j + 1)).symm b',
          Fin.cast (Formalism.L2.G.Pend.rank_eq X j).symm a') from rfl, subBG_diag]
      by_cases hs : IsOddPos s
      · simp only [VOf, Formalism.L2.G.Pend.cf, hs, and_self, ↓reduceIte, htw, hBi, Formalism.L2.G.Pend.mAt, Matrix.submatrix_apply,
          Matrix.map_apply, finCongr_apply]
        ring
      · simp only [VOf, Formalism.L2.G.Pend.cf, hs, and_self, ↓reduceIte, htw, hB, Formalism.L2.G.Pend.mAt, Matrix.transpose_apply,
          Matrix.submatrix_apply, Matrix.map_apply, finCongr_apply]
        ring
    · rintro ⟨vz, sz, az, bz⟩ _ hz
      by_contra hne
      have hV := left_ne_zero_of_mul hne
      have hLk := right_ne_zero_of_mul hne
      have hcond : (⟨vz, sz⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩ ∧ az = a := by
        by_contra hc
        apply hV
        unfold VOf
        exact if_neg hc
      obtain ⟨h1, h2⟩ := hcond
      unfold Formalism.L2.G.Pend.LkB at hLk
      obtain ⟨a'', _, ha''⟩ := Finset.exists_ne_zero_of_sum_ne_zero hLk
      have hy : (⟨v, (s, a', b')⟩ : X.ZA j) = ⟨vz, (sz, a'', bz)⟩ := by
        by_contra hc
        apply ha''
        exact if_neg hc
      cases h1
      have hb : b' = bz := congrArg (fun z : X.ZA j => z.2.2.2) hy
      subst hb
      exact hz (by rw [show az = a from h2])
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  · have hne : (Formalism.L2.G.Pend.kapOf X pos j ⟨v, (s, a, b)⟩).1 ≠ (Formalism.L2.G.Pend.kapOf X pos j ⟨v', (s', a', b')⟩).1 := by
      intro hh
      exact h (pos.injective hh).symm
    unfold Formalism.L2.PairingIndexBounds.F.subBG
    rw [if_neg hne, mul_zero]
    symm
    refine Finset.sum_eq_zero fun z _ => ?_
    by_contra hz
    have h1 := blockDiag_VOf X ℂ_[p] j fd c La' _ z (left_ne_zero_of_mul hz)
    have h2 := blockDiag_LkB X ℂ_[p] j (BOf fd j La) z _ (right_ne_zero_of_mul hz)
    exact h (h2.trans h1)

theorem delPolH_of (hSp : SubBSplit) : DelPolH := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ p _ X _ E hfin hst g hLT pos fd cc δ B χ lamK SS cl Ξ₀ muT
  intro hFr hS hK Y σ cls cmp κ ι Φ₀ τ sc sH Gm j cK hN hMv hOp hDeg hSer hChi hYEq
  intro La hLa x Q hQ c' L' hL'
  have hTh : Y.ThF j La (c', L') = Formalism.L2.G.Pend.thFOf X pos (Formalism.L2.PairingIndexBounds.F.FrecG E.toCEmb pos fd B χ lamK SS cl Ξ₀ muT
      (Formalism.L2.PairingIndexBounds.F.ltC g hLT)) j La (c', L') :=
    Formalism.L2.G.Pend.pendR_ThF_rep X E.toCEmb hfin hst _ _ hS hK j La (c', L') hLa
  have hsr : srOf Y j La (c', L') = (Y.eS j La * (Y.eT j (c', L'))⁻¹ : X.G.Kf) •
      linSub (fun z y => ∑ w, VOf Y.Kc fd (Formalism.L2.PairingIndexBounds.F.ltC g hLT) j (c', L') z w *
        Formalism.L2.G.Pend.LkB X Y.Kc j (BOf fd j La) w y)
        (resV (Formalism.L2.G.Pend.kapOf X pos j) (serG fd B χ lamK SS cl Ξ₀ muT j La (c', L'))) := by
    unfold srOf
    rw [hTh]
    congr 1
    show resV (Formalism.L2.G.Pend.kapOf X pos j) (linSub (fun x y => Formalism.L2.PairingIndexBounds.F.ltC g hLT *
      Formalism.L2.PairingIndexBounds.F.subBG E.toCEmb pos fd j La (c', L') x y) (serG fd B χ lamK SS cl Ξ₀ muT j La (c', L'))) = _
    rw [rename_linear _ _ _ _ (kapOf_bij X pos j)]
    congr 1
    funext z y
    exact hSp p X D E.toCEmb pos fd _ hFr j La (c', L') z y
  obtain ⟨hMe, hG, hO⟩ := hMv La hLa x
  beta_reduce at hMe
  have hc := chain_core X Y.Kc j (VOf Y.Kc fd (Formalism.L2.PairingIndexBounds.F.ltC g hLT) j (c', L'))
    (blockDiag_VOf X Y.Kc j fd _ (c', L')) (glInv X j (BOf fd j La)) (Gm j La x) hG hO (τ j c' L')
    (hYEq c' L' hL' (Gm j La x) hG hO) (resV (Formalism.L2.G.Pend.kapOf X pos j) (serG fd B χ lamK SS cl Ξ₀ muT j La (c', L')))
  rw [glAt_glInv] at hc
  have hPD := pairing_dictionary p X Y.Kc j D (D.R.N j) (D.R.N (j + 1)) ι (eIdx X D pos j hN) (eIdx_injective X D pos j hN) (Φ₀ j)
    (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1)))
    ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (κ j c' L'))
    (resV (Formalism.L2.G.Pend.kapOf X pos j) (serG fd B χ lamK SS cl Ξ₀ muT j La (c', L'))) (sH j La (c', L'))
    (hDeg La hLa x Q hQ) (fun α hα => hSer La hLa c' L' hL' α (hDeg La hLa x Q hQ α hα))
  show sc j c' L' • τ j c' L' (Φ₀ j (_ • pairR D (polDY D (t.O u μ).dgen (Q (cls j La.1 La.2)) (N' := D.R.N (j + 1)))
      ((t.rd u μ).Th t.seam t.amb j (cls j La.1 La.2) (κ j c' L')))) =
    cK • Formalism.L2.G.Pend.pairD X Y.Kc j (Formalism.L2.G.Pend.polDel X Y.Kc j (cmp j x La.1 La.2)) (srOf Y j La (c', L'))
  rw [hsr, Formalism.L2.G.Pend.pairD_smul_right, ← hMe, hc, hOp La hLa x Q hQ, hPD, LinearMap.map_smulₛₗ, map_smul, map_smul,
    ← algebraMap_smul Y.Kc (Y.eS j La * (Y.eT j (c', L'))⁻¹), smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [← hChi La hLa c' L' hL']

theorem difference_polynomial_hecke : DelPolH := delPolH_of substitution_split

end Formalism.L2.KerInert.SecondKernelHermitian
