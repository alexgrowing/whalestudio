import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvariantDerivationLog
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogChain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.MonoVal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvDer

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.LawLog GlobalTheory.FactorDepth
  GlobalTheory.IsoTriv

section Two

variable {K : Type} [Field K] [CharZero K] {d : ℕ}

theorem subst_secondBlockZero_twoPointVariables {ι : Type} (Y : Fin d → MvPowerSeries ι K) (hY : ∀ i, constantCoeff (Y i) = 0)
    (f : PS K 2 d) :
    subst Y (subst (GlobalTheory.LogJacobian.substSecondBlockZero (C := K) d) (subst (twoVars K d) f : MvPowerSeries (Fin d ⊕ Fin d) K) :
        MvPowerSeries (Fin d) K) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then Y q.2 else 0) f := by
  have hYs : HasSubst Y := hasSubst_of_constantCoeff_zero hY
  have hA := GlobalTheory.LogJacobian.hasSubst_substSecondBlockZero (C := K) d
  have hB : HasSubst (fun q : Fin 2 × Fin d => subst (GlobalTheory.LogJacobian.substSecondBlockZero (C := K) d) (twoVars K d q)) :=
    hasSubst_of_constantCoeff_zero fun q =>
      constantCoeff_subst_eq_zero hA (GlobalTheory.LogJacobian.constantCoeff_substSecondBlockZero d) (cc_twoVars q)
  rw [subst_comp_subst_apply hs_twoVars hA, subst_comp_subst_apply hB hYs]
  congr 1
  funext q
  simp only [twoVars]
  rw [subst_X hA]
  split_ifs with h
  · simp [GlobalTheory.LogJacobian.substSecondBlockZero, subst_X hYs]
  · simp only [GlobalTheory.LogJacobian.substSecondBlockZero, Sum.elim_inr]
    rw [← coe_substAlgHom hYs, map_zero]

theorem pderiv_inr_twoVars (k : Fin d) (f : PS K 2 d) :
    pderiv K (Sum.inr k) (subst (twoVars K d) f) = subst (twoVars K d) (pderiv K ((1 : Fin 2), k) f) := by
  classical
  rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst cc_twoVars, Finset.sum_eq_single ((1 : Fin 2), k)]
  · simp [twoVars, pderiv_X, Pi.single_apply]
  · intro q _ hq
    obtain ⟨a, i⟩ := q
    fin_cases a
    · simp [twoVars, pderiv_X, Pi.single_apply]
    · have : i ≠ k := fun h => hq (by simp [h])
      simp [twoVars, pderiv_X, Pi.single_apply, this]
  · simp

end Two

section Main

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℝ)} {d n : ℕ} {ι : Type}

theorem subst_jacEntry (F : FGLaw K d) (hF : ∀ a, MvIsInt v (subst (twoVars K d) (F.F a)))
    (Y : Fin d → MvPowerSeries ι K) (hY : ∀ i, constantCoeff (Y i) = 0) (k j : Fin d) :
    subst Y (GlobalTheory.LogJacobian.jacEntry (logFGLOf v F hF) k j) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then Y q.2 else 0) (pderiv K ((1 : Fin 2), k) (F.F j)) := by
  rw [← subst_secondBlockZero_twoPointVariables Y hY, ← pderiv_inr_twoVars]
  rfl

omit [CharZero K] in

theorem subst_ev_pt_zero [Finite ι] (T : Fin n × Fin d → MvPowerSeries ι K) (hT : ∀ q, constantCoeff (T q) = 0)
    (b : Fin n) (g : PS K 2 d) :
    subst T (ev (n := n) ![pt K d b, 0] g) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then T (b, q.2) else 0) g := by
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have h2 : HasSubst (fun p : Fin 2 × Fin d => (![pt K d b, 0] : Fin 2 → Pt K n d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨j, i⟩ := p
      fin_cases j <;> simp [pt]
  unfold ev
  rw [subst_comp_subst_apply h2 hTs]
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  · simp [pt, subst_X hTs]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply, one_ne_zero, if_false]
    rw [← coe_substAlgHom hTs, map_zero]

omit [CharZero K] in

theorem constantCoeff_subst_self {σ : Type} [Finite σ] (T : σ → MvPowerSeries ι K)
    (hT : ∀ q, constantCoeff (T q) = 0) (f : MvPowerSeries σ K) :
    constantCoeff (subst T f : MvPowerSeries ι K) = constantCoeff f := by
  have hs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have h0 : constantCoeff (subst T (f - (constantCoeff f) • 1) : MvPowerSeries ι K) = 0 :=
    constantCoeff_subst_eq_zero hs hT (by simp)
  rw [← coe_substAlgHom hs, map_sub, map_smul, map_one, coe_substAlgHom hs] at h0
  simpa [sub_eq_zero] using h0

variable [Fintype ι]

def logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) : Fin d → MvPowerSeries ι K :=
  fun e => ∑ l, (if cp l = b then u l e else 0) • (X l : MvPowerSeries ι K)

omit [CharZero K] in
theorem cc_logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) (e : Fin d) :
    constantCoeff (logLin cp u b e) = 0 := by
  simp only [logLin, map_sum, constantCoeff_smul, constantCoeff_X, smul_zero, Finset.sum_const_zero]

omit [CharZero K] in
theorem pderiv_logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) (e : Fin d) (l : ι) :
    pderiv K l (logLin cp u b e) = if cp l = b then C (u l e) else 0 := by
  classical
  unfold logLin
  rw [map_sum, Finset.sum_eq_single l]
  · rw [Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]
    split_ifs <;> simp
  · intro l' _ hl
    rw [Derivation.map_smul, pderiv_X_of_ne hl, smul_zero]
  · simp

theorem pderiv_subst_expPt (F : FGLaw K d) (hF : ∀ a, MvIsInt v (subst (twoVars K d) (F.F a)))
    (cp : ι → Fin n) (u : ι → Fin d → K) (l : ι) (Φ : PS K n d) :
    subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) (DofN F.F (cp l) (u l) Φ) =
      pderiv K l (subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) Φ) := by
  classical
  set G := logFGLOf v F hF with hG
  set T : Fin n × Fin d → MvPowerSeries ι K := fun q => expPt G (logLin cp u q.1) q.2 with hTdef
  have hT : ∀ q, constantCoeff (T q) = 0 := fun q => cc_expPt G (cc_logLin cp u q.1) q.2
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have key : ∀ b j, pderiv K l (T (b, j)) = if cp l = b then
      ∑ i : Fin d, C (u l i) * subst T (ev (n := n) ![pt K d b, 0] (pderiv K ((1 : Fin 2), i) (F.F j))) else 0 := by
    intro b j
    have h1 : pderiv K l (T (b, j)) = ∑ i, subst (logLin cp u b) (pderiv K i (expOf G j)) *
        pderiv K l (logLin cp u b i) :=
      ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst (cc_logLin cp u b) (expOf G j) l
    have h2 : ∀ i, subst (logLin cp u b) (pderiv K i (expOf G j)) =
        subst T (ev (n := n) ![pt K d b, 0] (pderiv K ((1 : Fin 2), i) (F.F j))) := by
      intro i
      rw [GlobalTheory.LogJacobian.pderiv_expOf, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (isExp_expOf G).1)
        (hasSubst_of_constantCoeff_zero (cc_logLin cp u b)), subst_ev_pt_zero T hT]
      exact subst_jacEntry F hF (fun e => T (b, e)) (fun e => hT (b, e)) i j
    rw [h1]
    simp only [h2, pderiv_logLin]
    split_ifs
    · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · simp
  rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst hT, Fintype.sum_prod_type, Finset.sum_eq_single (cp l)]
  · unfold DofN
    simp only [key, if_true]
    rw [← coe_substAlgHom hTs, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_sum, mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, coe_substAlgHom hTs, subst_C]
  · intro b _ hb
    simp [key, Ne.symm hb]
  · simp

end Main

theorem invDer : InvDerSt := by
  intro K _ _ v d F hF n ι _ cp u P Φ
  classical
  show _ = derivAt0 P (subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) Φ)
  have hk := pderiv_subst_expPt F hF cp u
  set T : Fin n × Fin d → MvPowerSeries ι K := fun q => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2
  have hT : ∀ q, constantCoeff (T q) = 0 := fun q => cc_expPt _ (cc_logLin cp u q.1) q.2
  have hit : ∀ (l : ι) (c : ℕ) (g : PS K n d),
      subst T ((DofN F.F (cp l) (u l))^[c] g) = (pderiv K l)^[c] (subst T g : MvPowerSeries ι K) := by
    intro l c
    induction c with
    | zero => intro g; rfl
    | succ c ih => intro g; rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hk]
  have hfold : ∀ (m : ι →₀ ℕ) (L : List ι),
      subst T (L.foldr (fun l g => (DofN F.F (cp l) (u l))^[m l] g) Φ) =
        L.foldr (fun l g => (pderiv K l)^[m l] g) (subst T Φ : MvPowerSeries ι K) := by
    intro m L
    induction L with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, hit, ih]
  unfold DpolyN derivAt0
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, constantCoeff_C, mul_assoc, ← constantCoeff_subst_self T hT]
  congr 1
  unfold DmonN
  rw [hfold, ← coeff_zero_eq_constantCoeff_apply,
    ReciprocityTheory.ChartRestriction.G.TB.MV.coeff_fold (fun l : ι => l) (fun _ _ h => h) m _ _ (Finset.nodup_toList _) 0,
    Finset.sum_map_toList, Finset.prod_map_toList]
  have h1 : (∑ l, m l • Finsupp.single l 1 : ι →₀ ℕ) = m := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact Finsupp.univ_sum_single m
  have h2 : (mfact m : K) = ∏ l, ((m l).factorial : K) := Finsupp.prod_fintype _ _ (by simp)
  simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.one_ascFactorial]
  rw [h1, h2, mul_comm]

end GlobalTheory.InvDer
