import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RelatedMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAt0SubstLinearLipschitz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ColApprox

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.FGDepth GlobalTheory.FactorDepth GlobalTheory.LawLog

variable {C : Type} [Field C] {d : ℕ} {τ τ' : Type}

abbrev NC (a : Fin d → MvPowerSeries τ C) : Prop := ∀ i, constantCoeff (a i) = 0

def ev1 (a : Fin d → MvPowerSeries τ C) (f : PS C 1 d) : MvPowerSeries τ C :=
  subst (fun p : Fin 1 × Fin d => (![a] : Fin 1 → Fin d → MvPowerSeries τ C) p.1 p.2) f

def ev2 (a b : Fin d → MvPowerSeries τ C) (f : PS C 2 d) : MvPowerSeries τ C :=
  subst (fun p : Fin 2 × Fin d => (![a, b] : Fin 2 → Fin d → MvPowerSeries τ C) p.1 p.2) f

theorem nc1 {a : Fin d → MvPowerSeries τ C} (ha : NC a) (p : Fin 1 × Fin d) :
    constantCoeff ((![a] : Fin 1 → Fin d → MvPowerSeries τ C) p.1 p.2) = 0 := by
  obtain ⟨j, i⟩ := p
  fin_cases j; exact ha i

theorem nc2 {a b : Fin d → MvPowerSeries τ C} (ha : NC a) (hb : NC b) (p : Fin 2 × Fin d) :
    constantCoeff ((![a, b] : Fin 2 → Fin d → MvPowerSeries τ C) p.1 p.2) = 0 := by
  obtain ⟨j, i⟩ := p
  fin_cases j; exacts [ha i, hb i]

theorem constantCoeff_substOnePointPowerSeries_eq_zero {a : Fin d → MvPowerSeries τ C} (ha : NC a) {f : PS C 1 d} (hf : constantCoeff f = 0) :
    constantCoeff (ev1 a f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (nc1 ha)) (nc1 ha) hf

theorem constantCoeff_germEvalPair_eq_zero {a b : Fin d → MvPowerSeries τ C} (ha : NC a) (hb : NC b) {f : PS C 2 d} (hf : constantCoeff f = 0) :
    constantCoeff (ev2 a b f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (nc2 ha hb)) (nc2 ha hb) hf

theorem subst_substOnePointPowerSeries {φ : τ → MvPowerSeries τ' C} (hφ : HasSubst φ) {a : Fin d → MvPowerSeries τ C} (ha : NC a)
    (f : PS C 1 d) : subst φ (ev1 a f) = ev1 (fun i => subst φ (a i)) f := by
  unfold ev1
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (nc1 ha)) hφ]
  congr 1
  funext ⟨j, i⟩
  fin_cases j; rfl

theorem subst_substTwoPointsPowerSeries {φ : τ → MvPowerSeries τ' C} (hφ : HasSubst φ) {a b : Fin d → MvPowerSeries τ C} (ha : NC a)
    (hb : NC b) (f : PS C 2 d) : subst φ (ev2 a b f) = ev2 (fun i => subst φ (a i)) (fun i => subst φ (b i)) f := by
  unfold ev2
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (nc2 ha hb)) hφ]
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> rfl

theorem subst_zero' {φ : τ → MvPowerSeries τ' C} (hφ : HasSubst φ) : subst φ (0 : MvPowerSeries τ C) = 0 := by
  rw [← coe_substAlgHom hφ, map_zero]

theorem substTwoPointsPowerSeries_zero_of_vanish_first_axis {a : Fin d → MvPowerSeries τ C} (ha : NC a) {h : PS C 2 d}
    (hh : ev (n := 1) ![pt C d 0, 0] h = 0) : ev2 a 0 h = 0 := by
  have hs : HasSubst (fun p : Fin 1 × Fin d => a p.2) := hasSubst_of_constantCoeff_zero fun p => ha p.2
  have h1 := congrArg (subst (fun p : Fin 1 × Fin d => a p.2)) (show ev2 (pt C (n := 1) d 0) 0 h = 0 from hh)
  rw [subst_substTwoPointsPowerSeries hs (fun i => by simp [pt]) (fun i => by simp), subst_zero' hs] at h1
  rw [← h1]
  congr 1
  · funext i; simp only [pt]; rw [subst_X hs]
  · funext i; exact (subst_zero' hs).symm

section Germ

variable [CharZero C] {n m : ℕ} (hL : PS C 1 d) (h : PS C 2 d) (k : ℕ) (g : PS C n d)

def germ (ψ : Fin n → Fin d → MvPowerSeries τ C) (s : Fin m → Fin d → MvPowerSeries τ C)
    (t : Fin m → Fin m → Fin d → MvPowerSeries τ C) : MvPowerSeries τ C :=
  subst (fun q : Fin n × Fin d => ψ q.1 q.2) g *
    PowerSeries.subst ((k : C) • (∑ j, ev1 (ψ j) hL - ∑ b, ∑ b', ev2 (s b) (t b b') h)) (PowerSeries.exp C)

variable {hL h}

theorem subst_germ (cL : constantCoeff hL = 0) (ch : constantCoeff h = 0) {φ : τ → MvPowerSeries τ' C}
    (hφ : HasSubst φ) {ψ : Fin n → Fin d → MvPowerSeries τ C} {s : Fin m → Fin d → MvPowerSeries τ C}
    {t : Fin m → Fin m → Fin d → MvPowerSeries τ C} (hψ : ∀ j, NC (ψ j)) (hs : ∀ b, NC (s b))
    (ht : ∀ b b', NC (t b b')) :
    subst φ (germ hL h k g ψ s t) = germ hL h k g (fun j i => subst φ (ψ j i)) (fun b i => subst φ (s b i))
      (fun b b' i => subst φ (t b b' i)) := by
  unfold germ
  have h0 : constantCoeff ((k : C) • (∑ j, ev1 (ψ j) hL - ∑ b, ∑ b', ev2 (s b) (t b b') h)) = 0 := by
    simp [map_sum, constantCoeff_substOnePointPowerSeries_eq_zero (hψ _) cL, constantCoeff_germEvalPair_eq_zero (hs _) (ht _ _) ch]
  rw [subst_mul hφ, subst_comp_subst_apply (a := fun q : Fin n × Fin d => ψ q.1 q.2)
    (hasSubst_of_constantCoeff_zero fun q => hψ q.1 q.2) hφ]
  congr 1
  unfold PowerSeries.subst
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => h0) hφ]
  congr 1
  funext _
  rw [← coe_substAlgHom hφ]
  simp only [map_smul, map_sub, map_sum]
  simp only [coe_substAlgHom, subst_substOnePointPowerSeries hφ (hψ _), subst_substTwoPointsPowerSeries hφ (hs _) (ht _ _)]

end Germ

section Exp

variable {v : AddValuation C (WithTop ℝ)} (L : LogFGL v d)

def exPt (w : Fin d → MvPowerSeries τ C) : Fin d → MvPowerSeries τ C := fun e => subst w (expOf L e)

theorem nc_exPt {w : Fin d → MvPowerSeries τ C} (hw : NC w) : NC (exPt L w) := fun e =>
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hw) hw ((isExp_expOf L).1 e)

theorem subst_exPt {φ : τ → MvPowerSeries τ' C} (hφ : HasSubst φ) {w : Fin d → MvPowerSeries τ C} (hw : NC w)
    (e : Fin d) : subst φ (exPt L w e) = exPt L (fun i => subst φ (w i)) e :=
  subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hw) hφ _

theorem lg_exPt {w : Fin d → MvPowerSeries τ C} (hw : NC w) (e : Fin d) : subst (exPt L w) (L.lg e) = w e := by
  have hs := hasSubst_of_constantCoeff_zero hw
  unfold exPt
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (isExp_expOf L).1) hs, (isExp_expOf L).2, subst_X hs]

theorem exPt_lg {a : Fin d → MvPowerSeries τ C} (ha : NC a) : exPt L (fun e => subst a (L.lg e)) = a := by
  have hs := hasSubst_of_constantCoeff_zero ha
  funext e
  unfold exPt
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero L.lg_const) hs, subst_lg_expOf, subst_X hs]

theorem exPt_add {F : Fin d → PS C 2 d} (hF0 : NC F) (hF : ∀ a, L.F a = subst (twoVars C d) (F a))
    {w w' : Fin d → MvPowerSeries τ C} (hw : NC w) (hw' : NC w') :
    (fun i => ev2 (exPt L w) (exPt L w') (F i)) = exPt L (w + w') := by
  have ha := nc_exPt L hw
  have hb := nc_exPt L hw'
  have hs : HasSubst (Sum.elim (exPt L w) (exPt L w')) :=
    hasSubst_of_constantCoeff_zero fun s => by cases s; exacts [ha _, hb _]
  rw [← exPt_lg L (a := fun i => ev2 (exPt L w) (exPt L w') (F i)) fun i => constantCoeff_germEvalPair_eq_zero ha hb (hF0 i)]
  congr 1
  funext e
  have h1 := congrArg (subst (Sum.elim (exPt L w) (exPt L w'))) (L.lg_F e)
  rw [subst_add hs, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero L.F_const) hs,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hs,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hs] at h1
  simp only [subst_X hs, Sum.elim_inl, Sum.elim_inr] at h1
  rw [Pi.add_apply, ← lg_exPt L hw e, ← lg_exPt L hw' e, ← h1]
  congr 1
  funext i
  rw [hF, subst_comp_subst_apply hs_twoVars hs]
  unfold ev2
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> simp [twoVars, subst_X hs]

theorem exPt_zero : exPt L (0 : Fin d → MvPowerSeries τ C) = 0 := by
  funext e
  exact subst_zero_of_constantCoeff_zero ((isExp_expOf L).1 e)

end Exp

theorem exPt_hom [CharZero C] {v : AddValuation C (WithTop ℝ)} (G : FGLaw C d)
    (hG : ∀ a, MvIsInt v (subst (twoVars C d) (G.F a))) (φ : Pt C 1 d) (hφ : NC φ)
    (hhom : comp1 φ G.F = addOf G.F (comp1 φ (pt C (n := 2) d 0)) (comp1 φ (pt C (n := 2) d 1)))
    {w : Fin d → MvPowerSeries τ C} (hw : NC w) :
    (fun i => ev1 (exPt (logFGLOf v G hG) w) (φ i)) = exPt (logFGLOf v G hG) (fun e => ∑ f, dLin φ e f • w f) := by
  funext i
  have hl := logOf_comp_hom G G φ hφ hhom
  have h1 := exp_eq_of_log_hom (logFGLOf v G hG) (logFGLOf v G hG) (fun e => subst (oneVar C d) (φ e))
    (fun e => constantCoeff_subst_eq_zero hs_oneVar cc_oneVar (hφ e)) (dLin φ) (fun e => by
      show subst _ (subst (oneVar C d) _) = ∑ f, dLin φ e f • subst (oneVar C d) _
      rw [subst_oneVar _ cc_oneVar _ hφ]
      have := congrFun hl e
      simp only [comp1] at this
      rw [this, ← coe_substAlgHom hs_oneVar]
      simp only [map_sum, map_smul]) _ w hw (fun _ => rfl) i
  refine Eq.trans ?_ h1.symm
  have hs : HasSubst (exPt (logFGLOf v G hG) w) := hasSubst_of_constantCoeff_zero (nc_exPt _ hw)
  show _ = subst (exPt (logFGLOf v G hG) w) _
  rw [subst_comp_subst_apply hs_oneVar hs]
  unfold ev1
  congr 1
  funext ⟨j, i⟩
  fin_cases j; simp [oneVar, subst_X hs]

section Core

variable {Λ : Type} [Fintype Λ]

def lin (u : Λ → Fin d → C) (c : Λ → C) : Fin d → MvPowerSeries Λ C :=
  fun e => ∑ l, (c l * u l e) • (X l : MvPowerSeries Λ C)

theorem nc_lin (u : Λ → Fin d → C) (c : Λ → C) : NC (lin u c) := fun e => by simp [lin]

theorem lin_add (u : Λ → Fin d → C) (c c' : Λ → C) : lin u c + lin u c' = lin u (c + c') := by
  funext e
  simp only [lin, Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib]

theorem lin_zero (u : Λ → Fin d → C) : lin u 0 = 0 := by
  funext e; simp [lin]

theorem mat_lin (u : Λ → Fin d → C) (M : Matrix (Fin d) (Fin d) C) (c z : Λ → C)
    (hM : ∀ l, c l ≠ 0 → M.mulVec (u l) = z l • u l) :
    (fun e => ∑ f, M e f • lin u c f) = lin u (fun l => c l * z l) := by
  funext e
  simp only [lin, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  by_cases hc : c l = 0
  · simp [hc]
  · have := congrFun (hM l hc) e
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [mul_assoc, ← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by ring

variable [CharZero C] {v : AddValuation C (WithTop ℝ)} {R : Type} [CommRing R] [Algebra R C] {O : Type} [CommRing O]
  [StarRing O] (B : FB R d O)

def colSum {m : ℕ} (x : Fin m → O) (s : List (Fin m)) : Pt C m d :=
  s.foldr (fun b acc => addOf (B.FK C) (comp1 (B.actK C (x b)) (pt C d b)) acc) 0

theorem nc_FK : NC (B.FK C) := (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G).const

theorem nc_actK (a : O) : NC (B.actK C a) := (GlobalTheory.FBMap.mapAct (algebraMap R C) B.A).const a

omit [CharZero C] in
theorem nc_pt {m : ℕ} (b : Fin m) : NC (pt C d b) := fun i => by simp [pt]

theorem nc_actPt {m : ℕ} (a : O) (b : Fin m) : NC (comp1 (B.actK C a) (pt C d b)) := fun i =>
  constantCoeff_substOnePointPowerSeries_eq_zero (nc_pt b) (nc_actK B a i)

theorem nc_colSum {m : ℕ} (x : Fin m → O) (s : List (Fin m)) : NC (colSum (C := C) B x s) := by
  induction s with
  | nil => intro i; simp [colSum]
  | cons b s ih => exact fun i => constantCoeff_germEvalPair_eq_zero (nc_actPt B _ b) ih (nc_FK B i)

omit [CharZero C] in
theorem int_map (hR : ∀ r, IsIntV v (algebraMap R C r)) {σ : Type} (f : MvPowerSeries σ R) :
    MvIsInt v (MvPowerSeries.map (algebraMap R C) f) := fun α => by
  rw [coeff_map]; exact hR _

theorem int_colSum (hR : ∀ r, IsIntV v (algebraMap R C r)) {m : ℕ} (x : Fin m → O) (s : List (Fin m))
    (i : Fin d) : MvIsInt v (colSum (C := C) B x s i) := by
  induction s generalizing i with
  | nil => intro α; simp [colSum, IsIntV]
  | cons b s ih =>
    refine ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (int_map hR _) ?_ (nc2 (nc_actPt B _ b) (nc_colSum B x s))
    rintro ⟨j, i⟩
    fin_cases j
    · refine ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (int_map hR _) ?_ (nc1 (nc_pt b))
      rintro ⟨j, i⟩ α
      fin_cases j
      show IsIntV v (coeff α (X (b, i)))
      rw [coeff_X]; split_ifs <;> simp [IsIntV]
    · exact ih i

variable {G : FGLaw C d} (hGF : G.F = B.FK C) (hG : ∀ a, MvIsInt v (subst (twoVars C d) (G.F a)))
  {m : ℕ} (col : Λ → Fin m) (u : Λ → Fin d → C) (σ : Fin m → O → C)
  (heig : ∀ a l, (dAct C B a).mulVec (u l) = σ (col l) a • u l)

def colExp (L : LogFGL v d) : Fin m × Fin d → MvPowerSeries Λ C :=
  fun q => exPt L (lin u fun l => if col l = q.1 then 1 else 0) q.2

omit [CharZero C] in
theorem hs_colExp (L : LogFGL v d) : HasSubst (colExp col u L) :=
  hasSubst_of_constantCoeff_zero fun q => nc_exPt L (nc_lin _ _) q.2

include hGF heig in
theorem subst_actPt (a : O) (b : Fin m) :
    (fun i => subst (colExp col u (logFGLOf v G hG)) (comp1 (B.actK C a) (pt C d b) i)) =
      exPt (logFGLOf v G hG) (lin u fun l => if col l = b then σ b a else 0) := by
  have hs := hs_colExp col u (logFGLOf v G hG)
  have hh := (GlobalTheory.FBMap.mapAct (algebraMap R C) B.A).hom a
  rw [add_pt] at hh
  have h1 := exPt_hom G hG (B.actK C a) (nc_actK B a) (by rw [hGF]; exact hh)
    (nc_lin u fun l => if col l = b then 1 else 0)
  rw [mat_lin u (dLin (B.actK C a)) _ (fun l => σ (col l) a) fun l _ => heig a l] at h1
  have e : (fun l => (if col l = b then (1 : C) else 0) * σ (col l) a) = fun l => if col l = b then σ b a else 0 := by
    funext l; split_ifs with hl <;> simp [*]
  rw [← e, ← h1]
  funext i
  refine (subst_substOnePointPowerSeries hs (nc_pt b) _).trans ?_
  congr 1
  funext e
  exact subst_X hs _

include hGF heig in
theorem subst_colSum (x : Fin m → O) (s : List (Fin m)) :
    (fun i => subst (colExp col u (logFGLOf v G hG)) (colSum (C := C) B x s i)) =
      exPt (logFGLOf v G hG) (lin u fun l => (s.map fun b => if col l = b then σ b (x b) else 0).sum) := by
  have hs := hs_colExp col u (logFGLOf v G hG)
  induction s with
  | nil =>
    funext i
    simp only [List.map_nil, List.sum_nil]
    rw [show (fun _ : Λ => (0 : C)) = 0 from rfl, lin_zero, exPt_zero]
    exact subst_zero' hs
  | cons b s ih =>
    funext i
    refine (subst_substTwoPointsPowerSeries hs (nc_actPt B _ b) (nc_colSum B x s) _).trans ?_
    rw [ih, subst_actPt B hGF hG col u σ heig]
    refine (congrFun (exPt_add (logFGLOf v G hG) (nc_FK B) (fun a => by rw [← hGF]; rfl) (nc_lin _ _)
      (nc_lin _ _)) i).trans ?_
    rw [lin_add]
    rfl

def coefs {n : ℕ} (γ : Fin m → Fin n → C) (δ : Fin m → Fin m → C) : Fin n ⊕ Fin m ⊕ Fin m × Fin m → Λ → C :=
  Sum.elim (fun j l => γ (col l) j)
    (Sum.elim (fun b l => if col l = b then 1 else 0) fun q l => if col l = q.2 then δ q.1 q.2 else 0)

theorem subst_univ (L : LogFGL v d) {hL : PS C 1 d} {h : PS C 2 d} (cL : constantCoeff hL = 0)
    (ch : constantCoeff h = 0) (k : ℕ) {n : ℕ} (g : PS C n d) (c : Fin n ⊕ Fin m ⊕ Fin m × Fin m → Λ → C) :
    subst (fun s : (Fin n ⊕ Fin m ⊕ Fin m × Fin m) × Fin d =>
        ∑ l, (c s.1 l * u l s.2) • (X l : MvPowerSeries Λ C))
      (germ (τ := (Fin n ⊕ Fin m ⊕ Fin m × Fin m) × Fin d) hL h k g
        (fun j => exPt L fun e => X (Sum.inl j, e)) (fun b => exPt L fun e => X (Sum.inr (Sum.inl b), e))
        fun b b' => exPt L fun e => X (Sum.inr (Sum.inr (b, b')), e)) =
      germ hL h k g (fun j => exPt L (lin u (c (Sum.inl j)))) (fun b => exPt L (lin u (c (Sum.inr (Sum.inl b)))))
        fun b b' => exPt L (lin u (c (Sum.inr (Sum.inr (b, b'))))) := by
  have hs : HasSubst (fun s : (Fin n ⊕ Fin m ⊕ Fin m × Fin m) × Fin d =>
      ∑ l, (c s.1 l * u l s.2) • (X l : MvPowerSeries Λ C)) :=
    hasSubst_of_constantCoeff_zero fun s => nc_lin u (c s.1) s.2
  have hX : ∀ j : Fin n ⊕ Fin m ⊕ Fin m × Fin m,
      NC fun e : Fin d => (X (j, e) : MvPowerSeries ((Fin n ⊕ Fin m ⊕ Fin m × Fin m) × Fin d) C) :=
    fun j e => by simp
  rw [subst_germ k g cL ch hs (fun _ => nc_exPt L (hX _)) (fun _ => nc_exPt L (hX _)) fun _ _ => nc_exPt L (hX _)]
  simp only [subst_exPt L hs (hX _), subst_X hs]
  rfl

include hGF heig in

theorem exists_germ_close (hR : ∀ r, IsIntV v (algebraMap R C r)) {h : PS C 2 d} (hc : B.IsCanonGauge C h) (w0 : O)
    (hu : ∀ l e, IsIntV v (u l e)) (hσ : ∀ b a, IsIntV v (σ b a)) {n : ℕ}
    (hU : ∀ x : Fin m → Fin n → O, ∃ U : PS R m d, FB.toK C U = FB.expS C ((∑ j : Fin n, ev (n := m)
      ![colSum B (fun b => x b j) (List.finRange m)] (B.hL C h w0)) - ∑ b : Fin m, ∑ b' : Fin m, ev (n := m)
        ![pt C d b, comp1 (B.actK C (w0 * ∑ j : Fin n, star (x b j) * x b' j)) (pt C d b')] h))
    (P : MvPolynomial Λ C) (k : ℕ) (g : PS C n d) (hg : MvIsInt v g) :
    ∃ K : ℝ, ∀ (M : ℝ) (x : Fin m → Fin n → O) (β : Fin m → Fin n → C), (∀ b j, IsIntV v (β b j)) →
      (∀ b j, ((M : ℝ) : WithTop ℝ) ≤ v (β b j - σ b (x b j))) →
      (∀ b b', ((M : ℝ) : WithTop ℝ) ≤ v (σ b' (w0 * ∑ j : Fin n, star (x b j) * x b' j))) →
      ∃ f : PS C m d, MvIsInt v f ∧ ((M - K : ℝ) : WithTop ℝ) ≤
        v (derivAt0 P (subst (fun q : Fin n × Fin d => exPt (logFGLOf v G hG) (lin u fun l => β (col l) q.1) q.2)
            (g * FB.expS C ((k : C) • ∑ j : Fin n, ev (n := n) ![pt C d j] (B.hL C h w0)))) -
          derivAt0 P (subst (colExp col u (logFGLOf v G hG)) f)) := by
  set L := logFGLOf v G hG with hL
  have ch : constantCoeff h = 0 := by
    have h0 := congrArg constantCoeff (substTwoPointsPowerSeries_zero_of_vanish_first_axis (τ := Fin 2 × Fin d) (a := 0) (fun _ => by simp) hc.ax1)
    have e : ev2 (0 : Fin d → PS C 2 d) 0 h = subst ((0 : Fin 2 × Fin d → C) • X) h := by
      unfold ev2; congr 1; funext ⟨j, i⟩; fin_cases j <;> simp
    rw [e, ← rescale_eq_subst, rescale_zero_apply] at h0
    simpa using h0
  have cL : constantCoeff (B.hL C h w0) = 0 := constantCoeff_germEvalPair_eq_zero (nc_pt 0) (nc_actPt B w0 0) ch
  obtain ⟨K, hK⟩ := GlobalTheory.FGDepth.derivAt0_subst_linear_lipschitz C v ((Fin n ⊕ Fin m ⊕ Fin m × Fin m) × Fin d) Λ P
    (germ (τ := (Fin n ⊕ Fin m ⊕ Fin m × Fin m) × Fin d) (B.hL C h w0) h k g
      (fun j => exPt L fun e => X (Sum.inl j, e)) (fun b => exPt L fun e => X (Sum.inr (Sum.inl b), e))
      fun b b' => exPt L fun e => X (Sum.inr (Sum.inr (b, b')), e))
  refine ⟨K, fun M x β hβ h1 h2 => ?_⟩
  obtain ⟨U, hU⟩ := hU x
  have hΦ : ∀ j, NC (colSum (C := C) B (fun b => x b j) (List.finRange m)) := fun j => nc_colSum B _ _
  have imul : ∀ a b : C, IsIntV v a → IsIntV v b → IsIntV v (a * b) := fun a b ha hb => by
    unfold IsIntV at *
    rw [v.map_mul]; exact add_nonneg ha hb
  have ico : ∀ (γ : Fin m → Fin n → C) (δ : Fin m → Fin m → C), (∀ b j, IsIntV v (γ b j)) →
      (∀ b j, IsIntV v (δ b j)) → ∀ s l, IsIntV v (coefs col γ δ s l) := by
    rintro γ δ hγ hδ (j | b | q) l
    · exact hγ _ _
    · simp only [coefs, Sum.elim_inl, Sum.elim_inr]; split_ifs <;> simp [IsIntV]
    · simp only [coefs, Sum.elim_inr]; split_ifs
      · exact hδ _ _
      · simp [IsIntV]
  have key := hK M (fun s l => coefs col β 0 s.1 l * u l s.2)
    (fun s l => coefs col (fun b j => σ b (x b j))
      (fun b b' => σ b' (w0 * ∑ j : Fin n, star (x b j) * x b' j)) s.1 l * u l s.2)
    (fun s l => imul _ _ (ico _ _ hβ (fun _ _ => by simp [IsIntV]) _ _) (hu _ _))
    (fun s l => imul _ _ (ico _ _ (fun _ _ => hσ _ _) (fun _ _ => hσ _ _) _ _) (hu _ _)) (by
      rintro ⟨s, e⟩ l
      rw [← sub_mul, v.map_mul]
      refine le_add_of_le_of_nonneg ?_ (hu _ _)
      rcases s with j | b | q
      · exact h1 _ _
      · simp [coefs]
      · simp only [coefs, Sum.elim_inr]; split_ifs
        · simpa using h2 q.1 q.2
        · simp)
  rw [subst_univ u L cL ch, subst_univ u L cL ch] at key
  refine ⟨ev (fun j => colSum B (fun b => x b j) (List.finRange m)) g * FB.toK C U ^ k, ?_, ?_⟩
  · rw [← map_pow]
    intro α
    rw [coeff_mul]
    exact v.map_le_sum fun q _ => imul _ _ (ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v hg
      (fun q => int_colSum B hR _ _ _) (fun q => hΦ q.1 q.2) _) (int_map hR _ _)
  convert key using 4
  · have hp : ∀ j, NC (exPt L (lin u fun l => β (col l) j)) := fun j => nc_exPt L (nc_lin _ _)
    have hs : HasSubst (fun q : Fin n × Fin d => exPt L (lin u fun l => β (col l) q.1) q.2) :=
      hasSubst_of_constantCoeff_zero fun q => hp q.1 q.2
    have e0 : g * FB.expS C ((k : C) • ∑ j : Fin n, ev (n := n) ![pt C d j] (B.hL C h w0)) =
        germ (m := 0) (B.hL C h w0) h k g (pt C d) (fun _ => 0) fun _ _ => 0 := by
      unfold germ
      rw [show (fun q : Fin n × Fin d => pt C d q.1 q.2) = X from rfl, subst_self]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
      rfl
    rw [e0, subst_germ k g cL ch hs nc_pt (fun _ _ => by simp) fun _ _ _ => by simp]
    have e1 : ∀ b b' : Fin m, coefs col β 0 (Sum.inr (Sum.inr (b, b'))) = 0 := fun b b' => by
      funext l; simp [coefs]
    simp only [germ, pt, subst_X hs, e1, lin_zero, exPt_zero, substTwoPointsPowerSeries_zero_of_vanish_first_axis (nc_exPt L (nc_lin _ _)) hc.ax1,
      Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero]
    rfl
  · have hs := hs_colExp col u L
    have e0 : ev (fun j => colSum B (fun b => x b j) (List.finRange m)) g * FB.toK C U ^ k =
        germ (B.hL C h w0) h k g (fun j => colSum B (fun b => x b j) (List.finRange m)) (pt C d)
          fun b b' => comp1 (B.actK C (w0 * ∑ j : Fin n, star (x b j) * x b' j)) (pt C d b') := by
      rw [hU, ← GlobalTheory.JetSer.IntTrans.expS_nsmul]
      · rfl
      · rw [map_sub, map_sum, map_sum, sub_eq_zero]
        refine (Finset.sum_eq_zero fun j _ => constantCoeff_substOnePointPowerSeries_eq_zero (hΦ j) cL).trans (Finset.sum_eq_zero fun b _ => ?_).symm
        rw [map_sum]
        exact Finset.sum_eq_zero fun b' _ => constantCoeff_germEvalPair_eq_zero (nc_pt b) (nc_actPt B _ b') ch
    rw [e0, subst_germ k g cL ch hs hΦ nc_pt fun b b' => nc_actPt B _ b']
    congr 1
    · funext j
      rw [subst_colSum B hGF hG col u σ heig]
      congr 2
      funext l
      rw [← Fin.sum_univ_def]
      simp [coefs]
    · funext b e
      exact subst_X hs _
    · funext b b'
      exact subst_actPt B hGF hG col u σ heig _ _

end Core

end GlobalTheory.ColApprox
