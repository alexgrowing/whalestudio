import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

noncomputable section

namespace GlobalTheory.RowLaw.CvEnd

open MvPowerSeries

variable {C : Type} [Field C]

section Ord

variable {σ τ : Type}

def ordGe (C : Type) [Field C] (w : τ → ℕ) (n : ℕ) : Submodule C (MvPowerSeries τ C) where
  carrier := {F | ∀ e : τ →₀ ℕ, Finsupp.weight w e < n → coeff e F = 0}
  add_mem' := fun {a b} ha hb e he => by rw [map_add, ha e he, hb e he, add_zero]
  zero_mem' := fun e _ => map_zero _
  smul_mem' := fun c a ha e he => by rw [coeff_smul, ha e he, mul_zero]

theorem mem_ordGe {w : τ → ℕ} {n : ℕ} {F : MvPowerSeries τ C} :
    F ∈ ordGe C w n ↔ (n : ℕ∞) ≤ weightedOrder w F :=
  ⟨fun h => nat_le_weightedOrder w h, fun h e he =>
    coeff_eq_zero_of_lt_weightedOrder w (lt_of_lt_of_le (by exact_mod_cast he) h)⟩

theorem ordGe_zero {w : τ → ℕ} (F : MvPowerSeries τ C) : F ∈ ordGe C w 0 :=
  fun _ he => absurd he (Nat.not_lt_zero _)

theorem ordGe_mul {w : τ → ℕ} {m n : ℕ} {F G : MvPowerSeries τ C} (hF : F ∈ ordGe C w m) (hG : G ∈ ordGe C w n) :
    F * G ∈ ordGe C w (m + n) := by
  rw [mem_ordGe] at *
  refine le_trans ?_ (le_weightedOrder_mul w)
  push_cast
  exact add_le_add hF hG

theorem ordGe_pow {w : τ → ℕ} {F : MvPowerSeries τ C} (hF : F ∈ ordGe C w 1) (k : ℕ) : F ^ k ∈ ordGe C w k := by
  induction k with
  | zero => exact ordGe_zero _
  | succ k ih => rw [pow_succ]; exact ordGe_mul ih hF

theorem ordGe_X {w : τ → ℕ} (s : τ) : (X s : MvPowerSeries τ C) ∈ ordGe C w (w s) := by
  classical
  intro e he
  rw [coeff_X, if_neg]
  rintro rfl
  simp [Finsupp.weight_single] at he

theorem ordGe_subst {w : τ → ℕ} {w' : σ → ℕ} {n : ℕ} {a : σ → MvPowerSeries τ C} (ha : HasSubst a)
    (hw : ∀ s, a s ∈ ordGe C w (w' s)) {f : MvPowerSeries σ C} (hf : f ∈ ordGe C w' n) :
    subst a f ∈ ordGe C w n := by
  rw [mem_ordGe]
  refine le_trans ?_ (le_weightedOrder_subst w ha f)
  simp only [ne_eq, le_iInf_iff]
  intro e he
  have h1 : n ≤ Finsupp.weight w' e := not_lt.1 fun h => he (hf e h)
  refine le_trans (Nat.cast_le.2 h1 : (n : ℕ∞) ≤ _) ?_
  simp only [Finsupp.weight_apply, Finsupp.sum, Function.comp_apply, Nat.cast_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
  exact mul_le_mul_right (mem_ordGe.1 (hw i)) _

theorem weight_one (e : σ →₀ ℕ) : Finsupp.weight (fun _ => 1) e = e.degree := by
  rw [Finsupp.degree_eq_weight_one]

theorem ordGe_one_of_const {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) : f ∈ ordGe C (fun _ => 1) 1 := by
  intro e he
  rw [weight_one] at he
  have : e = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]; omega
  rw [this, coeff_zero_eq_constantCoeff_apply, hf]

theorem coeff_mvExp_weight_one {w : τ → ℕ} {G : MvPowerSeries τ C} (hG : G ∈ ordGe C w 1) (e : τ →₀ ℕ)
    (he : Finsupp.weight w e = 1) : coeff e (mvExp G) = coeff e G := by
  classical
  have hne : e ≠ 0 := by
    rintro rfl
    simp at he
  show (∑ k ∈ Finset.range (e.degree + 1), coeff e (G ^ k) / (k.factorial : C)) = _
  rw [Finset.sum_eq_single 1]
  · simp
  · intro k _ hk
    by_cases h0 : k = 0
    · rw [h0, pow_zero, coeff_one, if_neg hne, zero_div]
    · rw [ordGe_pow hG k e (by omega), zero_div]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_range]
    have : e.degree ≠ 0 := fun h => hne ((Finsupp.degree_eq_zero_iff e).1 h)
    omega

end Ord

section Int

variable {V : VF C} {σ τ : Type}

theorem intS_mul {F G : MvPowerSeries τ C} (hF : IntS V F) (hG : IntS V G) : IntS V (F * G) := by
  classical
  intro e
  rw [coeff_mul]
  exact VF.Ge.sum fun p _ => (hF _).mul_int (hG _)

theorem intS_one : IntS V (1 : MvPowerSeries τ C) := by
  classical
  intro e
  rw [coeff_one]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem intS_subst {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (hi : ∀ s, IntS V (a s))
    {F : MvPowerSeries σ C} (hF : IntS V F) : IntS V (subst a F) := by
  intro e
  rw [coeff_subst ha]
  refine finsum_induction (fun x => V.Ge 0 x) (VF.Ge.zero 0) (fun _ _ => VF.Ge.add) fun μ => ?_
  rw [smul_eq_mul]
  refine (hF μ).mul_int ?_
  revert e
  show IntS V _
  refine Finset.prod_induction _ (IntS V) (fun _ _ => intS_mul) intS_one fun s _ => ?_
  show IntS V (a s ^ μ s)
  induction μ s with
  | zero => rw [pow_zero]; exact intS_one
  | succ k ih => rw [pow_succ]; exact intS_mul ih (hi s)

theorem isCv_along [Finite σ] {γ : σ → PowerSeries C} (hγ : IsCv V γ) {ι : Type} {f : ι → MvPowerSeries σ C}
    (h0 : ∀ i, constantCoeff (f i) = 0) (hf : ∀ i, IntS V (f i)) : IsCv V fun i => alongCv γ (f i) := by
  intro i
  refine ⟨constantCoeff_subst_zero (τ := Unit) (fun s => (hγ s).1) (h0 i), fun n => ?_⟩
  refine intS_subst (τ := Unit) (hasSubst_of_constantCoeff_zero fun s => (hγ s).1) (fun s e => ?_) (hf i)
    (Finsupp.single () n)
  have he : e = Finsupp.single () (e ()) := Finsupp.unique_single e
  rw [he]
  exact (hγ s).2 _

end Int

section Lin

variable {κ : Type} [Fintype κ]

def wz (κ : Type) : Fin 2 × κ → ℕ := fun p => p.1.val

def e0 (κ : Type) : κ ↪ Fin 2 × κ := ⟨fun x => ((0 : Fin 2), x), fun _ _ h => congrArg Prod.snd h⟩

def em (i : κ) (μ : κ →₀ ℕ) : Fin 2 × κ →₀ ℕ := μ.embDomain (e0 κ) + Finsupp.single ((1 : Fin 2), i) 1

def dz (i : κ) : MvPowerSeries (Fin 2 × κ) C →ₗ[C] MvPowerSeries κ C where
  toFun F := fun μ => coeff (em i μ) F
  map_add' F G := by funext μ; exact map_add (coeff (em i μ)) F G
  map_smul' c F := by funext μ; exact map_smul (coeff (em i μ)) c F

omit [Fintype κ] in
theorem coeff_dz (i : κ) (F : MvPowerSeries (Fin 2 × κ) C) (μ : κ →₀ ℕ) : coeff μ (dz i F) = coeff (em i μ) F := rfl

omit [Fintype κ] in
theorem emb_zero (μ : κ →₀ ℕ) (x : κ) : μ.embDomain (e0 κ) (0, x) = μ x := Finsupp.embDomain_apply_self (e0 κ) μ x

omit [Fintype κ] in
theorem emb_one (μ : κ →₀ ℕ) (x : κ) : μ.embDomain (e0 κ) (1, x) = 0 := by
  apply Finsupp.embDomain_notin_range
  rintro ⟨y, hy⟩
  exact absurd (congrArg Prod.fst hy) (by show (0 : Fin 2) ≠ 1; decide)

theorem weight_wz (e : Fin 2 × κ →₀ ℕ) : Finsupp.weight (wz κ) e = ∑ x, e (1, x) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [wz]

theorem weight_em (i : κ) (μ : κ →₀ ℕ) : Finsupp.weight (wz κ) (em i μ) = 1 := by
  classical
  rw [weight_wz]
  simp [em, emb_one, Finsupp.single_apply]

theorem exists_em (e : Fin 2 × κ →₀ ℕ) (he : Finsupp.weight (wz κ) e = 1) : ∃ i μ, e = em i μ := by
  classical
  rw [weight_wz] at he
  obtain ⟨i, hi⟩ := finsupp_deg_one (Finsupp.equivFunOnFinite.symm fun x => e (1, x)) (by
    rw [Finsupp.degree_eq_sum]; simpa using he)
  refine ⟨i, Finsupp.equivFunOnFinite.symm fun x => e (0, x), ?_⟩
  ext ⟨g, x⟩
  have := DFunLike.congr_fun hi x
  fin_cases g
  · simp [em, emb_zero, Finsupp.single_apply]
  · simpa [em, emb_one, Finsupp.single_apply] using this

theorem dz_of_two (i : κ) {F : MvPowerSeries (Fin 2 × κ) C} (hF : F ∈ ordGe C (wz κ) 2) : dz i F = 0 := by
  ext μ
  rw [coeff_dz, hF _ (by rw [weight_em]; omega), map_zero]

theorem dz_X_mul [DecidableEq κ] (i j : κ) (f : MvPowerSeries κ C) :
    dz i (X ((1 : Fin 2), j) * rename (e0 κ) f) = if i = j then f else 0 := by
  ext μ
  rw [coeff_dz, X, coeff_monomial_mul, one_mul]
  by_cases hij : i = j
  · subst hij
    rw [if_pos (by unfold em; exact le_add_self), if_pos rfl]
    unfold em
    rw [add_tsub_cancel_right, coeff_embDomain_rename]
  · rw [if_neg hij, if_neg, map_zero]
    rw [Finsupp.single_le_iff]
    simp [em, emb_one, Finsupp.single_apply, hij]

theorem taylor {F : MvPowerSeries (Fin 2 × κ) C} (hF : F ∈ ordGe C (wz κ) 1) :
    F - ∑ j, X ((1 : Fin 2), j) * rename (e0 κ) (dz j F) ∈ ordGe C (wz κ) 2 := by
  classical
  intro e he
  by_cases h1 : Finsupp.weight (wz κ) e = 1
  · obtain ⟨i, μ, rfl⟩ := exists_em e h1
    rw [← coeff_dz, map_sub, map_sum]
    simp [dz_X_mul]
  · have : F - ∑ j, X ((1 : Fin 2), j) * rename (e0 κ) (dz j F) ∈ ordGe C (wz κ) 1 :=
      Submodule.sub_mem _ hF (Submodule.sum_mem _ fun j _ => ordGe_mul (ordGe_X ((1 : Fin 2), j)) (ordGe_zero _))
    exact this e (by omega)

end Lin

section Chart

variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}

theorem sg_eq (X : RawChart C d I κ) (v : κ → C) : X.sg v = -∑ i, v i • dz i X.h := by
  ext μ
  rw [map_neg, map_sum]
  show -∑ i, v i * coeff (μ.mapDomain (fun x : κ => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), i) 1) X.h = _
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_smul, coeff_dz, em, Finsupp.embDomain_eq_mapDomain]
  rfl

theorem lg_const (H : RLaw X V) (i : κ) : constantCoeff (X.lg i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, H.lin i 0 (by simp), coeff_zero_eq_constantCoeff_apply, constantCoeff_X]

theorem h_ord (H : RLaw X V) : X.h ∈ ordGe C (wz κ) 1 := by
  intro e he
  refine H.axes 1 e fun s hs h1 => ?_
  rw [weight_wz, Nat.lt_one_iff, Finset.sum_eq_zero_iff] at he
  apply Finsupp.mem_support_iff.1 hs
  rw [← he s.2 (Finset.mem_univ _), ← h1]

theorem subst_sum_smul {σ τ ι : Type} [Fintype ι] {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (c : ι → C)
    (f : ι → MvPowerSeries σ C) : subst a (∑ y, c y • f y) = ∑ y, c y • subst a (f y) := by
  rw [← coe_substAlgHom ha, map_sum]
  simp only [map_smul]

theorem lin_const (H : RLaw X V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (x : κ) : constantCoeff (∑ y, M x y • subst a (X.lg y)) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [constantCoeff_smul, constantCoeff_subst_zero ha (lg_const H y), smul_zero]

theorem matrixEnd_const (H : RLaw X V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (i : κ) : constantCoeff (endP X M a i) = 0 :=
  constantCoeff_subst_zero (lin_const H M ha) (H.exc i)

theorem lg_endP (H : RLaw X V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (i : κ) :
    subst (endP X M a) (X.lg i) = ∑ y, M i y • subst a (X.lg y) := by
  have hL := hasSubst_of_constantCoeff_zero (lin_const H M ha)
  have := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero H.exc) hL (X.lg i)
  rw [H.lgex, subst_X hL] at this
  exact this.symm

theorem subst_endP (H : RLaw X V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (i : κ) :
    subst a (endP X M (MvPowerSeries.X : κ → MvPowerSeries κ C) i) = endP X M a i := by
  have hX : ∀ i : κ, constantCoeff (MvPowerSeries.X i : MvPowerSeries κ C) = 0 := fun i => constantCoeff_X i
  have hA := hasSubst_of_constantCoeff_zero ha
  unfold endP
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (lin_const H M hX)) hA]
  congr 1
  funext x
  rw [subst_sum_smul hA]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [subst_self]
  rfl

theorem lg_two (H : RLaw X V) {τ : Type} {w : τ → ℕ} {b : κ → MvPowerSeries τ C}
    (hb : ∀ i, constantCoeff (b i) = 0) (hw : ∀ i, b i ∈ ordGe C w 1) (i : κ) :
    subst b (X.lg i) - b i ∈ ordGe C w 2 := by
  have hB := hasSubst_of_constantCoeff_zero hb
  have h : X.lg i - MvPowerSeries.X i ∈ ordGe C (fun _ : κ => 1) 2 := by
    intro e he
    rw [weight_one] at he
    rw [map_sub, H.lin i e (by omega), sub_self]
  have := ordGe_subst hB hw h
  rwa [subst_sub hB, subst_X hB] at this

theorem one_le_weightedOrder_expMulLog (H : RLaw X V) (M : Matrix κ κ C) {τ : Type} {w : τ → ℕ} {b : κ → MvPowerSeries τ C}
    (hb : ∀ i, constantCoeff (b i) = 0) (hw : ∀ i, b i ∈ ordGe C w 1) (i : κ) :
    endP X M b i ∈ ordGe C w 1 :=
  ordGe_subst (w' := fun _ => 1) (hasSubst_of_constantCoeff_zero (lin_const H M hb))
    (fun _ => Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _
      (ordGe_subst (w' := fun _ => 1) (hasSubst_of_constantCoeff_zero hb) hw (ordGe_one_of_const (lg_const H y))))
    (ordGe_one_of_const (H.exc i))

theorem matrixEnd_two (H : RLaw X V) (M : Matrix κ κ C) {τ : Type} {w : τ → ℕ} {b : κ → MvPowerSeries τ C}
    (hb : ∀ i, constantCoeff (b i) = 0) (hw : ∀ i, b i ∈ ordGe C w 1) (i : κ) :
    endP X M b i - ∑ y, M i y • b y ∈ ordGe C w 2 := by
  have h1 := lg_two H (matrixEnd_const H M hb) (one_le_weightedOrder_expMulLog H M hb hw) i
  rw [lg_endP H M hb] at h1
  have h2 : ∑ y, M i y • (subst b (X.lg y) - b y) ∈ ordGe C w 2 :=
    Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (lg_two H hb hw y)
  have h3 := Submodule.sub_mem _ h2 h1
  simp only [smul_sub, Finset.sum_sub_distrib] at h3
  convert h3 using 1
  ring

theorem hasSubst_pair {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) : HasSubst fun p : Fin 2 × κ => if p.1 = 0 then a p.2 else b p.2 := by
  apply hasSubst_of_constantCoeff_zero
  intro p
  split_ifs
  · exact ha _
  · exact hb _

theorem pair_ord {τ : Type} {w : τ → ℕ} (a : κ → MvPowerSeries τ C) {b : κ → MvPowerSeries τ C}
    (hw : ∀ i, b i ∈ ordGe C w 1) (p : Fin 2 × κ) :
    (if p.1 = 0 then a p.2 else b p.2) ∈ ordGe C w (wz κ p) := by
  obtain ⟨g, x⟩ := p
  fin_cases g
  · exact ordGe_zero _
  · exact hw x

theorem hAt_ord (H : RLaw X V) {τ : Type} {w : τ → ℕ} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (hw : ∀ i, b i ∈ ordGe C w 1) :
    hAt X a b ∈ ordGe C w 1 :=
  ordGe_subst (hasSubst_pair ha hb) (pair_ord a hw) (h_ord H)

theorem hAt_two (H : RLaw X V) {τ : Type} {w : τ → ℕ} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (hw : ∀ i, b i ∈ ordGe C w 1) :
    hAt X a b - ∑ j, b j * subst a (dz j X.h) ∈ ordGe C w 2 := by
  have hP := hasSubst_pair ha hb
  have := ordGe_subst hP (pair_ord a hw) (taylor (h_ord H))
  rw [subst_sub hP, ← coe_substAlgHom hP, map_sum] at this
  convert this using 2
  · rw [coe_substAlgHom hP]; rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, coe_substAlgHom hP, subst_X hP, rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hP]
    congr 1
    congr 1
    funext x
    rw [Function.comp_apply, subst_X hP]
    rfl

theorem gp_const {n : ℕ} (j : Fin n) (i : κ) : constantCoeff (gp C κ j i) = 0 := constantCoeff_X _

theorem gp_ord (i : κ) : gp C κ (1 : Fin 2) i ∈ ordGe C (wz κ) 1 := ordGe_X ((1 : Fin 2), i)

theorem subst_gp (f : MvPowerSeries κ C) : subst (gp C κ (0 : Fin 2)) f = rename (e0 κ) f := by
  rw [rename_eq_subst]
  rfl

theorem dz_left (H : RLaw X V) (M : Matrix κ κ C) (i : κ) :
    dz i (hAt X (endP X M (gp C κ (0 : Fin 2))) (gp C κ 1)) =
      subst (endP X M (MvPowerSeries.X : κ → MvPowerSeries κ C)) (dz i X.h) := by
  classical
  have hX : ∀ i : κ, constantCoeff (MvPowerSeries.X i : MvPowerSeries κ C) = 0 := fun i => constantCoeff_X i
  have h := dz_of_two i (hAt_two H (matrixEnd_const H M (gp_const (0 : Fin 2))) (gp_const 1) gp_ord)
  rw [map_sub, sub_eq_zero, map_sum] at h
  have e : ∀ f : MvPowerSeries κ C, subst (endP X M (gp C κ (0 : Fin 2))) f =
      rename (e0 κ) (subst (endP X M (MvPowerSeries.X : κ → MvPowerSeries κ C)) f) := by
    intro f
    rw [← subst_gp, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (matrixEnd_const H M hX))
      (hasSubst_of_constantCoeff_zero (gp_const _))]
    congr 1
    funext x
    rw [subst_endP H M (gp_const _)]
  rw [h]
  simp only [e]
  unfold gp
  simp [dz_X_mul]

theorem dz_right (H : RLaw X V) (M : Matrix κ κ C) (i : κ) :
    dz i (hAt X (gp C κ (0 : Fin 2)) (endP X M (gp C κ 1))) = ∑ j, M j i • dz j X.h := by
  classical
  have h := dz_of_two i (hAt_two H (gp_const (0 : Fin 2)) (matrixEnd_const H M (gp_const 1))
    (one_le_weightedOrder_expMulLog H M (gp_const 1) gp_ord))
  rw [map_sub, sub_eq_zero, map_sum] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := dz_of_two i (ordGe_mul (matrixEnd_two H M (gp_const (1 : Fin 2)) gp_ord j)
    (ordGe_zero (subst (gp C κ (0 : Fin 2)) (dz j X.h))))
  rw [sub_mul, map_sub, sub_eq_zero] at h2
  rw [h2, subst_gp, Finset.sum_mul, map_sum]
  unfold gp
  simp [dz_X_mul]

theorem defect_int (H : RLaw X V) {M M' : Matrix κ κ C} (hE : IsEnd X V M M') {v : κ → C} (hv : ∀ i, V.Ge 0 (v i)) :
    IntS V (subst (endP X M (MvPowerSeries.X : κ → MvPowerSeries κ C)) (X.sg v) - X.sg (M'.mulVec v)) := by
  have hX : ∀ i : κ, constantCoeff (MvPowerSeries.X i : MvPowerSeries κ C) = 0 := fun i => constantCoeff_X i
  have hS := hasSubst_of_constantCoeff_zero (matrixEnd_const H M hX)
  set G := hAt X (endP X M (gp C κ (0 : Fin 2))) (gp C κ 1) - hAt X (gp C κ 0) (endP X M' (gp C κ 1)) with hG
  have hG1 : G ∈ ordGe C (wz κ) 1 :=
    Submodule.sub_mem _ (hAt_ord H (matrixEnd_const H M (gp_const _)) (gp_const _) gp_ord)
      (hAt_ord H (gp_const _) (matrixEnd_const H M' (gp_const _)) (one_le_weightedOrder_expMulLog H M' (gp_const _) gp_ord))
  have key : subst (endP X M (MvPowerSeries.X : κ → MvPowerSeries κ C)) (X.sg v) - X.sg (M'.mulVec v) =
      -∑ i, v i • dz i G := by
    rw [sg_eq, sg_eq, ← coe_substAlgHom hS, map_neg, coe_substAlgHom hS, subst_sum_smul hS]
    simp only [hG, map_sub, dz_left H, dz_right H, smul_sub, Finset.sum_sub_distrib, Matrix.mulVec, dotProduct,
      Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
    ring
  rw [key]
  intro μ
  rw [map_neg, map_sum]
  refine (VF.Ge.sum fun i _ => ?_).neg
  rw [coeff_smul, coeff_dz, ← coeff_mvExp_weight_one hG1 _ (weight_em i μ)]
  exact (hv i).mul_int (hE.2.2 _)

theorem sg_smul (X : RawChart C d I κ) (c : C) (v : κ → C) : X.sg (c • v) = c • X.sg v := by
  rw [sg_eq, sg_eq, smul_neg, Finset.smul_sum]
  simp only [Pi.smul_apply, smul_eq_mul, smul_smul]

end Chart

theorem end_mem_Cv : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (M M' : Matrix κ κ C) (s : JJ I g → C), IsEnd X V M M' → (∀ q, V.Ge 0 (s q)) → (∀ q, M'.mulVec (X.u (1 - g) q) = s q • X.u (1 - g) q) → ∀ a ∈ Cv X V g, ((fun i => ∑ j, M i j • a.1 j, fun q => s q • a.2 q) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X H g M M' s hE hs hu a ha
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := ha
  have hX : ∀ i : κ, constantCoeff (MvPowerSeries.X i : MvPowerSeries κ C) = 0 := fun i => constantCoeff_X i
  have hγ0 : ∀ i, constantCoeff (γ i : MvPowerSeries Unit C) = 0 := fun i => (hγ i).1
  have hΓ := hasSubst_of_constantCoeff_zero hγ0
  have hS := hasSubst_of_constantCoeff_zero (matrixEnd_const H M hX)
  have hsg := X.constantCoeff_sg (H.axes 0)
  have hK := isCv_along hγ (f := fun q : JJ I g =>
      subst (endP X M (MvPowerSeries.X : κ → MvPowerSeries κ C)) (X.sg (X.u (1 - g) q)) -
        X.sg (M'.mulVec (X.u (1 - g) q)))
    (fun q => by rw [map_sub, constantCoeff_subst_zero (matrixEnd_const H M hX) (hsg _), hsg, sub_self])
    (fun q => defect_int H hE (H.uint _ q))
  refine ⟨fun i => alongCv γ (endP X M MvPowerSeries.X i), fun q => s q • lam q + alongCv γ
      (subst (endP X M (MvPowerSeries.X : κ → MvPowerSeries κ C)) (X.sg (X.u (1 - g) q)) -
        X.sg (M'.mulVec (X.u (1 - g) q))), isCv_along hγ (matrixEnd_const H M hX) hE.1, fun q => ⟨?_, fun n => ?_⟩,
    fun i => ?_, fun q => ?_⟩
  · rw [map_add, (hK q).1, PowerSeries.constantCoeff_smul, (hlam q).1, smul_zero, add_zero]
  · rw [map_add, PowerSeries.coeff_smul]
    exact ((hs q).mul_int ((hlam q).2 n)).add ((hK q).2 n)
  · show _ = ∑ j, M i j • a.1 j
    simp only [← h1]
    unfold alongCv
    simp only [subst_endP H M hγ0]
    exact lg_endP H M hγ0 i
  · show s q • a.2 q = _
    beta_reduce
    rw [h2 q, hu q, sg_smul]
    unfold alongCv
    rw [subst_sub hΓ, subst_smul hΓ, subst_comp_subst_apply hS hΓ, smul_sub]
    abel

end GlobalTheory.RowLaw.CvEnd
