import Formalism.LocalToGlobal.CharacterGerms.CoeffAlongCvCongr

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section Rename

theorem prod_X_rename {σ τ : Type} (φ : σ → τ) (e : σ →₀ ℕ) :
    (e.prod fun s m => (MvPowerSeries.X (φ s) : MvPowerSeries τ C) ^ m) =
      MvPowerSeries.monomial (e.mapDomain φ) 1 := by
  refine Finsupp.induction_linear e ?_ ?_ ?_
  · simp
  · intro f g hf hg
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), hf, hg,
      Finsupp.mapDomain_add, MvPowerSeries.monomial_mul_monomial, one_mul]
  · intro a b
    rw [Finsupp.prod_single_index (h := fun s m => (MvPowerSeries.X (φ s) : MvPowerSeries τ C) ^ m) (pow_zero _),
      Finsupp.mapDomain_single]
    simp only [MvPowerSeries.X_pow_eq]

theorem coeff_subst_rename_inj {σ τ : Type} [Finite σ] (φ : σ → τ) (hφ : Function.Injective φ)
    (F : MvPowerSeries σ C) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff (e.mapDomain φ)
      (MvPowerSeries.subst (fun s => (MvPowerSeries.X (φ s) : MvPowerSeries τ C)) F) = MvPowerSeries.coeff e F := by
  have hA : MvPowerSeries.HasSubst (fun s => (MvPowerSeries.X (φ s) : MvPowerSeries τ C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by simp)
  rw [MvPowerSeries.coeff_subst hA, finsum_eq_single _ e]
  · rw [prod_X_rename, MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one]
  · intro d hd
    rw [prod_X_rename, MvPowerSeries.coeff_monomial, if_neg, smul_zero]
    intro h
    exact hd (Finsupp.mapDomain_injective hφ h).symm

variable {dd : ℕ}

theorem snd_injective_fin_one : Function.Injective (fun p : Fin 1 × Fin dd => p.2) := fun p q h => Prod.ext (Subsingleton.elim _ _) h

theorem hasSubst_snd : MvPowerSeries.HasSubst
    (fun p : Fin 1 × Fin dd => (MvPowerSeries.X p.2 : MvPowerSeries (Fin dd) C)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by simp)

theorem uncurry_eq_subst (f : PS C 1 dd) :
    un1 f = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => (MvPowerSeries.X p.2 : MvPowerSeries (Fin dd) C)) f := by
  ext μ
  have h := coeff_subst_rename_inj (C := C) (fun p : Fin 1 × Fin dd => p.2) snd_injective_fin_one f
    (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x))
  have e1 : (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)).mapDomain (fun p : Fin 1 × Fin dd => p.2) = μ := by
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_id
  rw [e1] at h
  exact h.symm

theorem subst_singlePointUncurry {τ : Type} {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (f : PS C 1 dd) :
    MvPowerSeries.subst a (un1 f) = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [uncurry_eq_subst, MvPowerSeries.subst_comp_subst_apply hasSubst_snd hA]
  congr 1
  funext p
  show MvPowerSeries.subst a (MvPowerSeries.X p.2) = a p.2
  rw [MvPowerSeries.subst_X hA]

theorem subst_oneVariableUncurry_eq_subst {σ : Type} [Finite σ] {b : σ → PS C 1 dd} (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    (f : MvPowerSeries σ C) :
    un1 (MvPowerSeries.subst b f) = MvPowerSeries.subst (fun s => un1 (b s)) f := by
  have hB : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [uncurry_eq_subst, MvPowerSeries.subst_comp_subst_apply hB hasSubst_snd]
  congr 1
  funext s
  rw [uncurry_eq_subst]

theorem uncurry_X (i : Fin dd) : un1 (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd) = MvPowerSeries.X i := by
  rw [uncurry_eq_subst, MvPowerSeries.subst_X hasSubst_snd]

theorem eval_single_eq_subst {n : ℕ} (a : Pt C n dd) (f : PS C 1 dd) :
    ev ![a] f = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  simp only [ev]
  congr 1
  funext p
  rw [Subsingleton.elim p.1 0]
  rfl

theorem uncurry_comp {φ a : Pt C 1 dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => un1 (a j)) (un1 (φ i)) = un1 (comp1 φ a i) := by
  have hu : ∀ j, MvPowerSeries.constantCoeff (un1 (a j)) = 0 := by
    intro j
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (a j) = 0
    rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ha j
  rw [subst_singlePointUncurry hu]
  show _ = un1 (ev ![a] (φ i))
  rw [eval_single_eq_subst, subst_oneVariableUncurry_eq_subst (b := fun p : Fin 1 × Fin dd => a p.2) (fun s => ha s.2)]

end Rename

def PTFBSt : Prop :=
  AllFB fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, x 0 = Sum.elim w 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x i n = 0

def AddCvFBSt : Prop := AllFB fun _ _ V _ _ _ _ X => X.AddCvSt V

def HStabFBSt : Prop :=
  AllFB fun _ _ V _ I _ _ X => ∀ (g : Fin 2) (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q →
    V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q))

section Inst

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

theorem FBChart.lg_const (i : Fin dd) : MvPowerSeries.constantCoeff (Y.lg i) = 0 := by
  have h := Y.lg_lin i 0 (by simp)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_X] at h
  exact h

theorem FBChart.chart_log_constantCoeff (i : Fin dd) : MvPowerSeries.constantCoeff ((Y.raw p).lg i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = 0
  rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact Y.lg_const i

theorem FBChart.chart_exp_constantCoeff (i : Fin dd) : MvPowerSeries.constantCoeff ((Y.raw p).ex i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.ex i) = 0
  rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact Y.ex_const i

theorem FBChart.raw_exlg (i : Fin dd) :
    MvPowerSeries.subst (Y.raw p).lg ((Y.raw p).ex i) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  show MvPowerSeries.subst (fun j => un1 (Y.lg j)) (un1 (Y.ex i)) = _
  rw [uncurry_comp (fun j => Y.lg_const j), Y.ex_lg]
  exact uncurry_X i

theorem FBChart.raw_lgex (i : Fin dd) :
    MvPowerSeries.subst (Y.raw p).ex ((Y.raw p).lg i) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  show MvPowerSeries.subst (fun j => un1 (Y.ex j)) (un1 (Y.lg i)) = _
  rw [uncurry_comp (fun j => Y.ex_const j), Y.lg_ex]
  exact uncurry_X i

theorem FBChart.raw_lin (i : Fin dd) (μ : Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ ((Y.raw p).lg i) =
      MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  show MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = _
  rw [Y.lg_lin i _ ?_, ← uncurry_X i]
  · rfl
  · have hd : ∀ ν : Fin dd →₀ ℕ, (ν.mapDomain fun x : Fin dd => ((0 : Fin 1), x)).degree = ν.degree := by
      intro ν
      refine Finsupp.induction_linear ν ?_ ?_ ?_
      · simp
      · intro f g hf hg
        rw [Finsupp.mapDomain_add, map_add, map_add, hf, hg]
      · intro a b
        rw [Finsupp.mapDomain_single]
        simp
    rw [hd]
    exact hμ

theorem FBChart.raw_axis0 (e : Fin 2 × Fin dd →₀ ℕ) (he : ∀ s ∈ e.support, s.1 ≠ 0) :
    MvPowerSeries.coeff e (Y.raw p).h = 0 := by
  refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0 e he
  intro g' hg'
  rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
  rfl

end Inst

theorem cartFB_of (hPT : PTFBSt) (hAdd : AddCvFBSt) (hStab : HStabFBSt) : CartFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g
  show RawChart.CartHyp (Y.raw p) V g
  haveI := Y.algClosed
  haveI : NeZero (V.l : C) := ⟨Nat.cast_ne_zero.2 V.l_prime.ne_zero⟩
  obtain ⟨ζ, hζr⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic V.l C)
    (Polynomial.degree_cyclotomic_pos V.l C V.l_prime.pos).ne'
  have hζ : IsPrimitiveRoot ζ V.l := (Polynomial.isRoot_cyclotomic_iff).1 hζr
  have hA : (Y.raw p).AddCvSt V := hAdd C V O dd Y d I p
  have h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ (Y.raw p).TySet V g :=
    RawChart.zero_mem (Y.raw p) (Y.chart_log_constantCoeff p) (Y.raw_axis0 p) V g
  have hadd : ∀ x y, x ∈ (Y.raw p).TySet V g → y ∈ (Y.raw p).TySet V g → x + y ∈ (Y.raw p).TySet V g :=
    fun x y hx hy => RawChart.add_mem (Y.raw p) V g hA p.u_int x y hx hy
  exact
    { zero := h0
      add := hadd
      neg := fun x hx => RawChart.neg_mem (Y.raw p) V g Y.l_odd x hx
      teich := fun c hc x hx => RawChart.teich_mem (Y.raw p) V g c hc x hx
      Vm := fun x hx => RawChart.Vpow_mem' (Y.raw p) V g 1 x hx
      Fm := fun x hx => RawChart.F_mem (Y.raw p) V g (Y.chart_log_constantCoeff p) (Y.raw_exlg p) hζ h0 hadd x hx
      sumV := fun y hy => RawChart.sumV_mem (Y.raw p) V g (Y.chart_log_constantCoeff p) (Y.chart_exp_constantCoeff p) (Y.raw_exlg p)
        (Y.raw_lgex p) h0 hadd y hy
      t2 := fun x hx s hs n => RawChart.val_nonneg_leading_coeff_of_mem_tySet (Y.raw p) V g (Y.raw_lin p) (Y.raw_axis0 p) (p.u_sat g)
        (hStab C V O dd Y d I p g) x hx s hs n
      t3 := fun ζ' hζ' => RawChart.const_mem_type_set_of_nonneg (Y.raw p) (Y.chart_log_constantCoeff p) (Y.raw_axis0 p) V g ζ' hζ'
      t4 := hPT C V O dd Y d I p g }

end Formalism.L2.FormalSeriesBounds
