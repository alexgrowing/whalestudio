import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConnectionKillsSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogInv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeExp

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section VF

variable {k : Type} [CommRing k] {τ : Type} [Fintype τ]

theorem vf_vf (c c' : τ → MvPowerSeries τ k) (G : MvPowerSeries τ k) :
    vf c (vf c' G) = vf (fun t => vf c (c' t)) G + ∑ s, ∑ t, c s * c' t * pderiv k s (pderiv k t G) := by
  unfold vf
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [add_comm]
  congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem vf_comm (c c' : τ → MvPowerSeries τ k) (G : MvPowerSeries τ k) :
    vf c (vf c' G) - vf c' (vf c G) = vf (fun t => vf c (c' t) - vf c' (c t)) G := by
  rw [vf_vf, vf_vf]
  have h : ∑ s, ∑ t, c' s * c t * pderiv k s (pderiv k t G) =
      ∑ s, ∑ t, c s * c' t * pderiv k s (pderiv k t G) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [pderiv_comm]
    ring
  rw [h]
  simp only [vf, sub_mul, Finset.sum_sub_distrib]
  ring

private theorem vf_sub' {k : Type} [CommRing k] {τ : Type} [Fintype τ] (c : τ → MvPowerSeries τ k)
    (a b : MvPowerSeries τ k) : vf c (a - b) = vf c a - vf c b := by
  simp only [vf, map_sub, mul_sub, Finset.sum_sub_distrib]

private theorem vf_mul' {k : Type} [CommRing k] {τ : Type} [Fintype τ] (c : τ → MvPowerSeries τ k)
    (a b : MvPowerSeries τ k) : vf c (a * b) = a * vf c b + b * vf c a := by
  simp only [vf, Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

theorem vfm_comm (c c' : τ → MvPowerSeries τ k) (f f' G : MvPowerSeries τ k) :
    (vf c (vf c' G - f' * G) - f * (vf c' G - f' * G)) - (vf c' (vf c G - f * G) - f' * (vf c G - f * G)) =
      vf (fun t => vf c (c' t) - vf c' (c t)) G - (vf c f' - vf c' f) * G := by
  rw [vf_sub', vf_sub', vf_mul', vf_mul', ← vf_comm]
  ring

theorem vf_Cmul (c : τ → MvPowerSeries τ k) (a : k) (g : MvPowerSeries τ k) : vf c (C a * g) = C a * vf c g := by
  simp only [vf, ← MvPowerSeries.smul_eq_C_mul, Derivation.map_smul, Finset.mul_sum, mul_smul_comm]

end VF

section Law

variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)

private theorem cc_ev_lemma {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have h0 : CZ (fun _ _ => (0 : PS k n d) : Fin n → Pt k n d) := by
    intro j i
    simp
  have h1 := ev_ev (a := (fun _ _ => (0 : PS k n d) : Fin n → Pt k n d)) h0 ha f
  rw [ev_zeroFam] at h1
  have h2 : (fun j i => ev (fun _ _ => (0 : PS k n d)) (a j i)) = fun _ _ => (0 : PS k n d) := by
    funext j i
    rw [ev_zeroFam, ha j i, map_zero]
  rw [h2, ev_zeroFam] at h1
  simpa using congrArg constantCoeff h1

private theorem constantCoeff_pderiv_eq_coeff_single {σ : Type} (p : σ) (f : MvPowerSeries σ k) :
    constantCoeff (pderiv k p f) = coeff (Finsupp.single p 1) f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

private theorem pderiv_fin_one_ev (g : PS k 2 d) (b : Fin d) :
    pderiv k ((0 : Fin 1), b) (ev (n := 1) ![pt k d 0, 0] g) =
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), b) g) := by
  rw [pderiv_ev cz1, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [pt_apply, MvPowerSeries.pderiv_X, Pi.single_apply]

theorem ezF (h : PS k 1 d) : ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![G.F] h) = h := by
  rw [ev_ev cz1 (czFF (G := G))]
  have e : (fun j i => ev (n := 1) ![pt k d 0, 0] ((![G.F] : Fin 1 → Pt k 2 d) j i)) =
      fun j => pt k (n := 1) d j := by
    funext j i
    fin_cases j
    simp [formalGroupLaw_ev_x_zero, pt_apply]
  rw [e, ev_pt]

theorem ez_y (h : PS k 1 d) : ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] h) = C (constantCoeff h) := by
  rw [ev_ev cz1 czY]
  have e : (fun j i => ev (n := 1) ![pt k d 0, 0] ((![pt k d 1] : Fin 1 → Pt k 2 d) j i)) =
      fun _ _ => (0 : PS k 1 d) := by
    funext j i
    fin_cases j
    simp [pt_apply, ev_X cz1]
  rw [e, ev_zeroFam]

theorem d_y (h : PS k 1 d) (b : Fin d) :
    pderiv k ((1 : Fin 2), b) (ev (n := 2) ![pt k d 1] h) = ev (n := 2) ![pt k d 1] (pderiv k ((0 : Fin 1), b) h) := by
  rw [pderiv_ev czY, Fintype.sum_prod_type, Fin.sum_univ_one]
  simp [pt_apply, MvPowerSeries.pderiv_X, Pi.single_apply]

theorem d_F (h : PS k 1 d) (v : Fin 2 × Fin d) :
    pderiv k v (ev (n := 2) ![G.F] h) = ∑ c, ev (n := 2) ![G.F] (pderiv k ((0 : Fin 1), c) h) * pderiv k v (G.F c) := by
  rw [pderiv_ev (czFF (G := G)), Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

theorem ez_Ar (j c : Fin d) : ev (n := 1) ![pt k d 0, 0] (Ar G j c) = Jac G j c := rfl

theorem ez_dF (c b : Fin d) : ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (G.F c)) = Jac G c b := rfl

theorem coeff_F_y (c i : Fin d) : coeff (Finsupp.single ((1 : Fin 2), i) 1) (G.F c) = if c = i then 1 else 0 := by
  have ha : CZ (![0, pt k d 0] : Fin 2 → Pt k 1 d) := CZ.cons cc_zero (CZ.cons (cc_pt 0) CZ.nil)
  have h := congrArg (pderiv k ((0 : Fin 1), i)) (G.unit c)
  rw [pderiv_ev ha, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp [pt_apply, MvPowerSeries.pderiv_X, Pi.single_apply] at h
  rw [← constantCoeff_pderiv_eq_coeff_single, ← cc_ev_lemma ha, h]
  split_ifs <;> simp_all

theorem cc_jac' (c i : Fin d) : constantCoeff (Jac G c i) = if c = i then 1 else 0 := by
  show constantCoeff (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (G.F c))) = _
  rw [cc_ev_lemma cz1, constantCoeff_pderiv_eq_coeff_single, coeff_F_y G c i]

theorem C_cc_jac (c i : Fin d) : (C (constantCoeff (Jac G c i)) : PS k 1 d) = if c = i then 1 else 0 := by
  rw [cc_jac' G c i]
  split_ifs <;> simp

theorem cc_d_jac (b c i : Fin d) : constantCoeff (pderiv k ((0 : Fin 1), b) (Jac G c i)) =
    coeff (Finsupp.single ((0 : Fin 2), b) 1 + Finsupp.single ((1 : Fin 2), i) 1) (G.F c) := by
  show constantCoeff (pderiv k ((0 : Fin 1), b)
    (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (G.F c)))) = _
  rw [pderiv_fin_one_ev, cc_ev_lemma cz1, constantCoeff_pderiv_eq_coeff_single, MvPowerSeries.coeff_pderiv]
  simp

private theorem coeff_single_add_single_eq_constantCoeff_pderiv_pderiv (F : PS k 2 d) (b i : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), b) 1 + Finsupp.single ((1 : Fin 2), i) 1) F =
      constantCoeff (pderiv k ((0 : Fin 2), b) (pderiv k ((1 : Fin 2), i) F)) := by
  rw [constantCoeff_pderiv_eq_coeff_single, MvPowerSeries.coeff_pderiv]
  simp

private theorem pderiv_zero_ev_swap (g : PS k 2 d) (b : Fin d) :
    pderiv k ((0 : Fin 2), b) (ev (n := 2) ![pt k d 1, pt k d 0] g) =
      ev (n := 2) ![pt k d 1, pt k d 0] (pderiv k ((1 : Fin 2), b) g) := by
  rw [pderiv_ev (CZ.cons (cc_pt 1) (CZ.cons (cc_pt 0) CZ.nil)), Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [pt_apply, MvPowerSeries.pderiv_X, Pi.single_apply]

private theorem pderiv_one_ev_swap (g : PS k 2 d) (b : Fin d) :
    pderiv k ((1 : Fin 2), b) (ev (n := 2) ![pt k d 1, pt k d 0] g) =
      ev (n := 2) ![pt k d 1, pt k d 0] (pderiv k ((0 : Fin 2), b) g) := by
  rw [pderiv_ev (CZ.cons (cc_pt 1) (CZ.cons (cc_pt 0) CZ.nil)), Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [pt_apply, MvPowerSeries.pderiv_X, Pi.single_apply]

theorem kappa_symm (b i c : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), b) 1 + Finsupp.single ((1 : Fin 2), i) 1) (G.F c) =
      coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), b) 1) (G.F c) := by
  rw [coeff_single_add_single_eq_constantCoeff_pderiv_pderiv, coeff_single_add_single_eq_constantCoeff_pderiv_pderiv]
  conv_lhs => rw [← G.comm c]
  rw [pderiv_one_ev_swap, pderiv_zero_ev_swap, cc_ev_lemma (CZ.cons (cc_pt 1) (CZ.cons (cc_pt 0) CZ.nil)), pderiv_comm]

theorem T_eq (b i j : Fin d) :
    ∑ c, Jac G c b * pderiv k ((0 : Fin 1), c) (Jac G j i) =
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (Ar G j i)) +
      ∑ c, Jac G j c * C (constantCoeff (pderiv k ((0 : Fin 1), b) (Jac G c i))) := by
  have h := congrArg (fun f => ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) f)) (jac_F G j i)
  simp only [d_F, map_sum, Derivation.leibniz, smul_eq_mul, ev_sum cz1, ev_add cz1, ev_mul cz1, ezF, ez_dF, d_y,
    ez_y, ez_Ar, C_cc_jac, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  have e : ∑ c, Jac G c b * pderiv k ((0 : Fin 1), c) (Jac G j i) =
      ∑ c, pderiv k ((0 : Fin 1), c) (Jac G j i) * Jac G c b :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [e, h]
  ring

theorem T_symm (b i j : Fin d) :
    ∑ c, Jac G c b * pderiv k ((0 : Fin 1), c) (Jac G j i) = ∑ c, Jac G c i * pderiv k ((0 : Fin 1), c) (Jac G j b) := by
  rw [T_eq G b i j, T_eq G i b j]
  congr 1
  · show ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (pderiv k ((1 : Fin 2), i) (G.F j))) =
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (pderiv k ((1 : Fin 2), b) (G.F j)))
    rw [pderiv_comm]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [cc_d_jac G b c i, cc_d_jac G i c b, kappa_symm G b i c]

def co (v : Fin d → k) : Fin 1 × Fin d → PS k 1 d := fun p => ∑ i, C (v i) * Jac G p.2 i

theorem dof_vf (v : Fin d → k) (g : PS k 1 d) : Dof G.F v g = vf (co G v) g := by
  unfold Dof vf
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

theorem vf_co_jac (u : Fin d → k) (j i : Fin d) :
    vf (co G u) (Jac G j i) = ∑ b, C (u b) * ∑ c, Jac G c b * pderiv k ((0 : Fin 1), c) (Jac G j i) := by
  unfold vf co
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem vf_finset_sum {τ : Type} [Fintype τ] {ι : Type} (s : Finset ι) (c : τ → MvPowerSeries τ k)
    (f : ι → MvPowerSeries τ k) : vf c (∑ i ∈ s, f i) = ∑ i ∈ s, vf c (f i) := by
  simp only [vf, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem sum_mul_sum_symm_swap_of_symmetric {ι : Type} [Fintype ι] (x y : ι → PS k 1 d) (T : ι → ι → PS k 1 d)
    (hT : ∀ b i, T b i = T i b) : ∑ i, x i * ∑ b, y b * T b i = ∑ i, y i * ∑ b, x b * T b i := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hT]
  ring

theorem co_bracket (u v : Fin d → k) (p : Fin 1 × Fin d) :
    vf (co G u) (co G v p) - vf (co G v) (co G u p) = 0 := by
  simp only [co, vf_finset_sum, vf_Cmul, vf_co_jac]
  rw [sub_eq_zero]
  exact sum_mul_sum_symm_swap_of_symmetric (fun i => C (v i)) (fun b => C (u b))
    (fun b i => ∑ c, Jac G c b * pderiv k ((0 : Fin 1), c) (Jac G p.2 i)) (fun b i => T_symm G b i p.2)

theorem dof_comm_law (u v : Fin d → k) (g : PS k 1 d) : Dof G.F u (Dof G.F v g) = Dof G.F v (Dof G.F u g) := by
  simp only [dof_vf]
  rw [← sub_eq_zero, vf_comm]
  have e : (fun t => vf (co G u) (co G v t) - vf (co G v) (co G u t)) = fun _ => 0 := funext (co_bracket G u v)
  rw [e]
  simp [vf]

end Law

section Transfer

theorem map_ev {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d m n : ℕ} {a : Fin m → Pt R n d} (ha : CZ a)
    (f : PS R m d) : MvPowerSeries.map φ (ev a f) = ev (fun j i => MvPowerSeries.map φ (a j i)) (MvPowerSeries.map φ f) := by
  exact MvPowerSeries.map_subst ha.hasSubst f

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem map_pt {n : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.map (algebraMap R k) (pt R d j i) = pt k d j i := by
  rw [pt_apply, pt_apply, map_X]

def lawK (B : FB R d O) : FGLaw k d where
  F := B.FK k
  const i := by
    simp [FB.FK, FGLaw.mapF, B.G.const i]
  unit i := by
    have h := congrArg (MvPowerSeries.map (algebraMap R k)) (B.G.unit i)
    rw [map_ev _ (CZ.cons cc_zero (CZ.cons (cc_pt 0) CZ.nil)), map_X] at h
    have e : (fun j c => MvPowerSeries.map (algebraMap R k) ((![0, pt R d 0] : Fin 2 → Pt R 1 d) j c)) =
        (![0, pt k d 0] : Fin 2 → Pt k 1 d) := by
      funext j c
      fin_cases j <;> simp [pt_apply]
    rw [e] at h
    exact h
  comm i := by
    have h := congrArg (MvPowerSeries.map (algebraMap R k)) (B.G.comm i)
    rw [map_ev _ (CZ.cons (cc_pt 1) (CZ.cons (cc_pt 0) CZ.nil))] at h
    have e : (fun j c => MvPowerSeries.map (algebraMap R k) ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) j c)) =
        (![pt k d 1, pt k d 0] : Fin 2 → Pt k 2 d) := by
      funext j c
      fin_cases j <;> simp [pt_apply]
    rw [e] at h
    exact h
  assoc i := by
    have hL : CZ (![fun l => ev (n := 3) ![pt R d 0, pt R d 1] (B.G.F l), pt R d 2] : Fin 2 → Pt R 3 d) :=
      CZ.cons (fun l => constantCoeff_ev cz01 (B.G.const l)) (CZ.cons (cc_pt 2) CZ.nil)
    have hR : CZ (![pt R d 0, fun l => ev (n := 3) ![pt R d 1, pt R d 2] (B.G.F l)] : Fin 2 → Pt R 3 d) :=
      CZ.cons (cc_pt 0) (CZ.cons (fun l => constantCoeff_ev cz12 (B.G.const l)) CZ.nil)
    have h := congrArg (MvPowerSeries.map (algebraMap R k)) (B.G.assoc i)
    rw [map_ev _ hL, map_ev _ hR] at h
    have eL : (fun j c => MvPowerSeries.map (algebraMap R k)
        ((![fun l => ev (n := 3) ![pt R d 0, pt R d 1] (B.G.F l), pt R d 2] : Fin 2 → Pt R 3 d) j c)) =
        (![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (B.FK k l), pt k d 2] : Fin 2 → Pt k 3 d) := by
      funext j c
      fin_cases j
      · show MvPowerSeries.map (algebraMap R k) (ev (n := 3) ![pt R d 0, pt R d 1] (B.G.F c)) =
          ev (n := 3) ![pt k d 0, pt k d 1] (B.FK k c)
        rw [map_ev _ cz01]
        congr 1
        funext j' c'
        fin_cases j' <;> simp [pt_apply]
      · simp [pt_apply]
    have eR : (fun j c => MvPowerSeries.map (algebraMap R k)
        ((![pt R d 0, fun l => ev (n := 3) ![pt R d 1, pt R d 2] (B.G.F l)] : Fin 2 → Pt R 3 d) j c)) =
        (![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (B.FK k l)] : Fin 2 → Pt k 3 d) := by
      funext j c
      fin_cases j
      · simp [pt_apply]
      · show MvPowerSeries.map (algebraMap R k) (ev (n := 3) ![pt R d 1, pt R d 2] (B.G.F c)) =
          ev (n := 3) ![pt k d 1, pt k d 2] (B.FK k c)
        rw [map_ev _ cz12]
        congr 1
        funext j' c'
        fin_cases j' <;> simp [pt_apply]
    rw [eL, eR] at h
    exact h

theorem invariantDerivations_commute_formal_connection : GE.DofCommSt := by
  unfold GE.DofCommSt
  intro R _ d O _ _ k _ _ _ B u v g
  exact dof_comm_law (lawK k B) u v g

end Transfer

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
