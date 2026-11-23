import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofDApply

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.GE

def HalfSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (F : Fin d → PS k 2 d) (ι : Type) [Fintype ι]
    (u : ι → Fin d → k) (c : ι → ι → k) (q : PS k 1 d),
    (∀ l l', c l l' = c l' l) → constantCoeff q = 0 → (∀ l, constantCoeff (Dof F (u l) q) = 0) →
    (∀ l l', Dof F (u l) (Dof F (u l') q) = C (c l l')) →
    ∀ (P : MvPolynomial ι k) (A : PS k 1 d),
      constantCoeff (DpolyOf F u P (A * q)) =
        algebraMap ℚ k (1 / 2) * constantCoeff (DpolyOf F u (secondOrder k c P) A)

variable {k : Type} [CommRing k] {d : ℕ}

section lin

variable (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)

theorem iter_add (D : PS k 1 d → PS k 1 d) (hD : ∀ f g, D (f + g) = D f + D g) (n : ℕ) (f g : PS k 1 d) :
    D^[n] (f + g) = D^[n] f + D^[n] g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, hD, ih]

theorem iter_Cmul (D : PS k 1 d → PS k 1 d) (hD : ∀ (r : k) f, D (C r * f) = C r * D f) (n : ℕ) (r : k)
    (f : PS k 1 d) : D^[n] (C r * f) = C r * D^[n] f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, hD, ih]

private theorem Dof_add' (v : Fin d → k) (f g : PS k 1 d) :
    Dof F v (f + g) = Dof F v f + Dof F v g := by
  first
  | simp only [Dof, map_add, mul_add, Finset.sum_add_distrib]
  | simp [Dof, mul_add, Finset.sum_add_distrib]

theorem foldr_add (L : List ι) (m : ι →₀ ℕ) (f g : PS k 1 d) :
    L.foldr (fun l h => (Dof F (u l))^[m l] h) (f + g) =
      L.foldr (fun l h => (Dof F (u l))^[m l] h) f + L.foldr (fun l h => (Dof F (u l))^[m l] h) g := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.foldr_cons, ih]
    exact iter_add _ (fun f g => Dof_add' F (u l) f g) _ _ _

private theorem Dof_C_mul (v : Fin d → k) (r : k) (f : PS k 1 d) :
    Dof F v (C r * f) = C r * Dof F v f := by
  first
  | (simp only [Dof, ← MvPowerSeries.smul_eq_C_mul, map_smul, mul_smul_comm, Finset.smul_sum]; done)
  | (simp only [Dof, ← MvPowerSeries.smul_eq_C_mul, Derivation.map_smul, mul_smul_comm, Finset.smul_sum]; done)
  | (simp only [Dof, Finset.mul_sum, Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib]; done)
  | (have hp := (pderiv : Unit))

theorem foldr_Cmul (L : List ι) (m : ι →₀ ℕ) (r : k) (f : PS k 1 d) :
    L.foldr (fun l h => (Dof F (u l))^[m l] h) (C r * f) =
      C r * L.foldr (fun l h => (Dof F (u l))^[m l] h) f := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.foldr_cons, ih]
    exact iter_Cmul _ (fun r f => Dof_C_mul F (u l) r f) _ _ _

theorem dmonOf_add (m : ι →₀ ℕ) (f g : PS k 1 d) :
    DmonOf F u m (f + g) = DmonOf F u m f + DmonOf F u m g :=
  foldr_add F u (Finset.univ : Finset ι).toList m f g

theorem dmonOf_Cmul (m : ι →₀ ℕ) (r : k) (f : PS k 1 d) :
    DmonOf F u m (C r * f) = C r * DmonOf F u m f :=
  foldr_Cmul F u (Finset.univ : Finset ι).toList m r f

theorem dmonOf_zero (m : ι →₀ ℕ) : DmonOf F u m (0 : PS k 1 d) = 0 := by
  simpa using dmonOf_Cmul F u m (0 : k) (0 : PS k 1 d)

theorem dpolyOf_eq_sum_of_subset (P : MvPolynomial ι k) (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S)
    (f : PS k 1 d) :
    DpolyOf F u P f = ∑ m ∈ S, C (MvPolynomial.coeff m P) * DmonOf F u m f := by
  unfold DpolyOf
  refine Finset.sum_subset hS ?_
  intro m _ hm
  have h0 : MvPolynomial.coeff m P = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]

theorem dpolyOf_add_P (P Q : MvPolynomial ι k) (f : PS k 1 d) :
    DpolyOf F u (P + Q) f = DpolyOf F u P f + DpolyOf F u Q f := by
  classical
  rw [dpolyOf_eq_sum_of_subset F u (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add f,
    dpolyOf_eq_sum_of_subset F u P (P.support ∪ Q.support) (fun x hx => Finset.mem_union_left _ hx) f,
    dpolyOf_eq_sum_of_subset F u Q (P.support ∪ Q.support) (fun x hx => Finset.mem_union_right _ hx) f,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, map_add, add_mul]

theorem dpolyOf_smul_P (a : k) (P : MvPolynomial ι k) (f : PS k 1 d) :
    DpolyOf F u (a • P) f = C a * DpolyOf F u P f := by
  rw [dpolyOf_eq_sum_of_subset F u (a • P) P.support MvPolynomial.support_smul f]
  unfold DpolyOf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, mul_assoc]

theorem dpolyOf_zero_P (f : PS k 1 d) : DpolyOf F u (0 : MvPolynomial ι k) f = 0 := by
  unfold DpolyOf
  simp

theorem dpolyOf_sum_P {α : Type} (s : Finset α) (P : α → MvPolynomial ι k) (f : PS k 1 d) :
    DpolyOf F u (∑ a ∈ s, P a) f = ∑ a ∈ s, DpolyOf F u (P a) f := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact dpolyOf_zero_P F u f
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dpolyOf_add_P, ih]

theorem dpolyOf_add_f (P : MvPolynomial ι k) (f g : PS k 1 d) :
    DpolyOf F u P (f + g) = DpolyOf F u P f + DpolyOf F u P g := by
  unfold DpolyOf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dmonOf_add, mul_add]

theorem dpolyOf_Cmul_f (P : MvPolynomial ι k) (r : k) (f : PS k 1 d) :
    DpolyOf F u P (C r * f) = C r * DpolyOf F u P f := by
  unfold DpolyOf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dmonOf_Cmul, mul_left_comm]

theorem dpolyOf_sum_f {α : Type} (s : Finset α) (P : MvPolynomial ι k) (f : α → PS k 1 d) :
    DpolyOf F u P (∑ a ∈ s, f a) = ∑ a ∈ s, DpolyOf F u P (f a) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    unfold DpolyOf
    simp [dmonOf_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dpolyOf_add_f, ih]

end lin

section deg

variable {ι : Type} [Fintype ι]

def DegLt (n : ℕ) (P : MvPolynomial ι k) : Prop := ∀ m : ι →₀ ℕ, n ≤ m.degree → MvPolynomial.coeff m P = 0

theorem degLt_mono {a b : ℕ} (hab : a ≤ b) {P : MvPolynomial ι k} (h : DegLt a P) : DegLt b P :=
  fun m hm => h m (le_trans hab hm)

theorem degLt_pderiv {n : ℕ} {P : MvPolynomial ι k} (h : DegLt (n + 1) P) (l : ι) :
    DegLt n (MvPolynomial.pderiv l P) := by
  classical
  intro m hm
  rw [MvPolynomial.as_sum P, map_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun s hs => ?_
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial]
  by_cases hsm : s - Finsupp.single l 1 = m
  · rw [if_pos hsm]
    have hc : MvPolynomial.coeff s P ≠ 0 := MvPolynomial.mem_support_iff.mp hs
    rcases Nat.eq_zero_or_pos (s l) with h0 | hpos
    · simp [h0]
    · exfalso
      have hle : Finsupp.single l 1 ≤ s := by
        first
        | (rw [Finsupp.single_le_iff]; exact hpos)
        | exact Finsupp.single_le_iff.mpr hpos
      have hs' : m + Finsupp.single l 1 = s := by
        rw [← hsm]
        exact tsub_add_cancel_of_le hle
      have hdeg : s.degree = m.degree + 1 := by
        first
        | rw [← hs', Finsupp.degree_add, Finsupp.degree_single]
        | rw [← hs', map_add, Finsupp.degree_single]
        | (rw [← hs']; simp [Finsupp.degree_add])
        | (rw [← hs']; simp)
      exact hc (h s (by omega))
  · rw [if_neg hsm]

theorem degLt_secondOrder (c : ι → ι → k) {n : ℕ} {P : MvPolynomial ι k} (h : DegLt (n + 1) P) :
    DegLt n (secondOrder k c P) := by
  intro m hm
  unfold secondOrder
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun l' _ => ?_
  rw [MvPolynomial.coeff_C_mul,
    degLt_pderiv (degLt_mono (Nat.le_succ n) (degLt_pderiv h l')) l m hm, mul_zero]

theorem degLt_iterate (c : ι → ι → k) (n j : ℕ) {P : MvPolynomial ι k} (h : DegLt (n + j) P) :
    DegLt n ((secondOrder k c)^[j] P) := by
  induction j generalizing P with
  | zero => first | exact h | simpa using h
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    exact ih (degLt_secondOrder c (n := n + j) (by first | exact h | simpa [Nat.add_assoc] using h))

theorem eq_zero_of_degLt_zero {P : MvPolynomial ι k} (h : DegLt 0 P) : P = 0 := by
  ext m
  rw [MvPolynomial.coeff_zero]
  exact h m (Nat.zero_le _)

theorem degLt_totalDegree (P : MvPolynomial ι k) : DegLt (P.totalDegree + 1) P := by
  intro m hm
  by_contra hne
  have hmem : m ∈ P.support := MvPolynomial.mem_support_iff.mpr hne
  have h1 : m.degree ≤ P.totalDegree := by
    first
    | exact MvPolynomial.le_totalDegree hmem
    | simpa [Finsupp.degree, Finsupp.sum] using MvPolynomial.le_totalDegree hmem
  omega

theorem iterate_eq_zero (c : ι → ι → k) (P : MvPolynomial ι k) :
    (secondOrder k c)^[P.totalDegree + 1] P = 0 :=
  eq_zero_of_degLt_zero (degLt_iterate c 0 _ (by rw [Nat.zero_add]; exact degLt_totalDegree P))

end deg

section wick

variable [Algebra ℚ k]

theorem half_pow (hH : HalfSt) (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (c : ι → ι → k) (q : PS k 1 d) (hc : ∀ l l', c l l' = c l' l) (hq0 : constantCoeff q = 0)
    (hq1 : ∀ l, constantCoeff (Dof F (u l) q) = 0)
    (hq2 : ∀ l l', Dof F (u l) (Dof F (u l') q) = C (c l l')) (n : ℕ) :
    ∀ (P : MvPolynomial ι k) (A : PS k 1 d),
      constantCoeff (DpolyOf F u P (A * q ^ n)) =
        algebraMap ℚ k (1 / 2) ^ n * constantCoeff (DpolyOf F u ((secondOrder k c)^[n] P) A) := by
  induction n with
  | zero => intro P A; simp
  | succ n ih =>
    intro P A
    have e : A * q ^ (n + 1) = (A * q) * q ^ n := by ring
    rw [e, ih P (A * q), hH k d F ι u c q hc hq0 hq1 hq2 ((secondOrder k c)^[n] P) A,
      Function.iterate_succ_apply', pow_succ]
    ring

theorem exp_cut (t : k) (q : PS k 1 d) (hq0 : constantCoeff q = 0) (N : ℕ) :
    ∃ Y : PS k 1 d, FB.expS k (t • q) =
      ∑ n ∈ Finset.range (N + 1), C (algebraMap ℚ k (1 / (n.factorial : ℚ)) * t ^ n) * q ^ n +
        q ^ (N + 1) * Y := by
  classical
  have hdvd : (PowerSeries.X : PowerSeries k) ^ (N + 1) ∣
      PowerSeries.exp k - ∑ n ∈ Finset.range (N + 1),
        algebraMap ℚ k (1 / (n.factorial : ℚ)) • (PowerSeries.X : PowerSeries k) ^ n := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    have hm' : m ∈ Finset.range (N + 1) := Finset.mem_range.mpr hm
    first
    | (simp only [map_sub, map_sum, map_smul, PowerSeries.coeff_exp, PowerSeries.coeff_X_pow, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hm', if_true, sub_self]; done)
    | (simp [PowerSeries.coeff_exp, PowerSeries.coeff_X_pow, hm']; done)
  obtain ⟨R, hR⟩ := hdvd
  have hexp : PowerSeries.exp k = (∑ n ∈ Finset.range (N + 1),
      algebraMap ℚ k (1 / (n.factorial : ℚ)) • (PowerSeries.X : PowerSeries k) ^ n) +
        PowerSeries.X ^ (N + 1) * R := by
    rw [← hR]
    ring
  have hc : constantCoeff (t • q) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hq0, mul_zero]
  have hs : PowerSeries.HasSubst (t • q) := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hc
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' hc
    | (show IsNilpotent _; rw [hc]; exact IsNilpotent.zero)
  have key : ∀ f : PowerSeries k, PowerSeries.subst (t • q) f = PowerSeries.substAlgHom hs f := by
    intro f
    first
    | rw [PowerSeries.coe_substAlgHom]
    | rfl
  have hX : PowerSeries.substAlgHom hs (PowerSeries.X : PowerSeries k) = t • q := by
    first
    | exact PowerSeries.substAlgHom_X hs
    | (rw [← key]; exact PowerSeries.subst_X hs)
  refine ⟨C (t ^ (N + 1)) * PowerSeries.subst (t • q) R, ?_⟩
  unfold FB.expS
  rw [hexp]
  simp only [key, map_add, map_sum, map_mul, map_pow, map_smul, hX]
  simp only [smul_pow, smul_smul, MvPowerSeries.smul_eq_C_mul, map_mul, map_pow]
  congr 1
  all_goals first
    | rfl
    | ring1
    | (refine Finset.sum_congr rfl fun n _ => ?_; ring1)

theorem wickExp_of (hH : HalfSt) : WickExpSt := by
  intro k _ _ d F ι _ u c P q hc hq0 hq1 hq2 t G
  obtain ⟨Y, hY⟩ := exp_cut t q hq0 P.totalDegree
  have hrem : constantCoeff (DpolyOf F u P (G * (q ^ (P.totalDegree + 1) * Y))) = 0 := by
    rw [show G * (q ^ (P.totalDegree + 1) * Y) = (G * Y) * q ^ (P.totalDegree + 1) by ring,
      half_pow hH F u c q hc hq0 hq1 hq2 (P.totalDegree + 1) P (G * Y), iterate_eq_zero,
      dpolyOf_zero_P, map_zero, mul_zero]
  rw [hY, mul_add, dpolyOf_add_f, map_add, hrem, add_zero, Finset.mul_sum, dpolyOf_sum_f, map_sum]
  unfold expSecond
  rw [dpolyOf_sum_P, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_left_comm G, dpolyOf_Cmul_f, map_mul, MvPowerSeries.constantCoeff_C,
    half_pow hH F u c q hc hq0 hq1 hq2 n P G, dpolyOf_smul_P, map_mul, MvPowerSeries.constantCoeff_C]
  ring

open G2 in

theorem gauge_exp_identity (hA : ExpAddZeroConstant) (hE : ConstantCoeffSubstitution) (hG : CanonicalGaugeDiffBiadditive) (hQ : QuadraticFormDerivatives)
    (hH : HalfSt) : GaugeExpSt := by
  have hW := wickExp_of hH
  intro R _ d O _ _ k _ _ _ B h h' hh hh' w0 m ι _ u Q f
  have hpt : ∀ (j : Fin 1) (i : Fin d), constantCoeff ((![pt k d 0] : Fin 1 → Pt k 1 d) j i) = 0 := by
    intro j i
    fin_cases j
    first
    | exact MvPowerSeries.constantCoeff_X _
    | simp [pt]
  have hpz : ∀ (j : Fin 2) (i : Fin d), constantCoeff ((![pt k d 0, 0] : Fin 2 → Pt k 1 d) j i) = 0 := by
    intro j i
    fin_cases j
    · first
      | exact MvPowerSeries.constantCoeff_X _
      | simp [pt]
    · show constantCoeff (0 : PS k 1 d) = 0
      exact map_zero _
  have ha : ∀ (j : Fin 2) (i : Fin d),
      constantCoeff ((![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] : Fin 2 → Pt k 1 d) j i) = 0 := by
    intro j i
    fin_cases j
    · first
      | exact MvPowerSeries.constantCoeff_X _
      | simp [pt]
    · show constantCoeff (ev ![pt k d 0] (B.actK k w0 i)) = 0
      rw [hE k d 1 1 ![pt k d 0] (B.actK k w0 i) hpt]
      show constantCoeff (MvPowerSeries.map (algebraMap R k) (B.A.act w0 i)) = 0
      first
      | rw [MvPowerSeries.constantCoeff_map, B.A.const w0 i, map_zero]
      | simp [B.A.const w0 i]
  have hh0 : constantCoeff h = 0 := by
    rw [← hE k d 2 1 ![pt k d 0, 0] h hpz, hh.ax1, map_zero]
  obtain ⟨hq0, hq1, hq2⟩ := hQ R d O k B (h' - h) (hG R d O k B h h' hh hh') w0
  have evAdd : ∀ (a : Fin 2 → Pt k 1 d), (∀ j i, constantCoeff (a j i) = 0) →
      ∀ f g : PS k 2 d, ev a (f + g) = ev a f + ev a g := by
    intro a hz f g
    have hs : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d => a p.1 p.2) := by
      first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => hz p.1 p.2)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
          (fun p => by rw [hz p.1 p.2]; exact IsNilpotent.zero)
      | exact ⟨fun p => by rw [hz p.1 p.2]; exact IsNilpotent.zero, fun e => Set.toFinite _⟩
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun p => hz p.1 p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => hz p.1 p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent
          (fun p => by rw [hz p.1 p.2]; exact IsNilpotent.zero)
    unfold ev
    first
    | exact MvPowerSeries.subst_add hs f g
    | (rw [← MvPowerSeries.coe_substAlgHom hs]; exact map_add _ f g)
  have hsplit : B.hL k h' w0 =
      B.hL k h w0 + ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] (h' - h) := by
    unfold FB.hL
    rw [← evAdd _ ha]
    congr 1
    ring
  have hc1 : constantCoeff ((m : k) • B.hL k h w0) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul]
    unfold FB.hL
    rw [hE k d 2 1 _ h ha, hh0, mul_zero]
  have hc2 : constantCoeff ((m : k) • ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] (h' - h)) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hq0, mul_zero]
  unfold FB.nabVal
  rw [hsplit, smul_add, hA k 1 d _ _ hc1 hc2, ← mul_assoc]
  exact hW k d (B.FK k) ι u
    (fun l l' => dotProduct (u l) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l'))) +
      dotProduct (u l') ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l))))
    Q _ (fun l l' => add_comm _ _) hq0 (fun l => hq1 (u l)) (fun l l' => hq2 (u l) (u l')) (m : k) _

end wick

end ReciprocityTheory.ChartRestriction.G.TB.GE
