import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqOf

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds PartialDerivEval RowTiePCEq ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

namespace RowTiePCEqSum

theorem subst_zero_const {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = 0 := by
  ext e
  rw [MvPowerSeries.coeff_subst MvPowerSeries.HasSubst.zero, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hn
    have hs' : n s ≠ 0 := by simpa using hs
    have : (n.prod fun s e => (0 : MvPowerSeries τ C) ^ e) = 0 :=
      Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.2 hs') (zero_pow hs')
    rw [this, map_zero, smul_zero]

theorem hasSubst_unit {τ : Type} {T : MvPowerSeries τ C} (hT : MvPowerSeries.constantCoeff T = 0) :
    MvPowerSeries.HasSubst (fun _ : Unit => T) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hT)

theorem subst_lin {σ τ : Type} {a : σ → MvPowerSeries τ C} (ha : MvPowerSeries.HasSubst a) {ι : Type}
    (s : Finset ι) (r : ι → C) (F : ι → MvPowerSeries σ C) :
    MvPowerSeries.subst a (∑ i ∈ s, r i • F i) = ∑ i ∈ s, r i • MvPowerSeries.subst a (F i) := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  first
  | exact map_smul _ _ _
  | exact AlgHom.map_smul_of_tower _ _ _

theorem coeff_subst_tyS {τ : Type} [Finite τ] {l : ℕ} (hl : 2 ≤ l) {T : MvPowerSeries τ C}
    (hT : MvPowerSeries.constantCoeff T = 0) (a : ℕ → C) (μ : τ →₀ ℕ) :
    MvPowerSeries.coeff μ (MvPowerSeries.subst (fun _ : Unit => T) (tyS l a)) =
      ∑ s ∈ Finset.range (μ.degree + 1), a s * MvPowerSeries.coeff μ (T ^ (l ^ s)) := by
  set N := μ.degree + 1 with hN
  set P : PowerSeries C := ∑ s ∈ Finset.range N, a s • PowerSeries.X ^ (l ^ s) with hP
  have hPc : ∀ m < l ^ N, PowerSeries.coeff m (tyS l a) = PowerSeries.coeff m P := by
    intro m hm
    rw [hP, map_sum]
    simp only [PowerSeries.coeff_smul, PowerSeries.coeff_X_pow]
    by_cases h : ∃ s', l ^ s' = m
    · obtain ⟨s', rfl⟩ := h
      rw [coeff_tyS_pow hl, Finset.sum_eq_single s']
      · simp
      · intro s _ hs
        rw [if_neg, smul_zero]
        intro h
        exact hs (Nat.pow_right_injective hl h).symm
      · intro h
        exfalso
        apply h
        rw [Finset.mem_range]
        exact (Nat.pow_lt_pow_iff_right (by omega)).1 hm
    · push Not at h
      rw [coeff_tyS_of_ne a m h]
      symm
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [if_neg (h s).symm, smul_zero]
  have hAg : Formalism.G.LogCR.Agree N (tyS l a : MvPowerSeries Unit C) (P : MvPowerSeries Unit C) := by
    intro e he
    have hes : e = Finsupp.single () (e ()) := Finsupp.unique_single e
    rw [hes] at he ⊢
    rw [Finsupp.degree_single] at he
    exact hPc _ (lt_of_lt_of_le he (Nat.lt_pow_self (by omega)).le)
  have h1 := Formalism.G.LogCR.Agree.subst (a := fun _ : Unit => T) (a' := fun _ : Unit => T) (fun _ => hT) (fun _ => hT) hAg
    (fun _ _ _ => rfl) μ (by omega)
  rw [h1, hP, ← MvPowerSeries.coe_substAlgHom (hasSubst_unit hT), map_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, map_pow, MvPowerSeries.coe_substAlgHom]
  rw [show (PowerSeries.X : PowerSeries C) = (MvPowerSeries.X () : MvPowerSeries Unit C) from rfl,
    MvPowerSeries.subst_X (hasSubst_unit hT), MvPowerSeries.coeff_smul]

section Add

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

def IsCvM (V : VF C) {τ : Type} (γ : Fin dd → MvPowerSeries τ C) : Prop :=
  ∀ i, MvPowerSeries.constantCoeff (γ i) = 0 ∧ IntS V (γ i)

theorem addCvM {τ : Type} [Finite τ] (γ γ' : Fin dd → MvPowerSeries τ C) (hγ : IsCvM V γ) (hγ' : IsCvM V γ') :
    ∃ γ'' : Fin dd → MvPowerSeries τ C, IsCvM V γ'' ∧
      (∀ i, MvPowerSeries.subst γ'' ((Y.raw p).lg i) =
        MvPowerSeries.subst γ ((Y.raw p).lg i) + MvPowerSeries.subst γ' ((Y.raw p).lg i)) ∧
      ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
        IntS V (MvPowerSeries.subst γ'' ((Y.raw p).sg v) - MvPowerSeries.subst γ ((Y.raw p).sg v) -
          MvPowerSeries.subst γ' ((Y.raw p).sg v)) := by
  set ρ : Fin 2 × Fin dd → MvPowerSeries τ C := fun q => ![γ, γ'] q.1 q.2 with hρ
  have hρ0 : ∀ q, MvPowerSeries.constantCoeff (ρ q) = 0 := by
    rintro ⟨b, j⟩
    fin_cases b
    · exact (hγ j).1
    · exact (hγ' j).1
  have hρI : ∀ q, IntS V (ρ q) := by
    rintro ⟨b, j⟩
    fin_cases b
    · exact (hγ j).2
    · exact (hγ' j).2
  have hρS := MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0
  set γ'' : Fin dd → MvPowerSeries τ C := fun j => MvPowerSeries.subst ρ (Y.B.G.F j) with hγ''
  have hγ''0 : ∀ j, MvPowerSeries.constantCoeff (γ'' j) = 0 := fun j =>
    constantCoeff_subst_zero hρ0 (Y.B.G.const j)
  have hev : ∀ (a : Pt C 2 dd), (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f : PS C 1 dd,
      MvPowerSeries.subst ρ (ev ![a] f) = MvPowerSeries.subst (fun j => MvPowerSeries.subst ρ (a j)) (un1 f) := by
    intro a ha f
    rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => ha q.2) hρS,
      subst_singlePointUncurry (fun j => constantCoeff_subst_zero hρ0 (ha j))]
  have hp0 : (fun j => MvPowerSeries.subst ρ (pt C (n := 2) dd 0 j)) = γ := by
    funext j
    show MvPowerSeries.subst ρ (MvPowerSeries.X ((0 : Fin 2), j)) = γ j
    rw [MvPowerSeries.subst_X hρS]
    rfl
  have hp1 : (fun j => MvPowerSeries.subst ρ (pt C (n := 2) dd 1 j)) = γ' := by
    funext j
    show MvPowerSeries.subst ρ (MvPowerSeries.X ((1 : Fin 2), j)) = γ' j
    rw [MvPowerSeries.subst_X hρS]
    rfl
  have hpa : (fun j => MvPowerSeries.subst ρ (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j)) = γ'' := by
    funext j
    rw [addOf_pts]
  have hc0 : ∀ j, MvPowerSeries.constantCoeff (pt C (n := 2) dd 0 j) = 0 := fun j => MvPowerSeries.constantCoeff_X _
  have hc1 : ∀ j, MvPowerSeries.constantCoeff (pt C (n := 2) dd 1 j) = 0 := fun j => MvPowerSeries.constantCoeff_X _
  have hca : ∀ j, MvPowerSeries.constantCoeff (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j) = 0 :=
    fun j => by rw [addOf_pts]; exact Y.B.G.const j
  refine ⟨γ'', fun j => ⟨hγ''0 j, IntS.subst hρ0 hρI (Y.intF j)⟩, ?_, ?_⟩
  · intro i
    have h := congrArg (MvPowerSeries.subst ρ) (Y.lg_add i)
    rw [← MvPowerSeries.coe_substAlgHom hρS, map_add, MvPowerSeries.coe_substAlgHom hρS, hev _ hca, hev _ hc0,
      hev _ hc1, hpa, hp0, hp1] at h
    exact h
  · intro v hv
    have h := IntS.subst hρ0 hρI (germI_holds Y v hv)
    rw [← MvPowerSeries.coe_substAlgHom hρS, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hρS, hev _ hca,
      hev _ hc0, hev _ hc1, hpa, hp0, hp1, ← Y.raw_sg p v] at h
    exact h

theorem sumCvM {τ : Type} [Finite τ] {ι : Type} (s : Finset ι) (γ : ι → Fin dd → MvPowerSeries τ C)
    (hγ : ∀ c, IsCvM V (γ c)) :
    ∃ Γ : Fin dd → MvPowerSeries τ C, IsCvM V Γ ∧
      (∀ i, MvPowerSeries.subst Γ ((Y.raw p).lg i) = ∑ c ∈ s, MvPowerSeries.subst (γ c) ((Y.raw p).lg i)) ∧
      ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
        IntS V (MvPowerSeries.subst Γ ((Y.raw p).sg v) - ∑ c ∈ s, MvPowerSeries.subst (γ c) ((Y.raw p).sg v)) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, fun _ => ⟨map_zero _, intS_zero⟩, fun i => ?_, fun v _ => ?_⟩
    · rw [Finset.sum_empty]
      exact subst_zero_const _ (Y.chart_log_constantCoeff p i)
    · rw [Finset.sum_empty, sub_zero, subst_zero_const _ ((Y.raw p).constantCoeff_sg (Y.raw_axis0 p) v)]
      exact intS_zero
  | insert c s hc ih =>
    obtain ⟨Γ, hΓ, hL, hS⟩ := ih
    obtain ⟨Γ', hΓ', hL', hS'⟩ := addCvM Y p Γ (γ c) hΓ (hγ c)
    refine ⟨Γ', hΓ', fun i => ?_, fun v hv => ?_⟩
    · rw [hL', hL, Finset.sum_insert hc]
      ring
    · rw [Finset.sum_insert hc]
      have := intS_add (hS' v hv) (hS v hv)
      convert this using 1
      ring

end Add

end RowTiePCEqSum

open RowTiePCEqSum in

theorem cEqSum_holds : CEqSumSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g H S t ht
  have hl2 : 2 ≤ V.l := V.l_prime.two_le
  have ht0 : ∀ c, MvPowerSeries.constantCoeff (t c) = 0 := ht.1
  have htS := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  have hmem : ∀ c, ∃ γ : Fin dd → PowerSeries C, ∃ lam : JJ I g → PowerSeries C, IsCv V γ ∧ IsCv V lam ∧
      (∀ i, alongCv γ ((Y.raw p).lg i) =
        ∑ c' : I g, (Y.raw p).u g c' i • tyS V.l (fun s => S.cur c s (Sum.inl c'))) ∧
      ∀ q : JJ I g, tyS V.l (fun s => S.cur c s (Sum.inr q)) =
        lam q - alongCv γ ((Y.raw p).sg ((Y.raw p).u (1 - g) q)) +
          ∑ c' : I g, if (Y.raw p).ty g c' = (Y.raw p).ty (1 - g) q then
            (Y.raw p).sg1 ((Y.raw p).u g c') ((Y.raw p).u (1 - g) q) •
              tyS V.l (fun s => S.cur c s (Sum.inl c')) else 0 :=
    fun c => by
      obtain ⟨h, -, -⟩ := S.curve c
      exact h
  choose γ lam hγ hlam h1 h2 using hmem
  have be0 : ∀ c (q : JJ I g), S.cur c 0 (Sum.inr q) = 0 := fun c q => by
    obtain ⟨-, h0, -⟩ := S.curve c
    rw [h0]
    rfl
  have hc : ∀ c (a : ℕ → C) (μ : I g →₀ ℕ),
      MvPowerSeries.coeff μ (MvPowerSeries.subst (fun _ : Unit => t c) (tyS V.l a)) =
        ∑ s ∈ Finset.range (μ.degree + 1), a s * MvPowerSeries.coeff μ (t c ^ (V.l ^ s)) :=
    fun c a μ => coeff_subst_tyS hl2 (ht0 c) a μ
  have hC : ∀ x : I g, ∑ c, MvPowerSeries.subst (fun _ : Unit => t c) (tyS V.l (fun s => S.cur c s (Sum.inl x))) =
      MvPowerSeries.X x := by
    intro x
    ext μ
    rw [map_sum, MvPowerSeries.coeff_X]
    simp only [hc]
    rw [Finset.sum_comm]
    exact ht.2 x μ
  have hB : ∀ q : JJ I g, ∑ c, MvPowerSeries.subst (fun _ : Unit => t c) (tyS V.l (fun s => S.cur c s (Sum.inr q))) =
      -S.ze t q := by
    intro q
    ext μ
    rw [map_sum, map_neg]
    simp only [hc]
    rw [Finset.sum_comm]
    show _ = -(-(∑ s ∈ Finset.Icc 1 μ.degree, ∑ c : I g, S.be c s q * MvPowerSeries.coeff μ (t c ^ (V.l ^ s))))
    rw [neg_neg, show Finset.range (μ.degree + 1) = insert 0 (Finset.Icc 1 μ.degree) by ext s; simp; omega,
      Finset.sum_insert (by simp)]
    simp only [be0, zero_mul, Finset.sum_const_zero, zero_add]
    rfl
  set γt : I g → Fin dd → MvPowerSeries (I g) C :=
    fun c i => MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) (γ c i) with hγtd
  have hγt : ∀ c, IsCvM V (γt c) := fun c i =>
    ⟨constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hγ c i).1,
      IntS.subst (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => intS_X _) (intS_ps.2 (hγ c i).2)⟩
  have key1 : ∀ c (f : MvPowerSeries (Fin dd) C), MvPowerSeries.subst (γt c) f =
      MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) (alongCv (γ c) f) := by
    intro c f
    unfold alongCv
    rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => (hγ c i).1)
      (hasSubst_unit (MvPowerSeries.constantCoeff_X c))]
  have key2 : ∀ c (F : PowerSeries C), MvPowerSeries.subst t
      (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) F) =
      MvPowerSeries.subst (fun _ : Unit => t c) F := by
    intro c F
    rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_unit (MvPowerSeries.constantCoeff_X c)) htS]
    congr 1
    funext _
    rw [MvPowerSeries.subst_X htS]
  have hlin : ∀ c (r : I g → C) (F : I g → PowerSeries C),
      MvPowerSeries.subst (fun _ : Unit => t c) (∑ c' : I g, r c' • F c') =
        ∑ c' : I g, r c' • MvPowerSeries.subst (fun _ : Unit => t c) (F c') :=
    fun c r F => subst_lin (hasSubst_unit (ht0 c)) _ r F
  obtain ⟨Γ, hΓ, hL, hSg⟩ := sumCvM Y p Finset.univ γt hγt
  have hΓS := MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => (hΓ i).1
  have hZ0 : ∀ j, MvPowerSeries.constantCoeff (MvPowerSeries.subst t (Γ j)) = 0 := fun j =>
    constantCoeff_subst_zero ht0 (hΓ j).1
  have hZS := MvPowerSeries.hasSubst_of_constantCoeff_zero hZ0
  have hsum : ∀ f : MvPowerSeries (Fin dd) C, MvPowerSeries.subst (fun j => MvPowerSeries.subst t (Γ j)) f =
      MvPowerSeries.subst t (MvPowerSeries.subst Γ f) := fun f =>
    (MvPowerSeries.subst_comp_subst_apply hΓS htS f).symm
  have hpush : ∀ f : MvPowerSeries (Fin dd) C, MvPowerSeries.subst t (∑ c, MvPowerSeries.subst (γt c) f) =
      ∑ c, MvPowerSeries.subst (fun _ : Unit => t c) (alongCv (γ c) f) := by
    intro f
    rw [← MvPowerSeries.coe_substAlgHom htS, map_sum, MvPowerSeries.coe_substAlgHom]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [key1, key2]
  have hlgZ : ∀ i, MvPowerSeries.subst (fun j => MvPowerSeries.subst t (Γ j)) ((Y.raw p).lg i) =
      ∑ c' : I g, (Y.raw p).u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C) := by
    intro i
    rw [hsum, hL i, hpush]
    simp only [h1, hlin]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [← Finset.smul_sum, hC c']
  have hZ : ∀ i, MvPowerSeries.subst t (Γ i) = (Y.raw p).expG g i := by
    intro i
    have e1 : MvPowerSeries.subst (fun j => MvPowerSeries.subst t (Γ j))
        (MvPowerSeries.subst (Y.raw p).lg ((Y.raw p).ex i)) = MvPowerSeries.subst t (Γ i) := by
      rw [Y.raw_exlg p i, MvPowerSeries.subst_X hZS]
    rw [← e1, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (Y.chart_log_constantCoeff p)) hZS]
    unfold RawChart.expG
    congr 1
    funext j
    exact hlgZ j
  refine ⟨Γ, fun i => (hΓ i).1, fun i => (hΓ i).2, hZ, fun q => ?_⟩
  set v := (Y.raw p).u (1 - g) q with hv
  have hvI : ∀ i, V.Ge 0 (v i) := fun i => p.u_int (1 - g) q i
  refine ⟨(MvPowerSeries.subst Γ ((Y.raw p).sg v) - ∑ c, MvPowerSeries.subst (γt c) ((Y.raw p).sg v)) +
    ∑ c, MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) (lam c q), ?_, ?_⟩
  · refine intS_add (hSg v hvI) (intS_sum _ fun c _ => ?_)
    exact IntS.subst (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => intS_X _) (intS_ps.2 (hlam c q).2)
  · have hexp : (Y.raw p).expG g = fun j => MvPowerSeries.subst t (Γ j) := by
      funext j
      exact (hZ j).symm
    have hA : ∀ c, MvPowerSeries.subst (fun _ : Unit => t c) (alongCv (γ c) ((Y.raw p).sg v)) =
        MvPowerSeries.subst (fun _ : Unit => t c) (lam c q) -
          MvPowerSeries.subst (fun _ : Unit => t c) (tyS V.l (fun s => S.cur c s (Sum.inr q))) +
          ∑ c' : I g, if (Y.raw p).ty g c' = (Y.raw p).ty (1 - g) q then
            (Y.raw p).sg1 ((Y.raw p).u g c') v •
              MvPowerSeries.subst (fun _ : Unit => t c) (tyS V.l (fun s => S.cur c s (Sum.inl c'))) else 0 := by
      intro c
      have e : alongCv (γ c) ((Y.raw p).sg v) = lam c q - tyS V.l (fun s => S.cur c s (Sum.inr q)) +
          ∑ c' : I g, if (Y.raw p).ty g c' = (Y.raw p).ty (1 - g) q then
            (Y.raw p).sg1 ((Y.raw p).u g c') v • tyS V.l (fun s => S.cur c s (Sum.inl c')) else 0 := by
        rw [h2 c q]
        ring
      rw [e, ← MvPowerSeries.coe_substAlgHom (hasSubst_unit (ht0 c)), map_add, map_sub, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun c' _ => ?_
      split_ifs
      · rw [map_smul]
      · rw [map_zero]
    have hAll : ∑ c, MvPowerSeries.subst (fun _ : Unit => t c) (alongCv (γ c) ((Y.raw p).sg v)) =
        S.ze t q + ∑ c, MvPowerSeries.subst (fun _ : Unit => t c) (lam c q) +
          ∑ c' : I g, if (Y.raw p).ty g c' = (Y.raw p).ty (1 - g) q then
            (Y.raw p).sg1 ((Y.raw p).u g c') v • (MvPowerSeries.X c' : MvPowerSeries (I g) C) else 0 := by
      simp only [hA]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hB q, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
      have hx : ∀ c' : I g, (∑ c : I g, if (Y.raw p).ty g c' = (Y.raw p).ty (1 - g) q then
            (Y.raw p).sg1 ((Y.raw p).u g c') v •
              MvPowerSeries.subst (fun _ : Unit => t c) (tyS V.l (fun s => S.cur c s (Sum.inl c'))) else 0) =
          if (Y.raw p).ty g c' = (Y.raw p).ty (1 - g) q then
            (Y.raw p).sg1 ((Y.raw p).u g c') v • (MvPowerSeries.X c' : MvPowerSeries (I g) C) else 0 := by
        intro c'
        split_ifs
        · rw [← Finset.smul_sum, hC c']
        · exact Finset.sum_const_zero
      rw [Finset.sum_congr rfl fun c' _ => hx c']
      ring
    have hsplit : MvPowerSeries.subst t ((MvPowerSeries.subst Γ ((Y.raw p).sg v) -
        ∑ c, MvPowerSeries.subst (γt c) ((Y.raw p).sg v)) +
          ∑ c, MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X c : MvPowerSeries (I g) C)) (lam c q)) =
        MvPowerSeries.subst t (MvPowerSeries.subst Γ ((Y.raw p).sg v)) -
          ∑ c, MvPowerSeries.subst (fun _ : Unit => t c) (alongCv (γ c) ((Y.raw p).sg v)) +
          ∑ c, MvPowerSeries.subst (fun _ : Unit => t c) (lam c q) := by
      rw [← hpush, ← MvPowerSeries.coe_substAlgHom htS, map_add, map_sub, map_sum, map_sum]
      simp only [MvPowerSeries.coe_substAlgHom, key2]
    rw [hexp, hsum, hsplit, hAll]
    ring

end Formalism.L2.FormalSeriesBounds
