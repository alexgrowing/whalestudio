import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {d d' : ℕ}

local notation "eX" => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.eXv
local notation "eZ'" => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.eZ

theorem eval_first_point_eq_rename (φ : PS R 1 d) : ev (n := 2) ![pt R d 0] φ = MvPowerSeries.rename (eX d) φ := by
  rw [MvPowerSeries.rename_eq_subst]
  unfold ev
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

theorem eval_second_point_eq_rename (φ : PS R 1 d) : ev (n := 2) ![pt R d 1] φ = MvPowerSeries.rename (eZ' d) φ := by
  rw [MvPowerSeries.rename_eq_subst]
  unfold ev
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

theorem coeff_xz_rename (P Q : PS R 1 d) (a b : Fin d) :
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), a) 1 + Finsupp.single ((1 : Fin 2), b) 1)
        (MvPowerSeries.rename (eX d) P * MvPowerSeries.rename (eZ' d) Q) =
      MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), a) 1) P *
        MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), b) 1) Q := by
  classical
  have hA : ∀ u : Fin 2 × Fin d →₀ ℕ, u ((1 : Fin 2), b) ≠ 0 →
      MvPowerSeries.coeff u (MvPowerSeries.rename (eX d) P) = 0 := by
    intro u hu
    refine MvPowerSeries.coeff_rename_eq_zero _ _ ?_
    rintro ⟨w, hw⟩
    apply hu
    rw [← hw]
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨⟨p, q⟩, hp⟩
    have h2 : (0 : Fin 2) = 1 := congrArg Prod.fst hp
    exact absurd h2 (by simp)
  have hB : ∀ v : Fin 2 × Fin d →₀ ℕ, v ((0 : Fin 2), a) ≠ 0 →
      MvPowerSeries.coeff v (MvPowerSeries.rename (eZ' d) Q) = 0 := by
    intro v hv
    refine MvPowerSeries.coeff_rename_eq_zero _ _ ?_
    rintro ⟨w, hw⟩
    apply hv
    rw [← hw]
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨⟨p, q⟩, hp⟩
    have h2 : (1 : Fin 2) = 0 := congrArg Prod.fst hp
    exact absurd h2 (by simp)
  have hne : ((0 : Fin 2), a) ≠ ((1 : Fin 2), b) := fun e => absurd (congrArg Prod.fst e) (by simp)
  have e0 : Finsupp.single ((0 : Fin 2), a) 1 = Finsupp.embDomain (eX d) (Finsupp.single ((0 : Fin 1), a) 1) := by
    rw [Finsupp.embDomain_single]; rfl
  have e1 : Finsupp.single ((1 : Fin 2), b) 1 = Finsupp.embDomain (eZ' d) (Finsupp.single ((0 : Fin 1), b) 1) := by
    rw [Finsupp.embDomain_single]; rfl
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single
    (Finsupp.single ((0 : Fin 2), a) 1, Finsupp.single ((1 : Fin 2), b) 1)]
  · show MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), a) 1) _ * MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), b) 1) _ = _
    rw [e0, e1, MvPowerSeries.coeff_embDomain_rename, MvPowerSeries.coeff_embDomain_rename]
  · rintro ⟨u, v⟩ huv hne'
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at huv
    simp only at huv ⊢
    by_cases hu : u ((1 : Fin 2), b) = 0
    · by_cases hv : v ((0 : Fin 2), a) = 0
      · exfalso
        apply hne'
        have hv1 := DFunLike.congr_fun huv ((1 : Fin 2), b)
        have hu0 := DFunLike.congr_fun huv ((0 : Fin 2), a)
        simp only [Finsupp.add_apply, Finsupp.single_apply, hne, hne.symm, if_true, if_false, hu, hv] at hv1 hu0
        have hrest : ∀ t, t ≠ ((0 : Fin 2), a) → t ≠ ((1 : Fin 2), b) → u t = 0 ∧ v t = 0 := by
          intro t h0 h1
          have ht := DFunLike.congr_fun huv t
          simp only [Finsupp.add_apply, Finsupp.single_apply, Ne.symm h0, Ne.symm h1, if_false] at ht
          omega
        refine Prod.ext (Finsupp.ext fun t => ?_) (Finsupp.ext fun t => ?_)
        · by_cases h0 : t = ((0 : Fin 2), a)
          · subst h0; simp; omega
          by_cases h1 : t = ((1 : Fin 2), b)
          · subst h1; simp [Finsupp.single_apply, hne.symm, hu]
          simp [Finsupp.single_apply, Ne.symm h0, (hrest t h0 h1).1]
        · by_cases h1 : t = ((1 : Fin 2), b)
          · subst h1; simp; omega
          by_cases h0 : t = ((0 : Fin 2), a)
          · subst h0; simp [Finsupp.single_apply, hne, hv]
          simp [Finsupp.single_apply, Ne.symm h1, (hrest t h0 h1).2]
      · rw [hB v hv, mul_zero]
    · rw [hA u hu, zero_mul]
  · intro h
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at h
    exact absurd rfl h

theorem const_side {Qs : Fin d' → PS R 1 d} (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0)
    (p : Fin 2 × Fin d') :
    MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d p.1] (Qs p.2)) = 0 := by
  obtain ⟨j, i⟩ := p
  fin_cases j
  · show MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d 0] (Qs i)) = 0
    rw [eval_first_point_eq_rename, MvPowerSeries.constantCoeff_rename, hQ]
  · show MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d 1] (Qs i)) = 0
    rw [eval_second_point_eq_rename, MvPowerSeries.constantCoeff_rename, hQ]

theorem subst_side {τ : Type} {b : Fin 2 × Fin d → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) (j : Fin 2)
    (φ : PS R 1 d) :
    MvPowerSeries.subst b (ev (n := 2) ![pt R d j] φ) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin d => b (j, q.2)) φ := by
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d => (![pt R d j] q.1 q.2 : PS R 2 d)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by
      obtain ⟨u, i⟩ := q
      fin_cases u
      exact MvPowerSeries.constantCoeff_X _
  unfold ev
  rw [MvPowerSeries.subst_comp_subst_apply hs hb]
  congr 1
  funext q
  obtain ⟨u, i⟩ := q
  fin_cases u
  exact MvPowerSeries.subst_X hb _

theorem subst_one' {σ τ : Type} {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (1 : MvPowerSeries σ R) = 1 := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_one]

theorem subst_zero' {σ τ : Type} {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (0 : MvPowerSeries σ R) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_zero]

theorem ev_subQ_eq_one {Qs : Fin d' → PS R 1 d} (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0)
    {f : PS R 2 d'} (A : Fin 2 → Pt R 1 d) (A' : Fin 2 → Pt R 1 d')
    (hA : ∀ j i, MvPowerSeries.constantCoeff (A j i) = 0) (hA' : ∀ j i, MvPowerSeries.constantCoeff (A' j i) = 0)
    (hc : ∀ j i, MvPowerSeries.subst (fun q : Fin 1 × Fin d => A j q.2) (Qs i) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2) (A' j i))
    (h : ev (n := 1) A' f = 1) : ev (n := 1) A (subQ Qs f) = 1 := by
  have hb : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d => A p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => hA p.1 p.2
  have hb' : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => A' p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => hA' p.1 p.2
  have hσ : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => ev (n := 2) ![pt R d p.1] (Qs p.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (const_side hQ)
  have hq : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d' => Qs q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hQ q.2
  have h1 := congrArg (MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2)) h
  unfold ev at h1
  rw [subst_one' hq, MvPowerSeries.subst_comp_subst_apply hb' hq] at h1
  unfold ev subQ
  rw [MvPowerSeries.subst_comp_subst_apply hσ hb, ← h1]
  congr 1
  funext p
  rw [subst_side hb, hc]

theorem axOne_subQ {Qs : Fin d' → PS R 1 d} (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0)
    {f : PS R 2 d'} (hf : AxOne f) : AxOne (subQ Qs f) := by
  have hq : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d' => Qs q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hQ q.2
  have hz : ∀ i, MvPowerSeries.subst (fun q : Fin 1 × Fin d => (0 : PS R 1 d)) (Qs i) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2) (0 : PS R 1 d') := fun i => by
    rw [subst_zero' hq]
    exact MvPowerSeries.subst_zero_of_constantCoeff_zero (hQ i)
  have hx : ∀ i, MvPowerSeries.subst (fun q : Fin 1 × Fin d => pt R d 0 q.2) (Qs i) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin d' => Qs q.2) (pt R d' 0 i) := fun i => by
    have e : (fun q : Fin 1 × Fin d => pt R d 0 q.2) = MvPowerSeries.X := by
      funext q
      obtain ⟨u, l⟩ := q
      fin_cases u
      rfl
    rw [e, MvPowerSeries.subst_self]
    show _ = MvPowerSeries.subst _ (MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 d')
    rw [MvPowerSeries.subst_X hq]
    rfl
  have c0 : ∀ {n : ℕ} (i : Fin n), MvPowerSeries.constantCoeff (pt R (n := 1) n 0 i) = 0 := fun i =>
    MvPowerSeries.constantCoeff_X _
  constructor
  · refine ev_subQ_eq_one hQ _ _ ?_ ?_ ?_ hf.1
    · intro j i; fin_cases j
      · exact map_zero _
      · exact c0 i
    · intro j i; fin_cases j
      · exact map_zero _
      · exact c0 i
    · intro j i; fin_cases j
      · exact hz i
      · exact hx i
  · refine ev_subQ_eq_one hQ _ _ ?_ ?_ ?_ hf.2
    · intro j i; fin_cases j
      · exact c0 i
      · exact map_zero _
    · intro j i; fin_cases j
      · exact c0 i
      · exact map_zero _
    · intro j i; fin_cases j
      · exact hx i
      · exact hz i

theorem bil_subQ {Qs : Fin d' → PS R 1 d} (hQ : ∀ i, MvPowerSeries.constantCoeff (Qs i) = 0)
    {f : PS R 2 d'} (hf : AxOne f) : bil (subQ Qs f) 1 1 = (linQ Qs).transpose * bil f 1 1 * linQ Qs := by
  classical
  have hσ : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => ev (n := 2) ![pt R d p.1] (Qs p.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (const_side hQ)
  have hA0 : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => (![0, pt R d' 0] : Fin 2 → Pt R 1 d') p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨j, i⟩ := p
      fin_cases j
      · exact map_zero _
      · exact MvPowerSeries.constantCoeff_X _
  have hA1 : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d' => (![pt R d' 0, 0] : Fin 2 → Pt R 1 d') p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨j, i⟩ := p
      fin_cases j
      · exact MvPowerSeries.constantCoeff_X _
      · exact map_zero _
  have h0 : ev (n := 1) ![0, pt R d' 0] (f - 1) = 0 := by
    unfold ev
    rw [MvPowerSeries.subst_sub hA0, subst_one' hA0]
    exact sub_eq_zero.2 hf.1
  have h1 : ev (n := 1) ![pt R d' 0, 0] (f - 1) = 0 := by
    unfold ev
    rw [MvPowerSeries.subst_sub hA1, subst_one' hA1]
    exact sub_eq_zero.2 hf.2
  ext a b
  have hdeg := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.degree_xz a b
  have hn : (Finsupp.single ((0 : Fin 2), a) 1 + Finsupp.single ((1 : Fin 2), b) 1 : Fin 2 × Fin d →₀ ℕ) ≠ 0 := by
    intro e
    rw [e] at hdeg
    simp at hdeg
  have key := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_subst_xz (f - 1) h0 h1 _ (const_side hQ) _ hdeg
  rw [MvPowerSeries.subst_sub hσ, subst_one' hσ, map_sub, MvPowerSeries.coeff_one, if_neg hn, sub_zero] at key
  show MvPowerSeries.coeff _ (subQ Qs f) = _
  refine key.trans ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
  have hl : (Finsupp.single ((0 : Fin 2), l) 1 + Finsupp.single ((1 : Fin 2), m) 1 : Fin 2 × Fin d' →₀ ℕ) ≠ 0 := by
    intro e
    have hd := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.degree_xz l m
    rw [e] at hd
    simp at hd
  have e0 : ev (n := 2) ![pt R d ((0 : Fin 2), l).1] (Qs ((0 : Fin 2), l).2) = MvPowerSeries.rename (eX d) (Qs l) :=
    eval_first_point_eq_rename _
  have e1 : ev (n := 2) ![pt R d ((1 : Fin 2), m).1] (Qs ((1 : Fin 2), m).2) = MvPowerSeries.rename (eZ' d) (Qs m) :=
    eval_second_point_eq_rename _
  rw [map_sub, MvPowerSeries.coeff_one, if_neg hl, sub_zero, e0, e1, coeff_xz_rename]
  show _ = linQ Qs l a * bil f 1 1 l m * linQ Qs m b
  simp only [linQ, bil]
  ring

theorem bil_axOne_subQ : ∀ (R : Type) [CommRing R] (d d' : ℕ) (Qs : Fin d' → PS R 1 d) (f : PS R 2 d'),
    (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → AxOne f →
      AxOne (subQ Qs f) ∧ bil (subQ Qs f) 1 1 = (linQ Qs).transpose * bil f 1 1 * linQ Qs :=
  fun _ _ _ _ _ _ hQ hf => ⟨axOne_subQ hQ hf, bil_subQ hQ hf⟩

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.BilQ
