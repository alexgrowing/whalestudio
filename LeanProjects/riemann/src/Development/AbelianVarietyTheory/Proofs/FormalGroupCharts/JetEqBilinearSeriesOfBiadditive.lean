import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesJetEqCalculus

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp.BilAdd

variable {k : Type} [CommRing k] {d : ℕ}

theorem hasSubst_pts {n l : ℕ} (a : Fin l → Pt k n d) (h : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) :
    MvPowerSeries.HasSubst (fun p : Fin l × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => h p.1 p.2

theorem ev_add {n l : ℕ} (a : Fin l → Pt k n d) (h : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f g : PS k l d) :
    ev a (f + g) = ev a f + ev a g :=
  MvPowerSeries.subst_add (hasSubst_pts a h) f g

theorem ev_pt {n l : ℕ} (a : Fin l → Pt k n d) (h : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (j : Fin l) (i : Fin d) :
    ev a (pt k d j i) = a j i :=
  MvPowerSeries.subst_X (hasSubst_pts a h) (j, i)

theorem ev_ev {n l r : ℕ} (a : Fin l → Pt k n d) (b : Fin n → Pt k r d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (hb : ∀ j i, MvPowerSeries.constantCoeff (b j i) = 0)
    (f : PS k l d) : ev b (ev a f) = ev (fun j i => ev b (a j i)) f :=
  MvPowerSeries.subst_comp_subst_apply (hasSubst_pts a ha) (hasSubst_pts b hb) f

theorem const_pt {n : ℕ} (j : Fin n) (i : Fin d) : MvPowerSeries.constantCoeff (pt k d j i) = 0 :=
  MvPowerSeries.constantCoeff_X _

theorem ev_id {n : ℕ} (f : PS k n d) : ev (fun j => pt k d j) f = f := by
  have := MvPowerSeries.subst_self (σ := Fin n × Fin d) (R := k)
  exact congrFun this f

def degIn (j : Fin 2) (e : Fin 2 × Fin d →₀ ℕ) : ℕ := ∑ i, e (j, i)

theorem coeff_double (j : Fin 2) (g : PS k 2 d) (e : Fin 2 × Fin d →₀ ℕ) :
    MvPowerSeries.coeff e (ev (n := 2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g) =
      2 ^ degIn j e * MvPowerSeries.coeff e g := by
  have h : ev (n := 2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g =
      MvPowerSeries.rescale (fun p : Fin 2 × Fin d => if p.1 = j then (2 : k) else 1) g := by
    rw [MvPowerSeries.rescale_eq_subst]
    unfold ev
    congr 1
    funext p
    by_cases hp : p.1 = j
    · subst hp
      simp [pt, two_smul]
    · simp [hp, pt]
  rw [h, MvPowerSeries.coeff_rescale]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type, degIn, ← Finset.prod_pow_eq_pow_sum,
    Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem eq_zero_of_double [Algebra ℚ k] {a : ℕ} (ha : a ≠ 1) {c : k} (h : 2 ^ a * c = c + c) : c = 0 := by
  have h0 : ((2 : ℚ) ^ a - 2) ≠ 0 := by
    intro h
    apply ha
    have : (2 : ℚ) ^ a = 2 ^ 1 := by linarith
    exact (pow_right_injective₀ (by norm_num) (by norm_num)) this
  have hu : IsUnit ((2 : k) ^ a - 2) := by
    have := (IsUnit.mk0 _ h0).map (algebraMap ℚ k)
    simpa [map_ofNat] using this
  apply hu.mul_right_eq_zero.mp
  linear_combination h

theorem exists_single {e : Fin 2 × Fin d →₀ ℕ} (h0 : degIn 0 e = 1) (h1 : degIn 1 e = 1) :
    ∃ i j, e = Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 := by
  have key : ∀ f : Fin d → ℕ, ∑ i, f i = 1 → ∃ i, ∀ i', f i' = if i = i' then 1 else 0 := by
    intro f hf
    obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
      by_contra hc
      push Not at hc
      simp [hc] at hf
    refine ⟨i, fun i' => ?_⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hf
    split_ifs with h
    · subst h
      omega
    · have := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨fun hh => h hh.symm, Finset.mem_univ i'⟩ : i' ∈ Finset.univ.erase i)
      omega
  obtain ⟨i, hi⟩ := key _ h0
  obtain ⟨j, hj⟩ := key _ h1
  refine ⟨i, j, ?_⟩
  ext ⟨l, p⟩
  fin_cases l
  · simp [hi, Finsupp.single_apply]
  · simp [hj, Finsupp.single_apply]

theorem coeff_bilSer (β : Matrix (Fin d) (Fin d) k) (e : Fin 2 × Fin d →₀ ℕ) :
    MvPowerSeries.coeff e (bilSer β (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      ∑ i, ∑ j, if e = Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 then β i j else 0 := by
  simp only [bilSer, map_sum, pt, MvPowerSeries.coeff_C_mul, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial,
    MvPowerSeries.coeff_monomial]
  simp

theorem single_inj {i j i' j' : Fin d}
    (h : (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 : Fin 2 × Fin d →₀ ℕ) =
      Finsupp.single ((0 : Fin 2), i') 1 + Finsupp.single ((1 : Fin 2), j') 1) : i = i' ∧ j = j' := by
  have h0 := DFunLike.congr_fun h (0, i)
  have h1 := DFunLike.congr_fun h (1, j)
  simp [Finsupp.single_apply] at h0 h1
  exact ⟨h0.symm, h1.symm⟩

theorem jeq_bil_of_double [Algebra ℚ k] (m : ℕ) (g : PS k 2 d)
    (h : ∀ j : Fin 2, JEq m (ev (n := 2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g) (g + g)) :
    JEq m g (bilSer (fun i j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g)
      (pt k (n := 2) d 0) (pt k (n := 2) d 1)) := by
  intro e he
  refine Eq.trans ?_ (coeff_bilSer _ e).symm
  by_cases hex : ∃ i j, e = Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1
  · obtain ⟨i, j, rfl⟩ := hex
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j, if_pos rfl]
    · intro b _ hb
      exact if_neg fun hh => hb (single_inj hh).2.symm
    · simp
    · intro b _ hb
      exact Finset.sum_eq_zero fun c _ => if_neg fun hh => hb (single_inj hh).1.symm
    · simp
  · have hz : MvPowerSeries.coeff e g = 0 := by
      have : ∃ j, degIn j e ≠ 1 := by
        by_contra hc
        push Not at hc
        exact hex (exists_single (hc 0) (hc 1))
      obtain ⟨j, hj⟩ := this
      have := h j e he
      rw [coeff_double, map_add] at this
      exact eq_zero_of_double hj this
    rw [hz]
    symm
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => if_neg fun hh => hex ⟨i, j, hh⟩

theorem ev_pair (b : Fin 3 → Pt k 2 d) (hb : ∀ j i, MvPowerSeries.constantCoeff (b j i) = 0) (g : PS k 2 d)
    (u v : Pt k 3 d) (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0) :
    ev b (ev ![u, v] g) = ev ![fun i => ev b (u i), fun i => ev b (v i)] g := by
  rw [ev_ev _ _ _ hb]
  · congr 1
    funext j
    fin_cases j <;> rfl
  · intro j i
    fin_cases j
    · exact hu i
    · exact hv i

theorem jeq_bilSer_of_biadditive : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d m : ℕ) (g : PS k 2 d), JEq m (ev (n := 3) ![pt k (n := 3) d 0 + pt k (n := 3) d 1, pt k (n := 3) d 2] g) (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g + ev (n := 3) ![pt k (n := 3) d 1, pt k (n := 3) d 2] g) → JEq m (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1 + pt k (n := 3) d 2] g) (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1] g + ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g) → JEq m g (bilSer (fun i j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g) (pt k (n := 2) d 0) (pt k (n := 2) d 1)) := by
  intro k _ _ d m g h1 h2
  have hsub := (GlobalTheory.ChartCmp.JCalc.jeq_calculus k m).2.2.2.1
  have hid : ev (n := 2) ![pt k (n := 2) d 0, pt k (n := 2) d 1] g = g := by
    refine Eq.trans ?_ (ev_id g)
    congr 1
    funext j
    fin_cases j <;> rfl
  have hc : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff (pt k (n := 3) d s i) = 0 := fun s i => const_pt s i
  have hc2 : ∀ (s t : Fin 3) i, MvPowerSeries.constantCoeff ((pt k (n := 3) d s + pt k (n := 3) d t) i) = 0 := by
    intro s t i
    simp [hc]
  apply jeq_bil_of_double
  intro j
  fin_cases j
  · have hb : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff
        ((![pt k (n := 2) d 0, pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 3 → Pt k 2 d) s i) = 0 := by
      intro s i
      fin_cases s <;> exact const_pt _ _
    have := hsub d 3 2 _ _ _ _ hb hb (fun _ _ => JEq.refl _ _) h1
    rw [ev_add _ hb, ev_pair _ hb _ _ _ (hc2 _ _) (hc _), ev_pair _ hb _ _ _ (hc _) (hc _),
      ev_pair _ hb _ _ _ (hc _) (hc _)] at this
    simp only [Pi.add_apply, ev_add _ hb, ev_pt _ hb] at this
    convert this using 2
    · funext l
      fin_cases l <;> rfl
    · exact hid.symm
    · exact hid.symm
  · have hb : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff
        ((![pt k (n := 2) d 0, pt k (n := 2) d 1, pt k (n := 2) d 1] : Fin 3 → Pt k 2 d) s i) = 0 := by
      intro s i
      fin_cases s <;> exact const_pt _ _
    have := hsub d 3 2 _ _ _ _ hb hb (fun _ _ => JEq.refl _ _) h2
    rw [ev_add _ hb, ev_pair _ hb _ _ _ (hc _) (hc2 _ _), ev_pair _ hb _ _ _ (hc _) (hc _),
      ev_pair _ hb _ _ _ (hc _) (hc _)] at this
    simp only [Pi.add_apply, ev_add _ hb, ev_pt _ hb] at this
    convert this using 2
    · funext l
      fin_cases l <;> rfl
    · exact hid.symm
    · exact hid.symm

end GlobalTheory.ChartCmp.BilAdd
