import Development.WeilBound.CoreStatements.HodgeTatePoints.CbBase

noncomputable section

namespace PositivityTheory.HtPt.Cb

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open ReciprocityTheory.ChartRestriction.G.TB

section

variable {R : Type} [CommRing R] {σ : Type} [Finite σ]

def scl (w : σ → ℕ) (m : σ →₀ ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun s => w s * m s

@[simp] theorem scl_apply (w : σ → ℕ) (m : σ →₀ ℕ) (s : σ) : scl w m s = w s * m s := rfl

theorem scl_inj {w : σ → ℕ} (hw : ∀ s, w s ≠ 0) : Function.Injective (scl w) := fun m m' h => by
  ext s
  have := congrArg (fun f => f s) h
  simpa [hw s] using this

theorem hasSubst_w {w : σ → ℕ} (hw : ∀ s, w s ≠ 0) :
    HasSubst (fun s => (X s : MvPowerSeries σ R) ^ w s) :=
  hasSubst_of_constantCoeff_zero fun s => by simp [hw s]

theorem prod_w (w : σ → ℕ) (m : σ →₀ ℕ) :
    (m.prod fun s e => ((X s : MvPowerSeries σ R) ^ w s) ^ e) = monomial (scl w m) 1 := by
  classical
  have := Fintype.ofFinite σ
  rw [monomial_eq', Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp [pow_mul]

theorem coeff_scl {w : σ → ℕ} (hw : ∀ s, w s ≠ 0) (g : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff (scl w m) (subst (fun s => (X s : MvPowerSeries σ R) ^ w s) g) = coeff m g := by
  classical
  rw [coeff_subst (hasSubst_w hw), finsum_eq_single _ m]
  · simp [prod_w]
  · intro m' h
    rw [prod_w, coeff_monomial, if_neg ((scl_inj hw).ne h.symm), smul_zero]

theorem coeff_not_scl {w : σ → ℕ} (hw : ∀ s, w s ≠ 0) (g : MvPowerSeries σ R) (e : σ →₀ ℕ)
    (he : ∀ m, e ≠ scl w m) :
    coeff e (subst (fun s => (X s : MvPowerSeries σ R) ^ w s) g) = 0 := by
  classical
  rw [coeff_subst (hasSubst_w hw)]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  rw [prod_w, coeff_monomial, if_neg (he m), smul_zero]

theorem exists_scl (p : ℕ) [hp : Fact p.Prime] [CharP R p] (S : σ → Prop) [DecidablePred S]
    (f : MvPowerSeries σ R) (hf : ∀ s, S s → pderiv R s f = 0) :
    ∃ g : MvPowerSeries σ R, f = subst (fun s => (X s : MvPowerSeries σ R) ^ (if S s then p else 1)) g := by
  classical
  have hw : ∀ s, (if S s then p else 1) ≠ 0 := fun s => by split_ifs <;> simp [hp.out.ne_zero]
  obtain ⟨g, hg⟩ : ∃ g : MvPowerSeries σ R, ∀ m, coeff m g = coeff (scl (fun s => if S s then p else 1) m) f :=
    ⟨fun m => coeff (scl (fun s => if S s then p else 1) m) f, fun _ => rfl⟩
  refine ⟨g, ?_⟩
  ext e
  by_cases he : ∃ m, e = scl (fun s => if S s then p else 1) m
  · obtain ⟨m, rfl⟩ := he
    rw [coeff_scl hw, hg]
  · rw [coeff_not_scl hw _ _ (not_exists.1 he)]
    obtain ⟨s, hS, hs⟩ : ∃ s, S s ∧ ¬ p ∣ e s := by
      by_contra hc
      push Not at hc
      refine he ⟨Finsupp.equivFunOnFinite.symm fun s => if S s then e s / p else e s, ?_⟩
      ext s
      by_cases h : S s
      · simp [h, Nat.mul_div_cancel' (hc s h)]
      · simp [h]
    have h0 : e s ≠ 0 := fun h => hs (h ▸ dvd_zero p)
    have h1 := congrArg (coeff (e - Finsupp.single s 1)) (hf s hS)
    rw [coeff_pderiv, tsub_add_cancel_of_le (by simpa [Finsupp.single_le_iff] using Nat.one_le_iff_ne_zero.2 h0),
      map_zero] at h1
    have h2 : (((e - Finsupp.single s 1 : σ →₀ ℕ) s : ℕ) : R) + 1 = (e s : R) := by
      rw [← Nat.cast_succ]; congr 1; simp; omega
    rw [h2] at h1
    have hu : IsUnit (e s : R) := (CharP.isUnit_natCast_iff hp.out).2 hs
    exact hu.mul_left_eq_zero.1 h1

end

section

variable {R : Type} [CommRing R] {d : ℕ} (p : ℕ)

theorem ev_pow_one_eq (g : PS R 1 d) : ev (n := 1) ![ptPow R d p 0] g =
    subst (fun s : Fin 1 × Fin d => (X s : PS R 1 d) ^ (if s.1 = 0 then p else 1)) g := by
  unfold ev; congr 1; funext ⟨j, i⟩; fin_cases j; simp [ptPow]

theorem ev_pow_two_eq (g : PS R 2 d) : ev (n := 2) ![ptPow R d p 0, pt R d 1] g =
    subst (fun s : Fin 2 × Fin d => (X s : PS R 2 d) ^ (if s.1 = 0 then p else 1)) g := by
  unfold ev; congr 1; funext ⟨j, i⟩; fin_cases j <;> simp [ptPow, pt]

variable [hp : Fact p.Prime]

theorem w_ne {n : ℕ} [NeZero n] (s : Fin n × Fin d) : (if s.1 = 0 then p else 1) ≠ 0 := by
  split_ifs <;> simp [hp.out.ne_zero]

theorem ev_pow_inj {f g : PS R 1 d} (h : ev (n := 1) ![ptPow R d p 0] f = ev ![ptPow R d p 0] g) : f = g := by
  ext m
  rw [← coeff_scl (w_ne p) f, ← coeff_scl (w_ne p) g, ← ev_pow_one_eq, ← ev_pow_one_eq, h]

theorem coeff_ev_pow_one (g : PS R 1 d) (j : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), j) p) (ev (n := 1) ![ptPow R d p 0] g) =
      coeff (Finsupp.single ((0 : Fin 1), j) 1) g := by
  rw [← coeff_scl (w_ne p) g, ev_pow_one_eq]
  congr 2
  ext s
  by_cases h : s = (0, j)
  · simp [h]
  · simp [Finsupp.single_eq_of_ne h]

theorem bil_ev_pow_two (g : PS R 2 d) : bil (ev (n := 2) ![ptPow R d p 0, pt R d 1] g) p 1 = bil g 1 1 := by
  ext i j
  rw [bil, bil, ← coeff_scl (w_ne p) g, ev_pow_two_eq]
  congr 2
  ext ⟨s, t⟩
  fin_cases s <;> simp [Finsupp.single_apply]

end

theorem series_in_p : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ), (∀ f : PS R 1 d, (∀ j, pderiv R ((0 : Fin 1), j) f = 0) → ∃ g : PS R 1 d, f = ev (n := 1) ![ptPow R d p 0] g) ∧ ∀ f : PS R 2 d, (∀ j, pderiv R ((0 : Fin 2), j) f = 0) → ∃ g : PS R 2 d, f = ev (n := 2) ![ptPow R d p 0, pt R d 1] g := by
  intro R _ p _ _ d
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩
  · simp only [ev_pow_one_eq]
    exact exists_scl p (fun s : Fin 1 × Fin d => s.1 = 0) f fun ⟨s, t⟩ h => by
      obtain rfl : s = 0 := h
      exact hf t
  · simp only [ev_pow_two_eq]
    exact exists_scl p (fun s : Fin 2 × Fin d => s.1 = 0) f fun ⟨s, t⟩ h => by
      obtain rfl : s = 0 := h
      exact hf t

theorem frob_subst : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d n : ℕ) (f : PS R n d), f ^ p = ev (fun j => ptPow R d p j) (MvPowerSeries.map (frobenius R p) f) := by
  intro R _ p hp _ d n f
  rw [← map_frobenius_expand p hp.out.ne_zero, map_expand, expand, substAlgHom_apply]
  rfl

end PositivityTheory.HtPt.Cb
