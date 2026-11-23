import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalLogEqSumOfMultiplicativeParam

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Sum

namespace GlobalTheory.FormalCocycle

section Tools

variable {k : Type} [CommRing k] {d : ℕ} {μ ν : Type}

def evAt {m : ℕ} (a : Fin m → Fin d → MvPowerSeries μ k) (f : PS k m d) : MvPowerSeries μ k :=
  subst (fun p : Fin m × Fin d => a p.1 p.2) f

def Cen (u : Fin d → MvPowerSeries μ k) : Prop := ∀ i, constantCoeff (u i) = 0

theorem ev_eq {m n : ℕ} (a : Fin m → Pt k n d) (f : PS k m d) : ev a f = evAt a f := rfl

theorem cen1 {u : Fin d → MvPowerSeries μ k} (hu : Cen u) : ∀ j, Cen (![u] j) := by
  intro j; fin_cases j; exact hu

theorem cen2 {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) :
    ∀ j, Cen (![u, v] j) := by
  intro j; fin_cases j; exacts [hu, hv]

theorem cen3 {u v w : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (hw : Cen w) :
    ∀ j, Cen (![u, v, w] j) := by
  intro j; fin_cases j; exacts [hu, hv, hw]

theorem cen4 {u v w t : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (hw : Cen w)
    (ht : Cen t) : ∀ j, Cen (![u, v, w, t] j) := by
  intro j; fin_cases j; exacts [hu, hv, hw, ht]

theorem cen_zero : Cen (0 : Fin d → MvPowerSeries μ k) := fun _ => by simp

theorem cen_X (g : Fin d → μ) : Cen (fun i => (X (g i) : MvPowerSeries μ k)) := fun _ => by simp

theorem cen_pt {n : ℕ} (j : Fin n) : Cen (pt k d j) := fun _ => by simp [pt]

theorem cen_add {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) : Cen (u + v) :=
  fun i => by simp [hu i, hv i]

theorem hasSubst_pts {m : ℕ} {a : Fin m → Fin d → MvPowerSeries μ k} (ha : ∀ j, Cen (a j)) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2

theorem cen_evAt {m : ℕ} {a : Fin m → Fin d → MvPowerSeries μ k} (ha : ∀ j, Cen (a j))
    {F : Fin d → PS k m d} (hF : ∀ i, constantCoeff (F i) = 0) : Cen fun i => evAt a (F i) :=
  fun i => constantCoeff_subst_eq_zero (hasSubst_pts ha) (fun p => ha p.1 p.2) (hF i)

theorem subst_evAt {m : ℕ} {b : μ → MvPowerSeries ν k} (hb : HasSubst b)
    {a : Fin m → Fin d → MvPowerSeries μ k} (ha : ∀ j, Cen (a j)) (f : PS k m d) :
    subst b (evAt a f) = evAt (fun j i => subst b (a j i)) f :=
  subst_comp_subst_apply (hasSubst_pts ha) hb f

theorem subst_evAt1 {b : μ → MvPowerSeries ν k} (hb : HasSubst b)
    {u : Fin d → MvPowerSeries μ k} (hu : Cen u) (f : PS k 1 d) :
    subst b (evAt ![u] f) = evAt ![fun i => subst b (u i)] f := by
  rw [subst_evAt hb (cen1 hu)]
  congr 1; funext j; fin_cases j; rfl

theorem subst_evAt2 {b : μ → MvPowerSeries ν k} (hb : HasSubst b)
    {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (f : PS k 2 d) :
    subst b (evAt ![u, v] f) = evAt ![fun i => subst b (u i), fun i => subst b (v i)] f := by
  rw [subst_evAt hb (cen2 hu hv)]
  congr 1; funext j; fin_cases j <;> rfl

theorem subst_evAt3 {b : μ → MvPowerSeries ν k} (hb : HasSubst b)
    {u v w : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (hw : Cen w) (f : PS k 3 d) :
    subst b (evAt ![u, v, w] f) =
      evAt ![fun i => subst b (u i), fun i => subst b (v i), fun i => subst b (w i)] f := by
  rw [subst_evAt hb (cen3 hu hv hw)]
  congr 1; funext j; fin_cases j <;> rfl

theorem subst_pt {m : ℕ} {a : Fin m → Fin d → MvPowerSeries μ k} (ha : ∀ j, Cen (a j))
    (j : Fin m) : (fun i => subst (fun p : Fin m × Fin d => a p.1 p.2) (pt k d j i)) = a j :=
  funext fun i => subst_X (hasSubst_pts ha) (j, i)

theorem subst_zero_pt {b : μ → MvPowerSeries ν k} (hb : HasSubst b) :
    (fun i => subst b ((0 : Fin d → MvPowerSeries μ k) i)) = (0 : Fin d → MvPowerSeries ν k) :=
  funext fun _ => GlobalTheory.FormalCalc.subst_zero' hb

def addAt (F : Fin d → PS k 2 d) (u v : Fin d → MvPowerSeries μ k) :
    Fin d → MvPowerSeries μ k := fun i => evAt ![u, v] (F i)

def mapAt (φ : Pt k 1 d) (u : Fin d → MvPowerSeries μ k) : Fin d → MvPowerSeries μ k :=
  fun i => evAt ![u] (φ i)

theorem cen_addAt {F : Fin d → PS k 2 d} (hF : ∀ i, constantCoeff (F i) = 0)
    {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) : Cen (addAt F u v) :=
  cen_evAt (cen2 hu hv) hF

theorem cen_mapAt {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0)
    {u : Fin d → MvPowerSeries μ k} (hu : Cen u) : Cen (mapAt φ u) :=
  cen_evAt (cen1 hu) hφ

theorem subst_addAt {b : μ → MvPowerSeries ν k} (hb : HasSubst b) (F : Fin d → PS k 2 d)
    {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) :
    (fun i => subst b (addAt F u v i)) =
      addAt F (fun i => subst b (u i)) fun i => subst b (v i) :=
  funext fun i => subst_evAt2 hb hu hv (F i)

theorem subst_mapAt {b : μ → MvPowerSeries ν k} (hb : HasSubst b) (φ : Pt k 1 d)
    {u : Fin d → MvPowerSeries μ k} (hu : Cen u) :
    (fun i => subst b (mapAt φ u i)) = mapAt φ fun i => subst b (u i) :=
  funext fun i => subst_evAt1 hb hu (φ i)

theorem mapAt_zero {φ : Pt k 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) :
    mapAt φ (0 : Fin d → MvPowerSeries μ k) = 0 := by
  funext i
  change subst (fun p : Fin 1 × Fin d => (![(0 : Fin d → MvPowerSeries μ k)] p.1) p.2) (φ i) = 0
  have e : (fun p : Fin 1 × Fin d => (![(0 : Fin d → MvPowerSeries μ k)] p.1) p.2) = 0 := by
    funext p; simp
  rw [e]
  exact subst_zero_of_constantCoeff_zero (hφ i)

theorem mapAt_mapAt {φ ψ : Pt k 1 d} (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (h : comp1 φ ψ = pt k (n := 1) d 0) {u : Fin d → MvPowerSeries μ k} (hu : Cen u) :
    mapAt φ (mapAt ψ u) = u := by
  have hb := hasSubst_pts (cen1 hu)
  have h1 := subst_mapAt hb φ (u := ψ) hψ
  have h2 : mapAt φ ψ = pt k (n := 1) d 0 := h
  rw [h2, subst_pt (cen1 hu)] at h1
  exact h1.symm

theorem mapAt_addAt {ℓ : Pt k 1 d} (hℓ : ∀ i, constantCoeff (ℓ i) = 0)
    {F : Fin d → PS k 2 d} (hF : ∀ i, constantCoeff (F i) = 0)
    (h : comp1 ℓ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1))
    {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) :
    mapAt ℓ (addAt F u v) = mapAt ℓ u + mapAt ℓ v := by
  have ha := cen2 hu hv
  have hb := hasSubst_pts ha
  have h2 : mapAt ℓ (addAt F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      mapAt ℓ (pt k (n := 2) d 0) + mapAt ℓ (pt k (n := 2) d 1) := h
  have h1 := subst_mapAt hb ℓ (cen_addAt hF (cen_pt (n := 2) 0) (cen_pt 1))
  rw [h2, subst_addAt hb F (cen_pt 0) (cen_pt 1), subst_pt ha, subst_pt ha] at h1
  have h3 := subst_mapAt hb ℓ (cen_pt (k := k) (d := d) (n := 2) 0)
  have h4 := subst_mapAt hb ℓ (cen_pt (k := k) (d := d) (n := 2) 1)
  rw [subst_pt ha] at h3 h4
  refine h1.symm.trans (funext fun i => ?_)
  rw [Pi.add_apply, subst_add hb, congrFun h3 i, congrFun h4 i]
  rfl

theorem formalSeriesSubstPoints_standard_three (c : PS k 3 d) : evAt ![pt k (n := 3) d 0, pt k d 1, pt k d 2] c = c := by
  have e : (fun p : Fin 3 × Fin d => (![pt k (n := 3) d 0, pt k d 1, pt k d 2] p.1) p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  rw [evAt, e, subst_self]
  rfl

theorem axis_at {c : PS k 3 d} (h : ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0)
    {u t : Fin d → MvPowerSeries μ k} (hu : Cen u) (ht : Cen t) : evAt ![0, u, t] c = 0 := by
  have ha := cen2 hu ht
  have hb := hasSubst_pts ha
  have h1 := congrArg (subst (fun p : Fin 2 × Fin d => ![u, t] p.1 p.2)) h
  rw [ev_eq, subst_evAt3 hb cen_zero (cen_pt 0) (cen_pt 1), subst_zero_pt hb, subst_pt ha,
    subst_pt ha, GlobalTheory.FormalCalc.subst_zero' hb] at h1
  exact h1

theorem symm_at {c : PS k 3 d} (h : ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c)
    {u v t : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (ht : Cen t) :
    evAt ![v, u, t] c = evAt ![u, v, t] c := by
  have ha := cen3 hu hv ht
  have hb := hasSubst_pts ha
  have h1 := congrArg (subst (fun p : Fin 3 × Fin d => ![u, v, t] p.1 p.2)) h
  rw [ev_eq, subst_evAt3 hb (cen_pt 1) (cen_pt 0) (cen_pt 2), subst_pt ha,
    subst_pt ha, subst_pt ha] at h1
  exact h1

theorem cocycle_at {F : Fin d → PS k 2 d} (hF : ∀ i, constantCoeff (F i) = 0) {c : PS k 3 d}
    (h : ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c +
        ev (n := 4) ![addOf F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c =
      ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c +
        ev (n := 4) ![pt k d 0, addOf F (pt k d 1) (pt k d 2), pt k d 3] c)
    {u v w t : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (hw : Cen w) (ht : Cen t) :
    evAt ![u, v, t] c + evAt ![addAt F u v, w, t] c =
      evAt ![v, w, t] c + evAt ![u, addAt F v w, t] c := by
  have ha := cen4 hu hv hw ht
  have hb := hasSubst_pts ha
  have h0 : evAt ![pt k (n := 4) d 0, pt k d 1, pt k d 3] c +
        evAt ![addAt F (pt k (n := 4) d 0) (pt k d 1), pt k d 2, pt k d 3] c =
      evAt ![pt k (n := 4) d 1, pt k d 2, pt k d 3] c +
        evAt ![pt k (n := 4) d 0, addAt F (pt k d 1) (pt k d 2), pt k d 3] c := h
  have h1 := congrArg (subst (fun p : Fin 4 × Fin d => ![u, v, w, t] p.1 p.2)) h0
  rw [subst_add hb, subst_add hb, subst_evAt3 hb (cen_pt 0) (cen_pt 1) (cen_pt 3),
    subst_evAt3 hb (cen_addAt hF (cen_pt 0) (cen_pt 1)) (cen_pt 2) (cen_pt 3),
    subst_evAt3 hb (cen_pt 1) (cen_pt 2) (cen_pt 3),
    subst_evAt3 hb (cen_pt 0) (cen_addAt hF (cen_pt 1) (cen_pt 2)) (cen_pt 3),
    subst_addAt hb F (cen_pt 0) (cen_pt 1), subst_addAt hb F (cen_pt 1) (cen_pt 2)] at h1
  simp only [subst_pt ha] at h1
  exact h1

theorem hasSubst_elim2 {u t : Fin d → MvPowerSeries μ k} (hu : Cen u) (ht : Cen t) :
    HasSubst (Sum.elim u t) :=
  hasSubst_of_constantCoeff_zero (by rintro (i | i); exacts [hu i, ht i])

theorem hasSubst_elim3 {u v t : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (ht : Cen t) :
    HasSubst (Sum.elim u (Sum.elim v t)) :=
  hasSubst_of_constantCoeff_zero (by rintro (i | i | i); exacts [hu i, hv i, ht i])

theorem subst_elim2 {b : μ → MvPowerSeries ν k} (hb : HasSubst b)
    {u t : Fin d → MvPowerSeries μ k} (hu : Cen u) (ht : Cen t)
    (K : MvPowerSeries (Fin d ⊕ Fin d) k) :
    subst b (subst (Sum.elim u t) K) =
      subst (Sum.elim (fun i => subst b (u i)) fun i => subst b (t i)) K := by
  rw [subst_comp_subst_apply (hasSubst_elim2 hu ht) hb, GlobalTheory.FormalCalc.subst_sumElim]

end Tools

theorem exists_coboundary_of_symm_cocycle :
    LogSt → (∀ (k : Type) [CommRing k] (d : ℕ) (φ : Pt k 1 d), (∀ i, constantCoeff (φ i) = 0) → IsUnit (dLin φ).det → ∃ φi : Pt k 1 d, IsInvPair φ φi) → ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (c : PS k 3 d), ev (n := 2) ![0, pt k d 0, pt k d 1] c = 0 → ev (n := 3) ![pt k d 1, pt k d 0, pt k d 2] c = c → ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c + ev (n := 4) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c = ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c + ev (n := 4) ![pt k d 0, addOf G.F (pt k d 1) (pt k d 2), pt k d 3] c → ∃ h : PS k 2 d, ev (n := 1) ![0, pt k d 0] h = 0 ∧ (∀ i, ev (n := 1) ![0, pt k d 0] (pderiv k ((0 : Fin 2), i) h) = 0) ∧ c = (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf G.F (pt k d 0) (pt k d 1), pt k d 2] h) := by
  intro hlog hinv k _ _ d G c hax hsy hco
  obtain ⟨ℓ, hℓ, hlin, hadd⟩ := hlog k d G
  obtain ⟨e, -, he, hle, hel⟩ := hinv k d ℓ hℓ (by rw [hlin, Matrix.det_one]; exact isUnit_one)
  have hF := G.const
  have hexp : ∀ {μ : Type} {u v : Fin d → MvPowerSeries μ k}, Cen u → Cen v →
      addAt G.F (mapAt e u) (mapAt e v) = mapAt e (u + v) := by
    intro μ u v hu hv
    have h1 := mapAt_addAt hℓ hF hadd (cen_mapAt he hu) (cen_mapAt he hv)
    rw [mapAt_mapAt he hle hu, mapAt_mapAt he hle hv] at h1
    rw [← h1, mapAt_mapAt hℓ hel (cen_addAt hF (cen_mapAt he hu) (cen_mapAt he hv))]
  obtain ⟨B, hB⟩ : ∃ B : MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) k,
      ∀ {μ : Type} {u v t : Fin d → MvPowerSeries μ k}, Cen u → Cen v → Cen t →
        subst (Sum.elim u (Sum.elim v t)) B = evAt ![mapAt e u, mapAt e v, t] c := by
    refine ⟨evAt ![mapAt e fun i => X (inl i), mapAt e fun i => X (inr (inl i)),
      fun i => X (inr (inr i))] c, ?_⟩
    intro μ u v t hu hv ht
    have hb := hasSubst_elim3 hu hv ht
    rw [subst_evAt3 hb (cen_mapAt he (cen_X _)) (cen_mapAt he (cen_X _)) (cen_X _),
      subst_mapAt hb e (cen_X _), subst_mapAt hb e (cen_X _)]
    simp only [subst_X hb, elim_inl, elim_inr]
  have hBX : B = evAt ![mapAt e fun i => X (inl i), mapAt e fun i => X (inr (inl i)),
      fun i => X (inr (inr i))] c := by
    rw [← hB (cen_X _) (cen_X _) (cen_X _), GlobalTheory.FormalCalc.subst_elim_elim_X]
  obtain ⟨K, ⟨hK0, hK1, hK⟩, -⟩ := GlobalTheory.FormalCalc.existsUnique_coboundary_param (B := B)
    (by
      have h1 := hB (μ := Fin d) (u := 0) (v := 0) (t := X) cen_zero cen_zero (cen_X id)
      rw [mapAt_zero he] at h1
      exact h1.trans (axis_at hax cen_zero (cen_X id)))
    (by
      rw [hB (cen_X _) (cen_X _) (cen_X _)]
      conv_rhs => rw [hBX]
      exact symm_at hsy (cen_mapAt he (cen_X _)) (cen_mapAt he (cen_X _)) (cen_X _))
    (by
      rw [hB (cen_X _) (cen_X _) (cen_X _), hB (cen_X _) (cen_X _) (cen_X _)]
      have h1 := hB (μ := Fin d ⊕ Fin d ⊕ Fin d ⊕ Fin d)
        (cen_add (cen_X fun i => inl i) (cen_X fun i => inr (inl i)))
        (cen_X fun i => inr (inr (inl i))) (cen_X fun i => inr (inr (inr i)))
      have h2 := hB (μ := Fin d ⊕ Fin d ⊕ Fin d ⊕ Fin d) (cen_X fun i => inl i)
        (cen_add (cen_X fun i => inr (inl i)) (cen_X fun i => inr (inr (inl i))))
        (cen_X fun i => inr (inr (inr i)))
      rw [← hexp (cen_X _) (cen_X _)] at h1 h2
      have h3 := cocycle_at hF hco (μ := Fin d ⊕ Fin d ⊕ Fin d ⊕ Fin d)
        (cen_mapAt he (cen_X fun i => inl i)) (cen_mapAt he (cen_X fun i => inr (inl i)))
        (cen_mapAt he (cen_X fun i => inr (inr (inl i)))) (cen_X fun i => inr (inr (inr i)))
      rw [← h1, ← h2] at h3
      exact h3)
  have hp : ∀ {n : ℕ} (j : Fin n), Cen (pt k d j) := cen_pt
  have hev : ∀ {n : ℕ} {u t : Pt k n d} (L : MvPowerSeries (Fin d ⊕ Fin d) k), Cen u → Cen t →
      ev ![u, t] (subst (Sum.elim (mapAt ℓ (pt k (n := 2) d 0)) (pt k d 1)) L) =
        subst (Sum.elim (mapAt ℓ u) t) L := by
    intro n u t L hu ht
    have ha := cen2 hu ht
    have hb := hasSubst_pts ha
    rw [ev, subst_elim2 hb (cen_mapAt hℓ (hp 0)) (hp 1), subst_mapAt hb ℓ (hp 0), subst_pt ha,
      subst_pt ha]
    rfl
  have hzero : ∀ L : MvPowerSeries (Fin d ⊕ Fin d) k,
      subst (Sum.elim (fun _ => 0) X : Fin d ⊕ Fin d → MvPowerSeries (Fin d) k) L = 0 →
      ev (n := 1) ![0, pt k d 0]
        (subst (Sum.elim (mapAt ℓ (pt k (n := 2) d 0)) (pt k d 1)) L) = 0 := by
    intro L hL
    rw [hev L cen_zero (hp 0), mapAt_zero hℓ]
    have hb : HasSubst (pt k (n := 1) d 0) := hasSubst_of_constantCoeff_zero (hp 0)
    have h1 := subst_elim2 hb (u := 0) (t := X) cen_zero (cen_X id) L
    rw [subst_zero_pt hb] at h1
    simp only [subst_X hb] at h1
    refine h1.symm.trans ?_
    exact (congrArg _ hL).trans (GlobalTheory.FormalCalc.subst_zero' hb)
  have hneg : ∀ {m n : ℕ} {a : Fin m → Pt k n d}, (∀ j, Cen (a j)) → ∀ f : PS k m d,
      ev a (-f) = - ev a f := by
    intro m n a ha f
    unfold ev
    rw [← coe_substAlgHom (hasSubst_pts ha), map_neg]
  refine ⟨-subst (Sum.elim (mapAt ℓ (pt k (n := 2) d 0)) (pt k d 1)) K, ?_, fun i => ?_, ?_⟩
  · rw [hneg (cen2 cen_zero (hp 0)), hzero K hK0, neg_zero]
  · have hb := hasSubst_pts (cen2 (cen_zero (μ := Fin 1 × Fin d)) (hp 0))
    rw [map_neg, hneg (cen2 cen_zero (hp 0)), neg_eq_zero,
      GlobalTheory.FormalCalc.pderiv_subst (hasSubst_elim2 (cen_mapAt hℓ (hp 0)) (hp 1)), Fintype.sum_sum_type]
    have h2 : ∀ j : Fin d, pderiv k ((0 : Fin 2), i) (pt k (n := 2) d 1 j) = 0 := fun j =>
      pderiv_X_of_ne (by simp)
    simp only [elim_inl, elim_inr, h2, mul_zero, Finset.sum_const_zero, add_zero]
    rw [ev, GlobalTheory.FormalCalc.subst_sum' hb]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h3 := hzero _ (hK1 j)
    rw [ev] at h3
    rw [subst_mul hb, h3, zero_mul]
  · have hA : Cen (addOf G.F (pt k (n := 3) d 0) (pt k d 1)) := cen_addAt hF (hp 0) (hp 1)
    rw [hneg (cen2 (hp 0) (hp 2)), hneg (cen2 (hp 1) (hp 2)), hneg (cen2 hA (hp 2)),
      hev K (hp 0) (hp 2), hev K (hp 1) (hp 2), hev K hA (hp 2)]
    have hl0 := cen_mapAt hℓ (hp (n := 3) 0)
    have hl1 := cen_mapAt hℓ (hp (n := 3) 1)
    have hb := hasSubst_elim3 hl0 hl1 (hp 2)
    have h1 := hB hl0 hl1 (hp 2)
    rw [mapAt_mapAt hℓ hel (hp 0), mapAt_mapAt hℓ hel (hp 1), formalSeriesSubstPoints_standard_three, hK, subst_sub hb,
      subst_sub hb, subst_elim2 hb (fun _ => by simp) (cen_X _), subst_elim2 hb (cen_X _) (cen_X _),
      subst_elim2 hb (cen_X _) (cen_X _)] at h1
    simp only [subst_add hb, subst_X hb, elim_inl, elim_inr] at h1
    have h4 : mapAt ℓ (addOf G.F (pt k (n := 3) d 0) (pt k d 1)) =
        fun i => mapAt ℓ (pt k (n := 3) d 0) i + mapAt ℓ (pt k (n := 3) d 1) i :=
      mapAt_addAt hℓ hF hadd (hp 0) (hp 1)
    rw [h4, ← h1]
    ring

end GlobalTheory.FormalCocycle
