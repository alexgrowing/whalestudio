import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem map_us {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (e : ℤˣ) (x : G) :
    f (e • x) = e • f x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

private theorem D_zero (C : DC) (n : ℤ) (x : C.Tot) (s t : ℤ) (h : s + 1 = t) :
    C.D n x 0 t = C.d 0 s t (x 0 s) := by
  obtain rfl : s = t - 1 := by omega
  rfl

private theorem D_succ (C : DC) (n : ℤ) (x : C.Tot) (p : ℕ) (s t : ℤ) (h : s + 1 = t) :
    C.D n x (p + 1) t = C.d (p + 1) s t (x (p + 1) s) + (n + 1).negOnePow • C.δ p t (x p t) := by
  obtain rfl : s = t - 1 := by omega
  rfl

private theorem col {C C' : DC} {Φ : C.Hom C'} {p : ℕ} (h : Φ.ColEx p) (r s t u : ℤ) (e1 : r + 1 = s)
    (e2 : s + 1 = t) (e3 : t + 1 = u) (a : C.A p t) (y : C'.A p s) (ha : C.d p t u a = 0)
    (hy : Φ p t a = C'.d p s t y) :
    ∃ (a' : C.A p s) (y' : C'.A p r), C.d p s t a' = a ∧ y = Φ p s a' + C'.d p r s y' := by
  subst e2
  subst e3
  obtain rfl : r = s - 1 := by omega
  exact h s a y ha hy

private structure Cl {C C' : DC} (Φ : C.Hom C') (n : ℤ) (p : ℕ) (b : ∀ s, C.A p s) (z : ∀ s, C'.A p s) : Prop where
  sb : ∀ s, (p : ℤ) + s ≠ n + 1 → b s = 0
  sz : ∀ s, (p : ℤ) + s ≠ n → z s = 0
  db : ∀ s t, s + 1 = t → C.d p s t (b s) = 0
  pz : ∀ s t, s + 1 = t → Φ p t (b t) = C'.d p s t (z s)

private structure Sv {C C' : DC} (Φ : C.Hom C') (n : ℤ) (p : ℕ) (b : ∀ s, C.A p s) (z : ∀ s, C'.A p s)
    (u : ∀ s, C.A p s) (v : ∀ s, C'.A p s) : Prop where
  su : ∀ s, (p : ℤ) + s ≠ n → u s = 0
  sv : ∀ s, (p : ℤ) + s ≠ n - 1 → v s = 0
  du : ∀ s t, s + 1 = t → C.d p s t (u s) = b t
  yv : ∀ r s, r + 1 = s → z s = Φ p s (u s) + C'.d p r s (v r)

private theorem solve {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {p : ℕ} (hcol : Φ.ColEx p)
    {b : ∀ s, C.A p s} {z : ∀ s, C'.A p s} (h : Cl Φ n p b z) : ∃ u v, Sv Φ n p b z u v := by
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℤ, s0 = n - p := ⟨_, rfl⟩
  obtain ⟨a', y', ha', hy'⟩ := col hcol (s0 - 1) s0 (s0 + 1) (s0 + 1 + 1) (by ring) rfl rfl
    (b (s0 + 1)) (z s0) (h.db _ _ rfl) (h.pz _ _ rfl)
  refine ⟨Function.update (fun _ => 0) s0 a', Function.update (fun _ => 0) (s0 - 1) y',
    ⟨?_, ?_, ?_, ?_⟩⟩
  · intro s hs
    rw [Function.update_of_ne (by omega)]
  · intro s hs
    rw [Function.update_of_ne (by omega)]
  · intro s t hst
    by_cases hs : s = s0
    · subst hst
      subst hs
      rw [Function.update_self, ha']
    · simp [Function.update_of_ne hs, h.sb t (by omega)]
  · intro r s hrs
    by_cases hs : s = s0
    · have hr : r = s - 1 := by omega
      subst hr
      subst hs
      rw [Function.update_self, Function.update_self, hy']
    · have hr : r ≠ s0 - 1 := by omega
      simp [Function.update_of_ne hs, Function.update_of_ne hr, h.sz s (by omega)]

private structure St {C C' : DC} (Φ : C.Hom C') (n : ℤ) (a : C.Tot) (y : C'.Tot) (p : ℕ) where
  b : ∀ s, C.A p s
  z : ∀ s, C'.A p s
  u : ∀ s, C.A p s
  v : ∀ s, C'.A p s
  cl : Cl Φ n p b z
  sv : Sv Φ n p b z u v
  hb : ∀ s, C.δ p s (a p s) = C.δ p s (b s)
  hz : ∀ s, C'.δ p s (y p s) = C'.δ p s (z s)

private theorem cl_zero {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {a : C.Tot} {y : C'.Tot}
    (ha : C.Deg (n + 1) a) (hy : C'.Deg n y) (hD : C.D (n + 1) a = 0) (hP : Φ.tot a = C'.D n y) :
    Cl Φ n 0 (a 0) (y 0) := by
  refine ⟨fun s hs => ha 0 s hs, fun s hs => hy 0 s hs, ?_, ?_⟩
  · intro s t e
    have h1 := congrFun (congrFun hD 0) t
    rw [D_zero C (n + 1) a s t e] at h1
    exact h1
  · intro s t e
    have h1 := congrFun (congrFun hP 0) t
    rw [D_zero C' n y s t e] at h1
    exact h1

private theorem cl_next {C C' : DC} {Φ : C.Hom C'} {n : ℤ} {a : C.Tot} {y : C'.Tot} {p : ℕ}
    (hC : C.Ok) (hC' : C'.Ok) (hΦ : Φ.Ok)
    (ha : C.Deg (n + 1) a) (hy : C'.Deg n y) (hD : C.D (n + 1) a = 0) (hP : Φ.tot a = C'.D n y)
    (x : St Φ n a y p) :
    Cl Φ n (p + 1) (fun s => a (p + 1) s - (n + 1).negOnePow • C.δ p s (x.u s))
      (fun s => y (p + 1) s + (n + 1).negOnePow • C'.δ p s (x.v s)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    simp only [ha (p + 1) s hs, x.sv.su s (by omega), map_zero, smul_zero, sub_zero]
  · intro s hs
    simp only [hy (p + 1) s hs, x.sv.sv s (by omega), map_zero, smul_zero, add_zero]
  · intro s t e
    have h1 := congrFun (congrFun hD (p + 1)) t
    rw [D_succ C (n + 1) a p s t e, Int.negOnePow_succ, Units.neg_smul, x.hb t] at h1
    simp only [Pi.zero_apply] at h1
    have h2 : C.d (p + 1) s t (C.δ p s (x.u s)) = C.δ p t (x.b t) := by
      rw [hC.comm, x.sv.du s t e]
    simp only [map_sub, map_us, h2]
    rwa [← sub_eq_add_neg] at h1
  · intro s t e
    have h1 := congrFun (congrFun hP (p + 1)) t
    rw [D_succ C' n y p s t e] at h1
    change Φ (p + 1) t (a (p + 1) t) = _ at h1
    have h3 : C'.δ p t (y p t) =
        C'.δ p t (Φ p t (x.u t)) + C'.d (p + 1) s t (C'.δ p s (x.v s)) := by
      rw [x.hz t, x.sv.yv s t e, map_add, hC'.comm]
    have h4 : Φ (p + 1) t (C.δ p t (x.u t)) = C'.δ p t (Φ p t (x.u t)) := hΦ.2 p t (x.u t)
    simp only [map_sub, map_add, map_us, h4]
    rw [h1, h3, smul_add]
    abel

theorem UpperTheory.totalExact_of_columnExact :
    ∀ (C C' : DC) (Φ : C.Hom C'), C.Ok → C'.Ok → Φ.Ok → (∀ p, Φ.ColEx p) → Φ.TotEx := by
  intro C C' Φ hC hC' hΦ hcol n a y ha hy hD hP
  have hcl0 := cl_zero (Φ := Φ) ha hy hD hP
  have hs0 := solve (hcol 0) hcl0
  let S0 : St Φ n a y 0 := ⟨a 0, y 0, hs0.choose, hs0.choose_spec.choose, hcl0,
    hs0.choose_spec.choose_spec, fun _ => rfl, fun _ => rfl⟩
  let step : ∀ p, St Φ n a y p → St Φ n a y (p + 1) := fun p x =>
    { b := fun s => a (p + 1) s - (n + 1).negOnePow • C.δ p s (x.u s)
      z := fun s => y (p + 1) s + (n + 1).negOnePow • C'.δ p s (x.v s)
      u := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose
      v := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose_spec.choose
      cl := cl_next hC hC' hΦ ha hy hD hP x
      sv := (solve (hcol (p + 1)) (cl_next hC hC' hΦ ha hy hD hP x)).choose_spec.choose_spec
      hb := fun s => by simp only [map_sub, map_us, hC.δδ, smul_zero, sub_zero]
      hz := fun s => by simp only [map_add, map_us, hC'.δδ, smul_zero, add_zero] }
  let S : ∀ p, St Φ n a y p := fun p => Nat.rec (motive := fun p => St Φ n a y p) S0 step p
  refine ⟨fun p s => (S p).u s, fun p s => (S p).v s, ?_, ?_, ?_, ?_⟩
  · intro p s hps
    exact (S p).sv.su s hps
  · intro p s hps
    exact (S p).sv.sv s hps
  · funext p t
    rcases p with _ | p
    · rw [D_zero C n _ (t - 1) t (by ring)]
      exact (S 0).sv.du (t - 1) t (by ring)
    · rw [D_succ C n _ p (t - 1) t (by ring)]
      have h1 := (S (p + 1)).sv.du (t - 1) t (by ring)
      change C.d (p + 1) (t - 1) t ((S (p + 1)).u (t - 1)) =
        a (p + 1) t - (n + 1).negOnePow • C.δ p t ((S p).u t) at h1
      beta_reduce
      rw [h1, sub_add_cancel]
  · funext p t
    rcases p with _ | p
    · show y 0 t = Φ 0 t ((S 0).u t) + C'.D (n - 1) (fun p s => (S p).v s) 0 t
      rw [D_zero C' (n - 1) _ (t - 1) t (by ring)]
      exact (S 0).sv.yv (t - 1) t (by ring)
    · show y (p + 1) t = Φ (p + 1) t ((S (p + 1)).u t) +
        C'.D (n - 1) (fun p s => (S p).v s) (p + 1) t
      rw [D_succ C' (n - 1) _ p (t - 1) t (by ring)]
      have h1 := (S (p + 1)).sv.yv (t - 1) t (by ring)
      change y (p + 1) t + (n + 1).negOnePow • C'.δ p t ((S p).v t) =
        Φ (p + 1) t ((S (p + 1)).u t) + C'.d (p + 1) (t - 1) t ((S (p + 1)).v (t - 1)) at h1
      have e : (n - 1 + 1).negOnePow = -(n + 1).negOnePow := by
        rw [sub_add_cancel, Int.negOnePow_succ, neg_neg]
      beta_reduce
      rw [e, Units.neg_smul, eq_sub_of_add_eq h1]
      abel
