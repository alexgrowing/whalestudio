import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.DegreeAdditivity

private theorem D_add {C : DC} (n : ℤ) (x y : C.Tot) : C.D n (x + y) = C.D n x + C.D n y := by
  funext p t
  rcases p with _ | p
  · simp [DC.D, map_add]
  · simp only [DC.D, Pi.add_apply, map_add, smul_add]
    abel

private theorem D_sub {C : DC} (n : ℤ) (x y : C.Tot) : C.D n (x - y) = C.D n x - C.D n y := by
  funext p t
  rcases p with _ | p
  · simp [DC.D, map_sub]
  · simp only [DC.D, Pi.sub_apply, map_sub, smul_sub]
    abel

private theorem D_zero {C : DC} (n : ℤ) : C.D n (0 : C.Tot) = 0 := by
  funext p t
  rcases p with _ | p <;> simp [DC.D]

private theorem Deg_zero {C : DC} {n : ℤ} : C.Deg n (0 : C.Tot) := fun _ _ _ => rfl

private theorem Deg_add {C : DC} {n : ℤ} {x y : C.Tot} (hx : C.Deg n x) (hy : C.Deg n y) :
    C.Deg n (x + y) := fun p s h => by
  change x p s + y p s = 0
  rw [hx p s h, hy p s h, add_zero]

private theorem Deg_sub {C : DC} {n : ℤ} {x y : C.Tot} (hx : C.Deg n x) (hy : C.Deg n y) :
    C.Deg n (x - y) := fun p s h => by
  change x p s - y p s = 0
  rw [hx p s h, hy p s h, sub_zero]

private theorem tot_add {C C' : DC} (Φ : C.Hom C') (x y : C.Tot) :
    Φ.tot (x + y) = Φ.tot x + Φ.tot y := by
  funext p s
  exact map_add _ _ _

private theorem tot_sub {C C' : DC} (Φ : C.Hom C') (x y : C.Tot) :
    Φ.tot (x - y) = Φ.tot x - Φ.tot y := by
  funext p s
  exact map_sub _ _ _

private theorem tot_zero {C C' : DC} (Φ : C.Hom C') : Φ.tot (0 : C.Tot) = 0 := by
  funext p s
  exact map_zero _

private theorem Deg_tot {C C' : DC} (Φ : C.Hom C') {n : ℤ} {x : C.Tot} (h : C.Deg n x) :
    C'.Deg n (Φ.tot x) := fun p s hne => by
  change Φ p s (x p s) = 0
  rw [h p s hne, map_zero]

private theorem hom_d {C C' : DC} {Φ : C.Hom C'} (h : Φ.Ok) (p : ℕ) (s t : ℤ) (e : t = s + 1)
    (x : C.A p s) : Φ p t (C.d p s t x) = C'.d p s t (Φ p s x) := by
  subst e
  exact h.1 p s x

private theorem tot_D {C C' : DC} {Φ : C.Hom C'} (h : Φ.Ok) (n : ℤ) (x : C.Tot) :
    Φ.tot (C.D n x) = C'.D n (Φ.tot x) := by
  funext p t
  rcases p with _ | p
  · simp only [DC.D, DC.Hom.tot]
    exact hom_d h 0 (t - 1) t (by ring) _
  · simp only [DC.D, DC.Hom.tot, map_add, Units.smul_def, map_zsmul]
    rw [hom_d h (p + 1) (t - 1) t (by ring), h.2]

private theorem rel_zero {C : DC} {n : ℤ} {H : Type 1} [AddCommGroup H] {rel : C.Tot → H → Prop}
    (h : TModel C n rel) : rel 0 0 := by
  obtain ⟨x, -, -, r⟩ := h.surj 0
  have := h.sub x 0 x 0 r r
  simpa using this

end UpperTheory.DegreeAdditivity

open UpperTheory.DegreeAdditivity in
theorem UpperTheory.bijective_iff_totalQuasiIso_of_totalModels :
    ∀ (C C' : DC) (Φ : C.Hom C'), C.Ok → C'.Ok → Φ.Ok → ∀ (H H' : ℤ → Type 1) [∀ n, AddCommGroup (H n)] [∀ n, AddCommGroup (H' n)] (rel : ∀ n, C.Tot → H n → Prop) (rel' : ∀ n, C'.Tot → H' n → Prop) (F : ∀ n, H n → H' n),
    (∀ n, TModel C n (rel n)) → (∀ n, TModel C' n (rel' n)) → (∀ n x a, rel n x a → rel' n (Φ.tot x) (F n a)) → ((∀ n, Function.Bijective (F n)) ↔ Φ.TotEx) := by
  intro C C' Φ hC hC' hΦ H H' _ _ rel rel' F hM hM' hF
  constructor
  · intro hbij n a y ha hy hDa hΦa
    obtain ⟨ca, ra⟩ := (hM (n + 1)).ex a ha hDa
    have r0 : rel' (n + 1) 0 (F (n + 1) 0) := by
      have := hF (n + 1) 0 0 (rel_zero (hM (n + 1)))
      rwa [tot_zero] at this
    have hF0 : F (n + 1) 0 = 0 :=
      ((hM' (n + 1)).zero 0 (F (n + 1) 0) Deg_zero r0).2 ⟨0, Deg_zero, D_zero _⟩
    have hFa : F (n + 1) ca = 0 := by
      refine ((hM' (n + 1)).zero _ _ (Deg_tot Φ ha) (hF (n + 1) a ca ra)).2 ⟨y, ?_, ?_⟩
      · simpa using hy
      · simpa using hΦa.symm
    have hca : ca = 0 := (hbij (n + 1)).1 (hFa.trans hF0.symm)
    obtain ⟨a', ha', hDa'⟩ := ((hM (n + 1)).zero a ca ha ra).1 hca
    simp only [add_sub_cancel_right] at ha' hDa'
    have hz : C'.Deg n (y - Φ.tot a') := Deg_sub hy (Deg_tot Φ ha')
    have hDz : C'.D n (y - Φ.tot a') = 0 := by
      rw [D_sub, ← tot_D hΦ, hDa', hΦa, sub_self]
    obtain ⟨cz, rz⟩ := (hM' n).ex _ hz hDz
    obtain ⟨c, hc⟩ := (hbij n).2 cz
    obtain ⟨w, hw, hDw, rw⟩ := (hM n).surj c
    have r2 := (hM' n).sub _ _ _ _ rz (hF n w c rw)
    rw [hc, sub_self] at r2
    obtain ⟨y', hy', hDy'⟩ :=
      ((hM' n).zero _ _ (Deg_sub hz (Deg_tot Φ hw)) r2).1 rfl
    refine ⟨a' + w, y', Deg_add ha' hw, hy', ?_, ?_⟩
    · rw [D_add, hDa', hDw, add_zero]
    · rw [tot_add, hDy']
      abel
  · intro hT m
    constructor
    · intro c1 c2 h12
      obtain ⟨x1, hx1, hD1, r1⟩ := (hM m).surj c1
      obtain ⟨x2, hx2, hD2, r2⟩ := (hM m).surj c2
      have r12 := (hM m).sub _ _ _ _ r1 r2
      have r12' := (hM' m).sub _ _ _ _ (hF m _ _ r1) (hF m _ _ r2)
      rw [h12, sub_self, ← tot_sub] at r12'
      obtain ⟨y, hy, hDy⟩ :=
        ((hM' m).zero _ 0 (Deg_tot Φ (Deg_sub hx1 hx2)) r12').1 rfl
      obtain ⟨a', -, ha', -, hDa', -⟩ := hT (m - 1) (x1 - x2) y
        (by simpa using Deg_sub hx1 hx2) hy
        (by rw [sub_add_cancel, D_sub, hD1, hD2, sub_self]) hDy.symm
      exact sub_eq_zero.mp (((hM m).zero _ _ (Deg_sub hx1 hx2) r12).2 ⟨a', ha', hDa'⟩)
    · intro c'
      obtain ⟨y, hy, hDy, ry⟩ := (hM' m).surj c'
      obtain ⟨a', y', ha', hy', hDa', hyeq⟩ :=
        hT m 0 y Deg_zero hy (D_zero _) (by rw [tot_zero, hDy])
      obtain ⟨c, rc⟩ := (hM m).ex a' ha' hDa'
      refine ⟨c, ?_⟩
      have r := (hM' m).sub _ _ _ _ ry (hF m _ _ rc)
      have h0 : c' - F m c = 0 :=
        ((hM' m).zero _ _ (Deg_sub hy (Deg_tot Φ ha')) r).2 ⟨y', hy', by rw [hyeq]; abel⟩
      exact (sub_eq_zero.mp h0).symm
