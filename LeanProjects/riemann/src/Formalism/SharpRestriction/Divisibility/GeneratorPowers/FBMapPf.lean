import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartTransportSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBCNab

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R') {d : ℕ}

def mp {n : ℕ} (a : Pt R n d) : Pt R' n d := fun i => map ψ (a i)

private theorem hs_lemma {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) :
    MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)

private theorem cz_ev_lemma_2 {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) (hf : constantCoeff f = 0) : constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hs_lemma a ha) (fun p => ha p.1 p.2) hf

theorem map_ev' {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R m d) :
    map ψ (ev a f) = ev (fun j => mp ψ (a j)) (map ψ f) := by
  unfold ev
  exact MvPowerSeries.map_subst (hs_lemma a ha) f

theorem mp_pt {n : ℕ} (j : Fin n) : mp ψ (pt R d j) = pt R' d j := by
  funext i
  simp only [mp, pt, MvPowerSeries.map_X]

theorem mp_zero {n : ℕ} : mp ψ (0 : Pt R n d) = 0 := by
  funext i
  simp [mp]

theorem mp_cons {n m : ℕ} (p : Pt R n d) (u : Fin m → Pt R n d) :
    (fun j => mp ψ (Matrix.vecCons p u j)) = Matrix.vecCons (mp ψ p) (fun j => mp ψ (u j)) := by
  funext j
  cases j using Fin.cases with
  | zero => rfl
  | succ k => rfl

theorem mp_nil {n : ℕ} : (fun j => mp ψ ((![] : Fin 0 → Pt R n d) j)) = ![] := by
  funext j
  exact j.elim0

theorem cz_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  simp only [pt, MvPowerSeries.constantCoeff_X]

theorem cz_add (F : Fin d → PS R 2 d) (hF : ∀ i, constantCoeff (F i) = 0) {n : ℕ} (a b : Pt R n d)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin d) :
    constantCoeff (addOf F a b i) = 0 := by
  have h : ∀ (j : Fin 2) (k : Fin d), constantCoeff ((![a, b] : Fin 2 → Pt R n d) j k) = 0 := by
    intro j k
    fin_cases j
    · exact ha k
    · exact hb k
  show constantCoeff (ev ![a, b] (F i)) = 0
  exact cz_ev_lemma_2 ![a, b] h (F i) (hF i)

theorem cz_comp1 (φ : Pt R 1 d) (hφ : ∀ i, constantCoeff (φ i) = 0) {n : ℕ} (a : Pt R n d)
    (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) : constantCoeff (comp1 φ a i) = 0 := by
  have h : ∀ (j : Fin 1) (k : Fin d), constantCoeff ((![a] : Fin 1 → Pt R n d) j k) = 0 := by
    intro j k
    fin_cases j
    exact ha k
  show constantCoeff (ev ![a] (φ i)) = 0
  exact cz_ev_lemma_2 ![a] h (φ i) (hφ i)

theorem mp_add (F : Fin d → PS R 2 d) {n : ℕ} (a b : Pt R n d)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    mp ψ (addOf F a b) = addOf (fun i => map ψ (F i)) (mp ψ a) (mp ψ b) := by
  funext i
  have h : ∀ (j : Fin 2) (k : Fin d), constantCoeff ((![a, b] : Fin 2 → Pt R n d) j k) = 0 := by
    intro j k
    fin_cases j
    · exact ha k
    · exact hb k
  show MvPowerSeries.map ψ (ev ![a, b] (F i)) = ev ![mp ψ a, mp ψ b] (MvPowerSeries.map ψ (F i))
  rw [map_ev' ψ _ h]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem mp_comp1 (φ : Pt R 1 d) {n : ℕ} (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) :
    mp ψ (comp1 φ a) = comp1 (mp ψ φ) (mp ψ a) := by
  funext i
  have h : ∀ (j : Fin 1) (k : Fin d), constantCoeff ((![a] : Fin 1 → Pt R n d) j k) = 0 := by
    intro j k
    fin_cases j
    exact ha k
  show MvPowerSeries.map ψ (ev ![a] (φ i)) = ev ![mp ψ a] (MvPowerSeries.map ψ (φ i))
  rw [map_ev' ψ _ h]
  congr 1
  funext j
  fin_cases j
  rfl

def mapG (G : FGLaw R d) : FGLaw R' d where
  F := fun i => map ψ (G.F i)
  const := fun i => by rw [constantCoeff_map, G.const i, map_zero]
  unit := fun i => by
    have h := congrArg (map ψ) (G.unit i)
    rw [map_ev' ψ _ (by intro j k; fin_cases j <;> simp [cz_pt]), mp_cons, mp_cons, mp_nil, mp_zero, mp_pt,
      map_X] at h
    exact h
  comm := fun i => by
    have h := congrArg (map ψ) (G.comm i)
    rw [map_ev' ψ _ (by intro j k; fin_cases j <;> simp [cz_pt]), mp_cons, mp_cons, mp_nil, mp_pt, mp_pt] at h
    exact h
  assoc := fun i => by
    have h := G.assoc i
    change ev ![addOf G.F (pt R d 0) (pt R d 1), pt R d 2] (G.F i) =
      ev ![pt R d 0, addOf G.F (pt R d 1) (pt R d 2)] (G.F i) at h
    have h2 := congrArg (map ψ) h
    rw [map_ev' ψ _ (by intro j k; fin_cases j <;> simp [cz_pt, cz_add _ G.const]),
      map_ev' ψ _ (by intro j k; fin_cases j <;> simp [cz_pt, cz_add _ G.const]),
      mp_cons, mp_cons, mp_nil, mp_cons, mp_cons, mp_nil, mp_add ψ _ _ _ (cz_pt _) (cz_pt _),
      mp_add ψ _ _ _ (cz_pt _) (cz_pt _), mp_pt, mp_pt, mp_pt] at h2
    exact h2

def mapA {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) : OAct O (mapG ψ G) where
  act := fun a => mp ψ (A.act a)
  const := fun a i => by
    show constantCoeff (map ψ (A.act a i)) = 0
    rw [constantCoeff_map, A.const a i, map_zero]
  hom := fun a => by
    have h := congrArg (mp ψ) (A.hom a)
    simp only [FGLaw.add] at h
    rw [mp_comp1 ψ _ _ (cz_add _ G.const _ _ (cz_pt _) (cz_pt _)), mp_add ψ _ _ _ (cz_pt _) (cz_pt _),
      mp_add ψ _ _ _ (cz_comp1 _ (A.const a) _ (cz_pt _)) (cz_comp1 _ (A.const a) _ (cz_pt _)),
      mp_comp1 ψ _ _ (cz_pt _), mp_comp1 ψ _ _ (cz_pt _), mp_pt, mp_pt] at h
    exact h
  add_act := fun a b => by
    have h := congrArg (mp ψ) (A.add_act a b)
    simp only [FGLaw.add] at h
    rw [mp_add ψ _ _ _ (A.const a) (A.const b)] at h
    exact h
  mul_act := fun a b => by
    have h := congrArg (mp ψ) (A.mul_act a b)
    rw [mp_comp1 ψ _ _ (A.const b)] at h
    exact h
  one_act := by
    have h := congrArg (mp ψ) A.one_act
    rw [mp_pt] at h
    exact h

section FB

variable {O : Type} [CommRing O] [StarRing O] (B : FB R d O)

local macro "fbm" : tactic => `(tactic| (simp only [map_mul, map_one, FGLaw.add, map_ev', mp_cons, mp_nil, mp_pt, mp_zero,
    mp_add, mp_comp1, Fin.forall_fin_succ, IsEmpty.forall_iff, Matrix.cons_val_zero, Matrix.cons_val_succ, cz_pt,
    cz_add _ B.G.const, cz_comp1 _ (B.A.const _), map_zero, Pi.zero_apply, implies_true, and_self, forall_const, true_and]
    at *))

set_option maxHeartbeats 1000000 in

def mapFB : FB R' d O where
  G := mapG ψ B.G
  A := mapA ψ B.A
  ph1 := map ψ B.ph1
  ph2 := map ψ B.ph2
  sy := map ψ B.sy
  ad := fun a => map ψ (B.ad a)
  cocycleLeft_zero_fst := by have h := congrArg (map ψ) B.cocycleLeft_zero_fst; fbm; exact h
  cocycleLeft_zero_snd := by have h := congrArg (map ψ) B.cocycleLeft_zero_snd; fbm; exact h
  cocycleLeft_zero_thd := by have h := congrArg (map ψ) B.cocycleLeft_zero_thd; fbm; exact h
  cocycleRight_zero_fst := by have h := congrArg (map ψ) B.cocycleRight_zero_fst; fbm; exact h
  cocycleRight_zero_snd := by have h := congrArg (map ψ) B.cocycleRight_zero_snd; fbm; exact h
  cocycleRight_zero_thd := by have h := congrArg (map ψ) B.cocycleRight_zero_thd; fbm; exact h
  symmetry_zero_fst := by have h := congrArg (map ψ) B.symmetry_zero_fst; fbm; exact h
  symmetry_zero_snd := by have h := congrArg (map ψ) B.symmetry_zero_snd; fbm; exact h
  adjoint_zero_fst := fun a => by have h := congrArg (map ψ) (B.adjoint_zero_fst a); fbm; exact h
  adjoint_zero_snd := fun a => by have h := congrArg (map ψ) (B.adjoint_zero_snd a); fbm; exact h
  cocycleLeft_assoc := by have h := congrArg (map ψ) B.cocycleLeft_assoc; fbm; exact h
  cocycleLeft_comm := by have h := congrArg (map ψ) B.cocycleLeft_comm; fbm; exact h
  cocycleRight_assoc := by have h := congrArg (map ψ) B.cocycleRight_assoc; fbm; exact h
  cocycleRight_comm := by have h := congrArg (map ψ) B.cocycleRight_comm; fbm; exact h
  interchange := by have h := congrArg (map ψ) B.interchange; fbm; exact h
  sy_inv := by have h := congrArg (map ψ) B.sy_inv; fbm; exact h
  sy_law := by have h := congrArg (map ψ) B.sy_law; fbm; exact h
  adjoint_compat_left := fun a => by have h := congrArg (map ψ) (B.adjoint_compat_left a); fbm; exact h
  adjoint_compat_right := fun a => by have h := congrArg (map ψ) (B.adjoint_compat_right a); fbm; exact h
  ad_one := by show map ψ (B.ad 1) = 1; rw [B.ad_one, map_one]
  ad_mul := fun a b => by have h := congrArg (map ψ) (B.ad_mul a b); fbm; exact h
  ad_add := fun a b => by have h := congrArg (map ψ) (B.ad_add a b); fbm; exact h
  ad_sy := fun a => by have h := congrArg (map ψ) (B.ad_sy a); fbm; exact h

end FB

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

theorem fbMap_holds : FBMapSt := by
  intro R R' _ _ ψ d O _ _ B
  exact ⟨FBMap.mapFB ψ B, fun j => rfl, fun a j => rfl, rfl, rfl, rfl, fun a => rfl⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1
