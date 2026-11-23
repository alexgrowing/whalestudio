import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedComplexCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumComplexCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumSystemDescendsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedSystemDescendsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBOfSub
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.MvSum

variable {K : Type} [Field K]

def shIn (ς : ℤˣ) {k : ℕ} (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (x : C.X m) : (Sh ς k C).X n :=
  show ∀ m' : {m' : ℕ // m' + k = n}, C.X m'.1 from
    fun m' => (show m = m'.1 by have := m'.2; omega) ▸ x

theorem shIn_d (ς : ℤˣ) {k : ℕ} (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (x : C.X m) (hx : C.d m x = 0) :
    (Sh ς k C).d n (shIn ς C h x) = 0 := by
  funext ⟨m', h'⟩
  cases m' with
  | zero => rfl
  | succ m' =>
    obtain rfl : m' = m := by omega
    change (ς : ℤ) • C.d m' x = 0
    rw [hx, smul_zero]

section Psi

variable {k : ℕ} {C D : Cx.{1} K} (ς : ℤˣ) (g : ∀ {m n : ℕ}, m + k = n → C.X m →ₗ[K] D.X n)

def psi (n : ℕ) : (Sh ς k C).X n →ₗ[K] D.X n where
  toFun w := if h : k ≤ n then g (m := n - k) (by omega) (w ⟨n - k, by omega⟩) else 0
  map_add' x y := by
    split_ifs with h
    · exact map_add _ _ _
    · simp
  map_smul' r x := by
    split_ifs with h
    · exact map_smul _ _ _
    · simp

theorem psi_eq {m n : ℕ} (h : m + k = n) (w : (Sh ς k C).X n) : psi ς g n w = g h (w ⟨m, h⟩) := by
  obtain rfl : m = n - k := by omega
  have hk : k ≤ n := by omega
  simp only [psi, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hk]

theorem psi_zero {n : ℕ} (h : n < k) (w : (Sh ς k C).X n) : psi ς g n w = 0 := by
  have hk : ¬ k ≤ n := by omega
  simp only [psi, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hk]

theorem psi_comm
    (hg : ∀ {m n : ℕ} (h : m + k = n) (h' : m + 1 + k = n + 1) (x : C.X m),
      D.d n (g h x) = (ς : ℤ) • g h' (C.d m x))
    (n : ℕ) (w : (Sh ς k C).X n) : D.d n (psi ς g n w) = psi ς g (n + 1) ((Sh ς k C).d n w) := by
  by_cases h : k ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
    have h' : m + 1 + k = m + k + 1 := by omega
    rw [psi_eq ς g rfl, psi_eq ς g h', hg rfl h']
    change _ = g h' ((ς : ℤ) • C.d m (w ⟨m, _⟩))
    rw [map_zsmul]
  · rw [psi_zero ς g (by omega), map_zero]
    by_cases h2 : k = n + 1
    · have h0 : 0 + k = n + 1 := by omega
      rw [psi_eq ς g h0]
      change 0 = g h0 0
      rw [map_zero]
    · rw [psi_zero ς g (by omega)]

def shHom
    (hg : ∀ {m n : ℕ} (h : m + k = n) (h' : m + 1 + k = n + 1) (x : C.X m),
      D.d n (g h x) = (ς : ℤ) • g h' (C.d m x)) : Cx.Hom (Sh ς k C) D (RingHom.id K) where
  f n := psi ς g n
  comm n x := psi_comm ς g hg n x

end Psi

theorem psi_nat {k : ℕ} {C C' D D' : Cx.{1} K} (ς : ℤˣ) (g : ∀ {m n : ℕ}, m + k = n → C.X m →ₗ[K] D.X n)
    (g' : ∀ {m n : ℕ}, m + k = n → C'.X m →ₗ[K] D'.X n) (f : Cx.Hom C C' (RingHom.id K))
    (f' : Cx.Hom D D' (RingHom.id K))
    (hn : ∀ {m n : ℕ} (h : m + k = n) (x : C.X m), f'.f n (g h x) = g' h (f.f m x))
    (n : ℕ) (w : (Sh ς k C).X n) : psi ς g' n ((Sh.map ς k f).f n w) = f'.f n (psi ς g n w) := by
  by_cases h : k ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
    rw [psi_eq ς g rfl, psi_eq ς g' rfl, hn]
    rfl
  · rw [psi_zero ς g (by omega), psi_zero ς g' (by omega), map_zero]

section Sum

variable {I : Type 1} [DecidableEq I]

def sumHom {E : I → Cx.{1} K} {D : Cx.{1} K} (φ : ∀ i, Cx.Hom (E i) D (RingHom.id K)) :
    Cx.Hom (Dsum E) D (RingHom.id K) where
  f n := DirectSum.toModule K I _ fun i => (φ i).f n
  comm n x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change D.d n (DirectSum.toModule K I _ (fun i => (φ i).f n) (DirectSum.lof K I (fun i => (E i).X n) i x)) =
        DirectSum.toModule K I _ (fun i => (φ i).f (n + 1))
          (DirectSum.lmap (fun i => (E i).d n) (DirectSum.lof K I (fun i => (E i).X n) i x))
      rw [DirectSum.lmap_lof, DirectSum.toModule_lof, DirectSum.toModule_lof, (φ i).comm]
    | add x y hx hy => simp only [map_add, hx, hy]

theorem sumHom_lof {E : I → Cx.{1} K} {D : Cx.{1} K} (φ : ∀ i, Cx.Hom (E i) D (RingHom.id K)) (n : ℕ) (i : I)
    (x : (E i).X n) : (sumHom φ).f n (DirectSum.lof K I (fun i => (E i).X n) i x) = (φ i).f n x :=
  DirectSum.toModule_lof _ _ _

theorem sumHom_nat {E E' : I → Cx.{1} K} {D D' : Cx.{1} K} (φ : ∀ i, Cx.Hom (E i) D (RingHom.id K))
    (φ' : ∀ i, Cx.Hom (E' i) D' (RingHom.id K)) (a : ∀ i, Cx.Hom (E i) (E' i) (RingHom.id K))
    (b : Cx.Hom D D' (RingHom.id K)) (h : ∀ i n x, (φ' i).f n ((a i).f n x) = b.f n ((φ i).f n x)) (n : ℕ)
    (x : (Dsum E).X n) : (sumHom φ').f n ((Dsum.map a).f n x) = b.f n ((sumHom φ).f n x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    have e : (Dsum.map a).f n (DirectSum.lof K I (fun i => (E i).X n) i x) =
        DirectSum.lof K I (fun i => (E' i).X n) i ((a i).f n x) := DirectSum.lmap_lof _ _ _
    change (sumHom φ').f n ((Dsum.map a).f n (DirectSum.lof K I (fun i => (E i).X n) i x)) =
      b.f n ((sumHom φ).f n (DirectSum.lof K I (fun i => (E i).X n) i x))
    rw [e, sumHom_lof, sumHom_lof, h]
  | add x y hx hy => simp only [map_add, hx, hy]

def eSh (ς : ℤˣ) {k : ℕ} (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : C.H m ≃ₗ[K] (Sh ς k C).H n :=
  Classical.choose ((GlobalTheory.T.shifted_complex_cohomology ς k C n).2 m h)

theorem eSh_cls (ς : ℤˣ) {k : ℕ} (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n)
    (hy : (Sh ς k C).d n y = 0) (hy' : C.d m (y ⟨m, h⟩) = 0) :
    eSh ς C h (C.cls (y ⟨m, h⟩) hy') = (Sh ς k C).cls y hy :=
  Classical.choose_spec ((GlobalTheory.T.shifted_complex_cohomology ς k C n).2 m h) y hy hy'

variable (k : I → ℕ) (ς : I → ℤˣ) (C : I → Cx.{1} K) (n : ℕ)

abbrev Ix : Type 1 := {v : I × ℕ // v.2 + k v.1 = n}

def reF : (⨁ v : Ix k n, (C v.1.1).H v.1.2) →ₗ[K] ⨁ u, (Sh (ς u) (k u) (C u)).H n :=
  DirectSum.toModule K _ _ fun v =>
    (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).H n) v.1.1) ∘ₗ (eSh (ς v.1.1) (C v.1.1) v.2).toLinearMap

def reG : (⨁ u, (Sh (ς u) (k u) (C u)).H n) →ₗ[K] ⨁ v : Ix k n, (C v.1.1).H v.1.2 :=
  DirectSum.toModule K I _ fun u =>
    if h : k u ≤ n then
      (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) ⟨(u, n - k u), by change n - k u + k u = n; omega⟩) ∘ₗ
        (eSh (ς u) (C u) (m := n - k u) (n := n) (by omega)).symm.toLinearMap
    else 0

theorem reG_reF : reG k ς C n ∘ₗ reF k ς C n = LinearMap.id := by
  refine DirectSum.linearMap_ext K fun v => LinearMap.ext fun y => ?_
  obtain ⟨⟨u, m⟩, h⟩ := v
  have h' : m + k u = n := h
  obtain rfl : m = n - k u := by omega
  have hk : k u ≤ n := by omega
  simp only [reF, reG, LinearMap.comp_apply, DirectSum.toModule_lof, LinearEquiv.coe_coe, dif_pos hk,
    LinearEquiv.symm_apply_apply, LinearMap.id_apply]

theorem reF_reG : reF k ς C n ∘ₗ reG k ς C n = LinearMap.id := by
  refine DirectSum.linearMap_ext K fun u => LinearMap.ext fun y => ?_
  by_cases hk : k u ≤ n
  · simp only [reF, reG, LinearMap.comp_apply, DirectSum.toModule_lof, LinearEquiv.coe_coe, dif_pos hk,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · have : Subsingleton ((Sh (ς u) (k u) (C u)).H n) := (GlobalTheory.T.shifted_complex_cohomology (ς u) (k u) (C u) n).1 (by omega)
    rw [Subsingleton.elim y 0, map_zero, map_zero]

def reE : (⨁ v : Ix k n, (C v.1.1).H v.1.2) ≃ₗ[K] ⨁ u, (Sh (ς u) (k u) (C u)).H n :=
  LinearEquiv.ofLinear (reF k ς C n) (reG k ς C n) (reF_reG k ς C n) (reG_reF k ς C n)

theorem exists_P : ∃ P : (⨁ v : Ix k n, (C v.1.1).H v.1.2) ≃ₗ[K] (Dsum fun u => Sh (ς u) (k u) (C u)).H n,
    ∀ (v : Ix k n) (x : (C v.1.1).X v.1.2) (hx : (C v.1.1).d v.1.2 x = 0)
      (hw : (Dsum fun u => Sh (ς u) (k u) (C u)).d n
        (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).X n) v.1.1 (shIn (ς v.1.1) (C v.1.1) v.2 x)) = 0),
      P (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) v ((C v.1.1).cls x hx)) =
        (Dsum fun u => Sh (ς u) (k u) (C u)).cls
          (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).X n) v.1.1 (shIn (ς v.1.1) (C v.1.1) v.2 x)) hw := by
  obtain ⟨e1, he1⟩ := GlobalTheory.T.direct_sum_complex_cohomology (fun u => Sh (ς u) (k u) (C u)) n
  refine ⟨(reE k ς C n).trans e1, ?_⟩
  intro v x hx hw
  have hy := shIn_d (ς v.1.1) (C v.1.1) v.2 x hx
  rw [LinearEquiv.trans_apply]
  have h1 : reE k ς C n (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) v ((C v.1.1).cls x hx)) =
      DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).H n) v.1.1
        ((Sh (ς v.1.1) (k v.1.1) (C v.1.1)).cls (shIn (ς v.1.1) (C v.1.1) v.2 x) hy) := by
    change reF k ς C n _ = _
    rw [reF, DirectSum.toModule_lof]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← eSh_cls (ς v.1.1) (C v.1.1) v.2 _ hy hx]
    rfl
  rw [h1]
  exact he1 v.1.1 _ hy hw

variable {D : Cx.{1} K} (g : ∀ (u : I) {m n : ℕ}, m + k u = n → (C u).X m →ₗ[K] D.X n)
  (hg : ∀ (u : I) {m n : ℕ} (h : m + k u = n) (h' : m + 1 + k u = n + 1) (x : (C u).X m),
    D.d n (g u h x) = (ς u : ℤ) • g u h' ((C u).d m x))

include hg in
theorem g_cocycle (u : I) {m n : ℕ} (h : m + k u = n) (x : (C u).X m) (hx : (C u).d m x = 0) :
    D.d n (g u h x) = 0 := by
  rw [hg u h (by omega), hx, map_zero, smul_zero]

theorem bij_iff : Function.Bijective ((sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n) ↔
    ∃ e : (⨁ v : Ix k n, (C v.1.1).H v.1.2) ≃ₗ[K] D.H n,
      ∀ (v : Ix k n) (x : (C v.1.1).X v.1.2) (hx : (C v.1.1).d v.1.2 x = 0)
        (hz : D.d n (g v.1.1 v.2 x) = 0),
        e (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) v ((C v.1.1).cls x hx)) =
          D.cls (g v.1.1 v.2 x) hz := by
  obtain ⟨P, hP⟩ := exists_P k ς C n
  have key : ∀ (v : Ix k n) (x : (C v.1.1).X v.1.2) (hx : (C v.1.1).d v.1.2 x = 0)
      (hz : D.d n (g v.1.1 v.2 x) = 0),
      (sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n
        (P (DirectSum.lof K (Ix k n) (fun v => (C v.1.1).H v.1.2) v ((C v.1.1).cls x hx))) =
        D.cls (g v.1.1 v.2 x) hz := by
    intro v x hx hz
    have hw : (Dsum fun u => Sh (ς u) (k u) (C u)).d n
        (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).X n) v.1.1 (shIn (ς v.1.1) (C v.1.1) v.2 x)) = 0 := by
      change DirectSum.lmap _ _ = 0
      rw [DirectSum.lmap_lof, shIn_d _ _ _ _ hx, map_zero]
    have hf : (sumHom fun u => shHom (ς u) (g u) (hg u)).f n
        (DirectSum.lof K I (fun u => (Sh (ς u) (k u) (C u)).X n) v.1.1 (shIn (ς v.1.1) (C v.1.1) v.2 x)) =
        g v.1.1 v.2 x := by
      rw [sumHom_lof]
      exact psi_eq (ς v.1.1) (g v.1.1) v.2 _
    rw [hP v x hx hw, CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (by rw [hf]; exact hz)]
    exact GlobalTheory.CompanionTheory.ConeKillC.cls_congr _ hf _ _
  constructor
  · intro hb
    refine ⟨P.trans (LinearEquiv.ofBijective _ hb), fun v x hx hz => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply]
    exact key v x hx hz
  · rintro ⟨e, he⟩
    have hEq : ((sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n) ∘ₗ P.toLinearMap = e.toLinearMap := by
      refine DirectSum.linearMap_ext K fun v => LinearMap.ext fun y => ?_
      obtain ⟨x, hx, rfl⟩ := GlobalTheory.CompanionTheory.ConeKillC.cls_surj _ _ y
      have hz := g_cocycle k ς C g hg v.1.1 v.2 x hx
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [key v x hx hz, he v x hx hz]
    have hb : Function.Bijective (((sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n) ∘ P) := by
      have : (((sumHom fun u => shHom (ς u) (g u) (hg u)).mapH n) ∘ P) = e := by
        funext y
        exact LinearMap.congr_fun hEq y
      rw [this]
      exact e.bijective
    exact (Function.Bijective.of_comp_iff _ P.bijective).1 hb

end Sum

variable {ι : Type} [DecidableEq ι] {I : Type 1} [DecidableEq I]

def mvHom (k : I → ℕ) (ς : I → ℤˣ) (A : I → Sy.{1} K ι) (T : Sy.{1} K ι)
    (g : ∀ (u : I) (S : Finset ι) {m n : ℕ}, m + k u = n → ((A u).K S).X m →ₗ[K] (T.K S).X n)
    (hd : ∀ (u : I) (S : Finset ι) {m n : ℕ} (h : m + k u = n) (h' : m + 1 + k u = n + 1) (x : ((A u).K S).X m),
      (T.K S).d n (g u S h x) = (ς u : ℤ) • g u S h' (((A u).K S).d m x))
    (hn : ∀ (u : I) {S S' : Finset ι} (hS : S ⊆ S') {m n : ℕ} (h : m + k u = n) (x : ((A u).K S).X m),
      (T.res hS).f n (g u S h x) = g u S' h (((A u).res hS).f m x)) :
    (sumSy fun u => shSy (ς u) (k u) (A u)).Hom T where
  φ S := sumHom (E := fun u => Sh (ς u) (k u) ((A u).K S)) fun u => shHom (ς u) (g u S) (hd u S)
  nat {S S'} h n x :=
    sumHom_nat (E := fun u => Sh (ς u) (k u) ((A u).K S)) (E' := fun u => Sh (ς u) (k u) ((A u).K S'))
      (fun u => shHom (ς u) (g u S) (hd u S)) (fun u => shHom (ς u) (g u S') (hd u S'))
      (fun u => Sh.map (ς u) (k u) ((A u).res h)) (T.res h)
      (fun u n x => psi_nat (ς u) (g u S) (g u S') ((A u).res h) (T.res h) (fun h' x => hn u h h' x) n x) n x

theorem mvSum : MVBij → ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I] (k : I → ℕ) (ς : I → ℤˣ) (A : I → Sy.{1} K ι) (T : Sy.{1} K ι) (g : ∀ (u : I) (S : Finset ι) {m n : ℕ}, m + k u = n → ((A u).K S).X m →ₗ[K] (T.K S).X n), (∀ (u : I) (S : Finset ι) {m n : ℕ} (h : m + k u = n) (h' : m + 1 + k u = n + 1) (x : ((A u).K S).X m), (T.K S).d n (g u S h x) = (ς u : ℤ) • g u S h' (((A u).K S).d m x)) → (∀ (u : I) {S S' : Finset ι} (hS : S ⊆ S') {m n : ℕ} (h : m + k u = n) (x : ((A u).K S).X m), (T.res hS).f n (g u S h x) = g u S' h (((A u).res hS).f m x)) → (∀ u, (A u).Desc) → T.Desc → (∀ S : Finset ι, S.Nonempty → ∀ n, MvE k A T g S n) → ∀ n, MvE k A T g ∅ n := by
  intro hMV K _ ι _ _ I _ k ς A T g hd hn hA hT hE n
  have hiff : ∀ (S : Finset ι) (n : ℕ), Function.Bijective (((mvHom k ς A T g hd hn).φ S).mapH n) ↔ MvE k A T g S n :=
    fun S n => bij_iff k ς (fun u => (A u).K S) n (fun u => g u S) (fun u => hd u S)
  exact (hiff ∅ n).1 (hMV K ι _ T (mvHom k ς A T g hd hn)
    (GlobalTheory.T.direct_sum_system_descends _ fun u => GlobalTheory.T.shifted_system_descends _ _ _ (hA u)) hT (fun S hS n => (hiff S n).2 (hE S hS n)) n)

end GlobalTheory.CompanionTheory.KunGlue.MvSum
