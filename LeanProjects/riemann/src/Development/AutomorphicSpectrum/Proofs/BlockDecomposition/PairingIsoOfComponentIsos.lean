import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.Transfer

variable {K : Type} [Field K]

theorem exCls (C : Cx.{1} K) {n : ℕ} (c : C.H n) : ∃ (x : C.X n) (hx : C.d n x = 0), C.cls x hx = c := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨x, hx, rfl⟩

theorem sub_mem_of_cls_eq {C : Cx.{1} K} {n : ℕ} {x y : C.X n} {hx : C.d n x = 0} {hy : C.d n y = 0}
    (h : C.cls x hx = C.cls y hy) : x - y ∈ C.B n :=
  (Submodule.Quotient.eq ((C.B n).submoduleOf (C.Z n)) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)).1 h

theorem cls_eq_of_sub_mem {C : Cx.{1} K} {n : ℕ} {x y : C.X n} {hx : C.d n x = 0} {hy : C.d n y = 0}
    (h : x - y ∈ C.B n) : C.cls x hx = C.cls y hy :=
  (Submodule.Quotient.eq ((C.B n).submoduleOf (C.Z n)) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)).2 h

theorem mapH_cls_eq {C D : Cx.{1} K} (φ : Cx.Hom C D (RingHom.id K)) {n : ℕ} (x : C.X n) (hx : C.d n x = 0)
    (h : D.d n (φ.f n x) = 0) : φ.mapH n (C.cls x hx) = D.cls (φ.f n x) h := rfl

theorem d_map_cocycle {C D : Cx.{1} K} (φ : Cx.Hom C D (RingHom.id K)) {n : ℕ} {x : C.X n} (hx : C.d n x = 0) :
    D.d n (φ.f n x) = 0 := by
  rw [φ.comm, hx, map_zero]

theorem d_mu_cocycle {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x : A.X p} {y : B.X q}
    (hx : A.d p x = 0) (hy : B.d q y = 0) : M.d n (pr.μ h x y) = 0 := by
  rw [pr.leib, hx, hy]
  simp

theorem cls_mu_left {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x x' : A.X p} {y : B.X q}
    {hx : A.d p x = 0} {hx' : A.d p x' = 0} (hy : B.d q y = 0) {hz : M.d n (pr.μ h x y) = 0}
    {hz' : M.d n (pr.μ h x' y) = 0} (e : A.cls x hx = A.cls x' hx') :
    M.cls (pr.μ h x y) hz = M.cls (pr.μ h x' y) hz' := by
  apply cls_eq_of_sub_mem
  have hb := sub_mem_of_cls_eq e
  rw [← LinearMap.sub_apply, ← map_sub]
  cases p with
  | zero =>
    have h0 : x - x' = 0 := hb
    rw [h0, map_zero, LinearMap.zero_apply]
    exact zero_mem _
  | succ p =>
    obtain ⟨w, hw⟩ := hb
    obtain rfl : n = (p + q) + 1 := by omega
    change _ ∈ LinearMap.range (M.d (p + q))
    refine ⟨pr.μ rfl w y, ?_⟩
    rw [pr.leib, hw, hy]
    simp

theorem cls_mu_right {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x : A.X p} {y y' : B.X q}
    (hx : A.d p x = 0) {hy : B.d q y = 0} {hy' : B.d q y' = 0} {hz : M.d n (pr.μ h x y) = 0}
    {hz' : M.d n (pr.μ h x y') = 0} (e : B.cls y hy = B.cls y' hy') :
    M.cls (pr.μ h x y) hz = M.cls (pr.μ h x y') hz' := by
  apply cls_eq_of_sub_mem
  have hb := sub_mem_of_cls_eq e
  rw [← map_sub]
  cases q with
  | zero =>
    have h0 : y - y' = 0 := hb
    rw [h0, map_zero]
    exact zero_mem _
  | succ q =>
    obtain ⟨w, hw⟩ := hb
    obtain rfl : n = (p + q) + 1 := by omega
    change _ ∈ LinearMap.range (M.d (p + q))
    refine ⟨(-1 : ℤ) ^ p • pr.μ rfl x w, ?_⟩
    rw [map_zsmul, pr.leib, hw, hx]
    simp [smul_smul, ← mul_pow]

def sumCongr {I : Type} [DecidableEq I] {A B : I → Type 1} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module K (A i)] [∀ i, Module K (B i)] (e : ∀ i, A i ≃ₗ[K] B i) : (⨁ i, A i) ≃ₗ[K] ⨁ i, B i :=
  DFinsupp.mapRange.linearEquiv e

theorem sumCongr_lof {I : Type} [DecidableEq I] {A B : I → Type 1} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module K (A i)] [∀ i, Module K (B i)] (e : ∀ i, A i ≃ₗ[K] B i) (i : I) (x : A i) :
    sumCongr e (DirectSum.lof K I A i x) = DirectSum.lof K I B i (e i x) :=
  DFinsupp.mapRange_single (hf := fun i => map_zero (e i))

theorem kunE_iff : ∀ {K : Type} [Field K] {P P' Q Q' T T' : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (pr' : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P' a) (Q' a') (T' c)) (p : ∀ a, Cx.Hom (P a) (P' a) (RingHom.id K)) (f : ∀ a, Cx.Hom (Q a) (Q' a) (RingHom.id K)) (g : ∀ a, Cx.Hom (T a) (T' a) (RingHom.id K)), (∀ a n, Function.Bijective ((p a).mapH n)) → (∀ a n, Function.Bijective ((f a).mapH n)) → (∀ a n, Function.Bijective ((g a).mapH n)) → (∀ {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j), (g c).f n ((pr ha).μ h x y) = (pr' ha).μ h ((p a).f i x) ((f a').f j y)) → (KunE pr ↔ KunE pr') := by
  intro K _ P P' Q Q' T T' pr pr' p f g hp hf hg hc
  let eP : ∀ a n, (P a).H n ≃ₗ[K] (P' a).H n := fun a n => LinearEquiv.ofBijective ((p a).mapH n) (hp a n)
  let eQ : ∀ a n, (Q a).H n ≃ₗ[K] (Q' a).H n := fun a n => LinearEquiv.ofBijective ((f a).mapH n) (hf a n)
  let eT : ∀ a n, (T a).H n ≃ₗ[K] (T' a).H n := fun a n => LinearEquiv.ofBijective ((g a).mapH n) (hg a n)
  let eS : ∀ c n : ℕ, (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) ≃ₗ[K]
      ⨁ t : Idx c n, (P' t.a).H t.i ⊗[K] (Q' t.a').H t.j :=
    fun c n => sumCongr fun t => TensorProduct.congr (eP t.a t.i) (eQ t.a' t.j)
  have hS : ∀ (c n : ℕ) (t : Idx c n) (x : (P t.a).X t.i) (y : (Q t.a').X t.j) (hx : (P t.a).d t.i x = 0)
      (hy : (Q t.a').d t.j y = 0),
      eS c n (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t
        ((P t.a).cls x hx ⊗ₜ (Q t.a').cls y hy)) =
      DirectSum.lof K _ (fun t : Idx c n => (P' t.a).H t.i ⊗[K] (Q' t.a').H t.j) t
        ((P' t.a).cls ((p t.a).f t.i x) (d_map_cocycle _ hx) ⊗ₜ (Q' t.a').cls ((f t.a').f t.j y) (d_map_cocycle _ hy)) := by
    intro c n t x y hx hy
    exact sumCongr_lof _ t _
  have hG : ∀ {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j)
      (hz : (T c).d n ((pr ha).μ h x y) = 0) (hz' : (T' c).d n ((pr' ha).μ h ((p a).f i x) ((f a').f j y)) = 0),
      eT c n ((T c).cls ((pr ha).μ h x y) hz) = (T' c).cls ((pr' ha).μ h ((p a).f i x) ((f a').f j y)) hz' := by
    intro a a' c ha i j n h x y hz hz'
    have e0 := hc ha h x y
    change (T' c).cls ((g c).f n ((pr ha).μ h x y)) (d_map_cocycle _ hz) = _
    exact cls_eq_of_sub_mem (by rw [e0, sub_self]; exact zero_mem _)
  constructor
  · intro H c n
    obtain ⟨e, he⟩ := H c n
    refine ⟨(eS c n).symm ≪≫ₗ e ≪≫ₗ eT c n, ?_⟩
    intro t x y hx hy hz
    obtain ⟨x0, hx0, e1⟩ := exCls (P t.a) ((eP t.a t.i).symm ((P' t.a).cls x hx))
    obtain ⟨y0, hy0, e2⟩ := exCls (Q t.a') ((eQ t.a' t.j).symm ((Q' t.a').cls y hy))
    have e1' : (P' t.a).cls ((p t.a).f t.i x0) (d_map_cocycle _ hx0) = (P' t.a).cls x hx := by
      have := congrArg (eP t.a t.i) e1
      rwa [LinearEquiv.apply_symm_apply] at this
    have e2' : (Q' t.a').cls ((f t.a').f t.j y0) (d_map_cocycle _ hy0) = (Q' t.a').cls y hy := by
      have := congrArg (eQ t.a' t.j) e2
      rwa [LinearEquiv.apply_symm_apply] at this
    have hS' := hS c n t x0 y0 hx0 hy0
    rw [e1', e2'] at hS'
    have hz0 := d_mu_cocycle (pr t.ha) t.h hx0 hy0
    have hz1 := d_mu_cocycle (pr' t.ha) t.h (d_map_cocycle (p t.a) hx0) (d_map_cocycle (f t.a') hy0)
    have hz2 := d_mu_cocycle (pr' t.ha) t.h hx (d_map_cocycle (f t.a') hy0)
    simp only [LinearEquiv.trans_apply]
    rw [← hS', LinearEquiv.symm_apply_apply, he t x0 y0 hx0 hy0 hz0, hG t.ha t.h x0 y0 hz0 hz1,
      cls_mu_left (pr' t.ha) t.h (d_map_cocycle (f t.a') hy0) (hz' := hz2) e1',
      cls_mu_right (pr' t.ha) t.h hx (hz' := hz) e2']
  · intro H c n
    obtain ⟨e, he⟩ := H c n
    refine ⟨eS c n ≪≫ₗ e ≪≫ₗ (eT c n).symm, ?_⟩
    intro t x y hx hy hz
    have hz1 := d_mu_cocycle (pr' t.ha) t.h (d_map_cocycle (p t.a) hx) (d_map_cocycle (f t.a') hy)
    simp only [LinearEquiv.trans_apply]
    rw [hS c n t x y hx hy, he t _ _ _ _ hz1, ← hG t.ha t.h x y hz hz1, LinearEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.KunGlue.Transfer
