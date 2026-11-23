import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorDirectSumBasisEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftSumDifferentialCompatStatement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.Glue

variable {K : Type} [Field K]

abbrev Bi (C : Cx.{1} K) (i : ℕ) : Type 1 := Module.Basis.ofVectorSpaceIndex K (C.H i)

abbrev bas (C : Cx.{1} K) (i : ℕ) : Module.Basis (Bi C i) K (C.H i) := Module.Basis.ofVectorSpace K (C.H i)

def rep (C : Cx.{1} K) (i : ℕ) (β : Bi C i) : C.Z i :=
  (Submodule.Quotient.mk_surjective _ (bas C i β)).choose

theorem rep_cls (C : Cx.{1} K) (i : ℕ) (β : Bi C i) :
    C.cls (rep C i β).1 (rep C i β).2 = bas C i β :=
  (Submodule.Quotient.mk_surjective _ (bas C i β)).choose_spec

structure Tup (P : ℕ → Cx.{1} K) (c : ℕ) : Type 1 where
  a : ℕ
  a' : ℕ
  ha : a + a' = c
  i : ℕ
  β : Bi (P a) i

instance (P : ℕ → Cx.{1} K) (c : ℕ) : DecidableEq (Tup P c) := Classical.decEq _

def tupEquiv (P : ℕ → Cx.{1} K) (c n : ℕ) :
    {v : Tup P c × ℕ // v.2 + v.1.i = n} ≃ Σ t : Idx c n, Bi (P t.a) t.i where
  toFun v := ⟨⟨v.1.1.a, v.1.1.i, v.1.1.a', v.1.2, v.1.1.ha, by have := v.2; omega⟩, v.1.1.β⟩
  invFun u := ⟨(⟨u.1.a, u.1.a', u.1.ha, u.1.i, u.2⟩, u.1.j), by have := u.1.h; simp only; omega⟩
  left_inv := by rintro ⟨⟨⟨a, a', ha, i, β⟩, m⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨a, i, a', j, ha, h⟩, β⟩; rfl

theorem lof_cast {V : Type 1} [DecidableEq V] (W : V → Type 1) [∀ u, AddCommGroup (W u)] [∀ u, Module K (W u)]
    {v v' : V} (h : v = v') (x : W v) : DirectSum.lof K V W v x = DirectSum.lof K V W v' (h ▸ x) := by
  subst h; rfl

theorem reidx {V U : Type 1} [DecidableEq V] [DecidableEq U] (σ : V ≃ U) (W : U → Type 1)
    [∀ u, AddCommGroup (W u)] [∀ u, Module K (W u)] :
    ∃ r : (⨁ v, W (σ v)) ≃ₗ[K] ⨁ u, W u,
      ∀ v x, r (DirectSum.lof K V (fun v => W (σ v)) v x) = DirectSum.lof K U W (σ v) x := by
  let f : (⨁ v, W (σ v)) →ₗ[K] ⨁ u, W u :=
    DirectSum.toModule K V _ fun v => DirectSum.lof K U W (σ v)
  let g : (⨁ u, W u) →ₗ[K] ⨁ v, W (σ v) :=
    DirectSum.toModule K U _ fun u =>
      (DirectSum.lof K V (fun v => W (σ v)) (σ.symm u)).comp
        ((LinearEquiv.cast (R := K) (M := W) (σ.apply_symm_apply u).symm).toLinearMap)
  refine ⟨LinearEquiv.ofLinear f g ?_ ?_, fun v x => ?_⟩
  · refine DirectSum.linearMap_ext K fun u => LinearMap.ext fun x => ?_
    have key : ∀ (u' : U) (hu : u' = u) (hh : u = u'),
        DirectSum.lof K U W u' (LinearEquiv.cast (R := K) (M := W) hh x) = DirectSum.lof K U W u x := by
      rintro _ rfl hh
      rfl
    simp only [LinearMap.comp_apply, LinearMap.id_apply, f, g, DirectSum.toModule_lof, LinearEquiv.coe_coe]
    exact key _ (σ.apply_symm_apply u) _
  · refine DirectSum.linearMap_ext K fun v => LinearMap.ext fun x => ?_
    have key : ∀ (v' : V) (hv : v' = v) (hh : σ v = σ v'),
        DirectSum.lof K V (fun v => W (σ v)) v' (LinearEquiv.cast (R := K) (M := W) hh x) =
          DirectSum.lof K V (fun v => W (σ v)) v x := by
      rintro _ rfl hh
      rfl
    simp only [LinearMap.comp_apply, LinearMap.id_apply, f, g, DirectSum.toModule_lof, LinearEquiv.coe_coe]
    exact key _ (σ.symm_apply_apply v) _
  · simp only [LinearEquiv.ofLinear_apply, f, DirectSum.toModule_lof]

def KunC {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (c n : ℕ) : Prop :=
  ∃ e : (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) ≃ₗ[K] (T c).H n,
    ∀ (t : Idx c n) (x : (P t.a).X t.i) (y : (Q t.a').X t.j) (hx : (P t.a).d t.i x = 0) (hy : (Q t.a').d t.j y = 0)
      (hz : (T c).d n ((pr t.ha).μ t.h x y) = 0),
      e (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t ((P t.a).cls x hx ⊗ₜ (Q t.a').cls y hy)) =
        (T c).cls ((pr t.ha).μ t.h x y) hz

def MvC {I : Type 1} [DecidableEq I] (k : I → ℕ) (A : I → Cx.{1} K) (T : Cx.{1} K)
    (g : ∀ (u : I) {m n : ℕ}, m + k u = n → (A u).X m →ₗ[K] T.X n) (n : ℕ) : Prop :=
  ∃ e : (⨁ v : {v : I × ℕ // v.2 + k v.1 = n}, (A v.1.1).H v.1.2) ≃ₗ[K] T.H n,
    ∀ (v : {v : I × ℕ // v.2 + k v.1 = n}) (x : (A v.1.1).X v.1.2) (hx : (A v.1.1).d v.1.2 x = 0)
      (hz : T.d n (g v.1.1 v.2 x) = 0),
      e (DirectSum.lof K _ (fun v : {v : I × ℕ // v.2 + k v.1 = n} => (A v.1.1).H v.1.2) v ((A v.1.1).cls x hx)) =
        T.cls (g v.1.1 v.2 x) hz

def gmap {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (c : ℕ)
    (u : Tup P c) {m n : ℕ} (h : m + u.i = n) : (Q u.a').X m →ₗ[K] (T c).X n :=
  (pr u.ha).μ (show u.i + m = n by omega) (rep (P u.a) u.i u.β).1

theorem mu_closed {C D E : Cx.{1} K} (p : CxPairing C D E) {i j n : ℕ} (h : i + j = n) (x : C.X i) (y : D.X j)
    (hx : C.d i x = 0) (hy : D.d j y = 0) : E.d n (p.μ h x y) = 0 := by
  rw [p.leib, hx, hy]; simp

def sec (C : Cx.{1} K) (i : ℕ) : C.H i →ₗ[K] C.Z i := (bas C i).constr K (rep C i)

theorem sec_bas (C : Cx.{1} K) (i : ℕ) (β : Bi C i) : sec C i (bas C i β) = rep C i β :=
  (bas C i).constr_basis K _ _

theorem cls_sec (C : Cx.{1} K) (i : ℕ) (ξ : C.H i) : C.cls (sec C i ξ).1 (sec C i ξ).2 = ξ := by
  have : (Submodule.mkQ _ : C.Z i →ₗ[K] C.H i).comp (sec C i) = LinearMap.id := by
    refine (bas C i).ext fun β => ?_
    simp only [LinearMap.comp_apply, sec_bas, LinearMap.id_apply]
    exact rep_cls C i β
  exact LinearMap.congr_fun this ξ

def prodR {C D E : Cx.{1} K} (p : CxPairing C D E) {i j n : ℕ} (h : i + j = n) (y : D.X j) (hy : D.d j y = 0) :
    C.H i →ₗ[K] E.H n :=
  (Submodule.mkQ _ : E.Z n →ₗ[K] E.H n).comp
    (LinearMap.codRestrict (E.Z n)
      (((p.μ h).flip y).comp ((C.Z i).subtype.comp (sec C i)))
      (fun ξ => mu_closed p h _ y (sec C i ξ).2 hy))

theorem prodR_apply {C D E : Cx.{1} K} (p : CxPairing C D E) {i j n : ℕ} (h : i + j = n) (y : D.X j) (hy : D.d j y = 0)
    (ξ : C.H i) :
    prodR p h y hy ξ = E.cls (p.μ h (sec C i ξ).1 y) (mu_closed p h _ y (sec C i ξ).2 hy) := rfl

theorem prodR_cls {C D E : Cx.{1} K} (p : CxPairing C D E) {i j n : ℕ} (h : i + j = n) (x : C.X i) (hx : C.d i x = 0)
    (y : D.X j) (hy : D.d j y = 0) (hz : E.d n (p.μ h x y) = 0) :
    prodR p h y hy (C.cls x hx) = E.cls (p.μ h x y) hz := by
  rw [prodR_apply, ← CrystallineSemistableComparison.P.cxcup_cls p h _ y (sec C i _).2 hy, ← CrystallineSemistableComparison.P.cxcup_cls p h x y hx hy, cls_sec]

theorem kun_iff_mv {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (c n : ℕ) :
    KunC pr c n ↔ MvC (I := Tup P c) (fun u => u.i) (fun u => Q u.a') (T c) (fun u {m n} h => gmap pr c u h) n := by
  classical
  obtain ⟨e₁, he₁⟩ := GlobalTheory.T.tensor_direct_sum_basis_equiv (K := K) (J := Idx c n) (fun t => (P t.a).H t.i) (fun t => (Q t.a').H t.j)
    (fun t => Bi (P t.a) t.i) (fun t => bas (P t.a) t.i)
  obtain ⟨r, hr⟩ := reidx (K := K) (tupEquiv P c n) (fun u : (Σ t : Idx c n, Bi (P t.a) t.i) => (Q u.1.a').H u.1.j)
  constructor
  · rintro ⟨e, he⟩
    refine ⟨(r.trans e₁.symm).trans e, ?_⟩
    rintro ⟨⟨⟨a, a', ha, i, β⟩, m⟩, h⟩ x hx hz
    have h' : i + m = n := by simpa [add_comm] using h
    have step := he ⟨a, i, a', m, ha, h'⟩ (rep (P a) i β).1 x (rep (P a) i β).2 hx hz
    have e1 := he₁ ⟨a, i, a', m, ha, h'⟩ β ((Q a').cls x hx)
    have r1 := hr ⟨(⟨a, a', ha, i, β⟩, m), h⟩ ((Q a').cls x hx)
    simp only [LinearEquiv.trans_apply]
    refine Eq.trans ?_ step
    refine congrArg e ?_
    rw [rep_cls]
    refine Eq.trans (congrArg e₁.symm r1) ?_
    exact (LinearEquiv.symm_apply_eq _).2 e1.symm
  · rintro ⟨E, hE⟩
    refine ⟨(e₁.trans r.symm).trans E, ?_⟩
    rintro ⟨a, i, a', j, ha, h⟩ x y hx hy hz
    have h' : j + i = n := by omega
    let L : (P a).H i →ₗ[K] (T c).H n :=
      ((E.toLinearMap.comp r.symm.toLinearMap).comp e₁.toLinearMap).comp
        ((DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) ⟨a, i, a', j, ha, h⟩).comp
          ((TensorProduct.mk K _ _).flip ((Q a').cls y hy)))
    have hL : L = prodR (pr ha) h y hy := by
      refine (bas (P a) i).ext fun β => ?_
      have e1 := he₁ ⟨a, i, a', j, ha, h⟩ β ((Q a').cls y hy)
      have r1 := hr ⟨(⟨a, a', ha, i, β⟩, j), h'⟩ ((Q a').cls y hy)
      have hz' := mu_closed (pr ha) h _ y (rep (P a) i β).2 hy
      have E1 := hE ⟨(⟨a, a', ha, i, β⟩, j), h'⟩ y hy hz'
      have r2 := (LinearEquiv.symm_apply_eq r).2 r1.symm
      have hLb : L (bas (P a) i β) = E (r.symm (e₁ (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j)
          ⟨a, i, a', j, ha, h⟩ (bas (P a) i β ⊗ₜ (Q a').cls y hy)))) := rfl
      rw [hLb, e1]
      refine Eq.trans (congrArg E r2) (Eq.trans E1 ?_)
      rw [prodR_apply]
      simp only [sec_bas]
      rfl
    have := LinearMap.congr_fun hL ((P a).cls x hx)
    rw [prodR_cls (pr ha) h x hx y hy hz] at this
    exact this

end GlobalTheory.CompanionTheory.KunGlue.Glue

open GlobalTheory.CompanionTheory.KunGlue.Glue in
theorem GlobalTheory.CompanionTheory.KunGlue.kun_glue : MVBij → ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] (P : ℕ → Cx.{1} K) (Q T : ℕ → Sy.{1} K ι) (pr : ∀ (S : Finset ι) {a a' c : ℕ}, a + a' = c → CxPairing (P a) ((Q a').K S) ((T c).K S)), (∀ {S S' : Finset ι} (h : S ⊆ S') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : ((Q a').K S).X j), ((T c).res h).f n ((pr S ha).μ hn x y) = (pr S' ha).μ hn x (((Q a').res h).f j y)) → (∀ a, (Q a).Desc) → (∀ c, (T c).Desc) → (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => (Q a).K S) (T := fun c => (T c).K S) (fun {a a' c} ha => pr S ha)) → KunE (P := P) (Q := fun a => (Q a).K ∅) (T := fun c => (T c).K ∅) (fun {a a' c} ha => pr ∅ ha) := by
  intro hmv K _ ι _ _ P Q T pr hnat hQ hT hK c n
  have main := GlobalTheory.T.mvE_empty_of_mvE_nonempty hmv (K := K) (ι := ι) (I := Tup P c) (fun u => u.i) (fun u => (-1 : ℤˣ) ^ u.i)
    (fun u => Q u.a') (T c) (fun u S {m n} h => gmap (Q := fun a => (Q a).K S) (T := fun c => (T c).K S) (fun {a a' c} ha => pr S ha) c u h)
    ?_ ?_ (fun u => hQ _) (hT c)
    (fun S hS n => (kun_iff_mv (Q := fun a => (Q a).K S) (T := fun c => (T c).K S) (fun {a a' c} ha => pr S ha) c n).1 (hK S hS c n)) n
  · exact (kun_iff_mv (Q := fun a => (Q a).K ∅) (T := fun c => (T c).K ∅) (fun {a a' c} ha => pr ∅ ha) c n).2 main
  · intro u S m n h h' x
    simp only [gmap]
    rw [(pr S u.ha).leib, (rep (P u.a) u.i u.β).2]
    simp
  · intro u S S' hS m n h x
    exact hnat hS u.ha _ _ x
