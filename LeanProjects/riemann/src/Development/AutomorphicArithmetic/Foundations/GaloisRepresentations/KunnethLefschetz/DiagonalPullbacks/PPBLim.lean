import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalPullbacks.ProjectiveBundleFormulaTorsion
import Development.EtaleCohomology.EtaleTrace.LRingPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.Di
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.Di.PBLimPf

open LRingPf

private theorem pi_bc {R A P : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)] [AddCommGroup P] [Module R P]
    (Ψ : (∀ j, M j) →ₗ[R] P) (hΨ : Function.Bijective Ψ) (φ : (∀ j, A ⊗[R] M j) →ₗ[A] A ⊗[R] P)
    (h : ∀ a : ∀ j, M j, φ (fun j => (1 : A) ⊗ₜ a j) = (1 : A) ⊗ₜ Ψ a) : Function.Bijective φ := by
  let e : (∀ j, M j) ≃ₗ[R] P := LinearEquiv.ofBijective Ψ hΨ
  let b : A ⊗[R] (∀ j, M j) ≃ₗ[A] A ⊗[R] P := LinearEquiv.baseChange R A _ _ e
  let p : A ⊗[R] (∀ j, M j) ≃ₗ[A] ∀ j, A ⊗[R] M j := TensorProduct.piRight R A A M
  have key : φ ∘ₗ p.toLinearMap = b.toLinearMap := by
    apply ext1
    intro x
    have hp : p ((1 : A) ⊗ₜ x) = fun j => (1 : A) ⊗ₜ x j := by
      funext j
      simp [p, TensorProduct.piRight_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hp, h]
    simp [b, e]
  have hφ : ∀ u, φ u = b (p.symm u) := by
    intro u
    have := LinearMap.congr_fun key (p.symm u)
    simpa using this
  have : (φ : (∀ j, A ⊗[R] M j) → A ⊗[R] P) = b ∘ p.symm := funext hφ
  rw [this]
  exact b.bijective.comp p.symm.bijective

variable {l : ℕ} [Fact l.Prime]

private def powL (hB : A11) {E : Scheme.{0}} (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0) :
    ∀ j : ℕ, Hl l (sch.obj E) (2 * (j : ℤ)) 0
  | 0 => z0 l hB E hl
  | j + 1 => cupL l (sch.obj E) (by push_cast; ring) hB (powL hB hl v j) v

private theorem powL_lvl (hB : A11) {E : Scheme.{0}} (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0) (j k : ℕ) :
    (powL hB hl v j).1 k = pow0 (l ^ k) (v.1 k) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h : 2 * (j : ℤ) + 2 = 2 * ((j + 1 : ℕ) : ℤ) := by push_cast; ring
    exact congrArg (fun t => cup0 (l ^ k) h t (v.1 k)) ih

private theorem power_zero_reduction_compat (hB : A11) {E : Scheme.{0}} (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0) (j k : ℕ) :
    red (l ^ (k + 1)) (l ^ k) _ _ 0 (pow0 (l ^ (k + 1)) (v.1 (k + 1)) j) = pow0 (l ^ k) (v.1 k) j := by
  rw [← powL_lvl hB hl, ← powL_lvl hB hl]
  exact (powL hB hl v j).2 k

private def Psi (hB : A11) {E Z : Scheme.{0}} (r : E ⟶ Z) (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0) (N : ℕ) (n : ℤ) :
    (∀ j : Fin N, Hl l (sch.obj Z) (n - 2 * ((j : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]] Hl l (sch.obj E) n 0 :=
  ∑ j : Fin N, ((cupL l (sch.obj E) (sub_add_cancel n (2 * ((j : ℕ) : ℤ))) hB).flip (powL hB hl v j)).comp
    ((pullHl l (sch.map r) _ 0).comp (LinearMap.proj j))

private theorem Psi_apply (hB : A11) {E Z : Scheme.{0}} (r : E ⟶ Z) (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0)
    (N : ℕ) (n : ℤ) (a : ∀ j : Fin N, Hl l (sch.obj Z) (n - 2 * ((j : ℕ) : ℤ)) 0) :
    Psi hB r hl v N n a = ∑ j : Fin N, cupL l (sch.obj E) (sub_add_cancel n (2 * ((j : ℕ) : ℤ))) hB
      (pullHl l (sch.map r) _ 0 (a j)) (powL hB hl v j) := by
  simp [Psi, LinearMap.sum_apply]

private theorem Psi_lvl (hB : A11) {E Z : Scheme.{0}} (r : E ⟶ Z) (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0)
    (N : ℕ) (n : ℤ) (a : ∀ j : Fin N, Hl l (sch.obj Z) (n - 2 * ((j : ℕ) : ℤ)) 0) (k : ℕ) :
    (Psi hB r hl v N n a).1 k = ∑ j : Fin N, (cup0 (l ^ k) (sub_add_cancel n _)
      (pull _ (sch.map r) _ _ (show Ht (l ^ k) _ _ 0 from (a j).1 k)) (pow0 (l ^ k) (v.1 k) j) : Ht (l ^ k) _ n 0) := by
  rw [Psi_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← powL_lvl hB hl]
  rfl

private theorem lvl_red (hB : A11) {E Z : Scheme.{0}} (r : E ⟶ Z) (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0)
    {m n : ℤ} (j : ℕ) (h : m + 2 * (j : ℤ) = n) (k : ℕ) (a : Ht (l ^ (k + 1)) (sch.obj Z) m 0) :
    red (l ^ (k + 1)) (l ^ k) _ n 0 (cup0 (l ^ (k + 1)) h (pull _ (sch.map r) _ _ a) (pow0 (l ^ (k + 1)) (v.1 (k + 1)) j)) =
      cup0 (l ^ k) h (pull _ (sch.map r) _ _ (red (l ^ (k + 1)) (l ^ k) _ m 0 a)) (pow0 (l ^ k) (v.1 k) j) := by
  have e := red_cc h hB (l ^ (k + 1)) (dvd_succ l k) (pull _ (sch.map r) _ _ a) (pow0 (l ^ (k + 1)) (v.1 (k + 1)) j)
  rw [power_zero_reduction_compat hB hl, ← pull_red] at e
  exact e

private theorem Psi_bij (hB : A11) {E Z : Scheme.{0}} (r : E ⟶ Z) (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0)
    (N : ℕ) (n : ℤ) (hv : ∀ k, ProjectiveBundleFormulaTorsion (l ^ k) N r (v.1 k)) : Function.Bijective (Psi hB r hl v N n) := by
  constructor
  · intro a b hab
    funext j
    refine Subtype.ext (funext fun k => ?_)
    have h := congrArg (fun y : Hl l (sch.obj E) n 0 => y.1 k) hab
    simp only [Psi_lvl] at h
    exact congrFun ((hv k n).1 h) j
  · intro y
    choose c hc using fun k => (hv k n).2 (y.1 k)
    have compat : ∀ k j, red (l ^ (k + 1)) (l ^ k) _ _ 0 (c (k + 1) j) = c k j := by
      intro k
      refine congrFun ((hv k n).1 ?_)
      refine Eq.trans ?_ (hc k).symm
      refine Eq.trans ?_ (y.2 k)
      rw [← hc (k + 1), map_sum]
      exact Finset.sum_congr rfl fun j _ => (lvl_red hB r hl v j _ k (c (k + 1) j)).symm
    refine ⟨fun j => ⟨fun k => c k j, fun k => compat k j⟩, Subtype.ext (funext fun k => ?_)⟩
    rw [Psi_lvl]
    exact hc k

private theorem powV_eq (hB : A11) {E : Scheme.{0}} (hl : IsUnit (l : Γ(E, ⊤))) (v : Hl l (sch.obj E) 2 0) (j : ℕ) :
    powV l (toV v) j = toV (powL hB hl v j) := by
  induction j with
  | zero => exact oneV_eq l hB E hl
  | succ j ih =>
    change cupV l E _ (powV l (toV v) j) (toV v) = _
    rw [ih, cupV_eq l hB, cupQ_tmul]
    rfl

end UpperTheory.Gal.KunnethLefschetz.Di.PBLimPf

open UpperTheory.Gal.KunnethLefschetz.Di.PBLimPf LRingPf in
theorem UpperTheory.Gal.KunnethLefschetz.Di.pBLim_holds :
    UpperTheory.Gal.KunnethLefschetz.Di.PBLim := by
  intro hI l _ _ N E Z r hl v hv n
  have hB := hI.a11
  have hE : IsUnit (l : Γ(E, ⊤)) := unit_pull l r hl
  let φ : (∀ j : Fin N, V l Z (n - 2 * ((j : ℕ) : ℤ))) →ₗ[ℚ_[l]] V l E n :=
    ∑ j : Fin N, ((cupV l E (sub_add_cancel n (2 * ((j : ℕ) : ℤ)))).flip (powV l (toV v) j)).comp
      ((pb l r _).comp (LinearMap.proj j))
  have hφ : ∀ a, φ a = ∑ j : Fin N, cupV l E (sub_add_cancel n _) (pb l r _ (a j)) (powV l (toV v) j) := by
    intro a
    simp [φ, LinearMap.sum_apply]
  have hb : Function.Bijective φ := by
    refine pi_bc (Psi hB r hE v N n) (Psi_bij hB r hE v N n hv) φ fun a => ?_
    rw [hφ, Psi_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [powV_eq hB hE, pb_tmul, cupV_eq l hB, cupQ_tmul]
  have : (fun a : ∀ j : Fin N, V l Z (n - 2 * ((j : ℕ) : ℤ)) =>
      ∑ j : Fin N, cupV l E (sub_add_cancel n _) (pb l r _ (a j)) (powV l (toV v) j)) = φ :=
    funext fun a => (hφ a).symm
  rw [this]
  exact hb
