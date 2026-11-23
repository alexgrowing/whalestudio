import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCochainCoordinateExtension
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GrpMain

section
variable {R : Type} [CommRing R] {G : Type} [TopologicalSpace G] [AddCommGroup G]
  {M : Type w} [AddCommGroup M] [Module R M]

omit [TopologicalSpace G] in
theorem rho_comm (ρ : Multiplicative G →* (M →ₗ[R] M)) (g h : G) (x : M) :
    ρ (Multiplicative.ofAdd g) (ρ (Multiplicative.ofAdd h) x) =
      ρ (Multiplicative.ofAdd h) (ρ (Multiplicative.ofAdd g) x) := by
  rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]

def shiftBy [IsTopologicalAddGroup G] (v : G) (n : ℕ) : C(Fin (n + 1) → G, Fin (n + 1) → G) :=
  ⟨fun x j => x j - v, by fun_prop⟩

def tw [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (v : G) (n : ℕ) :
    (lcCos R G M).cx.X n →ₗ[R] (lcCos R G M).cx.X n where
  toFun f := LocallyConstant.map (ρ (Multiplicative.ofAdd v))
    (LocallyConstant.comap (shiftBy v n) f) - f
  map_add' f g := by
    refine LocallyConstant.ext fun x => ?_
    change ρ (Multiplicative.ofAdd v) (f _ + g _) - (f x + g x) =
      (ρ (Multiplicative.ofAdd v) (f _) - f x) + (ρ (Multiplicative.ofAdd v) (g _) - g x)
    rw [map_add]
    abel
  map_smul' c f := by
    refine LocallyConstant.ext fun x => ?_
    change ρ (Multiplicative.ofAdd v) (c • f _) - c • f x =
      c • (ρ (Multiplicative.ofAdd v) (f _) - f x)
    rw [map_smul, smul_sub]

theorem tw_apply [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (v : G) (n : ℕ)
    (f : (lcCos R G M).cx.X n) (x : Fin (n + 1) → G) :
    tw ρ v n f x = ρ (Multiplicative.ofAdd v) (f fun j => x j - v) - f x := rfl

theorem tw_mem [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (v : G)
    (n : ℕ) (f : (lcCos R G M).cx.X n) (hf : f ∈ eqv ρ S n) : tw ρ v n f ∈ eqv ρ S n := by
  intro g hg x
  have e : (fun j => (fun i => g + x i) j - v) = fun i => g + (fun j => x j - v) i := by
    funext i
    exact add_sub_assoc _ _ _
  rw [tw_apply, tw_apply, e, hf g hg, hf g hg, map_sub, rho_comm]

theorem tw_d [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (v : G) (n : ℕ)
    (f : (lcCos R G M).cx.X n) :
    (lcCos R G M).d n (tw ρ v n f) = tw ρ v (n + 1) ((lcCos R G M).d n f) := by
  refine LocallyConstant.ext fun x => ?_
  rw [tw_apply, lc_d_apply, lc_d_apply, lc_d_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tw_apply, map_zsmul, smul_sub]

def twHom [IsTopologicalAddGroup G] (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (v : G) :
    Cx.Hom (grpCx ρ S) (grpCx ρ S) (RingHom.id R) where
  f n := (tw ρ v n).restrict fun f hf => tw_mem ρ S v n f hf
  comm n x := Subtype.ext (tw_d ρ v n x.1)

def Res (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (D : Submodule R M) (t : R) : Prop :=
  (∀ y ∈ eqv ρ S 0, (lcCos R G M).d 0 y = 0 → ∃ x ∈ D, t • y = LocallyConstant.const _ x) ∧
  ∀ n, ∀ y ∈ eqv ρ S (n + 1), (lcCos R G M).d (n + 1) y = 0 →
    ∃ x ∈ eqv ρ S n, (lcCos R G M).d n x = t • y

def invS (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) : Submodule R M where
  carrier := {x | ∀ g ∈ S, ρ (Multiplicative.ofAdd g) x = x}
  add_mem' {a b} ha hb g hg := by rw [map_add, ha g hg, hb g hg]
  zero_mem' g _ := map_zero _
  smul_mem' c a ha g hg := by rw [map_smul, ha g hg]

def invB (ρ : Multiplicative G →* (M →ₗ[R] M)) (S : Set G) (v : G) : invS ρ S →ₗ[R] invS ρ S :=
  (ρ (Multiplicative.ofAdd v) - LinearMap.id).restrict fun x hx g hg => by
    change ρ (Multiplicative.ofAdd g) (ρ (Multiplicative.ofAdd v) x - x) =
      ρ (Multiplicative.ofAdd v) x - x
    rw [map_sub, rho_comm, hx g hg]

theorem Res.congr (ρ : Multiplicative G →* (M →ₗ[R] M)) {S S' : Set G} (D : Submodule R M) (t : R)
    (h : ∀ n, eqv ρ S n = eqv ρ S' n) (hr : Res ρ S D t) : Res ρ S' D t := by
  have e : eqv ρ S = eqv ρ S' := funext h
  unfold Res at hr ⊢
  rw [← e]
  exact hr

end

def expo (i : ℕ) : ℕ := 2 ^ i - 1

def idx {k : ℕ} (e : Fin k ≃ Fin k) (i : ℕ) : Set (Fin k) := {j | ∃ a : Fin k, (a : ℕ) < i ∧ e a = j}

abbrev gens (l : ℕ) [Fact l.Prime] {k : ℕ} (e : Fin k ≃ Fin k) (i : ℕ) : Set (Fin k → ℤ_[l]) :=
  (fun j => Pi.single j (1 : ℤ_[l])) '' idx e i

end GlobalTheory.CompanionTheory.GrpMain
