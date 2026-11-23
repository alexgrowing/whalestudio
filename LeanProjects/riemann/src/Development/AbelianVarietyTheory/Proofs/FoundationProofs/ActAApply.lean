import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.FinWeil

def sgO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E := MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj

theorem coe_sgO (D : D7) (r : 𝓞 D.host.E) : ((sgO D r : 𝓞 D.host.E) : D.host.E) = D.host.conj (r : D.host.E) := rfl

abbrev XA (D : D7) (N N' : ℕ) : Type := Matrix (Fin N') (Fin N) (AE D)

theorem smul_AE (D : D7) (r : 𝓞 D.host.E) (y : AE D) : r • y = inc D (r : D.host.E) * y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.smul_tmul']
    simp [inc, Formalism.UG.inclE, Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

theorem ihE_mul (D : D7) (cc : Ideal (𝓞 D.host.K)) {s t : AE D} (hs : s ∈ OhE D) (ht : t ∈ IhE D cc) : s * t ∈ IhE D cc := by
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, s', hs', rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, s * s', mul_mem hs hs', by ring⟩
  | zero => simpa using zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

def latA (D : D7) (cc : Ideal (𝓞 D.host.K)) (N N' : ℕ) : Submodule (𝓞 D.host.E) (XA D N N') where
  carrier := {ζ | ∀ i j, ζ i j ∈ IhE D cc}
  add_mem' := fun ha hb i j => add_mem (ha i j) (hb i j)
  zero_mem' := fun _ _ => zero_mem _
  smul_mem' := fun r ζ h i j => by
    rw [Matrix.smul_apply, smul_AE]
    exact ihE_mul D cc ((AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨r, rfl⟩) (h i j)

theorem mem_latA {D : D7} {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} {ζ : XA D N N'} :
    ζ ∈ latA D cc N N' ↔ ∀ i j, ζ i j ∈ IhE D cc := Iff.rfl

def actA (D : D7) (N N' : ℕ) : GA D N × GA D N' →* Module.End (𝓞 D.host.E) (XA D N N') where
  toFun u :=
    { toFun := fun ζ => ((u.2 : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * ζ *
        (((u.1 : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
      map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r x => by
        have h : ∀ {a b : ℕ} (y : Matrix (Fin a) (Fin b) (AE D)), r • y = inc D (r : D.host.E) • y := fun y => by
          ext i j
          rw [Matrix.smul_apply, Matrix.smul_apply, smul_AE, smul_eq_mul]
        rw [RingHom.id_apply, h, h, Matrix.mul_smul, Matrix.smul_mul] }
  map_one' := by
    ext1 ζ
    simp
  map_mul' u v := by
    ext1 ζ
    simp [Matrix.mul_assoc]

theorem actA_apply {D : D7} {N N' : ℕ} (g : GA D N) (g' : GA D N') (ζ : XA D N N') :
    actA D N N' (g, g') ζ = ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * ζ *
      (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := rfl

theorem wd_add {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') (F G : VC D N N' → ℂ) :
    Wd D T x (F + G) = Wd D T x F + Wd D T x G := by
  funext z
  simp only [Wd, U, Pi.add_apply]
  ring

theorem wd_smul {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') (c : ℂ) (F : VC D N N' → ℂ) :
    Wd D T x (c • F) = c • Wd D T x F := by
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul]
  ring

def TTs (D : D7) (T : Tor D) (N N' : ℕ) : Submodule ℂ (VC D N N' → ℂ) where
  carrier := TT D T N N'
  add_mem' := by
    rintro F G ⟨hF, m, hm, h⟩ ⟨hG, n, hn, h'⟩
    refine ⟨hF.add hG, m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
    rw [wd_add]
    congr 1
    · rw [mul_smul]; exact h _ (AddSubgroup.nsmul_mem _ hx n)
    · rw [mul_comm, mul_smul]; exact h' _ (AddSubgroup.nsmul_mem _ hx m)
  zero_mem' := ⟨differentiable_const _, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩
  smul_mem' := by
    rintro c F ⟨hF, m, hm, h⟩
    exact ⟨hF.const_smul c, m, hm, fun x hx => by rw [wd_smul, h x hx]⟩

def psi0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : D.host.E) : ℂ :=
  ee (-(‖δ‖ ^ 2 / area (lamOf D cc δ) * (∑ τ, embT D τ a).im))

def IsPsi (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (ψ : AE D → ℂ) : Prop :=
  (∀ x y, ψ (x + y) = ψ x * ψ y) ∧ ψ 0 = 1 ∧ (∀ a, ψ (inc D a) = psi0 D cc δ a) ∧ (∀ y, ψ (y + sgA D y) = 1) ∧
    ∃ m : ℕ, 0 < m ∧ ∀ s ∈ OhE D, ψ ((m : AE D) * s) = 1

def gamA {D : D7} (ψ : AE D → ℂ) {N N' : ℕ} (ζ η : XA D N N') : ℂ := ψ (∑ i, ∑ j, ζ i j * sgA D (η i j))

def IsModel (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (w : 𝓞 D.host.E) (γ : XA D N N' → XA D N N' → ℂ)
    (WA : XA D N N' → TTs D (tor0 D cc δ) N N' →ₗ[ℂ] TTs D (tor0 D cc δ) N N') : Prop :=
  IsHeis (sgO D) w γ WA ∧ SelfDual γ (latA D cc N N') ∧
  (∀ u ζ η, γ (actA D N N' u ζ) (actA D N N' u η) = γ ζ η) ∧
  (∀ (z : Matrix (Fin N') (Fin N) D.host.E) (F : TTs D (tor0 D cc δ) N N'),
    (WA (z.map (inc D)) F : VC D N N' → ℂ) = Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F) ∧
  ∀ ζ F, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ latA D cc N N', WA (ζ + m • a) F = WA ζ F

end GlobalTheory.FinWeil
