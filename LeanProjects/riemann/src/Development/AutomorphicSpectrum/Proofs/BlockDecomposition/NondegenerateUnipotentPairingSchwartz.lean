import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemTwKerPolyBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRepsSumEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
open GlobalTheory.CompanionTheory.MirFourier
open scoped Topology

namespace GlobalTheory.CompanionTheory.BZShell.Radical

section aux

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem uM_add_eq (d : ℕ) (x y : Fin d → k) : uM d (x + y) = uM d x * uM d y :=
  map_mul (unipIn k d) (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)

theorem uM_zero_eq (d : ℕ) : uM (k := k) d 0 = 1 := map_one (unipIn k d)

theorem exists_pow_mem (d : ℕ) (H : Subgroup (Multiplicative (Fin d → k)))
    (hH : IsOpen (H : Set (Multiplicative (Fin d → k)))) (x : Multiplicative (Fin d → k)) :
    ∃ n : ℕ, 0 < n ∧ x ^ n ∈ H := by
  obtain ⟨s, hs⟩ := exists_mem_polyBall x
  let P : Subgroup (Multiplicative (Fin d → k)) := polyBall (k := k) d s
  haveI : CompactSpace P := isCompact_iff_compactSpace.mp (isCompact_polyBall d s)
  let N : Subgroup P := H.subgroupOf P
  have hN : IsOpen (N : Set P) := hH.preimage continuous_subtype_val
  haveI : Finite (P ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (H := N) Subgroup.index_ne_zero_of_finite ⟨x, hs⟩
  exact ⟨n, hn, by simpa [N, Subgroup.mem_subgroupOf] using hmem⟩

def stabU {d : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Mir k d) W) (t : W) :
    Subgroup (Multiplicative (Fin d → k)) where
  carrier := {x | ρ (unipIn k d x) t = t}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul]
    simp

theorem isOpen_stabU {d : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Mir k d) W)
    (hρ : IsSmooth ρ) (t : W) : IsOpen (stabU ρ t : Set (Multiplicative (Fin d → k))) :=
  (hρ t).preimage (continuous_unipIn d)

def bump {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (s : kˣ) (a : V) : SchF k d V :=
  ⟨(FourierPi.box (Fin d) s).indicator fun _ => a,
    ((LocallyConstant.const _ a).indicator ⟨(FourierPi.isCompact_box s).isClosed, FourierPi.isOpen_box s⟩).isLocallyConstant,
    HasCompactSupport.intro (FourierPi.isCompact_box s) fun _ hx => Set.indicator_of_notMem hx _⟩

end aux

theorem false_of_translation_invariant : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ) (hd : 0 < d) (R R' : MRep k d) (hR' : IsSmooth R'.ρ) {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Nontrivial V]
    (B : R.V →ₗ[ℂ] R'.V →ₗ[ℂ] ℂ) (hB : ∀ x v v', B (R.ρ (uM d x) v) (R'.ρ (uM d x) v') = B v v')
    (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (ι : SchF k d V →ₗ[ℂ] R.V) (hι : Function.Injective ι) (hιs : ∀ x f, ι (shiftF x f) = R.ρ (uM d x) (ι f))
    (ι' : SchF k d V' →ₗ[ℂ] R'.V) (hιs' : ∀ x f, ι' (shiftF x f) = R'.ρ (uM d x) (ι' f))
    (hr : ∀ x v, R'.ρ (uM d x) v - v ∈ LinearMap.range ι')
    (hC : ∀ f f' x, B (ι f) (ι' (shiftF x f')) = B (ι f) (ι' f')),
    False := by
  intro k _ _ _ _ d hd R R' hR' V V' _ _ _ _ _ B hB hn ι hι hιs ι' hιs' hr hC
  obtain ⟨a, ha⟩ := exists_ne (0 : V)
  let i₀ : Fin d := ⟨0, hd⟩
  have hU : {y : k | y ≠ 1} ∈ 𝓝 (0 : k) := isOpen_ne.mem_nhds (zero_ne_one (α := k))
  obtain ⟨s, hs⟩ := exists_cball_subset hU
  let x₀ : Fin d → k := Pi.single i₀ 1
  let f₀ : SchF k d V := bump d s a
  have hx₀ : x₀ ∉ FourierPi.box (Fin d) s := fun h => hs (h i₀ trivial) (by simp [x₀])
  have h0 : (0 : Fin d → k) ∈ FourierPi.box (Fin d) s := fun i _ => by simp [cball]
  have hne : shiftF x₀ f₀ - f₀ ≠ 0 := by
    intro h
    have h1 := congrArg (fun f : SchF k d V => f.1 0) h
    have h2 : (shiftF x₀ f₀).1 0 = 0 := by
      rw [shiftF_apply, zero_add]
      exact Set.indicator_of_notMem (f := fun _ => a) hx₀
    have h3 : f₀.1 0 = a := Set.indicator_of_mem (f := fun _ => a) h0
    have h4 : (shiftF x₀ f₀).1 0 - f₀.1 0 = 0 := h1
    rw [h2, h3, zero_sub, neg_eq_zero] at h4
    exact ha h4
  have hv : ι (shiftF x₀ f₀ - f₀) ≠ 0 := fun h => hne (hι (h.trans (map_zero ι).symm))
  obtain ⟨t, ht⟩ := hn _ hv
  apply ht
  have hinv : ∀ y z : Fin d → k, R'.ρ (uM d y) (R'.ρ (uM d z) t) = R'.ρ (uM d (y + z)) t := by
    intro y z
    rw [uM_add_eq, map_mul, Module.End.mul_apply]
  set w : R'.V := R'.ρ (uM d (-x₀)) t - t with hw
  have hBv : B (ι (shiftF x₀ f₀ - f₀)) t = B (ι f₀) w := by
    have h1 := hB x₀ (ι f₀) (R'.ρ (uM d (-x₀)) t)
    rw [hinv, add_neg_cancel, uM_zero_eq, map_one, Module.End.one_apply] at h1
    rw [map_sub, hιs, map_sub, LinearMap.sub_apply, hw, map_sub, h1]
  rw [hBv]
  obtain ⟨f', hf'⟩ := hr (-x₀) t
  have step : ∀ y : Fin d → k, B (ι f₀) (R'.ρ (uM d (y + -x₀)) t) - B (ι f₀) (R'.ρ (uM d y) t) = B (ι f₀) w := by
    intro y
    have hf2 : ι' f' = w := hf'
    have h1 : B (ι f₀) (R'.ρ (uM d y) w) = B (ι f₀) w := by
      rw [← hf2, ← hιs', hC]
    rw [← h1, hw, map_sub, map_sub, hinv]
  have hall : ∀ i : ℕ, B (ι f₀) (R'.ρ (uM d (i • x₀)) t) = B (ι f₀) t - (i : ℂ) * B (ι f₀) w := by
    intro i
    induction i with
    | zero => simp [uM_zero_eq]
    | succ i ih =>
      have h1 := step ((i + 1) • x₀)
      have h2 : (i + 1) • x₀ + -x₀ = i • x₀ := by
        rw [succ_nsmul]; abel
      rw [h2, ih] at h1
      push_cast
      linear_combination -h1
  obtain ⟨n, hn0, hnm⟩ := exists_pow_mem d (stabU R'.ρ t) (isOpen_stabU R'.ρ hR' t) (Multiplicative.ofAdd x₀)
  have hfix : R'.ρ (uM d (n • x₀)) t = t := hnm
  have h1 := hall n
  rw [hfix] at h1
  have h2 : (n : ℂ) * B (ι f₀) w = 0 := by linear_combination h1
  exact (mul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 hn0.ne')

end GlobalTheory.CompanionTheory.BZShell.Radical

end
