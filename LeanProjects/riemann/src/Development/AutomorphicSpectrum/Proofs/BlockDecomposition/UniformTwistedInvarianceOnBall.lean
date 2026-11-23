import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir

noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chi_eq_on_box {ψ : AddChar k Circle} {c j : ℤ} (hc : IsTrivialOn ψ c) {n : ℕ}
    {a a' : Fin n → k} (h : ∀ i, a' i - a i ∈ valBall k (c - j))
    {x : Multiplicative (Fin n → k)} (hx : x ∈ box k n j) : chi k ψ a x = chi k ψ a' x := by
  have hmem : (a' - a) ⬝ᵥ x.toAdd ∈ valBall k c := by
    refine sum_mem fun i _ => ?_
    have := mul_mem_valBall (h i) (hx i)
    simpa using this
  have hsplit : a' ⬝ᵥ x.toAdd = a ⬝ᵥ x.toAdd + (a' - a) ⬝ᵥ x.toAdd := by
    rw [← add_dotProduct]
    simp
  rw [chi_apply, chi_apply, hsplit, AddChar.map_add_eq_mul, hc _ hmem, mul_one]

theorem twKer_chiOn_le {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (ψ : AddChar k Circle)
    {a a' : Fin n → k} {H H' : Subgroup (Multiplicative (Fin n → k))} (hH : H ≤ H')
    (h : ∀ x ∈ H, chi k ψ a x = chi k ψ a' x) :
    twKer ρ H (chiOn k ψ a H) ≤ twKer ρ H' (chiOn k ψ a' H') := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, w, rfl⟩
  refine Submodule.subset_span ⟨⟨x, hH x.2⟩, w, ?_⟩
  simp [h x x.2]

theorem exists_box_forall_chi (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (v : V)
    (M : ℤ)
    (hv : ∀ a : Fin n → k, ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (chiOn k ψ a (box k n j'))) :
    ∃ J : ℤ, ∀ J' ≤ J, ∀ a : Fin n → k, (∀ i, a i ∈ valBall k M) →
      v ∈ twKer ρ (box k n J') (chiOn k ψ a (box k n J')) := by
  classical
  obtain ⟨c, hc⟩ := exists_isTrivialOn ψ hψ
  choose j hj using hv
  let U : (Fin n → k) → Set (Fin n → k) := fun a =>
    (fun a' => a' - a) ⁻¹' Set.pi Set.univ fun _ => (valBall k (c - j a) : Set k)
  have hUopen : ∀ a, IsOpen (U a) := fun a =>
    (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valBall _).preimage
      (continuous_id.sub continuous_const)
  have hS : IsCompact (Set.pi Set.univ fun _ : Fin n => (valBall k M : Set k)) :=
    isCompact_univ_pi fun _ => isCompact_valBall M
  have hcover : (Set.pi Set.univ fun _ : Fin n => (valBall k M : Set k)) ⊆ ⋃ a, U a := by
    intro a _
    refine Set.mem_iUnion.2 ⟨a, fun i _ => ?_⟩
    simp
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover U hUopen hcover
  obtain ⟨J, hJ⟩ := (t.image j).bddBelow
  refine ⟨J, fun J' hJ' a' ha' => ?_⟩
  obtain ⟨a, hat, haU⟩ := Set.mem_iUnion₂.1 (ht (fun i _ => ha' i))
  have hle : J' ≤ j a := hJ'.trans (hJ (Finset.mem_coe.2 (Finset.mem_image_of_mem j hat)))
  exact twKer_chiOn_le ρ ψ (box_antitone k n hle)
    (fun x hx => chi_eq_on_box hc (fun i => haU i (Set.mem_univ i)) hx) (hj a (j a) le_rfl)

end GlobalTheory.CompanionTheory.MirFourier

end
