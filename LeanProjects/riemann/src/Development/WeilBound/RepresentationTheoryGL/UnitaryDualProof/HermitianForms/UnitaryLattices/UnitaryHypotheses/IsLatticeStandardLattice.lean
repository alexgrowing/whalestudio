import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.UnipBLeColFixOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lat

variable (k) in

def lat0 (m : ℕ) : AddSubgroup (Fin (m + 1) → k) where
  carrier := {x | ∀ i, valuation k (x i) ≤ valuation k ((1 : kˣ) : k)}
  add_mem' := fun {a b} ha hb i => by
    show valuation k (a i + b i) ≤ _
    exact ((valuation k).map_add _ _).trans (max_le (ha i) (hb i))
  zero_mem' := fun i => by simp
  neg_mem' := fun {a} ha i => by
    show valuation k (-(a i)) ≤ _
    rw [Valuation.map_neg]
    exact ha i

theorem coe_standard_lattice (m : ℕ) : (lat0 k m : Set (Fin (m + 1) → k)) = Set.univ.pi fun _ => cball (1 : kˣ) := by
  ext x
  simp only [Set.mem_univ_pi, cball, Set.mem_setOf_eq]
  exact Iff.rfl

theorem isLattice_standard_lattice (m : ℕ) : IsLat (lat0 k m) := by
  unfold IsLat
  rw [coe_standard_lattice]
  exact ⟨isCompact_univ_pi fun _ => isCompact_cball _, isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball _⟩

theorem isLat_sup {m : ℕ} {A₁ A₂ : AddSubgroup (Fin (m + 1) → k)} (h1 : IsLat A₁) (h2 : IsLat A₂) :
    IsLat (A₁ ⊔ A₂) := by
  unfold IsLat at *
  rw [AddSubgroup.add_normal]
  exact ⟨h1.1.add h2.1, h2.2.add_left⟩

end Lat

section Transport

variable {ψ : AddChar k Circle} {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}

theorem kills_congr {a b : ℕ} (hab : a = b) {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (h : Kills ψ π a B) : Kills ψ π b B := by
  subst hab; exact h

theorem mirEq_congr {a b : ℕ} (hab : a = b) {ha : a + 1 ≤ N} {hb : b + 1 ≤ N} {s t : ℝ} (hst : s = t)
    {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (h : MirEq π a ha s B) : MirEq π b hb t B := by
  subst hab; subst hst; exact h

theorem lvl_congr {a b : ℕ} (hab : a = b) {ha : a + 2 ≤ N} {hb : b + 2 ≤ N} {s t : ℝ} (hst : s = t)
    {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (h : Lvl k ψ π a ha s B) : Lvl k ψ π b hb t B := by
  subst hab; subst hst; exact h

theorem isDens_smul {m : ℕ} {h : m + 2 ≤ N} {A₀ : AddSubgroup (Fin (m + 1) → k)} {B B' I C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (hB : IsDens ψ h π A₀ B B') (hI : IsDens ψ h π A₀ I C) (c : ℂ) (hIc : ∀ v w, I v w = c * B v w) :
    ∀ v w, C v w = c * B' v w := by
  intro v w
  obtain ⟨A₁, hA₁, -, hB1⟩ := hB v w
  obtain ⟨A₂, hA₂, -, hI2⟩ := hI v w
  have hL := isLat_sup hA₁ hA₂
  rw [hI2 _ hL le_sup_right, hB1 _ hL le_sup_left, hIc]
  ring

end Transport

section Chain

open Classical in

def chain (hUD : UDens k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : ℕ → (V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
  | 0 => B
  | d + 1 =>
    if h : ∃ hN : d + 2 ≤ N, Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) then
      Classical.choose (hUD ψ hψc hψ1 (N - 2 - d) N (by obtain ⟨hN, -⟩ := h; omega) V π hs (d : ℝ)
        (chain hUD hψc hψ1 π hs B d) h.2
        (lat0 k (N - 2 - d)) (isLattice_standard_lattice _))
    else 0

variable (hUD : UDens k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ} {V : Type}
  [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

theorem chain_zero : chain hUD hψc hψ1 π hs B 0 = B := rfl

theorem chain_succ (d : ℕ) (hN : d + 2 ≤ N)
    (hL : Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d)) :
    IsDens ψ (by omega : N - 2 - d + 2 ≤ N) π (lat0 k (N - 2 - d)) (chain hUD hψc hψ1 π hs B d)
        (chain hUD hψc hψ1 π hs B (d + 1)) ∧
      IsPsd (chain hUD hψc hψ1 π hs B (d + 1)) ∧ Kills ψ π (N - 2 - d + 1) (chain hUD hψc hψ1 π hs B (d + 1)) ∧
      MirEq π (N - 2 - d) (by omega) ((d : ℝ) + 1) (chain hUD hψc hψ1 π hs B (d + 1)) ∧
      (∀ v, chain hUD hψc hψ1 π hs B (d + 1) v v = 0 →
        v ∈ twKer π (derUnip k N (N - 2 - d + 1)) (lvlChar k ψ N (N - 2 - d + 1)) ⊔
          LinearMap.ker (chain hUD hψc hψ1 π hs B d)) := by
  have hh : ∃ hN : d + 2 ≤ N, Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) := ⟨hN, hL⟩
  simp only [chain, dif_pos hh]
  exact Classical.choose_spec (hUD ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ)
    (chain hUD hψc hψ1 π hs B d) hL (lat0 k (N - 2 - d)) (isLattice_standard_lattice _))

theorem isPsd_of_inv (hB : IsInvForm π B) : IsPsd B := by
  obtain ⟨h1, h2, -⟩ := hB
  unfold IsPsd
  refine ⟨h1, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · exact (h2 v hv).le

theorem chain_lvl (hB : IsInvForm π B) :
    ∀ d (hd : d + 2 ≤ N), Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d)
  | 0, hd => by
    refine ⟨isPsd_of_inv π B hB, ?_, ?_⟩
    · refine kills_congr (a := N) (by omega) ?_
      intro v hv w
      rw [twKer_derUnip_self ψ π] at hv
      rw [(Submodule.mem_bot ℂ).1 hv]
      simp
    · intro p _ v w
      simp [chain_zero, hB.2.2]
  | d + 1, hd => by
    obtain ⟨h1, h2, h3, h4, -⟩ := chain_succ hUD hψc hψ1 π hs B d (by omega) (chain_lvl hB d (by omega))
    exact ⟨h2, kills_congr (by omega) h3, mirEq_congr (by omega) (by push_cast; ring) h4⟩

end Chain

end PositivityTheory.RgUd.Form.U.Asm
