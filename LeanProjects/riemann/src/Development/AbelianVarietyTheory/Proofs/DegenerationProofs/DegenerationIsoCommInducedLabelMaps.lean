import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData

theorem eq_zero_of_forall_pow_smul {X : Type} [AddCommGroup X] [Module.Free ℤ X] {n : ℕ} (hn : 1 < n) (v : X)
    (h : ∀ j : ℕ, ∃ z, v = n ^ j • z) : v = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  refine b.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  obtain ⟨z, hz⟩ := h (b.repr v i).natAbs
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (d := ((n ^ (b.repr v i).natAbs : ℕ) : ℤ)) ⟨b.repr z i, ?_⟩ ?_
  · have := congrArg (fun w => b.repr w i) hz
    simpa only [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] using this
  · rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self hn

theorem exists_qt_image {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ p' : N'.QT k, p'.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 p'.1.2 := by
  have r := (TateInh.homOfIso J).rel_img p.1.2
  have r₁ := r.pow k
  rw [N.mem_QT.1 p.2] at r₁
  have r₂ := (TateInh.homOfIso J).rel_io p.1.1.toAdd
  exact ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), (TateInh.homOfIso J).img p.1.2),
    ((TateInh.homOfIso J).rel_existsUnique _).unique r₁ r₂⟩, rfl, r⟩

theorem iso_comm_of_labels : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), 1 < n → Labels N EF ζ lab → Labels N' EF ζ' lab' → ∀ J : NumD.Iso N N', (∀ j (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j)), p'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 p'.1.2 → ∃ x, N.QEq (lab _ x) p ∧ N'.QEq (lab' _ x) p') → (∀ j (y : N.X), ∃ p : N.QT (n ^ j), p.1.1.toAdd = y) → ∀ (α : N.X →+ N.X) (α' : N'.X →+ N'.X) (gam : La → La), (∀ j x, ∃ z, (lab (n ^ j) (gam x)).1.1.toAdd = α (lab (n ^ j) x).1.1.toAdd + n ^ j • z) → (∀ j x, ∃ z, (lab' (n ^ j) (gam x)).1.1.toAdd = α' (lab' (n ^ j) x).1.1.toAdd + n ^ j • z) → ∀ y, J.e (α y) = α' (J.e y) := by
  intro C _ N N' La _ EF ζ ζ' lab lab' n hn hL hL' J hJ hs α α' gam ha ha' y
  have hk : ∀ j, 0 < n ^ j := fun j => pow_pos (by omega) j
  have key : ∀ j x, ∃ z, J.e (lab (n ^ j) x).1.1.toAdd = (lab' (n ^ j) x).1.1.toAdd + n ^ j • z := by
    intro j x
    obtain ⟨p', e, r⟩ := exists_qt_image J (lab (n ^ j) x)
    obtain ⟨x₀, h, h'⟩ := hJ j _ p' e r
    have h₁ := (hL'.2.1 _ (hk j) x₀ x).2 ((hL.2.1 _ (hk j) x₀ x).1 h)
    obtain ⟨z, hz, -⟩ := (N'.qEq_equivalence _).trans ((N'.qEq_equivalence _).symm h₁) h'
    exact ⟨z, e ▸ hz⟩
  refine sub_eq_zero.1 (eq_zero_of_forall_pow_smul hn _ fun j => ?_)
  obtain ⟨p, rfl⟩ := hs j y
  obtain ⟨x, z₀, h₀, -⟩ := hL.2.2.1 _ (hk j) p
  obtain ⟨z₁, h₁⟩ := ha j x
  obtain ⟨z₂, h₂⟩ := ha' j x
  obtain ⟨z₃, h₃⟩ := key j x
  obtain ⟨z₄, h₄⟩ := key j (gam x)
  refine ⟨J.e (α z₀) - J.e z₁ + z₄ + z₂ - α' z₃ - α' (J.e z₀), ?_⟩
  rw [h₁, h₂, map_add, map_nsmul] at h₄
  rw [h₀]
  simp only [map_add, map_nsmul, h₃]
  linear_combination (norm := module) h₄

end GlobalTheory.ModelData
