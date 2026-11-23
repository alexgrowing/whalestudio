import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasselmanFirstPropertyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsDomMonoid
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedVectorZeroOfDualStatement

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem hecke_pow_kills_of_proj_eq_zero : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V),
    IsSmooth π → ∀ t : D.T, D.IsStrDom t → ∀ U : Module.End ℂ (fixed π D.J),
    PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U → ∀ v : fixed π D.J, D.proj π (v : V) = 0 →
    ∃ j : ℕ, (U ^ j) v = 0 := by
  intro G _ _ _ D V _ _ π hπ t ht U hU v hv

  have hdom : ∀ r : ℕ, D.IsDom (t ^ r) := by
    intro r
    induction r with
    | zero => simpa using (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).1
    | succ r ih =>
      rw [pow_succ]
      exact (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).2 _ _ ih ht.1

  have hecke : ∀ r : ℕ, PositivityTheory.Lbc.IsHeckeOpG π D.J ((t ^ r : D.T) : G) (U ^ r) := by
    intro r
    induction r with
    | zero =>
      intro w l _
      simp
    | succ r ih =>
      rw [pow_succ, pow_succ U]
      exact GlobalTheory.T.casselman_first_property G D V π hπ (t ^ r) t (hdom r) ht.1 _ _ ih hU

  have key : ∀ u ∈ twKer π D.N 1, ∃ R : ℕ, ∀ r ≥ R,
      ∀ l : Module.Dual ℂ V, (∀ x ∈ D.J, l ∘ₗ π x = l) → l (π ((t : G) ^ r) u) = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨n, w, rfl⟩ := hu
      obtain ⟨R, hR⟩ := ht.2.1 (n : G) n.2
      refine ⟨R, fun r hr l hl => ?_⟩
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
      have hmem : (t : G) ^ (R + j) * (n : G) * ((t : G) ^ (R + j))⁻¹ ∈ D.J ⊓ D.N := by
        have := (hdom j).1 _ hR
        convert this using 1
        simp only [Subgroup.coe_pow]
        rw [add_comm R j, pow_add]
        group
      have hx := hl _ hmem.1
      have hy := LinearMap.congr_fun hx (π ((t : G) ^ (R + j)) w)
      simp only [LinearMap.comp_apply] at hy
      have hz : π ((t : G) ^ (R + j) * (n : G) * ((t : G) ^ (R + j))⁻¹) (π ((t : G) ^ (R + j)) w)
          = π ((t : G) ^ (R + j)) (π (n : G) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [hz] at hy
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hy, sub_self]
    | zero => exact ⟨0, fun r _ l _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨A, hA⟩ := ha
      obtain ⟨B, hB⟩ := hb
      refine ⟨max A B, fun r hr l hl => ?_⟩
      rw [map_add, map_add, hA r (le_trans (le_max_left _ _) hr) l hl,
        hB r (le_trans (le_max_right _ _) hr) l hl, add_zero]
    | smul c a _ ha =>
      obtain ⟨A, hA⟩ := ha
      refine ⟨A, fun r hr l hl => ?_⟩
      rw [map_smul, map_smul, hA r hr l hl, smul_zero]
  obtain ⟨R, hR⟩ := key _ ((Submodule.Quotient.mk_eq_zero _).1 hv)
  refine ⟨R, ?_⟩
  have h0 : (((U ^ R) v : fixed π D.J) : V) = 0 := by
    refine GlobalTheory.T.fixed_vector_zero_of_dual G D.J D.isCompact_J V π hπ _ ((U ^ R) v).2 fun l hl => ?_
    rw [← hecke R v l hl, Subgroup.coe_pow]
    exact hR R le_rfl l hl
  exact Subtype.ext h0

end GlobalTheory.CompanionTheory.Cass
