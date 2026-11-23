import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

open Set Topology TopologicalSpace

namespace LateralTheory.E.CurveKrullDim

variable {X : Type} [TopologicalSpace X]

theorem two_le_dim (A B : IrreducibleCloseds X) (hAB : (A : Set X) ⊂ B) (hB : (B : Set X) ≠ univ)
    [IrreducibleSpace X] : (2 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let T : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have h1 : A < B := by
    rw [← SetLike.coe_ssubset_coe]; exact hAB
  have h2 : B < T := by
    rw [← SetLike.coe_ssubset_coe]; exact ssubset_univ_iff.mpr hB
  let l : LTSeries (IrreducibleCloseds X) := ⟨2, ![A, B, T], fun i => by
    fin_cases i
    · exact h1
    · exact h2⟩
  have hl : l.length = 2 := rfl
  unfold topologicalKrullDim
  exact Order.le_krullDim_iff.mpr ⟨l, hl⟩

theorem closed_of_ne_univ [IrreducibleSpace X] [T0Space X] (hd : topologicalKrullDim X ≤ 1) (z : X)
    (hz : closure ({z} : Set X) ≠ univ) : IsClosed ({z} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  by_contra hne
  have hyz : closure ({y} : Set X) ⊂ closure {z} := by
    refine ⟨closure_minimal (by simpa using hy) isClosed_closure, fun h => hne ?_⟩
    have h1 : z ⤳ y := specializes_iff_mem_closure.mpr hy
    have h2 : y ⤳ z := specializes_iff_mem_closure.mpr (h (subset_closure rfl))
    exact (h1.antisymm h2).eq.symm
  have := two_le_dim ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ hyz hz
  have h3 := this.trans hd
  norm_cast at h3

theorem finite_of_closed [IrreducibleSpace X] [T0Space X] [QuasiSober X] [NoetherianSpace X]
    (hd : topologicalKrullDim X ≤ 1) (Z : Set X) (hZ : IsClosed Z) (hne : Z ≠ univ) : Z.Finite := by
  have hpt : ∀ z ∈ Z, IsClosed ({z} : Set X) := fun z hz => closed_of_ne_univ hd z
    (fun h => hne (eq_univ_of_univ_subset (h ▸ closure_minimal (by simpa using hz) hZ)))
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := Z)
  have hsub : ∀ S ∈ irreducibleComponents Z, (Subtype.val '' S).Subsingleton := by
    intro S hS
    have hirr : IsIrreducible (Subtype.val '' S) := hS.1.image _ continuous_subtype_val.continuousOn
    obtain ⟨g, hg⟩ := QuasiSober.sober hirr.closure isClosed_closure
    have hgZ : g ∈ Z := closure_minimal (by rintro _ ⟨x, -, rfl⟩; exact x.2) hZ (hg.mem)
    have : closure (Subtype.val '' S) = {g} := by
      rw [← hg.def, (hpt g hgZ).closure_eq]
    intro a ha b hb
    have ha' := subset_closure ha; have hb' := subset_closure hb
    rw [this] at ha' hb'
    exact ha'.trans hb'.symm
  have : Z = ⋃ S ∈ irreducibleComponents Z, Subtype.val '' S := by
    ext x; constructor
    · intro hx
      have : (⟨x, hx⟩ : Z) ∈ ⋃₀ irreducibleComponents Z := by rw [sUnion_irreducibleComponents]; trivial
      obtain ⟨S, hS, hxS⟩ := this
      exact mem_iUnion₂.mpr ⟨S, hS, ⟨_, hxS, rfl⟩⟩
    · intro hx
      obtain ⟨S, -, y, -, rfl⟩ := mem_iUnion₂.mp hx
      exact y.2
  rw [this]
  exact hfin.biUnion fun S hS => (hsub S hS).finite

end LateralTheory.E.CurveKrullDim
