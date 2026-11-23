import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.LatBCIdx

theorem relIndex_span_latBC : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)) (r : ℕ) (v : Fin r → Fin m → K), L.FG → IsFrame K L v →
    (Submodule.span (𝓞 K') (Set.range fun j i => algebraMap K K' (v j i))).toAddSubgroup.relIndex
        (latBC K' L).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup ^ Module.finrank K K' := by
  intro K K' _ _ _ _ _ m L r v hL hv
  let l : L →ₗ[𝓞 K] (Fin m → K') :=
    { toFun := fun x i => algebraMap K K' ((x : Fin m → K) i)
      map_add' := fun x y => by funext i; simp
      map_smul' := fun a x => by
        funext i
        show algebraMap K K' ((a : K) * (x : Fin m → K) i) = a • algebraMap K K' ((x : Fin m → K) i)
        rw [map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply (𝓞 K) K K'] }
  have hr : Set.range l = (fun w i => algebraMap K K' (w i)) '' (L : Set (Fin m → K)) := by
    ext y; simp [l]
  let eL : Fin r → L := fun k => ⟨v k, hv.1 k⟩
  have hsub : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.addSubgroupOf L.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup := by
    have : Submodule.span (𝓞 K) (Set.range v) = (Submodule.span (𝓞 K) (Set.range eL)).map L.subtype := by
      rw [Submodule.map_span, ← Set.range_comp]; rfl
    ext x
    rw [this]
    exact ⟨fun ⟨y, hy, h⟩ => (Subtype.ext h : y = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have hidx : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup =
      Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) := by
    rw [AddSubgroup.relIndex, hsub]; rfl
  have i1 := IsFrame.relIndex_ne_zero hL hv
  rw [hidx] at i1 ⊢
  haveI : Finite (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) := Nat.finite_of_card_ne_zero i1
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hL
  have hli : LinearIndependent K' fun k => l (eL k) :=
    linearIndependent_algebraMap_comp_iff.2 hv.2.1
  have hidx' := GlobalTheory.SlopeExt.relIndex_span (S := 𝓞 K') l eL (hli.restrict_scalars' (𝓞 K'))
    (Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : 𝓞 K)
    (fun x hx => by
      have h1 : ((Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : ℕ) : K) • (x : Fin m → K) = 0 := by
        have := congrArg Subtype.val hx
        rw [Nat.cast_smul_eq_nsmul] at this ⊢
        exact this
      exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 i1)))
    (fun x => by
      rw [Nat.cast_smul_eq_nsmul]
      exact (Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup.nsmul_index_mem x)
  rw [GlobalTheory.SlopeExt.card_tensor K K' (isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩),
    hr] at hidx'
  exact hidx'

end GlobalTheory.LatBCIdx
