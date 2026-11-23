import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualEquivSymmApply

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}

def stabEquivW (hs : h.IsSymm) (hc : IsCompl U (orthK h U)) (N : Submodule (𝓞 K) ↥(orthK h U)) :
    stabFix h U (push (orthK h U) N) ≃ Formalism.ThetaLiftIndependence.autL (formOn h (orthK h U)) N where
  toFun g := ⟨restr g.2.1, restr_mem g.2.1, push_injective _ (by rw [← gmap_push g.2.1]; exact g.2.2)⟩
  invFun g := ⟨extId hc g.1, extId_mem hs hc g.2.1, by rw [gmap_extId_push hs hc g.2.1, g.2.2]⟩
  left_inv g := Subtype.ext (extId_restr hc g.2.1)
  right_inv g := Subtype.ext (restr_extId hs hc g.2.1)

theorem card_stab_push (hs : h.IsSymm) (hc : IsCompl U (orthK h U)) (N : Submodule (𝓞 K) ↥(orthK h U)) :
    Nat.card (stabFix h U (push (orthK h U) N)) = Nat.card (Formalism.ThetaLiftIndependence.autL (formOn h (orthK h U)) N) :=
  Nat.card_congr (stabEquivW hs hc N)

theorem sameGenusFix_push_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hc : IsCompl U (orthK h U)) (A B : Submodule (𝓞 K) ↥(orthK h U)) :
    SameGenusFix (F := F) h U (push (orthK h U) A) (push (orthK h U) B) ↔
      Formalism.HermitianLatticesTheory.SameGenus (formOn h (orthK h U)) A B := by
  rw [GoodGenusOrbits.sameGenus_iff (F := F) hK hF A B]
  constructor
  · intro H 𝔭
    obtain ⟨g, hg, e⟩ := H 𝔭.1 𝔭.2
    refine ⟨restr hg, restr_mem hg, push_injective _ ?_⟩
    rw [← gmap_push hg, push_locF _ 𝔭.2.isPrime, push_locF _ 𝔭.2.isPrime]
    exact e
  · intro H 𝔭 h𝔭
    obtain ⟨g, hg, e⟩ := H ⟨𝔭, h𝔭⟩
    refine ⟨extId hc g, extId_mem hs hc hg, ?_⟩
    rw [← push_locF _ h𝔭.isPrime, ← push_locF _ h𝔭.isPrime, gmap_extId_push hs hc hg]
    exact congrArg _ e

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
