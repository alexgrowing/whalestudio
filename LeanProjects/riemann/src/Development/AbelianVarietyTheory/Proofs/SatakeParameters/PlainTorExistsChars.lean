import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU.PlainChars

theorem exists_fin_enum {S : Type*} (t : Multiset S) {n : ℕ} (hn : Multiset.card t = n) :
    ∃ ξ : Fin n → S, Finset.univ.val.map ξ = t := by
  subst hn
  refine ⟨fun j => t.toList.get (Fin.cast (by simp) j), ?_⟩
  rw [Fin.univ_val_map]
  conv_rhs => rw [← Multiset.coe_toList t]
  congr 1
  apply List.ext_get (by simp)
  intro i h1 h2
  simp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_ofChar (x : IrrGL k) (hx : x.1 = 1) : ∃ θ hθ, x = IrrGL.ofChar θ hθ := by
  obtain ⟨n, c⟩ := x
  obtain rfl : n = 1 := hx
  obtain ⟨θ, hθ, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  exact ⟨θ, hθ, congrArg (Sigma.mk 1) (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨e⟩))⟩

end GlobalTheory.RoadU.PlainChars

theorem GlobalTheory.RoadU.plainTor_exists_chars : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL k), PlainTor x → ∃ (ξ : Fin x.1 → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport x.rep (chars ξ hξ) ∧ Unlinked (chars ξ hξ) := by
  intro k _ _ _ _ _ x ⟨s, hs, h1, hu⟩
  let S := {χ : kˣ →* ℂˣ // IsSmoothChar χ}
  let F : S → IrrGL k := fun χ => IrrGL.ofChar χ.1 χ.2
  obtain ⟨t, rfl⟩ : ∃ t : Multiset S, t.map F = s :=
    haveI : CanLift (IrrGL k) S F fun y => ∃ χ, F χ = y := ⟨fun _ hy => hy⟩
    (Multiset.canLift F (fun y => ∃ χ, F χ = y)).prf s fun y hy => by
      obtain ⟨χ, hχ, e⟩ := PlainChars.exists_eq_ofChar y (h1 y hy)
      exact ⟨⟨χ, hχ⟩, e.symm⟩
  have hcard : Multiset.card t = x.1 := by
    have h2 := hs.sum_fst
    rw [Multiset.map_map] at h2
    have h3 : t.map (Sigma.fst ∘ F) = Multiset.replicate (Multiset.card t) 1 :=
      Multiset.eq_replicate.2 ⟨by simp, fun b hb => by
        obtain ⟨χ, -, rfl⟩ := Multiset.mem_map.1 hb
        rfl⟩
    rw [h3, Multiset.sum_replicate, smul_eq_mul, mul_one, Fintype.card_fin] at h2
    exact h2
  obtain ⟨ξ, hξ⟩ := PlainChars.exists_fin_enum t hcard
  have hc : chars (fun j => (ξ j).1) (fun j => (ξ j).2) = t.map F := by
    rw [← hξ, Multiset.map_map]
    rfl
  exact ⟨fun j => (ξ j).1, fun j => (ξ j).2, hc ▸ hs, hc ▸ hu⟩
