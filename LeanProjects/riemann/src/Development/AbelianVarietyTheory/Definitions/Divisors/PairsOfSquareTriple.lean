import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple

noncomputable section

namespace GlobalTheory.ThK.Inhab

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {X : Chars F E}

theorem pairV {a a' : ℕ} {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  (Check.isPair_of_isTriple h).1

theorem pairV' {a a' : ℕ} {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  (Check.isPair_of_isTriple h).2

theorem two_le_rank {a a' : ℕ} {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    2 ≤ a' ∧ a' < a := by
  have h1 := h.geo.aBig
  exact ⟨by omega, h.geo.lt⟩

theorem conj_conj (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

example : BorelSpace (AE F E)ˣ := ⟨rfl⟩

example {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (K : Subgroup (UA σ J)) : BorelSpace K :=
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  Subtype.borelSpace _

example {a a' : ℕ} {G : Geo σ a a'} (h : G.IsGood B) : 2 * ((a - a') / 2) + a' = a ∧ 2 ≤ (a - a') / 2 := by
  obtain ⟨k, hk⟩ := h.even
  have h1 := h.lt
  have h2 := h.eBig
  omega

example : (9 - (1 + 2)) / 2 + 1 = 4 ∧ (7 + 2 - 3) / 2 = 3 := by decide

end General

section Grid

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil
  GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

end Grid

end GlobalTheory.ThK.Inhab

end
