import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellInv
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellBru
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellMono
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellPt
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellSchur
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellGeo
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SplittingAdmissibleOfTermData

noncomputable section
namespace Formalism.MainNotions.BridgeLemma
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.LatticeGluingRadicals NumberField Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tie_trace {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (x : E) : algebraMap F E (Algebra.trace F E x) = x + star x := by
  classical

  have hfix : ∀ c : F, star (algebraMap F E c) = algebraMap F E c :=
    fun c => (hc.fixed _).2 ⟨c, rfl⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hc.deg2]; norm_num)
  let s : E ≃ₐ[F] E :=
    { toFun := star
      invFun := star
      left_inv := star_star
      right_inv := star_star
      map_mul' := fun a b => by rw [star_mul, mul_comm]
      map_add' := star_add
      commutes' := hfix }
  have hs1 : s ≠ 1 := by
    intro h
    have hbot : (⊥ : Subalgebra F E) = ⊤ := by
      refine eq_top_iff.2 fun a _ => ?_
      have ha : star a = a := DFunLike.congr_fun h a
      obtain ⟨c, hc'⟩ := RingHom.mem_range.1 ((hc.fixed a).1 ha)
      exact Algebra.mem_bot.2 ⟨c, hc'⟩
    have h1 : Module.finrank F E = 1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbot
    rw [hc.deg2] at h1
    exact absurd h1 (by norm_num)
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ Module.finrank F E := by
    first
      | exact AlgEquiv.card_le
      | exact (Fintype.card_congr (algEquivEquivAlgHom F E)).le.trans AlgHom.card_le
  have hpair : ({1, s} : Finset (E ≃ₐ[F] E)).card = 2 := Finset.card_pair (Ne.symm hs1)
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    have hge : ({1, s} : Finset (E ≃ₐ[F] E)).card ≤ Fintype.card (E ≃ₐ[F] E) :=
      Finset.card_le_univ _
    rw [hc.deg2] at hle
    omega
  haveI : IsGalois F E := by
    first
      | exact IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, hc.deg2])
      | exact IsGalois.of_card_aut_eq_finrank F E (by rw [hcard, hc.deg2])
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, hpair]
  first
    | rw [trace_eq_sum_automorphisms]
    | rw [Algebra.trace_eq_sum_automorphisms]
  rw [huniv, Finset.sum_pair (Ne.symm hs1)]
  try rfl

theorem tie_aniso (D : D7) (T : ℕ) (hT : 0 < T) (F : LFlag (hS D) D.R.rS (T : D.host.E)) (y : (hS D).V)
    (h1 : ∀ a, (hS D).hT (F.fl.fvec a) y = 0) (h2 : (hS D).hT y y = 0) : y ∈ F.fl.X := by
  by_contra hy
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hmem : y ∈ orth (hS D) (Xplus F) := by
    rw [p_mem_orth]
    intro x hx
    have hle : Xplus F ≤ LinearMap.ker ((hS D).hT.flip y) := by
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨a, rfl⟩
        have := h1 a.castSucc
        simpa [FlagG.fvec] using this
      · rintro _ rfl
        have := h1 (Fin.last _)
        simpa [FlagG.fvec] using this
    exact hle hx
  have hp := p_posX D T hT F τ y hmem hy
  unfold nrm at hp
  rw [h2, map_zero] at hp
  simp at hp

end Formalism.MainNotions.BridgeLemma
end
