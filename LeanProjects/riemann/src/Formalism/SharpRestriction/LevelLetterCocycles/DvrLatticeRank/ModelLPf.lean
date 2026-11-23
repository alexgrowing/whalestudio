import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfL
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfD
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfK

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem modell_pf : ModelLStep := by
  unfold ModelLStep modelLR recU
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hr h' hh' T hT hJ c
  obtain ⟨u₀, hu₀, hΛ⟩ := MLL.exists_mul_gamma_Eat_pow_eq_Eat_pow D HW F Cm CA CB CK hA l hl K LL hG π' E hr h'
  obtain ⟨hu, hu1⟩ := MLL.rec_u D HW l hl K LL hG
  have hwd := MLL.rec_WD D HW F Cm CA CB CK hA l hl K LL hG π' E hr T hT c
  have hlet := Formalism.MainNotions.ArcLiftingSetup.γA_letE ((HW l).W K 1 LL hG) ((HW l).W K 1 LL hG).gamK c
  have hlev := fun τ ζ (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) a =>
    MLL.rec_lev D HW F Cm l hl K LL hG c τ ζ hpt a
  unfold ModelL
  refine ⟨MLF.nl_le _ _ _ _ _ _ _, fun x hx => MLH.nl_γ _ _ _ _ _ _ _ hu₀ hΛ hlet _ hlev hx,
    fun a ha x hx => MLF.nl_smulA _ _ _ _ _ _ _ ha hx,
    MLD.model_lattice_filtration D HW F Cm CA CB CK hA l hl K LL hG π' E hr h' hh' T hT hJ c,
    fun x hx k hk => MLF.nl_sat _ _ _ _ _ _ _ hwd ?_ hx k hk,
    MLD.model_lattice_power D HW F Cm CA CB CK hA l hl K LL hG π' E hr h' hh' T hT hJ c,
    fun x hx hγ => MLJ.local_form _ _ _ _ _ _ _ hwd hu₀ hΛ hlet _ hu hu1 hlev ?_ hx hγ⟩
  · rw [map_natCast]
    exact Formalism.MainNotions.LiftingTheory.tr_pLL_ne ((HW l).W K 1 LL hG)
  · intro τ ζ hpt
    obtain ⟨U, hU, hU0⟩ := MLK.lev_Eat_simple D HW l hl K LL hG π' E hr c ζ τ hpt
    refine ⟨U ^ h', ?_, ?_⟩
    · rw [map_pow, hU, mul_pow]
    · rw [map_pow]
      exact pow_ne_zero _ hU0

end Formalism.MainNotions.N.Ln34

end
