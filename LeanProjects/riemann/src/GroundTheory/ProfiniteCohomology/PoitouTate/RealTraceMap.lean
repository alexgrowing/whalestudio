import Mathlib
import GroundTheory.ProfiniteCohomology.PoitouTate.RealTrace
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (N : ℕ) [NeZero N] [Fintype S]

theorem exists_gsTraceQZ :
    ∃ χ : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ QZ,
      χ.comp (ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom.toAddMonoidHom =
        gsSumInvReal S ιr ιs N :=
  QZ.exists_comp_eq_of_ker_le _ _ fun ξ hξ => gsSumInvReal_eq_zero_of S ιr ιs N ξ hξ

def gsTraceQZ : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ QZ :=
  Classical.choose (exists_gsTraceQZ S ιr ιs N)

theorem gsTraceQZ_comp :
    (gsTraceQZ S ιr ιs N).comp
        (ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom.toAddMonoidHom =
      gsSumInvReal S ιr ιs N :=
  Classical.choose_spec (exists_gsTraceQZ S ιr ιs N)

theorem nsmul_gsTraceQZ
    (z : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3) :
    N • gsTraceQZ S ιr ιs N z = 0 :=
  (map_nsmul (gsTraceQZ S ιr ιs N) N z).symm.trans
    ((congrArg (gsTraceQZ S ιr ιs N) (nsmul_tateCompactCohomologyRes_eq_zero (gsFinFamily S ιs)
      (gsRealFamily S ιr) (nsmul_gsRoots S N) 3 z)).trans (map_zero _))

def gsTrace : tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 3 →+ ZMod N :=
  zmodOfQZ (gsTraceQZ S ιr ιs N) (nsmul_gsTraceQZ S ιr ιs N)

theorem gsTrace_localToCompact (ξ : ptTLocal (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2) :
    zmodToQZ N (gsTrace S ιr ιs N
      ((ptTLocalToCompact (gsFinFamily S ιs) (gsRealFamily S ιr) (gsRoots S N) 2).hom ξ)) =
      ∑ v, gsLocalInvRootsQZ S ιs N v (ξ.1 v) + ∑ w, gsRealInvRootsQZ S ιr N w (ξ.2 w) :=
  (zmodToQZ_zmodOfQZ _ _ _).trans (DFunLike.congr_fun (gsTraceQZ_comp S ιr ιs N) ξ)

end GroundTheory.ProfCoh
