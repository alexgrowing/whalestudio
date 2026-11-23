import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesRing
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CokernelCoherent
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackCoherent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

lemma injective_app_of_mono {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) [Mono φ]
    (U : X.Opens) : Function.Injective (φ.app U) := by
  have : Mono ((Scheme.Modules.toPresheaf X).map φ) := inferInstance
  have h := (NatTrans.mono_iff_mono_app _).1 this (op U)
  exact (AddCommGrpCat.mono_iff_injective _).1 h

variable {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}} [X.Over (Spec (.of A))]
  (F : X.Modules)

abbrev reesTarget : (reesScheme I X).Modules :=
  (Scheme.Modules.pushforward (reesPolyMap I X)).obj
    ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F))

abbrev reesUnit : (Scheme.Modules.pullback (reesPr I X)).obj F ⟶ reesTarget I F :=
  (Scheme.Modules.pullbackPushforwardAdjunction (reesPolyMap I X)).unit.app _

def reesSheaf : (reesScheme I X).Modules := Abelian.coimage (reesUnit I F)

def reesSheafπ : (Scheme.Modules.pullback (reesPr I X)).obj F ⟶ reesSheaf I F :=
  Abelian.coimage.π (reesUnit I F)

def reesSheafι : reesSheaf I F ⟶ reesTarget I F := Abelian.factorThruCoimage (reesUnit I F)

instance : Mono (reesSheafι I F) := (coimCokSC_shortExact (reesUnit I F)).mono_f

lemma reesSheafπ_ι : reesSheafπ I F ≫ reesSheafι I F = reesUnit I F :=
  Abelian.coimage.fac (reesUnit I F)

variable {I F}

lemma isCoherent_pullback_reesPr (hF : IsCoherent F) :
    IsCoherent ((Scheme.Modules.pullback (reesPr I X)).obj F) :=
  isCoherent_pullback _ hF

lemma isQuasicoherent_reesTarget (hF : IsCoherent F) : (reesTarget I F).IsQuasicoherent := by
  have := (isCoherent_pullback (reesPolyMap I X) (isCoherent_pullback_reesPr hF)).1
  exact isQuasicoherent_pushforward_of_isAffineHom _ _

theorem isCoherent_reesSheaf (hF : IsCoherent F) : IsCoherent (reesSheaf I F) := by
  have := (isCoherent_pullback_reesPr (I := I) hF).1
  have := isQuasicoherent_reesTarget (I := I) hF
  exact isCoherent_cokernel (kernel.ι (reesUnit I F)) (isCoherent_pullback_reesPr hF)

lemma surjective_reesSheafπ_app (hF : IsCoherent F) {W : (reesScheme I X).Opens}
    (hW : IsAffineOpen W) : Function.Surjective ((reesSheafπ I F).app W) := by
  have := (isCoherent_pullback_reesPr (I := I) hF).1
  have := isQuasicoherent_reesTarget (I := I) hF
  exact surjective_cokernel_π_app (kernel.ι (reesUnit I F)) hW

lemma injective_reesSheafι_app (W : (reesScheme I X).Opens) :
    Function.Injective ((reesSheafι I F).app W) :=
  injective_app_of_mono _ W

end

end GroundTheory.Arith.SchemeCoh
