import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting

theorem twist_settings_unread : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (N : TwNew D), (∃ A' : SideA N.toD7 (N.cf cf) jE, A'.row = N.row A.row ∧ (∀ lam, A'.pl.ι lam = A.pl.ι lam) ∧ (∀ w a, A'.wdT.e w a = A.wdT.e w a) ∧ (∀ j h1 h2 π, A'.au.cls j h1 h2 π = A.au.cls j h1 h2 π) ∧ ∀ hL, (Nonempty (CGTrue hL D A.wdT) → Nonempty (CGTrue hL N.toD7 A'.wdT)) ∧ (AUTrue hL D A.wdT A.au → AUTrue hL N.toD7 A'.wdT A'.au)) ∧ (∀ M tup Q, MtInput D M tup Q → MtInput N.toD7 (N.mt M) tup Q) ∧ (BlocksUnique D → BlocksUnique N.toD7) := by
  intro D cf jE A N
  let A' : SideA N.toD7 (N.cf cf) jE :=
    { bare := A.bare
      wdT := A.wdT
      lab := A.lab
      chr := { A.chr with }
      row := N.row A.row
      pl := { A.pl with }
      iota := A.iota
      wd := { A.wd with }
      grp := { A.grp with }
      par := { A.par with }
      au := { A.au with }
      chiT := A.chiT }
  refine ⟨⟨A', rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun hL => ⟨fun ⟨h⟩ => ⟨{ h with }⟩, fun h => h⟩⟩,
    fun M tup Q h => { h with }, fun h => h⟩

end GlobalTheory.HeightCounting
