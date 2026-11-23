import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesOpenWithLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.NPin.pin_of_nTrue : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (nt : NTrue hL D cf C tp), ValLL0 D cf → (∀ σ σ', (nt.rep σ).Iso (nt.rep σ') → σ = σ') → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → ChebSplit D.nd → ∃ P : Pin hL D, P.cf = cf ∧ P.C = C ∧ HEq P.tp tp ∧ HEq P.rep nt.rep ∧ HEq P.M (mtL nt.L nt.M) := by
  intro hL D cf C tp nt hval hinj hstar hexp hsplit hcheb
  obtain ⟨⟨D0, cf0, jE, A, cg, au, rep, row, low, Pq, S, hLm, eig, θ, Bs, M, C0, tp0, ch, mt, big, L, Sp, Au, ss, heq⟩, pack⟩ := nt
  dsimp only at pack heq hinj ⊢
  subst heq
  cases pack
  obtain ⟨Hk, hHk⟩ := GlobalTheory.FitHecke.heckeOpen_withLoc D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hstar hexp hsplit hcheb big L Sp Au
  obtain ⟨ty⟩ := GlobalTheory.HeightCounting.typesOpen_withLoc D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hstar hexp hsplit hcheb big L Sp Au ss
  obtain ⟨tw⟩ := GlobalTheory.T.side_multiplicity_character D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hstar hexp hsplit hcheb big L Sp Au
  refine ⟨{ cf := cfL L cf0, C := chL L C0, tp := tpL L tp0, chr := tw.chrN, val := hval, Q_eq := ?Q, T := { A.wdT with }, lab := A.lab, cg := { cg with }, M := mtL L M, H := Hk, au := ?au, rep := rep, rep_inj := hinj, row := ?row, locW_eq := fun i i' σ w => (Au.locW i σ w).trans (Au.locW i' σ w).symm, jE := jE, ty := ty, wd := { A.wd with }, wdOf := Au.wdOf }, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  case Q =>
    intro i
    have hm : i ∈ L.X.nd.locs (L.X.nd.j i) (L.X.nd.w i) := (L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
    exact (Sp.Q_eq _ _ i hm).trans (Sp.Qc_eq _ _)
  case au =>
    intro j h1 h2 π s σ h
    rw [hHk]
    exact au j h1 h2 π s σ h
  case row =>
    intro i
    refine ⟨fun σ s τ h => ?_, fun σ v w hvw Dv hα => ?_⟩
    · exact (congrArg (A.wdT.e s.w) (Au.locW i σ s.w)).trans (row.1 σ s τ h)
    · obtain ⟨α, h1, h2⟩ := row.2 σ v w hvw Dv hα
      exact ⟨α, h1, (Au.satW i σ w).trans h2⟩
