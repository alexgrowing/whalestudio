import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsogenyOfSurjectivePolAVStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAbelianSchemeModelOfIsogenyDedekind
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionOfFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTripleOfAbelianModelDedekindStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIsogenousDedekindStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_pat_model_of_isogeny : ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (σ : K →+* ℂ) (P : Out.PolAV (Sp R)) (P₀ : Out.PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left) (T₀ : PAT H (Sp K)) (ψ : P₀.A ⟶ T₀.t.G), IsPolFibre (algebraMap R K) P P₀ φ → P.g = T₀.g → IsMonHom ψ → Surjective ψ.left → ∃ (T : PAT H (Sp R)) (_ : SABMap T₀.t T.t (spMap (algebraMap R K))), T.g = T₀.g := by
  intro hU hL hL2 hX hK E _ _ _ H R K _ _ _ _ _ σ P P₀ φ T₀ ψ hP hg hψ hs
  obtain ⟨hfin, hfl, n, hn, hker⟩ := GlobalTheory.T.finite_flat_torsion_ker_of_surjective_polAV hU hL K σ P₀ T₀.pol ψ (hP.1.trans hg) hψ hs
  obtain ⟨B, _, φB, Ψ, hB, gp, -, hΨfin, hΨfl, hΨs, -⟩ :=
    GlobalTheory.exists_abelianScheme_model_of_isogeny_dedekind hL R K P P₀.A T₀.t.G φ ψ n hP.2.1 T₀.ab hψ hfin hfl hs hn hker
  obtain ⟨t, m, e, -, -⟩ := GlobalTheory.T.exists_triple_of_abelian_model_dedekind hL hX E H R K T₀.t B φB hB gp
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have hpr : IsProper t.G.hom := by
    have := hB.proper
    rw [← Over.w e.hom]
    infer_instance
  have hA : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, hpr, t.semi.geomConnected⟩
  obtain ⟨w, hw, -⟩ := m.lin
  have i : LBIso T₀.t.PP.L (t.PP.L.pull m.φ) := ⟨w, hw⟩
  have ha : Out.RelAmple t.G t.PP.L :=
    GlobalTheory.T.relAmple_of_generic_isogenous_dedekind hL hL2 R K P t.G (Ψ ≫ e.inv) t.PP.L T₀.t.G m.φ T₀.t.PP.L hA t.PP.isLB T₀.t.PP.isLB
      (by rw [Over.comp_left]; infer_instance) (by rw [Over.comp_left]; infer_instance)
      (by rw [Over.comp_left]; infer_instance) m.cart i T₀.ample
  obtain ⟨_, w', hw', -⟩ := t.sym
  exact ⟨⟨t, hA, T₀.g,
    smoothOfRelativeDimension_of_fibre R K (algebraMap R K) t.G _ m.φ T₀.t.G.hom T₀.g hA m.cart.1 T₀.dim,
    sym_of_lbIso_neg ⟨w', hw'⟩, ha,
    hK.kTriv_of_generic hA t.PP.isLB ha m.cart T₀.t.PP.isLB i T₀.ktriv⟩, m, rfl⟩

end GlobalTheory.CM
