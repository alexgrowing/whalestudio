import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianEndomorphismUniqueOverDegenerationDat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorProjectionAdjointPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupsAdjointHomPairClosedFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

namespace GlobalTheory.MumIsoAdj

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem linHom_unique (hR : Base R) (hG : IsSemiAbelian G) {U : Unif (maximalIdeal R) D A G} {a a' k k' g g'}
    (h : LinHom U.toUnifPre U.toUnifPre a k g) (h' : LinHom U.toUnifPre U.toUnifPre a' k' g') (ha : a = a')
    (hk : ∀ y, k y = k' y) : g = g' := by
  obtain rfl := ha
  obtain rfl : k = k' := AddMonoidHom.ext hk
  obtain ⟨u₁, u₂⟩ := GlobalTheory.MumUniq.main R hR.1 D A G hG U a k
  exact u₂ g g' (congrFun (u₁ _ _ (linHom_iff_linEnd.1 h).2 (linHom_iff_linEnd.1 h').2))

end

theorem iso_of_factor_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ U₀ : Unif (maximalIdeal R) D A₀ G₀, ∃ (ε : G ≅ G₀) (u : G' ⟶ G₀) (u' : G₀ ⟶ G'), IsMonHom ε.hom ∧ IsMonHom u ∧ IsMonHom u' ∧ ε.hom = inc ≫ u ∧ u ≫ u' = oG.act (Star.star F.e * F.f * F.e) ∧ GAdj U'.LG.L U₀.LG.L u u' := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi A₀ G₀ _ _ hG₀ U₀
  obtain ⟨-, hsym, g, hg⟩ := hF
  obtain ⟨u, u', hu, hu', hadj⟩ :=
    GlobalTheory.T.uniformisedGroups_adjointHomPair_closedForm R hR D' A' G' hG' U' D A₀ G₀ hG₀ U₀ _ _ _ _ (GlobalTheory.T.idempotentFactor_projection_adjointPair R _ D D' F)
  have hO : ∀ a : F.O, LinHom U'.toUnifPre U'.toUnifPre (F.o.onB.act a)
      (DistribMulAction.toAddMonoidHom D'.toPre.X (Star.star a)) (oG.act a) := fun a =>
    ⟨oG.hom a, fun e => hlin.q_lin e a, fun e => by
      obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
      exact ⟨t, ht, hi⟩⟩
  have hu1 := hu.1
  have hu1' := hu'.1
  have hee : Star.star F.e * Star.star F.e = Star.star F.e := by rw [← star_mul, F.idem]
  have hsS : Star.star (Star.star F.e * F.f * F.e) = Star.star F.e * F.f * F.e := by
    rw [star_mul, star_mul, star_star, ← _root_.mul_assoc, ← hsym]
  have hsg : (Star.star F.e * F.f * F.e) * Star.star g = Star.star F.e := by
    have := congrArg Star.star hg
    rwa [star_mul, hsS] at this
  have hkey : F.e * Star.star g * (Star.star F.e * F.f * F.e) = F.e := by
    calc F.e * Star.star g * (Star.star F.e * F.f * F.e)
        = g * ((Star.star F.e * F.f * F.e) * Star.star g) * (Star.star F.e * F.f * F.e) := by
          nth_rewrite 1 [← hg]; simp only [_root_.mul_assoc]
      _ = g * (Star.star F.e * (Star.star F.e * F.f * F.e)) := by rw [hsg, _root_.mul_assoc]
      _ = F.e := by
          rw [← _root_.mul_assoc (Star.star F.e) (Star.star F.e * F.f) F.e,
            ← _root_.mul_assoc (Star.star F.e) (Star.star F.e) F.f, hee, hg]
  have hxi : ∀ y, F.xi y = F.e • F.xi y := fun y => by rw [← F.xi_xp, F.xp_xi]
  have hincE : F.inc ≫ F.o.onB.act F.e = F.inc := by
    rw [← F.pr_inc, ← Category.assoc, F.inc_pr, Category.id_comp]
  have h1 : u ≫ u' = oG.act (Star.star F.e * F.f * F.e) :=
    GlobalTheory.MumIsoAdj.linHom_unique hR hG' (hu.comp hu') (hO _)
      (by rw [F.o.onB.map_mul (Star.star F.e * F.f) F.e, ← F.pr_inc]; exact (Category.assoc _ _ _).symm)
      (fun y => by
        change (Star.star F.e * F.f) • F.xi (F.xp y) = Star.star (Star.star F.e * F.f * F.e) • y
        rw [hsS, F.xi_xp, smul_smul])
  have h2 : u' ≫ oG.act (F.e * g) ≫ u = 𝟙 G₀ :=
    GlobalTheory.MumIsoAdj.linHom_unique hR hG₀ ((hu'.comp (hO _)).comp hu) (LinHom.id _)
      (by
        calc ((F.inc ≫ F.o.onB.act (Star.star F.e * F.f)) ≫ F.o.onB.act (F.e * g)) ≫ F.pr
            = F.inc ≫ F.o.onB.act ((F.e * g) * (Star.star F.e * F.f * F.e)) ≫ F.pr := by
              rw [F.o.onB.map_mul (F.e * g) (Star.star F.e * F.f * F.e),
                F.o.onB.map_mul (Star.star F.e * F.f) F.e]
              conv_lhs => rw [← hincE]
              simp only [Category.assoc]
          _ = 𝟙 _ := by
              rw [_root_.mul_assoc F.e g, hg, F.idem, ← F.pr_inc]
              simp only [← Category.assoc, F.inc_pr, Category.id_comp])
      (fun y => by
        change F.xp (Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y)) = y
        have hw : Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y) =
            (Star.star g * (Star.star F.e * F.f * F.e)) • F.xi y := by
          conv_lhs => rw [hxi y]
          rw [smul_smul, smul_smul, star_mul]
          congr 1
          simp only [_root_.mul_assoc]
          rw [← _root_.mul_assoc (Star.star F.e) (Star.star F.e), hee]
        have h3 : F.xi (F.xp (Star.star (F.e * g) • ((Star.star F.e * F.f) • F.xi y))) = F.xi y := by
          rw [F.xi_xp, hw, smul_smul, ← _root_.mul_assoc, hkey, ← hxi]
        have := congrArg F.xp h3
        rwa [F.xp_xi, F.xp_xi] at this)
  refine ⟨⟨inc ≫ u, u' ≫ oG.act g ≫ pr, ?_, ?_⟩, u, u', inferInstance, hu.1, hu'.1, rfl, h1, hadj⟩
  · calc (inc ≫ u) ≫ u' ≫ oG.act g ≫ pr = inc ≫ ((u ≫ u') ≫ oG.act g) ≫ pr := by simp only [Category.assoc]
      _ = 𝟙 G := by
          rw [h1, ← oG.map_mul, hg, ← hpi]
          simp only [← Category.assoc, hip, Category.id_comp]
  · calc (u' ≫ oG.act g ≫ pr) ≫ inc ≫ u = u' ≫ (oG.act g ≫ pr ≫ inc) ≫ u := by simp only [Category.assoc]
      _ = 𝟙 G₀ := by rw [hpi, ← oG.map_mul, h2]

end GlobalTheory.MumIsoAdj
