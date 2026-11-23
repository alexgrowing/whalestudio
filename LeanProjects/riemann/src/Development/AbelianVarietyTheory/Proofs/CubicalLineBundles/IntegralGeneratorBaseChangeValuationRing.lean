import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SecTieBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoUniqueOfRig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem secInt_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), SecBC i 1 x x' s s' → SecInt T m1 m2 s → SecInt T' m1' m2' s' := by
  intro E _ _ _ H Dw l Xo T T' ψ i hψ x x' G G' t t' m1 m2 m1' m2' n n' hx h1 h2 s s' hb
  rintro ⟨θ, hθ, w2, σ, θ2, r2, i2, p2, tie⟩
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨wn, gn, rn, -⟩ := n.lin
  obtain ⟨wn', gn', rn', -⟩ := n'.lin
  obtain ⟨w2', g2', r2', -⟩ := m2'.lin
  have Rn : RigIso n wn := ⟨gn, rn⟩
  have Rn' : RigIso n' wn' := ⟨gn', rn'⟩
  have R2' : RigIso m2' w2' := ⟨g2', r2'⟩
  obtain ⟨θ', hθ'⟩ := sec_pull_down ((isGen_iff wn).1 gn) G.t.PP.isLB G'.t.PP.isLB θ
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((isGen_iff w2').1 g2') G'.t.PP.isLB t'.PP.isLB θ'
  have nz : ∀ y : Sp T.V, ∃ z : G.t.G.left, G.t.G.hom z = y ∧ z ∈ Out.nonzeroLocus θ := fun y => by
    obtain ⟨b, hb, -⟩ := GlobalTheory.KeyOnPol.exists_generator hS G.pol
    obtain ⟨z, hz, hm⟩ := hb y
    obtain ⟨a, ha, -⟩ := hθ b
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    rw [ha k, Scheme.basicOpen_mul] at hk
    exact ⟨z, hz, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk.2⟩⟩
  have nz' := SectionBaseChange.fibre_nonzero_of_pull G'.t.PP.isLB hθ' n.cart.1 nz
  refine ⟨θ', SectionBaseChange.generates hS G.pol n.cart.1 G'.t.PP.isLB ⟨wn, gn⟩ θ' nz', w2', σ',
    thfPull G'.t.PP.L m2'.φ θ', R2', ?_, fun _ _ => rfl, ?_⟩
  · refine (TieCalc.isoMaps_iff _ _ _).2 fun Z r z j k hj hk => ?_
    exact (gs_appLE m2'.φ _ _ _ r z (mem_pull.2 hj) _).trans (hσ' Z r z j k hj hk)
  · refine (TieCalc.secTie_baseChange m1 tie i m1' n' s' wn' (thfPull t.PP.L n'.φ σ) σ' hx h1 hb Rn'
      (fun _ _ => rfl)).2 ((TieCalc.isoMaps_iff _ _ _).2 fun Z r z j k hj hk => ?_)
    have hbase : spMap (algebraMap T'.V T'.Fr) ≫ spMap ψ = spMap i ≫ spMap (algebraMap T.V T.Fr) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψ]
    obtain ⟨N, hN⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ n m2'
    have hN' : N.φ = m2'.φ ≫ n.φ := hN
    obtain ⟨wa, ra, Ta⟩ := GlobalTheory.LiftBaseChange.rigIso_comp n m2' N rfl hN' Rn R2'
    obtain ⟨wb, rb, Tb⟩ := GlobalTheory.LiftBaseChange.rigIso_comp m2 n' N hbase (hN'.trans h2) r2 Rn'
    have hp : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m2'.cart.1 G'.ab.proper
    have hab : IsAbelianScheme t'.G := ⟨t'.semi.comm, t'.semi.smooth, hp, t'.semi.geomConnected⟩
    obtain rfl : wa = wb := iso_unique_of_rig GlobalTheory.globalFns_holds t'.G hab t'.PP.isLB G.t.PP.isLB ra.1 rb.1 ra.2 rb.2
    obtain ⟨a, ha⟩ := exists_chart G.t.PP.isLB (m2.φ (n'.φ (r z)))
    obtain ⟨b, hb'⟩ := exists_chart G'.t.PP.isLB (m2'.φ (r z))
    have ha' : n.φ (m2'.φ (r z)) ∈ G.t.PP.L.U a := (congrArg (fun q => q (r z) ∈ G.t.PP.L.U a) h2).mpr ha
    have e1 := hθ' Z (r ≫ m2'.φ) z a b ha' hb'
    have e2 := hσ' Z r z b k hb' hk
    have le : (G.t.PP.L.pull m2.φ).U (fun _ => a) ≤ m2.φ ⁻¹ᵁ G.t.PP.L.U a := fun q hq => mem_pull.1 hq
    have e3 := (TieCalc.isoMaps_iff _ _ _).1 i2 Z (r ≫ n'.φ) z a j ha hj
    rw [p2 (fun _ => a) le, gs_appLE m2.φ _ _ le (r ≫ n'.φ) z (mem_pull.2 ha), Category.assoc, ← h2,
      ← Category.assoc, e1, e2, ← _root_.mul_assoc, ← Units.val_mul, ← Ta Z r z a b k ha' hb' hk,
      Tb Z r z a j k ha hj hk, Units.val_mul, _root_.mul_assoc] at e3
    exact (gs_appLE n'.φ _ _ _ r z (mem_pull.2 hj) _).trans ((Units.mul_right_inj _).1 e3).symm

end GlobalTheory.LamT
