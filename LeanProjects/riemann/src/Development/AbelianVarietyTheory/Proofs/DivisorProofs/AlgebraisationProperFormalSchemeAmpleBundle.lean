import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CancelPowersOfCechLineBundlesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveAlgebraisationFormalEmbeddingComStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleAlgebraisationGeneratedSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoAlgebraisedPowersCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoZpowLocalUnitsPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleIsoLocalUnitsCompOfPullbackSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleCompatibleSectionsThickeningTowerStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem isClosedImmersion_lift_id {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (h : 𝟙 X ≫ f = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id R))) :
    IsClosedImmersion (pullback.lift (𝟙 X) f h) := by
  have hi : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [show CommRingCat.ofHom (RingHom.id R) = 𝟙 _ from rfl, Spec.map_id]
    infer_instance
  have e : pullback.lift (𝟙 X) f h = inv (pullback.fst f (Spec.map (CommRingCat.ofHom (RingHom.id R)))) :=
    IsIso.eq_inv_of_inv_hom_id (pullback.lift_fst _ _ _)
  rw [e]
  infer_instance

theorem veryAmpleBy_of_lbIso {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    {H H'' : LB X} (hH : H.IsLB) (hH'' : H''.IsLB) (hI : LBIso H H'') {n : ℕ} {s : Fin (n + 1) → LB.Sec H}
    (hs : VeryAmpleBy f H s) : ∃ s'' : Fin (n + 1) → LB.Sec H'', VeryAmpleBy f H'' s'' := by
  obtain ⟨w, hw⟩ := LBIso.trans hH'' hH (pull_isLB hH _) (LBIso.symm hI) (LBIso.symm (GlobalTheory.lbIso_pull_id hH))
  choose s'' hs'' using fun j => (GlobalTheory.SecPullIso.section_pull X X (𝟙 X) H H'' w hH hH'' hw (s j)).1
  exact ⟨s'', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H n s hH hs R (RingHom.id R) X f (𝟙 X)
    (by rw [show CommRingCat.ofHom (RingHom.id R) = 𝟙 _ from rfl, Spec.map_id]; simp)
    (isClosedImmersion_lift_id f _) H'' w s'' hH'' hw fun j => (hs'' j).1⟩

end GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem formalAlgebraisation_schemes : GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  intro R _ _ I hI Y β hβ hY N hN hNN hA
  choose v hv using hNN
  obtain ⟨a, ha1, hlift⟩ := GlobalTheory.T.exists_veryAmple_compatible_sections_thickeningTower R I Y β hβ N hN hA
  have hpw : ∀ (c : ℤ) (e : ℕ), ∃ wa : LB.Iso (GlobalTheory.AbLaw.pw (N e) c) ((GlobalTheory.AbLaw.pw (N (e + 1)) c).pull (β e)),
      wa.IsGen ∧ ∀ (z : (Y e).left) (k : (N (e + 1)).ι) (k' : (N e).ι), β e z ∈ (N (e + 1)).U k → z ∈ (N e).U k' →
        Geo.Tor.gw wa (𝟙 _) z k k' = Geo.Tor.gw (v e) (𝟙 _) z k k' ^ c := fun c e => by
    obtain ⟨wa, h1, h2⟩ := GlobalTheory.T.exists_bundleIso_zpow_local_units_pow (Y (e + 1)).left (Y e).left (β e) (N (e + 1)) (N e) (v e) (hv e) c
    exact ⟨wa, h1, fun z k k' hk hk' => h2 (Y e).left (𝟙 _) z k k' hk hk'⟩
  choose va hva hvaw using hpw (a : ℤ)
  choose vb hvb hvbw using hpw ((a + 1 : ℕ) : ℤ)
  obtain ⟨n, s, hsRel, hsVA⟩ := hlift a (Or.inl rfl) va hva
  obtain ⟨n₂, s₂, hs₂Rel, hs₂VA⟩ := hlift (a + 1) (Or.inr rfl) vb hvb
  obtain ⟨B, H', s', b, w, hH', hVA', hpb, hcomp, hw, -⟩ := GlobalTheory.T.exists_projective_algebraisation_formalEmbedding_complete R I hI Y β hβ
    (fun e => GlobalTheory.AbLaw.pw (N e) a) va (fun e => ⟨isLB_pw (hN e) _, hva e⟩) n s hsRel (hsVA 0)
  have hBp : IsProper B.hom := GlobalTheory.AbLaw.isProper_of_isProjBy R B.left B.hom ⟨H', hH', n, s', hVA'⟩
  obtain ⟨M₂, s₂', w', hM₂, hw'⟩ := GlobalTheory.T.exists_lineBundle_algebraisation_generatedSystem R I hI B hBp Y β b hpb hcomp
    (fun e => GlobalTheory.AbLaw.pw (N e) ((a + 1 : ℕ) : ℤ)) vb (fun e => ⟨isLB_pw (hN e) _, hvb e⟩) n₂ s₂ hs₂Rel
    (fun e => (hs₂VA e).1)
  have c1 : ∀ e z k l' l, b e z ∈ H'.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l →
      Geo.Tor.gw (w e) (𝟙 _) z k l = Geo.Tor.gw (w (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ (a : ℤ) := by
    intro e z k l' l h1 h2 h3
    rw [← hvaw e z l' l h2 h3]
    exact GlobalTheory.T.bundleIso_local_units_comp_of_pullback_sections B.left (Y (e + 1)).left (Y e).left (b (e + 1)) (β e) (b e) (hcomp e) H'
      (GlobalTheory.AbLaw.pw (N (e + 1)) a) (GlobalTheory.AbLaw.pw (N e) a) (w (e + 1)) (va e) (w e) (Fin (n + 1)) s' (s (e + 1)) (s e)
      (fun j => (hw (e + 1)).2 j) (fun j => hsRel e j) (fun j => (hw e).2 j) (hsVA e).1 z k l' l h1 h2 h3
  have c2 : ∀ e z k l' l, b e z ∈ M₂.U k → β e z ∈ (N (e + 1)).U l' → z ∈ (N e).U l →
      Geo.Tor.gw (w' e) (𝟙 _) z k l =
        Geo.Tor.gw (w' (e + 1)) (β e) z k l' * Geo.Tor.gw (v e) (𝟙 _) z l' l ^ ((a + 1 : ℕ) : ℤ) := by
    intro e z k l' l h1 h2 h3
    rw [← hvbw e z l' l h2 h3]
    exact GlobalTheory.T.bundleIso_local_units_comp_of_pullback_sections B.left (Y (e + 1)).left (Y e).left (b (e + 1)) (β e) (b e) (hcomp e) M₂
      (GlobalTheory.AbLaw.pw (N (e + 1)) ((a + 1 : ℕ) : ℤ)) (GlobalTheory.AbLaw.pw (N e) ((a + 1 : ℕ) : ℤ)) (w' (e + 1)) (vb e) (w' e)
      (Fin (n₂ + 1)) s₂' (s₂ (e + 1)) (s₂ e)
      (fun j => (hw' (e + 1)).2 j) (fun j => hs₂Rel e j) (fun j => (hw' e).2 j) (hs₂VA e).1 z k l' l h1 h2 h3
  have hiso := GlobalTheory.T.lineBundleIso_algebraised_powers_compatible R I hI B hBp Y β b hpb hcomp N v hN (a : ℤ) ((a + 1 : ℕ) : ℤ) H' M₂ hH' hM₂ w w'
    (fun e => ⟨(hw e).1, (hw' e).1⟩) c1 c2
  have hcast : ((a + 1 : ℕ) : ℤ) = (a : ℤ) + 1 := by push_cast; rfl
  rw [hcast] at hiso
  have hM : (GlobalTheory.AbLaw.tw M₂ H' (-1)).IsLB := isLB_tw hM₂ hH' _
  have hH'M : LBIso H' (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.tw M₂ H' (-1)) a) := GlobalTheory.T.cancel_powers_of_cech_line_bundles.2 B.left H' M₂ a hH' hM₂ hiso
  have hNM : ∀ e, LBIso (N e) ((GlobalTheory.AbLaw.tw M₂ H' (-1)).pull (b e)) := fun e =>
    GlobalTheory.T.cancel_powers_of_cech_line_bundles.1 B.left (Y e).left (b e) H' M₂ (N e) a hH' hM₂ (hN e) ⟨w e, (hw e).1⟩
      (hcast ▸ ⟨w' e, (hw' e).1⟩)
  obtain ⟨s'', hs''⟩ := veryAmpleBy_of_lbIso B.hom hH' (isLB_pw hM _) hH'M hVA'
  exact ⟨B, GlobalTheory.AbLaw.tw M₂ H' (-1), b, hBp, hM,
    (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B _ hM).2 ⟨a, ha1, n, s'', hs''⟩, hpb, hcomp, hNM⟩

end GlobalTheory.FormalAlg
