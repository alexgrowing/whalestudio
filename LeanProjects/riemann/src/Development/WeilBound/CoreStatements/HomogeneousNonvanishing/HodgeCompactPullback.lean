import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HeightPullbackDominatingMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompatStatement
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LatticeIntegrallyClosedTorsion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NotInFibreOfIsUnit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeVectorBundlePullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapOfFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralElementRegularStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentIdealLocalGeneratorStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticeBasisExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DifferentScaledLatticeExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObjectStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcptPullK

theorem pull_eq {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X)
    {E F : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F] (L : Lat ξ E) (j : E →+ F)
    (p' : Cpt ξ') (hq : genPt ξ ⤳ f p'.1) :
    L.pull ξ' f j p' = Submodule.span (regAt ξ' p') (j '' (L ⟨f p'.1, hq⟩ : Set E)) := by
  unfold Lat.pull
  congr 1
  ext e'
  constructor
  · rintro ⟨_, e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨hq, e, he, rfl⟩

theorem unitAt_natCast {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} (q : Cpt ξ) (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → unitAt ξ q (p : Ω)) : unitAt ξ q (n : Ω) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one =>
    simpa [unitAt] using (regAt ξ q).one_mem
  | prime p hp => exact h p hp dvd_rfl
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := fun e => hn (by simp [e])
    have hb0 : b ≠ 0 := fun e => hn (by simp [e])
    obtain ⟨a1, a2, a3⟩ := ha ha0 fun p hp hd => h p hp (hd.mul_right _)
    obtain ⟨b1, b2, b3⟩ := hb hb0 fun p hp hd => h p hp (hd.mul_left _)
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.cast_mul]; exact mul_ne_zero a1 b1
    · rw [Nat.cast_mul]; exact (regAt ξ q).mul_mem a2 b2
    · rw [Nat.cast_mul, mul_inv]; exact (regAt ξ q).mul_mem a3 b3

theorem noeth_stalk {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (hg : IsCptGen ξ) (q : Cpt ξ)
    (h : IsNoetherianRing (regAt ξ q)) : IsNoetherianRing (X.presheaf.stalk q.1) :=
  isNoetherianRing_of_ringEquiv (regAt ξ q) (RingEquiv.ofBijective (genMap ξ q).rangeRestrict
    ⟨fun a b e => hg.inj q (congrArg Subtype.val e), (genMap ξ q).rangeRestrict_surjective⟩).symm

set_option maxHeartbeats 1000000 in
theorem hodgeCpt_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (Z : Scheme.{0}) (ξ' : Sp Ω' ⟶ Z) (h : Z ⟶ A.X), A.ξ ≫ A.f = x ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn {q | InFibre A.ξ p q} (labelRk D s) ⊤) → (∀ q : Z, genPt ξ' ⤳ q) → CoordTie ℤ ξ' (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ h i → ∃ (A' : HodgeCpt Y S y') (e : A'.X ≅ Z) (j : A.Li →+ A'.Li) (m : SABMap A'.t A.t (e.hom ≫ h)), A'.ξ ≫ e.hom = ξ' ∧ A'.f = e.hom ≫ h ≫ A.f ∧ A'.m.φ = m.φ ≫ A.m.φ ∧ A'.cst = i.comp A.cst ∧ A'.R = A.R ∧ IsExtOver i j ∧ (∀ v, (A'.M.pt (j v)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt v).left) ∧ (∀ p ∈ S, ∀ s, ((A'.M.htOm A'.t.PP.L (p ^ A'.R p)).map (A'.Vgen s).dualRestrict).IsVBOn {q | InFibre A'.ξ p q} (labelRk D s) ⊤) ∧ ∀ s, A'.V s = (A.V s).pull A'.ξ (e.hom ≫ h) j := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω Ω' _ _ i K K' _ _ J J' _ _ y y' A x Z ξ' h hx hS hvb hall htie hnorm hdom
  haveI : CharZero Ω := charZero_of_injective_ringHom A.cst.injective
  haveI : CharZero Ω' := charZero_of_injective_ringHom i.injective
  have hgen := A.tie.gen
  have hgen' := htie.gen
  obtain ⟨t', ⟨mh⟩⟩ : ∃ t' : SAB H Z, Nonempty (SABMap t' A.t h) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM Out.proved_CubePullSt h A.t⟩⟩
  obtain ⟨mf, hmf⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ A.m mh
  obtain ⟨Li', acg', mod', ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists Z t'.G Ω' ξ'
  obtain ⟨ρ', hρ', -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act Z t'.G Ω' ξ' Li' M' (𝓞 E) t'.act.act t'.act.hom t'.act.one
    t'.act.mul t'.act.add
  obtain ⟨j, hj⟩ := GlobalTheory.T.lie_model_pullback_map A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' hdom mh.cart
  have hsm : Smooth A.t.G.hom := A.t.semi.smooth
  obtain ⟨hext, hspan, hlat⟩ := GlobalTheory.T.lie_lattice_dominant_compat A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j hgen hgen' hdom
    mh.cart hsm hj
  have hρj := GlobalTheory.T.lie_model_pullback_action A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j (𝓞 E) A.t.act.act t'.act.act A.ρ ρ'
    hdom mh.cart hj A.act hρ' (fun a => mh.act a)
  obtain ⟨jd, hjd⟩ := GlobalTheory.T.dual_map_of_field_extension Ω Ω' i A.Li Li' j hext hspan
  have hW : ∀ s, eigSp ρ' ((i.comp A.cst).comp (labelEmb c s)) = Submodule.span Ω' (j '' (A.Vgen s : Set A.Li)) := fun s =>
    GlobalTheory.T.eigenspace_field_extension E Ω Ω' i A.Li Li' j A.ρ ρ' (A.emb s) hext hspan hρj
  have hdm := GlobalTheory.CompanionTheory.Ar.RegAtDom.regAt_dominates A.X Ω A.ξ Z Ω' ξ' h i hdom
  have hsp : ∀ p' : Cpt ξ', genPt A.ξ ⤳ h p'.1 := fun p' => (hdm p').choose
  have hreg : ∀ (p' : Cpt ξ'), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, i a ∈ regAt ξ' p' := fun p' => (hdm p').choose_spec.1
  have hun : ∀ (p' : Cpt ξ'), ∀ a ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩, unitAt ξ' p' (i a) → unitAt A.ξ ⟨h p'.1, hsp p'⟩ a :=
    fun p' => (hdm p').choose_spec.2 hgen'
  have hfib : ∀ (p : ℕ) (p' : Cpt ξ'), InFibre ξ' p p' ↔ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := by
    intro p p'
    refine not_congr ⟨fun hu => ?_, fun ⟨a, b, d⟩ => ?_⟩
    · have hr : (p : Ω) ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := natCast_mem _ p
      exact hun p' _ hr (by simpa using hu)
    · refine ⟨?_, ?_, ?_⟩
      · intro e; apply a; apply i.injective; simpa using e
      · simpa using hreg p' _ b
      · simpa using hreg p' _ d
  have hnoeth := (GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1
  have hnoeth' := (GlobalTheory.T.regAt_noetherian_model_noetherian Z Ω' ξ' ℤ _ _ htie).1
  have hic : ∀ q : Cpt A.ξ, IsIntegrallyClosed (A.X.presheaf.stalk q.1) := fun q => (A.normal q.1).2
  have hic' : ∀ q : Cpt ξ', IsIntegrallyClosed (Z.presheaf.stalk q.1) := fun q => (hnorm q.1).2
  have htors : ∀ p ∈ S, FullTorsion t'.G ξ' (p ^ A.R p) := fun p hp =>
    GlobalTheory.T.full_torsion_pullback A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ _ hdom mh.cart (A.tors p hp)
  have hint : ∀ (s) (q : Cpt A.ξ) (a : 𝓞 E), A.emb s a ∈ regAt A.ξ q := fun s q a =>
    GlobalTheory.T.integral_element_regular A.X Ω A.ξ q hgen (hic q) _ ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (A.emb s).toIntAlgHom)

  have hω : ∀ p ∈ S, ∀ p' : Cpt ξ', 0 < D.p + D.q → M'.htOm t'.PP.L (p ^ A.R p) p' =
      Submodule.span (regAt ξ' p') (jd '' (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩ : Set _)) := by
    intro p hp p' hpos
    have hN : 0 < p ^ A.R p := pow_pos (A.S_prime p hp).pos _
    obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c O β Y A.X A.f A.t A.m Ω A.ξ x hx
    obtain ⟨s0', o', ⟨m0'⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c O β Y Z (h ≫ A.f) t' mf Ω' ξ' (spMap i ≫ x) (by
      rw [← Category.assoc, hdom, Category.assoc, hx, Category.assoc])
    have hc1 : IsIntegrallyClosed (A.X.presheaf.stalk (h p'.1)) := hic ⟨h p'.1, hsp p'⟩
    have hn1 : IsNoetherianRing (A.X.presheaf.stalk (h p'.1)) := noeth_stalk hgen ⟨h p'.1, hsp p'⟩ (hnoeth _)
    have h1 := PositivityTheory.UnitarySelfGeneration.lattice_integrally_closed_torsion E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) ⟨h p'.1, hsp p'⟩ hgen hN
      (A.tors p hp) hc1 hn1
    have h1' := PositivityTheory.UnitarySelfGeneration.lattice_integrally_closed_torsion E H D l (KA l) (baseKA l) Z Ω' ξ' s0' o' t' m0' Li' M' (p ^ A.R p) p' hgen' hN
      (htors p hp) (hic' _) (noeth_stalk hgen' _ (hnoeth' _))
    have h2 := PositivityTheory.UnitarySelfGeneration.height_pullback_dominating_map A.X Z Ω Ω' A.ξ ξ' h i A.t.G t'.G mh.φ A.Li Li' A.M M' j hgen hgen' hdom mh.cart hsm hj jd hjd
      (p ^ A.R p) hN p' (hsp p') hc1 hn1 (h1.2.1 hpos) h1.1
    rw [h1'.2.2, h2, pull_eq ξ' h _ jd p' (hsp p'), h1.2.2]
  have hpos : ∀ s, 0 < labelRk D s → 0 < D.p + D.q := by
    intro s hs
    rcases s with τ | τ
    · have : 0 < D.p := hs
      omega
    · have : 0 < D.q := hs
      omega
  have hdual : ∀ p ∈ S, ∀ s, ∀ p' : Cpt ξ', InFibre ξ' p p' →
      M'.htDual t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) p' =
        Submodule.span (regAt ξ' p') (j '' (A.M.htDual A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) ⟨h p'.1, hsp p'⟩ : Set A.Li)) := by
    intro p hp s p' hf
    have hq := (hfib p p').1 hf
    obtain ⟨U, hU, b, hb, hfr⟩ := hvb p hp s ⟨h p'.1, hsp p'⟩ hq
    obtain ⟨hli, hbs⟩ := hfr ⟨h p'.1, hsp p'⟩ hq hU
    exact GlobalTheory.T.dual_lattice_basis_extension Ω Ω' i (regAt A.ξ ⟨h p'.1, hsp p'⟩) (regAt ξ' p') A.Li Li' j jd (A.Vgen s) _
      (A.M.htOm A.t.PP.L (p ^ A.R p) ⟨h p'.1, hsp p'⟩) (M'.htOm t'.PP.L (p ^ A.R p) p') (labelRk D s) b hext (hreg p') hjd
      (hW s) (fun hr => hω p hp p' (hpos s hr)) hli hb hbs
  have hhtw : ∀ p ∈ S, ∀ s, ∀ p' : Cpt ξ', InFibre ξ' p p' →
      M'.htW t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) (differentIdeal ℤ (𝓞 E)) p' =
        Submodule.span (regAt ξ' p')
          (j '' (A.M.htW A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) (differentIdeal ℤ (𝓞 E)) ⟨h p'.1, hsp p'⟩ : Set A.Li)) := by
    intro p hp s p' hf
    haveI := regAt_isLocalRing (ξ := A.ξ) ⟨h p'.1, hsp p'⟩
    obtain ⟨d₀, hd₀, hne, hdv⟩ := GlobalTheory.T.different_ideal_local_generator E Ω (regAt A.ξ ⟨h p'.1, hsp p'⟩) (A.emb s) (hint s _)
    exact GlobalTheory.T.different_scaled_lattice_extension Ω Ω' i (regAt A.ξ ⟨h p'.1, hsp p'⟩) (regAt ξ' p') A.Li Li' j (A.Vgen s) _ (𝓞 E) (A.emb s)
      (differentIdeal ℤ (𝓞 E)) d₀ (A.M.htDual A.t.PP.L (p ^ A.R p) A.ρ (A.emb s) ⟨h p'.1, hsp p'⟩)
      (M'.htDual t'.PP.L (p ^ A.R p) ρ' ((i.comp A.cst).comp (labelEmb c s)) p') hext (hreg p') (hW s) hd₀ hne hdv
      (fun e he => LieModel.mem_eigSp_of_mem_htDual _ _ _ _ _ he) (hdual p hp s p' hf)
  have hV : ∀ s, Lat.patch S (M'.eigLat ρ' ((i.comp A.cst).comp (labelEmb c s)))
      (fun p => htLabel M' t'.PP.L (p ^ A.R p) ρ' (fun s' => (i.comp A.cst).comp (labelEmb c s')) s) =
      (A.V s).pull ξ' h j := by
    intro s
    funext p'
    rw [pull_eq ξ' h _ j p' (hsp p')]
    by_cases hc : ∃ p ∈ S, InFibre ξ' p p'
    · obtain ⟨p, hp, hf⟩ := hc
      rw [Lat.patch_of_unique S _ _ hp hf fun p2 hp2 h2 =>
        inFibre_unique (A.S_prime p hp) (A.S_prime p2 hp2) hf h2]
      have e1 : A.V s ⟨h p'.1, hsp p'⟩ = A.HT p s ⟨h p'.1, hsp p'⟩ :=
        Lat.patch_of_unique S _ _ hp ((hfib p p').1 hf) fun p2 hp2 h2 =>
          inFibre_unique (A.S_prime p hp) (A.S_prime p2 hp2) ((hfib p p').1 hf) h2
      rw [e1]
      rcases s with τ | τ
      · exact hhtw p hp _ p' hf
      · exact hdual p hp _ p' hf
    · have hc' : ∀ p ∈ S, ¬ InFibre ξ' p p' := fun p hp hf => hc ⟨p, hp, hf⟩
      rw [Lat.patch_of_not S _ _ hc']
      have hc'' : ∀ p ∈ S, ¬ InFibre A.ξ p ⟨h p'.1, hsp p'⟩ := fun p hp hf => hc' p hp ((hfib p p').2 hf)
      have e1 : A.V s ⟨h p'.1, hsp p'⟩ = A.dR s ⟨h p'.1, hsp p'⟩ := Lat.patch_of_not S _ _ hc''
      rw [e1]
      have hdisc : (((NumberField.discr E : ℤ) : Ω))⁻¹ ∈ regAt A.ξ ⟨h p'.1, hsp p'⟩ := by
        have hn0 : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
        obtain ⟨-, -, hu⟩ := unitAt_natCast (ξ := A.ξ) ⟨h p'.1, hsp p'⟩ _ hn0 fun p hpp hd => by
          have hin := hS p hpp (Int.natCast_dvd.2 hd)
          exact not_not.1 (hc'' p hin)
        rcases Int.natAbs_eq (NumberField.discr E) with e | e
        · rw [e]; simpa using hu
        · rw [e]
          simpa using (regAt A.ξ ⟨h p'.1, hsp p'⟩).neg_mem hu
      show M'.lat p' ⊓ _ = _
      rw [hlat, pull_eq ξ' h _ j p' (hsp p')]
      exact GlobalTheory.T.lattice_eigen_field_extension E Ω Ω' i A.Li Li' j A.ρ ρ' (A.emb s) _ _ (A.M.lat ⟨h p'.1, hsp p'⟩) hext hρj (hreg p')
        (fun a e he => GlobalTheory.T.lie_lattice_stable_under_action A.X Ω A.ξ A.t.G A.Li A.M (𝓞 E) A.t.act A.ρ A.act _ a e he) (hint s _) hdisc
  have hvb' : ∀ s, (Lat.patch S (M'.eigLat ρ' ((i.comp A.cst).comp (labelEmb c s)))
      (fun p => htLabel M' t'.PP.L (p ^ A.R p) ρ' (fun s' => (i.comp A.cst).comp (labelEmb c s')) s)).IsVB (labelRk D s)
      (eigSp ρ' ((i.comp A.cst).comp (labelEmb c s))) := by
    intro s
    rw [hV s, hW s]
    have h3 := GlobalTheory.T.lattice_vector_bundle_pullback A.X Ω A.ξ A.Li Z Ω' ξ' h i Li' j (A.V s) Set.univ (labelRk D s) (A.Vgen s) hdom hext.1 hext.2
      (A.vb s)
    intro p' _
    obtain ⟨U, hU, b, hb, hfr⟩ := h3 p' ⟨hsp p', trivial⟩
    exact ⟨U, hU, b, hb, fun q _ hq => hfr q ⟨hsp q, trivial⟩ hq⟩
  have hvbt : ∀ p ∈ S, ∀ s, ((M'.htOm t'.PP.L (p ^ A.R p)).map
      (eigSp ρ' ((i.comp A.cst).comp (labelEmb c s))).dualRestrict).IsVBOn {q | InFibre ξ' p q} (labelRk D s) ⊤ := by
    intro p hp s
    exact GlobalTheory.T.lattice_flag_field_extension A.X Z Ω Ω' A.ξ ξ' h i A.Li Li' j jd (A.Vgen s) _ (A.M.htOm A.t.PP.L (p ^ A.R p))
      (M'.htOm t'.PP.L (p ^ A.R p)) {q | InFibre A.ξ p q} {q | InFibre ξ' p q} (labelRk D s) hdom hgen' hext hjd (hW s)
      (hvb p hp s) fun p' hf => ⟨hsp p', (hfib p p').1 hf, fun hr => hω p hp p' (hpos s hr)⟩
  let m' : SABMap t' A.t ((Iso.refl Z).hom ≫ h) :=
    { cm := mh.cm
      cart := by simpa using mh.cart
      base := by simpa using mh.base
      act := mh.act
      lin := mh.lin }
  refine ⟨{ X := Z, ξ := ξ', all := hall, tie := htie, normal := hnorm, f := h ≫ A.f, Ω₀ := A.Ω₀, ξ₀ := A.ξ₀,
            gen₀ := A.gen₀, cst := i.comp A.cst, cst_over := ?_, fn := i.comp A.fn, fn_over := ?_, t := t', m := mf,
            Li := Li', M := M', ρ := ρ', act := hρ', S_prime := A.S_prime, R := A.R, R_ge := A.R_ge, tors := htors,
            vb := hvb' }, Iso.refl Z, j, m', ?_, ?_, ?_, rfl, rfl, hext, hj, hvbt, ?_⟩
  · have e : ξ' ≫ h = spMap i ≫ A.ξ := hdom
    have e2 : ξ' ≫ h ≫ A.f ≫ Y.s = spMap i ≫ A.ξ ≫ A.f ≫ Y.s := by
      rw [← Category.assoc, e, Category.assoc]
    simp only [Category.assoc]
    rw [e2, A.cst_over]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · have := A.fn_over
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at this ⊢
    rw [← Category.assoc, hdom, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · simp
  · simp
  · exact hmf
  · intro s
    have e : (Iso.refl Z).hom ≫ h = h := Category.id_comp h
    refine (hV s).trans ?_
    exact congrArg (fun g => (A.V s).pull ξ' g j) e.symm

end GlobalTheory.CompanionTheory.Ar.HcptPullK

namespace PositivityTheory.UnitarySelfGeneration

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem hodge_compact_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (Z : Scheme.{0}) (ξ' : Sp Ω' ⟶ Z) (h : Z ⟶ A.X), A.ξ ≫ A.f = x ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, ∀ s, ((A.M.htOm A.t.PP.L (p ^ A.R p)).map (A.Vgen s).dualRestrict).IsVBOn {q | InFibre A.ξ p q} (labelRk D s) ⊤) → (∀ q : Z, genPt ξ' ⤳ q) → CoordTie ℤ ξ' (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) → IsNormalScheme Z → GlobalTheory.CompanionTheory.Ar.Dominates ξ' A.ξ h i → ∃ (A' : HodgeCpt Y S y') (e : A'.X ≅ Z) (j : A.Li →+ A'.Li) (m : SABMap A'.t A.t (e.hom ≫ h)), A'.ξ ≫ e.hom = ξ' ∧ A'.f = e.hom ≫ h ≫ A.f ∧ A'.m.φ = m.φ ≫ A.m.φ ∧ A'.cst = i.comp A.cst ∧ A'.R = A.R ∧ IsExtOver i j ∧ (∀ v, (A'.M.pt (j v)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt v).left) ∧ (∀ p ∈ S, ∀ s, ((A'.M.htOm A'.t.PP.L (p ^ A'.R p)).map (A'.Vgen s).dualRestrict).IsVBOn {q | InFibre A'.ξ p q} (labelRk D s) ⊤) ∧ ∀ s, A'.V s = (A.V s).pull A'.ξ (e.hom ≫ h) j :=
  @GlobalTheory.CompanionTheory.Ar.HcptPullK.hodgeCpt_pull

end PositivityTheory.UnitarySelfGeneration
