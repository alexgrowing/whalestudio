import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianVarietyCutOutBoundedDegreeTorsionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaSectionsVeryAmplePeriodicStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphismStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmpleStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.ZV

namespace GlobalTheory.EmbCut

theorem powIsLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) : (lbPow L n).IsLB :=
  DVR.linComb_isLB L hL _ _

theorem isoPullAlong {X Y : Scheme.{0}} {L M : LB X} (h : LBIso L M) (j : Y ⟶ X) : LBIso (L.pull j) (M.pull j) :=
  LBIso.chartPull (Geo.Tor.chartPullPull L j j rfl) (Geo.Tor.chartPullPull M j j rfl) h

theorem symB_of_iso {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hs : SymB L)
    {Y : Scheme.{0}} (e : Y ≅ A.left) {M : LB Y} (hM : M.IsLB) (N : ℕ) (h : LBIso M ((lbPow L N).pull e.hom)) :
    SymB (A := A) (M.pull e.inv) := by
  have h1 : LBIso (M.pull e.inv) (lbPow L N) :=
    LBIso.chartPull (Geo.Tor.chartPullPull M e.inv e.inv rfl) (Geo.Tor.chartPullSec _ e.hom e.inv e.inv_hom_id) h
  have hN := powIsLB hL N
  have hM' := Geo.Tor.pull_isLB hM e.inv
  obtain ⟨-, a, -, -, c, -⟩ := GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K A.left A.hom L hL
  exact LBIso.trans hM' hN (Geo.Tor.pull_isLB hM' _) h1 (LBIso.trans hN (Geo.Tor.pull_isLB hN _) (Geo.Tor.pull_isLB hM' _)
    (LBIso.trans hN (powIsLB (Geo.Tor.pull_isLB hL _) N) (Geo.Tor.pull_isLB hN _) ((a _ (Geo.Tor.pull_isLB hL _) hs).2 N) (c _ _ N))
    (isoPullAlong h1.symm _))

theorem sectionsHaveFiniteDimension_of_iso_pulled_pow {K : Type} [Field K] {X Y : Scheme.{0}} (p : X ⟶ Sp K) {L : LB X} (hL : L.IsLB)
    (e : Y ≅ X) {M : LB Y} (hM : M.IsLB) (N : ℕ) (h : LBIso M ((lbPow L N).pull e.hom)) (n r : ℕ)
    (hr : SectionsHaveFiniteDimension p (lbPow L (N * n)) r) : SectionsHaveFiniteDimension (e.hom ≫ p) (lbPow M n) r := by
  have hN := powIsLB hL N
  have h1 : SectionsHaveFiniteDimension p (lbPow (lbPow L N) n) r :=
    ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K X p _ (powIsLB hL (N * n))).2.1 _ (powIsLB hN n)
      ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K X p L hL).2.2.1 N n).symm).1 r hr
  have h2 := ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K X p _ (powIsLB hN n)).2.2.2.2.2 Y e r).1 h1
  have h3 : LBIso (lbPow M n) ((lbPow (lbPow L N) n).pull e.hom) :=
    LBIso.trans (powIsLB hM n) (powIsLB (Geo.Tor.pull_isLB hN _) n) (Geo.Tor.pull_isLB (powIsLB hN n) _)
      (((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K Y (e.hom ≫ p) M hM).2.1 _ (Geo.Tor.pull_isLB hN _) h).2 n)
      ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K X p _ hN).2.2.2.2.1 Y e.hom n)
  exact ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K Y (e.hom ≫ p) _ (Geo.Tor.pull_isLB (powIsLB hN n) _)).2.1 _ (powIsLB hM n) h3.symm).1 r h2

end GlobalTheory.EmbCut

namespace GlobalTheory

open EmbCut in

theorem cutBy_embedded_abelian : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)), ∃ (Hh : Type) (_ : Finite Hh) (hh : Hh → Ix g ((n ^ j) ^ 2)) (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p : Hh → Ix g ((n ^ j) ^ 2) → K), t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab (hh h) ^ n ^ j)).left (p h)) → CutBy (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) Q d p := by
  intro H H2 g J _ Mat κ n hn hodd
  have hn2 := hn.two_le
  haveI : NeZero ((n ^ 2) ^ 2) := ⟨by positivity⟩
  obtain ⟨d, k₀, hd⟩ := GlobalTheory.T.abelianVariety_cut_out_bounded_degree_torsion H H2 g ((n ^ 2) ^ 2) (Ix g ((n ^ 2) ^ 2))
  refine ⟨max 2 k₀, fun j hj o _ b => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨by positivity⟩
  have hdvd : n ^ 2 ∣ n ^ j := pow_dvd_pow n (le_of_max_le_left hj)
  have hdvd' : (n ^ 2) ^ 2 ∣ (n ^ j) ^ 2 := pow_dvd_pow_of_dvd hdvd 2
  obtain ⟨Q, hQ⟩ := hd _ le_rfl (Ix g ((n ^ j) ^ 2)) (fun a i => ZMod.castHom hdvd' (ZMod ((n ^ 2) ^ 2)) (a i))
    (fun c => by
      choose a ha using fun i => ZMod.castHom_surjective hdvd' (c i)
      exact ⟨a, funext ha⟩)
  refine ⟨Ix g ((n ^ j) ^ 2), inferInstance, id, Q, d, fun K _ _ β t σ p hE hp => ?_⟩
  obtain ⟨hiso, hM, hV, hL, hmod, -, hlab⟩ := GlobalTheory.T.thetaSections_veryAmple_periodic H H2 o g (n ^ j) J b K β t (n ^ 2) σ hodd.pow hdvd
    (by nlinarith) hE
  let e : (Over.mk (𝟙 (Sp K)) ⊗ t.A).left ≅ t.A.left := asIso (snd (Over.mk (𝟙 (Sp K))) t.A).left
  have he : e.hom ≫ t.A.hom = (fst (Over.mk (𝟙 (Sp K))) t.A).left :=
    pullback.condition.symm.trans (Category.comp_id _)
  have hk : ((n ^ j : ℕ) : K) ≠ 0 := fun h => by
    have := (b.unit.map β).ne_zero
    rw [map_natCast, Nat.cast_pow, h] at this
    exact this (by simp)
  have key := hQ K t.pol rfl _ e _ σ (n ^ j) _ (fun h => t.lab h ^ n ^ j) p hM
    (symB_of_iso t.isLB (GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample H H2 K t.pol).2.2.1 e hM _ hL) (he.symm ▸ hV)
    (fun a a' h => hmod a a' fun i => by
      have := congrFun h i
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa only [ZMod.castHom_apply, ZMod.natCast_val] using this)
    (fun m hm => sectionsHaveFiniteDimension_of_iso_pulled_pow t.A.hom t.isLB e hM _ hL m _ (by
      rw [← mul_pow]
      exact PowSec.exists_basis_sections H.globalSectionsRank K t.pol _ (Nat.mul_pos (by positivity) hm)))
    ((le_of_max_le_right hj).trans (Nat.lt_pow_self hn2).le) hk hlab
    (fun h => by
      have : (t.lab h ^ n ^ j).left ≫ e.inv = (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left := by
        rw [Iso.comp_inv_eq]
        exact (congrArg (fun q => q.left) (lift_snd (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j))).symm
      exact this.symm ▸ hp h)
  exact he ▸ key

end GlobalTheory
