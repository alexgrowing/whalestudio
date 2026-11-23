import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLevelOverIntegers
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSiegPre
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPrincipalLift
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsZpRingHomIntegers
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilySRep
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianLift

private theorem exists_odd_prime_ne (p : ℕ) : ∃ n : ℕ, n.Prime ∧ Odd n ∧ n ≠ p := by
  by_cases h : p = 3
  · exact ⟨5, by norm_num, by decide, by omega⟩
  · exact ⟨3, by norm_num, by decide, fun e => h e.symm⟩

theorem exists_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* O) (P : Out.PolAV (Geo.Tor.Sp O)) (φ : P.A.left ⟶ P₀.A.left), Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ → Geo.Tor.LBIso P.L (P₀.L.pull φ) → P.g = P₀.g → 1 ≤ P.g → ∀ (R' : Type) [CommRing R'] (π : R' →+* O), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∃ (G : Over (Spec (CommRingCat.of R'))) (_ : GrpObj G) (_ : IsCommMonObj G) (Q : LB (G ⊗ G).left) (ψ : P.A.left ⟶ G.left) (ψ₂ : (P.A ⊗ P.A).left ⟶ (G ⊗ G).left), IsAbelianScheme G ∧ Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧ (∃ t : (Q.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) ∧ Geo.Tor.LBIso Q (Q.pull (lift (snd G G) (fst G G)).left) ∧ Out.RelAmple G (Q.pull (lift (𝟙 G) (𝟙 G)).left) ∧ (∀ (Z : Over (Spec (CommRingCat.of R'))) (x : Z ⟶ G), (∃ t : (Q.pull (lift (snd G Z ≫ x) (fst G Z)).left).Gen, t.IsGen) → x = 1) ∧ Geo.Tor.IsGrpPullback P.A G (Spec.map (CommRingCat.ofHom π)) ψ ∧ Geo.Tor.IsSquare ψ ψ₂ ∧ Geo.Tor.LBIso (abelian₂ P.A P.L) (Q.pull ψ₂) := by
  intro p _ C _ _ _ v O _ _ hv _ _ T _ _ P₀ io P φ hφ hL hg h1 R' _ π hπ hker
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have : IsDomain O := hinj.isDomain _
  have : IsLocalRing O := by
    have : ValuationRing O := ValuationRing.of_integers v hv
    infer_instance
  obtain ⟨n, hn, hodd, hnp⟩ := exists_odd_prime_ne p
  obtain ⟨j, hj⟩ := GlobalTheory.ZM.SiegelLargeLevel.exists_siegelFamily_sRep GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1
    GlobalTheory.AbLaw.CubeAssembly.cube_gen GlobalTheory.thetaUnifAV_all P.g n h1 hn hodd
  obtain ⟨Ag, hAg⟩ := hj j le_rfl p hp hnp
  have hM0 : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  have hcop : ((n ^ j) ^ 2).Coprime p :=
    Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ ((Nat.coprime_primes hn hp).2 hnp))
  generalize (n ^ j) ^ 2 = M at Ag hAg hM0 hcop
  obtain ⟨β, hβ, hMu, hprim⟩ := GlobalTheory.exists_zp_ringHom_integers p C v O hv M hM0 hcop
  have hζ : β (Geo.Tor.zetaZP p M) ^ M = 1 := hinj (by
    rw [map_pow, map_one]; exact (hprim C (algebraMap O C)).pow_eq_one)
  let ze : Oˣ := (IsUnit.of_pow_eq_one hζ hM0).unit
  have hze : (ze : O) = β (Geo.Tor.zetaZP p M) := rfl
  obtain ⟨lev, hl₁, hl₂, hl₃⟩ := GlobalTheory.exists_level_over_integers p C v O hv T P₀ io P φ hφ hL hg P.g M ze rfl hMu
    (hprim C (algebraMap O C))
  obtain ⟨c, e, he, hc, hcP⟩ := GlobalTheory.SiegelOverLocal.exists_siegPre O T P₀ io P φ hφ hL hg _ β P.g M (Geo.Tor.zetaZP p M) ze lev rfl hMu hze
    hprim hl₁ hl₂ hl₃
  obtain ⟨β', c', hc', φ₁, φ₂, hpb, hsq, hiso, -⟩ :=
    GlobalTheory.SiegelLift.exists_principal_lift P.g p M Ag hAg hcop hM0 O R' π hπ hker β hβ c hc
  let k : P.A ⊗ P.A ⟶ c.A ⊗ c.A := lift (fst P.A P.A ≫ e.inv) (snd P.A P.A ≫ e.inv)
  have hk : k.left ≫ (lift (fst c.A c.A ≫ e.hom) (snd c.A c.A ≫ e.hom)).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Over.id_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [k]
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  refine ⟨c'.A, c'.grp, c'.comm, c'.P, e.inv.left ≫ φ₁, k.left ≫ φ₂, c'.ab, c'.isLB, c'.rig₁, c'.rig₂, c'.symm,
    hc'.1, hc'.2, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact ((Geo.Tor.isGrpPullback_of_iso e.symm).comp hpb).congr (Category.id_comp _) rfl
  · rw [Category.assoc, hsq.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst]
  · rw [Category.assoc, hsq.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd]
  · have hA : Geo.Tor.LBIso (abelian₂ P.A P.L) (c.P.pull k.left) :=
      Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullSec _ _ k.left hk) (Geo.Tor.chartPullPull c.P k.left k.left rfl)
        hcP.symm
    have hB : Geo.Tor.LBIso (c.P.pull k.left) (c'.P.pull (k.left ≫ φ₂)) :=
      Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullPull c.P k.left k.left rfl)
        (Geo.Tor.chartPullSame c'.P _ (fun _ => φ₂) _ k.left fun _ => rfl) hiso
    exact Geo.Tor.LBIso.trans (DVR.linComb_isLB _ P.isLB _ _) (Geo.Tor.pull_isLB c.isLB _)
      (Geo.Tor.pull_isLB c'.isLB _) hA hB

end GlobalTheory.AbelianLift
