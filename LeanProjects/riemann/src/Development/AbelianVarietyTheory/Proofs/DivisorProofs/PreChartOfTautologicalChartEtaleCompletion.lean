import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdicCompletionTensorResidueField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongEqSpanMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XMemNonZeroDivisors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsRelParam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeCycAway
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChartPre

theorem essFiniteType_int_stalk (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp (cycAway n)) [LocallyOfFiniteType s] (x : X) :
    Algebra.EssFiniteType ℤ (X.presheaf.stalk x) := by
  have h1 : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  let p : PrimeSpectrum (cycAway n) := s x
  have h2 : (algebraMap (cycAway n) ((Spec.structureSheaf (cycAway n)).presheaf.stalk p)).EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  haveI := finiteType_cycAway n
  have h3 : (algebraMap ℤ (cycAway n)).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h4 := (h3.comp h2).comp h1
  rw [← RingHom.essFiniteType_algebraMap]
  convert h4
  exact RingHom.ext_int _ _

theorem eq_of_jK_comp_eq {R o : Type} [CommRing R] [IsDomain R] [CommRing o] {u v : Sp R ⟶ Sp o}
    (h : jK R ≫ u = jK R ≫ v) : u = v := by
  obtain ⟨u, rfl⟩ := Spec.map_surjective u
  obtain ⟨v, rfl⟩ := Spec.map_surjective v
  have h' : u ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) = v ≫ CommRingCat.ofHom (algebraMap R (FractionRing R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact h
  congr 1
  ext a
  exact IsFractionRing.injective R (FractionRing R) (congrArg (fun f => f.hom a) h')

theorem preChart_of_isEtaleCompletion : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue C.R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → PreChart F (π ≫ z) j φ BD d (ξ (closedPoint C.R)) := by
  intro g hg φ hφ _ n hn _ F Z z i OZ d S π j _ BD hM hB C G₁ _ _ y α₁ ξ hF hy het hfu
  obtain ⟨J, -, -, -, -, hP, -, hji, -, -, hval⟩ := hB
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨-, -, -, hiz, -⟩, -⟩ := hM
  obtain ⟨hsa, hab, hgen, hmum, hbase⟩ := hF
  obtain ⟨hreg, hch, -, -, hrel, -⟩ := GlobalTheory.TChart.Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  obtain ⟨hmono, hrk, hcone, hdef, -⟩ := GlobalTheory.TChart.Taut.monomial_chart g n φ (by omega) C
  haveI : IsProper (π ≫ z) := by
    obtain ⟨N, ιP, hιP, e⟩ := hP
    rw [← e]
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (cycAway n) N
    infer_instance
  haveI : S.IsSeparated := ⟨by
    rw [← terminal.comp_from (π ≫ z)]
    infer_instance⟩
  haveI : Algebra.EssFiniteType ℤ (S.presheaf.stalk (ξ (closedPoint C.R))) :=
    essFiniteType_int_stalk n S (π ≫ z) _
  haveI : IsNoetherianRing C.R := C.compl.1
  have hc : IsAdicComplete (maximalIdeal C.R) C.R := C.compl.2.1
  have hξ : ξ ≫ π ≫ z = spMap C.b := eq_of_jK_comp_eq (by
    rw [← hbase, ← Category.assoc, ← hy, Category.assoc, ← Category.assoc j, hji, hiz])
  have hrad := GlobalTheory.EtaleCompletionRadical.isRadical_map_of_isEtaleCompletion _ _ (Scheme.stalkClosedPointTo ξ).hom hc het hfu
  obtain ⟨hb₁, hb₂⟩ := GlobalTheory.BdEqChart.boundary_eq g n F S j C.R C.b ξ G₁ y ((Over.pullback (jK C.R)).obj G₁)
    (pullback.fst G₁.hom (jK C.R)) α₁ hsa (isGrpPullback_pullback G₁ (jK C.R)) hgen hy hrad C.m C.t hrel hab
  haveI : Module.Free ℤ C.Q.X := Module.Free.of_equiv C.e.toIntLinearEquiv.symm
  have hnat : ∀ k, ∃ c : ℕ, φ.evalZ ((n : ℤ) • C.δ k) = c := fun k =>
    (hφ C.Q.X hrk).exists_nat (Submodule.smul_mem _ _ (hcone.mem k)) fun w =>
      mul_nonneg (Int.natCast_nonneg n) (hcone.nonneg k w)
  choose c hcn using hnat
  have ha : ∀ k, ((d * c k : ℕ) : ℝ) = d * φ.evalZ ((n : ℤ) • C.δ k) := fun k => by rw [hcn, Nat.cast_mul]
  have hBD := GlobalTheory.ChartIdeal.idlAlong_eq_span_monomial g n F S j φ hφ d BD.idealSheaf hval C.R hc C.b ξ C.Q G₁ y α₁ hsa hgen
    hy.symm hmum C.m C.t C.δ (fun k => d * c k) hrel hab hcone hdef hmono ha
  exact ⟨C.R, inferInstance, hreg, inferInstance, C.b, ξ, C.m, C.t, C.Q, C.δ, fun k => d * c k, G₁, inferInstance, y, α₁,
    ⟨hc, hch, hξ, rfl, het, hfu⟩, ⟨hrel, hb₂, hb₁⟩, ⟨hsa, hab, hy, hgen⟩, ⟨hmum, hrk, hcone, hdef, hmono⟩, ha, hBD⟩

end GlobalTheory.TChartPre
