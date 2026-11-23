import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNilpotentGroupChartSmoothCommGroup
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesReadingGroupHomNilpotentCharts
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HopfPointMem
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupChartFamilyStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateDatumReduceScalarsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedVarietyIntegerActionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianSchemeTorsionRepresentationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TrivialPolarizedAbelianPointEqOneStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

namespace GlobalTheory.CompanionTheory.Ar.GR.Top

theorem pt_eq_one_of_g_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (P : Out.PolAV (Spec (CommRingCat.of R))), P.g = 0 → ∀ z : sp (R₀ := R) R ⟶ P.A, z = 1 :=
  GlobalTheory.T.trivial_polarized_abelian_point_eq_one

theorem exists_cp (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C] (hv : v.Integers R)
    (hpv : v (p : C) < 1) :
    ∃ cp : R, v (algebraMap R C cp) ^ (p - 1) = v (algebraMap R C (p : R)) := by
  have h1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (p : C) h1
  have hle : v c ≤ 1 := by
    by_contra h
    push_neg at h
    have : 1 < v c ^ (p - 1) := one_lt_pow₀ h h1.ne'
    rw [← map_pow, hc] at this
    exact absurd hpv (not_lt.2 this.le)
  obtain ⟨r, hr⟩ := hv.exists_of_le_one hle
  exact ⟨r, by rw [hr, ← v.map_pow, hc, map_natCast (algebraMap R C)]⟩

theorem hopf_carrier_g_zero {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {R : Type} [CommRing R]
    [Algebra R C] (AA : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) R (Nb p 0)) :
    AA.carrier = ReciprocityTheory.PGsh.L2.intFun R (Nb p 0) := by
  let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
  refine le_antisymm AA.le_int fun f hf => ?_
  obtain ⟨r, hr⟩ := hf default
  have : f = r • (1 : Nb p 0 → C) := by
    funext x
    rw [Subsingleton.elim x default, ← hr]
    simp [Algebra.smul_def]
  rw [this]
  exact AA.carrier.smul_mem r AA.one_mem

theorem torsFun_one_eq {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {R : Type} [CommRing R]
    [Algebra R C] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] (T : TorsRep G p) :
    torsFun C T (fun _ : Nb p 0 => (1 : sp (R₀ := R) R ⟶ G)) = ReciprocityTheory.PGsh.L2.intFun R (Nb p 0) := by
  let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
  obtain ⟨φ₀, hφ₀, -⟩ := T.univ R (1 : sp (R₀ := R) R ⟶ G) (one_pow p)
  ext f
  constructor
  · rintro ⟨a, ha⟩ x
    exact ⟨φ₀ a, (ha x φ₀ hφ₀).symm⟩
  · intro hf
    obtain ⟨r, hr⟩ := hf default
    refine ⟨algebraMap R T.A r, fun x φ _ => ?_⟩
    rw [Subsingleton.elim x default, ← hr, AlgHom.commutes]
    rfl

theorem main : HodgeTateDatumStatement := by
  intro p _ C _ _ _ v R _ _ hv hp hcomp _ P
  haveI : IsLocalRing R := isLocal_of_integers hv
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  haveI : Fact ¬IsUnit (p : R) := ⟨fun hu => by
    have h1 := hv.one_of_isUnit hu
    rw [map_natCast] at h1
    rw [h1] at hp
    exact lt_irrefl _ hp⟩
  haveI : IsAdicComplete (Ideal.span {(p : R)}) R := hcomp
  haveI : IsCommMonObj P.A := P.isAb.comm
  have hT : Nonempty (TorsRep P.A p) :=
    GlobalTheory.T.abelian_scheme_torsion_representation R p (Fact.out : p.Prime).one_le P.A P.L P.isAb P.isLB P.ample
  refine ⟨hT, ?_⟩
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · obtain ⟨cp, hcp⟩ := exists_cp p hv hp
    have hpne : v (algebraMap R C (p : R)) ≠ 0 := by
      rw [map_natCast]
      exact fun h => Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero ((Valuation.zero_iff v).1 h)
    have hplt : v (algebraMap R C (p : R)) < 1 := by rwa [map_natCast]
    have hS : HodgeTateSetting p v R (ℤ_[p] ⊗[ℤ] ℤ) (sigE p ℤ) cp := by
      refine ⟨hv, hplt, hpne, hcp, ?_⟩
      intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        have h : ∀ (x : ℤ_[p]) (y : ℤ), sigE p ℤ (x ⊗ₜ[ℤ] y) = x ⊗ₜ[ℤ] star y := fun _ _ => rfl
        rw [h, h, star_star]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    obtain ⟨H⟩ := GlobalTheory.ChF.htd_dim_zero p C v R hv ℤ cp
    rw [← hg] at H
    obtain ⟨hS', H', -⟩ := GlobalTheory.T.hodge_tate_datum_reduce_scalars p P.g C v R (ℤ_[p] ⊗[ℤ] ℤ) (sigE p ℤ) cp hS H
    have h1 := pt_eq_one_of_g_zero R P hg
    revert H'
    rw [hg]
    intro H'
    refine ⟨cp, hS', H', fun _ => 1, ⟨?_, ?_, ?_⟩, fun T => ?_⟩
    · intro x y _
      let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
      exact Subsingleton.elim x y
    · intro x y
      exact (_root_.mul_one _).symm
    · intro z
      exact ⟨fun _ => ⟨0, (h1 z).symm⟩, fun _ => by rw [h1 z]; exact one_pow p⟩
    · rw [hopf_carrier_g_zero, torsFun_one_eq]
  · obtain ⟨F, X, hX⟩ := GlobalTheory.ChF.exists_nilChart R P.A P.g P.smoothDim
    obtain ⟨o⟩ := GlobalTheory.T.polarised_variety_integer_action R P
    have hα : ∀ a : ℤ, ∃ φ, Reads X X (o.act a) φ := fun a =>
      GlobalTheory.ChF.exists_reads R P.A P.A _ _ F.F F.F X X hX hX (o.act a) (o.hom a)
    choose α hα using hα
    obtain ⟨cp, hS, H, S, pt, -, -, -, -, -, hpt, hAA, -⟩ :=
      GlobalTheory.T.formal_group_chart_family p C v R hv P hg P.g rfl ℤ o F X hX α hα
    obtain ⟨hS', H', hAA', -⟩ := GlobalTheory.T.hodge_tate_datum_reduce_scalars p P.g C v R (ℤ_[p] ⊗[ℤ] ℤ) (sigE p ℤ) cp hS H
    exact ⟨cp, hS', H', pt, hpt, fun T => by rw [hAA']; exact hAA T⟩

end GlobalTheory.CompanionTheory.Ar.GR.Top
