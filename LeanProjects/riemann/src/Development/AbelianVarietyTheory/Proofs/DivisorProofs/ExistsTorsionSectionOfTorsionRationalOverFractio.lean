import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDeterminedAtGenericPoint
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsConst

theorem exists_factor_generic {R : Type} [CommRing R] [IsDomain R] {k : Type} [Field k] (τ : Sp k ⟶ Sp R)
    (w : Sp k) (hw : τ w = (⊥ : PrimeSpectrum R)) : ∃ κ : FractionRing R →+* k, τ = spMap κ ≫ jK R := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective τ
  have hφ : Function.Injective φ.hom := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : PrimeSpectrum.comap φ.hom w = ⊥ := hw
    have h2 : a ∈ (PrimeSpectrum.comap φ.hom w).asIdeal := by
      show φ.hom a ∈ (w : PrimeSpectrum k).asIdeal
      rw [ha]; exact Ideal.zero_mem _
    rw [h1] at h2
    exact h2
  refine ⟨IsFractionRing.lift hφ, ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext a
  simp

theorem exists_section_generic {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] {n : ℕ} (hA : IsAbelianScheme A) (hn : IsUnit (n : Γ(Sp R, ⊤)))
    (h : TorsRat A n) {K : Type} [Field K] [IsAlgClosed K] (κ : FractionRing R →+* K)
    (x : Over.mk (spMap κ ≫ jK R) ⟶ A) (hx : x ^ n = 1) :
    ∃ σ : 𝟙_ (Over (Sp R)) ⟶ A, σ ^ n = 1 ∧ toUnit _ ≫ σ = x := by
  obtain ⟨x₀, h₀⟩ := h K κ x hx
  let ρ : Over.mk (spMap κ ≫ jK R) ⟶ Over.mk (jK R) := Over.homMk (spMap κ) rfl
  have e₀ : x = ρ ≫ x₀ := Over.OverMorphism.ext h₀
  have hfl : Flat (spMap κ) := by
    letI := κ.toAlgebra
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hsu : Surjective (spMap κ) := ⟨fun p => ⟨Classical.arbitrary _, Subsingleton.elim (α := Sp (FractionRing R)) _ _⟩⟩
  have hepi : Epi ρ.left := Flat.epi_of_flat_of_surjective (spMap κ)
  have hx₀ : x₀ ^ n = 1 := by
    have : ρ ≫ x₀ ^ n = ρ ≫ 1 := by rw [MonObj.comp_pow, ← e₀, hx, MonObj.comp_one]
    exact Over.OverMorphism.ext ((cancel_epi ρ.left).1 congr(($this).left))
  have hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := fun p => by
    refine ⟨inferInstance, ?_⟩
    have : (PrimeSpectrum.asIdeal p).IsPrime := PrimeSpectrum.isPrime p
    have h := StructureSheaf.IsLocalization.to_stalk R p
    exact @isIntegrallyClosed_of_isLocalization R ((Spec.structureSheaf R).presheaf.stalk p) _ _ (_) _ _
      (PrimeSpectrum.asIdeal p).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _) h
  have j₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have j₂ : Flat (jK R) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have j₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    intro a ha
    have : a = 0 := IsFractionRing.injective R (FractionRing R) (ha.trans (map_zero _).symm)
    rw [this]; exact Ideal.zero_mem _)⟩
  have hp : IsProper A.hom := hA.proper
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_of_pow_eq_one hT (jK R) A n hn _ x₀ hx₀ (𝟙 _) (Category.id_comp _)
  let σ : 𝟙_ (Over (Sp R)) ⟶ A := Over.homMk s hs₁
  have e₁ : toUnit (Over.mk (jK R)) ≫ σ = x₀ := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, GlobalTheory.ObjPull.toUnit_left']
    exact hs₂.trans (Category.id_comp _)
  refine ⟨σ, ?_, ?_⟩
  · have : toUnit (Over.mk (jK R)) ≫ σ ^ n = toUnit (Over.mk (jK R)) ≫ 1 := by
      rw [MonObj.comp_pow, e₁, hx₀, MonObj.comp_one]
    apply Over.OverMorphism.ext
    have h2 := congr(($this).left)
    rw [Over.comp_left, Over.comp_left, GlobalTheory.ObjPull.toUnit_left'] at h2
    have : AlgebraicGeometry.IsReduced (𝟙_ (Over (Sp R))).left := inferInstanceAs (AlgebraicGeometry.IsReduced (Sp R))
    exact ext_of_isDominant_of_isSeparated A.hom (by rw [Over.w, Over.w]) (jK R) h2
  · rw [e₀, ← e₁, ← Category.assoc, comp_toUnit]

theorem exists_section_of_torsRat : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsIntegrallyClosed R₀] (A : Over (Sp R₀)) [GrpObj A] [IsCommMonObj A] (n : ℕ), IsAbelianScheme A → IsUnit (n : R₀) → TorsRat A n → ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ Sp R₀) (x : Over.mk t ⟶ A), x ^ n = 1 → ∃ σ : 𝟙_ (Over (Sp R₀)) ⟶ A, σ ^ n = 1 ∧ toUnit (Over.mk t) ≫ σ = x := by
  intro R _ _ _ _ A _ _ n hA hn h K _ _ t x hx
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion A hn'
  obtain ⟨y, hy, -⟩ := LatticeTorsion.existsUnique_torsion A n x hx
  obtain ⟨w⟩ : Nonempty (Sp K) := inferInstance
  have hs : (⊥ : PrimeSpectrum R) ⤳ (torsion A n).hom (y.left w) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨z, hz, ez⟩ := Flat.generalizingMap (torsion A n).hom hs
  let k := AlgebraicClosure ((torsion A n).left.residueField z)
  let u : Sp k ⟶ (torsion A n).left :=
    spMap (algebraMap ((torsion A n).left.residueField z) k) ≫ (torsion A n).left.fromSpecResidueField z
  obtain ⟨v⟩ : Nonempty (Sp k) := inferInstance
  have hu : u v = z := by
    have : u v ∈ Set.range ((torsion A n).left.fromSpecResidueField z) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rwa [Scheme.range_fromSpecResidueField] at this
  obtain ⟨κ, hκ⟩ := exists_factor_generic (u ≫ (torsion A n).hom) v
    ((Scheme.Hom.comp_apply _ _ _).trans (by rw [hu]; exact ez))
  let u' : Over.mk (spMap κ ≫ jK R) ⟶ torsion A n := Over.homMk u hκ
  obtain ⟨σ, hσ, eσ⟩ := exists_section_generic A hA hn' h κ (u' ≫ torsion.ι A n) (by
    rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one])
  obtain ⟨C, hC, hCz⟩ := TorsionCover.exists_clopen_eq_one A hA hn'
    (torsion.ι A n * (toUnit _ ≫ σ)⁻¹) (by
      rw [mul_pow, inv_pow, ← MonObj.comp_pow, hσ, MonObj.comp_one, LatticeTorsion.torsionι_pow_eq_one, inv_one,
        _root_.mul_one])
  have key : ∀ (T : Over (Sp R)) (a : T ⟶ torsion A n),
      a ≫ (torsion.ι A n * (toUnit _ ≫ σ)⁻¹) = 1 ↔ toUnit T ≫ σ = a ≫ torsion.ι A n := fun T a => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit, mul_inv_eq_one, eq_comm]
  have hzC : z ∈ C := (hCz _ u').1 ((key _ _).2 eσ) ⟨v, hu⟩
  have hyC : y.left w ∈ C := hz.mem_closed hC.isClosed hzC
  refine ⟨σ, hσ, ?_⟩
  rw [← hy]
  refine (key _ _).1 ((hCz _ y).2 ?_)
  rintro _ ⟨w', rfl⟩
  rwa [Subsingleton.elim (α := Sp K) w' w]

end GlobalTheory.TorsConst
