import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfPeriod
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleAdjointOfWeilPairingAdjointStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalTorusAlgebraic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfMapLattice
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUnifOfParts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaUnifAVOfLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open PeriodPoint

theorem exists_obj_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → ∀ l : Level H, ∃ (b : Base l ℂ) (o : Obj D l b (𝟙 (Sp ℂ))), b.ρ = H.rt0 ∧ b.ζ = zeta l.A ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G, x ≠ 1 := by
  intro E _ _ _ H D hpq l
  have laws : Out.Laws := GlobalTheory.T.abelianScheme_laws_unconditional.1
  obtain ⟨g, ty, hty, hg, P, hP⟩ := PeriodExists.exists_typeFn_period H D
  obtain ⟨t, -, -, f, ν, htow, hiso, hsim, hζ, -⟩ := UnifParts.exists_inGenus D l (KA l).val.toRingHom
    fun l' N ν a b c =>
      (SimMult.exists_sim_trivial_of_mult SimAlg.sim_group exists_sim_lift E H D l' N ν a b c).imp fun _ h => h.1
  replace hζ : zeta l.A = _ := hζ
  obtain ⟨T, L, u, hA, hdim, hamp, hK, ht₁, ht₂, hker, hact, hW⟩ :=
    exists_triple laws GlobalTheory.T.theorem_of_cube_polAbelianScheme principalTorus_algebraic
      (exists_isMonHom_of_map_lattice (thetaUnifAV_of_laws laws.cube laws.mulN laws.weil laws.weilNondeg laws.globalSectionsRank)
        laws) (GlobalTheory.T.lambdaBundle_adjoint_of_weilPairing_adjoint laws) (PrimNorm.exists_primitive_normalisation laws.globalFns) (kTriv_of_descent laws)
      relAmple_finite_pow_iso D ty P hP
  let Q : Out.PolAV (Sp ℂ) :=
    { A := T.G, isAb := hA, g := g, smoothDim := hdim, L := T.PP.L, isLB := T.PP.isLB,
      rigid := ⟨T.PP.rig, T.PP.rigGen⟩, sym := CechPic.sym_of_isSymmetric T.PP T.sym, ample := hamp, ktriv := hK }
  obtain ⟨v, hv, heig⟩ := exists_lieBasis_of_holUnif T.G L g u hA.smooth ht₁ ht₂
  have hmul : ∀ (n : ℕ) a, 0 < n → u.ex ((n : ℂ)⁻¹ • P (n • a)) = 1 := fun n a hn => by
    rw [hker, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
    exact ⟨a, rfl⟩
  have hadd : ∀ (n : ℕ) a b, u.ex ((n : ℂ)⁻¹ • P (f n (a + b))) =
      u.ex ((n : ℂ)⁻¹ • P (f n a)) * u.ex ((n : ℂ)⁻¹ • P (f n b)) := fun n a b => by
    rw [map_add, map_add, smul_add, u.ex_add]
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨κ, hκ₁, hκ₂, hκ₃⟩ := exists_halfLevel (D := D) l (fun a => u.ex ((l.M : ℂ)⁻¹ • P (f l.M a))) (hadd l.M)
    fun b => by rw [map_nsmul, hmul _ _ hM]
  let b : Base l ℂ :=
    { unit := fun n hn => IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')
      ρ := H.rt0
      ρ_sq := H.sqrt_neg_disc_sq
      ζ := zeta l.A
      ζ_prim := Complex.isPrimitiveRoot_exp l.A l.A_pos.ne' }
  let o : Obj D l b (𝟙 (Sp ℂ)) :=
    { t := T, proper := hA.proper, ample := hamp, ktriv := hK
      eta := κ, eta_add := hκ₁, eta_ker := hκ₂
      etaA := fun a => u.ex ((l.A : ℂ)⁻¹ • P (f l.A a))
      etaA_add := hadd l.A
      etaA_ker := fun a => by rw [map_nsmul, hmul _ _ l.A_pos]
      geom := fun k _ _ x β hx => by
        obtain rfl : x = spMap β := (Category.comp_id x).symm.trans hx
        refine ⟨?_, ?_⟩
        · exact detCond_of_eigenbasis lieMult_of_eigenbasis D T ty hty v hv
            (fun i a => heig _ _ (T.act.hom a) (hact a) i) β
        · obtain ⟨I, hI₁, hI₂⟩ := exists_tateIso_of_periods laws E H D D g ty P Q T.act u.ex f ν hpq hP u.ex_add
            u.ex_onto hker hact hW htow hiso hsim k β
          exact ⟨I, (hI₁ _).trans (congrArg β hζ.symm), fun a => (hI₂ _ a).symm,
            fun a ha => by rw [hκ₃ a ha]; exact (hI₂ _ a).symm⟩ }
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank]; omega)
  obtain ⟨a₀, b₀, h₀⟩ := PeriodTate.exists_pairing_one D
  refine ⟨b, o, rfl, rfl, hg ▸ hdim, u.ex ((2 : ℂ)⁻¹ • P a₀), fun h => ?_⟩
  obtain ⟨c, hc⟩ := (hker _).1 h
  have e : a₀ = 2 • c := hP.2.1 (by
    rw [map_nsmul, hc, ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_ofNat, smul_inv_smul₀ two_ne_zero])
  rw [e, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h₀
  omega

end GlobalTheory
