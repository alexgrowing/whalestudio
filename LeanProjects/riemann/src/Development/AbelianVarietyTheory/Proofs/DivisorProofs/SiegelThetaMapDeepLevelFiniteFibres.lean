import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesAndEndDeterminedTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescendStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialScaledFiniStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelThetaPointOfThetaConstantsLevelSquareStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjIsAbelianSchemeDimRigidifiedSym
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSiegelPointsE8ThetaPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegThQF

theorem sharpOver_of_polIso {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {K : Type} [Field K]
    {Q Q' : PolAV (Sp K)} {y : Sp K ⟶ F.X} (φ : Q'.A ≅ Q.A) (hφ : IsPolIso Q' Q φ) (h : GlobalTheory.Poinc.SharpOver F W Q y) :
    GlobalTheory.Poinc.SharpOver F W Q' y := by
  have := hφ.1
  obtain ⟨t, ht⟩ := hφ.2
  have h1 : LBIso Q'.L (Q.L.pull φ.hom.left) := LBIso.symm ⟨t, ht⟩
  simpa using GlobalTheory.Poinc.sharpOver_pullback g n _ _ F W _ _ Q Q' y (𝟙 _) φ.hom.left h (isGrpPullback_of_iso φ) h1

theorem finite_sharp (g n : ℕ) (hn : 2 ≤ n) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W)
    (K : Type) [Field K] [IsAlgClosed K] (Q : PolAV (Sp K)) :
    Set.Finite {y : Sp K ⟶ F.X | GlobalTheory.Poinc.SharpOver F W Q y} :=
  GlobalTheory.T.finite_siegelPoints_e8ThetaPower g n (by omega) F W hW K Q

def ThData {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {K : Type} [Field K] (y : Sp K ⟶ F.X)
    (h m : ℕ) (ze : Γ(Sp K, ⊤)ˣ) (v : (Fin (2 * h) → ZMod (m ^ 2)) → Γ((baseOver (Sp K)).left, ⊤)) : Prop :=
  ∃ (Q : PolAV (Sp K)) (hg : Q.g = h) (lev : Out.Level Q (m ^ 2) ze),
    GlobalTheory.Poinc.SharpOver F W Q y ∧ IsThetaPt Q m (levelPoint lev hg) v

theorem finite_thData {g n : ℕ} (hn : 2 ≤ n) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W)
    (ℓ h j : ℕ) (hℓ : ℓ.Prime) (ho : Odd ℓ) (hj : 4 ≤ j) (hbig : ((ℓ ^ 2) ^ 2) ^ h * h.factorial < ℓ ^ j)
    (K : Type) [Field K] [IsAlgClosed K] (hl : ((ℓ : ℕ) : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ)
    (v : (Fin (2 * h) → ZMod ((ℓ ^ j) ^ 2)) → Γ((baseOver (Sp K)).left, ⊤)) :
    Set.Finite {y : Sp K ⟶ F.X | ThData F W y h (ℓ ^ j) ze v} := by
  by_cases hne : ∃ y₀ : Sp K ⟶ F.X, ThData F W y₀ h (ℓ ^ j) ze v
  · obtain ⟨y₀, Q₀, hg₀, lev₀, -, hθ₀⟩ := hne
    refine (finite_sharp g n hn F W hW K Q₀).subset ?_
    rintro y ⟨Q, hg, lev, hS, hθ⟩
    have hN' : ℓ ^ j = ℓ ^ (j - 4) * (ℓ ^ 2) ^ 2 := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    obtain ⟨φ, hφ, -⟩ := (GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion).1 h ℓ 2 (j - 4) ((ℓ ^ 2) ^ 2) (ℓ ^ j)
      hℓ ho le_rfl rfl hN' hbig K hl Q₀ Q hg₀ hg ze lev₀ lev v hθ₀ hθ
    exact sharpOver_of_polIso φ hφ hS
  · convert Set.finite_empty
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hy => hne ⟨y, hy⟩

theorem finite_fibres : ∀ (ℓ : ℕ), ℓ.Prime → Odd ℓ → ∀ (g : ℕ), ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ℓ ∣ n → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig (ℓ ^ j) f → QFin f := by
  intro ℓ hℓ ho g
  refine ⟨4 + ((ℓ ^ 2) ^ 2) ^ (8 * g) * (8 * g).factorial, fun j hj n _ hn3 _ F W hW _ P rig N f hth K _ _ x => ?_⟩
  obtain ⟨hPg, hSh, hrig, hmo, -, hmu, hN, -, hmap⟩ := hth
  have hn : 2 ≤ n := by omega
  have hj4 : 4 ≤ j := by omega
  have hbig : ((ℓ ^ 2) ^ 2) ^ (8 * g) * (8 * g).factorial < ℓ ^ j :=
    lt_of_lt_of_le (by omega : ((ℓ ^ 2) ^ 2) ^ (8 * g) * (8 * g).factorial < j) (Nat.lt_pow_self hℓ.one_lt).le
  obtain ⟨β0, -⟩ := GlobalTheory.ThetaQuasiFinite.exists_spMap (x ≫ F.s)
  have hm0 : ((ℓ ^ j : ℕ) : K) ≠ 0 := by
    have := hmu.map β0
    rw [map_natCast] at this
    exact this.ne_zero
  have hl0 : ((ℓ : ℕ) : K) ≠ 0 := fun h0 => hm0 (by rw [Nat.cast_pow, h0, zero_pow (by omega)])
  have hpos : 0 < (ℓ ^ j) ^ 2 := pow_pos (pow_pos hℓ.pos _) _
  haveI : NeZero (((ℓ ^ j) ^ 2 : ℕ) : K) := ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ hm0⟩
  obtain ⟨z0, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ((ℓ ^ j) ^ 2)
  let eK := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  have hz' := hz.map_of_injective eK.injective
  set ze : Γ(Sp K, ⊤)ˣ := (hz'.isUnit hpos.ne').unit with hzedef
  have hze : IsPrimitiveRoot ze ((ℓ ^ j) ^ 2) := hz'.isUnit_unit hpos.ne'
  obtain ⟨⟨e, he⟩, -⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_basic_properties).2.2 (cycAway n) K N (x ≫ f)
  obtain ⟨T, hT⟩ := GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_scaled_finite K (N + 1) e
  haveI := P.isAb.comm
  haveI : NeZero ((ℓ ^ j) ^ 2) := ⟨hpos.ne'⟩
  refine (Set.finite_iUnion fun d : T × ((Fin (2 * (8 * g)) → ZMod ((ℓ ^ j) ^ 2)) → Fin (N + 1)) =>
    finite_thData hn F W hW ℓ (8 * g) j hℓ ho hj4 hbig K hl0 ze
      (fun a => GlobalTheory.ZH.fn ((d.1 : Fin (N + 1) → K) (d.2 a)))).subset ?_
  intro y hy
  have hy' : y ≫ f = x ≫ f := hy
  obtain ⟨Q, α, hQg, hpb, hQL⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.abelianSchemeLaws_all.1.polBaseChange y P
  have hQg' : Q.g = 8 * g := hQg.trans hPg
  have hfib : PolFib P.A P.L (8 * g) (y ≫ 𝟙 F.X) := ⟨Q, α, hQg', by rwa [Category.comp_id], hQL⟩
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable _ P.A P.L P.isLB (8 * g) K _ hfib
  obtain ⟨pt, cy, hcy⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ P.A P.L rig P.isLB hrig (8 * g) (ℓ ^ j) (N + 1) K _ θ hmo hm0 hN hfib
  have hH : HasTh P.A P.L rig (ℓ ^ j) (y ≫ 𝟙 F.X) cy := ⟨θ, pt, hθ, hcy⟩
  have hP1 : PCrd (y ≫ f) (symTup cy) := hmap.1 K y cy hH
  rw [hy'] at hP1
  obtain ⟨a, ha0, ha⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend).2.1 (cycAway n) K N (x ≫ f) e (symTup cy) he hP1
  obtain ⟨mu, hmu0, hmuT⟩ := hT cy a ha0 ha
  haveI := Q.isAb.comm
  obtain ⟨rigQ, hrigQ⟩ := Q.rigid
  have hQ : HasTh Q.A Q.L rigQ (ℓ ^ j) (𝟙 (Sp K)) cy := by
    rw [hasTh_iff] at hH ⊢
    refine (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ P.A P.L rig P.isLB hrig (Sp K) Q.A Q.L rigQ y α Q.isLB hrigQ hpb hQL (ℓ ^ j) (ℓ ^ j)
      (N + 1) (N + 1) K (𝟙 _) cy cy).2 ?_
    simpa only [Category.id_comp, Category.comp_id] using hH
  obtain ⟨lev, β, hβ⟩ := GlobalTheory.T.exists_level_thetaPoint_of_thetaConstants_level_square K Q rigQ (8 * g) (ℓ ^ j) (N + 1) hQg' cy ze hrigQ hmo hm0 hze hQ
  have hSQ : GlobalTheory.Poinc.SharpOver F W Q y := by
    simpa using GlobalTheory.Poinc.sharpOver_pullback g n _ _ F W _ _ P Q (𝟙 F.X) y α hSh hpb hQL
  exact Set.mem_iUnion.2 ⟨(⟨_, hmuT⟩, β), Q, hQg', lev, hSQ, hβ mu hmu0⟩

end GlobalTheory.SiegThQF
