import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsAdmissibleSmoothingFactorAddIntVector
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.NormalModularTowerTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.AlgEquivMemRingOfIntegersModularTowerTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.MemRingOfIntegersModularTowerTopOfForallValuatio
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.ExistsIsLocallyConstantLiftToGeometricGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.ValuationSiegelUnitLevelEqOne
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassEqKummerCharacterOfChosenRootFunctionFiStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCupProductCoboundaryTheoremStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalLevStatement
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L GlobalTheory.KEdge GlobalTheory.NeedB Polynomial
attribute [local instance] algMdl algPoly algRat

namespace UpperTheory.Kd.L.KummerExtensionIntegrality

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem resGeo {F K Kb : Type} [Field F] [Field K] [Field Kb] [Algebra F K] [Algebra F Kb] [Algebra K Kb] [IsScalarTower F K Kb]
    (g : Kb ≃ₐ[F] Kb) (hg : g ∈ geo F K Kb) : ∃ g' : Kb ≃ₐ[K] Kb, ∀ z, g' z = g z :=
  ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun a => (TopW.mem_geo g).1 hg a, fun _ => rfl⟩

private theorem kumRes {F K Kb : Type} [Field F] [Field K] [Field Kb] [Algebra F Kb] [Algebra K Kb] {N : ℕ} (ζ θ : Kb)
    {g : Kb ≃ₐ[F] Kb} {g' : Kb ≃ₐ[K] Kb} (h : ∀ z, g' z = g z) : kum (K := K) (N := N) ζ θ g' = kum (K := F) (N := N) ζ θ g := by
  have e := h θ
  unfold kum
  generalize g' θ = a at e ⊢
  subst e
  rfl

private theorem constInt (X : Tower Ω ε) (M : ℕ) (f : topL X M) (h : (f : X.K) = X.jK ∨ (f : X.K) ∈ Set.range (algebraMap Ω X.K)) :
    f ∈ FunctionField.ringOfIntegers Ω (topL X M) := by
  have key : ∃ P : Polynomial Ω, algebraMap (Polynomial Ω) (topL X M) P = f := by
    rcases h with h | ⟨c, h⟩
    · refine ⟨Polynomial.X, Subtype.ext ?_⟩
      show ((jPoly X _ Polynomial.X : topL X M) : X.K) = _
      rw [coe_jPoly, Polynomial.aeval_X, h]
    · refine ⟨Polynomial.C c, Subtype.ext ?_⟩
      show ((jPoly X _ (Polynomial.C c) : topL X M) : X.K) = _
      rw [coe_jPoly, Polynomial.aeval_C, h]
  obtain ⟨P, rfl⟩ := key
  exact isIntegral_algebraMap

private theorem polyMem (X : Tower Ω ε) (M : ℕ) (B : ValuationSubring (topBar X M))
    (hB : ∀ f : topL X M, ((f : X.K) = X.jK ∨ (f : X.K) ∈ Set.range (algebraMap Ω X.K)) → algebraMap (topL X M) (topBar X M) f ∈ B)
    (P : Polynomial Ω) : algebraMap (topL X M) (topBar X M) (algebraMap (Polynomial Ω) (topL X M) P) ∈ B := by
  have hC : ∀ c : Ω, algebraMap (topL X M) (topBar X M) (algebraMap (Polynomial Ω) (topL X M) (Polynomial.C c)) ∈ B := fun c =>
    hB _ (Or.inr ⟨c, by
      show _ = ((jPoly X _ (Polynomial.C c) : topL X M) : X.K)
      rw [coe_jPoly, Polynomial.aeval_C]⟩)
  have hX : algebraMap (topL X M) (topBar X M) (algebraMap (Polynomial Ω) (topL X M) Polynomial.X) ∈ B :=
    hB _ (Or.inl (by
      show ((jPoly X _ Polynomial.X : topL X M) : X.K) = _
      rw [coe_jPoly, Polynomial.aeval_X]))
  induction P using Polynomial.induction_on with
  | C a => exact hC a
  | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul]
    exact mul_mem h hX

private theorem memOfInt (X : Tower Ω ε) (M : ℕ) (B : ValuationSubring (topBar X M))
    (hB : ∀ f : topL X M, ((f : X.K) = X.jK ∨ (f : X.K) ∈ Set.range (algebraMap Ω X.K)) → algebraMap (topL X M) (topBar X M) f ∈ B)
    (x : topL X M) (hx : x ∈ FunctionField.ringOfIntegers Ω (topL X M)) : algebraMap (topL X M) (topBar X M) x ∈ B := by
  obtain ⟨p, hp, hev⟩ : IsIntegral (Polynomial Ω) x := hx
  let φ : Polynomial Ω →+* B :=
    ((algebraMap (topL X M) (topBar X M)).comp (algebraMap (Polynomial Ω) (topL X M))).codRestrict B.toSubring
      (fun P => polyMem X M B hB P)
  have hφ : (algebraMap B (topBar X M)).comp φ = (algebraMap (topL X M) (topBar X M)).comp (algebraMap (Polynomial Ω) (topL X M)) := rfl
  have hi : IsIntegral B (algebraMap (topL X M) (topBar X M) x) := by
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map, hφ, ← Polynomial.hom_eval₂, hev, map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  rw [← hy]
  exact y.2

private theorem topexOf [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M l n : ℕ} (hM : M ≠ 0) (hl : l ≠ 0) (hd : l ^ n ∣ M) {u v : X.K}
    (hu : u ∈ topF X M) (hv : v ∈ topF X M) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hW : ∀ W : ValuationSubring X.K, X.OverY W → W.valuation u = 1 ∧ W.valuation v = 1) :
    IsTopEta X M (topChar X M l n u) (topChar X M l n v) (topEta X M (topChar X M l n u) (topChar X M l n v)) ∧
      ∀ σ : topGal X M, ∃ w : topL X M, IsTopW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
        (topEta X M (topChar X M l n u) (topChar X M l n v)) σ w := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl⟩
  haveI := isScalarTower_poly_rat X (CongruenceSubgroup.Gamma M)
  haveI : FiniteDimensional (RatFunc Ω) (topL X M) := GlobalTheory.T.finiteDimensional_lev_of_gamma_le Ω ε X _ M (Nat.pos_of_ne_zero hM) le_rfl
  haveI : Normal (topF X M) (topL X M) := UpperTheory.normal_modularTowerTop X hM
  haveI : Algebra.IsAlgebraic (topF X M) (topBar X M) := Algebra.IsAlgebraic.trans (topF X M) (topL X M) (topBar X M)
  have hN : 0 < l ^ n := pow_pos (Nat.pos_of_ne_zero hl) n
  have hζ := isPrimitiveRoot_topZeta X M hl n
  have hfix := topGal_topZeta X hl hd
  let a : topL X M := ⟨u, mdl_le_lev X _ _ hu⟩
  let b : topL X M := ⟨v, mdl_le_lev X _ _ hv⟩
  let aF : topF X M := ⟨u, hu⟩
  let bF : topF X M := ⟨v, hv⟩
  have ha0 : a ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  have hb0 : b ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have haF0 : aF ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  have hbF0 : bF ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hpl : ∀ W : ValuationSubring X.K, X.OverY W → ∀ z : X.K, W.valuation z = 1 → z ∈ W ∧ z⁻¹ ∈ W := fun W _ z hz =>
    ⟨(W.valuation_le_one_iff z).1 hz.le, (W.valuation_le_one_iff _).1 (by rw [map_inv₀, hz, inv_one])⟩
  have hai : a ∈ FunctionField.ringOfIntegers Ω (topL X M) := UpperTheory.mem_ringOfIntegers_modularTowerTop_of_forall_valuation X M a fun W hw => (hpl W hw u (hW W hw).1).1
  have hbi : b ∈ FunctionField.ringOfIntegers Ω (topL X M) := UpperTheory.mem_ringOfIntegers_modularTowerTop_of_forall_valuation X M b fun W hw => (hpl W hw v (hW W hw).2).1
  have hai' : a⁻¹ ∈ FunctionField.ringOfIntegers Ω (topL X M) := UpperTheory.mem_ringOfIntegers_modularTowerTop_of_forall_valuation X M a⁻¹ fun W hw => (hpl W hw u (hW W hw).1).2
  have hbi' : b⁻¹ ∈ FunctionField.ringOfIntegers Ω (topL X M) := UpperTheory.mem_ringOfIntegers_modularTowerTop_of_forall_valuation X M b⁻¹ fun W hw => (hpl W hw v (hW W hw).2).2
  have hα : topRoot X M (l ^ n) u ^ (l ^ n) = algebraMap (topL X M) (topBar X M) a := topRoot_pow X M hN.ne' _
  have hβ : topRoot X M (l ^ n) v ^ (l ^ n) = algebraMap (topL X M) (topBar X M) b := topRoot_pow X M hN.ne' _
  have hαF : topRoot X M (l ^ n) u ^ (l ^ n) = algebraMap (topF X M) (topBar X M) aF := by
    rw [hα, IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]; rfl
  have hβF : topRoot X M (l ^ n) v ^ (l ^ n) = algebraMap (topF X M) (topBar X M) bF := by
    rw [hβ, IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]; rfl
  have hx := topChar_apply X hl hd hu hu0
  have hy := topChar_apply X hl hd hv hv0
  obtain ⟨-, -, -, -, η₀, hlc, hcob, hin⟩ := GlobalTheory.T.kummerCupProduct_coboundary_theorem Ω (topL X M) (topBar X M) (l ^ n) (topZeta X M l n) hN hζ a b _ _ ha0 hb0
    hai hai' hbi hbi' hα hβ
  obtain ⟨η, hηlc, hηe⟩ := UpperTheory.exists_isLocallyConstant_lift_to_geometric_galois (F := topF X M) η₀ hlc
  have hex : ∃ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η := by
    refine ⟨η, ?_, hηlc, ?_⟩
    · intro g hg h hh
      obtain ⟨g', hg'⟩ := resGeo g hg
      obtain ⟨h', hh'⟩ := resGeo h hh
      have e1 := hηe g g' hg hg'
      have e2 := hηe h h' hh hh'
      have e3 := hηe (g * h) (g' * h') (mul_mem hg hh) fun z => by
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hg', hh']
      rw [e1, e2, e3, hx, hy, ← kumRes _ _ hg', ← kumRes _ _ hh']
      exact hcob g' h'
    · intro B g hB hI hg
      obtain ⟨g', hg'⟩ := resGeo g hg
      rw [hηe g g' hg hg']
      refine hin B (fun x hx => memOfInt X M B hB x hx) g' fun z hz => ?_
      rw [hg']
      exact hI z hz
  have hT := isTopEta_topEta X M hex
  refine ⟨hT, fun σ => ⟨topW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
        (topEta X M (topChar X M l n u) (topChar X M l n v)) σ, ?_⟩⟩
  exact GlobalTheory.T.edgeClass_eq_kummerCharacter_of_chosen_root_function_field Ω (topL X M) (topBar X M) (topF X M) (l ^ n) (topZeta X M l n) hN hζ hfix (UpperTheory.algEquiv_mem_ringOfIntegers_modularTowerTop X M) aF bF _ _ haF0 hbF0
    hai hai' hbi hbi' hαF hβF _ _ hx hy _ hT.1 hT.2.1
    (fun B g hB hI hg => hT.2.2 B g (fun f hf => hB _ (constInt X M f hf)) hI hg) σ

end UpperTheory.Kd.L.KummerExtensionIntegrality

theorem UpperTheory.Kd.L.topex :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (x : ZMod N) (m n : ℕ), 1 ≤ m → IsTopEta X (topMu l n m N) (topChar X (topMu l n m N) l n (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0))) (topChar X (topMu l n m N) l n (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ)))) (topEta X (topMu l n m N) (topChar X (topMu l n m N) l n (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0))) (topChar X (topMu l n m N) l n (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ))))) ∧ ∀ σ : topGal X (topMu l n m N), ∃ w : topL X (topMu l n m N), IsTopW (K := topL X (topMu l n m N)) (topZeta X (topMu l n m N) l n) (topChar X (topMu l n m N) l n (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0))) (topChar X (topMu l n m N) l n (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ)))) (topEta X (topMu l n m N) (topChar X (topMu l n m N) l n (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0))) (topChar X (topMu l n m N) l n (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ))))) σ w := by
  intro Ω _ _ _ _ ε X l _ N _ c d gm hP x m n hm
  have hl : l.Prime := Fact.out
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hD0 : 0 < N * l ^ (m + n) := Nat.mul_pos hN0 (pow_pos hl.pos _)
  obtain ⟨⟨hu, hu0, hv, hv0⟩, -⟩ := UpperTheory.Kd.L.units ε X l N c d gm hP x m n hm
  have hld : (l : ℤ) ∣ ((N * l ^ (m + n) : ℕ) : ℤ) := by
    exact_mod_cast Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N
  have hlp : (l : ℤ) ∣ (l : ℤ) ^ (m + n) := dvd_pow_self _ (by omega)
  have hlN : ¬ (l : ℤ) ∣ (N : ℤ) := fun h => hP.cop (Int.natCast_dvd_natCast.1 h)
  have c6 : ∀ e : ℕ, Nat.Coprime e (6 * l * N) → Nat.Coprime e 6 ∧ Nat.Coprime e (N * l ^ (m + n)) := fun e he =>
    ⟨Nat.Coprime.coprime_dvd_right (Dvd.intro _ (by rw [mul_assoc])) he,
      Nat.Coprime.mul_right (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) he)
        (Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_right (Dvd.dvd.mul_right (Dvd.intro_left 6 rfl) N) he))⟩
  refine KummerExtensionIntegrality.topexOf X (NeZero.ne _) hl.ne_zero ?_ hu hv hu0 hv0 fun W hW => ⟨?_, ?_⟩
  · exact Dvd.dvd.mul_right (pow_dvd_pow l (by omega)) _
  · refine UpperTheory.valuation_siegelUnitLevel_eq_one ε X c N _ _ hP.c1 (c6 c hP.cc).1 (c6 c hP.cc).2 hN0 hD0 (fun h => hlN ?_) W hW
    have h1 := hld.trans h.1
    have h2 : (l : ℤ) ∣ (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n) := Dvd.dvd.mul_left hlp _
    exact (Int.dvd_add_left h2).1 h1
  · refine UpperTheory.valuation_siegelUnitLevel_eq_one ε X d N _ _ hP.d1 (c6 d hP.dc).1 (c6 d hP.dc).2 hN0 hD0 (fun h => hlN (hld.trans h.2)) W hW
