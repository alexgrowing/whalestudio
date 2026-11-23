import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSums
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValuesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValuesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesOfExpansionLawsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcTorsionValuesNormsIntegralPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegraStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcIsometryTorsionIntegralGaugeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralGaugeValuesAreValuationUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDimensionalFieldDegenerationValuesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionClassesDescendFiniteAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuationSubringIntegralClosureCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuedFieldValuationCentreLePowStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxCosetNormGeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcLiftExtensionLargerClosedFieldStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LabelledTorsionValuesAdditiveKernelSurjectiveStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ArcSeries

theorem exists_root_system {K : Type} [Field K] [IsAlgClosed K] (u : Kˣ) : ∃ r, Roots u r := by
  have hs : ∀ (n : ℕ) (x : Kˣ), ∃ y : Kˣ, y ^ (n + 1) = x := fun n x => by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : K) n.succ_pos
    exact ⟨Units.mk0 y fun e => x.ne_zero (by rw [← hy, e]; simp), Units.ext hy⟩
  choose rt hrt using hs
  let s : ℕ → Kˣ := fun n => Nat.rec u (fun n x => rt n x) n
  have h1 : ∀ n d, s (n + d) ^ ((n + d).factorial / n.factorial) = s n := fun n d => by
    induction d with
    | zero => simp [Nat.div_self n.factorial_pos]
    | succ d ih =>
      rw [← add_assoc, Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (Nat.le_add_right _ _)),
        pow_mul]
      exact (congrArg (· ^ _) (hrt _ _)).trans ih
  refine ⟨fun n => s n ^ (n.factorial / n), ?_, fun n m hn hm => ?_⟩
  · change s 1 ^ 1 = u
    exact hrt 0 u
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.le_mul_of_pos_right n hm)
    have a := h1 n d
    rw [← hd] at a
    change (s (n * m) ^ ((n * m).factorial / (n * m))) ^ m = s n ^ (n.factorial / n)
    rw [← a, ← pow_mul, ← pow_mul]
    congr 1
    obtain ⟨p, hp⟩ := Nat.dvd_factorial (Nat.mul_pos hn hm) le_rfl
    obtain ⟨q, hq⟩ := Nat.dvd_factorial hn le_rfl
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_right n hm)
    have e1 : (n * m).factorial / (n * m) = p := by rw [hp]; exact Nat.mul_div_cancel_left _ (Nat.mul_pos hn hm)
    have e2 : n.factorial / n = q := by rw [hq]; exact Nat.mul_div_cancel_left _ hn
    have e3 : (n * m).factorial / n.factorial = t := by rw [ht]; exact Nat.mul_div_cancel_left _ n.factorial_pos
    rw [e1, e2, e3]
    refine Nat.eq_of_mul_eq_mul_left hn ?_
    rw [hp, hq] at ht
    linarith

theorem base_local {O : Type} [CommRing O] [IsDomain O] {ϖ : O} (h : GlobalTheory.LN.ArcBase O ϖ) :
    IsLocalRing O ∧ IsPrincipalIdealRing O := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · letI := h.toField
    exact ⟨inferInstance, inferInstance⟩
  · exact ⟨inferInstance, inferInstance⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem exists_reps {n : ℕ} (hn : 0 < n) : ∃ (Ix : Type) (_ : Finite Ix) (t : Ix → D.La), ∀ a, ∃ i e, t i = a + n • e := by
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  let P : Submodule ℤ D.La := LinearMap.range ((n : ℤ) • LinearMap.id)
  have : Finite (D.La ⧸ P) := Module.finite_of_fg_torsion (M := D.La ⧸ P) fun x => by
    obtain ⟨x, rfl⟩ := P.mkQ_surjective x
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    change (n : ℤ) • P.mkQ x = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero P).2 ⟨x, rfl⟩
  refine ⟨D.La ⧸ P, this, Quotient.out, fun a => ?_⟩
  obtain ⟨e, he⟩ := (Submodule.Quotient.eq P).1 (Quotient.out_eq (Submodule.Quotient.mk a : D.La ⧸ P))
  exact ⟨_, e, by rw [← natCast_zsmul]; exact (eq_add_of_sub_eq' he.symm)⟩

theorem eq_zero_of_nsmul {n : ℕ} (hn : n ≠ 0) (a : D.La) (h : n • a = 0) : a = 0 := by
  refine D.unimod.1 (LinearMap.ext fun y => ?_)
  have := congrArg (fun x => D.EF x y) h
  simp only [map_nsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, nsmul_eq_mul, mul_eq_zero,
    Nat.cast_eq_zero, hn, false_or] at this
  rw [this, map_zero, LinearMap.zero_apply]

theorem exists_series : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → Nonempty (Ser a K (algebraMap _ K)) := by
  intro hHV _ _ _ _ _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hB K _ _ _ _ _ _ hK
  have hL : Laws := hHV.1.1
  have hL2 : Laws2 := hHV.1.2.1
  have gt := GlobalTheory.T.torus_torsion_points_correspond_values
  have wp := GlobalTheory.T.torsionPairing_values_of_familiesValues gt (GlobalTheory.T.families_values_correspond hL hL2)
  obtain ⟨_, _⟩ := base_local hB
  let F := AlgebraicClosure (FractionRing O')
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.exists_valuationSubring_integral_closure_completeDVR O' ϖ hB F
  have hin : ∀ r : O', algebraMap (FractionRing O') F (algebraMap O' _ r) ∈ S₀ := fun r =>
    (hS₀ _).2 (by rw [← IsScalarTower.algebraMap_apply]; exact isIntegral_algebraMap)
  obtain ⟨A₀, hA₀⟩ := GlobalTheory.T.exists_arcIsometry_torsion_integralGauge hL gt E H D l Xo c W₀ Y O' b ϖ a hB F S₀ hin
  let io : F →+* K := (IsAlgClosed.lift : F →ₐ[FractionRing O'] K).toRingHom
  have hio : io.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') K :=
    (IsAlgClosed.lift : F →ₐ[FractionRing O'] K).comp_algebraMap
  obtain ⟨A, -, I₀, l₀, -, -, x₀, q₀⟩ :=
    GlobalTheory.T.exists_arcLift_extension_larger_closed_field hL gt wp E H D l Xo c W₀ Y O' b ϖ a hB F K io hio ⊤ (fun _ => trivial) A₀
  have hinj := FaithfulSMul.algebraMap_injective (PowerSeries O') K
  have hX : algebraMap (PowerSeries O') K PowerSeries.X ≠ 0 := (map_ne_zero_iff _ hinj).2 PowerSeries.X_ne_zero
  obtain ⟨r, hr⟩ := exists_root_system (Units.mk0 _ hX)
  have hr1 : (r 1 : K) = algebraMap (PowerSeries O') K PowerSeries.X := by rw [hr.1]; rfl
  obtain ⟨iθ, iσ, ith, iψ⟩ := GlobalTheory.T.integralGauge_values_are_valuationUnits O' a.D₀ F S₀ hin A₀.N A₀.ν hA₀
  have level : ∀ (m j : ℕ) (z : D.La), ∃ (R₁ : Subalgebra (PowerSeries O') K) (v w : D.La → K), Odd m → 0 < j →
      Module.Finite (PowerSeries O') R₁ ∧ (∀ x, v x ∈ R₁) ∧
      Sums (PowerSeries.X : PowerSeries O') io A₀.N A₀.be.be m j (A₀.q (m ^ 2)) (A₀.q j z) (r (m ^ 2 * j)) v w := by
    intro m j z
    by_cases h : Odd m ∧ 0 < j
    swap
    · exact ⟨⊥, 0, 0, fun a b => (h ⟨a, b⟩).elim⟩
    obtain ⟨hm, hj⟩ := h
    have hm2 : 0 < m ^ 2 := pow_pos hm.pos 2
    obtain ⟨Ix, _, t, ht⟩ := exists_reps D hm2
    let k : Option Ix → ℕ := fun i => i.elim j fun _ => m ^ 2
    let p : ∀ i, A₀.N.QT (k i) := fun i => match i with
      | none => A₀.q j z
      | some i => A₀.q (m ^ 2) (t i)
    obtain ⟨K₁, A₁, f1, f2, f3, f4, f5, f6, f7⟩ :=
      GlobalTheory.T.exists_finiteDimensional_field_degenerationValues O' a.D₀ F A₀.N A₀.ν (Set.range fun i => (p i).1.2.b) (Set.finite_range _)
    obtain ⟨O₁, _, N₀, I, hI, hp⟩ := GlobalTheory.T.torsionClasses_descend_finite_algebra O' F S₀ hS₀ A₀.N K₁ A₁ f1 f3 f4 f5 f6 f7 iθ iσ ith (iψ a.gen) (Option Ix) k p
      (fun i => by cases i; exacts [hj, hm2]) fun i => f2 _ ⟨i, rfl⟩
    have : FaithfulSMul O' F := (faithfulSMul_iff_algebraMap_injective _ _).2 (by
      rw [IsScalarTower.algebraMap_eq O' (FractionRing O') F]
      exact (algebraMap (FractionRing O') F).injective.comp (IsFractionRing.injective O' _))
    have : Module.Free O' O₁ := Module.free_of_finite_type_torsion_free'
    obtain ⟨R₁, v, w, h⟩ := exists_sums (O := O') O₁.val.toRingHom io (fun x => by
        rw [← hK, ← hio]; rfl) A₀.be.be hm hj (A₀.q (m ^ 2)) (A₀.q j z) (r (m ^ 2 * j))
      (by rw [← Units.val_pow_eq_pow_val, hr.pow (Nat.mul_pos hm2 hj)]; rfl) I hI
      (fun x => by
        obtain ⟨i, e, he⟩ := ht x
        exact hp (some i) _ (((GlobalTheory.T.labelledTorsionValues_additive_kernel_surjective gt E H D O' F A₀.arc _ hm2).2.1 _ _).2 ⟨e, he⟩))
      (hp none _ ((A₀.N.qEq_equivalence _).refl _))
    exact ⟨R₁, v, w, fun _ _ => h⟩
  choose R₁ v w hlev using level
  have ext : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
      [Algebra (FractionRing O') C] (gam : K →+* C),
      (∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) = gam (algebraMap (PowerSeries O') K (PowerSeries.C x))) →
      (∀ f, ‖gam (algebraMap (PowerSeries O') K f)‖ ≤ 1) → ∃ A' : Lift a C, A'.ν.IntN ∧ A.arc.Over gam A'.arc ∧
        ∃ I : NumD.Hom (gam.comp io) A₀.N A'.N, I.lam = 1 ∧ (∀ y z, A'.be.be (I.e y) (I.e z) = A₀.be.be y z) ∧
          ∀ n x, (A'.q n x).1.1.toAdd = I.e (A₀.q n x).1.1.toAdd ∧ I.Rel (A₀.q n x).1.2 (A'.q n x).1.2 := by
    intro C _ _ _ _ gam h1 h2
    obtain ⟨S, hS⟩ := exists_ball C
    obtain ⟨A', hA', I₁, l₁, r₁, z₁, x₁, q₁⟩ := GlobalTheory.T.exists_arcLift_extension_larger_closed_field hL gt wp E H D l Xo c W₀ Y O' b ϖ a hB K C gam
      (IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun x => (congrArg gam (hK x)).trans (h1 x).symm))
      S (fun x => (hS _).2 (by rw [h1]; exact h2 _)) A
    refine ⟨A', ⟨S, hS, hA'⟩, ⟨I₁, r₁, z₁, fun s y => A'.ν.eX.injective ?_, fun n x _ =>
      ⟨A'.q n x, (q₁ n x).1, (q₁ n x).2, (A'.N.qEq_equivalence _).refl _⟩⟩, homComp I₀ I₁ _ fun _ => rfl, ?_, fun y z => ?_,
      fun n x => ⟨(q₁ n x).1.trans (congrArg I₁.e (q₀ n x).1), homComp_rel _ _ _ _ (q₀ n x).2 (q₁ n x).2⟩⟩
    · change A'.ν.eX (I₁.e (A.ν.eX.symm (s • A.ν.eX y))) = A'.ν.eX (A'.ν.eX.symm (s • A'.ν.eX (I₁.e y)))
      exact ((x₁ _).trans (A.ν.eX.apply_symm_apply _)).trans
        ((A'.ν.eX.apply_symm_apply _).trans (congrArg (s • ·) (x₁ y))).symm
    · change I₁.lam * Units.map _ I₀.lam = 1
      rw [l₁, l₀, map_one, _root_.mul_one]
    · change A'.be.be (I₁.e (I₀.e y)) (I₁.e (I₀.e z)) = _
      rw [A'.be_eq, A₀.be_eq, x₁, x₁, x₀, x₀]
  have hrm : ∀ m j, Odd m → 0 < j → r (m ^ 2) = r (m ^ 2 * j) ^ j ∧ r j = r (m ^ 2 * j) ^ m ^ 2 := fun m j hm hj =>
    ⟨(hr.2 _ _ (pow_pos hm.pos 2) hj).symm, by rw [mul_comm]; exact (hr.2 _ _ hj (pow_pos hm.pos 2)).symm⟩
  refine ⟨⟨⟨inferInstance, hinj, fun x => Algebra.IsAlgebraic.isAlgebraic (R := PowerSeries O') x, hK⟩, A, r, hr1,
    ⟨rfl, hr.2⟩, fun m => v m 1 0, w, ?_, ?_⟩⟩
  · intro n j hp ho hu hj S hS
    have hm : Odd (n ^ j) := ho.pow
    obtain ⟨hfin, hmem, hsum⟩ := hlev (n ^ j) 1 0 hm one_pos
    have hvS : ∀ x, v (n ^ j) 1 0 x ∈ S := fun x =>
      mem_of_isIntegral S hS ((Algebra.IsIntegral.isIntegral (⟨_, hmem x⟩ : R₁ (n ^ j) 1 0)).map (R₁ _ _ _).val)
    have key : ∀ e : ℕ, ∃ (C : Type) (_ : NormedField C) (gam : K →+* C) (u : ℝ), 0 < u ∧ u < 1 ∧
        (∀ x, S.valuation (v (n ^ j) 1 0 x) < 1 → ‖gam (v (n ^ j) 1 0 x)‖ < 1 ∧
          (S.valuation (algebraMap (PowerSeries O') K PowerSeries.X) = 1 → ‖gam (v (n ^ j) 1 0 x)‖ ≤ u ^ e)) ∧
        (∃ x, 1 ≤ ‖gam (v (n ^ j) 1 0 x)‖) ∧ ∀ x, ∃ h, u ^ (A₀.be.be (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd
          (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd).toNat ≤ ‖gam (v (n ^ j) 1 0 (x + n ^ (j - 1) • h))‖ := by
      intro e
      obtain ⟨C, _, _, _, _, gam, g1, g2, g3⟩ := GlobalTheory.T.exists_valuedField_valuationCentre_le_pow (PowerSeries O') K PowerSeries.X
        (fun h => not_isUnit_zero (by simpa using h.map PowerSeries.constantCoeff : IsUnit (0 : O')))
        PowerSeries.X_ne_zero _ hfin S hS e
      letI : Algebra (FractionRing O') C := (gam.comp (algebraMap _ K)).toAlgebra
      have h1 : ∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) =
          gam (algebraMap (PowerSeries O') K (PowerSeries.C x)) := fun x => congrArg gam (hK x)
      have hce : CExt O' ⊥ C := ⟨fun x => by rw [h1]; exact g1 _, fun x hx => by
        rw [(Submodule.mem_bot _).1 hx]; simp⟩
      obtain ⟨A', hN, -, I, hI, hβ, hq⟩ := ext C gam h1 g1
      let r' : ℕ → Cˣ := fun n => Units.map gam.toMonoidHom (r n)
      have hu' : (r' 1 : C) = gam (algebraMap (PowerSeries O') K PowerSeries.X) := congrArg gam hr1
      have hu1 : ‖(r' 1 : C)‖ < 1 := hu' ▸ g2
      have hpow : r' ((n ^ j) ^ 2) ^ (n ^ j) ^ 2 = r' 1 := by
        rw [← map_pow, hr.pow (pow_pos hm.pos 2), ← hr.1]
      have hn : ‖(n : C)‖ = 1 := by
        obtain ⟨y, hy⟩ := hu.exists_right_inv
        have a1 := hce.1 n
        have a2 := hce.1 y
        have a3 := congrArg (fun x => ‖algebraMap (FractionRing O') C (algebraMap O' _ x)‖) hy
        simp only [map_mul, map_natCast, map_one, norm_mul, norm_one] at a1 a3
        nlinarith [norm_nonneg (n : C)]
      obtain ⟨qf, hq1, hq2⟩ := (GlobalTheory.T.arcTorsionValues_norms_integral_positive E H D l Xo c W₀ Y O' b ϖ a hB C hce A' hN).2.2 (r' 1) hu1
      choose p hp' using fun x => (existsUnique_twRel A'.be (r' 1) _ hpow (A'.q _ x)).exists
      obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.labelledTorsionValues_additive_kernel_surjective gt E H D O' C A'.arc _ (pow_pos hm.pos 2)
      obtain ⟨c1, c2⟩ := GlobalTheory.T.twist_tx_coset_norm_ge_alt C A'.N _ A'.be (r' 1) _ qf n _ j hp ho hn hj hu1 hpow hq1 hq2
        (GlobalTheory.T.abelianPartValues_torsion_pairing_separation_integral hL hL2 (GlobalTheory.T.abelianPartValues_of_expansionLaws hL) O' a.D₀ a.even a.bimult C hce A'.N A'.ν hN n hp ho hn)
        D.La (A'.q _) (eq_zero_of_nsmul D hp.ne_zero) t1 t2 t3 p hp'
      have hv := (hsum C gam g1 g2 A'.N I _ A'.be hI hβ (r' 1) (r' ((n ^ j) ^ 2)) (r' 1) hu'
        (by rw [← (hrm _ 1 hm one_pos).1]; rfl) (by rw [← (hrm _ 1 hm one_pos).2]; rfl) (A'.q _) p (hq _) hp').1
      refine ⟨C, inferInstance, gam, ‖(r' 1 : C)‖, norm_pos_iff.2 (r' 1).ne_zero, hu1,
        fun x hx => hu' ▸ g3 _ (hmem x) hx, by simpa only [hv] using c1, fun x => ?_⟩
      simpa only [hv, (hq _ x).1, hβ] using c2 x
    have hlt : ∀ x, S.valuation (v (n ^ j) 1 0 x) ≠ 1 → S.valuation (v (n ^ j) 1 0 x) < 1 := fun x h =>
      lt_of_le_of_ne ((S.valuation_le_one_iff _).2 (hvS x)) h
    refine ⟨hvS, ?_, fun hXu x => ?_⟩
    · obtain ⟨C, _, gam, u, -, -, k1, ⟨x, hx⟩, -⟩ := key 0
      exact ⟨x, not_not.1 fun h => (k1 x (hlt x h)).1.not_ge hx⟩
    · obtain ⟨C, _, gam, u, u0, u1, k1, -, k2⟩ := key ((A₀.be.be (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd
        (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd).toNat + 1)
      obtain ⟨h, hh⟩ := k2 x
      exact ⟨h, not_not.1 fun hne => (hh.trans ((k1 _ (hlt _ hne)).2 hXu)).not_gt
        (pow_lt_pow_right_of_lt_one₀ u0 u1 (Nat.lt_succ_self _))⟩
  · intro C _ _ _ _ _ gam u h1 g1 hu hu1
    obtain ⟨A', hN, hO, I, hI, hβ, hq⟩ := ext C gam h1 g1
    refine ⟨A', fun n => Units.map gam.toMonoidHom (r n), hN, hO, fun _ => rfl, fun m hm p hp => ?_⟩
    have S := fun j z hj => (hlev m j z hm hj).2.2 C gam g1 (by rw [hu] at hu1; exact hu1) A'.N I _ A'.be hI hβ u
      (Units.map gam.toMonoidHom (r (m ^ 2))) (Units.map gam.toMonoidHom (r j)) hu
      (by rw [← (hrm _ j hm hj).1]; rfl) (by rw [← (hrm _ j hm hj).2]; rfl) (A'.q _) p (hq _) hp
    exact ⟨⟨1, fun x => by rw [Units.val_one, _root_.one_mul]; exact (S 1 0 one_pos).1 x⟩,
      fun j hj z q hq' => (S j z hj).2 (A'.q j z) q (hq j z).1 (hq j z).2 hq'⟩

end GlobalTheory.ArcSeries
end
