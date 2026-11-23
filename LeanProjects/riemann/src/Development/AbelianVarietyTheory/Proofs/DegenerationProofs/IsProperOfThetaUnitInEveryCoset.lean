import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValuesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesOfExpansionLawsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBaseStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianPartValuesTorsionPairingSeparationIntegraStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsEqDegenerationSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxCosetCriterionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairingStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfUnifOfSubsingleton

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.CosetGood

theorem subsingleton_of_forall_hom {X : Type} [AddCommGroup X] [Module.Free ℤ X] {n : ℕ} (hn : n.Prime)
    (h : ∀ (l : X →+ ZMod n) (y : X), l y = 0) : Subsingleton X := by
  haveI : Fact n.Prime := ⟨hn⟩
  let b := Module.Free.chooseBasis ℤ X
  haveI : IsEmpty (Module.Free.ChooseBasisIndex ℤ X) := ⟨fun i => by
    have := h ((Int.castAddHom (ZMod n)).comp (b.coord i).toAddMonoidHom) (b i)
    simp at this⟩
  exact b.repr.toEquiv.subsingleton

theorem subsingleton_of_labels {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [IsAlgClosed C] (N : NumD C) (Q : QuadraticMap ℤ N.X ℝ) (hQ : N.Int Q) {n g j : ℕ} (hn : n.Prime) (ho : Odd n)
    (h1 : ‖(n : C)‖ = 1) (hT : N.Tors n g) (hj : 2 ≤ j) {La : Type} [AddCommGroup La]
    (r : N.QT ((n ^ j) ^ 2) → La → Prop) (tot : ∀ a, ∃ q, r q a) (cot : ∀ q, ∃ a, r q a)
    (mul : ∀ q q' a a', r q a → r q' a' → r (q * q') (a + a')) (inj : ∀ q q' a, r q a → r q' a → N.QEq q q')
    (v : La → C) (hv : ∀ q : La → N.QT ((n ^ j) ^ 2), (∀ a, r (q a) a) → ∃ c : C, ∀ a, v a = c * N.tx (n ^ j) (q a))
    (hle : ∀ a, ‖v a‖ ≤ 1) (hco : ∀ a, ∃ h, ‖v (a + n ^ (j - 1) • h)‖ = 1) : Subsingleton N.X := by
  classical
  obtain ⟨hA, hB, -⟩ := GlobalTheory.T.tx_coset_norm_one_and_ne_zero C N Q hQ n g hn ho h1 hT j (by omega)
  obtain ⟨q₀, -, -, hq₀⟩ := hB 1 rfl
  obtain ⟨a₀, ha₀⟩ := cot (1 * q₀)
  have tot' : ∀ a, ∃ q, r q a ∧ (a = a₀ → q = 1 * q₀) := fun a => by
    by_cases e : a = a₀
    · exact ⟨_, e ▸ ha₀, fun _ => rfl⟩
    · obtain ⟨q, hq⟩ := tot a
      exact ⟨q, hq, fun e' => absurd e' e⟩
  choose q hq hq' using tot'
  obtain ⟨c, hc⟩ := hv q hq
  have c1 : ‖c‖ ≤ 1 := by
    have := hle a₀
    rwa [hc, hq' a₀ rfl, norm_mul, hq₀, _root_.mul_one] at this
  have hu : ∀ a, ‖v a‖ = 1 → ‖N.tx (n ^ j) (q a)‖ = 1 := fun a ha => by
    rw [hc, norm_mul] at ha
    have := (hA (q a)).1
    nlinarith [norm_nonneg c, norm_nonneg (N.tx (n ^ j) (q a))]
  refine subsingleton_of_forall_hom hn fun l y => ?_
  have hl : ∀ (i : ℕ) (z : N.X), i ≠ 0 → l (n ^ i • z) = 0 := fun i z hi => by
    rw [map_nsmul, nsmul_eq_mul, Nat.cast_pow, ZMod.natCast_self, zero_pow hi, zero_mul]
  have he : ∀ p p' : N.QT ((n ^ j) ^ 2), N.QEq p p' → l p'.1.1.toAdd = l p.1.1.toAdd := by
    rintro p p' ⟨z, hz, -⟩
    rw [hz, map_add, show (n ^ j) ^ 2 • z = n ^ (j * 2) • z by rw [pow_mul], hl _ _ (by omega), add_zero]
  let Y : La →+ ZMod n := AddMonoidHom.mk' (fun a => l (q a).1.1.toAdd) fun a a' =>
    (he _ _ (inj _ _ _ (mul _ _ _ _ (hq a) (hq a')) (hq (a + a')))).trans (map_add l _ _)
  have hY : ∀ a, Y a = 0 := fun a => by
    obtain ⟨h, hh⟩ := hco a
    obtain ⟨z, hz⟩ := (hA _).2 (hu _ hh)
    have e : Y (a + n ^ (j - 1) • h) = 0 := (congrArg l hz).trans (hl _ _ (by omega))
    rwa [map_add, map_nsmul, nsmul_eq_mul, Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega), zero_mul,
      add_zero] at e
  have hn0 : (n : C) ≠ 0 := fun e => by rw [e, norm_zero] at h1; exact zero_ne_one h1
  have hs := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hn0 hT (j * 2)).2.2.1 y
  rw [pow_mul] at hs
  obtain ⟨p, rfl⟩ := hs
  obtain ⟨a, ha⟩ := cot p
  exact (he _ _ (inj _ _ _ (hq a) ha)).trans (hY a)

theorem exists_unitBall (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 :=
  ⟨(NormedField.valuation (K := C)).valuationSubring, fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    rfl⟩

theorem subsingleton_lattice (hV : HV) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
    (o : Full D C) (M : Mdl o) {n j : ℕ} (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hj : 2 ≤ j) (v : D.La → C)
    (hv : o.Theta (n ^ j) v) (hle : ∀ x, ‖v x‖ ≤ 1) (hco : ∀ x, ∃ h, ‖v (x + n ^ (j - 1) • h)‖ = 1) :
    Subsingleton M.P.D.toPre.X := by
  letI := H.starRing
  have hL : Laws := hV.1.1
  have hL2 : Laws2 := hV.1.2.1
  obtain ⟨hdvr, hcomp, hchar⟩ := (GlobalTheory.LN.cDvr_iff M.W).1 M.cdv
  have hR : AdmBase M.W (IsLocalRing.maximalIdeal M.W) := ⟨inferInstance, inferInstance, inferInstance, hcomp⟩
  have hev := M.P.D.psi_even
  have hbi := M.P.D.tau_bimult
  obtain ⟨S, hS⟩ := exists_unitBall C
  obtain ⟨N, ν, hν⟩ := GlobalTheory.ValuesExist.exists_integral_values hL M.W M.P.D.toPre hev hbi C S
    fun r => (hS _).2 (M.ext.1 r)
  have hI : ν.IntN := ⟨S, hS, hν⟩
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.degenerationValues_int_of_admissibleBase M.W _ hR M.P.D C M.ext N ν hI
  have hT := GlobalTheory.T.abelianPartValues_torsion_pairing_separation_integral hL hL2 (GlobalTheory.T.abelianPartValues_of_expansionLaws hL) M.W M.P.D.toPre hev hbi C
    ⟨M.ext.1, fun r hr => M.ext.2 r (bot_le (a := IsLocalRing.maximalIdeal M.W) hr)⟩ N ν hI n hn ho h1
  obtain ⟨g₁, g₂, g₃, -, g₅⟩ := GlobalTheory.T.torus_torsion_points_correspond_values M.W M.P.D.toPre hev hbi C N ν
  have hk : 0 < (n ^ j) ^ 2 := pow_pos (pow_pos hn.pos _) _
  obtain ⟨g₆, g₇, g₈⟩ := g₅ ((n ^ j) ^ 2)
  obtain ⟨f, f₁, f₂, f₃, f₄, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hV.1 M.W _ hR M.P.D M.P.A M.t.G M.t.semi M.P.U C _ hk
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback M.cart (𝟙 (Sp C)) (jFK (R := M.W) C) (Category.id_comp _).symm
  let x : D.La → (TFK (R := M.W) C ⟶ M.P.A.A) := fun a => e (o.I.ev ((n ^ j) ^ 2) a)
  have hp : ∀ a, o.I.ev ((n ^ j) ^ 2) a ^ (n ^ j) ^ 2 = 1 := fun a => (o.I.onto _ hk _).2 ⟨a, rfl⟩
  have hx : ∀ a, x a ^ (n ^ j) ^ 2 = 1 := fun a => (map_pow e _ _).symm.trans ((congrArg e (hp a)).trans (map_one e))
  have hv' : IsThetaPt M.P.A (n ^ j) x fun a => fnOf (v a) := by
    have key : ∀ (s : Sp C ⟶ (TK M.W).left) (_ : s = 𝟙 _ ≫ jFK (R := M.W) C) (y : D.La → (Over.mk s ⟶ M.P.A.A)),
        (∀ a, (y a).left = (o.I.ev ((n ^ j) ^ 2) a).left ≫ M.φ) → IsThetaPt M.P.A (n ^ j) y fun a => fnOf (v a) := by
      rintro s rfl y hy
      exact (ThetaPtUp.isThetaPt_iff (T := baseOver (Sp C)) M.cart M.lb hy hp _).1 hv
    exact key _ (Category.id_comp _).symm x fun a => he _
  have hm : ((n ^ j : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.2 (pow_pos hn.pos _).ne'
  obtain ⟨-, c₂, c₃, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL C _ M.P.A (jFK (R := M.W) C) (n ^ j) ho.pow hm D.La x hx
  haveI := subsingleton_of_labels N Q hQ hn ho h1 hT hj (fun q a => ∃ p, ν.QPt p q ∧ f p = x a) (fun a => ?_)
    (fun q => ?_) ?_ ?_ v (fun q hq => ?_) hle hco
  · exact ν.eX.symm.toEquiv.subsingleton
  · obtain ⟨p, hp⟩ := f₂ _ (hx a)
    obtain ⟨q, hq, -⟩ := g₆ p
    exact ⟨q, p, hq, hp⟩
  · obtain ⟨p, hp⟩ := g₇ q
    obtain ⟨w, hw⟩ := M.P.U.toUnifPre.ext
    have h₀ : f p ^ (n ^ j) ^ 2 = 1 := ((f₁ p (f p)).2 rfl w hw).1
    obtain ⟨a, ha⟩ := (o.I.onto _ hk (e.symm (f p))).1
      ((map_pow e.symm _ _).symm.trans ((congrArg e.symm h₀).trans (map_one e.symm)))
    exact ⟨a, p, hp, ((congrArg e ha).trans (e.apply_symm_apply _)).symm⟩
  · rintro q q' a a' ⟨p, hp, e₁⟩ ⟨p', hp', e₂⟩
    obtain ⟨p'', hp''⟩ := g₇ (q * q')
    refine ⟨p'', hp'', (f₄ p p' p'' ⟨p'', ?_, (g₃ _ _ _ _ _ _ hp.2 hp'.2 hp''.2).2 rfl, qk_equiv_refl hbi _⟩).trans ?_⟩
    · rw [← hp''.1, ← hp.1, ← hp'.1, ← map_add]; rfl
    · rw [e₁, e₂]
      exact ((congrArg e (o.I.add _ a a')).trans (map_mul e _ _)).symm
  · rintro q q' a ⟨p, hp, e₁⟩ ⟨p', hp', e₂⟩
    exact (g₈ p p' q q' hp hp').1 ((f₃ p p').1 (e₁.trans e₂.symm))
  · choose p hp hp' using hq
    have ht := GlobalTheory.T.theta_constants_eq_degeneration_series hV GlobalTheory.T.torus_torsion_points_correspond_values (GlobalTheory.T.families_values_correspond hL hL2) M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext
      N ν (n ^ j) ho.pow D.La p q x (fun a => (f₁ _ _).2 (hp' a).symm) hp
    obtain ⟨c, hc⟩ := (c₂ 1 _ v ((c₃ _).1 ht)).1 ((c₃ _).1 hv')
    exact ⟨c, fun a => congrFun hc a⟩

theorem isProper_of_unit_in_cosets : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (n j : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → 2 ≤ j → ∀ v, o.Theta (n ^ j) v → (∀ x, ‖v x‖ ≤ 1) → (∀ x, ∃ h, ‖v (x + n ^ (j - 1) • h)‖ = 1) → IsProper M.t.G.hom := by
  intro hV _ _ _ _ _ _ E _ _ _ H D C _ _ _ _ _ o M n j hn ho h1 hj v hv hle hco
  obtain ⟨hdvr, hcomp, hchar⟩ := (GlobalTheory.LN.cDvr_iff M.W).1 M.cdv
  exact (isAbelianScheme_of_unif_of_subsingleton hV.1.1 hV.1.2.1 M.W hcomp M.P.D M.P.A M.t.G M.t.semi M.P.U
    (subsingleton_lattice hV o M hn ho h1 hj v hv hle hco)).proper

end GlobalTheory.CosetGood
end
