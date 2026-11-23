import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLevelPointsOfLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelOKOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitExtensionDivisibleValuationFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalTatePairsUnitaryTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullDegArcDataAtUniformiserStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TraitArc

open GlobalTheory.TauTwist ReciprocityTheory.ChartRestriction.G.DVR

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dm : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {T : Formalism.L2.Pj.CDVR}

theorem tateCl_of (β : O →+* c.F) (b : O →+* T.V) (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X]
    (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) {ϖ : T.V} (hϖ : Irreducible ϖ)
    (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A)
    (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M)
    (h : ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A →
      ∃ I : (letI := H.starRing; TateIsoQ Dm D.toPre oD F),
        (I.ζ l.A : F) = algebraMap (FractionRing T.V) F (algebraMap T.V _ (b z)) ∧
        (∀ a q, QkExt (algebraMap _ F) (pA a) q → QkPt.Equiv D.toPre F q (I.ev l.A a)) ∧
        ∀ a q, QkExt (algebraMap _ F) (pM a) q → QkPt.Equiv D.toPre F q (I.ev l.M a)) :
    TateCl D oD hϖ Dm β b hdiv pA pM := by
  intro F _ _ _ z hz
  letI := H.starRing
  obtain ⟨I, hζ, e₂, e₃⟩ := h F z hz
  have hw := GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)
  have ht := isScalarForm_tF D oD hϖ
  have hq := psiRel0 (H := H) D hϖ
  have hR := isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ (dvd_refl l.M') hdiv)
  let s : D.toPre.X → D.toPre.X → Fˣ := fun y x =>
    Units.map (algebraMap (FractionRing T.V) F).toMonoidHom (rF D hϖ l.M' y x)
  have hs : IsRootForm (𝓞 E) l.M' (tF D hϖ) s :=
    ⟨hR.1.map _, fun y x => by
      show (Units.map _ _) ^ _ = _
      rw [← map_pow, hR.2 y x]
      rfl⟩
  obtain ⟨s', I', s₁, -, s₃, s₄, s₅⟩ := exists_tateIsoQ_twist D.tau_bimult hw ht oD l.M' s hs I
  have lev : ∀ {k : ℕ} (hk : 0 < k) (hd : k ∣ l.M') (p : QkPt D.toPre (FractionRing T.V) k) (v : Dm.La),
      (∀ q, QkExt (algebraMap _ F) p q → QkPt.Equiv D.toPre F q (I.ev k v)) → ∀ q',
      QkExt (algebraMap _ F) (qkScale hw ht hq (isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ hd hdiv)) _ p) q' →
      QkPt.Equiv (D0 (H := H) D hϖ) F q' (I'.ev k v) := by
    intro k hk hd p v he q' hq'
    obtain ⟨q, rfl⟩ := (qkScaleEquiv hw ht hq (s₁ k hk) _).surjective q'
    have e := qkRel_qkScaleEquiv (D := D.toPre) (hψ := (D0 (H := H) D hϖ).psi_gen) hw ht hq (s₁ k hk) q
    refine e.equiv hw ht hq (s₁ k hk) (s₅ k hk v) (he q (QkRel.qkExt_of (fun y x => ?_)
      (qkRel_qkScale hw ht hq (isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ hd hdiv)) p) e hq'))
    rw [s₃ k hk hd]
    show (Units.map _ _) ^ _ = _
    rw [← map_pow]
    congr 1
    obtain ⟨j, hj⟩ := dvd_of_dvd D hϖ (dvd_refl l.M') hdiv y x
    obtain ⟨i, hi⟩ := hd
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    have hM' : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by decide) l.three_le) l.A_pos
    have hi0 : (i : ℤ) ≠ 0 := by
      rintro h
      have : i = 0 := by exact_mod_cast h
      rw [this, mul_zero] at hi
      omega
    simp only [rF, ← zpow_natCast, ← zpow_mul]
    congr 1
    rw [hj, hi, Nat.mul_div_cancel_left _ hk]
    push_cast
    rw [Int.mul_ediv_cancel_left _ (mul_ne_zero hk0 hi0), _root_.mul_assoc, Int.mul_ediv_cancel_left _ hk0]
    ring
  exact ⟨I', by rw [s₄]; exact hζ, fun v => lev l.A_pos (Nat.dvd_lcm_right l.M l.A) _ v (e₂ v),
    fun v _ q hq => lev (lt_of_lt_of_le (by decide) l.three_le) (Nat.dvd_lcm_left l.M l.A) _ v (e₃ v) q hq⟩

end GlobalTheory.TraitArc

open GlobalTheory.TraitArc in

theorem GlobalTheory.TraitArc.exists_input_recovering : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∀ (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ₁ : R →+* V₁) (b₁ : O →+* V₁), GlobalTheory.LN.CDvr V₁ → Function.Injective ρ₁ → ρ₁.Finite → IsLocalHom ρ₁ → Function.Injective b₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ρ : R →+* V) (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), GlobalTheory.LN.CDvr V ∧ Function.Injective ρ ∧ ρ.Finite ∧ Irreducible ϖ ∧ ∀ (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp V ⟶ Y.X), Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y → ∃ (t : SAB H (Sp V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal V) t), Nonempty (IsPullDeg ρ D.toPre P.D.toPre) := by
  intro R _ _ _ hR E _ _ _ H Dm D _ o hX hP l c O _ β hβ V₁ _ _ _ ρ₁ b₁ hV₁ hρ₁ hf₁ hl₁ hb₁
  have hM' : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by decide) l.three_le) l.A_pos
  obtain ⟨T, ρ, b, ϖ, D', hρ, hρf, hb, hϖ, ⟨hD⟩, hdvd, hrat⟩ :=
    GlobalTheory.T.exists_traitExtension_divisible_valuationForm R D O V₁ ρ₁ b₁ hV₁ hρ₁ hf₁ hl₁ hb₁ (2 * l.M') (by omega)
  have hBase : Base R := ⟨by haveI := hR.1; exact ⟨inferInstance, inferInstance, inferInstance, hR.2.1⟩, hR.2.2⟩
  obtain ⟨inst, o', hP'⟩ := GlobalTheory.Mum.pelOK_of_isPullDeg R hBase E H Dm D o hP T.V ρ hρ D' ⟨hD⟩
  letI := inst
  have hX' : Nontrivial D'.toPre.X := hD.xe.toEquiv.nontrivial
  have hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D' hϖ a a' := fun a a' => by
    have := hdvd _ (isQ_qv D' hϖ) a a'
    exact_mod_cast this
  obtain ⟨pA, pM, hT⟩ := GlobalTheory.T.exists_rational_tate_pairs_unitaryType E H Dm l c O β hβ T b hb D' o' hP' (fun k hk => hrat k (hk.mul_left 2))
  have hLie : LieCl D' o' Dm β b := by
    intro F _ _ _ r _ τ
    obtain ⟨n, h₁, h₂⟩ := (hP'.2.2.2 F).1 τ
    refine ⟨n, h₁, ?_⟩
    split_ifs
    · exact h₂
    · exact h₂.trans hP'.1
  have hTate := tateCl_of β b D' o' hϖ hdiv pA pM hT
  refine ⟨T.V, T.cr, T.dom, inferInstance, ρ, b, ϖ, arc D' o' hϖ β b hX' hP'.2.2.1 hdiv pA pM hLie hTate,
    ⟨T.dvr, T.cpl, T.ch0⟩, hρ, hρf, hϖ, ?_⟩
  intro Xo Y y hy
  obtain ⟨t, m, P, ⟨hD₂⟩⟩ := GlobalTheory.T.exists_pullDeg_arcData_at_uniformiser E H Dm l c O β T b D' o' ϖ hϖ hX' hP'.2.2.1 hdiv pA pM hLie hTate Xo Y y hy
  refine ⟨t, m, P, ?_⟩
  have := GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R T.V T.V ρ (RingHom.id T.V) D.toPre D'.toPre P.D.toPre
    Function.injective_id ⟨hD⟩ ⟨hD₂⟩
  rwa [RingHom.id_comp] at this
