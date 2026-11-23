import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionZerosTwistLe
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionForm

open TorsionZero in

theorem exists_sec_of_form {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp K) {L : LB X}
    (hL : L.IsLB) {N d : ℕ} {J : Type} (s : J → (lbPow L N).Sec) {F : MvPolynomial J K}
    (hF : F.IsHomogeneous d) :
    ∃ u : (lbPow L (N * d)).Sec, ∀ (z : Sp K ⟶ X) (v : J → K), z ≫ p = 𝟙 _ → Crd (lbPow L N) s z v →
      (⊤ ≤ z ⁻¹ᵁ Out.nonzeroLocus u ↔ MvPolynomial.eval v F ≠ 0) := by
  obtain ⟨R, _, _, _, 𝒜, _, Φ, -, -, -, hρ⟩ := SectionRing.exists_sectionRing K X p L hL
  have hm := aeval_mem_of_isHomogeneous 𝒜 (fun j => (Φ N (s j)).2) hF
  obtain ⟨u, hu⟩ := (Φ (N * d)).surjective ⟨_, hm⟩
  have hu' : (Φ _ u : R) = MvPolynomial.aeval (fun j => (Φ N (s j) : R)) F := congrArg Subtype.val hu
  refine ⟨u, ?_⟩
  rintro z v hz ⟨l, c, hl, hv⟩
  obtain ⟨ρ, hρc, hρ⟩ := hρ l
  let ev : R →ₐ[K] K :=
    { (TorsionZero.val z ((lbPow L 0).U l) hl).comp ρ with
      commutes' := fun a => (congrArg (TorsionZero.val z ((lbPow L 0).U l) hl) (hρc a)).trans
        (val_const p z hz _ hl a) }
  have e₁ : ev (Φ _ u) = TorsionZero.val z ((lbPow L (N * d)).U l) hl (u.f l) :=
    congrArg (TorsionZero.val z ((lbPow L 0).U l) hl) (hρ _ u)
  have e₂ : v = fun j => ev (Φ N (s j)) * c := funext fun j => by
    rw [hv, _root_.mul_comm, CrdCalc.valR_eq z _ hl]
    exact congrArg (· * (c : K)) (congrArg (TorsionZero.val z ((lbPow L 0).U l) hl) (hρ _ (s j))).symm
  rw [EndOnTorsion.le_nonzeroLocus_iff u z l hl, ← e₁, hu', MvPolynomial.comp_aeval_apply,
    ← MvPolynomial.coe_aeval_eq_eval]
  change _ ↔ MvPolynomial.aeval v F ≠ 0
  rw [e₂, aeval_mul_of_isHomogeneous _ _ hF, mul_ne_zero_iff]
  exact (and_iff_left (pow_ne_zero _ c.ne_zero)).symm

theorem mem_vanishingIdeal_of_vanish_on_torsion :
    Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (J : Type) (s : J → (lbPow P.L N).Sec) (F : MvPolynomial J K), 4 ≤ N → (k : K) ≠ 0 → N ^ P.g * P.g.factorial * d < k ^ 2 → F.IsHomogeneous d → (∀ x : (Out.baseOver (Sp K)) ⟶ P.A, x ^ k = 1 → ∃ v : J → K, Crd (lbPow P.L N) s (x.left : Sp K ⟶ P.A.left) v ∧ MvPolynomial.eval v F = 0) → F ∈ MvPolynomial.vanishingIdeal K (cone P.A.hom (lbPow P.L N) s) := by
  intro h K _ _ P N d k J s F hN hk hd hF hx
  have := polAV_isIntegral_of_isAlgClosed K P
  obtain ⟨u, hu⟩ := exists_sec_of_form P.A.hom P.isLB s hF
  have h₅ : ∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ k = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus u := fun x e hx' => by
    obtain ⟨v, hv, h0⟩ := hx x e
    exact (hu x.left v (Over.w x) hv).1 hx' h0
  rintro v ⟨z, hz, hv⟩
  by_contra hne
  have hzu := (hu z v hz hv).2 hne
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · let x : Out.baseOver (Sp K) ⟶ P.A := Over.homMk z hz
    have e : 𝟙 P.A = 1 := EndOnTorsion.eq_of_dim_zero P P hg _ _ (by rw [Category.comp_id, MonObj.comp_one])
    have e' : x = 1 := by rw [← Category.comp_id x, e, MonObj.comp_one]
    exact h₅ x (by rw [e', one_pow]) hzu
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 ((TorsionZero.top_le_iff z _).1 hzu)
    have hM1 : 1 ≤ k := Nat.pos_of_ne_zero fun e => hk (by rw [e, Nat.cast_zero])
    have hcard := (h.mulN (Sp K) P _ hM1).2.2.2.2 K (𝟙 _) hk
    have h₄ := card_zeros_on_torsion_coset_le h.mulN SectionRing.exists_sectionRing
      (PowSec.exists_basis_sections h.globalSectionsRank) (veryAmple_lbPow h.ample) (exists_mulPull_sec h.mulPull)
      SmoothDim.ringKrullDim_affineOpen polAV_isIntegral_of_isAlgClosed isIntegral_adjoin_of_mul_pow_mem
      graded_bezout_bound K P N d k 1 hg hN hk u
      ⟨j, fun e => by rw [e, Scheme.basicOpen_zero] at hj; exact hj⟩
    have e : k ^ (2 * P.g) = k ^ 2 * k ^ (2 * P.g - 2) := by rw [← pow_add]; congr 1; omega
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => and_iff_left_of_imp (h₅ x)), hcard, e] at h₄
    exact absurd (Nat.le_of_mul_le_mul_right h₄ (pow_pos hM1 _)) (not_le.2 hd)

end GlobalTheory.TorsionForm
