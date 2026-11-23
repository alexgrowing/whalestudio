import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TiltFrobeniusTeichmullerAction
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormSubgroupOpen
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial
open GlobalTheory.UnramifiedCrys

private def algSub (p : ℕ) [hp : Fact p.Prime] (R : Type) [CommRing R] [CharP R p] : Subring R where
  carrier := {y | ∃ m, 0 < m ∧ y ^ p ^ m = y}
  one_mem' := ⟨1, one_pos, one_pow _⟩
  zero_mem' := ⟨1, one_pos, zero_pow (pow_pos hp.out.pos _).ne'⟩
  mul_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [mul_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [add_pow_char_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  neg_mem' := by
    rintro x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    have h := sub_pow_char_pow (p := p) (n := a) (0 : R) x
    rwa [zero_sub, hx, zero_pow (pow_pos hp.out.pos _).ne', zero_sub] at h

private theorem exists_alg {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    (ρ : G →* (R ≃+* R)) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → ρ g y = y) → M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      ∀ g (f : R →+* R), (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → f y = ρ g y) →
        (M g).map (zlW p R) * W.map (WittVector.map f) = W :=
  _root_.UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.exists_alg ρ hopen M hM hJ

private theorem map_iterFrob {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p] (k : ℕ)
    (x : WittVector p R) :
    WittVector.map (iterateFrobenius R p (k + 1)) x =
      WittVector.frobenius (WittVector.map (iterateFrobenius R p k) x) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  ext i
  simp [iterateFrobenius_def, frobenius_def, pow_succ, pow_mul]

private theorem φB_pow_ιA {l : ℕ} [Fact l.Prime] (k : ℕ) (x : WittVector l (OCb l)) :
    ((PP l).φB ^ k) ((AIP l).ιA x) = (AIP l).ιA (WittVector.map (iterateFrobenius _ l k) x) := by
  induction k with
  | zero =>
    rw [pow_zero]
    change (AIP l).ιA x = _
    congr 1
    ext i
    simp
  | succ k ih =>
    rw [pow_succ', map_iterFrob, (AIP l).ιA_φ, ← ih]
    rfl

open GlobalTheory.UnramifiedRep GlobalTheory.Cyc in
theorem UpperTheory.crystalline_frobenius_algebraic_elements :
    UpperTheory.V.Af.Wd.WittPer := by
  intro l _ K r M hM hMI
  obtain ⟨-, -, hI, -, -⟩ := iqBasic l
  obtain ⟨Ti⟩ := tiedP l
  have := compactSpace_GK K
  obtain ⟨W, hW, hWg⟩ := exists_alg (p := l) ((AIP l).actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq (AIP l) y m hm hy)) M hM
    (fun g hg => hMI g ((hI g).2 (norm_sub_lt_one_of_fix (AIP l) g hg)))
  have key : ∀ (g : ↥(GK K)) (f : OCb l →+* OCb l) (F : Bcr l → Bcr l),
      (∀ m, 0 < m → ∀ y : OCb l, y ^ l ^ m = y → f y = (AIP l).actT g y) →
      (∀ x, F ((AIP l).ιA x) = (AIP l).ιA (WittVector.map f x)) →
      (M g).map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l])) * ((AIP l).ιA.mapMatrix W).map F =
        (AIP l).ιA.mapMatrix W := fun g f F hf hF => by
    conv_rhs => rw [← hWg g f hf, map_mul]
    congr 1
    · ext i j
      exact (ιA_zlW (AIP l) Ti (M g i j)).symm
    · ext i j
      exact hF _
  refine ⟨(AIP l).ιA.mapMatrix W, ?_, fun g => ?_, fun g k hk => ?_⟩
  · rw [← RingHom.map_det]
    exact hW.map _
  · exact key g ((AIP l).actT g).toRingHom _ (fun _ _ _ _ => rfl) fun x => ((AIP l).ιA_act g x).symm
  · exact key g (iterateFrobenius _ l k) _
      (fun m hm y hy => (UpperTheory.tilt_frobenius_teichmuller_action l y m hm hy g k hk).symm) fun x => φB_pow_ιA k x
