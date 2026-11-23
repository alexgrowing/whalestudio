import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsConstOfCover
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsLinearOfLogDeriv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.ArtinKernel

open GlobalTheory.TangentOrigin

section Main

variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

omit [IsLocalRing R] [Module.Finite ℂ R] in
theorem log_deriv_rule (ρ : R →ₐ[ℂ] ℂ) (κ : R →ₗ[ℂ] ℂ) {F F' G : R} {g₀ d : ℂ} (e : F * algebraMap ℂ R g₀ = G * F')
    (hρ : ρ G = g₀) (k : κ (F' * G) = ρ F' * d + ρ G * κ F') (n₀ : g₀ ≠ 0) (n₁ : ρ F' ≠ 0) :
    g₀ * (κ F * (ρ F)⁻¹) = d + g₀ * (κ F' * (ρ F')⁻¹) := by
  have e1 := congrArg ρ e
  have e2 := congrArg κ e
  rw [map_mul, map_mul, hρ, AlgHom.commutes, mul_comm] at e1
  have e3 : ρ F = ρ F' := mul_left_cancel₀ n₀ e1
  rw [mul_comm G, k, hρ, Algebra.algebraMap_eq_smul_one, mul_smul_comm, _root_.mul_one,
    map_smul, smul_eq_mul] at e2
  rw [e3]
  field_simp
  linear_combination e2

theorem exists_linear_of_first_order (hL : L.IsLB) (a : u.Λ → ℂ) (B : u.Λ → ((Fin g → ℂ) →ₗ[ℂ] ℂ))
    (ha : ∀ l, a l ≠ 0)
    (hfr : ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = a l * cexp (B l z) * u.fr i (z + l))
    (ρ : R →ₐ[ℂ] ℂ) (x : spO R ⟶ A) (hx : resPt ρ ≫ x = 1) (κ : R →ₗ[ℂ] ℂ) (w : Fin g → ℂ)
    (hκ : ∀ (W : A.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ W) (f : Γ(A.left, W)),
        (∀ r, κ (r * evalPt (R := R) x.left W h f) =
          ρ r * κ (evalPt (R := R) x.left W h f) + ρ (evalPt (R := R) x.left W h f) * κ r) ∧
        κ (evalPt (R := R) x.left W h f) = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w)
    (c : LB.Gen (Out.translDiff A L x)) (hc : c.IsGen) :
    ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ l : u.Λ, B l w = lam l := by
  have hsub := subsingleton_primeSpectrum (R := R)
  have hle := snd_preimage_le (L := L) ρ x hx
  have hD : ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
      ⊤ ≤ (famPt u R z).left ⁻¹ᵁ (Out.translDiff A L x).U (fun _ => i) :=
    fun i z hz => le_trans (famPt_mem (R := R) u z hz) ((famPt u R z).left.preimage_mono (hle i))
  obtain ⟨F, hFdef⟩ : ∃ F : L.ι → (Fin g → ℂ) → R, ∀ i z,
      F i z = evalPt' (R := R) (famPt u R z).left _ (c.s (fun _ => i)).val :=
    ⟨fun i z => evalPt' (R := R) (famPt u R z).left _ (c.s (fun _ => i)).val, fun _ _ => rfl⟩
  have hF : ∀ i (lam : R →ₗ[ℂ] ℂ),
      DifferentiableOn ℂ (fun z => lam (F i z)) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i} := fun i lam => by
    simp only [hFdef]
    exact differentiableOn_famPt u (hle i) _ lam
  have hF0 : ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → ρ (F i z) ≠ 0 := fun i z hz => by
    rw [hFdef, evalPt'_eq _ (hD i z hz)]
    exact (((c.s (fun _ => i)).isUnit.map _).map ρ).ne_zero
  refine exists_linear_of_log_deriv u hL a B ha hfr w (fun i z => κ (F i z) * (ρ (F i z))⁻¹)
    (fun i => (hF i κ).mul ((hF i ρ.toLinearMap).inv (hF0 i))) (fun i z l hl => ?_) (fun i i' z hz hz' => ?_)
  · have : F i (z + l) = F i z := by
      rw [hFdef, hFdef, famPt, famPt, ex_add_lattice u z hl]
    simp only [this]
  · have a1 := ThetaGroupFrame.top_le_inf _ hz hz'
    have a0 : ⊤ ≤ (x ≫ translBy u z).left ⁻¹ᵁ (L.U i ⊓ L.U i') :=
      (top_le_iff_residue ρ.toRingHom _ _ (residue_transl u ρ x hx z) _).2 a1
    have e := evalPt_gen_two (R := R) L _ _ c hc _ _ _ (famPt_transl u x z) (famPt_snd u z)
      (fun _ => i) (fun _ => i') (hD i z hz) (hD i' z hz') a0 (top_le_const _ _ a1)
    have hρ : ρ (evalPt (R := R) (x ≫ translBy u z).left _ a0 (L.g i i').val) = _ :=
      residue_evalPt ρ.toRingHom _ _ (residue_transl u ρ x hx z) _ a0 (L.g i i').val
    have k := first_order_transl u ρ x κ w hκ z _ a0 (L.g i i').val (F i' z)
    have e' : F i z * algebraMap ℂ R (valAt' (u.ex z).left _ (L.g i i').val) =
        evalPt (R := R) (x ≫ translBy u z).left _ a0 (L.g i i').val * F i' z := by
      rw [hFdef, hFdef, evalPt'_eq _ (hD i z hz), evalPt'_eq _ (hD i' z hz'),
        ← evalPt_const (R := R) _ _ (top_le_const _ _ a1) a1]
      exact e
    have n0 := valAt'_unit_ne_zero _ a1 (L.g i i')
    have n2 := hF0 i' z hz'
    exact log_deriv_rule ρ κ e' hρ k n0 n2

end Main

theorem eq_one_of_gen_translDiff :
    (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w)) w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) → (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), (∃ (U : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)) → (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → ∀ (g : ℕ) (u : HolUnif A L g) (a : u.Λ → ℂ) (B : u.Λ → ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∃ (U : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) → (∀ l, a l ≠ 0) → (∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = a l * cexp (B l z) * u.fr i (z + l)) → (∀ (w : Fin g → ℂ) (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ), (∀ l : u.Λ, cexp (B l w) = cexp (lam l)) → w ∈ u.Λ) → (∀ (w : Fin g → ℂ) (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ), (∀ l : u.Λ, B l w = lam l) → w = 0) → (∀ (R : Type) [CommRing R] [Algebra ℂ R], IsLocalRing R → Module.Finite ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1)) := by
  rintro hp - A _ L - hL g u a B ⟨U, t, hU, h0, huniq, ht⟩ ha hfr hΛ hnd R _ _ _ _ x ⟨c, hc⟩
  obtain ⟨ρ, hρ⟩ := exists_residue (R := R)
  obtain ⟨w, hw⟩ := u.ex_onto (resPt ρ ≫ x)
  obtain ⟨lam, hlam⟩ := exists_linear_of_gen u hL a B ha hfr (resPt ρ) x w hw.symm (fun V f => by
    simpa using (hp (Fin g → ℂ) Set.univ (spO R) A (fun _ => resPt ρ) u.ex
      (fun U f => ⟨by simpa using isOpen_const, differentiableOn_const _⟩)
      (fun U f => by simpa using u.hol U f) V f).2) c hc
  have hx : resPt ρ ≫ x = 1 := hw.symm.trans ((u.ker w).2 (hΛ w lam hlam))
  by_contra hx1
  obtain ⟨κ, v, -, hv, hκ⟩ := exists_first_order u ρ hρ hU h0 huniq ht x (hx.trans (ex_zero u).symm) hx1
  obtain ⟨lam', hlam'⟩ := exists_linear_of_first_order u hL a B ha hfr ρ x hx κ v hκ c hc
  exact hv (hnd v lam' hlam')

end GlobalTheory.ArtinKernel
