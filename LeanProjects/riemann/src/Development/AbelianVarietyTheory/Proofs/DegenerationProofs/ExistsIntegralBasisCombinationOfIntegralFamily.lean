import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationNonnegIffSpanMultiplicationTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreSectionLinearCombExistsUniqueThetaActionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionLinearCombIffExpansionSumStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelValuationDataStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionPointsGroupPairingStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetricLiftNormalisedPullbackThetaSmulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory.TestFibre

theorem exists_nsmul_of_nsmul_eq_zero {K : Type} {r N : ℕ} (hr : 0 < r) (hN : 0 < N) (a₀ : K → ZMod (r * N))
    (h : N • a₀ = 0) : ∃ a : K → ZMod (r * N), r • a = a₀ := by
  haveI : NeZero (r * N) := ⟨(Nat.mul_pos hr hN).ne'⟩
  have key : ∀ i, ∃ b : ZMod (r * N), r • b = a₀ i := by
    intro i
    have h1 : ((N * (a₀ i).val : ℕ) : ZMod (r * N)) = 0 := by
      have := congrFun h i
      simpa [nsmul_eq_mul] using this
    rw [ZMod.natCast_eq_zero_iff, _root_.mul_comm N] at h1
    obtain ⟨d, hd⟩ := Nat.dvd_of_mul_dvd_mul_right hN h1
    refine ⟨(d : ZMod (r * N)), ?_⟩
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← hd, ZMod.natCast_zmod_val]
  choose a ha using key
  exact ⟨a, funext ha⟩

theorem exists_span_translates_of_eq_sq (h : Laws) (h₂ : Laws2) {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V] (hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V) {ϖ : V}
    (hϖ : Irreducible ϖ) {D : DegData V (IsLocalRing.maximalIdeal V)} {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif (IsLocalRing.maximalIdeal V) D A G)
    (w₀ : W0 U.toUnifPre) (rig : LB.Gen (A.L.pull (eSec A.A))) (hw : NormW U.toUnifPre w₀ rig)
    (th th' : SecA A F 1) (ϑ : Fam D.toPre F 1) (hϑ : U.ExpandsF F 1 w₀ th' ϑ) (hP : Prim D Q v ϑ) (c : F)
    (hth : ∀ j, th.f j = liftFun A.A _ (cF V c) * th'.f j) (m : ℕ) (hm : Odd m) (hu : IsUnit (m : V)) (h3 : 3 ≤ m)
    (N : ℕ) (hN : N = m ^ 2) (Φ : Fam D.toPre F N) (hΦ : NuGe D Q F v N Φ 0) :
    ∃ (n : ℕ) (a : Fin n → F) (z : Fin n → (TFK (R := V) F ⟶ A.A)) (t : Fin n → SecA A F N)
      (r : Fin n → Fam D.toPre F N),
      (∀ i, 0 ≤ v (a i) ∧ z i ^ N = 1 ∧ U.ExpandsF F N w₀ (t i) (r i) ∧
        ∀ (s₁ σ : SecA A F N) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := V) F)), IsNormPull A rig m N th s₁ →
          SymLift A.A A.L (N : ℤ) N (z i) θ → IsActOf A.A A.L (N : ℤ) θ s₁ σ →
          ∀ j, σ.f j = liftFun A.A _ (cF V c) * (t i).f j) ∧ Φ = ∑ i, a i • r i := by
  subst hN
  obtain ⟨hL, h1, h2, h3', h4⟩ := laws_all h h₂
  obtain ⟨n, a, z, t, c', r, H, hs⟩ :=
    (GlobalTheory.T.valuation_nonneg_iff_span_multiplicationTranslates hL h1 h2 h3' h4 V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ rig hw th' ϑ hϑ hP m hm hu h3 Φ).1 hΦ
  refine ⟨n, a, z, t, r, fun i => ?_, hs⟩
  obtain ⟨ha, hz, hT, hE⟩ := H i
  exact ⟨ha, hz, hE, fun s₁ σ θ hs₁ hθ hσ =>
    GlobalTheory.T.symmetricLift_normalisedPullback_theta_smul hL V A F rig hw.2.1 m hm th th' c hth s₁ σ (t i) (z i) θ (c' i) hz hs₁ hθ hσ hT⟩

theorem IsComb.of_eq_mul {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} {J : Type} [Fintype J] {s : J → SecA A F k} {b : J → F}
    {σ t : SecA A F k} (hσ : IsComb A s b σ) {c : F} (hc : c ≠ 0)
    (ht : ∀ j, σ.f j = liftFun A.A _ (cF R c) * t.f j) : IsComb A s (fun l => c⁻¹ * b l) t := by
  intro j
  have hmul : ∀ x y : F, (liftFun A.A _ (cF R (x * y)) : Γ((TFK (R := R) F ⊗ A.A).left, (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U j)) = liftFun A.A _ (cF R x) * liftFun A.A _ (cF R y) := by
    intro x y
    simp only [liftFun, cF, map_mul]
  have hone : (liftFun A.A _ (cF R (1 : F)) : Γ((TFK (R := R) F ⊗ A.A).left, (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U j)) = 1 := by
    simp only [liftFun, cF, map_one]
  have h1 : t.f j = liftFun A.A _ (cF R c⁻¹) * σ.f j := by
    rw [ht j, ← _root_.mul_assoc, ← hmul, inv_mul_cancel₀ hc, hone, _root_.one_mul]
  rw [h1, hσ j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [hmul, _root_.mul_assoc]

theorem exists_isComb_expands_of_nuGe_zero : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ → ValOver ϖ (PadicAlgCl p) v → NormIs u l ϖ Q v lam → ∀ (w₀ : W0 u.U.toUnifPre) (th' : SecA u.A (PadicAlgCl p) 1) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1) (c : PadicAlgCl p), NormW u.U.toUnifPre w₀ rig → u.U.ExpandsF (PadicAlgCl p) 1 w₀ th' ϑ → Prim u.D Q v ϑ → (∀ j, th.f j = liftFun u.A.A _ (cF u.V c) * th'.f j) → c ≠ 0 → ∀ Φ : Fam u.D.toPre (PadicAlgCl p) S.N, NuGe u.D Q (PadicAlgCl p) v S.N Φ 0 → ∃ (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N), (∀ j, ‖c * b j‖ ≤ 1) ∧ IsComb u.A s b σ ∧ u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ := by
  intro h h₂ _ o Ω _ _ _ _ S ρ p _ y₀ u l hy x rig e th s hx hs ϖ Q v lam hϖ hv hNorm w₀ th' ϑ c hw hϑ hP hth hc Φ hΦ
  obtain ⟨hchar, hun, hadm, -⟩ := GlobalTheory.T.uniformisedModel_valuation_data o Ω S ρ p y₀ u l hy
  obtain ⟨hadd, -, hbij, -⟩ := (GlobalTheory.T.uniformisedModel_torsionPoints_group_pairing h o Ω S ρ p y₀ u).2 x hx
  obtain ⟨-, -, -, -, hpull, hact⟩ := hs
  obtain ⟨-, hQ, -, hle, -⟩ := hNorm
  have hN0 : 0 < S.N := lt_of_lt_of_le (by norm_num) S.N_ge
  have hn3 : 3 ≤ ρ.n := by
    have h2 := ρ.n_prime.two_le
    obtain ⟨d, hd⟩ := ρ.n_odd
    omega
  have hm3 : 3 ≤ ρ.n ^ ρ.k :=
    hn3.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  have hmu : IsUnit ((ρ.n ^ ρ.k : ℕ) : u.V) := by
    rw [Nat.cast_pow]; exact hun.pow _
  obtain ⟨n, a, z, t, r, H, hΦs⟩ := exists_span_translates_of_eq_sq h h₂ u.complete hϖ hQ hv u.semi u.U w₀ rig hw
    th th' ϑ hϑ hP c hth (ρ.n ^ ρ.k) ρ.n_odd.pow hmu hm3 S.N ρ.N_eq Φ hΦ
  have hx0 : x 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hxs : ∀ (k : ℕ) (b : S.Gam), x (k • b) = x b ^ k := by
    intro k b
    induction k with
    | zero => rw [zero_nsmul, hx0, pow_zero]
    | succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hpt : ∀ i, ∃ g : S.Gam, x (S.r • g) = z i := by
    intro i
    obtain ⟨a₀, ha₀, -⟩ := hbij (z i) (by rw [_root_.mul_comm S.r, pow_mul, (H i).2.1, one_pow])
    obtain ⟨a₁, -, hu₁⟩ := hbij 1 (one_pow _)
    have h0 : S.N • a₀ = 0 :=
      (hu₁ _ (by show x _ = 1; rw [hxs, ha₀, (H i).2.1])).trans (hu₁ 0 hx0).symm
    obtain ⟨g, hg⟩ := exists_nsmul_of_nsmul_eq_zero S.r_pos hN0 a₀ h0
    exact ⟨g, by rw [← ha₀, ← hg]⟩
  choose g hg using hpt
  have ht : ∀ i, IsComb u.A s (fun j => c⁻¹ * y₀ (algebraMap o S.R (S.ρ (g i) j ρ.i₀))) (t i) := by
    intro i
    obtain ⟨θ, hθ, hθa⟩ := hact (g i)
    obtain ⟨σ, hσ, -⟩ := (GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N S.J s (fun _ => 0)).2.2.2.1 θ (s ρ.i₀)
    rw [hg] at hθ
    exact IsComb.of_eq_mul (hθa _ _ hσ) hc ((H i).2.2.2 _ σ θ hpull hθ hσ)
  obtain ⟨σ, hσ⟩ := (GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N (Fin n) t a).1
  refine ⟨_, σ, fun j => ?_,
    (GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N S.J s (fun _ => 0)).2.2.2.2 (Fin n) _ t a σ ht hσ, ?_⟩
  · rw [Finset.mul_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [← _root_.mul_assoc, mul_inv_cancel_left₀ hc, norm_mul]
    have h1 : ‖a i‖ ≤ 1 := by
      have := (hle (a i) 0).1 (by simpa using (H i).1)
      simpa using this
    exact mul_le_one₀ (hy _) (norm_nonneg _) h1
  · rw [hΦs]
    exact (GlobalTheory.T.isFibreSectionLinearComb_iff_expansion_sum (laws_all h h₂).1 u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hN0 w₀ hw.1
      (Fin n) t r a σ fun i => (H i).2.2.1).1 hσ

end GlobalTheory.TestFibre
