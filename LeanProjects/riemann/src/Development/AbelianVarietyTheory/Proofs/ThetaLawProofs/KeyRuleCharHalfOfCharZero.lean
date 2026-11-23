import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyPBId
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaLawZeroOfEven
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NonzeroLocusConstMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsKeyPow
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LatticeBlocks
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaLawSymplecticNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueAtNormalForm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyPow

theorem IsKeyPow.dim_eq {R : Type} [CommRing R] {y x : KeyIn R} {j : ℕ} (h : IsKeyPow y x j) :
    y.P.g = j * x.P.g := by
  obtain ⟨_, hg, -⟩ := h
  exact hg.symm

theorem IsKeyPow.two_le_dim {R : Type} [CommRing R] {y x : KeyIn R} (h : IsKeyPow y x 2) : 2 ≤ y.P.g := by
  have := x.g_pos
  rw [h.dim_eq]
  omega

theorem exists_int_half {g : ℕ} {a : Fin g → ℂ} (h : ∀ i, a i = 0 ∨ a i = 1 / 2) :
    ∃ n : Fin g → ℤ, a = fun i => (((n i : ℝ) / 2 : ℝ) : ℂ) := by
  have : ∀ i, ∃ m : ℤ, a i = (((m : ℝ) / 2 : ℝ) : ℂ) := fun i => by
    rcases h i with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose n hn using this
  exact ⟨n, funext hn⟩

theorem even_dot_double {g g' : ℕ} (e : Fin 2 × Fin g ≃ Fin g') (n n' : Fin g → ℤ) :
    Even ((fun p => n (e.symm p).2) ⬝ᵥ (fun p => n' (e.symm p).2)) := by
  refine ⟨n ⬝ᵥ n', ?_⟩
  unfold dotProduct
  rw [← e.sum_comp]
  simp [Fintype.sum_prod_type, two_mul]

theorem keyRule_charHalf_of_charZero : ReciprocityTheory.ChartRestriction.G.Key.Chi.InversionStatement → ∀ N : ℕ → ℕ,
    GlobalTheory.KeyPow.KeyRule N 2 GlobalTheory.KeyPow.charZero' →
      GlobalTheory.KeyPow.KeyRule (fun g => 2 * N (2 * g)) 1 GlobalTheory.KeyPow.charHalf := by
  intro hinv N ⟨κ, hH, hF, hU, hN⟩
  have hex : ∀ (R : Type) [CommRing R] (x : KeyIn R), ∃ y, IsKeyPow y x 2 :=
    fun R _ x => GlobalTheory.KeyPow.exists_isKeyPow R x 2 (by norm_num)
  choose sq hsq using hex
  have indep : ∀ (K : Type) [Field K] [CharZero K] (x y : KeyIn K), IsKeyPow y x 2 →
      (κ K (sq K x) : K) = κ K y := fun K _ _ x y hy =>
    hF K K (RingHom.id K) y (sq K x) hy.two_le_dim
      (GlobalTheory.KeyPow.keyPB_of_isKeyPow K K (RingHom.id K) x y x (sq K x) 2 (GlobalTheory.keyPB_id K x) hy (hsq K x))
  refine ⟨fun K _ _ x => κ K (sq K x), ?_, ?_, ?_, ?_⟩
  · intro K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M _ h₁ h₂
    have hy := hsq K ⟨P, hg, rig, hr, th, hth, v, hv⟩
    obtain ⟨t, ht, w, hw, M', hp, ht', hw', hd⟩ :=
      GlobalTheory.PowChange.isKeyPow_change K P hg rig hr th hth v hv th' hth' v' hv' a M 2 _ h₁ h₂ hy
    have key := hH K _ (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).g_pos _
      (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).rig_gen _ (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).th_ne _
      (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).basis t ht w hw (a ^ 2) M' hy.two_le_dim ht' hw'
    have hdim : (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).P.g = 2 * P.g := hy.dim_eq
    dsimp only
    rw [indep K _ _ hp]
    rw [hd, ← pow_mul, ← pow_mul] at key
    rw [← hdim, show 8 * (2 * N (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).P.g) =
      2 * (8 * N (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).P.g) by ring,
      show 4 * (2 * N (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).P.g) =
      2 * (4 * N (sq K ⟨P, hg, rig, hr, th, hth, v, hv⟩).P.g) by ring]
    exact key
  · intro K K' _ _ _ _ f x x' _ h
    exact hF K K' f _ _ (hsq K x).two_le_dim (GlobalTheory.KeyPow.keyPB_of_isKeyPow K K' f x _ x' _ 2 h (hsq K x) (hsq K' x'))
  · intro R K _ _ _ _ _ _ _ x xK _ h
    obtain ⟨u, hu, hu'⟩ := hU R K (sq R x) (sq K xK) (hsq R x).two_le_dim
      (GlobalTheory.KeyPow.keyPB_of_isKeyPow R K _ x _ xK _ 2 h (hsq R x) (hsq K xK))
    exact ⟨u, hu, fun k _ _ r xk hr hk =>
      hu' k r (sq k xk) hr (GlobalTheory.KeyPow.keyPB_of_isKeyPow R k r x _ xk _ 2 hk (hsq R x) (hsq k xk))⟩
  · intro x τ a b _ hab hx
    obtain ⟨n, rfl⟩ := exists_int_half hab.1
    obtain ⟨n', rfl⟩ := exists_int_half hab.2
    have hy := hsq ℂ x
    obtain ⟨e, τ', M', hd, hn⟩ := GlobalTheory.KeyPow.normalAt_pow x _ 2 τ 1 (fun i => (n i : ℝ) / 2) (fun i => (n' i : ℝ) / 2) 1 hy hx
    obtain ⟨sp, hsp, hlaw⟩ := GlobalTheory.KeyPow.exists_thetaLaw_zero_of_even hinv _ _ _ (even_dot_double e n n')
    obtain ⟨M'', c, hc, hq, hn'⟩ := GlobalTheory.T.theta_law_symplectic_normal_form (sq ℂ x) τ' M' (1 ^ 2) sp _ _ 0 0 hsp hlaw (by simp)
      (by simpa using hn)
    have hq' : M''.det ^ 4 / c ^ 8 = 1 := by rw [hq, hd]; simp
    have hM : M''.det ≠ 0 := fun h => by simp [h] at hq'
    have := GlobalTheory.KeyPow.value_at_normalForm N 2 (κ ℂ) (sq ℂ x).P.g 0 0 hy.two_le_dim (hH ℂ)
      (fun z hz τ h => hN z τ _ _ (hz ▸ hy.two_le_dim) ⟨rfl, rfl⟩ h) (sq ℂ x) rfl _ M'' c hc hM
      (by simpa using hn')
    rw [hq', _root_.one_pow] at this
    exact Units.ext this

end GlobalTheory.KeyPow
end
