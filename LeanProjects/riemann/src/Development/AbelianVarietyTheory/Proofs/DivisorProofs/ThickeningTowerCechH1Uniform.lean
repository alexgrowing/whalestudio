import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousFormOfOverlapIdealPowThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormKilledByPowerOfTripleChartProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedRatiosEvalIdealMulEqZeroSuccStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormChartChangeCoeffIdealPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosProjectiveRelationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSerreVanishingCechCocyclesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg.TowerH1
variable {R : Type} [CommRing R] {I : Ideal R}
  {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}

theorem cst_eq_zero (e : ℕ) (V : (Y e).left.Opens) {a : R} (ha : a ∈ I ^ (e + 1)) :
    AbLaw.cst ((Y e).hom ≫ thick R I e) V a = 0 := by
  have h : (thick R I e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = 0 := by
    have := congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← this]
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  simp only [AbLaw.cst, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, h, map_zero]

theorem mul_eq_zero_of_mem (e : ℕ) (V : (Y e).left.Opens) {x y : Γ((Y e).left, V)}
    (hx : x ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) : x * y = 0 := by
  have h : x * y ∈ towerIdeal Y e (I ^ (e + 1)) V := by
    have h0 := Ideal.mul_mem_mul hx hy
    unfold towerIdeal at h0 ⊢
    rw [← Ideal.map_mul, ← pow_succ'] at h0
    exact h0
  have hb : towerIdeal Y e (I ^ (e + 1)) V = ⊥ := by
    unfold towerIdeal
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    exact cst_eq_zero e V ha
  rw [hb] at h
  exact h

theorem mul_eq_mul_of_sub_mem (e : ℕ) (V : (Y e).left.Opens) {x x' y : Γ((Y e).left, V)}
    (hx : x - x' ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) : x * y = x' * y := by
  have := mul_eq_zero_of_mem e V hx hy
  rw [sub_mul] at this
  exact sub_eq_zero.1 this

theorem pow_mul_eq_pow_mul_of_sub_mem (e : ℕ) (V : (Y e).left.Opens) {x x' y : Γ((Y e).left, V)}
    (hx : x - x' ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) (m : ℕ) :
    x ^ m * y = x' ^ m * y :=
  mul_eq_mul_of_sub_mem e V (Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow x x' m) hx) hy

theorem pow_mul_eq_of_sub_one_mem (e : ℕ) (V : (Y e).left.Opens) {x y : Γ((Y e).left, V)}
    (hx : x - 1 ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) (m : ℕ) : x ^ m * y = y := by
  rw [pow_mul_eq_pow_mul_of_sub_mem e V hx hy m, one_pow, one_mul]

theorem rs_mem (e : ℕ) (J : Ideal R) {U V : (Y e).left.Opens} (h : V ≤ U) {x : Γ((Y e).left, U)}
    (hx : x ∈ towerIdeal Y e J U) : rs (Y e).left h x ∈ towerIdeal Y e J V := by
  unfold towerIdeal at hx ⊢
  have h1 := Ideal.mem_map_of_mem (rs (Y e).left h) hx
  rw [Ideal.map_map] at h1
  have h2 : (rs (Y e).left h).comp (AbLaw.cst ((Y e).hom ≫ thick R I e) U) = AbLaw.cst ((Y e).hom ≫ thick R I e) V :=
    RingHom.ext fun r => rs_cst _ h r
  rwa [h2] at h1

theorem isUnit_rs_of_le_basicOpen {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U))
    (hb : V ≤ X.basicOpen f) : IsUnit (rs X h f) := by
  have hu : IsUnit (rs X (X.basicOpen_le f) f) := X.toRingedSpace.isUnit_res_basicOpen f
  have := hu.map (rs X hb)
  rwa [rs_rs] at this

end GlobalTheory.FormalAlg.TowerH1

namespace GlobalTheory.FormalAlg.TowerH1

theorem ev_X {R : Type} [CommRing R] {I : Ideal R}
    {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {n : ℕ} (C : Charts I Y β n) (e : ℕ) (i m : Fin (n + 1)) :
    C.ev e i (MvPolynomial.X m) = C.ρ e i m := by
  simp only [Charts.ev, MvPolynomial.eval₂Hom_X']

end GlobalTheory.FormalAlg.TowerH1

open GlobalTheory.FormalAlg.TowerH1 in

theorem GlobalTheory.FormalAlg.towerCech_h1_uniform : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ e : ℕ, (∀ c : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j), (∀ i j, c i j ∈ towerIdeal Y e (I ^ e) _) → (∀ i j l, rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e j) (c i j) + rs (Y e).left (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) (C.ρ e i j) ^ k * rs (Y e).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j ⊓ C.D e l) (c j l) = rs (Y e).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e l) (c i l)) → ∃ a : ∀ i, Γ((Y e).left, C.D e i), (∀ i, a i ∈ towerIdeal Y e (I ^ e) _) ∧ ∀ i j, c i j = rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (a i) - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (a j)) := by
  intro R _ _ I Y β hβ n C
  classical
  let J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R) := fun e => ⨅ i, RingHom.ker (C.ev e i)
  have hJ : ∀ e F, F ∈ J e ↔ ∀ i, C.ev e i F = 0 := by
    intro e F
    simp only [J, Ideal.mem_iInf, RingHom.mem_ker]
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.uniform_serre_vanishing_cech_cocycles R I n J (fun e t a F ha _ _ hF =>
    (hJ _ _).2 fun i => GlobalTheory.T.liftedRatios_eval_ideal_mul_eq_zero_succ R I Y β hβ n C e a F i ha ((hJ e F).1 hF i))
  refine ⟨d₀, fun k hk e c hc hcoc => ?_⟩
  have lev := GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hβ n C
  choose N₀ hN₀ using fun i j => GlobalTheory.T.exists_homogeneous_form_of_overlap_ideal_pow_thickening R I Y β hβ n C e i j (c i j) (hc i j)
  let N := Finset.univ.sup (fun p : Fin (n + 1) × Fin (n + 1) => N₀ p.1 p.2)
  have hN : ∀ i j, N₀ i j ≤ N := fun i j =>
    Finset.le_sup (f := fun p : Fin (n + 1) × Fin (n + 1) => N₀ p.1 p.2) (Finset.mem_univ (i, j))
  choose F hFh hFc hFe using fun i j => hN₀ i j N (hN i j) k
  have hFm : ∀ i j, F i j ∈ Ideal.map MvPolynomial.C (I ^ e) := fun i j =>
    MvPolynomial.mem_map_C_iff.2 (hFc i j)

  have htri : ∀ i j l, ∃ L : ℕ, ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) * MvPolynomial.X j * MvPolynomial.X l) ^ L *
      (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l - MvPolynomial.X j ^ N * F i l) ∈ J e := by
    intro i j l
    have hH : (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l - MvPolynomial.X j ^ N * F i l :
        MvPolynomial (Fin (n + 1)) R).IsHomogeneous (N + (k + 2 * N)) :=
      (((MvPolynomial.isHomogeneous_X_pow l N).mul (hFh i j)).add
        ((MvPolynomial.isHomogeneous_X_pow i N).mul (hFh j l))).sub
        ((MvPolynomial.isHomogeneous_X_pow j N).mul (hFh i l))
    have hHc : ∀ m, MvPolynomial.coeff m (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l -
        MvPolynomial.X j ^ N * F i l : MvPolynomial (Fin (n + 1)) R) ∈ I ^ e :=
      MvPolynomial.mem_map_C_iff.1 (sub_mem (add_mem (Ideal.mul_mem_left _ _ (hFm i j))
        (Ideal.mul_mem_left _ _ (hFm j l))) (Ideal.mul_mem_left _ _ (hFm i l)))

    have hTij : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e j := inf_le_left
    have hTil : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e l := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hTjl : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j ⊓ C.D e l := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hTi : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i := inf_le_left.trans inf_le_left
    have hTj : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j := inf_le_left.trans inf_le_right
    have h1 : rs (Y e).left hTi (C.ev e i (F i j)) =
        rs (Y e).left hTi (C.ρ e i j) ^ N * rs (Y e).left hTij (c i j) := by
      have := congrArg (rs (Y e).left hTij) (hFe i j)
      simpa only [rs_rs, map_mul, map_pow] using this
    have h3 : rs (Y e).left hTi (C.ev e i (F i l)) =
        rs (Y e).left hTi (C.ρ e i l) ^ N * rs (Y e).left hTil (c i l) := by
      have := congrArg (rs (Y e).left hTil) (hFe i l)
      simpa only [rs_rs, map_mul, map_pow] using this
    have h2 : rs (Y e).left hTi (C.ev e i (F j l)) =
        rs (Y e).left hTi (C.ρ e i j) ^ (k + 2 * N) * (rs (Y e).left hTj (C.ρ e j l) ^ N *
          rs (Y e).left hTjl (c j l)) := by
      have t1 := congrArg (rs (Y e).left hTij)
        (GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hβ n C e (k + 2 * N) (F j l) (hFh j l) (hFc j l) i j).2.2
      have t2 := congrArg (rs (Y e).left hTjl) (hFe j l)
      simp only [rs_rs, map_mul, map_pow] at t1 t2
      rw [t1, t2]
    have hcjl : rs (Y e).left hTjl (c j l) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hTjl (hc j l)
    have hP : rs (Y e).left hTi (C.ρ e i i) - 1 ∈ towerIdeal Y e I _ := by
      have := rs_mem e I hTi (lev.2.1 e i)
      rwa [map_sub, map_one] at this
    have hB : rs (Y e).left hTi (C.ρ e i l) - rs (Y e).left hTi (C.ρ e i j) * rs (Y e).left hTj (C.ρ e j l)
        ∈ towerIdeal Y e I _ := by
      have := rs_mem e I hTij (lev.2.2 e i j l)
      simpa only [map_sub, map_mul, rs_rs] using this
    have e1 := pow_mul_eq_of_sub_one_mem e _ hP hcjl N
    have e2 := pow_mul_eq_pow_mul_of_sub_mem e _ hB hcjl N
    have hyp := hcoc i j l
    have hz : rs (Y e).left hTi (C.ev e i (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l -
        MvPolynomial.X j ^ N * F i l)) = 0 := by
      simp only [map_add, map_sub, map_mul, map_pow, ev_X]
      rw [h1, h2, h3]
      linear_combination (rs (Y e).left hTi (C.ρ e i j) ^ (k + 2 * N) * rs (Y e).left hTj (C.ρ e j l) ^ N) * e1 -
        rs (Y e).left hTi (C.ρ e i j) ^ (k + N) * e2 +
        rs (Y e).left hTi (C.ρ e i j) ^ N * rs (Y e).left hTi (C.ρ e i l) ^ N * hyp
    obtain ⟨L, hL⟩ := GlobalTheory.T.homogeneousForm_killed_by_power_of_tripleChart_product R I Y β hβ n C e _ _ hH hHc i j l hz
    exact ⟨L, (hJ _ _).2 hL⟩

  obtain ⟨N', G, hGh, hGc, hrel⟩ := hd₀ k hk e N F hFh hFc htri
  have tr := fun i j => GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hβ n C e (k + N') (G j) (hGh j) (hGc j) i j
  refine ⟨fun i => C.ev e i (G i), fun i => (tr i i).1, fun i j => ?_⟩
  obtain ⟨L, hL⟩ := hrel i j
  have hl : C.D e i ⊓ C.D e j ≤ C.D e i := inf_le_left
  have hr : C.D e i ⊓ C.D e j ≤ C.D e j := inf_le_right
  have h0 := congrArg (rs (Y e).left hl) ((hJ _ _).1 hL i)
  simp only [map_mul, map_sub, map_pow, ev_X, map_zero] at h0
  rw [hFe i j, (tr i j).2.2] at h0
  have hci := hc i j
  have hai : rs (Y e).left hl (C.ev e i (G i)) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hl (tr i i).1
  have haj : rs (Y e).left hr (C.ev e j (G j)) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hr (tr j j).1
  have hP : rs (Y e).left hl (C.ρ e i i) - 1 ∈ towerIdeal Y e I _ := by
    have := rs_mem e I hl (lev.2.1 e i)
    rwa [map_sub, map_one] at this
  have ec := pow_mul_eq_of_sub_one_mem e _ hP hci (L + N')
  have ea := pow_mul_eq_of_sub_one_mem e _ hP hai (L + N)
  have eb := pow_mul_eq_of_sub_one_mem e _ hP haj (L + N + N')
  have hu : IsUnit (rs (Y e).left hl (C.ρ e i j) ^ (L + N + N')) :=
    (isUnit_rs_of_le_basicOpen hl _ (lev.1 e i j).ge).pow _
  have hw : rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * (c i j - (rs (Y e).left hl (C.ev e i (G i)) -
      rs (Y e).left hl (C.ρ e i j) ^ k * rs (Y e).left hr (C.ev e j (G j)))) = 0 := by
    linear_combination h0 - rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * ec +
      rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * ea -
      rs (Y e).left hl (C.ρ e i j) ^ (L + N + N' + k) * eb
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 hw)
