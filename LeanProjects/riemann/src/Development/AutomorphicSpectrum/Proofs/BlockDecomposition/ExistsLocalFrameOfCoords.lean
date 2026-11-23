import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
open TensorProduct DividedPowers

namespace GlobalTheory.CompanionTheory.ConeLocal

theorem dividedPowerFiltration_dividedPowersBot_of_one_le {K : Type} [CommRing K] {r : ℕ} (hr : 1 ≤ r) : pdP (dividedPowersBot K) r = ⊥ := by
  refine Ideal.span_eq_bot.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have h : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra h
    push Not at h
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by simpa using h)
    omega
  obtain ⟨p, hp, h0⟩ := h
  refine List.prod_eq_zero (List.mem_map.2 ⟨p, hp, ?_⟩)
  have e : p.2 = 0 := hl p hp
  rw [e]
  exact (dividedPowersBot K).dpow_eval_zero h0

theorem tfBase_dpBot {K : Type} [Field K] [CharZero K] {s : ℕ} (hs : 1 ≤ s) : TFBase (dividedPowersBot K) 1 s where
  nil := dividedPowerFiltration_dividedPowersBot_of_one_le hs
  tf r x h := by simpa using h
  dv n hn := ⟨0, (n : K)⁻¹, by
    have : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
    simp [this]⟩

theorem exists_loc : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ), 1 ≤ s →
    ∃ (E : Frame (sP (KS q s {W})) d) (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε := by
  intro K _ _ X q W d c s hs
  have hb : TFBase (dividedPowersBot K) 1 s := tfBase_dpBot hs
  obtain ⟨c', e, hTF, he1, he2, he3⟩ := GlobalTheory.CompanionTheory.ChartAlg.chart_exists (O := K) (R := K) (dividedPowersBot K) 1 s hb q
    (Ideal.Quotient.mk ⊥) (fun a => rfl) c
  letI := (strV q W).toAlgebra
  have hg := GlobalTheory.CompanionTheory.ChartMaps.good c'
  have hD : KS q s {W} c'.D := ⟨hTF, W, rfl, c'.inV⟩
  obtain ⟨hpow, hc⟩ := GlobalTheory.CompanionTheory.ChartFil.chart_grConst c' hg (KS q s {W}) (ks_in q s W) hD
  let E := c'.frame hg (KS q s {W}) (ks_in q s W) hD
  let ε : Γ(X, W) ≃+* c'.D.B := (Algebra.TensorProduct.lid K Γ(X, W)).symm.toRingEquiv.trans e
  have hε : ∀ f, ε f = e ((1 : K) ⊗ₜ[K] f) := fun f => rfl
  refine ⟨E, ε, hc, fun x hx => ?_, fun a => ?_, fun T u g => ?_, fun i T u v => ?_⟩
  · have h2 : (show c'.D.B from x) ∈ c'.D.pdPow 1 := hx
    rw [hpow, dividedPowerFiltration_dividedPowersBot_of_one_le le_rfl, Ideal.map_bot] at h2
    exact Ideal.mem_bot.1 h2
  · have e1 : (1 : K) ⊗ₜ[K] (strV q W a) = a ⊗ₜ[K] (1 : Γ(X, W)) := by
      have : strV q W a = a • (1 : Γ(X, W)) := by
        rw [Algebra.smul_def, mul_one]; rfl
      rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change ε (strV q W a) = c'.D.i a
    rw [hε, e1, he1]
  · have h1 := GlobalTheory.CompanionTheory.GrForm.ev_nat (q := q) u.hom c'.inV (ks_in q s W _ T.property) g
    exact h1.trans ((congrArg (Ideal.quotientMap T.obj.J u.hom.φ u.hom.hle) (he3 g)).trans rfl)
  · change (v.hom.φ (c'.t i) - u.hom.φ (c'.t i) : T.obj.B) = v.hom.φ (ε (c.t i)) - u.hom.φ (ε (c.t i))
    rw [hε, he2]

end GlobalTheory.CompanionTheory.ConeLocal
