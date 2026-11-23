import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaRR.Elim

variable {k : Type} [CommRing k] {S : Scheme.{0}} [IsIntegral S] {p : S ⟶ Sp k}

theorem lin_single {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) :
    (lin fun j => (((Pi.single i 1 : ι → ℤ) j : ℤ) : ℝ)) = MvPolynomial.X i := by
  simp [lin, Pi.single_apply, apply_ite, ite_mul]

theorem gdeg_triv (HC : GlobalTheory.Published.ArCalc) {d : ℕ} (hp : IsArithVar p (d + 1)) :
    gdeg (HermLB.triv p) (d + 1) = 0 := by
  obtain ⟨Ψ, hΨ⟩ := ((HC.arExists k S p _ hp).2 (Fin 0) fun i => i.elim0).2
  have e := hΨ.1 0
  simp only [lin, comb, Finset.univ_eq_empty, Finset.sum_empty, Finset.toList_empty, List.foldr_nil] at e
  rw [← e]
  simp

theorem gdeg_fnB_const (HC : GlobalTheory.Published.ArCalc) {d : ℕ} (hp : IsArithVar p (d + 1)) (c : ℝ) (hu) (hc) :
    gdeg (fnB (p := p) (fun _ _ => c) hu hc) (d + 1) = 0 := by
  rw [(HermLB.isometric_raise_triv _ hu hc).gdeg_eq, ← gdeg_triv HC hp]
  simp only [gdeg, chInt, HermLB.raise, Weight.chernInt, Weight.chernPart_addFn_const]

theorem elim : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (S : Scheme.{0}) [IsIntegral S] (p : S ⟶ Sp k), IsRegSurf p → ∀ (M D : HermLB p) (t I a ρ : ℝ), (∀ (N : HermLB p) (Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ), IsArFun ![M, D, N] 1 Ψ → Ψ (MvPolynomial.X 0 * MvPolynomial.X 2) - t * gdeg N 1 / 2 = -(Ψ (MvPolynomial.X 1 * MvPolynomial.X 2) / 2) ∧ Ψ (MvPolynomial.X 0 ^ 2) / 2 - I / 2 = Ψ (MvPolynomial.X 1 ^ 2) / 8 - a / 12 + ρ / 2 * gdeg D 1) → a = 6 * I + (6 * ρ + 3 * t) * gdeg D 1 := by
  intro HC k _ S _ p hS M D t I a ρ H
  have hp : IsArithVar p 1 := hS.toIsArithVar
  have hu (σ : k →+* ℂ) (y : CxPts p σ) : CInfAt (fun _ => (2 : ℝ)) y := cInfAt_const _ y
  have hc (σ σ' : k →+* ℂ) : (Weight.ofFun (p := p) (σ := σ) fun _ => (2 : ℝ)).IsConj
      (Weight.ofFun (σ := σ') fun _ => (2 : ℝ)) := fun _ _ _ _ _ => rfl
  let L : Fin 2 → HermLB p := ![M, D]
  let F : Option (Fin 2) → HermLB p := fun o => o.elim (fnB (fun _ _ => 2) hu hc) L
  obtain ⟨Φ, hΦ⟩ := ((HC.arExists k S p 1 hp).2 _ F).1
  have key (o : Option (Fin 2)) :
      Φ (MvPolynomial.X (some 0) * MvPolynomial.X o) - t * gdeg (F o) 1 / 2 =
        -(Φ (MvPolynomial.X (some 1) * MvPolynomial.X o) / 2) ∧
      Φ (MvPolynomial.X (some 0) * MvPolynomial.X (some 0)) / 2 - I / 2 =
        Φ (MvPolynomial.X (some 1) * MvPolynomial.X (some 1)) / 8 - a / 12 + ρ / 2 * gdeg D 1 := by
    let e : Fin 3 → Option (Fin 2) := ![some 0, some 1, o]
    have h := H (F o) _ (((HC.arIso k S p 1 hp).2 _ F Φ hΦ).2.2 (Fin 3) ![M, D, F o]
      (fun j => Pi.single (e j) 1) fun j => by
        have := isometric_comb_single F (e j)
        fin_cases j <;> exact this)
    simp only [lin_single, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, MvPolynomial.aeval_X, sq] at h
    exact h
  have deg (i : Fin 2) : Φ (MvPolynomial.X (some i) * MvPolynomial.X none) = gdeg (L i) 1 := by
    have h := HC.arChange k S p 1 hp (Fin 2) L _ hu hc Φ hΦ (Pi.single i 1)
    rw [lin_single, MvPolynomial.rename_X, pow_one, mul_comm] at h
    rw [h, ← (isometric_comb_single L i).gdeg_eq, gdeg, chInt, chInt, mul_finsum]
    refine finsum_congr fun σ => ?_
    rw [← Weight.chernInt_const_mul]
    norm_num
  have h0 := (key none).1
  have z : gdeg (F none) 1 = 0 := gdeg_fnB_const HC hp 2 hu hc
  rw [deg, deg, z] at h0
  have h1 := (key (some 0)).1
  obtain ⟨h2, h3⟩ := key (some 1)
  rw [mul_comm (MvPolynomial.X (some 1))] at h1
  change gdeg M 1 - _ = -(gdeg D 1 / 2) at h0
  change _ - t * gdeg M 1 / 2 = _ at h1
  change _ - t * gdeg D 1 / 2 = _ at h2
  have hM : gdeg M 1 = -(gdeg D 1 / 2) := by linarith
  rw [hM] at h1
  linarith

end GlobalTheory.ThetaRR.Elim
