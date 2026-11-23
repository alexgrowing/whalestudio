import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralIndependentOfCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFunctionalVanishesOnMonomialStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.VertDeg

theorem oneB_flat_eq_zero : Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (D : ℕ), Y.dim = D → ∀ num : Form (Cl V.p) D, IsArForm D num → ∀ (M : HermLB V.p) (lg : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ), Norms V M (fun _ => 1) (fun _ _ => 0) lg → ∀ (v : Fin D → Cl V.p) (j : Fin D), num (Fin.cons (cl (oneB V.p)) (Function.update v j (cl M))) = 0 := by
  intro hP F _ _ Y V D hD num hnum M lg hM v j
  have hX : IsArithVar V.p D := hD ▸ V.ar
  have hA := hP.p4

  have hB : ∀ N : Fin D → HermLB V.p,
      num (Fin.cons (cl (oneB V.p)) (fun k => cl (Function.update N j M k))) = 0 := by
    intro N
    set Lf : Fin D → HermLB V.p := Function.update N j M with hLf
    let K : Option (Fin D) → HermLB V.p := fun o => o.elim (oneB V.p) Lf
    obtain ⟨Φ, hΦ⟩ := ((hA.arExists) (𝓞 F) V.X V.p D hX).2 (Option (Fin D)) K |>.1
    let a : Fin (D + 1) → Option (Fin D) → ℝ := Fin.cons (Pi.single none 1) (fun k => Pi.single (some k) 1)
    have e1 := hnum (Option (Fin D)) K Φ hΦ a
    have e2 : (fun j => ∑ o, a j o • cl (K o)) = Fin.cons (cl (oneB V.p)) (fun k => cl (Lf k)) := by
      funext t
      refine Fin.cases ?_ (fun k => ?_) t
      · simp [a, K, Pi.single_apply]
      · simp [a, K, Pi.single_apply]
    have e3 : (∏ t, lin (a t)) = MvPolynomial.X none * MvPolynomial.rename some (∏ k, MvPolynomial.X k) := by
      have hl : ∀ o : Option (Fin D), lin (Pi.single o (1 : ℝ)) = MvPolynomial.X o := by
        intro o; simp [lin, Pi.single_apply]
      rw [Fin.prod_univ_succ, map_prod]
      simp [a, hl]
    rw [e2, e3] at e1
    rw [← e1]
    let Ψ : MvPolynomial (Fin D) ℝ →ₗ[ℝ] ℝ :=
      Φ ∘ₗ LinearMap.mulLeft ℝ (MvPolynomial.X none) ∘ₗ (MvPolynomial.rename some).toLinearMap
    have hΨ : ∀ Q, Ψ Q = Φ (MvPolynomial.X none * MvPolynomial.rename some Q) := fun Q => rfl
    rw [← hΨ]
    refine GlobalTheory.T.polarization_functional_vanishes_on_monomial D Ψ j fun n => ?_
    have key : ∀ n' : Fin D → ℤ, Ψ (lin (fun i => (n' i : ℝ)) ^ D) =
        ∑ᶠ σ, ((comb Lf n').φ σ).chernInt D Set.univ (fun _ => 1) := by
      intro n'
      rw [hΨ, map_pow]
      have h2 := (hA.arMix.fnB (u := fun _ _ => 2) hA.arExists hX (L := Lf) hΦ n').2
      rw [h2, chInt, mul_finsum]
      refine finsum_congr fun σ => ?_
      rw [show (fun _ : CxPts V.p σ => (2 : ℝ)) = fun y => 2 * (fun _ => (1 : ℝ)) y from funext fun _ => (mul_one _).symm,
        Weight.chernInt_const_mul]
      ring
    rw [key, key]
    refine finsum_congr fun σ => ?_
    exact GlobalTheory.T.chern_integral_independent_of_coefficient hP F Y V D hD M lg hM (Fin D) Lf j (by simp [hLf]) n σ

  rw [← MultilinearMap.curryLeft_apply]
  set T := num.curryLeft (cl (oneB V.p))
  have hv : ∀ k, v k = ∑ L ∈ (v k).support, v k L • cl L := fun k => by
    conv_lhs => rw [← Finsupp.sum_single (v k)]
    simp [Finsupp.sum, cl, Finsupp.smul_single]
  let A : Fin D → Finset (HermLB V.p) := fun k => if k = j then {M} else (v k).support
  let c : Fin D → HermLB V.p → ℝ := fun k L => if k = j then 1 else v k L
  let g : Fin D → HermLB V.p → Cl V.p := fun k L => c k L • cl L
  have hg : Function.update v j (cl M) = fun k => ∑ L ∈ A k, g k L := by
    funext k
    by_cases hk : k = j
    · subst hk; simp [A, g, c]
    · rw [Function.update_of_ne hk, hv k]; simp [A, g, c, hk]
  rw [hg, MultilinearMap.map_sum_finset]
  refine Finset.sum_eq_zero fun r hr => ?_
  have hrj : r j = M := by
    have := (Fintype.mem_piFinset.1 hr) j
    simpa [A] using this
  rw [show (fun k => g k (r k)) = fun k => c k (r k) • cl (r k) from rfl, MultilinearMap.map_smul_univ]
  have := hB r
  rw [Function.update_eq_self_iff.2 hrj.symm] at this
  have h0 : T (fun k => cl (r k)) = 0 := by
    rw [MultilinearMap.curryLeft_apply]; exact this
  rw [h0, smul_zero]

end GlobalTheory.VertDeg
