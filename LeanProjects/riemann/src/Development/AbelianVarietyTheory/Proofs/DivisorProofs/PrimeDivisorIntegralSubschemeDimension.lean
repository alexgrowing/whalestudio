import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOfRationalSectionViaDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishRealOfVanishInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRoots
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.VertFibre

open MvPolynomial

theorem lin_single_one {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) : lin (Pi.single i (1 : ℝ)) = X i := by
  simp [lin, Pi.single_apply]

theorem cross_eq_zero_of_diag {D : ℕ} (Ψ : MvPolynomial (Option (Fin D)) ℝ →ₗ[ℝ] ℝ)
    (h : ∀ n : Fin D → ℤ, Ψ (X none * rename some (lin fun i => (n i : ℝ)) ^ D) = 0) :
    Ψ (X none * ∏ j, X (some j)) = 0 := by
  have hβ := GlobalTheory.IntRealPow.vanish_real_of_vanish_int Ψ (X none) D h
  let φ : Module.Dual ℝ (MvPolynomial (Fin D) ℝ) :=
    Ψ ∘ₗ LinearMap.mulLeft ℝ (X none) ∘ₗ (rename (R := ℝ) (some : Fin D → Option (Fin D))).toLinearMap
  have hP : PowLinSpan.polOf φ D = 0 := MvPolynomial.funext fun x => by
    rw [PowLinSpan.eval_polOf, map_zero]
    show Ψ (X none * rename some ((∑ i, C (x i) * X i) ^ D)) = 0
    rw [map_pow]
    exact hβ x
  have hH : (∏ j, (X j : MvPolynomial (Fin D) ℝ)).IsHomogeneous D := by
    simpa using IsHomogeneous.prod Finset.univ (fun j => (X j : MvPolynomial (Fin D) ℝ)) (fun _ => 1)
      (fun j _ => isHomogeneous_X ℝ j)
  have := PowLinSpan.homog_kill φ D hP _ hH
  simpa [φ, map_prod] using this

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem num_cons_eq {num : Form (Cl p) D} (hn : IsArForm D num) (M : HermLB p) (N : Fin D → HermLB p)
    (Φ : MvPolynomial (Option (Fin D)) ℝ →ₗ[ℝ] ℝ) (hΦ : IsArFun (fun o : Option (Fin D) => o.elim M N) D Φ) :
    num (Fin.cons (cl M) fun j => cl (N j)) = Φ (MvPolynomial.X none * ∏ j, MvPolynomial.X (some j)) := by
  classical
  have h := hn (Option (Fin D)) _ Φ hΦ (Fin.cons (Pi.single none 1) fun j => Pi.single (some j) 1)
  rw [Fin.prod_univ_succ] at h
  simp only [Fin.cons_zero, Fin.cons_succ, lin_single_one] at h
  rw [h]
  congr 1
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [Fintype.sum_option, Pi.single_apply]
  · simp [Fintype.sum_option, Pi.single_apply]

theorem num_fnB_const (hP : Hypotheses2) (hX : IsArithVar p D) {num : Form (Cl p) D} (hn : IsArForm D num)
    (N : Fin D → HermLB p) (c : ℝ) :
    num (Fin.cons (cl (fnB (fun _ _ => 2 * c) (fun _ y => CxPts.cInfAt_const (2 * c) y)
        fun _ _ _ _ _ _ _ => rfl : HermLB p)) fun j => cl (N j)) =
      c * num (Fin.cons (cl (oneB p)) fun j => cl (N j)) := by
  have HE := hP.p4.arExists
  have HC := hP.p4.arChange
  obtain ⟨Φ, hΦ⟩ := ((HE k X p D hX).2 (Option (Fin D)) fun o => o.elim
    (fnB (fun _ _ => 2 * c) (fun _ y => CxPts.cInfAt_const (2 * c) y) fun _ _ _ _ _ _ _ => rfl : HermLB p) N).1
  obtain ⟨Φ₁, hΦ₁⟩ := ((HE k X p D hX).2 (Option (Fin D)) fun o => o.elim (oneB p) N).1
  rw [num_cons_eq hn _ N Φ hΦ, num_cons_eq hn _ N Φ₁ hΦ₁]
  have key := cross_eq_zero_of_diag (Φ - c • Φ₁) fun n => by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      HC k X p D hX (Fin D) N (fun _ _ => 2 * c) (fun _ y => CxPts.cInfAt_const (2 * c) y)
        (fun _ _ _ _ _ _ _ => rfl) Φ hΦ n,
      HC k X p D hX (Fin D) N (fun _ _ => 2) (fun _ y => CxPts.cInfAt_const 2 y)
        (fun _ _ _ _ _ _ _ => rfl) Φ₁ hΦ₁ n, chInt, chInt]
    have e (σ : k →+* ℂ) : ((comb N n).φ σ).chernInt D Set.univ (fun _ => 2 * c) =
        c * ((comb N n).φ σ).chernInt D Set.univ (fun _ => 2) := by
      rw [← Weight.chernInt_const_mul]
      congr 1
      funext y
      ring
    simp only [e, ← mul_finsum]
    ring
  rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, sub_eq_zero] at key
  exact key

end GlobalTheory.VertFibre

namespace GlobalTheory.VertFibre

theorem finsum_ord_mul_deg_eq : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ num : Form (Cl p) D, IsArForm D num → ∀ (N : Fin D → HermLB p) (l : ℕ) [Fact l.Prime] (d : X → ℝ), (∀ z, Scheme.ord ((l : X.functionField)) z ≠ 0 → ∃ (Z : Scheme.{0}) (i : Z ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (_ : Algebra (ZMod l) Γ(Z, ⊤)), i (genericPoint Z) = z ∧ topologicalKrullDim Z = D ∧ d z = interNum (ZMod l) (structureModule Z) (fun j => (N j).B.pull i)) → ∑ᶠ z, (Scheme.ord ((l : X.functionField)) z : ℝ) * d z = num (Fin.cons (cl (oneB p)) fun j => cl (N j)) := by
  intro hP k _ X _ _ p D hX num hn N l _ d hd
  have hl : l.Prime := Fact.out
  have hl0 : ((l : ℕ) : X.functionField) ≠ 0 := by
    have := hX.charZero
    have hinj := germ_injective_of_isIntegral X (U := ⊤) (genericPoint X) trivial
    intro h
    apply (Nat.cast_ne_zero (R := Γ(X, ⊤))).2 hl.ne_zero
    apply hinj
    rw [map_natCast, map_zero]
    exact h
  let T : HermLB p := fnB (fun _ _ => 2 * Real.log l) (fun _ y => CxPts.cInfAt_const (2 * Real.log l) y)
    fun _ _ _ _ _ _ _ => rfl
  let r : T.B.ι → X.functionFieldˣ := fun _ => Units.mk0 _ hl0
  have hr : IsRatSec T.B r := fun a b h =>
    ((congrArg (· * ((l : ℕ) : X.functionField)) (map_one (fnOf _ h))).trans (one_mul _)).symm
  have he (z : X) : (T.div hr).IsEqn z (r PUnit.unit) := (presents_divOfRatSec _ hr).isEqn PUnit.unit z trivial
  have hm (z : X) : (T.div hr).mult z = Scheme.ord ((l : X.functionField)) z := (he z).mult_eq
  have hlog : ∀ σ, ∀ y ∈ offSupp p σ (T.div hr), logNorm (T.φ σ) r y = 0 := by
    intro σ y _
    have e := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial (l : Γ(X, ⊤))
    rw [map_natCast, CxPts.ev_eq CxPts.mem_ptsIn_top, map_natCast] at e
    rw [logNorm]
    change Real.log ‖ratVal ((l : ℕ) : X.functionField) y‖ - 2 * Real.log l / 2 = 0
    rw [e, Complex.norm_natCast]
    ring
  have hv := GlobalTheory.T.height_of_rational_section_via_divisor hP k X p D hX num hn T r hr hlog N (fun _ => l) d fun z hz => by
    rw [hm] at hz
    obtain ⟨Z, i, h1, h2, h3, h4, h5, h6⟩ := hd z hz
    exact ⟨‹Fact l.Prime›, Z, i, h1, h2, h3, h4, h5, h6⟩
  have hc := num_fnB_const hP hX hn N (Real.log l)
  have hpos : 0 < Real.log l := Real.log_pos (by exact_mod_cast hl.one_lt)
  rw [hc] at hv
  simp only [hm] at hv
  rw [← finsum_mul] at hv
  exact mul_right_cancel₀ hpos.ne' (hv.symm.trans (mul_comm _ _))

end GlobalTheory.VertFibre
