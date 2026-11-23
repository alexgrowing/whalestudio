import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisConjugateCmPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionRatioDeterminedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActionRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoprimeLatticeMultiplierStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRiemannFormGaloisConjugateStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjRiemann

theorem im_conj_form_eq : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) →
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') →
          (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) →
          ∀ (u₀ : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E))) (Hm : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ) (χ : u₀.Λ → ℂ),
            u₀.ex = u'.ex → u₀.IsAH Hm χ →
            ∀ x ∈ lattice c (y * (upIdele K E t)⁻¹), ∀ x' ∈ lattice c (y * (upIdele K E t)⁻¹),
              ((fun j ↦ g (φ (T.U.e j) x)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) x'))).im =
                (modF t)⁻¹ * ∑ i, T.U.h i * (φ i x * starRingEnd ℂ (φ i x')).im := by
  intro hPC hADR hADC K _ _ d δ io hK2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ _hΩ hTT E _ _ _ _ I _ φ _hφ hφK c y hc 𝔠 T X' p hp u' hlat
    _hdiff htors u₀ Hm χ hex hAH
  have W := GlobalTheory.T.galois_conjugate_cm_point hPC hADR hADC K t E I φ g c y hc 𝔠 T X' p hp u' hlat htors u₀ Hm χ hex hAH
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hexp : ∀ (r r' : ℝ) (k : ℕ), 0 < k →
      Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (r' : ℂ) / k) →
        ∃ n : ℤ, r' - r = k * n := by
    intro r r' k hk h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    refine ⟨n, ?_⟩
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have e1 : (2 * (Real.pi : ℂ) * Complex.I) * (((r' - r : ℝ) : ℂ) - ((k * n : ℝ) : ℂ)) = 0 := by
      have hn' := congrArg (fun z => z * (k : ℂ)) hn
      simp only [add_mul, div_mul_cancel₀ _ hk'] at hn'
      push_cast
      linear_combination hn'
    rcases mul_eq_zero.1 e1 with h0 | h0
    · exact absurd h0 h2pi
    · exact_mod_cast sub_eq_zero.1 h0
  have h0L : (0 : E) ∈ lattice c y := by
    show algebraMap E (Af E) 0 * _ ∈ hatO c
    rw [map_zero, zero_mul]; exact (hatO c).zero_mem
  have h0L' : (0 : E) ∈ lattice c (y * (upIdele K E t)⁻¹) := by
    show algebraMap E (Af E) 0 * _ ∈ hatO c
    rw [map_zero, zero_mul]; exact (hatO c).zero_mem
  have htrz : ∀ z ∈ lattice c (y * (upIdele K E t)⁻¹),
      ((upIdele K E t : Af E) * algebraMap E (Af E) (z / ((1 : ℕ) : E)) - algebraMap E (Af E) ((0 : E) / ((1 : ℕ) : E))) *
        ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
    intro z hz
    have hz' : algebraMap E (Af E) z * (((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := hz
    convert hz' using 1
    simp only [Nat.cast_one, div_one, zero_div, map_zero, sub_zero, mul_inv_rev, inv_inv, Units.val_mul]
    ring
  have htrw : ∀ w ∈ lattice c y,
      ((upIdele K E t : Af E) * algebraMap E (Af E) ((0 : E) / ((1 : ℕ) : E)) - algebraMap E (Af E) (w / ((1 : ℕ) : E))) *
        ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
    intro w hw
    have hw' : algebraMap E (Af E) w * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := hw
    have e : ((upIdele K E t : Af E) * algebraMap E (Af E) ((0 : E) / ((1 : ℕ) : E)) - algebraMap E (Af E) (w / ((1 : ℕ) : E))) *
        ((y⁻¹ : (Af E)ˣ) : Af E) = -(algebraMap E (Af E) w * ((y⁻¹ : (Af E)ˣ) : Af E)) := by
      simp only [Nat.cast_one, div_one, zero_div, map_zero, mul_zero, zero_sub, neg_mul]
    rw [e]; exact (hatO c).neg_mem hw'
  have hEg : ∀ z ∈ lattice c (y * (upIdele K E t)⁻¹), ∀ z' ∈ lattice c (y * (upIdele K E t)⁻¹), ∃ n : ℤ,
      ((fun j ↦ g (φ (T.U.e j) z)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) z'))).im = n := by
    intro z hz z' hz'
    have h := W 1 0 0 z z' one_pos h0L h0L hz hz' (htrz z hz) (htrz z' hz')
    have hl : (∑ i, T.U.h i * (φ i 0 * starRingEnd ℂ (φ i 0)).im) = 0 := by simp
    rw [hl] at h
    obtain ⟨n, hn⟩ := hexp 0 _ 1 one_pos (by rw [← h]; simp)
    exact ⟨n, by simpa using hn⟩
  have hEf : ∀ w ∈ lattice c y, ∀ w' ∈ lattice c y, ∃ n : ℤ,
      (∑ i, T.U.h i * (φ i w * starRingEnd ℂ (φ i w')).im) = n := by
    intro w hw w' hw'
    have h := W 1 w w' 0 0 one_pos hw hw' h0L' h0L' (htrw w hw) (htrw w' hw')
    have hl : ((fun j ↦ g (φ (T.U.e j) 0)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) 0))).im = 0 := by
      simp
    rw [hl] at h
    have h1 : Complex.exp (-(2 * Real.pi * Complex.I) * (((∑ i, T.U.h i * (φ i w * starRingEnd ℂ (φ i w')).im : ℝ)) : ℂ) /
        ((1 : ℕ) : ℂ)) = Complex.exp (-(2 * Real.pi * Complex.I) * ((0 : ℝ) : ℂ) / ((1 : ℕ) : ℂ)) :=
      g.injective (by rw [h]; simp)
    obtain ⟨n, hn⟩ := hexp _ 0 1 one_pos h1
    exact ⟨-n, by push_cast at hn ⊢; linarith⟩
  have hsc : ∀ (m : K) (u u' : E), (∑ i, T.U.h i * (φ i (algebraMap K E m * u) * starRingEnd ℂ (φ i (algebraMap K E m * u'))).im) =
      Complex.normSq (io m) * ∑ i, T.U.h i * (φ i u * starRingEnd ℂ (φ i u')).im := by
    intro m u u'
    have hφm : ∀ i, φ i (algebraMap K E m) = io m := fun i => by rw [← hφK i]; rfl
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, hφm, map_mul]
    have e : io m * φ i u * (starRingEnd ℂ (io m) * starRingEnd ℂ (φ i u')) =
        (Complex.normSq (io m) : ℂ) * (φ i u * starRingEnd ℂ (φ i u')) := by
      rw [Complex.normSq_eq_conj_mul_self]; ring
    rw [e, Complex.im_ofReal_mul]; ring
  have hApos : 0 < modF t :=
    finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos (by
      have : Ideal.absNorm v.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      positivity) _
  have hcong : ∀ k : ℕ, 0 < k → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ Nat.Coprime b k ∧ IsCoprime a (k : ℤ) ∧
      ∀ s : {q : E × E // q.1 ∈ lattice c (y * (upIdele K E t)⁻¹) ∧ q.2 ∈ lattice c (y * (upIdele K E t)⁻¹)},
        (∃ n : ℤ, (b : ℝ) / modF t * (∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im) = n) ∧
        ∃ n : ℤ, ((fun j ↦ g (φ (T.U.e j) s.1.1)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) s.1.2))).im -
          a * ((b : ℝ) / modF t * (∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im)) = k * n := by
    intro k hk
    obtain ⟨a, ha, hga⟩ := GlobalTheory.T.galois_action_roots_of_unity g k hk
    obtain ⟨m, b, hb, hbk, hnorm, hm⟩ := GlobalTheory.T.norm_coprime_lattice_multiplier K d δ io hK2 hd hδ E t c y hc k hk
    refine ⟨a, b, hb, hbk, ha, ?_⟩
    rintro ⟨⟨u, u'⟩, hu, hu'⟩
    have hmu := (hm u hu).1
    have hmu' := (hm u' hu').1
    have hbA : (b : ℝ) / modF t * (∑ i, T.U.h i * (φ i u * starRingEnd ℂ (φ i u')).im) =
        ∑ i, T.U.h i * (φ i (algebraMap K E m * u) * starRingEnd ℂ (φ i (algebraMap K E m * u'))).im := by
      rw [hsc, hnorm]
    obtain ⟨n₀, hn₀⟩ := hEf _ hmu _ hmu'
    refine ⟨⟨n₀, by rw [hbA, hn₀]⟩, ?_⟩
    have h := W k (algebraMap K E m * u) (algebraMap K E m * u') u u' hk hmu hmu' hu hu' (hm u hu).2 (hm u' hu').2
    rw [hn₀] at h
    have e3 : Complex.exp (-(2 * Real.pi * Complex.I) * (((n₀ : ℝ)) : ℂ) / k) =
        Complex.exp (2 * Real.pi * Complex.I * ((-n₀ : ℤ) : ℂ) / k) := by
      congr 1; push_cast; ring
    rw [e3, hga (-n₀)] at h
    have e4 : Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * ((-n₀ : ℤ) : ℂ)) / k) =
        Complex.exp (-(2 * Real.pi * Complex.I) * ((((a * n₀ : ℤ) : ℝ)) : ℂ) / k) := by
      congr 1; push_cast; ring
    rw [e4] at h
    obtain ⟨n, hn⟩ := hexp _ _ k hk h
    refine ⟨n, ?_⟩
    show _ - _ * ((b : ℝ) / modF t * (∑ i, T.U.h i * (φ i u * starRingEnd ℂ (φ i u')).im)) = _
    rw [hbA, hn₀]
    push_cast at hn ⊢
    linarith
  have hpos : ∃ s : {q : E × E // q.1 ∈ lattice c (y * (upIdele K E t)⁻¹) ∧ q.2 ∈ lattice c (y * (upIdele K E t)⁻¹)},
      (∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im) ≠ 0 ∧
      0 < (∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im) *
        ((fun j ↦ g (φ (T.U.e j) s.1.1)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) s.1.2))).im := by
    obtain ⟨χT, hT⟩ := T.U.ah
    obtain ⟨u, hu, u', hu', hne, hp⟩ := GlobalTheory.T.cm_riemann_form_galois_conjugate K d δ io hK2 hd hδ g hTT.2.2.1 E I φ hφK c (y * (upIdele K E t)⁻¹) hc _ T.U.e
      T.U.h Hm Module.finrank_pos hT.2.1 hAH.1 hAH.2.1
    exact ⟨⟨(u, u'), hu, hu'⟩, hne, hp⟩
  intro x hx x' hx'
  have key := GlobalTheory.T.rational_function_ratio_determined {q : E × E // q.1 ∈ lattice c (y * (upIdele K E t)⁻¹) ∧ q.2 ∈ lattice c (y * (upIdele K E t)⁻¹)}
    (fun s => ∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im)
    (fun s => ((fun j ↦ g (φ (T.U.e j) s.1.1)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) s.1.2))).im)
    (modF t) hApos (fun s => hEg _ s.2.1 _ s.2.2) hcong hpos ⟨(x, x'), hx, hx'⟩
  rw [inv_mul_eq_div]
  exact key

end GlobalTheory.ConjRiemann
