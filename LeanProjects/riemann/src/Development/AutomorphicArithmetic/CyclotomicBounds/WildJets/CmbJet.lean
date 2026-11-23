import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProductStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

open GlobalTheory.NormSum.Term in
theorem UpperTheory.WildA.cmbJet :
    ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (cc : Ideal (𝓞 D.host.K)), cc = ⊤ → ∀ (δ t0 : ℂ), Crv D cc δ →
      GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a b r : ℕ) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l])
      (β : Fin r → Matrix (Fin b) (Fin a) D.host.E), OnB D β → LocBasis D l (YYl D (stdL D a) (stdL D b)) β →
      ∀ (n : ℕ), 0 < n → (l ∣ n → SplitIn D l) → ∀ (C : ℝ), 0 ≤ C → ∀ G : VC D a b → ℂ,
      KernelAt.Cmb D (tor0 D cc δ) lam (LaB D (tor0 D cc δ) β) (pullB D (tor0 D cc δ) β (GL3Theta.th0 (lamOf D cc δ) t0)) n C G →
      ∀ mon : GL3Theta.Idx D a b →₀ ℕ,
        Term.Bd lam (C * (l : ℝ) ^ ((mon.degree : ℝ) * (dl l + (if l = D.host.d then 1 / 4 else 0) + (padicValNat l n : ℝ))))
          (GL3Theta.applyAt0 D (MvPolynomial.monomial mon 1) G) := by
  intro D hI S dl hL cc hcc δ t0 hC ht a b r l _ lam β hb hloc n hn hsp C hC0 G hG mon
  subst hcc
  obtain ⟨k, c, s, hs, hr, hF⟩ := hG.out
  have hp : l.Prime := Fact.out
  have hp0 : (0 : ℝ) < l := by exact_mod_cast hp.pos
  have hN := norm_natCast_inv l hn.ne'
  have he0 : 0 ≤ (if l = D.host.d then (l : ℝ) ^ (((mon.degree : ℕ) : ℝ) / 4) else 1) := by
    split_ifs <;> positivity
  have hmon : (MvPolynomial.monomial mon 1 : MvPolynomial (GL3Theta.Idx D a b) ℂ) =
      MvPolynomial.map (Int.castRingHom ℂ) (MvPolynomial.monomial mon 1) := by
    rw [MvPolynomial.map_monomial, map_one (Int.castRingHom ℂ)]
  have hcol := rpow_collect hp0 (l = D.host.d) mon.degree 0 (dl l) (padicValNat l n : ℝ)
  rw [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero] at hcol
  rw [← hcol, mul_left_comm, hmon, hF]
  refine bd_applyAt0 (lam := lam) D (by positivity) _ _
    (MvPolynomial.isHomogeneous_monomial _ rfl) fun f => ?_
  refine bd_coord D (by positivity) (by positivity) (tor0 D ⊤ δ) (fun _ _ => rfl)
    (YYl D (stdL D a) (stdL D b)) (hL.2.2.2.2 l lam a b) _ (fun y hy => ?_) f
  rw [iteratedFDeriv_comb _ (fun i => (c i : ℂ))
    (fun i => U D (tor0 D ⊤ δ) (s i) (pullB D (tor0 D ⊤ δ) β (GL3Theta.th0 (lamOf D ⊤ δ) t0))) fun i =>
    contDiff_U_pullB D _ β _ (differentiable_evenTheta D ⊤ δ t0 hC) (s i) _]
  refine Bd.sum (by positivity) _ _ fun i _ => ?_
  refine (Bd.coe (hr i)).mul ?_
  have := GlobalTheory.T.jets_torsion_translates_cm_theta_product D hI l lam ⊤ δ hC (by simp) t0 ht a b _ β hb hloc (s i) n
    hn (hs i) hsp _ y hy
  rw [hN] at this
  exact this
