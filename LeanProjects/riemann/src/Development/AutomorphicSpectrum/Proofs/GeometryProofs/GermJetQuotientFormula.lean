import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

section Pow1

variable {k : Type} [Field k] {d : ℕ}

theorem aeval_firstOrder {B A : Type} [CommRing B] [Algebra k B] [CommRing A] [Algebra k A]
    (τ : B →ₐ[k] A) (ε : A) (hε : ε * ε = 0) (c : Fin d → k) (z : Fin d → B)
    (P : MvPolynomial (Fin 2 × Fin d) k) :
    MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then algebraMap k A (c q.2) * ε else τ (z q.2)) P =
      τ (MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : B) else z q.2) P) +
      ε * ∑ i, algebraMap k A (c i) * τ (MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : B) else z q.2)
        (MvPolynomial.pderiv ((0 : Fin 2), i) P)) := by
  set θ : MvPolynomial (Fin 2 × Fin d) k →ₐ[k] B :=
    MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : B) else z q.2) with hθ
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ, mul_add, Finset.sum_add_distrib]
    ring
  | mul_X P q hP =>
    obtain ⟨a, j⟩ := q
    rw [map_mul, hP, MvPolynomial.aeval_X]
    by_cases ha : a = 0
    · subst ha
      have key : ∀ i, τ (θ (MvPolynomial.pderiv ((0 : Fin 2), i) (P * MvPolynomial.X ((0 : Fin 2), j)))) =
          if j = i then τ (θ P) else 0 := by
        intro i
        have hX : θ (MvPolynomial.X ((0 : Fin 2), j)) = 0 := by simp [hθ]
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hX, zero_mul, add_zero,
          MvPolynomial.pderiv_X]
        by_cases hij : j = i
        · subst hij; simp
        · simp [Pi.single_apply, hij, Ne.symm hij]
      simp only [key, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have hX : θ (P * MvPolynomial.X ((0 : Fin 2), j)) = 0 := by simp [hθ]
      rw [hX, map_zero, zero_add]
      linear_combination (algebraMap k A (c j) * ∑ i, algebraMap k A (c i) * τ (θ (MvPolynomial.pderiv ((0 : Fin 2), i) P))) * hε
    · have key : ∀ i, θ (MvPolynomial.pderiv ((0 : Fin 2), i) (P * MvPolynomial.X (a, j))) =
          θ (MvPolynomial.pderiv ((0 : Fin 2), i) P) * z j := by
        intro i
        have h0 : MvPolynomial.pderiv ((0 : Fin 2), i) (MvPolynomial.X (a, j) : MvPolynomial (Fin 2 × Fin d) k) = 0 := by
          rw [MvPolynomial.pderiv_X, Pi.single_apply, if_neg]
          intro h; exact ha (congrArg Prod.fst h)
        rw [Derivation.leibniz, h0, smul_zero, zero_add, smul_eq_mul, map_mul, mul_comm]
        simp [hθ, ha]
      have hX : θ (P * MvPolynomial.X (a, j)) = θ P * z j := by simp [hθ, ha]
      simp only [key, hX, ha, if_false, map_mul, Finset.mul_sum, Finset.sum_mul, add_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring

theorem mk_psTrunc_of_le {κ : Type} [Fintype κ] [DecidableEq κ] {m N : ℕ} (hN : m ≤ N)
    (f : MvPowerSeries κ k) :
    Ideal.Quotient.mk (orig k κ ^ (m + 1)) (psTrunc N f) = psJet m f := by
  rw [psJet, Ideal.Quotient.eq]
  refine GermD.mem_orig_pow_of fun e he => ?_
  by_contra hlt
  push Not at hlt
  apply MvPolynomial.mem_support_iff.mp he
  rw [MvPolynomial.coeff_sub, GermFun.coeff_psTrunc _ _ _ (by omega), GermFun.coeff_psTrunc _ _ _ (by omega), sub_self]

theorem mk_pderiv_psTrunc {κ : Type} [Fintype κ] [DecidableEq κ] {m N : ℕ} (hN : m + 1 ≤ N)
    (f : MvPowerSeries κ k) (q : κ) :
    Ideal.Quotient.mk (orig k κ ^ (m + 1)) (MvPolynomial.pderiv q (psTrunc N f)) =
      psJet m (MvPowerSeries.pderiv k q f) := by
  rw [psJet, Ideal.Quotient.eq]
  refine GermD.mem_orig_pow_of fun e he => ?_
  by_contra hlt
  push Not at hlt
  apply MvPolynomial.mem_support_iff.mp he
  have hd : (e + Finsupp.single q 1).degree = e.degree + 1 := by simp
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_pderiv, GermFun.coeff_psTrunc _ _ _ (by omega),
    GermFun.coeff_psTrunc _ _ _ (by omega), MvPowerSeries.coeff_pderiv, sub_self]

theorem aeval_axis_eq_psJet (m : ℕ) (P : MvPolynomial (Fin 2 × Fin d) k) (h : Germ.PS k 2 d)
    (hP : Ideal.Quotient.mk (orig k (Fin 2 × Fin d) ^ (m + 1)) P = psJet m h) :
    MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : Jet k (Fin 1 × Fin d) m)
      else Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2))) P =
      psJet m (Germ.ev (n := 1) ![0, Germ.pt k d 0] h) := by
  have ha : ∀ q : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![0, Germ.pt k d 0] : Fin 2 → Germ.Pt k 1 d) q.1 q.2) = 0 := by
    rintro ⟨a, j⟩
    fin_cases a <;> simp [Germ.pt]
  rw [Germ.ev, FBIdJet.psJet_subst m _ ha, ← hP, GermD.jetMap_mk]
  have e : (MvPolynomial.aeval (fun q : Fin 2 × Fin d => if q.1 = 0 then (0 : Jet k (Fin 1 × Fin d) m)
      else Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2))) : MvPolynomial (Fin 2 × Fin d) k →ₐ[k] _) =
      (Ideal.Quotient.mkₐ k _).comp (MvPolynomial.aeval fun q : Fin 2 × Fin d =>
        psTrunc m ((![0, Germ.pt k d 0] : Fin 2 → Germ.Pt k 1 d) q.1 q.2)) := by
    refine MvPolynomial.algHom_ext fun q => ?_
    obtain ⟨a, j⟩ := q
    rw [MvPolynomial.aeval_X, AlgHom.comp_apply, MvPolynomial.aeval_X]
    show _ = psJet m _
    fin_cases a
    · simp [psJet, psTrunc]
    · have : (![0, Germ.pt k d 0] : Fin 2 → Germ.Pt k 1 d) 1 j =
          ((MvPolynomial.X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin d) k) : MvPowerSeries _ k) := by
        simp [Germ.pt]
      simp only [Fin.mk_one, this, ExpGF.psJet_coe]
      simp
  rw [e]
  rfl

theorem psJet_sum_C_mul {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (u : Fin d → k)
    (h : Fin d → MvPowerSeries κ k) :
    psJet m (∑ i, MvPowerSeries.C (u i) * h i) = ∑ i, algebraMap k (Jet k κ m) (u i) * psJet m (h i) := by
  have hadd : ∀ f g : MvPowerSeries κ k, psJet m (f + g) = psJet m f + psJet m g := fun f g => by
    simp [psJet, psTrunc, Finset.sum_add_distrib]
  have hzero : psJet m (0 : MvPowerSeries κ k) = 0 := by simp [psJet, psTrunc]
  have hC : ∀ c : k, psJet m (MvPowerSeries.C c : MvPowerSeries κ k) = algebraMap k (Jet k κ m) c := fun c => by
    have : (MvPowerSeries.C c : MvPowerSeries κ k) = ((MvPolynomial.C c : MvPolynomial κ k) : MvPowerSeries κ k) := by simp
    rw [this, ExpGF.psJet_coe]
    rfl
  let L : MvPowerSeries κ k →+ Jet k κ m := ⟨⟨psJet m, hzero⟩, hadd⟩
  have := map_sum L (fun i => MvPowerSeries.C (u i) * h i) Finset.univ
  refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
  show psJet m _ = _
  rw [FBIdJet.psJet_mul, hC]

theorem jq_psJet_ptPow (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (d m : ℕ) (w : Fin d → k)
    (g : Germ.PS k 2 d) (hg : AxOne g) :
    jq w p m (psJet (p + m + 1) (Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] g)) =
      1 + dQ _ p ^ p * algebraMap _ _ (psJet m (dSer g fun i => w i ^ p)) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set B := Jet k (Fin 1 × Fin d) m with hB
  set A := Jet B Unit p with hA
  have hε : dQ B p ^ p * dQ B p ^ p = 0 := by
    rw [← pow_add]
    exact pow_eq_zero_of_le (by omega) (dQ_pow B p)
  have ha : ∀ q : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![ptPow k d p 0, Germ.pt k d 1] : Fin 2 → Germ.Pt k 2 d) q.1 q.2) = 0 := by
    rintro ⟨a, j⟩
    fin_cases a
    · simp [ptPow, hp]
    · simp [Germ.pt]
  have hjq : ∀ Q : MvPolynomial (Fin 2 × Fin d) k, jq w p m (Ideal.Quotient.mk _ Q) =
      MvPolynomial.aeval (fun q : Fin 2 × Fin d =>
        if q.1 = 0 then algebraMap k A (w q.2) * dQ B p
        else inR (k := k) B p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2)))) Q := fun Q => rfl
  have step : jq w p m (psJet (p + m + 1) (Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] g)) =
      MvPolynomial.aeval (fun q : Fin 2 × Fin d =>
        if q.1 = 0 then algebraMap k A (w q.2 ^ p) * dQ B p ^ p
        else inR (k := k) B p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2)))) (psTrunc (p + m + 1) g) := by
    rw [Germ.ev, FBIdJet.psJet_subst _ _ ha, psJet, GermD.jetMap_mk, hjq, MvPolynomial.comp_aeval_apply]
    congr 2
    funext q
    obtain ⟨a, j⟩ := q
    rw [← hjq]
    show jq w p m (psJet _ _) = _
    fin_cases a
    · have : (![ptPow k d p 0, Germ.pt k d 1] : Fin 2 → Germ.Pt k 2 d) 0 j =
          ((MvPolynomial.X ((0 : Fin 2), j) ^ p : MvPolynomial (Fin 2 × Fin d) k) : MvPowerSeries _ k) := by
        simp [ptPow]
      simp only [Fin.zero_eta, this, ExpGF.psJet_coe, hjq]
      simp [mul_pow]
    · have : (![ptPow k d p 0, Germ.pt k d 1] : Fin 2 → Germ.Pt k 2 d) 1 j =
          ((MvPolynomial.X ((1 : Fin 2), j) : MvPolynomial (Fin 2 × Fin d) k) : MvPowerSeries _ k) := by
        simp [Germ.pt]
      simp only [Fin.mk_one, this, ExpGF.psJet_coe, hjq]
      simp
  rw [step, aeval_firstOrder (inR (k := k) B p) (dQ B p ^ p) hε (fun i => w i ^ p)
    (fun j => Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) (psTrunc (p + m + 1) g)]
  rw [aeval_axis_eq_psJet m _ g (mk_psTrunc_of_le (by omega) g), hg.1, FBIdJet.psJet_one, map_one]
  congr 2
  rw [dSer, psJet_sum_C_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aeval_axis_eq_psJet m _ _ (mk_pderiv_psTrunc (by omega) g _), map_mul]
  rw [← IsScalarTower.algebraMap_apply]
  rfl

end Pow1

end GlobalTheory.CompanionTheory.Ar.Coc
