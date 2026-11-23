import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralOfCombinedMetrics

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

namespace GlobalTheory.CompanionTheory.ChernTwist

section Multi

variable {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

theorem mInt_update_add_rsmul (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (a : Fin e) (P Q : LocPot X) (hP : IsPotential A P) (hQ : IsPotential A Q) (t : ℝ) (g : X → ℝ)
    (hg : Continuous g) :
    mInt A (Function.update Φ a (P + Q.rsmul t)) g =
      mInt A (Function.update Φ a P) g + t * mInt A (Function.update Φ a Q) g := by
  cases e with
  | zero => exact a.elim0
  | succ e =>
    let s : Equiv.Perm (Fin (e + 1)) := Equiv.swap 0 a
    let τ : Fin e → LocPot X := Fin.tail (Φ ∘ s)
    have hτ : ∀ i, IsPotential A (τ i) := fun i => hΦ _
    have key : ∀ T : LocPot X, mInt A (Function.update Φ a T) g = mInt A (Fin.cons T τ) g := by
      intro T
      rw [← mIntSymm A (Function.update Φ a T) s g]
      congr 1
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [s]
      · have hne : s i.succ ≠ a := by
          intro h
          have : i.succ = s a := by rw [← h]; simp [s]
          simp [s] at this
        simp [Function.update_of_ne hne, τ, Fin.tail]
    have hc : ∀ T : LocPot X, IsPotential A T → ∀ i, IsPotential A ((Fin.cons T τ : Fin (e + 1) → LocPot X) i) :=
      fun T hT i => Fin.cases hT hτ i
    have hQt := isPotentialRsmul A t Q hQ
    rw [key, key, key, mIntAdd A P (Q.rsmul t) τ hP hQt hτ g (mIntegrableCont A _ (hc P hP) g hg)
      (mIntegrableCont A _ (hc _ hQt) g hg), mIntRsmul A t Q τ hQ hτ g]

theorem exists_poly_mInt (A : FinHolAtlas e X) (P Q : LocPot X) (hP : IsPotential A P) (hQ : IsPotential A Q)
    (g : X → ℝ) (hg : Continuous g) (S : Finset (Fin e)) :
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → ∃ R : Polynomial ℝ, R.natDegree ≤ S.card ∧
      ∀ t : ℝ, mInt A (fun i => if i ∈ S then P + Q.rsmul t else Φ i) g = R.eval t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro Φ _
    exact ⟨Polynomial.C (mInt A Φ g), by simp, fun t => by simp⟩
  | insert a S ha ih =>
    intro Φ hΦ
    have hup : ∀ T : LocPot X, IsPotential A T → ∀ i, IsPotential A (Function.update Φ a T i) := by
      intro T hT i
      by_cases e' : i = a
      · subst e'; simpa using hT
      · simpa [Function.update_of_ne e'] using hΦ i
    obtain ⟨R₁, d₁, h₁⟩ := ih _ (hup P hP)
    obtain ⟨R₂, d₂, h₂⟩ := ih _ (hup Q hQ)
    refine ⟨R₁ + Polynomial.X * R₂, ?_, fun t => ?_⟩
    · rw [Finset.card_insert_of_notMem ha]
      refine Polynomial.natDegree_add_le_of_degree_le (d₁.trans (Nat.le_succ _)) ?_
      refine Polynomial.natDegree_mul_le.trans ?_
      have := Polynomial.natDegree_X_le (R := ℝ)
      omega
    · set Ψ : Fin e → LocPot X := fun i => if i ∈ S then P + Q.rsmul t else Φ i with hΨ
      have hΨp : ∀ i, IsPotential A (Ψ i) := by
        intro i
        simp only [hΨ]
        split_ifs
        · exact isPotentialAdd A _ _ hP (isPotentialRsmul A t Q hQ)
        · exact hΦ i
      have e₀ : (fun i => if i ∈ insert a S then P + Q.rsmul t else Φ i) =
          Function.update Ψ a (P + Q.rsmul t) := by
        funext i
        by_cases e' : i = a
        · subst e'; simp
        · simp [Function.update_of_ne e', hΨ, e']
      have e₁ : ∀ T : LocPot X, Function.update Ψ a T =
          fun i => if i ∈ S then P + Q.rsmul t else Function.update Φ a T i := by
        intro T
        funext i
        by_cases e' : i = a
        · subst e'; simp [ha]
        · simp [Function.update_of_ne e', hΨ]
      rw [e₀, mInt_update_add_rsmul A Ψ hΨp a P Q hP hQ t g hg, e₁, e₁, h₁, h₂]
      simp

end Multi

theorem chernInt_twist_polynomial :
    ∀ (Y : Var ℂ) (Δ Δ₀ : Y.Dv) (L L₀ : LB Y.X) (r : L.ι → Y.Fnˣ) (r₀ : L₀.ι → Y.Fnˣ), Presents Δ L r →
      Presents Δ₀ L₀ r₀ → ∀ (φ : Weight Y.str (RingHom.id ℂ) L) (φ₀ : Weight Y.str (RingHom.id ℂ) L₀), φ.IsCInf →
      φ₀.IsCInf → ∃ P : Polynomial ℝ, P.natDegree ≤ Y.dim ∧ ∀ m : ℕ, ∃ (L' : LB Y.X) (r' : L'.ι → Y.Fnˣ)
        (ψ : Weight Y.str (RingHom.id ℂ) L'), Presents (Δ + m • Δ₀) L' r' ∧ ψ.IsCInf ∧
          ψ.chernInt Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  intro Y Δ Δ₀ L L₀ r r₀ h h₀ φ φ₀ hφ hφ₀
  have := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (RingHom.id ℂ) Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  obtain ⟨R⟩ := genSmooth_of_smooth Y.str Y.dim (RingHom.id ℂ)
  have hA := R.isAlgAtlas_finAtlas
  have hP : IsPotential R.finAtlas φ.locPot := Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth R).1 hφ)
  have hQ : IsPotential R.finAtlas φ₀.locPot := Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth R).1 hφ₀)
  obtain ⟨Pol, hdeg, hev⟩ := exists_poly_mInt R.finAtlas φ.locPot φ₀.locPot hP hQ (fun _ => 1) continuous_const
    Finset.univ (fun _ => φ.locPot) (fun _ => hP)
  refine ⟨Pol, by simpa using hdeg, fun m => ?_⟩
  have hpr := h.tens (GlobalTheory.CombChern.presents_zpow h₀ (m : ℤ))
  rw [natCast_zsmul] at hpr
  have hψ : (φ.tens (φ₀.zpow (m : ℤ))).IsCInf := hφ.tens (hφ₀.zpow _)
  refine ⟨_, _, φ.tens (φ₀.zpow (m : ℤ)), hpr, hψ, ?_⟩
  have hT := isPotentialAdd R.finAtlas _ _ hP (isPotentialRsmul R.finAtlas (m : ℝ) _ hQ)
  have hsf : SameForm R.finAtlas (φ.tens (φ₀.zpow (m : ℤ))).locPot (φ.locPot + φ₀.locPot.rsmul (m : ℝ)) := by
    refine Weight.sameForm_of_eq _ hA hT fun x => ?_
    refine ⟨(pick φ.isLB x, fun _ => pick φ₀.isLB x), mem_ptsIn_inf.2 ⟨mem_pick φ.isLB x, mem_pow_iff.2 (mem_pick φ₀.isLB x)⟩,
      fun z => ?_⟩
    have e := φ₀.zpow_φ (m : ℤ) (fun _ => pick φ₀.isLB x) z
    change (φ.φ (pick φ.isLB x) z + (φ₀.zpow (m : ℤ)).φ (fun _ => pick φ₀.isLB x) z) / 2 =
      φ.φ (pick φ.isLB x) z / 2 + (m : ℝ) * (φ₀.φ (pick φ₀.isLB x) z / 2)
    rw [e]
    push_cast
    ring
  rw [((Weight.chernInt_eq_mInt R hψ measurable_const).2
    (GlobalTheory.Published.ChernDegreeComplexModel.integrable Y _ hψ)), SameForm.mInt_eq (fun _ => hsf)]
  simpa using hev (m : ℝ)

end GlobalTheory.CompanionTheory.ChernTwist
