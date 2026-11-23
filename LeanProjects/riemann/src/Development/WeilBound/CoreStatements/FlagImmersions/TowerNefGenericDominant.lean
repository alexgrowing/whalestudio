import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MultiIsProjVarFOfRatDiv
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem abel_le {N : ℕ} (f u : Fin (N + 1) → ℝ) (hf : ∀ a b, a ≤ b → f b ≤ f a)
    (hu : ∀ i, 0 ≤ ∑ k ∈ Finset.Iic i, u k) (i : Fin (N + 1)) :
    f i * ∑ k ∈ Finset.Iic i, u k ≤ ∑ k ∈ Finset.Iic i, f k * u k := by
  induction i using Fin.induction with
  | zero =>
    have : Finset.Iic (0 : Fin (N + 1)) = {0} := by ext k; simp
    simp [this]
  | succ j ih =>
    have h1 : Finset.Iic j.succ = insert j.succ (Finset.Iic j.castSucc) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_def, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
      omega
    have h2 : j.succ ∉ Finset.Iic j.castSucc := by
      simp only [Finset.mem_Iic, Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      omega
    rw [h1, Finset.sum_insert h2, Finset.sum_insert h2]
    have h3 := hf j.castSucc j.succ (Fin.castSucc_lt_succ).le
    have h4 := mul_le_mul_of_nonneg_right h3 (hu j.castSucc)
    rw [mul_add]
    linarith

theorem abel_nonneg {N : ℕ} (f u : Fin N → ℝ) (hf : ∀ a b, a ≤ b → f b ≤ f a)
    (hu : ∀ i, 0 ≤ ∑ k ∈ Finset.Iic i, u k)
    (h0 : ∀ i : Fin N, (i : ℕ) + 1 = N → ∑ k ∈ Finset.Iic i, u k = 0) : 0 ≤ ∑ k, f k * u k := by
  obtain _ | N := N
  · simp
  · have h := abel_le f u hf hu (Fin.last N)
    rw [h0 (Fin.last N) (by simp), mul_zero] at h
    have e : Finset.Iic (Fin.last N) = Finset.univ := by
      ext k; simp [Fin.le_last]
    rwa [e] at h

theorem tower_nef_generic_dominant : PB.NefPol → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), R.Smooth → R.Flat → ∀ B c, (∀ lam : Wt Ψ N, Dominant lam → (T.M B c).NefGen lam 0) ∧ (T.M B c).NefGen 0 1 := by
  intro hNP hI II _ Ψ _ _ N T R hSm hFl B c
  classical
  obtain ⟨hJ, alg, -⟩ := hSm B c
  set M := T.M B c with hM
  revert hJ
  generalize R.tie B c = tie
  intro hJ
  have : CharZero M.Ω := algebraRat.charZero M.Ω
  let I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily ℚ M.ι := fun V _ L => GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ V L
  have hIf : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I :=
    GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full _ _ _
  let Fl : Set (Option (Ψ × Fin N)) := {a | ∃ τ, ∃ i : Fin N, (i : ℕ) + 1 = N ∧ a = some (τ, i)}
  have hnef := fun n hn => (hNP hI (dimFl Ψ N) (Option (Ψ × Fin N)) (R.Sys c) Fl
    (by rintro _ ⟨τ, i, hi, rfl⟩ t; exact hFl c τ i hi t) M.K M.ι M.Ω M.y tie.Re hJ M.birational I hIf n hn).1
  have key : ∀ W : Ideal (MRing M.ι), IsArithVar W 2 → M.P ≤ W → ∃ d : (M.K → ℤ) →+ ℤ,
      (∀ L : HermLine M.ι, IsSmoothHerm L → geomDeg W L 1 = d L.a) ∧ (∀ a, 0 ≤ d (tie.Re.ref a).a) ∧
        ∀ a ∈ Fl, d (tie.Re.ref a).a = 0 := by
    intro W hW hPW
    have hWq : ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 :=
      GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hW
    have hup : ∀ a : M.K → ℤ, Function.update (fun _ : Fin 1 => (0 : M.K → ℤ)) 0 a = fun _ => a := by
      intro a; funext j; rw [Subsingleton.elim j 0]; simp
    let d : (M.K → ℤ) →+ ℤ := AddMonoidHom.mk'
      (fun a => I (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 fun _ => a) fun a b => by
        have := ReciprocityTheory.ChartRestriction.G.AI.I1.multilin_thm ℚ M.ι I hIf _ 1 (fun _ => 0) 0 a b hWq
        simpa only [hup] using this
    have hpos : ∀ n : Option (Ψ × Fin N) → ℤ, (∀ a ∉ Fl, 0 ≤ n a) → 0 ≤ d (PB.combLine tie.Re.ref n).a := by
      intro n hn
      have := hnef n hn _ hWq (Ideal.map_mono hPW)
      have e : ![(PB.combLine tie.Re.ref n).a] = fun _ : Fin 1 => (PB.combLine tie.Re.ref n).a := by
        funext j; rw [Subsingleton.elim j 0]; rfl
      rw [e] at this
      exact this
    have hs : ∀ (a : Option (Ψ × Fin N)) (m : ℤ),
        (PB.combLine tie.Re.ref (Pi.single a m)).a = m • (tie.Re.ref a).a := by
      intro a m
      funext k
      rw [PB.combLine_a, Finset.sum_eq_single a (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      simp
    have h1 : ∀ a, 0 ≤ d (tie.Re.ref a).a := by
      intro a
      have := hpos (Pi.single a 1) fun b _ => by
        by_cases hb : b = a
        · simp [hb]
        · simp [Pi.single_eq_of_ne hb]
      rwa [hs, one_smul] at this
    refine ⟨d, fun L hL => ?_, h1, fun a ha => ?_⟩
    · exact Giv.degreeGeneric_of_degree hI.degree M.K M.ι W 1 (fun _ => L) hW fun _ => hL
    · have := hpos (Pi.single a (-1)) fun b hbF => by
        have hb : b ≠ a := fun h => hbF (h ▸ ha)
        simp [Pi.single_eq_of_ne hb]
      rw [hs, neg_one_smul, map_neg] at this
      linarith [h1 a]
  refine ⟨fun lam hlam W hW hPW => ?_, fun W hW hPW => ?_⟩
  · obtain ⟨d, hd, h1, h0⟩ := key W hW hPW
    have hS : ∀ τ i, ∑ k ∈ Finset.Iic i, (-(d (M.xdeg (τ, k)) : ℝ)) = d (tie.Re.ref (some (τ, i))).a := by
      intro τ i
      rw [tie.fund_deg, map_neg, map_sum]
      simp
      rfl
    rw [Fintype.sum_option, Fintype.sum_prod_type]
    have e0 : M.coef lam 0 none = 0 := by simp [RootModel.coef]
    rw [e0, zero_mul, zero_add]
    refine Finset.sum_nonneg fun τ _ => ?_
    have := abel_nonneg (lam τ) (fun k => -(d (M.xdeg (τ, k)) : ℝ)) (hlam τ)
      (fun i => by rw [hS]; exact_mod_cast h1 _)
      (fun i hi => by rw [hS, h0 _ ⟨τ, i, hi, rfl⟩]; simp)
    refine this.trans_eq (Finset.sum_congr rfl fun k _ => ?_)
    have e1 : geomDeg W (M.line 1 (some (τ, k))) 1 = d (M.xdeg (τ, k)) := by
      rw [← M.x_deg 1 (τ, k)]
      exact hd _ (M.x_smooth 1 _)
    rw [e1]
    simp [RootModel.coef]
  · obtain ⟨d, hd, h1, -⟩ := key W hW hPW
    rw [Fintype.sum_option]
    have e0 : ∀ r, M.coef (0 : Wt Ψ N) 1 (some r) = 0 := fun r => by simp [RootModel.coef]
    simp only [e0, zero_mul, Finset.sum_const_zero, add_zero]
    have e1 : geomDeg W (M.line 1 none) 1 = d (tie.Re.ref none).a := by
      rw [tie.ref_none.1]
      exact hd _ M.A_smooth
    rw [e1]
    refine mul_nonneg ?_ (by exact_mod_cast h1 _)
    simp [RootModel.coef]

end RootFieldNumerics
