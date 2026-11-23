import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SimilitudeFactorFormGroupBoundedOfTestSupport
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentialsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isSmoothHerm_combLine {σ : Type} [Fintype σ] {A : σ → HermLine ι} (hA : ∀ a, IsSmoothHerm (A a))
    (n : σ → ℤ) : IsSmoothHerm (GlobalTheory.CompanionTheory.Ar.PB.combLine A n) := by
  refine contDiffOn_prod fun a _ => ?_
  intro z hz
  have h0 : (A a).h z ≠ 0 := ((A a).pos z hz).ne'
  have hf := hA a z hz
  have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (A a).h z ^ m)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
    intro m
    cases m with
    | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
    | negSucc k =>
      simp only [zpow_negSucc]
      exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
  exact key _

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {P : LocPot X}
    (hP : IsPotential A P) (x : X) : IsTwiceDifferentiableAt A P x := by
  intro j hj
  have hopen := (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  have hm : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x :=
    ⟨(A.chart j).map_source hj, by
      rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact P.mem_U x⟩
  exact ((hP.1 x j).contDiffAt (hopen.mem_nhds hm)).of_le (by first | exact ENat.LEInfty.out | exact (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)) | simp)

theorem mInt_potOf_eq_of_deg {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {L L' : Fin e → HermLine ι}
    (hL : ∀ j, IsSmoothHerm (L j)) (hL' : ∀ j, IsSmoothHerm (L' j)) (ha : ∀ j, (L j).a = (L' j).a) :
    mInt R.A (fun j => potOf R (L j)) (fun _ => 1) = mInt R.A (fun j => potOf R (L' j)) (fun _ => 1) := by
  let B : Fin e → HermLine ι := fun j => GlobalTheory.CompanionTheory.Ar.PB.combLine ![L j, L' j] ![1, -1]
  have hB0 : ∀ j, (B j).a = 0 := fun j => by
    rw [(combLine_div (L j) (L' j)).1, ha j, sub_self]
  have hBs : ∀ j, IsSmoothHerm (B j) := fun j =>
    isSmoothHerm_combLine (fun a => by
      fin_cases a
      · exact hL j
      · exact hL' j) _
  let u : Fin e → R.X → ℝ := fun j x => Real.log ((B j).h (R.lift x x))
  have hu : ∀ j, R.A.Smooth (u j) := fun j => smooth_diag R (hBs j) (hB0 j)
  have h1 : mInt R.A (fun j => potOf R (L j)) (fun _ => 1) =
      mInt R.A (fun j => potOf R (L' j) + LocPot.ofFun (u j)) (fun _ => 1) := by
    refine mInt_congr _ (locDens_congr_of_eqOn R fun i x y hy => ?_) fun _ => rfl
    show Real.log ((L i).h (R.lift x y)) = Real.log ((L' i).h (R.lift x y)) + Real.log ((B i).h (R.lift y y))
    have hm := (R.mem x y hy).1
    rw [← h_eq_of_sameOrbit (hB0 i) (R.compat x y y ⟨hy, R.mem_U y⟩), (combLine_div (L i) (L' i)).2,
      Real.log_div ((L i).pos _ hm).ne' ((L' i).pos _ hm).ne']
    ring
  rw [h1]
  exact massIndep R.A _ u (fun i => isPotential_potOf R (hL' i)) hu

end Lines

section Coef

variable {Ψ : Type} [DecidableEq Ψ] {N : ℕ}

def rootCoef (r p : Ψ × Fin N) : ℤ :=
  (if p.1 = r.1 ∧ (p.2 : ℕ) + 1 = r.2 then 1 else 0) - (if p = r then 1 else 0)

theorem sum_rootCoef_mul [Fintype Ψ] (r : Ψ × Fin N) (f : Ψ × Fin N → ℤ) :
    ∑ p, rootCoef r p * f p =
      (if h : 0 < (r.2 : ℕ) then f (r.1, ⟨(r.2 : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) r.2.isLt⟩) else 0) - f r := by
  obtain ⟨τ, i⟩ := r
  simp only [rootCoef, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  congr 1
  · split_ifs with h
    · rw [Finset.sum_eq_single (τ, ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩)]
      · rw [if_pos ⟨rfl, by simp only; omega⟩]
      · rintro ⟨τ', l⟩ - hne
        rw [if_neg]
        rintro ⟨h1, h2⟩
        simp only at h1 h2
        subst h1
        exact hne (by simp only [Prod.mk.injEq, true_and]; ext; simp only; omega)
      · simp
    · refine Finset.sum_eq_zero fun p _ => if_neg ?_
      rintro ⟨-, h2⟩
      have h2' : (p.2 : ℕ) + 1 = i := h2
      omega
  · simp

theorem sum_neg_mul_rootCoef [Fintype Ψ] (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    ∑ r, -lam r * (rootCoef r p : ℝ) = GlobalTheory.CompanionTheory.Ar.PB.gap lam p := by
  obtain ⟨τ, l⟩ := p
  have h2 : ∑ r : Ψ × Fin N, lam r * (if (τ, l) = r then (1 : ℝ) else 0) = lam (τ, l) := by simp
  have h1 : ∑ r : Ψ × Fin N, lam r * (if (τ, l).1 = r.1 ∧ (((τ, l).2 : Fin N) : ℕ) + 1 = r.2 then (1 : ℝ) else 0) =
      if h : (l : ℕ) + 1 < N then lam (τ, ⟨(l : ℕ) + 1, h⟩) else 0 := by
    split_ifs with h
    · rw [Finset.sum_eq_single (τ, ⟨(l : ℕ) + 1, h⟩)]
      · simp
      · rintro ⟨τ', m⟩ - hne
        rw [if_neg, mul_zero]
        rintro ⟨h1, h2⟩
        simp only at h1 h2
        subst h1
        exact hne (by simp only [Prod.mk.injEq, true_and]; ext; simp only; omega)
      · simp
    · refine Finset.sum_eq_zero fun r _ => ?_
      rw [if_neg, mul_zero]
      rintro ⟨-, h2⟩
      have := r.2.isLt
      simp only at h2
      omega
  have h3 : GlobalTheory.CompanionTheory.Ar.PB.gap lam (τ, l) =
      lam (τ, l) - if h : (l : ℕ) + 1 < N then lam (τ, ⟨(l : ℕ) + 1, h⟩) else 0 := by
    unfold GlobalTheory.CompanionTheory.Ar.PB.gap gapX
    split_ifs with h <;> simp [h]
  rw [h3, ← h1, ← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [rootCoef]
  push_cast
  ring

end Coef

section Real

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mInt_ref_eq {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (w : Fin D → σ) :
    mInt Re.R.A (fun j => potOf Re.R (Re.ref (w j))) (fun _ => 1) = Re.deg * S.degNum w := by
  have hth : ∀ a, IsPotential S.A (S.th a) := fun a => (S.sing a).1
  have hpb : ∀ a, IsPotential Re.R.A ((S.th a).pullback Re.π Re.holo.1) := fun a =>
    isPotentialPullback S.A Re.R.A Re.π Re.holo (S.th a) (hth a)
  have h1 := (GlobalTheory.T.monge_ampere_integral_congr_potentials D Re.R.X Re.R.A Set.univ (fun j => potOf Re.R (Re.ref (w j)))
    (fun j => (S.th (w j)).pullback Re.π Re.holo.1) (fun _ => 1) (fun _ => 1)
    (fun j => by simp) (fun i => Re.ref_pot (w i)) (fun i x _ => isC2At_of_isPotential _ (hpb _) x)
    (fun _ _ => rfl)).1
  rw [h1]
  exact (degreeFormulaInt S.A Re.R.A Re.π Re.holo Re.deg Re.br Re.degree (fun j => S.th (w j)) (fun i => hth _)
    (fun _ => 1) (mIntegrableCont S.A _ (fun i => hth _) _ continuous_const)).2

theorem mInt_combLine_eq {D : ℕ} {σ : Type} [Fintype σ] {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P)
    (n : Fin D → σ → ℤ) :
    mInt Re.R.A (fun j => potOf Re.R (GlobalTheory.CompanionTheory.Ar.PB.combLine Re.ref (n j))) (fun _ => 1) =
      ∑ w : Fin D → σ, (∏ i, (n i (w i) : ℝ)) * (Re.deg * S.degNum w) := by
  have hP : ∀ a, IsPotential Re.R.A (potOf Re.R (Re.ref a)) := fun a => isPotential_potOf Re.R (Re.ref_smooth a)
  have h1 : mInt Re.R.A (fun j => potOf Re.R (GlobalTheory.CompanionTheory.Ar.PB.combLine Re.ref (n j))) (fun _ => 1) =
      mInt Re.R.A (fun j => sumPot (fun a => (n j a : ℝ)) fun a => potOf Re.R (Re.ref a)) (fun _ => 1) := by
    refine mInt_congr _ (fun j y hy => ?_) fun _ => rfl
    refine ReciprocityTheory.ChartRestriction.G.Geo.maDens_congr fun i => ?_
    filter_upwards [((Re.R.A.chart j).isOpen_inter_preimage_symm (Re.R.isOpen_U ((Re.R.A.chart j).symm y))).mem_nhds
      ⟨hy, Re.R.mem_U _⟩] with y' hy'
    have hm := (Re.R.mem _ _ hy'.2).1
    show Real.log (∏ a, (Re.ref a).h _ ^ n i a) = ∑ a, (n i a : ℝ) * Real.log ((Re.ref a).h _)
    rw [Real.log_prod fun a _ => (zpow_pos ((Re.ref a).pos _ hm) _).ne']
    exact Finset.sum_congr rfl fun a _ => Real.log_zpow _ _
  rw [h1, (GlobalTheory.T.monge_ampere_integral_multilinear_expansion D Re.R.X Re.R.A σ Set.univ (fun a => potOf Re.R (Re.ref a)) (fun j a => (n j a : ℝ))
    (fun _ => 1) (fun j => by simp) (fun a x _ => isC2At_of_isPotential _ (hP a) x)
    (fun w => mIntegrableCont _ _ (fun i => hP _) _ continuous_const)).2]
  exact Finset.sum_congr rfl fun w _ => by rw [mInt_ref_eq Re w]

end Real

section Main

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem geoMono_word (hE : ResExistsStatement) (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) {J : Ideal (MRing M.ι)}
    (R : AnLogRes M.P J (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N)) (w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N) → Ψ × Fin N) :
    M.geoMono (Finsupp.mapDomain some (∑ j, Finsupp.single (w j) 1)) =
      mInt R.A (fun j => potOf R (M.x 1 (w j))) (fun _ => 1) / (M.δ : ℝ) := by
  classical
  have hmap : Finsupp.mapDomain some (∑ j, Finsupp.single (w j) 1) =
      ∑ j, Finsupp.single (some (w j)) (1 : ℕ) := by
    rw [Finsupp.mapDomain_finset_sum]
    simp [Finsupp.mapDomain_single]
  rw [hmap]
  have hdeg : (∑ j, Finsupp.single (some (w j)) (1 : ℕ)).degree = GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N := by
    rw [map_sum]
    simp [Finsupp.degree_single]
  have hnone : (∑ j, Finsupp.single (some (w j)) (1 : ℕ)) none = 0 := by
    simp [Finsupp.finset_sum_apply]
  have hms : Finsupp.toMultiset (∑ j, Finsupp.single (some (w j)) (1 : ℕ)) =
      Multiset.map (fun j => some (w j)) Finset.univ.val := by
    rw [Finsupp.toMultiset_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    rw [Finset.sum_eq_multiset_sum]
    have e : (fun i => ({some (w i)} : Multiset (Option (Ψ × Fin N)))) = (fun p => {p}) ∘ fun j => some (w j) := rfl
    rw [e, ← Multiset.map_map, Multiset.sum_map_singleton]
  obtain ⟨ρ, hρ⟩ := GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.exists_perm_toList fun j => some (w j)
  have hML : GlobalTheory.CompanionTheory.Ar.Top.monoLines (M.line 1) (∑ j, Finsupp.single (some (w j)) (1 : ℕ))
      (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N) = (fun i => M.x 1 (w i)) ∘ ρ := by
    funext k
    have hk : (k : ℕ) < (Multiset.map (fun j => some (w j)) Finset.univ.val).toList.length := by
      have := k.2
      simp [Multiset.length_toList]
    unfold GlobalTheory.CompanionTheory.Ar.Top.monoLines
    rw [hms, dif_pos hk, hρ k hk]
    rfl
  unfold GlobalTheory.CompanionTheory.Ar.Top.RootModel.geoMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one, hML]
  congr 1
  refine (ptsIntegral_one_eq_mInt hE resBridge R M.arith (L := (fun i => M.x 1 (w i)) ∘ ρ)
    (fun j => M.x_smooth 1 _)).trans ?_
  exact mIntSymm R.A (fun j => potOf R (M.x 1 (w j))) ρ _

end Main

end GlobalTheory.CompanionTheory.Ar.Cmp
