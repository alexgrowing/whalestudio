import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt

noncomputable section

open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.Lit.Geo

def OneStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (Y : GA E a → Herm E a) (C : ℝ), IsFld U Y C → ∀ q : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ η : Co Ξ q, IsLev U Ξ η →
      ∃ η' : Co Ξ q, IsLev U Ξ η' ∧ dCo (smLie Ξ) η' = dCo (smLie Ξ) η ∧ ∀ (g : GA E a) (M M' : ℝ), 0 ≤ M → 0 ≤ M' →
        (∀ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + (Y g).1 → Bd η (g * infGL E a h) M) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + t • (Y g).1 →
          Bd (Ξ := Ξ) (dCo (smLie Ξ) η) (g * infGL E a h) M') → Bd η' g (B * (M + M'))

def BdBasis : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ),
    ∃ (T : Finset (Fin q → Herm E a)) (B : ℝ), 0 ≤ B ∧ ∀ (α : Co Ξ q) (g : GA E a) (M : ℝ), 0 ≤ M →
      (∀ X ∈ T, ‖ev (α X) (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ M) → Bd α g (B * M)

def BdCompact : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → ∀ R : ℝ,
      ∃ M : ℝ, 0 ≤ M ∧ ∀ g : GA E a, qht g ≤ R → Bd α g M

def BdGrowth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q),
    (Moderate α → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ g : GA E a, Bd α g (C * qht g ^ N)) ∧
    (Rapid α → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA E a, Bd α g (C / qht g ^ N))

def Prim : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ),
    IsStep U f Y C c f₀ → ∀ (q : ℕ) (η : Co Ξ q), IsLev U Ξ η → Moderate (Ξ := Ξ) (dCo (smLie Ξ) η) →
      ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, ∃ η' : Co Ξ q, IsLev U Ξ η' ∧ dCo (smLie Ξ) η' = dCo (smLie Ξ) η ∧
        ∀ g : GA E a, f g ≤ n * c → Bd η' g (Real.exp (D * (n + 1)))

def CutBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ) (u : Sm E a) (η ζ : Co Ξ q),
    (∀ (X : Fin (q + 1) → Herm E a) g, ev (dCo (smLie Ξ) ζ X) g = u.1 g • ev (dCo (smLie Ξ) η X) g +
      ∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * (lie E a (toL (X i).1) u).1 g) • ev (η (i.removeNth X)) g) →
    ∀ (g : GA E a) (s b M M' : ℝ), 0 ≤ M → 0 ≤ M' → 0 ≤ b →
      ‖1 - u.1 (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ s →
      (∀ X, ‖(lie E a X u).1 (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ b * ‖X‖) →
      (b = 0 ∨ Bd η g M) → Bd (Ξ := Ξ) (dCo (smLie Ξ) η) g M' →
      Bd (Ξ := Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g (s * M' + (q + 1) * b * M)

def Approx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ U : Subgroup (GL (Fin a) (Af E)),
    IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (q : ℕ) (η : Co Ξ q),
    IsLev U Ξ η → Moderate (Ξ := Ξ) (dCo (smLie Ξ) η) → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ R : ℝ, ∃ ζ : Co Ξ q, IsLev U Ξ ζ ∧
      CSupp ζ ∧ CSupp (Ξ := Ξ) (dCo (smLie Ξ) ζ) ∧ ∀ g : GA E a,
        (qht g ≤ R → Bd (Ξ := Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g 0) ∧
        Bd (Ξ := Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g (C * qht g ^ N)

def PtRetr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a),
    IsData Ξ r χ G e → ∀ (q : ℕ) (α β : Co Ξ q), IsLev U Ξ α → IsLev U Ξ β → ∀ g : GA E a,
      ptIp χ G e α β g = ∑ I : Fin q → Fin n,
        star (ev (α fun i => e (I i)) (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1) ⬝ᵥ
          G *ᵥ ev (β fun i => e (I i)) (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1

def PtBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a),
    IsData Ξ r χ G e → ∀ q : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ α β : Co Ξ q, IsLev U Ξ α → IsLev U Ξ β → ∀ (g : GA E a) (M M' : ℝ),
      0 ≤ M → 0 ≤ M' → Bd α g M → Bd β g M' → ‖ptIp χ G e α β g‖ ≤ B * M * M'

theorem ptIp_sub {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q : ℕ} (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) {n : ℕ} (e : Fin n → Herm E a) (α β β' : Co Ξ q) (g : GA E a) :
    ptIp χ G e α (β - β') g = ptIp χ G e α β g - ptIp χ G e α β' g := by
  simp only [ptIp, AlternatingMap.sub_apply, map_sub, Pi.sub_apply, Matrix.mulVec_sub, dotProduct_sub,
    Finset.sum_sub_distrib, mul_sub]

theorem firstGeometricCondition_of_properties (h1 : PairFacts) (h2 : QhtFacts) (h3 : LevD) (h4 : BdGrowth) (h5 : Approx) (h6 : PtBd)
    (h7 : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure],
      IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)) : G1 := by
  intro E _ _ _ a ha μ _ U hUo hUc Ξ r χ G n e hD q β η hβ hη hR hδ hM
  haveI := h7 E a μ
  obtain ⟨N, C, hC, hA⟩ := h5 E a ha U hUo hUc Ξ q η hη hM
  obtain ⟨C', hC', hB⟩ := (h4 E a Ξ (q + 1) β).2 hR (N + 1)
  obtain ⟨B, hB0, hP⟩ := h6 E a ha U hUo Ξ r χ G n e hD (q + 1)
  have hdη := (h3 E a U Ξ q η hη).1
  have hq := (h2 E a).1
  have key : ∀ R : ℝ, 0 < R → ‖pair μ χ G e β (dCo (smLie Ξ) η)‖ ≤
      B * C' * C * (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ).real Set.univ / R := fun R hR0 => by
    obtain ⟨ζ, hζ, hc, hc', hg⟩ := hA R
    have hdζ := (h3 E a U Ξ q ζ hζ).1
    have hγ := (h3 E a U Ξ (q + 1) _ hdη).2 _ hdζ
    have i1 := (h1 E a ha μ U hUo Ξ r χ G n e hD (q + 1)).1 β _ hβ hdη hR hM
    have i2 := ((h1 E a ha μ U hUo Ξ r χ G n e hD (q + 1)).2.1 _ β hdζ hβ hc').2
    have z : pair μ χ G e β (dCo (smLie Ξ) ζ) = 0 := by
      rw [(h1 E a ha μ U hUo Ξ r χ G n e hD q).2.2.2 β ζ hβ hζ (Or.inr hc), hδ]
      simp [pair, ptIp]
    have e1 : pair μ χ G e β (dCo (smLie Ξ) η) = pair μ χ G e β (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) := by
      rw [← sub_zero (pair μ χ G e β (dCo (smLie Ξ) η)), ← z]
      simp only [pair, ptIp_sub]
      exact (integral_sub i1 i2).symm
    rw [e1, mul_div_right_comm]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
    have q1 := hq x.out
    have q0 : 0 < qht x.out := one_pos.trans_le q1
    by_cases hx : qht x.out ≤ R
    · refine (hP β _ hβ hγ x.out _ 0 (by positivity) le_rfl (hB _) ((hg _).1 hx)).trans ?_
      rw [mul_zero]
      positivity
    · refine (hP β _ hβ hγ x.out _ _ (by positivity) (by positivity) (hB _) (hg _).2).trans ?_
      have e2 : B * (C' / qht x.out ^ (N + 1)) * (C * qht x.out ^ N) = B * C' * C / qht x.out := by
        field_simp
        ring
      rw [e2]
      exact div_le_div_of_nonneg_left (by positivity) hR0 (not_le.1 hx).le
  exact norm_le_zero_iff.1 (ge_of_tendsto (tendsto_const_nhds.div_atTop Filter.tendsto_id)
    ((Filter.eventually_gt_atTop 0).mono key))

end UpperTheory.V.Lit.Geo
