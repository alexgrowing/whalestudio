import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SubstitutionOfVariables

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser Aser Aser')

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

abbrev wK (p : ℕ) [Fact p.Prime] (c : WW p) : K0 p := algebraMap (WW p) (K0 p) c

def RestBeta (p : ℕ) [Fact p.Prime] : Prop :=
  5 ≤ p → DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be →
    ∃ c : WW p, (sigW p)^[2] c = c ∧ E0 p (inParam p be - Gser p (wK p c) (wK p (sigW p c)))

def RestGc (p : ℕ) [Fact p.Prime] : Prop :=
  5 ≤ p → ∀ c : WW p, (sigW p)^[2] c = c → ∀ (n' r0 r1 : ℕ), 2 ≤ n' → Even n' → ∀ (B : OmBasis p n')
    (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∀ μ : PowerSeries K', PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X →
    ∃ u : Fin n' → K', (∀ s, u s ∈ Rp p K' vp) ∧ ∃ V : MvPowerSeries (Zidx n' r0 r1) K', IntR (Rp p K' vp) V ∧
      MvPowerSeries.subst (tOf vp μ (coordZ B K' 1)) (expK (-(MvPowerSeries.map (algebraMap (K0 p) K')
          (Gt p (Eidx n' r0 r1) (wK p c) (wK p (sigW p c)))))) =
        expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hhS p K' u)) * V

def RestGcA {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ c : WW p, (sigW p)^[2] c = c → ∀ (j : ℕ)
    (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∀ μ : PowerSeries K', PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X →
    ∃ u : ∀ v : X.Pl, Fin (X.G.P.n' v) → K', (∀ v s, u v s ∈ Rp p K' vp) ∧
      ∃ V : MvPowerSeries (X.ZA j) K', IntR (Rp p K' vp) V ∧
        MvPowerSeries.subst (tOf vp μ (X.coordZA K' j)) (expK (-(MvPowerSeries.map (algebraMap (K0 p) K')
            (Gt p (X.EA j) (wK p c) (wK p (sigW p c)))))) =
          (∏ v, expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v (u v)))) * V

section

variable {p : ℕ} [hp : Fact p.Prime]

theorem th_Gser_const (c c' : K0 p) : MvPowerSeries.constantCoeff (Gser p c c') = 0 := by
  have hA : MvPowerSeries.constantCoeff (Aser (K0 p) p) = 0 := by
    show Aser (K0 p) p 0 = 0
    simp [Aser]
  have hA' : MvPowerSeries.constantCoeff (Aser' (K0 p) p) = 0 := by
    show Aser' (K0 p) p 0 = 0
    simp [Aser']
  simp [Gser, hA, hA']

theorem th_be_const {be : MvPowerSeries (Fin 2) (K0 p)} (h : BeProp p be) :
    MvPowerSeries.constantCoeff be = 0 := by
  by_contra hne
  have hh := (h.ab 0 hne).1
  simp at hh

theorem th_coordZ_eq {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') :
    coordZ (r0 := r0) (r1 := r1) B K' vp = fun x => MvPowerSeries.C vp * coordZ B K' 1 x := by
  funext x
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;>
    simp only [coordZ, Finset.mul_sum, one_mul, map_mul, mul_assoc]

theorem th_coordZ_int {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : IntR (Rp p K' vp) (coordZ B K' 1 x) := by
  intro n
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;>
  · simp only [coordZ, map_sum, one_mul]
    refine Subring.sum_mem _ fun s _ => ?_
    rw [MvPowerSeries.coeff_C_mul]
    refine Subring.mul_mem _ (Subring.subset_closure (Set.mem_union_left _ ⟨_, rfl⟩)) ?_
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _

theorem th_coordZA_int (X : Sys p) (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') (j : ℕ)
    (x : X.EA j ⊕ X.EA j) : IntR (Rp p K' vp) (X.coordZA K' j x) := by
  intro n
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;>
  · simp only [Sys.coordZA, map_sum]
    refine Subring.sum_mem _ fun s _ => ?_
    rw [MvPowerSeries.coeff_C_mul]
    refine Subring.mul_mem _ (Subring.subset_closure (Set.mem_union_left _ ⟨_, rfl⟩)) ?_
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _

private theorem constantCoeff_coordZ_eq_zero {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K']
    (vp : K') (x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : MvPowerSeries.constantCoeff (coordZ B K' vp x) = 0 := by
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;> simp [coordZ]

theorem restSExp_of (hB : RestBeta p) (hG : RestGc p) : RestSExp p := by
  intro h5 hD be hbe n' r0 r1 h2 hev B Ph hPh K' _ _ vp hvp
  obtain ⟨c, hc, hE⟩ := hB h5 hD be hbe
  obtain ⟨μ, hμ0, hμR, hμ1⟩ := exists_mu (p := p) K' vp hvp
  obtain ⟨u, hu, V, hV, hGeq⟩ := hG h5 c hc n' r0 r1 h2 hev B K' vp hvp μ hμ0 hμ1
  obtain ⟨V', hV', hred⟩ := th_reduce (p := p) be (th_be_const hbe) (wK p c) (wK p (sigW p c))
    (th_Gser_const _ _) (fun _ => hE) Ph hPh K' vp μ hμ0 hμR hμ1 (coordZ B K' 1)
    (fun i => constantCoeff_coordZ_eq_zero B K' 1 i) (fun i => th_coordZ_int B K' vp i)
  refine ⟨u, hu, V * V', IntR_mul hV hV', ?_⟩
  unfold ThZ
  rw [th_coordZ_eq B K' vp, hred, hGeq, mul_assoc]

private theorem constantCoeff_coordZA_eq_zero (X : Sys p) (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ)
    (x : X.EA j ⊕ X.EA j) : MvPowerSeries.constantCoeff (X.coordZA K' j x) = 0 := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA]

private theorem mvPowerSeries_map_algebraMap_map_algebraMap (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K'] [Algebra (K0 p) K']
    [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] {σ : Type} (F : MvPowerSeries σ (K0 p)) :
    MvPowerSeries.map (algebraMap K1 K') (MvPowerSeries.map (algebraMap (K0 p) K1) F) =
      MvPowerSeries.map (algebraMap (K0 p) K') F := by
  ext n
  simp [MvPowerSeries.coeff_map, IsScalarTower.algebraMap_apply (K0 p) K1 K']

theorem restSExpA_of (X : Sys p) (hB : RestBeta p) (hG : RestGcA X) : RestSExpA X := by
  intro hD be hbe j Ph hPh K1 _ _ K' _ _ _ _ vp hvp
  obtain ⟨c, hc, hE⟩ : ∃ c : WW p, (sigW p)^[2] c = c ∧
      (X.EA j → E0 p (inParam p be - Gser p (wK p c) (wK p (sigW p c)))) := by
    by_cases h5 : 5 ≤ p
    · obtain ⟨c, hc, hE⟩ := hB h5 hD be hbe
      exact ⟨c, hc, fun _ => hE⟩
    · refine ⟨0, ?_, fun e => absurd (X.std e.1).five_le h5⟩
      first
        | exact Function.iterate_fixed (map_zero (sigW p)) 2
        | simp
  obtain ⟨μ, hμ0, hμR, hμ1⟩ := exists_mu (p := p) K' vp hvp
  obtain ⟨u, hu, V, hV, hGeq⟩ := hG c hc j K' vp hvp μ hμ0 hμ1
  obtain ⟨V', hV', hred⟩ := th_reduce (p := p) be (th_be_const hbe) (wK p c) (wK p (sigW p c))
    (th_Gser_const _ _) hE Ph hPh K' vp μ hμ0 hμR hμ1 (X.coordZA K' j)
    (fun i => constantCoeff_coordZA_eq_zero X K' j i) (fun i => th_coordZA_int X K' vp j i)
  refine ⟨u, hu, V * V', IntR_mul hV hV', ?_⟩
  rw [atPi_map_ThZA (X := X), mvPowerSeries_map_algebraMap_map_algebraMap, hred, hGeq, mul_assoc]

theorem baseChange_preserves_unitary_of (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) (hB : RestBeta p) (hG : RestGc p) :
    Conclusion1 D X Y :=
  kernel_expansion_of_restrictions D X Y hA (restSExp_of hB hG) (restSInt p)

theorem expansion_all_places_of_computation (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) (hB : RestBeta p) (hG : RestGcA X) :
    ExpansionsMultiply D X Y :=
  all_places_of_restrictions (hA := hA) (hE := restSExpA_of X hB hG) (hI := restSIntA (X := X))

end

end Formalism.MainNotions.FormalGroupSystem.Pf
