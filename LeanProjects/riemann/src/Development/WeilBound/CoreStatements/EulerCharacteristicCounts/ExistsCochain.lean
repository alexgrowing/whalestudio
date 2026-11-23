import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlochKatoCocycleOfCrysDeRhamPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCoboundaryLift

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

namespace PositivityTheory.LocalTateOrthogonality.Orth

section Pairing

variable {Qp : Type} [Field Qp] {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (P : V →ₗ[LL] V' →ₗ[LL] LL) (R : Type) [CommRing R] [Algebra Qp R]

def pr : V ⊗[Qp] R →ₗ[Qp] V' ⊗[Qp] R →ₗ[Qp] LL ⊗[Qp] R :=
  TensorProduct.map₂ (P.restrictScalars₁₂ Qp Qp) (LinearMap.mul Qp R)

variable {R}

@[simp] theorem pr_tmul (v : V) (r : R) (v' : V') (r' : R) :
    pr P R (v ⊗ₜ[Qp] r) (v' ⊗ₜ[Qp] r') = P v v' ⊗ₜ[Qp] (r * r') := rfl

theorem pr_smul_right (x : V ⊗[Qp] R) (c : LL) (v' : V') (r' : R) :
    pr P R x ((c • v') ⊗ₜ[Qp] r') = c • pr P R x (v' ⊗ₜ[Qp] r') := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v r => rw [pr_tmul, pr_tmul, map_smul, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, smul_add]

end Pairing

section Algebra

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    {P : V →ₗ[LL] V' →ₗ[LL] LL}

open GlobalTheory.FundDel

theorem charRep_apply (χ : G →* LLˣ) (g : G) (x : LL) : charRep χ g x = (χ g : LL) * x := rfl

theorem pr_act (hP : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y) (g : G)
    (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    actVB PD (charRep (cycLL PD LL)) g (pr P B x y) = pr P B (actVB PD ρ g x) (actVB PD ρ' g y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul v r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul v' r' =>
      rw [pr_tmul, actVB_tmul', actVB_tmul', actVB_tmul', pr_tmul, hP, map_mul, charRep_apply]

theorem pr_actdR (hP : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y) (g : G)
    (x : V ⊗[Qp] BdR) (y : V' ⊗[Qp] BdR) :
    actVdR PD (charRep (cycLL PD LL)) g (pr P BdR x y) =
      pr P BdR (actVdR PD ρ g x) (actVdR PD ρ' g y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul v r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul v' r' =>
      rw [pr_tmul, actVdR_tmul', actVdR_tmul', actVdR_tmul', pr_tmul, hP, map_mul, charRep_apply]

theorem pr_φ (x : V ⊗[Qp] B) (v' : V') :
    φVB PD (LL := LL) (V := LL) (pr P B x (v' ⊗ₜ[Qp] 1)) =
      pr P B (φVB PD (LL := LL) (V := V) x) (v' ⊗ₜ[Qp] 1) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul v r => rw [pr_tmul, φVB_tmul', φVB_tmul', pr_tmul, mul_one, mul_one]

theorem pr_ι (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    ιV PD (LL := LL) (V := LL) (pr P B x y) =
      pr P BdR (ιV PD (LL := LL) (V := V) x) (ιV PD (LL := LL) (V := V') y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul v r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul v' r' => rw [pr_tmul, ιV_tmul', ιV_tmul', ιV_tmul', pr_tmul, map_mul]

theorem pr_fil (a : ℤ) (y : V ⊗[Qp] BdR) (hy : y ∈ FilV PD (LL := LL) (V := V) a) (v' : V') :
    pr P BdR y (v' ⊗ₜ[Qp] 1) ∈ FilV PD (LL := LL) (V := LL) a := by
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [AlgebraTensorModule.map_tmul, pr_tmul, mul_one]
    exact GlobalTheory.CobCrisLift.tmul_mem PD _ b.2
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply]
    exact add_mem hx hy

theorem exists_cochain
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y)
    (hsurj : ∀ (u : LL ⊗[Qp] B) (w : LL ⊗[Qp] BdR), ∃ (x : LL ⊗[Qp] B) (y : LL ⊗[Qp] BdR),
      y ∈ FilV PD (LL := LL) (V := LL) 0 ∧ x - φVB PD (LL := LL) (V := LL) x = u ∧
        ιV PD (LL := LL) (V := LL) x - y = w)
    (hker : ∀ x : LL ⊗[Qp] B, φVB PD (LL := LL) (V := LL) x = x →
      ιV PD (LL := LL) (V := LL) x ∈ FilV PD (LL := LL) (V := LL) 0 → ∃ v : LL, x = v ⊗ₜ[Qp] (1 : B))
    (a : G → V) (x : V ⊗[Qp] B) (hx : ∀ g, a g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x)
    (h₁ : x - φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ)
    (d : V ⊗[Qp] BdR) (h₂ : d ∈ DdR PD ρ)
    (hd : ιV PD (LL := LL) (V := V) x - d ∈ FilV PD (LL := LL) (V := V) 0)
    (b : G → V') (hb : ∀ g h, b (g * h) = b g + ρ' g (b h))
    (β : V' ⊗[Qp] B) (hβ : ∀ g, b g ⊗ₜ[Qp] (1 : B) = actVB PD ρ' g β - β) :
    ∃ (f : G → LL) (w : LL ⊗[Qp] B),
      (∀ g, f g ⊗ₜ[Qp] (1 : B) = pr P B x (b g ⊗ₜ[Qp] 1) +
        (actVB PD (charRep (cycLL PD LL)) g w - w)) ∧
      ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) f = cupL ρ' P a b := by
  obtain ⟨w, w', hw', hw1, hw2⟩ := hsurj (pr P B (x - φVB PD (LL := LL) (V := V) x) β)
    (pr P BdR d (ιV PD (LL := LL) (V := V') β))
  have key : ∀ g, ∃ v : LL, pr P B x (b g ⊗ₜ[Qp] 1) +
      (actVB PD (charRep (cycLL PD LL)) g (-w) - (-w)) = v ⊗ₜ[Qp] (1 : B) := by
    intro g
    have e₁ : actVB PD ρ g (x - φVB PD (LL := LL) (V := V) x) = x - φVB PD (LL := LL) (V := V) x :=
      sub_eq_zero.1 ((Submodule.mem_iInf _).1 h₁ g)
    have e₂ : actVdR PD ρ g d = d := sub_eq_zero.1 ((Submodule.mem_iInf _).1 h₂ g)
    have f₁ : pr P B (x - φVB PD (LL := LL) (V := V) x) (b g ⊗ₜ[Qp] 1) =
        actVB PD (charRep (cycLL PD LL)) g (w - φVB PD (LL := LL) (V := LL) w) -
          (w - φVB PD (LL := LL) (V := LL) w) := by
      rw [hw1, pr_act PD hP, e₁, hβ, map_sub (pr P B _)]
    have hιb : (b g ⊗ₜ[Qp] (1 : BdR)) = actVdR PD ρ' g (ιV PD (LL := LL) (V := V') β) -
        ιV PD (LL := LL) (V := V') β := by
      rw [← ιV_actVB', ← map_sub, ← hβ, ιV_tmul', map_one]
    have f₂ : pr P BdR d (b g ⊗ₜ[Qp] 1) =
        actVdR PD (charRep (cycLL PD LL)) g (ιV PD (LL := LL) (V := LL) w - w') -
          (ιV PD (LL := LL) (V := LL) w - w') := by
      rw [hw2, pr_actdR PD hP, e₂, hιb, map_sub (pr P BdR _)]
    apply hker
    · rw [map_sub (pr P B), LinearMap.sub_apply, map_sub] at f₁
      rw [map_add, map_sub, pr_φ, φVB_actVB', map_neg, map_neg, map_neg, ← sub_eq_zero, ← neg_eq_zero,
        ← sub_eq_zero.2 f₁]
      abel
    · have : ιV PD (LL := LL) (V := LL) (pr P B x (b g ⊗ₜ[Qp] 1) +
          (actVB PD (charRep (cycLL PD LL)) g (-w) - (-w))) =
          pr P BdR (ιV PD (LL := LL) (V := V) x - d) (b g ⊗ₜ[Qp] 1) -
            (actVdR PD (charRep (cycLL PD LL)) g w' - w') := by
        rw [map_add, map_sub, pr_ι, ιV_tmul', map_one, ιV_actVB', map_sub (pr P BdR),
          LinearMap.sub_apply, f₂, map_sub, map_neg, map_neg]
        abel
      rw [this]
      exact sub_mem (pr_fil PD 0 _ hd _) (sub_mem (actVdR_mem_FilV' PD _ g 0 _ hw') hw')
  choose f hf using key
  refine ⟨f, -w, fun g => (hf g).symm, ?_⟩
  funext ⟨g, h⟩
  apply tmul_one_injective' PD
  change (charRep (cycLL PD LL) g (f h) - f (g * h) + f g) ⊗ₜ[Qp] (1 : B) =
    P (a g) (ρ' g (b h)) ⊗ₜ[Qp] (1 : B)
  have e : charRep (cycLL PD LL) g (f h) ⊗ₜ[Qp] (1 : B) =
      actVB PD (charRep (cycLL PD LL)) g (f h ⊗ₜ[Qp] (1 : B)) := by
    rw [actVB_tmul', map_one]
  have e' : P (a g) (ρ' g (b h)) ⊗ₜ[Qp] (1 : B) =
      pr P B (a g ⊗ₜ[Qp] (1 : B)) (ρ' g (b h) ⊗ₜ[Qp] (1 : B)) := by rw [pr_tmul, mul_one]
  rw [add_tmul, sub_tmul, e, e', hx, ← hf, ← hf, ← hf, map_add, pr_act PD hP, actVB_tmul', map_one, hb,
    add_tmul, map_add, map_sub, actVB_mul', map_sub (pr P B), LinearMap.sub_apply]
  abel

end Algebra

section Top

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)

theorem orthL_of
    (hfund : ∀ (LL : Type) [Field LL] [Algebra Qp LL],
      (∀ (u : LL ⊗[Qp] B) (w : LL ⊗[Qp] BdR), ∃ (x : LL ⊗[Qp] B) (y : LL ⊗[Qp] BdR),
      y ∈ FilV PD (LL := LL) (V := LL) 0 ∧ x - φVB PD (LL := LL) (V := LL) x = u ∧
        ιV PD (LL := LL) (V := LL) x - y = w) ∧
      ∀ x : LL ⊗[Qp] B, φVB PD (LL := LL) (V := LL) x = x →
      ιV PD (LL := LL) (V := LL) x ∈ FilV PD (LL := LL) (V := LL) 0 → ∃ v : LL, x = v ⊗ₜ[Qp] (1 : B))
    (hlift : ∀ (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] (O : Type) [CommRing O]
      [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ A : GRep G Qp LL O, IsDR PD A.ρ →
      ∀ (c : G → A.V) (x : A.V ⊗[Qp] B), (∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD A.ρ g x - x) →
      x - φVB PD (LL := LL) (V := A.V) x ∈ Dcris PD A.ρ ∧ ∃ d ∈ DdR PD A.ρ,
        ιV PD (LL := LL) (V := A.V) x - d ∈ FilV PD (LL := LL) (V := A.V) 0)
    (hcont : LocalSituation.contCore PD) : GlobalTheory.CompanionTheory.LocDual.OrthL PD := by
  intro LL _ _ _ O _ _ hO A A' P hP hdR a ha b hb
  obtain ⟨-, x, hx⟩ := ha
  obtain ⟨⟨hbc, hb⟩, β, hβ⟩ := hb
  by_cases h0 : ∀ v v', P v v' = 0
  · refine ⟨0, continuous_const, ?_⟩
    rw [map_zero]
    funext z
    exact (h0 _ _).symm
  push Not at h0
  obtain ⟨v₀, v₀', hv⟩ := h0
  have : IsTopologicalRing LL := hO.2.2.2.1
  have hPc : Continuous fun z : A.V × A'.V => P z.1 z.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left P
  have hχ : Continuous fun g => ((cycLL PD LL g : LLˣ) : LL) := by
    have : (fun g => ((cycLL PD LL g : LLˣ) : LL)) =
        fun g => P (A.ρ g v₀) (A'.ρ g v₀') * (P v₀ v₀')⁻¹ := by
      funext g
      rw [hP.1, mul_inv_cancel_right₀ hv]
    rw [this]
    exact (hPc.comp ((A.cont v₀).prodMk (A'.cont v₀'))).mul continuous_const
  let A1 : GRep G Qp LL O :=
    { V := LL
      ρ := charRep (cycLL PD LL)
      cont := fun y => hχ.mul continuous_const }
  obtain ⟨h₁, d, h₂, hd⟩ := hlift LL O hO A hdR a x hx
  obtain ⟨f, w, hf, hdf⟩ := exists_cochain PD hP.1 (hfund LL).1 (hfund LL).2 a x hx h₁ d h₂ hd b hb β hβ
  refine ⟨f, ?_, hdf⟩
  let e := Module.finBasis LL A'.V
  refine hcont LL O hO A1 _ (fun i => pr P B x (e i ⊗ₜ[Qp] 1)) (fun i g => e.coord i (b g))
    (fun i => (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp hbc) w f (fun g => ?_)
  refine (hf g).trans ?_
  congr 1
  conv_lhs => rw [← e.sum_repr (b g), TensorProduct.sum_tmul, map_sum]
  exact Finset.sum_congr rfl fun i _ => pr_smul_right P x _ _ _

end Top

theorem orthL_tied (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) : GlobalTheory.CompanionTheory.LocDual.OrthL (P.PD K) :=
  orthL_of (P.PD K) (fun LL _ _ => GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI T K LL LL)
    (fun LL _ _ _ O _ _ hO A => GlobalTheory.CobCrisLift.coboundary_lift l P AI T K LL O hO A)
    (GlobalTheory.FundCont.contCore_tied l P AI T K)

theorem tdOrth : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l),
    GlobalTheory.CompanionTheory.LocDual.OrthL ((D.loc l).PD K) :=
  fun D l _ K => orthL_tied l (D.loc l) (D.locA l) (D.locT l) K

end PositivityTheory.LocalTateOrthogonality.Orth
