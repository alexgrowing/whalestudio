import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCoboundaryLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystalline
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContCoreTied
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKOrth

section Pair

variable {Qp LL : Type} [Field Qp] [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (R : Type) [CommRing R] [Algebra Qp R]

def pairT (P : V →ₗ[LL] V' →ₗ[LL] LL) : V ⊗[Qp] R →ₗ[Qp] V' ⊗[Qp] R →ₗ[Qp] LL ⊗[Qp] R :=
  TensorProduct.curry ((TensorProduct.map (TensorProduct.lift (P.restrictScalars₁₂ Qp Qp))
    (LinearMap.mul' Qp R)) ∘ₗ (TensorProduct.tensorTensorTensorComm Qp V R V' R).toLinearMap)

variable {R}

@[simp] theorem pairT_tmul (P : V →ₗ[LL] V' →ₗ[LL] LL) (v : V) (r : R) (v' : V') (r' : R) :
    pairT R P (v ⊗ₜ[Qp] r) (v' ⊗ₜ[Qp] r') = P v v' ⊗ₜ[Qp] (r * r') := by
  simp [pairT]

theorem pairT_smul_right (P : V →ₗ[LL] V' →ₗ[LL] LL) (x : V ⊗[Qp] R) (c : LL) (y : V' ⊗[Qp] R) :
    pairT R P x (c • y) = c • pairT R P x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp [hx, hx', smul_add]
  | tmul v r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp [hy, hy', smul_add]
    | tmul v' r' =>
      rw [TensorProduct.smul_tmul', pairT_tmul, pairT_tmul, TensorProduct.smul_tmul', map_smul]

end Pair

section PD

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem charRep_apply (χ : G →* LLˣ) (g : G) (c : LL) : charRep χ g c = ((χ g : LLˣ) : LL) * c := by
  simp [charRep]

theorem actVB_tmul (ρ : Representation LL G V) (g : G) (v : V) (b : B) :
    actVB PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actB g b := rfl

theorem actVdR_tmul (ρ : Representation LL G V) (g : G) (v : V) (b : BdR) :
    actVdR PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actdR g b := rfl

theorem actVB_mul (ρ : Representation LL G V) (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b => simp [actVB_tmul, map_mul, Module.End.mul_apply]

theorem pairT_actVB (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y) (g : G)
    (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    pairT B P (actVB PD ρ g x) (actVB PD ρ' g y) =
      actVB PD (charRep (cycLL PD LL)) g (pairT B P x y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul v r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul v' r' =>
      rw [actVB_tmul, actVB_tmul, pairT_tmul, pairT_tmul, actVB_tmul, hP, charRep_apply, map_mul]

theorem pairT_actVdR (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = ((cycLL PD LL g : LLˣ) : LL) * P x y) (g : G)
    (x : V ⊗[Qp] BdR) (y : V' ⊗[Qp] BdR) :
    pairT BdR P (actVdR PD ρ g x) (actVdR PD ρ' g y) =
      actVdR PD (charRep (cycLL PD LL)) g (pairT BdR P x y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul v r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul v' r' =>
      rw [actVdR_tmul, actVdR_tmul, pairT_tmul, pairT_tmul, actVdR_tmul, hP, charRep_apply, map_mul]

theorem pairT_φVB (P : V →ₗ[LL] V' →ₗ[LL] LL) (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    φVB PD (LL := LL) (V := LL) (pairT B P x y) =
      pairT B P (φVB PD (LL := LL) (V := V) x) (φVB PD (LL := LL) (V := V') y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul v r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul v' r' =>
      simp [φVB, pairT_tmul]

theorem pairT_ιV (P : V →ₗ[LL] V' →ₗ[LL] LL) (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    ιV PD (LL := LL) (V := LL) (pairT B P x y) =
      pairT BdR P (ιV PD (LL := LL) (V := V) x) (ιV PD (LL := LL) (V := V') y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul v r =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul v' r' =>
      simp [ιV, pairT_tmul]

theorem pairT_filV (P : V →ₗ[LL] V' →ₗ[LL] LL) (a : ℤ) (z : V ⊗[Qp] BdR)
    (hz : z ∈ FilV PD (LL := LL) (V := V) a) (v' : V') :
    pairT BdR P z (v' ⊗ₜ[Qp] (1 : BdR)) ∈ FilV PD (LL := LL) (V := LL) a := by
  obtain ⟨y, rfl⟩ := hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply]; exact add_mem hy hy'
  | tmul v f =>
    rw [AlgebraTensorModule.map_tmul, pairT_tmul, mul_one]
    exact ⟨P v v' ⊗ₜ[Qp] f, rfl⟩

theorem actVdR_filV (ρ : Representation LL G V) (a : ℤ) (g : G) (z : V ⊗[Qp] BdR)
    (hz : z ∈ FilV PD (LL := LL) (V := V) a) : actVdR PD ρ g z ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨y, rfl⟩ := hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => simp only [map_add]; exact add_mem hy hy'
  | tmul v f =>
    rw [AlgebraTensorModule.map_tmul, actVdR_tmul]
    exact ⟨ρ g v ⊗ₜ[Qp] (⟨PD.actdR g f, PD.Fil_G g a f f.2⟩ : (PD.Fil a).restrictScalars Qp), rfl⟩

include PD in
theorem nontrivial_B' : Nontrivial B := by
  have : Nontrivial BdR := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply PD.not_mem_filtration_two
    rw [Subsingleton.elim (PD.ι PD.t) 0]
    exact (PD.Fil 2).zero_mem
  exact PD.ι.toRingHom.domain_nontrivial

include PD in
theorem tmul_one_injective : Function.Injective fun c : LL => c ⊗ₜ[Qp] (1 : B) := by
  haveI := nontrivial_B' PD
  exact Algebra.TensorProduct.includeLeft_injective (S := Qp) (A := LL) (B := B)
    (algebraMap Qp B).injective

omit [Algebra K₀ B] [IsScalarTower Qp K₀ B] in
theorem tmul_one_sub_add (u v w : LL) :
    (u - v + w) ⊗ₜ[Qp] (1 : B) = u ⊗ₜ[Qp] (1 : B) - v ⊗ₜ[Qp] (1 : B) + w ⊗ₜ[Qp] (1 : B) := by
  rw [add_tmul, sub_tmul]

end PD

section Char

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

def charGRep (χ : G →* LLˣ) (hχ : Continuous fun g => ((χ g : LLˣ) : LL)) : GRep G Qp LL O where
  V := LL
  ρ := charRep χ
  cont x := by
    have : (fun g => charRep χ g x) = fun g => ((χ g : LLˣ) : LL) * x := by
      funext g; exact charRep_apply χ g x
    rw [this]
    exact hχ.mul continuous_const

end Char

set_option maxHeartbeats 1600000 in

theorem cob_of_cont (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL] (hO : GoodO (Qp := ℚ_[l]) LL O)
    (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (hdR : IsDR (P.PD K) A.ρ)
    (hD : IsDual1 (P.PD K) A.ρ A'.ρ m)
    (hχ : Continuous fun g => ((cycLL (P.PD K) LL g : LLˣ) : LL))
    (a : ↥(GK K) → A.V) (ha : a ∈ finiteCocycles (P.PD K) A.ρ) (b : ↥(GK K) → A'.V)
    (hb : b ∈ finiteCocycles (P.PD K) A'.ρ) : CobL (P.PD K) (cupL A'.ρ m a b) := by
  haveI : IsTopologicalRing LL := hO.2.2.2.1
  obtain ⟨x, hx⟩ := ha.2
  obtain ⟨y, hy⟩ := hb.2
  obtain ⟨hd1, d2, hd2, hd2'⟩ :=
    GlobalTheory.CobCrisLift.coboundary_lift l P AI hT K LL O hO A hdR a x hx
  obtain ⟨hsurj, hker⟩ := GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI hT K LL LL
  obtain ⟨w1, w2, hw2, hw1φ, hw1ι⟩ :=
    hsurj (pairT P.R.B m (x - φVB (P.PD K) (LL := LL) (V := A.V) x) y)
      (pairT P.R.BdR m d2 (ιV (P.PD K) (LL := LL) (V := A'.V) y))
  have hfix1 : ∀ g, actVB (P.PD K) A.ρ g (x - φVB (P.PD K) (LL := LL) (V := A.V) x) =
      x - φVB (P.PD K) (LL := LL) (V := A.V) x := fun g => by
    have := (Submodule.mem_iInf _).1 hd1 g
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
  have hfix2 : ∀ g, actVdR (P.PD K) A.ρ g d2 = d2 := fun g => by
    have := (Submodule.mem_iInf _).1 hd2 g
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
  let F : ↥(GK K) → LL ⊗[ℚ_[l]] P.R.B := fun h =>
    pairT P.R.B m x (b h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) -
      (actVB (P.PD K) (charRep (cycLL (P.PD K) LL)) h w1 - w1)
  have hFφ : ∀ h, φVB (P.PD K) (LL := LL) (V := LL) (F h) = F h := fun h => by
    have e1 : φVB (P.PD K) (LL := LL) (V := A'.V) (b h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
        b h ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
      simp [φVB]
    have e2 : pairT P.R.B m (x - φVB (P.PD K) (LL := LL) (V := A.V) x) (b h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
        actVB (P.PD K) (charRep (cycLL (P.PD K) LL)) h
          (pairT P.R.B m (x - φVB (P.PD K) (LL := LL) (V := A.V) x) y) -
          pairT P.R.B m (x - φVB (P.PD K) (LL := LL) (V := A.V) x) y := by
      rw [hy h, map_sub, ← pairT_actVB (P.PD K) A.ρ A'.ρ m hD.1 h _ y, hfix1 h]
    have s1 : F h - φVB (P.PD K) (LL := LL) (V := LL) (F h) =
        (pairT P.R.B m x (b h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) -
          pairT P.R.B m (φVB (P.PD K) (LL := LL) (V := A.V) x) (b h ⊗ₜ[ℚ_[l]] (1 : P.R.B))) -
        (actVB (P.PD K) (charRep (cycLL (P.PD K) LL)) h
          (w1 - φVB (P.PD K) (LL := LL) (V := LL) w1) -
          (w1 - φVB (P.PD K) (LL := LL) (V := LL) w1)) := by
      simp only [F, map_sub, pairT_φVB, e1, GlobalTheory.CobCrisLift.φVB_act]
      abel
    rw [eq_comm, ← sub_eq_zero, s1, hw1φ, ← LinearMap.sub_apply, ← map_sub, e2, sub_self]

  have hFι : ∀ h, ιV (P.PD K) (LL := LL) (V := LL) (F h) ∈ FilV (P.PD K) (LL := LL) (V := LL) 0 := fun h => by
    have e1 : ιV (P.PD K) (LL := LL) (V := A'.V) (b h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
        b h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
      simp [ιV]
    have e1' : b h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) A'.ρ h (ιV (P.PD K) (LL := LL) (V := A'.V) y) -
        ιV (P.PD K) (LL := LL) (V := A'.V) y := by
      rw [← e1, hy h, map_sub, GlobalTheory.CobCrisLift.ιV_act]
    have e2 : pairT P.R.BdR m d2 (b h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) =
        actVdR (P.PD K) (charRep (cycLL (P.PD K) LL)) h
          (pairT P.R.BdR m d2 (ιV (P.PD K) (LL := LL) (V := A'.V) y)) -
          pairT P.R.BdR m d2 (ιV (P.PD K) (LL := LL) (V := A'.V) y) := by
      rw [e1', map_sub, ← pairT_actVdR (P.PD K) A.ρ A'.ρ m hD.1 h d2 _, hfix2 h]
    have hι1 : ιV (P.PD K) (LL := LL) (V := LL) w1 =
        pairT P.R.BdR m d2 (ιV (P.PD K) (LL := LL) (V := A'.V) y) + w2 := sub_eq_iff_eq_add.1 hw1ι
    have s1 : ιV (P.PD K) (LL := LL) (V := LL) (F h) =
        pairT P.R.BdR m (ιV (P.PD K) (LL := LL) (V := A.V) x - d2) (b h ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) -
          (actVdR (P.PD K) (charRep (cycLL (P.PD K) LL)) h w2 - w2) := by
      simp only [F, map_sub, pairT_ιV, e1, GlobalTheory.CobCrisLift.ιV_act, hι1, map_add, LinearMap.sub_apply, e2]
      abel
    rw [s1]
    exact sub_mem (pairT_filV (P.PD K) m 0 _ hd2' (b h))
      (sub_mem (actVdR_filV (P.PD K) _ 0 h w2 hw2) hw2)
  have hF : ∀ h, ∃ c : LL, F h = c ⊗ₜ[ℚ_[l]] (1 : P.R.B) := fun h => hker (F h) (hFφ h) (hFι h)
  choose f hf using hF
  let bas := Module.finBasis LL A'.V
  let β : Fin (finrank LL A'.V) → ↥(GK K) → LL := fun i g => bas.coord i (b g)
  have hβ : ∀ i, Continuous (β i) := fun i =>
    (IsModuleTopology.continuous_of_linearMap (bas.coord i)).comp hb.1.1

  have hsum : ∀ g, f g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = ∑ i, β i g • pairT P.R.B m x (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B)) +
      (actVB (P.PD K) (charRep (cycLL (P.PD K) LL)) g (-w1) - -w1) := by
    intro g
    have eb : b g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = ∑ i, β i g • (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B)) := by
      conv_lhs => rw [← bas.sum_repr (b g)]
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.smul_tmul']
      rfl
    rw [← hf g]
    simp only [F, eb, map_sum, pairT_smul_right, map_neg]
    abel
  have hcont : Continuous f :=
    GlobalTheory.FundCont.contCore_tied l P AI hT K LL O hO
      (charGRep (Qp := ℚ_[l]) (O := O) (cycLL (P.PD K) LL) hχ) _
      (fun i => pairT P.R.B m x (bas i ⊗ₜ[ℚ_[l]] (1 : P.R.B))) β hβ (-w1) f hsum
  refine ⟨f, hcont, ?_⟩
  funext ⟨g, h⟩
  have hcup : cupL A'.ρ m a b (g, h) = m (a g) (A'.ρ g (b h)) := rfl
  rw [hcup]
  apply tmul_one_injective (P.PD K) (LL := LL)
  beta_reduce
  have hd : ReciprocityTheory.Def.d1 (charRep (cycLL (P.PD K) LL)) f (g, h) =
      charRep (cycLL (P.PD K) LL) g (f h) - f (g * h) + f g := rfl
  have hact : (charRep (cycLL (P.PD K) LL) g (f h)) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      actVB (P.PD K) (charRep (cycLL (P.PD K) LL)) g (f h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) := by
    rw [actVB_tmul, map_one]
  have hbh : actVB (P.PD K) A'.ρ g (b h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) = A'.ρ g (b h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    rw [actVB_tmul, map_one]
  have hcoc : b (g * h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      b g ⊗ₜ[ℚ_[l]] (1 : P.R.B) + A'.ρ g (b h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
    rw [hb.1.2 g h, add_tmul]
  have hrhs : (m (a g) (A'.ρ g (b h))) ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      pairT P.R.B m (actVB (P.PD K) A.ρ g x) (actVB (P.PD K) A'.ρ g (b h ⊗ₜ[ℚ_[l]] (1 : P.R.B))) -
        pairT P.R.B m x (A'.ρ g (b h) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) := by
    rw [hbh, ← LinearMap.sub_apply, ← map_sub, ← hx g, pairT_tmul, mul_one]
  have main : actVB (P.PD K) (charRep (cycLL (P.PD K) LL)) g (F h) - F (g * h) + F g =
      pairT P.R.B m (actVB (P.PD K) A.ρ g x) (actVB (P.PD K) A'.ρ g (b h ⊗ₜ[ℚ_[l]] (1 : P.R.B))) -
        pairT P.R.B m x (A'.ρ g (b h) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) := by
    simp only [F, map_sub, actVB_mul, hcoc, map_add,
      ← pairT_actVB (P.PD K) A.ρ A'.ρ m hD.1 g]
    abel
  calc (ReciprocityTheory.Def.d1 (charRep (cycLL (P.PD K) LL)) f (g, h)) ⊗ₜ[ℚ_[l]] (1 : P.R.B)
      = actVB (P.PD K) (charRep (cycLL (P.PD K) LL)) g (f h ⊗ₜ[ℚ_[l]] (1 : P.R.B)) -
          f (g * h) ⊗ₜ[ℚ_[l]] (1 : P.R.B) + f g ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
        rw [hd, tmul_one_sub_add, hact]
    _ = actVB (P.PD K) (charRep (cycLL (P.PD K) LL)) g (F h) - F (g * h) + F g := by
        rw [hf h, hf (g * h), hf g]
    _ = _ := main
    _ = _ := hrhs.symm

theorem bk_orth : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR (P.PD K) A.ρ → IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ a ∈ finiteCocycles (P.PD K) A.ρ, ∀ b ∈ finiteCocycles (P.PD K) A'.ρ, CobL (P.PD K) (cupL A'.ρ m a b) := by
  intro l _ P AI hT K LL _ _ _ O _ _ hO A A' m hdR hD a ha b hb
  haveI : IsTopologicalRing LL := hO.2.2.2.1
  by_cases hV : ∃ v : A.V, v ≠ 0
  · obtain ⟨v, hv⟩ := hV
    obtain ⟨v', hv'⟩ : ∃ v', m v v' ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv (hD.2.1 v h)
    have hm : Continuous fun p : A.V × A'.V => m p.1 p.2 :=
      IsModuleTopology.continuous_bilinear_of_finite_left m
    have hχ : Continuous fun g => ((cycLL (P.PD K) LL g : LLˣ) : LL) := by
      have e : (fun g => ((cycLL (P.PD K) LL g : LLˣ) : LL)) =
          fun g => m (A.ρ g v) (A'.ρ g v') * (m v v')⁻¹ := by
        funext g
        rw [hD.1, mul_assoc, mul_inv_cancel₀ hv', mul_one]
      rw [e]
      exact (hm.comp ((A.cont v).prodMk (A'.cont v'))).mul continuous_const
    exact cob_of_cont l P AI hT K LL O hO A A' m hdR hD hχ a ha b hb
  · push_neg at hV
    refine ⟨0, continuous_const, funext fun x => ?_⟩
    simp [cupL, hV (a x.1), ReciprocityTheory.Def.d1]

end GlobalTheory.BKOrth
