import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TwistDR

theorem exists_unit_of_span {k F R : Type} [Field k] [Infinite k] [Field F] [CommRing R] [Algebra F R]
    [Module k R] [Module.Finite F R] (hk : ∀ (c : k) (x : R), ∃ r : R, c • x = r * x)
    (U : Submodule k R) (hU : Submodule.span F (U : Set R) = ⊤) : ∃ d ∈ U, IsUnit d := by
  classical
  haveI : IsArtinianRing R := IsArtinianRing.of_finite F R
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  let S : MaximalSpectrum R → Submodule k U := fun m =>
    { carrier := {x | (x : R) ∈ m.asIdeal}
      add_mem' := fun ha hb => m.asIdeal.add_mem ha hb
      zero_mem' := m.asIdeal.zero_mem
      smul_mem' := fun c x hx => by
        obtain ⟨r, hr⟩ := hk c x
        change c • (x : R) ∈ m.asIdeal
        rw [hr]
        exact m.asIdeal.mul_mem_left r hx }
  have hS : ⊤ ∉ Finset.univ.image S := by
    intro h
    obtain ⟨m, -, hm⟩ := Finset.mem_image.1 h
    apply m.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : Submodule.span F (U : Set R) ≤ m.asIdeal.restrictScalars F :=
      Submodule.span_le.2 fun x hx => (hm ▸ Submodule.mem_top : (⟨x, hx⟩ : U) ∈ S m)
    exact h1 (hU ▸ Submodule.mem_top)
  have h2 := Subspace.biUnion_ne_univ_of_top_notMem hS
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).1 h2
  refine ⟨x, x.2, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hn
  apply hx
  exact Set.mem_biUnion (x := S ⟨m, hm⟩) (by simp) hxm

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem mem_DdR (ρ : Representation LL G V) (x : V ⊗[Qp] BdR) :
    x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := by
  simp [DdR, sub_eq_zero]

def tw (χ : G → LL) (g : G) : BdR ⊗[Qp] LL →ₗ[Qp] BdR ⊗[Qp] LL :=
  TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) (LinearMap.mulLeft Qp (χ g))

theorem tw_tmul (χ : G → LL) (g : G) (b : BdR) (c : LL) :
    tw PD χ g (b ⊗ₜ[Qp] c) = PD.actdR g b ⊗ₜ[Qp] (χ g * c) := rfl

theorem tw_smul (χ : G → LL) (g : G) (b : BdR) (w : BdR ⊗[Qp] LL) :
    tw PD χ g (b • w) = PD.actdR g b • tw PD χ g w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [tw_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

def twInv (χ : G → LL) : Submodule K (BdR ⊗[Qp] LL) where
  carrier := {x | ∀ g, tw PD χ g x = x}
  add_mem' ha hb g := by rw [map_add, ha g, hb g]
  zero_mem' g := map_zero _
  smul_mem' c x hx g := by
    rw [← algebraMap_smul BdR c x, tw_smul, AlgEquiv.commutes, hx g]

theorem finrank_twInv [FiniteDimensional Qp LL] (ν : Representation LL G (Fin 1 → LL)) (χ : G → LL)
    (hν : ∀ g x, ν g x = χ g • x) (h : finrank LL ↥(DdR PD ν) = finrank Qp K * finrank LL (Fin 1 → LL)) :
    finrank K ↥(twInv PD χ) = finrank Qp LL := by
  haveI := PD.finK
  let e : (Fin 1 → LL) ⊗[Qp] BdR ≃ₗ[Qp] BdR ⊗[Qp] LL :=
    ((LinearEquiv.funUnique (Fin 1) Qp LL).rTensor BdR).trans (TensorProduct.comm Qp LL BdR)
  have he : ∀ g x, e (actVdR PD ν g x) = tw PD χ g (e x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [e, actVdR, tw_tmul, hν]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hm : ((DdR PD ν).restrictScalars Qp).map (e : _ →ₗ[Qp] _) = (twInv PD χ).restrictScalars Qp := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Submodule.restrictScalars_mem, mem_DdR]
    refine forall_congr' fun g => ?_
    rw [← he, e.injective.eq_iff]
  have h1 : finrank Qp ↥(twInv PD χ) = finrank Qp ↥(DdR PD ν) := by
    have := LinearEquiv.finrank_map_eq e ((DdR PD ν).restrictScalars Qp)
    rw [hm] at this
    exact this
  rw [← Module.finrank_mul_finrank Qp K ↥(twInv PD χ), ← Module.finrank_mul_finrank Qp LL ↥(DdR PD ν), h,
    finrank_fintype_fun_eq_card, Fintype.card_fin, mul_one, mul_comm (finrank Qp LL)] at h1
  exact Nat.eq_of_mul_eq_mul_left finrank_pos h1

theorem exists_unit [Infinite Qp] [FiniteDimensional Qp LL] (hB : IsField BdR) (χ : G → LL)
    (h : finrank K ↥(twInv PD χ) = finrank Qp LL) : ∃ d ∈ twInv PD χ, IsUnit d := by
  letI : Field BdR := hB.toField
  haveI : Infinite K := Infinite.of_injective _ (algebraMap Qp K).injective
  have hpos : 0 < finrank Qp LL := finrank_pos
  haveI : Module.Finite K ↥(twInv PD χ) := Module.finite_of_finrank_pos (h ▸ hpos)
  refine exists_unit_of_span (F := BdR) (fun c x => ⟨algebraMap K _ c, Algebra.smul_def c x⟩) _ ?_
  let v := Module.finBasisOfFinrankEq K _ h
  have h1 : LinearIndependent K fun i => (v i : BdR ⊗[Qp] LL) :=
    v.linearIndependent.map' (twInv PD χ).subtype (twInv PD χ).ker_subtype
  have h2 : LinearIndependent BdR fun i => (v i : BdR ⊗[Qp] LL) := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    refine GlobalTheory.RegularRing.linearIndepOn_of_invariant (fun g b => PD.actdR g b)
      (fun g => (tw PD χ g).toAddMonoidHom) (tw_smul PD χ) ?_ _ (fun g i => (v i).2 g) s
      (h1.linearIndepOn _)
    intro b b' hb hg
    obtain ⟨c, hc⟩ := PD.invdR (b' / b) fun g => by
      have h3 : PD.actdR g b ≠ 0 := (map_ne_zero _).2 hb
      rw [map_div₀, div_eq_div_iff h3 hb]
      linear_combination hg g
    exact ⟨c, by rw [hc, div_mul_cancel₀ _ hb]⟩
  haveI : Nonempty (Fin (finrank Qp LL)) := ⟨⟨0, hpos⟩⟩
  rw [eq_top_iff, ← h2.span_eq_top_of_card_eq_finrank (by simp)]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact (v i).2

variable (V) in

def mulR : BdR ⊗[Qp] LL →ₗ[Qp] (V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR) :=
  TensorProduct.lift (LinearMap.mk₂ Qp
    (fun b c => c • AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b))
    (fun b b' c => by ext; simp [add_mul, tmul_add])
    (fun q b c => by ext; simp [smul_comm q c])
    (fun b c c' => add_smul _ _ _)
    (fun q b c => smul_assoc _ _ _))

theorem mulR_tmul (b : BdR) (c : LL) (v : V) (b' : BdR) :
    mulR V (b ⊗ₜ[Qp] c) (v ⊗ₜ[Qp] b') = (c • v) ⊗ₜ[Qp] (b * b') := by
  simp [mulR, smul_tmul']

theorem mulR_one (x : V ⊗[Qp] BdR) : mulR V (1 : BdR ⊗[Qp] LL) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rw [Algebra.TensorProduct.one_def, mulR_tmul, one_smul, one_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mulR_mul (d d' : BdR ⊗[Qp] LL) (x : V ⊗[Qp] BdR) :
    mulR V (d * d') x = mulR V d (mulR V d' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b =>
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [add_mul, map_add, LinearMap.add_apply, hx, hy]
    | tmul b₁ c₁ =>
      induction d' using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [mul_add, map_add, LinearMap.add_apply, hx, hy]
      | tmul b₂ c₂ => simp only [Algebra.TensorProduct.tmul_mul_tmul, mulR_tmul, mul_smul, mul_assoc]

theorem act_mulR (ρ ρ' : Representation LL G V) (χ : G → LL) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (g : G) (d : BdR ⊗[Qp] LL) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ' g (mulR V d x) = mulR V (tw PD χ g d) (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b =>
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul b₁ c₁ => simp [mulR_tmul, tw_tmul, actVdR, hρ, mul_smul]

theorem finrank_DdR_twist [Infinite Qp] [FiniteDimensional Qp LL] (hB : IsField BdR)
    (ρ ρ' : Representation LL G V) (ν : Representation LL G (Fin 1 → LL)) (χ : G → LL)
    (hν : ∀ g x, ν g x = χ g • x) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (h : finrank LL ↥(DdR PD ν) = finrank Qp K * finrank LL (Fin 1 → LL)) :
    finrank LL ↥(DdR PD ρ') = finrank LL ↥(DdR PD ρ) := by
  obtain ⟨_, hd, d, rfl⟩ := exists_unit PD hB χ (finrank_twInv PD ν χ hν h)
  let e : V ⊗[Qp] BdR ≃ₗ[LL] V ⊗[Qp] BdR := LinearEquiv.ofLinear (mulR V d.1) (mulR V d⁻¹.1)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← mulR_mul, Units.mul_inv, mulR_one, LinearMap.id_apply])
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← mulR_mul, Units.inv_mul, mulR_one, LinearMap.id_apply])
  have he : ∀ g x, actVdR PD ρ' g (e x) = e (actVdR PD ρ g x) := fun g x => by
    change actVdR PD ρ' g (mulR V d.1 x) = mulR V d.1 _
    rw [act_mulR PD ρ ρ' χ hρ, hd g]
  have hm : (DdR PD ρ).map (e : _ →ₗ[LL] _) = DdR PD ρ' := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_DdR, mem_DdR]
    refine forall_congr' fun g => ?_
    rw [he, e.injective.eq_iff]
  rw [← hm, LinearEquiv.finrank_map_eq]

end Generic

theorem isDR_twist_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (ν : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ : ↥(GK K) → ↥LL.1), (∀ g x, ν g x = χ g • x) → (∀ g x, ρ' g x = χ g • ρ g x) → IsDR (P.PD K) ν → (IsDR (P.PD K) ρ ↔ IsDR (P.PD K) ρ') := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ ρ' ν χ hν hρ h
  haveI := LL.2
  unfold IsDR
  rw [finrank_DdR_twist (P.PD K) (GlobalTheory.RegularRing.isField_of_tied T) ρ ρ' ν χ hν hρ h]

end GlobalTheory.TwistDR
