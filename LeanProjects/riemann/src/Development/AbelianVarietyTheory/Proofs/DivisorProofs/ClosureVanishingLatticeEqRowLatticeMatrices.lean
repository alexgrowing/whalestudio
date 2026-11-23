import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqActStdLat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralHilbert90FiniteIdelesTrivialWhereTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupported

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.VacShapeCl

open Filter Topology

section Core

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def prods {m n : ℕ} (X : Set (Fin m → k)) (Y : Set (Fin n → k)) : Set (Matrix (Fin m) (Fin n) k) :=
  {Z | ∃ x ∈ X, ∃ y ∈ Y, Z = vecMulVec x y}

theorem prod_mem_span {m n : ℕ} {X : Set (Fin m → k)} {Y : Set (Fin n → k)} {x : Fin m → k} {y : Fin n → k}
    (hx : x ∈ Submodule.span 𝒪[k] X) (hy : y ∈ Submodule.span 𝒪[k] Y) :
    vecMulVec x y ∈ Submodule.span 𝒪[k] (prods X Y) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
    | zero =>
      have : vecMulVec x (0 : Fin n → k) = 0 := by ext i j; simp [vecMulVec_apply]
      rw [this]; exact zero_mem _
    | add y y' _ _ h h' =>
      have : vecMulVec x (y + y') = vecMulVec x y + vecMulVec x y' := by ext i j; simp [vecMulVec_apply, mul_add]
      rw [this]; exact add_mem h h'
    | smul c y _ h =>
      have : vecMulVec x (c • y) = c • vecMulVec x y := by
        ext i j; simp [vecMulVec_apply, Submonoid.smul_def, smul_eq_mul]
      rw [this]; exact Submodule.smul_mem _ c h
  | zero =>
    have : vecMulVec (0 : Fin m → k) y = 0 := by ext i j; simp [vecMulVec_apply]
    rw [this]; exact zero_mem _
  | add x x' _ _ h h' =>
    have : vecMulVec (x + x') y = vecMulVec x y + vecMulVec x' y := by ext i j; simp [vecMulVec_apply, add_mul]
    rw [this]; exact add_mem h h'
  | smul c x _ h =>
    have : vecMulVec (c • x) y = c • vecMulVec x y := by
      ext i j; simp [vecMulVec_apply, Submonoid.smul_def, smul_eq_mul]
    rw [this]; exact Submodule.smul_mem _ c h

theorem exists_ne_zero_of_mem_nhds {U : Set k} (hU : U ∈ 𝓝 (0 : k)) : ∃ t ∈ U, t ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨t, ht, hto, h0t⟩ := mem_nhds_iff.1 hU
  have e : t = {0} := Set.Subset.antisymm (fun s hs => h s (ht hs)) (Set.singleton_subset_iff.2 h0t)
  haveI : DiscreteTopology k := discreteTopology_of_isOpen_singleton_zero (e ▸ hto)
  have hfin : (𝒪[k] : Set k).Finite := (GlobalTheory.SplitWeil.Model.isCompact_int (k := k)).finite_of_discrete
  haveI : Finite 𝒪[k] := hfin.to_subtype
  exact IsDiscreteValuationRing.not_isField 𝒪[k] (Finite.isField_of_domain 𝒪[k])

theorem exists_bound {m n : ℕ} {C : Set (Matrix (Fin m) (Fin n) k)} (hC : IsCompact C) :
    ∃ c : 𝒪[k], c ≠ 0 ∧ ∀ Z ∈ C, ∀ i j, (c : k) * Z i j ∈ 𝒪[k] := by
  haveI : Nonempty {c : 𝒪[k] // c ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  have hO : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer (v := valuation k)

  have hd : ∀ x : k, ∃ d : 𝒪[k], d ≠ 0 ∧ (d : k) * x ∈ 𝒪[k] := by
    intro x
    by_cases hx : x ∈ 𝒪[k]
    · exact ⟨1, one_ne_zero, by simpa using hx⟩
    · have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ zero_mem _)
      have hlt : 1 < valuation k x := lt_of_not_ge hx
      have hinv : x⁻¹ ∈ 𝒪[k] := by
        change valuation k x⁻¹ ≤ 1
        rw [map_inv₀]; exact (inv_lt_one_of_one_lt₀ hlt).le
      refine ⟨⟨x⁻¹, hinv⟩, fun h0 => inv_ne_zero hx0 (congrArg Subtype.val h0), ?_⟩
      change x⁻¹ * x ∈ 𝒪[k]
      rw [inv_mul_cancel₀ hx0]; exact one_mem _
  choose d hd0 hdx using hd
  obtain ⟨⟨c, hc⟩, h⟩ := hC.elim_directed_cover
    (fun c : {c : 𝒪[k] // c ≠ 0} => {Z : Matrix (Fin m) (Fin n) k | ∀ i j, (c.1 : k) * Z i j ∈ 𝒪[k]})
    (fun c => by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        IsOpen.preimage (f := fun Z : Matrix (Fin m) (Fin n) k => (c.1 : k) * Z i j) (by fun_prop) hO)
    (fun Z _ => by
      refine Set.mem_iUnion.2 ⟨⟨∏ i, ∏ j, d (Z i j), Finset.prod_ne_zero_iff.2 fun i _ =>
        Finset.prod_ne_zero_iff.2 fun j _ => hd0 _⟩, fun i j => ?_⟩
      obtain ⟨r, hr⟩ : d (Z i j) ∣ ∏ i, ∏ j, d (Z i j) :=
        (Finset.dvd_prod_of_mem (fun j => d (Z i j)) (Finset.mem_univ j)).trans
          (Finset.dvd_prod_of_mem (fun i => ∏ j, d (Z i j)) (Finset.mem_univ i))
      change ((∏ i, ∏ j, d (Z i j) : 𝒪[k]) : k) * Z i j ∈ 𝒪[k]
      rw [hr, Subring.coe_mul, mul_comm ((d (Z i j) : k)), mul_assoc]
      exact mul_mem r.2 (hdx _))
    (fun a b => ⟨⟨a.1 * b.1, mul_ne_zero a.2 b.2⟩, fun Z hZ i j => by
        change ((a.1 * b.1 : 𝒪[k]) : k) * Z i j ∈ 𝒪[k]
        rw [Subring.coe_mul, mul_comm (a.1 : k), mul_assoc]
        exact mul_mem b.1.2 (hZ i j),
      fun Z hZ i j => by
        change ((a.1 * b.1 : 𝒪[k]) : k) * Z i j ∈ 𝒪[k]
        rw [Subring.coe_mul, mul_assoc]
        exact mul_mem a.1.2 (hZ i j)⟩)
  exact ⟨c, hc, fun Z hZ => h hZ⟩

theorem fg_of_bound {m : ℕ} (M : Submodule 𝒪[k] (Fin m → k)) (d : k) (hd : d ≠ 0)
    (h : ∀ x ∈ M, ∀ i, d * x i ∈ 𝒪[k]) : M.FG := by
  let φ : (Fin m → 𝒪[k]) →ₗ[𝒪[k]] (Fin m → k) :=
    { toFun := fun a i => d⁻¹ * (a i : k)
      map_add' := fun a b => by funext i; simp [mul_add]
      map_smul' := fun c a => by funext i; first | (simp [Subring.smul_def, smul_eq_mul]; ring) | simp [Subring.smul_def, smul_eq_mul, mul_left_comm] }
  have hle : M ≤ LinearMap.range φ := fun x hx =>
    ⟨fun i => ⟨d * x i, h x hx i⟩, by funext i; simp [φ, inv_mul_cancel_left₀ hd]⟩
  rw [← Submodule.map_comap_eq_self hle]
  exact (IsNoetherian.noetherian _).map φ

end Core

section Core2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_act_std {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι k) (x : ι → k) :
    x ∈ GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.act g (GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms.stdLat k ι) ↔ ∀ i, ((g⁻¹).val *ᵥ x) i ∈ 𝒪[k] := by
  constructor
  · rintro ⟨w, hw, rfl⟩ i
    have e : (g⁻¹).val *ᵥ (((Matrix.mulVecLin g.val).restrictScalars 𝒪[k]) w) = w := by
      simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.inv_mul,
        Matrix.one_mulVec]
    rw [e]
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 ((Submodule.mem_pi.1 hw) i (Set.mem_univ i))
    rw [← hy]; exact y.2
  · intro h
    refine ⟨(g⁻¹).val *ᵥ x, Submodule.mem_pi.2 fun i _ => Submodule.mem_one.2 ⟨⟨_, h i⟩, rfl⟩, ?_⟩
    simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv,
      Matrix.one_mulVec]

theorem span_eq_top_left {m n : ℕ} (hn : 0 < n) {X : Set (Fin m → k)} {Y : Set (Fin n → k)}
    (ho : IsOpen (closure (Submodule.span 𝒪[k] (prods X Y) : Set (Matrix (Fin m) (Fin n) k)))) :
    Submodule.span k X = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  set ℓ : Fin m → k := fun i => f fun j => if i = j then 1 else 0 with hℓ
  have hfx : ∀ x, f x = ∑ i, x i * ℓ i := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ f x]; simp [hℓ, smul_eq_mul]
  have hX : ∀ x ∈ X, ∑ i, x i * ℓ i = 0 := fun x hx => by
    rw [← hfx]
    have : f x ∈ (Submodule.span k X).map f := Submodule.mem_map_of_mem (Submodule.subset_span hx)
    rw [hf] at this
    exact (Submodule.mem_bot k).1 this
  let H : Submodule 𝒪[k] (Matrix (Fin m) (Fin n) k) :=
    { carrier := {Z | ∀ j, ∑ i, Z i j * ℓ i = 0}
      add_mem' := fun {A B} hA hB j => by
        simp only [Set.mem_setOf_eq, Matrix.add_apply, add_mul, Finset.sum_add_distrib, hA j, hB j, add_zero]
      zero_mem' := fun j => by simp
      smul_mem' := fun c A hA j => by
        have := hA j
        simp only [Matrix.smul_apply, Subring.smul_def, smul_eq_mul, mul_assoc, ← Finset.mul_sum, this, mul_zero] }
  have hsub : Submodule.span 𝒪[k] (prods X Y) ≤ H := Submodule.span_le.2 (by
    rintro _ ⟨x, hx, y, hy, rfl⟩ j
    show ∑ i, vecMulVec x y i j * ℓ i = 0
    simp only [vecMulVec_apply]
    have : ∑ i, x i * y j * ℓ i = y j * ∑ i, x i * ℓ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hX x hx, mul_zero])
  have hHc : IsClosed (H : Set (Matrix (Fin m) (Fin n) k)) := by
    show IsClosed {Z : Matrix (Fin m) (Fin n) k | ∀ j, ∑ i, Z i j * ℓ i = 0}
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_eq (by fun_prop) continuous_const
  have hcl : closure (Submodule.span 𝒪[k] (prods X Y) : Set (Matrix (Fin m) (Fin n) k)) ⊆ (H : Set (Matrix (Fin m) (Fin n) k)) := closure_minimal (fun Z hZ => hsub hZ) hHc
  have hℓ0 : ∀ i, ℓ i = 0 := by
    intro i₀
    let j₀ : Fin n := ⟨0, hn⟩
    let φ : k → Matrix (Fin m) (Fin n) k := fun t => Matrix.of fun i j => if i = i₀ ∧ j = j₀ then t else 0
    have hφ : Continuous φ := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      by_cases h : i = i₀ ∧ j = j₀
      · simp only [φ, Matrix.of_apply, if_pos h]; exact continuous_id
      · simp only [φ, Matrix.of_apply, if_neg h]; exact continuous_const
    have h0 : φ 0 ∈ closure (Submodule.span 𝒪[k] (prods X Y) : Set (Matrix (Fin m) (Fin n) k)) := by
      have : φ 0 = 0 := by ext i j; simp [φ]
      rw [this]; exact subset_closure (zero_mem _)
    obtain ⟨t, ht, ht0⟩ := exists_ne_zero_of_mem_nhds (hφ.continuousAt.preimage_mem_nhds (ho.mem_nhds h0))
    have := hcl ht j₀
    simpa [φ, ht0] using this
  apply hf0
  refine LinearMap.ext fun x => ?_
  rw [hfx]
  simp [hℓ0]

theorem span_eq_top_right {m n : ℕ} (hm : 0 < m) {X : Set (Fin m → k)} {Y : Set (Fin n → k)}
    (ho : IsOpen (closure (Submodule.span 𝒪[k] (prods X Y) : Set (Matrix (Fin m) (Fin n) k)))) :
    Submodule.span k Y = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  set ℓ : Fin n → k := fun i => f fun j => if i = j then 1 else 0 with hℓ
  have hfx : ∀ y, f y = ∑ j, y j * ℓ j := fun y => by
    rw [LinearMap.pi_apply_eq_sum_univ f y]; simp [hℓ, smul_eq_mul]
  have hY : ∀ y ∈ Y, ∑ j, y j * ℓ j = 0 := fun y hy => by
    rw [← hfx]
    have : f y ∈ (Submodule.span k Y).map f := Submodule.mem_map_of_mem (Submodule.subset_span hy)
    rw [hf] at this
    exact (Submodule.mem_bot k).1 this
  let H : Submodule 𝒪[k] (Matrix (Fin m) (Fin n) k) :=
    { carrier := {Z | ∀ i, ∑ j, Z i j * ℓ j = 0}
      add_mem' := fun {A B} hA hB i => by
        simp only [Set.mem_setOf_eq, Matrix.add_apply, add_mul, Finset.sum_add_distrib, hA i, hB i, add_zero]
      zero_mem' := fun i => by simp
      smul_mem' := fun c A hA i => by
        have := hA i
        simp only [Matrix.smul_apply, Subring.smul_def, smul_eq_mul, mul_assoc, ← Finset.mul_sum, this, mul_zero] }
  have hsub : Submodule.span 𝒪[k] (prods X Y) ≤ H := Submodule.span_le.2 (by
    rintro _ ⟨x, hx, y, hy, rfl⟩ i
    show ∑ j, vecMulVec x y i j * ℓ j = 0
    simp only [vecMulVec_apply]
    have : ∑ j, x i * y j * ℓ j = x i * ∑ j, y j * ℓ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hY y hy, mul_zero])
  have hHc : IsClosed (H : Set (Matrix (Fin m) (Fin n) k)) := by
    show IsClosed {Z : Matrix (Fin m) (Fin n) k | ∀ i, ∑ j, Z i j * ℓ j = 0}
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const
  have hcl : closure (Submodule.span 𝒪[k] (prods X Y) : Set (Matrix (Fin m) (Fin n) k)) ⊆ (H : Set (Matrix (Fin m) (Fin n) k)) := closure_minimal (fun Z hZ => hsub hZ) hHc
  have hℓ0 : ∀ j, ℓ j = 0 := by
    intro j₀
    let i₀ : Fin m := ⟨0, hm⟩
    let φ : k → Matrix (Fin m) (Fin n) k := fun t => Matrix.of fun i j => if i = i₀ ∧ j = j₀ then t else 0
    have hφ : Continuous φ := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      by_cases h : i = i₀ ∧ j = j₀
      · simp only [φ, Matrix.of_apply, if_pos h]; exact continuous_id
      · simp only [φ, Matrix.of_apply, if_neg h]; exact continuous_const
    have h0 : φ 0 ∈ closure (Submodule.span 𝒪[k] (prods X Y) : Set (Matrix (Fin m) (Fin n) k)) := by
      have : φ 0 = 0 := by ext i j; simp [φ]
      rw [this]; exact subset_closure (zero_mem _)
    obtain ⟨t, ht, ht0⟩ := exists_ne_zero_of_mem_nhds (hφ.continuousAt.preimage_mem_nhds (ho.mem_nhds h0))
    have := hcl ht i₀
    simpa [φ, ht0] using this
  apply hf0
  refine LinearMap.ext fun y => ?_
  rw [hfx]
  simp [hℓ0]

end Core2

section Core3

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem closure_eq {m n : ℕ} (X : Set (Fin m → k)) (Y : Set (Fin n → k))
    (ho : IsOpen (closure (Submodule.span 𝒪[k] (prods X Y) : Set (Matrix (Fin m) (Fin n) k))))
    (hc : IsCompact (closure (Submodule.span 𝒪[k] (prods X Y) : Set (Matrix (Fin m) (Fin n) k)))) :
    ∃ (P : GL (Fin m) k) (Λ : Submodule 𝒪[k] (Fin n → k)), ∀ Z : Matrix (Fin m) (Fin n) k,
      Z ∈ closure (Submodule.span 𝒪[k] (prods X Y) : Set (Matrix (Fin m) (Fin n) k)) ↔
        P.val * Z ∈ GlobalTheory.SplitFlip.matLat (Fin m) Λ := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨1, ⊤, fun Z => ?_⟩
    have hZ : Z = 0 := by ext i; exact i.elim0
    exact iff_of_true (by rw [hZ]; exact subset_closure (zero_mem _))
      (GlobalTheory.SplitFlip.mem_matLat.2 fun _ => Submodule.mem_top)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, ⊤, fun Z => ?_⟩
    have hZ : Z = 0 := by ext i j; exact j.elim0
    exact iff_of_true (by rw [hZ]; exact subset_closure (zero_mem _))
      (GlobalTheory.SplitFlip.mem_matLat.2 fun _ => Submodule.mem_top)
  have h1 := span_eq_top_left hn ho
  have h2 := span_eq_top_right hm ho
  obtain ⟨c, hc0, hcb⟩ := exists_bound hc
  have hc0' : (c : k) ≠ 0 := fun h => hc0 (Subtype.ext h)
  obtain ⟨x₀, hx₀, i₀, hxi⟩ : ∃ x ∈ X, ∃ i, x i ≠ 0 := by
    by_contra hh
    push_neg at hh
    have hle : Submodule.span k X ≤ ⊥ := Submodule.span_le.2 fun x hx => by
      rw [SetLike.mem_coe, Submodule.mem_bot]; funext i; exact hh x hx i
    rw [h1] at hle
    have e := (Submodule.mem_bot k).1 (hle (Submodule.mem_top (x := fun _ : Fin m => (1 : k))))
    exact one_ne_zero (congrFun e ⟨0, hm⟩)
  obtain ⟨y₀, hy₀, j₀, hyj⟩ : ∃ y ∈ Y, ∃ j, y j ≠ 0 := by
    by_contra hh
    push_neg at hh
    have hle : Submodule.span k Y ≤ ⊥ := Submodule.span_le.2 fun y hy => by
      rw [SetLike.mem_coe, Submodule.mem_bot]; funext j; exact hh y hy j
    rw [h2] at hle
    have e := (Submodule.mem_bot k).1 (hle (Submodule.mem_top (x := fun _ : Fin n => (1 : k))))
    exact one_ne_zero (congrFun e ⟨0, hn⟩)
  have hb₁ : ∀ x ∈ Submodule.span 𝒪[k] X, ∀ i, ((c : k) * y₀ j₀) * x i ∈ 𝒪[k] := fun x hx i => by
    have := hcb _ (subset_closure (prod_mem_span hx (Submodule.subset_span hy₀))) i j₀
    rw [vecMulVec_apply] at this
    convert this using 1; ring
  have hb₂ : ∀ y ∈ Submodule.span 𝒪[k] Y, ∀ j, ((c : k) * x₀ i₀) * y j ∈ 𝒪[k] := fun y hy j => by
    have := hcb _ (subset_closure (prod_mem_span (Submodule.subset_span hx₀) hy)) i₀ j
    rw [vecMulVec_apply] at this
    convert this using 1; ring
  have hL₁ : Submodule.IsLattice k (Submodule.span 𝒪[k] X) :=
    ⟨fg_of_bound _ _ (mul_ne_zero hc0' hyj) hb₁, by rw [Submodule.span_span_of_tower]; exact h1⟩
  have hL₂ : Submodule.IsLattice k (Submodule.span 𝒪[k] Y) :=
    ⟨fg_of_bound _ _ (mul_ne_zero hc0' hxi) hb₂, by rw [Submodule.span_span_of_tower]; exact h2⟩
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.RootEx.UnfoldShape.exists_eq_act_stdLat k (Fin m) _ hL₁
  obtain ⟨Q₀, hQ₀⟩ := GlobalTheory.RootEx.UnfoldShape.exists_eq_act_stdLat k (Fin n) _ hL₂
  have mem₁ : ∀ x, x ∈ Submodule.span 𝒪[k] X ↔ ∀ i, ((P₀⁻¹).val *ᵥ x) i ∈ 𝒪[k] := fun x => by
    rw [hP₀]; exact mem_act_std P₀ x
  have mem₂ : ∀ y, y ∈ Submodule.span 𝒪[k] Y ↔ ∀ j, ((Q₀⁻¹).val *ᵥ y) j ∈ 𝒪[k] := fun y => by
    rw [hQ₀]; exact mem_act_std Q₀ y
  have key : ∀ Z, Z ∈ Submodule.span 𝒪[k] (prods X Y) ↔
      (P₀⁻¹).val * Z ∈ GlobalTheory.SplitFlip.matLat (Fin m) (Submodule.span 𝒪[k] Y) := by
    intro Z
    constructor
    · intro hZ
      let N : Submodule 𝒪[k] (Matrix (Fin m) (Fin n) k) :=
        { carrier := {W | (P₀⁻¹).val * W ∈ GlobalTheory.SplitFlip.matLat (Fin m) (Submodule.span 𝒪[k] Y)}
          add_mem' := fun {A B} hA hB => by
            simp only [Set.mem_setOf_eq, Matrix.mul_add]; exact add_mem hA hB
          zero_mem' := by simp only [Set.mem_setOf_eq, Matrix.mul_zero]; exact zero_mem _
          smul_mem' := fun c A hA => by
            simp only [Set.mem_setOf_eq, Matrix.mul_smul]; exact Submodule.smul_mem _ c hA }
      refine (Submodule.span_le.2 ?_ : Submodule.span 𝒪[k] (prods X Y) ≤ N) hZ
      rintro _ ⟨x, hx, y, hy, rfl⟩
      show (P₀⁻¹).val * vecMulVec x y ∈ GlobalTheory.SplitFlip.matLat (Fin m) (Submodule.span 𝒪[k] Y)
      rw [GlobalTheory.SplitFlip.mem_matLat]
      intro i
      have hxi := (mem₁ x).1 (Submodule.subset_span hx) i
      have e : ((P₀⁻¹).val * vecMulVec x y).row i = (⟨_, hxi⟩ : 𝒪[k]) • y := by
        funext j
        simp only [Matrix.row, Matrix.mul_apply, vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul,
          Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_assoc]
      rw [e]; exact Submodule.smul_mem _ _ (Submodule.subset_span hy)
    · intro hZ
      have e : Z = ∑ i, vecMulVec (fun a => P₀.val a i) (((P₀⁻¹).val * Z) i) := by
        have hPZ : P₀.val * ((P₀⁻¹).val * Z) = Z := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
        ext a b
        rw [Matrix.sum_apply]
        simp only [vecMulVec_apply]
        conv_lhs => rw [← hPZ]
        rw [Matrix.mul_apply]
      rw [e]
      refine Submodule.sum_mem _ fun i _ => prod_mem_span ((mem₁ _).2 fun j => ?_) (hZ i)
      have e2 : ((P₀⁻¹).val *ᵥ fun a => P₀.val a i) j = ((P₀⁻¹).val * P₀.val) j i := rfl
      rw [e2, Units.inv_mul, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  have hclosed : IsClosed (Submodule.span 𝒪[k] (prods X Y) : Set (Matrix (Fin m) (Fin n) k)) := by
    have e : (Submodule.span 𝒪[k] (prods X Y) : Set (Matrix (Fin m) (Fin n) k)) =
        {Z | ∀ i j, ((Q₀⁻¹).val *ᵥ ((P₀⁻¹).val * Z) i) j ∈ 𝒪[k]} := by
      ext Z
      rw [SetLike.mem_coe, key, GlobalTheory.SplitFlip.mem_matLat]
      exact forall_congr' fun i => mem₂ _
    rw [e]
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun j => IsClosed.preimage ?_
      (Valuation.isClosed_integer (v := valuation k))
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    fun_prop
  refine ⟨P₀⁻¹, Submodule.span 𝒪[k] Y, fun Z => ?_⟩
  rw [hclosed.closure_eq]
  exact key Z

end Core3

section Adelic

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (piW incM AE latAtV At)

theorem vecMulVec_map {R S G : Type} [CommRing R] [CommRing S] [FunLike G R S] [RingHomClass G R S] {p q : Type} (t : G)
    (x : p → R) (y : q → R) :
    (vecMulVec x y).map t = vecMulVec (fun i => t (x i)) (fun j => t (y j)) := by
  ext i j; simp [vecMulVec_apply, map_mul]

theorem vecMulVec_neg_left {R : Type} [CommRing R] {p q : Type} (x : p → R) (y : q → R) :
    vecMulVec (-x) y = -vecMulVec x y := by
  ext i j; simp [vecMulVec_apply]

theorem vecMulVec_neg_smul {R : Type} [CommRing R] {p q : Type} (c : R) (x : p → R) (y : q → R) :
    vecMulVec (-(c • x)) y = c • vecMulVec (-x) y := by
  ext i j; simp [vecMulVec_apply, mul_assoc]

theorem mul_vecMulVec_mul {R : Type} [CommRing R] {p q r s : Type} [Fintype q] [Fintype r] (A : Matrix p q R)
    (B : Matrix s r R) (x : q → R) (y : r → R) : A * vecMulVec x y * Bᵀ = vecMulVec (A *ᵥ x) (B *ᵥ y) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_int_iff {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (x : Fv F v) : x ∈ 𝒪[Fv F v] ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (Fv F v))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem piW_smul {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (a : AF F) (z : AE F E) :
    piW t (a • z) = evFin F v a * piW t z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]
  | tmul b e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    show evFin F v (a * b) * t e = evFin F v a * (evFin F v b * t e)
    rw [map_mul, mul_assoc]

theorem map_piW_smul {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (a : AF F) {p q : Type} (u : Matrix p q (AE F E)) :
    (a • u).map (piW t) = evFin F v a • u.map (piW t) := by
  ext i j; simp [piW_smul]

theorem map_piW_smul_incM {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (a : AF F) {p q : Type} (J : Matrix p q E) :
    (a • incM F J).map (piW t) = evFin F v a • J.map t := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, incM, GlobalTheory.VacIndic.smul_inclR_eq, smul_eq_mul]
  rfl

end Adelic

section Shape

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (piW incM AE latAtV At)

theorem isConjOf_sig (D : D7) : Formalism.L2.DIV.IsConjOf D.sp.cm.sig := by
  refine ⟨fun h0 => ?_, fun e => star_star e, fun e he => ?_⟩
  · have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun e =>
      (D.sp.cm.fixed e).1 (AlgHom.congr_fun h0 e)
    have h1 : Module.finrank D.host.F D.host.E = 1 :=
      (LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
        ⟨(algebraMap D.host.F D.host.E).injective, hs⟩)).symm.trans (Module.finrank_self _)
    have := D.sp.cm.deg2
    omega
  · exact (D.sp.cm.fixed e).1 he

theorem exists_unit_diff {D : D7} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (hU : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E)) :
    ∃ (b : 𝓞 D.host.E) (α : Fv D.host.F v), α ∈ v.adicCompletionIntegers D.host.F ∧
      α * (τ (D.sp.cm.sig (b : D.host.E)) - τ (b : D.host.E)) = 1 := by
  haveI := hU
  obtain ⟨b, hb⟩ := GlobalTheory.TwU.IntegralHilbert90Unramified.exists_sub_sig_notMem D.sp.cm.sig (isConjOf_sig D) (splitPrime τ)
  rw [mem_splitPrime] at hb
  have hle := apply_coe_mem τ (b - RingOfIntegers.mapAlgHom D.sp.cm.sig b)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hle
  have h1 := le_antisymm hle (not_lt.1 hb)
  have e : ((b - RingOfIntegers.mapAlgHom D.sp.cm.sig b : 𝓞 D.host.E) : D.host.E) =
      (b : D.host.E) - D.sp.cm.sig (b : D.host.E) := by
    rfl
  have hδ : Valued.v (τ (D.sp.cm.sig (b : D.host.E)) - τ (b : D.host.E)) = 1 := by
    have : τ (D.sp.cm.sig (b : D.host.E)) - τ (b : D.host.E) =
        -τ ((b - RingOfIntegers.mapAlgHom D.sp.cm.sig b : 𝓞 D.host.E) : D.host.E) := by
      rw [e, map_sub]; ring
    rw [this, Valuation.map_neg, h1]
  have hδ0 : τ (D.sp.cm.sig (b : D.host.E)) - τ (b : D.host.E) ≠ 0 := fun h => by
    rw [h, map_zero] at hδ; exact zero_ne_one hδ
  refine ⟨b, (τ (D.sp.cm.sig (b : D.host.E)) - τ (b : D.host.E))⁻¹, ?_, inv_mul_cancel₀ hδ0⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hδ, inv_one]

variable {D : D7} {a a' : ℕ}

theorem coBar_eq (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (u : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E)) :
    GlobalTheory.VacShape.coBar Bs Γ u =
      -(Γ.V'.J.map Bs.τ₁ * u.map (piW (Bs.τ₁.comp D.sp.cm.sig)) * (Γ.W.J.map Bs.τ₁)ᵀ) := by
  unfold GlobalTheory.VacShape.coBar
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem coBar_neg (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (u : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E)) :
    GlobalTheory.VacShape.coBar Bs Γ (-u) = -GlobalTheory.VacShape.coBar Bs Γ u := by
  have := GlobalTheory.VacShape.coBar_add Bs Γ u (-u)
  rw [add_neg_cancel, GlobalTheory.VacShape.coBar_zero] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem coBar_smul (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (c : AF D.host.F) (u : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E)) :
    GlobalTheory.VacShape.coBar Bs Γ (c • u) = evFin D.host.F Bs.v₁ c • GlobalTheory.VacShape.coBar Bs Γ u := by
  rw [coBar_eq, coBar_eq, map_piW_smul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem coBar_gen (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (c : AF D.host.F) (x : Fin a' → D.host.E) (y : Fin (a + a') → D.host.E) :
    GlobalTheory.VacShape.coBar Bs Γ (c • incM D.host.F (vecMulVec x y)) =
      evFin D.host.F Bs.v₁ c • vecMulVec (-(Γ.V'.J.map Bs.τ₁ *ᵥ fun i => (Bs.τ₁.comp D.sp.cm.sig) (x i)))
        (Γ.W.J.map Bs.τ₁ *ᵥ fun j => (Bs.τ₁.comp D.sp.cm.sig) (y j)) := by
  rw [coBar_eq, map_piW_smul_incM, vecMulVec_map (Bs.τ₁.comp D.sp.cm.sig),
    Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec_mul, vecMulVec_neg_left, smul_neg]

end Shape

section Main

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (piW incM AE latAtV At)

variable {D : D7} {a a' : ℕ}

def Xs (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) : Set (Fin a' → Fv D.host.F Bs.v₁) :=
  {z | ∃ x ∈ L₁, z = -(Γ.V'.J.map Bs.τ₁ *ᵥ fun i => (Bs.τ₁.comp D.sp.cm.sig) (x i))}

def Ys (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)) : Set (Fin (a + a') → Fv D.host.F Bs.v₁) :=
  {z | ∃ y ∈ L₂, z = Γ.W.J.map Bs.τ₁ *ᵥ fun j => (Bs.τ₁.comp D.sp.cm.sig) (y j)}

theorem gen_mem_Sa (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (hU : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E)) (x : Fin a' → D.host.E) (hx : x ∈ L₁)
    (y : Fin (a + a') → D.host.E) (hy : y ∈ L₂) :
    vecMulVec (-(Γ.V'.J.map Bs.τ₁ *ᵥ fun i => (Bs.τ₁.comp D.sp.cm.sig) (x i)))
      (Γ.W.J.map Bs.τ₁ *ᵥ fun j => (Bs.τ₁.comp D.sp.cm.sig) (y j)) ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ := by
  obtain ⟨b, α, hα, hb⟩ := exists_unit_diff Bs.τ₁ hU
  have hτb := apply_coe_mem Bs.τ₁ b
  refine ⟨GlobalTheory.LatVac.liftV Bs.v₁ α • incM D.host.F (vecMulVec (b • x) y) -
    GlobalTheory.LatVac.liftV Bs.v₁ (α * Bs.τ₁ (b : D.host.E)) • incM D.host.F (vecMulVec x y), ?_, ?_, ?_⟩
  · refine sub_mem (AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV Bs.v₁ α, ?_, b • x, L₁.smul_mem b hx, y, hy, rfl⟩)
      (AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV Bs.v₁ _, ?_, x, hx, y, hy, rfl⟩)
    · rw [GlobalTheory.LatVac.evFin_liftV]; exact hα
    · rw [GlobalTheory.LatVac.evFin_liftV]; exact mul_mem hα hτb
  · rw [Matrix.map_sub _ (map_sub _), map_piW_smul_incM, map_piW_smul_incM, GlobalTheory.LatVac.evFin_liftV,
      GlobalTheory.LatVac.evFin_liftV]
    have hbx : ∀ i, (b • x) i = (b : D.host.E) * x i := fun i => rfl
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, vecMulVec_apply, Matrix.zero_apply, hbx,
      map_mul, smul_eq_mul]
    ring_nf
  · rw [sub_eq_add_neg, GlobalTheory.VacShape.coBar_add, coBar_neg, coBar_gen, coBar_gen, GlobalTheory.LatVac.evFin_liftV,
      GlobalTheory.LatVac.evFin_liftV, ← sub_eq_add_neg]
    have e1 : (fun i => (Bs.τ₁.comp D.sp.cm.sig) ((b • x) i)) =
        Bs.τ₁ (D.sp.cm.sig (b : D.host.E)) • fun i => (Bs.τ₁.comp D.sp.cm.sig) (x i) := by
      funext i
      simp [Algebra.smul_def, map_mul]
    have e3 : (Γ.V'.J.map Bs.τ₁ *ᵥ fun i => (Bs.τ₁.comp D.sp.cm.sig) ((b • x) i)) =
        Bs.τ₁ (D.sp.cm.sig (b : D.host.E)) • (Γ.V'.J.map Bs.τ₁ *ᵥ fun i => (Bs.τ₁.comp D.sp.cm.sig) (x i)) := by
      rw [e1]; exact Matrix.mulVec_smul _ _ _
    rw [e3, vecMulVec_neg_smul, smul_smul, ← sub_smul]
    have e2 : α * Bs.τ₁ (D.sp.cm.sig (b : D.host.E)) - α * Bs.τ₁ (b : D.host.E) = 1 := by rw [← hb]; ring
    rw [e2, one_smul]

theorem Sa_eq (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (hU : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E)) :
    (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁))) =
      (Submodule.span 𝒪[Fv D.host.F Bs.v₁] (prods (Xs Bs Γ L₁) (Ys Bs Γ L₂)) :
        Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁))) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u, hu, -, rfl⟩
    induction hu using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, -, hcint, x, hx, y, hy, rfl⟩ := hz
      rw [coBar_gen]
      exact Submodule.smul_mem _ (⟨evFin D.host.F Bs.v₁ c, (mem_int_iff _).2 hcint⟩ : 𝒪[Fv D.host.F Bs.v₁])
        (Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩)
    | zero => rw [GlobalTheory.VacShape.coBar_zero]; exact zero_mem _
    | add u u' _ _ h h' => rw [GlobalTheory.VacShape.coBar_add]; exact add_mem h h'
    | neg u _ h => rw [coBar_neg]; exact neg_mem h
  · let SM : Submodule 𝒪[Fv D.host.F Bs.v₁] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)) :=
      { carrier := GlobalTheory.VacShape.Sa Bs Γ L₁ L₂
        add_mem' := fun hA hB => add_mem hA hB
        zero_mem' := zero_mem _
        smul_mem' := by
          rintro c _ ⟨u, hu, hu0, rfl⟩
          have hc : (c : Fv D.host.F Bs.v₁) ∈ Bs.v₁.adicCompletionIntegers D.host.F := (mem_int_iff _).1 c.2
          refine ⟨GlobalTheory.LatVac.liftV Bs.v₁ c • u, (GlobalTheory.LatVac.latAtV_at_stable _ _ _).2 _ hc u hu, ?_, ?_⟩
          · rw [map_piW_smul, hu0, smul_zero]
          · rw [coBar_smul, GlobalTheory.LatVac.evFin_liftV]; rfl }
    have hle : Submodule.span 𝒪[Fv D.host.F Bs.v₁] (prods (Xs Bs Γ L₁) (Ys Bs Γ L₂)) ≤ SM :=
      Submodule.span_le.2 (by
        rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
        exact gen_mem_Sa Bs Γ L₁ L₂ hU x hx y hy)
    exact fun Z hZ => hle hZ

end Main

end GlobalTheory.VacShapeCl

open GlobalTheory.VacShapeCl in

theorem GlobalTheory.VacShapeCl.closure_Sa_eq_matLat : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    IsOpen (closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)))) → IsCompact (closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)))) →
    ∃ (P : GL (Fin a') (Fv D.host.F Bs.v₁)) (Λ : Submodule 𝒪[Fv D.host.F Bs.v₁] (Fin (a + a') → Fv D.host.F Bs.v₁)),
      ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁), Y ∈ closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁))) ↔ P.val * Y ∈ matLat (Fin a') Λ := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ ho hc
  rw [GlobalTheory.VacShapeCl.Sa_eq Bs Γ L₁ L₂ hTr.base.unram] at ho hc ⊢
  exact GlobalTheory.VacShapeCl.closure_eq _ _ ho hc
