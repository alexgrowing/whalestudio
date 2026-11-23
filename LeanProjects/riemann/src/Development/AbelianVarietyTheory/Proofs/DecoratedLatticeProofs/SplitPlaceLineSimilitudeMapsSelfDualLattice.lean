import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSecAddCsec
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLineSim

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_not_int : ∃ x : k, x ∉ 𝒪[k] := by
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  refine ⟨r⁻¹, fun h => ?_⟩
  have h1 : valuation k r⁻¹ ≤ 1 := h
  have hr : r ≠ 0 := hr0
  have : (1 : ValueGroupWithZero k) ≤ valuation k r := by
    calc (1 : ValueGroupWithZero k) = valuation k (r * r⁻¹) := by rw [mul_inv_cancel₀ hr, map_one]
      _ = valuation k r * valuation k r⁻¹ := map_mul _ _ _
      _ ≤ valuation k r * 1 := by gcongr
      _ = valuation k r := mul_one _
  exact absurd hr1 (not_lt.2 this)

theorem mul_sec' (q : SplitPt D k) (a : AE D) (b : k) : a * q.sec b = q.sec (q.pr a * b) := by
  rw [mul_comm, FrameLat.sec_mul_right, mul_comm]

theorem mul_csec (q : SplitPt D k) (a : AE D) (b : k) :
    a * cA D (q.sec b) = cA D (q.sec (q.pr (cA D a) * b)) := by
  rw [← mul_sec', map_mul, Formalism.L2.Theta.cA_cA]

theorem mulVec_sec' (q : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (A : Fin n → k) :
    (M *ᵥ fun i => q.sec (A i)) = fun j => q.sec ((M.map q.pr *ᵥ A) j) := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_sec', map_sum]

theorem mulVec_csec (q : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (B : Fin n → k) :
    (M *ᵥ fun i => cA D (q.sec (B i))) = fun j => cA D (q.sec ((M.map (fun a => q.pr (cA D a)) *ᵥ B) j)) := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_csec, map_sum]

theorem pr_cA_sec (q : SplitPt D k) (c : k) : q.pr (cA D (q.sec c)) = 0 := by
  have he : q.pr (cA D q.e) = 0 := by
    have h1 : q.pr (cA D q.e * q.e) = 0 := by rw [FrameLat.cAe_mul_e, map_zero]
    have pe : q.pr q.e = 1 := by rw [← FrameLat.sec_one, q.pr_sec]
    rwa [map_mul, pe, mul_one] at h1
  rw [← FrameLat.e_mul_sec q c, map_mul, map_mul, he, zero_mul]

theorem pr_cA_xi_int (q : SplitPt D k) (h : q.UnitAA) : q.pr (cA D (incA D D.host.xi0)) ∈ 𝒪[k] := by
  have hid : cA D (q.sec 1) ∈ idAt D (· = q.v) := FrameLat.csec_mem_idAt (p := q) 1
  have hc : cA D (q.sec 1) ∈ intAt D (· = q.v) := by
    refine (GlobalTheory.SplitIntComp.mem_intAt_iff q hid).2 ⟨?_, ?_⟩
    · rw [pr_cA_sec]; exact zero_mem _
    · rw [Formalism.L2.Theta.cA_cA, q.pr_sec]; exact one_mem _
  have h2 := (h.1 _ hc).1
  have h3 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.1).1 h2).2
  rwa [map_mul, Formalism.L2.Theta.cA_cA, map_mul, q.pr_sec, mul_one] at h3

theorem pr_xi_int (q : SplitPt D k) (h : q.UnitAA) : q.pr (incA D D.host.xi0) ∈ 𝒪[k] :=
  (GlobalTheory.SplitIntComp.val_xi q h).le

end GlobalTheory.SplitLineSim

namespace GlobalTheory.SplitLineSim
open GlobalTheory.FinPl

theorem line_sim_maps : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (L L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (LL : GlobalTheory.FinPl.Lat L) (LZ : GlobalTheory.FinPl.Lat L'') (zL : Fin L.rank → k) (z₀ : Fin L''.rank → k) (u : k), q.UnitAA → IsSelfDualC L LL → IsSelfDualC L'' LZ → L.rank = 1 → L''.rank = 1 → (∀ y : k, y ∈ 𝒪[k] ↔ (fun i => q.sec (zL i * y)) ∈ GlobalTheory.FinPl.latV L LL (· = q.v)) → (∀ y : k, y ∈ 𝒪[k] ↔ (fun i => q.sec (z₀ i * y)) ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v)) → valuation k u = 1 → τ.map (ofSplit q).pr *ᵥ z₀ = u • zL → τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ y ∈ GlobalTheory.FinPl.latV L'' LZ (· = q.v), (rat τ : Mx D L.rank L''.rank) *ᵥ y ∈ GlobalTheory.FinPl.latV L LL (· = q.v) := by
  intro D k _ _ _ _ q L L'' τ LL LZ zL z₀ u hU hLL hLZ hr hr'' hcL hcZ hu hτz hτ y hy
  haveI : Unique (Fin L.rank) := ⟨⟨⟨0, by omega⟩⟩, fun j => Fin.ext (by have := j.2; omega)⟩
  haveI : Unique (Fin L''.rank) := ⟨⟨⟨0, by omega⟩⟩, fun j => Fin.ext (by have := j.2; omega)⟩
  set j0 : Fin L.rank := default with hj0
  set i0 : Fin L''.rank := default with hi0
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hu_int : u ∈ 𝒪[k] := hu.le
  have hui_int : u⁻¹ ∈ 𝒪[k] := by
    show valuation k u⁻¹ ≤ 1
    rw [map_inv₀, hu, inv_one]

  have h1 : q.pr (incA D (τ j0 i0)) * z₀ i0 = u * zL j0 := by
    have := congrFun hτz j0
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hzL : zL j0 ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_not_int (k := k)
    apply hx
    rw [hcL]
    have : (fun i => q.sec (zL i * x)) = 0 := by
      funext i
      rw [Subsingleton.elim i j0, h0, zero_mul, map_zero]
      rfl
    rw [this]
    exact zero_mem _
  have hz0 : z₀ i0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact hzL ((mul_eq_zero.1 h1.symm).resolve_left hu0)

  have hyS : ∀ i, y i ∈ idAt D (· = q.v) := FrameLat.latV_supp hy
  set A : Fin L''.rank → k := fun i => q.pr (y i) with hA
  set B : Fin L''.rank → k := fun i => q.pr (cA D (y i)) with hB
  have hyAB : y = (fun i => q.sec (A i)) + fun i => cA D (q.sec (B i)) := by
    funext i
    exact GlobalTheory.SplitIntComp.eq_sec_add_csec q (hyS i)
  rw [hyAB] at hy
  obtain ⟨hyA, hyB⟩ := (FrameLat.decomp hLZ A B).1 hy
  rw [hyAB, Matrix.mulVec_add, mulVec_sec', mulVec_csec]
  refine (FrameLat.decomp hLL _ _).2 ⟨?_, ?_⟩
  ·
    set c : k := A i0 / z₀ i0 with hc
    have hcA : ∀ i, z₀ i * c = A i := fun i => by
      rw [Subsingleton.elim i i0, hc, mul_div_cancel₀ _ hz0]
    have hcint : c ∈ 𝒪[k] := (hcZ c).2 (by simpa only [hcA] using hyA)
    have : (fun j => q.sec ((((rat τ : Mx D L.rank L''.rank)).map q.pr *ᵥ A) j)) =
        fun j => q.sec (zL j * (u * c)) := by
      funext j
      rw [Subsingleton.elim j j0]
      congr 1
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique]
      rw [← hcA i0]
      change q.pr (incA D (τ j0 i0)) * (z₀ i0 * c) = _
      rw [← mul_assoc, h1]
      ring
    rw [this]
    exact (hcL _).1 (mul_mem hu_int hcint)
  ·
    rw [FrameLat.csec_mem_iff hLL]
    intro x hx
    have h00 : star (τ j0 i0) * (L.gram j0 j0 * τ j0 i0) = -(D.host.xi0 * star D.host.xi0) * L''.gram i0 i0 := by
      have := congrFun (congrFun hτ i0) i0
      rw [Matrix.mul_apply, Fintype.sum_unique, Matrix.mul_apply, Fintype.sum_unique,
        Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul] at this
      exact this
    let φ : D.host.E →+* k := (q.pr.comp (cA D)).comp (incA D)
    have hφs : ∀ t : D.host.E, φ (star t) = q.pr (incA D t) := fun t => by
      show q.pr (cA D (incA D (star t))) = _
      rw [FrameLat.cA_incA, star_star]

    have e3 : q.pr (incA D (τ j0 i0)) * (q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0)))) =
        -(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0)) * q.pr (cA D (incA D (L''.gram i0 i0))) := by
      have h2 := congrArg φ h00
      rw [map_mul, map_mul, map_mul, map_neg, map_mul, hφs (τ j0 i0), hφs D.host.xi0] at h2
      exact h2
    have hcw_int : -(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0)) ∈ 𝒪[k] :=
      neg_mem (mul_mem (pr_cA_xi_int q hU) (pr_xi_int q hU))
    obtain ⟨c', hc'⟩ : ∃ c' : k, c' = x j0 / zL j0 := ⟨_, rfl⟩
    have hxc : ∀ j, zL j * c' = x j := fun j => by
      rw [Subsingleton.elim j j0, hc', mul_div_cancel₀ _ hzL]
    have hc'int : c' ∈ 𝒪[k] := (hcL c').2 (by simpa only [hxc] using hx)

    have hz1 : (fun i => q.sec (z₀ i)) ∈ latV L'' LZ (· = q.v) := by
      simpa only [mul_one] using (hcZ 1).1 (one_mem _)
    have hZB := (FrameLat.csec_mem_iff hLZ B).1 hyB z₀ hz1
    simp only [Fintype.sum_unique] at hZB
    have hinv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
    have e0 : ((((rat τ : Mx D L.rank L''.rank)).map (fun a => q.pr (cA D a)) *ᵥ B) j0) =
        q.pr (cA D (incA D (τ j0 i0))) * B i0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_unique]
      rfl
    simp only [Fintype.sum_unique]
    rw [e0, ← hxc j0]
    have key : zL j0 * c' * q.pr (cA D (incA D (L.gram j0 j0))) * (q.pr (cA D (incA D (τ j0 i0))) * B i0) =
        c' * u⁻¹ * (-(q.pr (cA D (incA D D.host.xi0)) * q.pr (incA D D.host.xi0))) *
          (z₀ i0 * q.pr (cA D (incA D (L''.gram i0 i0))) * B i0) := by
      linear_combination (c' * u⁻¹ * z₀ i0 * B i0) * e3 -
        (c' * u⁻¹ * q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0))) * B i0) * h1 -
        (c' * q.pr (cA D (incA D (L.gram j0 j0))) * q.pr (cA D (incA D (τ j0 i0))) * B i0 * zL j0) * hinv
    rw [key]
    exact mul_mem (mul_mem (mul_mem hc'int hui_int) hcw_int) hZB

end GlobalTheory.SplitLineSim
