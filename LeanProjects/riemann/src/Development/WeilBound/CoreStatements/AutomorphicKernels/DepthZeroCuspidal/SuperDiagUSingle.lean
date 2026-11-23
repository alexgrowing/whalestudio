import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.IsLevelOne
import GroundTheory.AutomorphicForms.Iwasawa
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Whittaker

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Basics
variable {m : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem corner_cs_cs (g : GL (Fin m) k) (i j : Fin m) :
    (corner g : Matrix (Fin (m+1)) (Fin (m+1)) k) i.castSucc j.castSucc = (g : Matrix _ _ k) i j := by
  simp [corner, val_emb₂, stdSum, Matrix.reindex_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem corner_cs_last (g : GL (Fin m) k) (i : Fin m) :
    (corner g : Matrix (Fin (m+1)) (Fin (m+1)) k) i.castSucc (Fin.last m) = 0 := by
  simp [corner, val_emb₂, stdSum, Matrix.reindex_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem corner_last_cs (g : GL (Fin m) k) (j : Fin m) :
    (corner g : Matrix (Fin (m+1)) (Fin (m+1)) k) (Fin.last m) j.castSucc = 0 := by
  simp [corner, val_emb₂, stdSum, Matrix.reindex_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem corner_last_last (g : GL (Fin m) k) :
    (corner g : Matrix (Fin (m+1)) (Fin (m+1)) k) (Fin.last m) (Fin.last m) = 1 := by
  simp [corner, val_emb₂, stdSum, Matrix.reindex_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem corner_mul (g h : GL (Fin m) k) : corner (g * h) = corner g * corner h := by
  simp only [corner]
  rw [← map_mul]
  simp

theorem mem_fixed_iff {V : Type} [AddCommGroup V] [Module ℂ V] {G : Type} [Group G]
    (ρ : Representation ℂ G V) (H : Subgroup G) (x : V) :
    x ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h x = x := by
  constructor
  · intro hx h hh
    have := hx ⟨h, hh⟩
    simpa using this
  · intro hx h
    simpa using hx h h.2

theorem rho_mul {V : Type} [AddCommGroup V] [Module ℂ V] {G : Type} [Group G]
    (ρ : Representation ℂ G V) (a b : G) (x : V) : ρ (a * b) x = ρ a (ρ b x) := by
  rw [map_mul, Module.End.mul_apply]

def stabG {V : Type} [AddCommGroup V] [Module ℂ V] {G : Type} [Group G]
    (ρ : Representation ℂ G V) (x : V) : Subgroup G where
  carrier := {g | ρ g x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [rho_mul, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [← rho_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem mem_fixed_iff_le {V : Type} [AddCommGroup V] [Module ℂ V] {G : Type} [Group G]
    (ρ : Representation ℂ G V) (H : Subgroup G) (x : V) :
    x ∈ fixed ρ H ↔ H ≤ stabG ρ x := by
  rw [mem_fixed_iff]
  exact ⟨fun h g hg => h g hg, fun h g hg => h hg⟩

theorem val_eq_unif {c : kˣ} (hc : ord k c = 1) : valuation k (c : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (K := k) (uniformizer k)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact uniformizer_ne_zero hx.symm
  set u := Units.mk0 x hx0
  have h1 : ord k u = 1 := ord_eq_one (by simpa [u] using hx)
  have h3 : ord k (u * u⁻¹) = 0 := by rw [mul_inv_cancel]; exact ord_eq_zero (by simp)
  have h2 : ord k (c * u⁻¹) = 0 := by
    rw [ord_mul] at h3 ⊢
    omega
  have h4 := ord_eq_zero_iff.1 h2
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀] at h4
  have hu0 : valuation k (u : k) ≠ 0 := by simp [u, hx0]
  rw [← hx]
  have := (mul_inv_eq_one₀ hu0).1 h4
  simpa [u] using this

theorem levelOne_triv {ψ : AddChar k Circle} (hψ : IsLevelOne ψ) {y : k} (hy : valuation k y < 1) :
    ψ y = 1 := by
  obtain ⟨c, hc, hc1⟩ := hψ
  exact (hc c).2 le_rfl y (by rw [val_eq_unif hc1]; exact le_uniformizer_iff.2 hy)

theorem levelOne_exists {ψ : AddChar k Circle} (hψ : IsLevelOne ψ) :
    ∃ y : k, valuation k y ≤ 1 ∧ ψ y ≠ 1 := by
  obtain ⟨c, hc, hc1⟩ := hψ
  by_contra H
  push_neg at H
  have := (hc 1).1 (fun y hy => H y (by simpa using hy))
  rw [map_one, val_eq_unif hc1] at this
  exact absurd uniformizer_lt_one (not_lt.2 this)

end Basics

section Mask
variable {N : ℕ} (P : Fin N → Fin N → Prop) [DecidableRel P]

def maskM (X : Matrix (Fin N) (Fin N) k) : Matrix (Fin N) (Fin N) k := fun a b => if P a b then X a b else 0

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem maskM_mul (hP : ∀ a b c, P a b → P b c → False) (X Y : Matrix (Fin N) (Fin N) k) :
    maskM P X * maskM P Y = 0 := by
  ext a c
  simp only [Matrix.mul_apply, maskM, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases h1 : P a b
  · by_cases h2 : P b c
    · exact (hP a b c h1 h2).elim
    · simp [h2]
  · simp [h1]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem maskM_add (X Y : Matrix (Fin N) (Fin N) k) : maskM P (X + Y) = maskM P X + maskM P Y := by
  ext a b
  simp only [maskM, Matrix.add_apply]
  split_ifs <;> simp

def U (hP : ∀ a b c, P a b → P b c → False) (X : Matrix (Fin N) (Fin N) k) : GL (Fin N) k :=
  ⟨1 + maskM P X, 1 - maskM P X, by simp [add_mul, mul_sub, maskM_mul P hP],
    by simp [sub_mul, mul_add, maskM_mul P hP]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem U_val (hP : ∀ a b c, P a b → P b c → False) (X : Matrix (Fin N) (Fin N) k) :
    ((U P hP X : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = 1 + maskM P X := rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem U_inv_val (hP : ∀ a b c, P a b → P b c → False) (X : Matrix (Fin N) (Fin N) k) :
    (((U P hP X)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = 1 - maskM P X := rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem U_mul (hP : ∀ a b c, P a b → P b c → False) (X Y : Matrix (Fin N) (Fin N) k) :
    U P hP X * U P hP Y = U P hP (X + Y) := by
  apply Units.ext
  rw [Units.val_mul, U_val, U_val, U_val, maskM_add, add_mul, one_mul, mul_add, mul_one, maskM_mul P hP]
  abel

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem U_mem_unipB (hP : ∀ a b c, P a b → P b c → False) (hlt : ∀ a b, P a b → a < b)
    (X : Matrix (Fin N) (Fin N) k) : U P hP X ∈ unipB k (Fin N) := by
  rw [mem_unipB]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [U_val, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hji), maskM,
      if_neg (fun h => absurd (hlt i j h) (not_lt.2 hji.le)), add_zero]
  · rw [U_val, Matrix.add_apply, Matrix.one_apply_eq, maskM, if_neg (fun h => lt_irrefl _ (hlt i i h)), add_zero]

theorem U_mem_KO (hP : ∀ a b c, P a b → P b c → False) (X : Matrix (Fin N) (Fin N) k)
    (hX : ∀ a b, P a b → valuation k (X a b) ≤ 1) : U P hP X ∈ KO k (Fin N) := by
  have hM : GlobalTheory.StepData.IntM (maskM P X) := fun a b => by
    simp only [maskM]
    split_ifs with h
    · exact hX a b h
    · exact zero_mem _
  rw [GlobalTheory.StepData.mem_KO, U_inv_val, U_val]
  exact ⟨GlobalTheory.StepData.intM_one.add hM, by
    rw [sub_eq_add_neg]; exact GlobalTheory.StepData.intM_one.add hM.neg⟩

theorem U_mem_KOne (hP : ∀ a b c, P a b → P b c → False) (X : Matrix (Fin N) (Fin N) k)
    (hX : ∀ a b, P a b → valuation k (X a b) < 1) : U P hP X ∈ KOne k (Fin N) := by
  rw [GlobalTheory.StepData.mem_KOne, U_val, add_sub_cancel_left]
  intro a b
  simp only [maskM]
  split_ifs with h
  · exact hX a b h
  · simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem diag_conj_U (hP : ∀ a b c, P a b → P b c → False) (X : Matrix (Fin N) (Fin N) k) (τ : Fin N → kˣ) :
    GroundTheory.Automorphic.Iwasawa.diagGL k N τ * U P hP X * (GroundTheory.Automorphic.Iwasawa.diagGL k N τ)⁻¹ =
      U P hP (Matrix.of fun a b => (τ a : k) * X a b * ((τ b : k))⁻¹) := by
  apply Units.ext
  rw [← map_inv, Units.val_mul, Units.val_mul, GroundTheory.Automorphic.Iwasawa.coe_diagGL,
    GroundTheory.Automorphic.Iwasawa.coe_diagGL, U_val, U_val]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.add_apply, maskM, Matrix.one_apply, Pi.inv_apply, Units.val_inv_eq_inv_val, Matrix.of_apply]
  by_cases hab : a = b
  · subst hab
    split_ifs <;> field_simp
  · split_ifs <;> simp_all

end Mask

section Rep
variable {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem fixed_of_KO (ρ : Representation ℂ (GL (Fin N) k) V) {w : V} (hw : w ∈ fixed ρ (KOne k (Fin N)))
    {g : GL (Fin N) k} (hg : g ∈ KO k (Fin N)) : ρ g w ∈ fixed ρ (KOne k (Fin N)) := by
  rw [mem_fixed_iff] at hw ⊢
  intro h hh
  have h1 : g⁻¹ * h * g ∈ KOne k (Fin N) := by
    have := (Subgroup.mem_normalizer_iff.1 (KO_le_normalizer (inv_mem hg)) h).1 hh
    simpa using this
  rw [← rho_mul, show h * g = g * (g⁻¹ * h * g) by group, rho_mul, hw _ h1]

theorem whit_U {ψ : AddChar k Circle} (hψ : IsLevelOne ψ) (ρ : Representation ℂ (GL (Fin N) k) V)
    {l : Module.Dual ℂ V} (hl : IsFunctional ψ ρ l) (P : Fin N → Fin N → Prop) [DecidableRel P]
    (hP : ∀ a b c, P a b → P b c → False) (hlt : ∀ a b, P a b → a < b) (X : Matrix (Fin N) (Fin N) k)
    (hX : ∀ a b, P a b → valuation k (X a b) < 1) (x : V) :
    l (ρ (U P hP X) x) = l x := by
  rw [hl _ (U_mem_unipB P hP hlt X) x]
  have : ψ (superDiag (U P hP X)) = 1 := by
    apply levelOne_triv hψ
    unfold superDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => Valuation.map_sum_lt _ one_ne_zero fun j hj => ?_
    have hij : i ≠ j := by
      rintro rfl
      simp at hj
    rw [U_val, Matrix.add_apply, Matrix.one_apply_ne hij, zero_add, maskM]
    split_ifs with h
    · exact hX i j h
    · simp
  rw [this]
  simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem superDiag_U_single {M : ℕ} (p : Fin M)
    (hP : ∀ a b c : Fin (M + 1), (a = p.castSucc ∧ b = p.succ) → (b = p.castSucc ∧ c = p.succ) → False)
    (y : k) : superDiag (U (fun a b : Fin (M + 1) => a = p.castSucc ∧ b = p.succ) hP (Matrix.of fun _ _ => y)) = y := by
  unfold superDiag
  rw [Finset.sum_eq_single p.castSucc]
  · rw [Finset.sum_eq_single p.succ]
    · simp [U_val, maskM, Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := p)).ne]
    · intro j hj hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc] at hj
      exact absurd (Fin.ext (by simp [hj])) hne
    · simp
  · intro i _ hne
    refine Finset.sum_eq_zero fun j hj => ?_
    have hij : i ≠ j := by
      rintro rfl
      simp at hj
    rw [U_val, Matrix.add_apply, Matrix.one_apply_ne hij, zero_add, maskM, if_neg (fun h => hne h.1)]
  · simp

theorem diag_step_le {M : ℕ} {ψ : AddChar k Circle} (hψ : IsLevelOne ψ)
    (ρ : Representation ℂ (GL (Fin (M + 1)) k) V) {l : Module.Dual ℂ V} (hl : IsFunctional ψ ρ l)
    {w : V} (hw : w ∈ fixed ρ (KOne k (Fin (M + 1)))) (τ : Fin (M + 1) → kˣ)
    (h : l (ρ (GroundTheory.Automorphic.Iwasawa.diagGL k (M + 1) τ) w) ≠ 0) (p : Fin M) :
    valuation k (τ p.castSucc : k) ≤ valuation k (τ p.succ : k) := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨y, hy1, hy⟩ := levelOne_exists hψ
  let P : Fin (M + 1) → Fin (M + 1) → Prop := fun a b => a = p.castSucc ∧ b = p.succ
  have hP : ∀ a b c, P a b → P b c → False := by
    rintro a b c ⟨-, rfl⟩ ⟨h, -⟩
    exact (Fin.castSucc_lt_succ (i := p)).ne' h
  have hlt' : ∀ a b, P a b → a < b := by
    rintro a b ⟨rfl, rfl⟩
    exact Fin.castSucc_lt_succ (i := p)
  set D := GroundTheory.Automorphic.Iwasawa.diagGL k (M + 1) τ with hD
  let X : Matrix (Fin (M + 1)) (Fin (M + 1)) k := Matrix.of fun _ _ => y
  have hconj : D⁻¹ * U P hP X * D ∈ KOne k (Fin (M + 1)) := by
    have := diag_conj_U P hP X τ⁻¹
    rw [map_inv, inv_inv] at this
    rw [hD, this]
    apply U_mem_KOne
    rintro a b ⟨rfl, rfl⟩
    have h0 : valuation k (τ p.castSucc : k) ≠ 0 := by simp
    simp only [X, Matrix.of_apply, Pi.inv_apply, Units.val_inv_eq_inv_val, inv_inv, map_mul, map_inv₀]
    calc (valuation k (τ p.castSucc : k))⁻¹ * valuation k y * valuation k (τ p.succ : k)
        ≤ (valuation k (τ p.castSucc : k))⁻¹ * 1 * valuation k (τ p.succ : k) := by gcongr
      _ < 1 := by
        rw [mul_one, inv_mul_lt_iff₀ (zero_lt_iff.2 h0), mul_one]
        exact hlt
  have key : ρ (U P hP X) (ρ D w) = ρ D w := by
    rw [← rho_mul, show U P hP X * D = D * (D⁻¹ * U P hP X * D) by group, rho_mul,
      (mem_fixed_iff _ _ _).1 hw _ hconj]
  have := hl _ (U_mem_unipB P hP hlt' X) (ρ D w)
  rw [key, superDiag_U_single p hP y] at this
  apply hy
  have h2 : (ψ y : ℂ) = 1 := mul_right_cancel₀ h (this.symm.trans (one_mul _).symm)
  exact Circle.ext (by simpa using h2)

end Rep

section Parab
variable {M : ℕ}

def dTwo (p : Fin M) : Fin 2 → ℕ := ![p.val + 1, M - p.val]

theorem dTwo_sum (p : Fin M) : ∑ a, dTwo p a = M + 1 := by
  have := p.isLt
  simp [dTwo, Fin.sum_univ_two]
  omega

def eTwo (p : Fin M) : (Σ a, Fin (dTwo p a)) ≃ Fin (M + 1) := stdBlocks (dTwo p) (dTwo_sum p)

theorem eTwo_zero (p : Fin M) (i : Fin (dTwo p 0)) : ((eTwo p ⟨0, i⟩ : Fin (M + 1)) : ℕ) ≤ p.val := by
  have h := stdBlocks_val (dTwo p) (dTwo_sum p) 0 i
  have hi := i.isLt
  simp only [dTwo] at hi
  simp only [eTwo, h]
  simp
  simp at hi
  omega

theorem eTwo_one (p : Fin M) (j : Fin (dTwo p 1)) : p.val < ((eTwo p ⟨1, j⟩ : Fin (M + 1)) : ℕ) := by
  have h := stdBlocks_val (dTwo p) (dTwo_sum p) 1 j
  simp only [eTwo, h]
  simp [dTwo]
  omega

def PB (p : Fin M) (a b : Fin (M + 1)) : Prop := a.val ≤ p.val ∧ p.val < b.val

instance (p : Fin M) : DecidableRel (PB p) := fun a b => by unfold PB; infer_instance

theorem hPB (p : Fin M) : ∀ a b c, PB p a b → PB p b c → False := by
  rintro a b c ⟨-, h1⟩ ⟨h2, -⟩
  omega

theorem hltB (p : Fin M) : ∀ a b, PB p a b → a < b := by
  rintro a b ⟨h1, h2⟩
  exact Fin.lt_def.2 (by omega)

theorem PB_e (p : Fin M) (a b : Fin 2) (i : Fin (dTwo p a)) (j : Fin (dTwo p b)) :
    PB p (eTwo p ⟨a, i⟩) (eTwo p ⟨b, j⟩) ↔ a = 0 ∧ b = 1 := by
  fin_cases a <;> fin_cases b
  · have := eTwo_zero p j
    simp [PB]
    omega
  · have := eTwo_zero p i
    have := eTwo_one p j
    simp [PB]
    omega
  · have := eTwo_one p i
    simp [PB]
    omega
  · have := eTwo_one p i
    simp [PB]
    omega

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem one_e (p : Fin M) (a b : Fin 2) (i : Fin (dTwo p a)) (j : Fin (dTwo p b)) :
    (1 : Matrix (Fin (M + 1)) (Fin (M + 1)) k) (eTwo p ⟨a, i⟩) (eTwo p ⟨b, j⟩) =
      if (⟨a, i⟩ : Σ a, Fin (dTwo p a)) = ⟨b, j⟩ then 1 else 0 := by
  rw [Matrix.one_apply]
  exact if_congr (eTwo p).injective.eq_iff rfl rfl

theorem fin_two_lt {a b : Fin 2} (h : b < a) : a = 1 ∧ b = 0 := by
  fin_cases a <;> fin_cases b <;> simp_all

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem U_mem_unipRad (p : Fin M) (X : Matrix (Fin (M + 1)) (Fin (M + 1)) k) :
    U (PB p) (hPB p) X ∈ unipRad k (eTwo p) := by
  rw [mem_unipRad]
  refine ⟨?_, ?_⟩
  · rw [mem_parab_iff]
    intro a b i j hba
    obtain ⟨rfl, rfl⟩ := fin_two_lt hba
    have hP' : ¬ PB p (eTwo p ⟨1, i⟩) (eTwo p ⟨0, j⟩) := by rw [PB_e]; simp
    rw [U_val, Matrix.add_apply, one_e, maskM, if_neg hP']
    simp
  · intro a i j
    have hP' : ¬ PB p (eTwo p ⟨a, i⟩) (eTwo p ⟨a, j⟩) := by rw [PB_e]; rintro ⟨rfl, h⟩; simp at h
    rw [U_val, Matrix.add_apply, one_e, maskM, if_neg hP']
    simp [Matrix.one_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem unipRad_eq_U (p : Fin M) {g : GL (Fin (M + 1)) k} (hg : g ∈ unipRad k (eTwo p)) :
    (g : Matrix (Fin (M + 1)) (Fin (M + 1)) k) = 1 + maskM (PB p) (g : Matrix (Fin (M + 1)) (Fin (M + 1)) k) := by
  obtain ⟨hpar, hdiag⟩ := mem_unipRad.1 hg
  rw [mem_parab_iff] at hpar
  ext x y
  obtain ⟨⟨a, i⟩, rfl⟩ := (eTwo p).surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := (eTwo p).surjective y
  rw [Matrix.add_apply, one_e, maskM]
  by_cases hab : a = b
  · subst hab
    have hP' : ¬ PB p (eTwo p ⟨a, i⟩) (eTwo p ⟨a, j⟩) := by rw [PB_e]; rintro ⟨rfl, h⟩; simp at h
    rw [if_neg hP', hdiag]
    simp [Matrix.one_apply]
  · have hne : ¬ ((⟨a, i⟩ : Σ a, Fin (dTwo p a)) = ⟨b, j⟩) := fun h => hab (congrArg Sigma.fst h)
    rw [if_neg hne, zero_add]
    rcases lt_or_gt_of_ne hab with h | h
    · have : a = 0 ∧ b = 1 := by
        obtain ⟨h1, h2⟩ := fin_two_lt h
        exact ⟨h2, h1⟩
      rw [if_pos ((PB_e p a b i j).2 this)]
    · have hP' : ¬ PB p (eTwo p ⟨a, i⟩) (eTwo p ⟨b, j⟩) := by rw [PB_e]; rintro ⟨rfl, rfl⟩; simp at h
      rw [if_neg hP', hpar a b i j h]

end Parab

section Main

theorem diag_no_step {M : ℕ} (π : IrrRep (GL (Fin (M + 1)) k)) (hπ : IsCuspidal π.ρ) {ψ : AddChar k Circle}
    (hψ : IsLevelOne ψ) {l : Module.Dual ℂ π.V} (hl : IsFunctional ψ π.ρ l) {w : π.V}
    (hw : w ∈ fixed π.ρ (KOne k (Fin (M + 1)))) (τ : Fin (M + 1) → kˣ)
    (hmono : Monotone fun a => valuation k (τ a : k)) (p : Fin M)
    (hp : valuation k (τ p.castSucc : k) < valuation k (τ p.succ : k)) :
    l (π.ρ (GroundTheory.Automorphic.Iwasawa.diagGL k (M + 1) τ) w) = 0 := by
  classical
  haveI : Fintype 𝓀[k] := Fintype.ofFinite _
  have hP := hPB p
  have hlt := hltB p
  let lift : 𝓀[k] → 𝒪[k] := Function.surjInv IsLocalRing.residue_surjective
  have hlift : ∀ x, IsLocalRing.residue 𝒪[k] (lift x) = x := Function.surjInv_eq _
  let Yc : (Fin (M + 1) → Fin (M + 1) → 𝓀[k]) → Matrix (Fin (M + 1)) (Fin (M + 1)) k :=
    fun c => Matrix.of fun a b => ((lift (c a b) : 𝒪[k]) : k)
  have hYc : ∀ c a b, valuation k (Yc c a b) ≤ 1 := fun c a b => (lift (c a b)).2
  let s : π.V := ∑ c, π.ρ (U (PB p) hP (Yc c)) w
  have hinv : ∀ Y : Matrix (Fin (M + 1)) (Fin (M + 1)) k, (∀ a b, valuation k (Y a b) ≤ 1) →
      π.ρ (U (PB p) hP Y) s = s := by
    intro Y hY
    let r : Fin (M + 1) → Fin (M + 1) → 𝓀[k] := fun a b => IsLocalRing.residue 𝒪[k] ⟨Y a b, hY a b⟩
    have step : ∀ c, π.ρ (U (PB p) hP Y) (π.ρ (U (PB p) hP (Yc c)) w) = π.ρ (U (PB p) hP (Yc (c + r))) w := by
      intro c
      let Z : Matrix (Fin (M + 1)) (Fin (M + 1)) k := Y + Yc c - Yc (c + r)
      have hZ : U (PB p) hP Z ∈ KOne k (Fin (M + 1)) := by
        apply U_mem_KOne
        intro a b _
        have e1 : Z a b = ((⟨Y a b, hY a b⟩ + lift (c a b) - lift (c a b + r a b) : 𝒪[k]) : k) := by
          simp [Z, Yc]
        rw [e1, ← GlobalTheory.StepData.residue_eq_zero_iff_lt, map_sub, map_add, hlift, hlift]
        simp only [r]
        ring
      rw [← rho_mul, U_mul, show Y + Yc c = Yc (c + r) + Z by simp [Z], ← U_mul, rho_mul,
        (mem_fixed_iff _ _ _).1 hw _ hZ]
    simp only [s, map_sum, step]
    exact Fintype.sum_equiv (Equiv.addRight r) _ _ (fun c => rfl)
  have hsK : s ∈ fixed π.ρ (KOne k (Fin (M + 1))) :=
    Submodule.sum_mem _ fun c _ => fixed_of_KO π.ρ hw (U_mem_KO (PB p) hP _ fun a b _ => hYc c a b)
  have hs : s ∈ fixed π.ρ (KOne k (Fin (M + 1)) ⊔ (unipRad k (eTwo p) ⊓ KO k (Fin (M + 1)))) := by
    rw [mem_fixed_iff_le] at hsK ⊢
    refine sup_le hsK fun g hg => ?_
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
    have hgU : g = U (PB p) hP (g : Matrix (Fin (M + 1)) (Fin (M + 1)) k) := Units.ext (unipRad_eq_U p hg1)
    have hint := (GlobalTheory.StepData.mem_KO.1 hg2).1
    show π.ρ g s = s
    rw [hgU]
    exact hinv _ fun a b => hint a b
  have h0l : (0 : Fin (M + 1)) ≠ Fin.last M := by
    intro h
    have := congrArg Fin.val h
    simp at this
    have := p.isLt
    omega
  have hne : unipRad k (eTwo p) ≠ ⊥ := by
    intro hbot
    have hmem := U_mem_unipRad (k := k) p (Matrix.of fun _ _ => (1 : k))
    rw [hbot, Subgroup.mem_bot] at hmem
    have := congrArg (fun g : GL (Fin (M + 1)) k => (g : Matrix (Fin (M + 1)) (Fin (M + 1)) k) 0 (Fin.last M)) hmem
    simp only [U_val, Units.val_one, Matrix.add_apply, Matrix.one_apply_ne h0l, maskM] at this
    rw [if_pos ⟨by simp, by simp⟩] at this
    simp at this
  have : Subsingleton (Jacquet π.ρ (unipRad k (eTwo p))) := hπ.2 2 (dTwo p) (eTwo p) hne
  have hs0 : s = 0 := GlobalTheory.DepthZeroJac.depthZeroJacquetInjective k (M + 1) 2 (dTwo p) (eTwo p)
    (GlobalTheory.SplitRead.Irr.ofIrrRep π) s hs (Subsingleton.elim _ _)
  have heach : ∀ c, l (π.ρ (GroundTheory.Automorphic.Iwasawa.diagGL k (M + 1) τ) (π.ρ (U (PB p) hP (Yc c)) w)) =
      l (π.ρ (GroundTheory.Automorphic.Iwasawa.diagGL k (M + 1) τ) w) := by
    intro c
    rw [← rho_mul, show GroundTheory.Automorphic.Iwasawa.diagGL k (M + 1) τ * U (PB p) hP (Yc c) =
      (GroundTheory.Automorphic.Iwasawa.diagGL k (M + 1) τ * U (PB p) hP (Yc c) *
        (GroundTheory.Automorphic.Iwasawa.diagGL k (M + 1) τ)⁻¹) * GroundTheory.Automorphic.Iwasawa.diagGL k (M + 1) τ by group,
      rho_mul, diag_conj_U]
    apply whit_U hψ π.ρ hl (PB p) hP hlt
    intro a b hab
    have ha : valuation k (τ a : k) ≤ valuation k (τ p.castSucc : k) :=
      hmono (Fin.le_iff_val_le_val.2 (by simpa using hab.1))
    have hb : valuation k (τ p.succ : k) ≤ valuation k (τ b : k) :=
      hmono (Fin.le_iff_val_le_val.2 (by simpa using hab.2))
    have hb0 : valuation k (τ b : k) ≠ 0 := by simp
    simp only [Matrix.of_apply, map_mul, map_inv₀]
    calc valuation k (τ a : k) * valuation k (Yc c a b) * (valuation k (τ b : k))⁻¹
        ≤ valuation k (τ a : k) * 1 * (valuation k (τ b : k))⁻¹ := by gcongr; exact hYc c a b
      _ < 1 := by
        rw [mul_one, mul_inv_lt_iff₀ (zero_lt_iff.2 hb0), one_mul]
        exact lt_of_le_of_lt ha (lt_of_lt_of_le hp hb)
  have hsum : l (π.ρ (GroundTheory.Automorphic.Iwasawa.diagGL k (M + 1) τ) s) =
      (Fintype.card (Fin (M + 1) → Fin (M + 1) → 𝓀[k]) : ℂ) *
        l (π.ρ (GroundTheory.Automorphic.Iwasawa.diagGL k (M + 1) τ) w) := by
    simp only [s, map_sum, heach, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hs0, map_zero, map_zero] at hsum
  have hc : (Fintype.card (Fin (M + 1) → Fin (M + 1) → 𝓀[k]) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  exact (mul_eq_zero.1 hsum.symm).resolve_left hc

theorem diag_support {M : ℕ} (π : IrrRep (GL (Fin (M + 1)) k)) (hπ : IsCuspidal π.ρ) {ψ : AddChar k Circle}
    (hψ : IsLevelOne ψ) {l : Module.Dual ℂ π.V} (hl : IsFunctional ψ π.ρ l) {w : π.V}
    (hw : w ∈ fixed π.ρ (KOne k (Fin (M + 1)))) (τ : Fin (M + 1) → kˣ) (hτ : τ (Fin.last M) = 1)
    (h : l (π.ρ (GroundTheory.Automorphic.Iwasawa.diagGL k (M + 1) τ) w) ≠ 0) :
    ∀ a, valuation k (τ a : k) = 1 := by
  have hmono : Monotone fun a => valuation k (τ a : k) :=
    Fin.monotone_iff_le_succ.2 (diag_step_le hψ π.ρ hl hw τ h)
  have heq : ∀ p : Fin M, valuation k (τ p.castSucc : k) = valuation k (τ p.succ : k) := fun p =>
    le_antisymm (hmono (Fin.castSucc_lt_succ (i := p)).le)
      (not_lt.1 fun hp => h (diag_no_step π hπ hψ hl hw τ hmono p hp))
  intro a
  induction a using Fin.reverseInduction with
  | last => simp [hτ]
  | cast p ih => rw [heq p]; exact ih

end Main

theorem whittaker_support {m : ℕ} (π : IrrRep (GL (Fin (m + 1)) k)) (hπ : IsCuspidal π.ρ) (ψ : AddChar k Circle)
    (hψ : IsLevelOne ψ) (l : Module.Dual ℂ π.V) (hl : IsFunctional ψ π.ρ l)
    (v : π.V) (hv : v ∈ fixed π.ρ (KOne k (Fin (m + 1)))) (g : GL (Fin m) k)
    (hg : l (π.ρ (corner g) v) ≠ 0) : valuation k ((GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  obtain ⟨u, hu, lam, κ, hκ, rfl⟩ := GroundTheory.Automorphic.Iwasawa.exists_iwasawa k m g
  let τ : Fin (m + 1) → kˣ := Fin.lastCases 1 fun i => GroundTheory.Automorphic.Iwasawa.uniformizerUnit k ^ lam i
  have hcD : corner (GroundTheory.Automorphic.Iwasawa.torusPow k m lam) = GroundTheory.Automorphic.Iwasawa.diagGL k (m + 1) τ := by
    apply Units.ext
    ext a b
    rw [GroundTheory.Automorphic.Iwasawa.coe_diagGL, Matrix.diagonal_apply]
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simp [τ, corner_last_last]
      | cast j => simp [corner_last_cs, (Fin.castSucc_lt_last j).ne']
    | cast i =>
      induction b using Fin.lastCases with
      | last => simp [corner_cs_last, (Fin.castSucc_lt_last i).ne]
      | cast j =>
        rw [corner_cs_cs]
        simp [τ, GroundTheory.Automorphic.Iwasawa.torusPow, Matrix.diagonal_apply]
  have hcu : corner u ∈ unipB k (Fin (m + 1)) := by
    obtain ⟨hu1, hu2⟩ := (GroundTheory.Automorphic.Iwasawa.mem_unipotent k m).1 hu
    rw [mem_unipB]
    refine ⟨fun a b hba => ?_, fun a => ?_⟩
    · induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => exact absurd hba (lt_irrefl _)
        | cast j => exact corner_last_cs u j
      | cast i =>
        induction b using Fin.lastCases with
        | last => exact absurd hba (not_lt.2 (Fin.castSucc_lt_last i).le)
        | cast j =>
          rw [corner_cs_cs]
          exact hu1 (Fin.castSucc_lt_castSucc_iff.1 hba)
    · induction a using Fin.lastCases with
      | last => exact corner_last_last u
      | cast i => rw [corner_cs_cs]; exact hu2 i
  have hint : ∀ h : GL (Fin m) k, (∀ i j, (h : Matrix (Fin m) (Fin m) k) i j ∈ 𝒪[k]) →
      GlobalTheory.StepData.IntM (corner h : Matrix (Fin (m + 1)) (Fin (m + 1)) k) := by
    intro h hh a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rw [corner_last_last]; exact one_mem _
      | cast j => rw [corner_last_cs]; exact zero_mem _
    | cast i =>
      induction b using Fin.lastCases with
      | last => rw [corner_cs_last]; exact zero_mem _
      | cast j => rw [corner_cs_cs]; exact hh i j
  have hκ' := (GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff k m).1 hκ
  have hci : (corner κ)⁻¹ = corner κ⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [← corner_mul, mul_inv_cancel]; exact map_one _)
  have hcκ : corner κ ∈ KO k (Fin (m + 1)) :=
    GlobalTheory.StepData.mem_KO.2 ⟨hint κ hκ'.1, by rw [hci]; exact hint κ⁻¹ hκ'.2⟩
  have hv' := fixed_of_KO π.ρ hv hcκ
  rw [corner_mul, corner_mul, rho_mul, rho_mul, hl _ hcu, hcD] at hg
  have h1 := right_ne_zero_of_mul hg
  have hall := diag_support π hπ hψ hl hv' τ (by simp [τ]) h1
  have hvu : valuation k ((GeneralLinearGroup.det u : kˣ) : k) = 1 := by
    obtain ⟨hu1, hu2⟩ := (GroundTheory.Automorphic.Iwasawa.mem_unipotent k m).1 hu
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular hu1]
    simp [hu2]
  have hvt : valuation k ((GeneralLinearGroup.det (GroundTheory.Automorphic.Iwasawa.torusPow k m lam) : kˣ) : k) = 1 := by
    rw [GeneralLinearGroup.val_det_apply, GroundTheory.Automorphic.Iwasawa.torusPow,
      GroundTheory.Automorphic.Iwasawa.coe_diagGL, Matrix.det_diagonal, map_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    have := hall i.castSucc
    simpa [τ] using this
  have hvk : valuation k ((GeneralLinearGroup.det κ : kˣ) : k) = 1 :=
    GlobalTheory.StepData.valuation_det_of_mem_KO (GlobalTheory.StepData.mem_KO.2 ⟨hκ'.1, hκ'.2⟩)
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, map_mul, map_mul, hvu, hvt, hvk]
  simp

end PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

end
