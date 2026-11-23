import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSelfDualLatticeOfMemAllLatticeCompletionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.SrcSplit

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem tmul_mul_rat {m n k : ℕ} (c : AF D.host.F) (x : Matrix (Fin m) (Fin n) D.host.E) (π : Matrix (Fin n) (Fin k) D.host.E) :
    (Matrix.of fun i j => c ⊗ₜ[D.host.F] x i j : Mx D m n) * rat π = Matrix.of fun i j => c ⊗ₜ[D.host.F] (x * π) i j := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  show (c ⊗ₜ[D.host.F] x i l) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] π l j) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem rat_mulVec_tmul {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (c : AF D.host.F) (z : Fin n → D.host.E) :
    rat M *ᵥ (fun i => c ⊗ₜ[D.host.F] z i) = fun k => c ⊗ₜ[D.host.F] (M *ᵥ z) k := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k j) * (c ⊗ₜ[D.host.F] z j) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem mul_rat_mem_hatMx {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (π : Matrix (Fin n) (Fin n) D.host.E) (hM : ∀ x ∈ M, x * π ∈ M) {w : Mx D m n} (hw : w ∈ hatMx M) :
    w ⬝ rat π ∈ hatMx M := by
  let g : Mx D m n →+ Mx D m n :=
    { toFun := fun w => w ⬝ rat π, map_zero' := Matrix.zero_mul _, map_add' := fun a b => Matrix.add_mul a b _ }
  have hle : hatMx M ≤ (hatMx M).comap g := by
    refine (AddSubgroup.closure_le _).2 fun w hw => ?_
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    show (_ : Mx D m n) ⬝ rat π ∈ hatMx M
    rw [tmul_mul_rat]
    exact AddSubgroup.subset_closure ⟨α, hα, x * π, hM x hx, rfl⟩
  exact hle hw

theorem mul_mem_smul_homLat {m n : ℕ} (I : Ideal (𝓞 D.host.E)) (LS : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (π : Matrix (Fin n) (Fin n) D.host.E)
    (hπ : ∀ y ∈ LS, π *ᵥ y ∈ LS) : ∀ x ∈ I • homLat LS LT, x * π ∈ I • homLat LS LT := by
  let f : Matrix (Fin m) (Fin n) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin m) (Fin n) D.host.E :=
    { toFun := (· * π), map_add' := fun a b => Matrix.add_mul a b π, map_smul' := fun r a => Matrix.smul_mul r a π }
  have hH : (homLat LS LT).map f ≤ homLat LS LT := by
    rintro _ ⟨x, hx, rfl⟩ y hy
    show (x * π) *ᵥ y ∈ LT
    rw [← Matrix.mulVec_mulVec]
    exact hx _ (hπ y hy)
  intro x hx
  have h1 : f x ∈ (I • homLat LS LT).map f := ⟨x, hx, rfl⟩
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl hH h1

theorem mul_rat_mem_latO (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : GlobalTheory.FinPl.Pl D → Prop) (π π' : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (hadj : S.gram * π = π'ᴴ * S.gram)
    (hπ' : ∀ s ∈ LS, π' *ᵥ s ∈ LS) {u : Mx D T.rank S.rank} (hu : u ∈ latO S T LS LT P) :
    u ⬝ rat π ∈ latO S T LS LT P := by
  let g : Mx D T.rank S.rank →+ Mx D T.rank S.rank :=
    { toFun := fun w => w ⬝ rat π, map_zero' := Matrix.zero_mul _, map_add' := fun a b => Matrix.add_mul a b _ }
  have hle : latO S T LS LT P ≤ (latO S T LS LT P).comap g := by
    refine (AddSubgroup.closure_le _).2 fun w hw => ?_
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    show (_ : Mx D T.rank S.rank) ⬝ rat π ∈ latO S T LS LT P
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, π' *ᵥ s, hπ' s hs, t, ht, ?_⟩
    have e := tmul_mul_rat (pairA D.host.F 0 α) (Matrix.of fun i j => a * t i * ∑ k, star (s k) * S.gram k j) π
    simp only [Matrix.of_apply] at e
    rw [e]
    ext i j
    simp only [Matrix.of_apply]
    congr 1
    have e1 : ∀ v : Fin S.rank → D.host.E, ∀ l, ∑ k, star (v k) * S.gram k l = (star v ᵥ* S.gram) l := fun v l => rfl
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, e1]
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, ← hadj, ← Matrix.vecMul_vecMul]
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact hle hu

end GlobalTheory.AscFin.SrcSplit

namespace GlobalTheory.AscFin.SrcSplit

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem proj_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : ∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D,
      (fun i => pairA D.host.F 0 (indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L)
    (hmono : ∀ v, MonoAt d L L₀ v) (s : Fin S.rank → D.host.E) (hs : s ∈ L) :
    (d.e * d.qX) *ᵥ s ∈ L ∧ (d.e' * d.qY) *ᵥ s ∈ L := by
  have key : ∀ v, (fun i => pairA D.host.F 0 (indP D.host.F (· = v)) ⊗ₜ[D.host.F] s i) ∈ latV S L (· = v) := fun v =>
    AddSubgroup.subset_closure ⟨indP D.host.F (· = v), indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, s, hs,
      by funext k; rw [one_mul]⟩
  have split : ∀ (c : AF D.host.F) {k : ℕ} (e : Matrix (Fin S.rank) (Fin k) D.host.E)
      (q : Matrix (Fin k) (Fin S.rank) D.host.E),
      (fun i => c ⊗ₜ[D.host.F] ((e * q) *ᵥ s) i) =
        ∑ i, GlobalTheory.FinPl.colMul (rat e) i ((rat q *ᵥ (fun i => c ⊗ₜ[D.host.F] s i)) i) := by
    intro c k e q
    rw [← rat_mulVec_tmul, rat_mul, ← Matrix.mulVec_mulVec]
    generalize rat q *ᵥ (fun i => c ⊗ₜ[D.host.F] s i) = w
    funext l
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.colMul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  constructor
  · refine hL _ fun v => ?_
    rw [split]
    exact sum_mem fun i _ => ((hmono v _).1 (key v)).1 i
  · refine hL _ fun v => ?_
    rw [split]
    exact sum_mem fun i _ => ((hmono v _).1 (key v)).2.1 i

theorem mem_of_proj {m : ℕ} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (A : AddSubgroup (Mx D m S.rank))
    (hA : ∀ w ∈ A, w ⬝ rat (d.e * d.qX) ∈ A ∧ w ⬝ rat (d.e' * d.qY) ∈ A) (u : Mx D m S.rank) (hu : u ∈ A) :
    u ⬝ d.jX ⬝ d.pX ∈ A ∧ u ⬝ d.jY ⬝ d.pY ∈ A ∧ u ⬝ d.j0 ⬝ d.p0 ∈ A := by
  have eX : d.jX ⬝ d.pX = rat (d.e * d.qX) := by rw [rat_mul]; rfl
  have eY : d.jY ⬝ d.pY = rat (d.e' * d.qY) := by rw [rat_mul]; rfl
  have e0 : d.j0 ⬝ d.p0 = 1 - d.jX ⬝ d.pX - d.jY ⬝ d.pY := by
    rw [← d.sum_eq_one]; abel
  obtain ⟨hX, hY⟩ := hA u hu
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, eX]; exact hX
  · rw [Matrix.mul_assoc, eY]; exact hY
  · rw [Matrix.mul_assoc, e0, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, eX, eY]
    exact sub_mem (sub_mem hu hX) hY

theorem adj_X {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    (negSp S).gram * (d.e * d.qX) = (d.e' * d.qY)ᴴ * (negSp S).gram := by
  have hG : S.gramᴴ = S.gram := Matrix.ext fun i j => S.herm.eq _ _
  show -S.gram * (d.e * (d.e'ᴴ * S.gram)) = (d.e' * (d.eᴴ * S.gram))ᴴ * -S.gram
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

theorem adj_Y {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    (negSp S).gram * (d.e' * d.qY) = (d.e * d.qX)ᴴ * (negSp S).gram := by
  have hG : S.gramᴴ = S.gram := Matrix.ext fun i j => S.herm.eq _ _
  show -S.gram * (d.e' * (d.eᴴ * S.gram)) = (d.e * (d.e'ᴴ * S.gram))ᴴ * -S.gram
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

end GlobalTheory.AscFin.SrcSplit

open GlobalTheory.AscFin.SrcSplit in

theorem GlobalTheory.AscFin.srcSplit_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jX) ∈ latRow G (2 * ρ + 1) ∧ (F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY) ∈ latRow G (2 * ρ + 1) ∧ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).j0) ∈ latRow G (2 * ρ + 1) := by
  intro D hD T L μ0 hLμ sc G W M hM F hF ρ h u hu
  obtain ⟨-, H2, -⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hLμ sc G W M hM F hF
  have hmono : ∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := fun v => ((H2 ρ h).2.1 v).1
  have hin : Node.InRange D.R.m (.grid (2 * ρ + 2) 0) := ⟨h, Nat.zero_le _⟩
  have hsd : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV hin (fun j hj => by injection hj with h1; omega)).sd
  have hP := proj_mem (F.dB ρ h) (GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions hsd) hmono
  have memR : ∀ w : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank (G.V (.grid (2 * ρ + 2) 0)).rank, w ∈ latRow G (2 * ρ + 1) → ∀ π π' : Matrix (Fin (G.V (.grid (2 * ρ + 2) 0)).rank) (Fin (G.V (.grid (2 * ρ + 2) 0)).rank) D.host.E,
      (negSp (G.V (.grid (2 * ρ + 2) 0))).gram * π = π'ᴴ * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram →
      (∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0), π' *ᵥ s ∈ G.Λ (.grid (2 * ρ + 2) 0)) →
      (∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0), π *ᵥ s ∈ G.Λ (.grid (2 * ρ + 2) 0)) →
      w ⬝ rat π ∈ latRow G (2 * ρ + 1) := by
    intro w hw π π' hadj hπ' hπ
    obtain ⟨hw1, hw2⟩ := hw
    refine ⟨mul_rat_mem_latO (negSp (G.V (.grid (2 * ρ + 2) 0))) _ _ _ _ π π' hadj hπ' hw1, fun e he => ?_⟩
    rw [← Matrix.smul_mul]
    exact mul_rat_mem_hatMx _ π (mul_mem_smul_homLat _ _ _ π hπ) (hw2 e he)
  exact mem_of_proj (F.dB ρ h) (latRow G (2 * ρ + 1))
    (fun w hw => ⟨memR w hw _ _ (adj_X (F.dB ρ h)) (fun s hs => (hP s hs).2) (fun s hs => (hP s hs).1),
      memR w hw _ _ (adj_Y (F.dB ρ h)) (fun s hs => (hP s hs).1) (fun s hs => (hP s hs).2)⟩) u hu
