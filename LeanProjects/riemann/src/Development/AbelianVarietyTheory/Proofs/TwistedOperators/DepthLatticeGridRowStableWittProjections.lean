import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjXPreservesEmbeddingLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjYPreservesEmbeddingLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ProjLat

variable {D : D7}

theorem tmul_mul_incA (x : AF D.host.F) (y z : D.host.E) : (x ⊗ₜ[D.host.F] y) * incA D z = x ⊗ₜ[D.host.F] (y * z) := by
  show (x ⊗ₜ[D.host.F] y) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem of_tmul_mul_rat {m n k : ℕ} (x : AF D.host.F) (X : Matrix (Fin m) (Fin n) D.host.E) (M : Matrix (Fin n) (Fin k) D.host.E) :
    HMul.hMul (Matrix.of fun i j => x ⊗ₜ[D.host.F] X i j : Mx D m n) (rat M : Mx D n k) =
      Matrix.of fun i j => x ⊗ₜ[D.host.F] (X * M) i j := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, tmul_mul_incA, TensorProduct.tmul_sum]

theorem latO_mul_rat {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} (M M' : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (hadj : M'ᴴ * S.gram = S.gram * M) (hL : ∀ s ∈ LS, M' *ᵥ s ∈ LS) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    HMul.hMul (u : Mx D T.rank S.rank) (rat M : Mx D S.rank S.rank) ∈ latO S T LS LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, hP, a, ha, M' *ᵥ s, hL s hs, t, ht, ?_⟩
    have h : ∀ l j, ∑ k, star (M' k l) * S.gram k j = ∑ k, S.gram l k * M k j := fun l j => by
      have := congrFun (congrFun hadj l) j
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using this
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, tmul_mul_incA, ← TensorProduct.tmul_sum]
    congr 1
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum, mul_assoc]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp_rw [mul_left_comm (star (M' _ y)) (star (s y))]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h y j]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem hatMx_mul_rat {m n : ℕ} (N : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (M : Matrix (Fin n) (Fin n) D.host.E) (hN : ∀ x ∈ N, x * M ∈ N) {w : Mx D m n} (hw : w ∈ hatMx N) :
    HMul.hMul w (rat M : Mx D n n) ∈ hatMx N := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    exact ⟨α, hα, x * M, hN x hx, of_tmul_mul_rat _ _ _⟩
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem smul_homLat_mul {m n : ℕ} (I : Ideal (𝓞 D.host.E)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (M : Matrix (Fin n) (Fin n) D.host.E) (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ)
    {x : Matrix (Fin m) (Fin n) D.host.E} (hx : x ∈ I • homLat Λ Λ') : x * M ∈ I • homLat Λ Λ' := by
  refine Submodule.smul_induction_on (p := fun x => x * M ∈ I • homLat Λ Λ') hx ?_ ?_
  · intro r hr n hn
    show (r • n) * M ∈ _
    rw [Matrix.smul_mul]
    exact Submodule.smul_mem_smul hr (fun y hy => by rw [← Matrix.mulVec_mulVec]; exact hn _ (hM y hy))
  · intro x y hx hy
    show (x + y) * M ∈ _
    rw [Matrix.add_mul]; exact add_mem hx hy

theorem proj_adj {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : (d.e' * d.qY)ᴴ * S.gram = S.gram * (d.e * d.qX) := by
  simp only [HypDec.qX, HypDec.qY, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, Matrix.mul_assoc]

theorem proj_adj' {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : (d.e * d.qX)ᴴ * S.gram = S.gram * (d.e' * d.qY) := by
  simp only [HypDec.qX, HypDec.qY, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, Matrix.mul_assoc]

theorem latRow_mul_rat {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : ℕ)
    (Mx₁ Mx₂ : Matrix (Fin (G.V (.grid (i + 1) 0)).rank) (Fin (G.V (.grid (i + 1) 0)).rank) D.host.E)
    (hadj : Mx₂ᴴ * (G.V (.grid (i + 1) 0)).gram = (G.V (.grid (i + 1) 0)).gram * Mx₁)
    (h1 : ∀ v ∈ G.Λ (.grid (i + 1) 0), Mx₁ *ᵥ v ∈ G.Λ (.grid (i + 1) 0))
    (h2 : ∀ v ∈ G.Λ (.grid (i + 1) 0), Mx₂ *ᵥ v ∈ G.Λ (.grid (i + 1) 0))
    {u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))} (hu : u ∈ latRow G i) :
    HMul.hMul u (rat Mx₁ : Mx D _ _) ∈ latRow G i := by
  obtain ⟨hu1, hu2⟩ := hu
  have hadj' : Mx₂ᴴ * (G.pS (.chi i 0)).gram = (G.pS (.chi i 0)).gram * Mx₁ := by
    show Mx₂ᴴ * (-(G.V (.grid (i + 1) 0)).gram) = (-(G.V (.grid (i + 1) 0)).gram) * Mx₁
    rw [Matrix.mul_neg, Matrix.neg_mul, hadj]
  have hu1' : u ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) (fun _ => True) := hu1
  have L1 := @latO_mul_rat D (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) (fun _ => True) Mx₁ Mx₂ hadj' h2
  have t1 := L1 hu1'
  have t2 : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • HMul.hMul u (rat Mx₁ : Mx D _ _) ∈ hatMx (G.modul • homLat (G.latS (.chi i 0)) (G.latT (.chi i 0))) := by
    intro e he
    rw [← Matrix.smul_mul]
    exact hatMx_mul_rat _ _ (fun x hx => smul_homLat_mul _ _ _ _ h1 hx) (hu2 e he)
  exact ⟨t1, t2⟩

theorem latRow_proj : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (_ : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), u * ((F.dJ (σ + 1) h).jX * (F.dJ (σ + 1) h).pX) ∈ latRow G (2 * σ + 2) ∧ u * ((F.dJ (σ + 1) h).jY * (F.dJ (σ + 1) h).pY) ∈ latRow G (2 * σ + 2) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' u hu
  have hA := hF.hJ (σ + 1) h
  have e : G.Λ (.grid (2 * σ + 2 + 1) 0) = _ := G.sp.colLat (2 * (σ + 1) + 1) (by omega) (by omega)
  have hX : ∀ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0), ((F.dJ (σ + 1) h).e * (F.dJ (σ + 1) h).qX) *ᵥ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0) := by
    intro v hv
    rw [e] at hv ⊢
    exact GlobalTheory.T.proj_X_preserves_embedding_lattice _ _ hA _ _ _ hv
  have hY : ∀ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0), ((F.dJ (σ + 1) h).e' * (F.dJ (σ + 1) h).qY) *ᵥ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0) := by
    intro v hv
    rw [e] at hv ⊢
    exact GlobalTheory.T.proj_Y_preserves_embedding_lattice _ _ hA _ _ _ hv
  rw [show (F.dJ (σ + 1) h).jX * (F.dJ (σ + 1) h).pX = rat ((F.dJ (σ + 1) h).e * (F.dJ (σ + 1) h).qX) from (rat_mul _ _).symm,
    show (F.dJ (σ + 1) h).jY * (F.dJ (σ + 1) h).pY = rat ((F.dJ (σ + 1) h).e' * (F.dJ (σ + 1) h).qY) from (rat_mul _ _).symm]
  exact ⟨latRow_mul_rat G (2 * σ + 2) _ _ (proj_adj _) hX hY hu, latRow_mul_rat G (2 * σ + 2) _ _ (proj_adj' _) hY hX hu⟩

end GlobalTheory.ProjLat

end
