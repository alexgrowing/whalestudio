import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LatSandwich

variable {D : D7}

theorem incA_eq (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem rat_mul_tmul_mul {k l m n : ℕ} (A : Matrix (Fin k) (Fin l) D.host.E) (X : Matrix (Fin l) (Fin m) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (p : AF D.host.F) :
    rat A ⬝ (Matrix.of fun i j => p ⊗ₜ[D.host.F] X i j : Mx D l m) ⬝ rat B =
      Matrix.of fun i j => p ⊗ₜ[D.host.F] (A * X * B) i j := by
  ext i j
  simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, incA_eq, Finset.sum_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, ← TensorProduct.tmul_sum]

theorem sandwich_hatMx {k l m n : ℕ} {M : Submodule (𝓞 D.host.E) (Matrix (Fin l) (Fin m) D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Matrix (Fin k) (Fin n) D.host.E)} (A : Matrix (Fin k) (Fin l) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (h : ∀ x ∈ M, A * x * B ∈ M') {z : Mx D l m} (hz : z ∈ hatMx M) :
    rat A ⬝ z ⬝ rat B ∈ hatMx M' := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    rw [rat_mul_tmul_mul]
    exact AddSubgroup.subset_closure ⟨α, hα, _, h x hx, rfl⟩
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem ha

theorem sandwich_homLat {k l m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin l → D.host.E)} {Λ₂ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ₂' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)} (A : Matrix (Fin k) (Fin l) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ₂') (hB : ∀ y ∈ Λ₂, B *ᵥ y ∈ Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) : ∀ x ∈ 𝔪 • homLat Λ Λ', A * x * B ∈ 𝔪 • homLat Λ₂ Λ₂' := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun r hr x hx => ?_) (fun x y hx hy => ?_)
  · have e : A * (r • x) * B = r • (A * x * B) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e]
    refine Submodule.smul_mem_smul hr fun y hy => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hA _ (hx _ (hB y hy))
  · rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy

theorem sandwich_entry {k l m n : ℕ} (A : Matrix (Fin k) (Fin l) D.host.E) (B : Matrix (Fin m) (Fin n) D.host.E)
    (a : D.host.E) (t : Fin l → D.host.E) (r : Fin m → D.host.E) (i : Fin k) (j : Fin n) :
    (A * Matrix.of (fun i j => a * t i * r j) * B) i j = a * (A *ᵥ t) i * ∑ m, r m * B m j := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sandwich_latO {S T S' T' : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {LS' : Set (Fin S'.rank → D.host.E)} {LT' : Set (Fin T'.rank → D.host.E)} (A : Matrix (Fin T'.rank) (Fin T.rank) D.host.E)
    (B : Matrix (Fin S.rank) (Fin S'.rank) D.host.E) (hA : ∀ t ∈ LT, A *ᵥ t ∈ LT')
    (hB : ∀ s ∈ LS, ∃ s' ∈ LS', ∀ j, ∑ k, star (s' k) * S'.gram k j = ∑ m, (∑ k, star (s k) * S.gram k m) * B m j)
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) {w : WO S T} (hw : w ∈ latO S T LS LT P) :
    (rat A ⬝ w ⬝ rat B : WO S' T') ∈ latO S' T' LS' LT' P := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨s', hs', e⟩ := hB s hs
    have e1 : (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
        Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
          (Matrix.of (fun i j => a * t i * ∑ k, star (s k) * S.gram k j) : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j := rfl
    rw [e1, rat_mul_tmul_mul]
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s', hs', A *ᵥ t, hA t ht, ?_⟩
    ext i j
    simp only [Matrix.of_apply]
    rw [sandwich_entry, e j]
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem ha

theorem orthogonalSumAuxiliaryVectors_frame_mulVec_mem_lattice {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {M : Matrix (Fin B.rank) (Fin A.rank) D.host.E} (hM : M = frameMat B A d.ι) {y : Fin A.rank → D.host.E} (hy : y ∈ Λ) :
    M *ᵥ y ∈ d.lat Λ 𝔟 :=
  ⟨y, hy, 0, fun p => (𝔟 p).val.zero_mem, by rw [hM, Matrix.mulVec_zero, add_zero]⟩

theorem orthogonalSumAuxiliaryVectors_projection_mem_lattice {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {M : Matrix (Fin B.rank) (Fin A.rank) D.host.E} (hM : M = frameMat B A d.ι) (hiso : Mᴴ * B.gram * M = A.gram)
    {x : Fin B.rank → D.host.E} (hx : x ∈ d.lat Λ 𝔟) : (A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ x ∈ Λ := by
  obtain ⟨y, hy, u, -, rfl⟩ := hx
  have h1 : A.gram⁻¹ * (Mᴴ * B.gram) * M = 1 := by
    rw [Matrix.mul_assoc, hiso, Matrix.nonsing_inv_mul _ (gram_isUnit_det A)]
  have h2 : A.gram⁻¹ * (Mᴴ * B.gram) * d.a = 0 := by
    have := d.perp
    rw [cT_sig, ← hM] at this
    rw [Matrix.mul_assoc, this, Matrix.mul_zero]
  rw [← hM, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, h2, Matrix.one_mulVec,
    Matrix.zero_mulVec, add_zero]
  exact hy

theorem proj_form {A B : HSp D} (M : Matrix (Fin B.rank) (Fin A.rank) D.host.E) (s : Fin B.rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) k) * A.gram k j = ∑ m, (∑ k, star (s k) * B.gram k m) * M m j := by
  have e1 : (A.gram⁻¹ * (Mᴴ * B.gram))ᴴ * A.gram = B.gram * M := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, gram_conjTranspose,
      gram_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det A),
      Matrix.mul_one]
  have e2 : (fun j => ∑ k, star (((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) k) * A.gram k j) =
      star ((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) ᵥ* A.gram := by
    funext j; simp only [Matrix.vecMul, dotProduct, Pi.star_apply]
  have e3 : (fun j => ∑ m, (∑ k, star (s k) * B.gram k m) * M m j) = (star s ᵥ* B.gram) ᵥ* M := by
    funext j; simp only [Matrix.vecMul, dotProduct, Pi.star_apply]
  have key : star ((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) ᵥ* A.gram = (star s ᵥ* B.gram) ᵥ* M := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, e1, ← Matrix.vecMul_vecMul]
  exact congrFun (e2.trans (key.trans e3.symm)) j

end GlobalTheory.LatSandwich

namespace GlobalTheory.AscFin

open GlobalTheory.LatSandwich

theorem pcBF_core_mem_latCore : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀,
    ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).1 ∈ latCore G (2 * ρ + 1) := by
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h u hu
  simp only [pcBF, piecesOf, AddSubgroup.mem_comap, AddMonoidHom.coe_comp, Function.comp_apply] at hu
  rw [OrthDec.resS_apply]

  have key : rat (F.dJ ρ h).q0 ⬝ (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ⬝ rat ((F.dB ρ h).i₀ * (F.oB ρ h).iA) =
      u ⬝ (F.oB ρ h).jA := by
    rw [rat_mul, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply]
    change (F.dJ ρ h).p0 ⬝ ((F.dJ ρ h).j0 ⬝ u ⬝ (F.dB ρ h).p0) ⬝ ((F.dB ρ h).j0 ⬝ (F.oB ρ h).jA) = _
    simp only [← Matrix.mul_assoc]
    rw [HypDec.p0_j0, Matrix.one_mul, Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [← key]

  have lat1 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  have lat2 : G.Λ (.grid (2 * ρ + 2) 0) = (G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := G.sp.colLat (2 * ρ + 2) (by omega) h
  have iso2 : ((F.dB ρ h).i₀ * (F.oB ρ h).iA)ᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * ((F.dB ρ h).i₀ * (F.oB ρ h).iA) =
      (G.V (.core (2 * ρ + 2))).gram := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (F.oB ρ h).iAᴴ * ((F.dB ρ h).i₀ᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * (F.dB ρ h).i₀) * (F.oB ρ h).iA := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [(F.dB ρ h).iso, (F.oB ρ h).isoA]

  have hA : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), (F.dJ ρ h).q0 *ᵥ t ∈ G.Λ (.core (2 * ρ + 1)) := fun t ht =>
    orthogonalSumAuxiliaryVectors_projection_mem_lattice _ _ _ (hF.aJ ρ h) (F.dJ ρ h).iso (lat1 ▸ ht)

  have hB1 : ∀ y ∈ G.Λ (.core (2 * ρ + 2)), ((F.dB ρ h).i₀ * (F.oB ρ h).iA) *ᵥ y ∈ G.Λ (.grid (2 * ρ + 2) 0) :=
    fun y hy => lat2 ▸ orthogonalSumAuxiliaryVectors_frame_mulVec_mem_lattice _ _ _ (hF.aB ρ h) hy

  have hB : ∀ s ∈ (G.Λ (.grid (2 * ρ + 2) 0) : Set (Fin (negSp (G.V (.grid (2 * ρ + 2) 0))).rank → D.host.E)),
      ∃ s' ∈ (G.Λ (.core (2 * ρ + 2)) : Set (Fin (negSp (G.V (.core (2 * ρ + 2)))).rank → D.host.E)), ∀ j,
        ∑ k, star (s' k) * (negSp (G.V (.core (2 * ρ + 2)))).gram k j =
          ∑ m, (∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k m) * ((F.dB ρ h).i₀ * (F.oB ρ h).iA) m j := by
    intro s hs
    rw [SetLike.mem_coe, lat2] at hs
    refine ⟨_, orthogonalSumAuxiliaryVectors_projection_mem_lattice _ _ _ (hF.aB ρ h) iso2 hs, fun j => ?_⟩
    simp only [negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_mul]
    rw [proj_form]
  have hu1 : (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ∈ latO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) := hu.1
  have hu2 : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ∈
      hatMx (G.modul • homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) := hu.2
  refine ⟨?_, fun e he => ?_⟩
  · have h1 := sandwich_latO (S' := negSp (G.V (.core (2 * ρ + 2)))) (T' := G.V (.core (2 * ρ + 1)))
      (LS' := (G.Λ (.core (2 * ρ + 2)) : Set _)) (LT' := (G.Λ (.core (2 * ρ + 1)) : Set _)) _ _ hA hB _ hu1
    exact h1
  · have h2 := sandwich_hatMx _ _ (sandwich_homLat _ _ hA hB1 G.modul) (hu2 e he)
    rw [Matrix.mul_smul, Matrix.smul_mul] at h2
    exact h2

end GlobalTheory.AscFin
