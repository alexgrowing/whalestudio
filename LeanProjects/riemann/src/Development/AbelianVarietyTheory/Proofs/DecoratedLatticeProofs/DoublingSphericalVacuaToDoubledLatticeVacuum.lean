import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause resL resR)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.VacBox

variable {D : D7}

theorem gram_dbl_inv (A : HSp D) : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) :=
  Matrix.inv_eq_left_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (isHermND_gram A).2.isUnit, blkMat_one])

theorem hO_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    hO (dblSp A) B x y = hO A B (resL A B x) (resL A B y) - hO A B (resR A B x) (resR A B y) := by
  simp only [hO]
  rw [gram_dbl_inv]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, resL, resR, Matrix.of_apply,
    blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
    map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem hO_neg_neg (A B : HSp D) (x y : WO A B) : hO A B (-x) (-y) = hO A B x y := by
  simp only [hO, Matrix.neg_apply, map_neg, mul_neg, neg_mul, neg_neg]

theorem symplOH_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    symplOH (dblSp A) B x y = symplOH A B (resL A B x) (resL A B y) - symplOH A B (resR A B x) (resR A B y) := by
  simp only [symplOH, symplO, hO_dbl, mul_sub, map_sub]

theorem symplOH_neg_neg (A B : HSp D) (x y : WO A B) : symplOH A B (-x) (-y) = symplOH A B x y := by
  simp only [symplOH, symplO, hO_neg_neg]

theorem resL_add (A B : HSp D) (x y : WO (dblSp A) B) : resL A B (x + y) = resL A B x + resL A B y :=
  Matrix.ext fun _ _ => rfl

theorem resR_add (A B : HSp D) (x y : WO (dblSp A) B) : resR A B (x + y) = resR A B x + resR A B y :=
  Matrix.ext fun _ _ => rfl

def resLHom (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resL A B
  map_zero' := Matrix.ext fun _ _ => rfl
  map_add' := resL_add A B

def resRHom (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resR A B
  map_zero' := Matrix.ext fun _ _ => rfl
  map_add' := resR_add A B

theorem conj_psi_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (z : AF D.host.F) :
    conj (ψ z) = ψ (-z) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ, one_pow, inv_one, Complex.ofReal_one,
    mul_one]

theorem heisO_delta {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (A B : HSp D) (w₀ : WO (dblSp A) B)
    (f₁ f₂ : WO A B → ℂ) :
    heisO ψ (dblSp A) B w₀ (delta A B f₁ f₂) =
      delta A B (heisO ψ A B (resL A B w₀) f₁) (heisO ψ A B (-resR A B w₀) f₂) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, resL_add, resR_add, map_mul, conj_psi_eq hψ, symplOH_dbl, symplOH_neg_neg, neg_add]
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

theorem sum_dbl_gram_inl (A : HSp D) (s : Fin (dblSp A).rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (s k) * (dblSp A).gram k (finSumFinEquiv (Sum.inl j)) =
      ∑ k, star ((fun k => s (finSumFinEquiv (Sum.inl k))) k) * A.gram k j := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]

theorem sum_dbl_gram_inr (A : HSp D) (s : Fin (dblSp A).rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (s k) * (dblSp A).gram k (finSumFinEquiv (Sum.inr j)) =
      ∑ k, star ((-fun k => s (finSumFinEquiv (Sum.inr k))) k) * A.gram k j := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, Matrix.neg_apply, Pi.neg_apply, star_neg, mul_neg, neg_mul]

theorem res_mem_latO {A B : HSp D} {LA : Lat A} {LB : Lat B} {P : FinPl D → Prop} {u : WO (dblSp A) B}
    (hu : u ∈ latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB P) :
    resL A B u ∈ latO A B LA LB P ∧ resR A B u ∈ latO A B LA LB P := by
  have key : latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB P ≤
      (latO A B LA LB P).comap (resLHom A B) ⊓ (latO A B LA LB P).comap (resRHom A B) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    refine ⟨AddSubgroup.subset_closure
      ⟨α, hα, hP, a, ha, fun k => s (finSumFinEquiv (Sum.inl k)), hs.1, t, ht, ?_⟩,
      AddSubgroup.subset_closure
      ⟨α, hα, hP, a, ha, -fun k => s (finSumFinEquiv (Sum.inr k)), neg_mem hs.2, t, ht, ?_⟩⟩
    · ext i j
      simp only [resLHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, resL, Matrix.of_apply]
      exact congrArg (fun z => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * z)) (sum_dbl_gram_inl A s j)
    · ext i j
      simp only [resRHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, resR, Matrix.of_apply]
      exact congrArg (fun z => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * z)) (sum_dbl_gram_inr A s j)
  exact key hu

theorem latO_mono_at {A B : HSp D} (LA : Lat A) (LB : Lat B) {Sf : Finset (FinPl D)} {v : FinPl D} (hv : v ∉ Sf) :
    latO A B LA LB (fun u => u = v) ≤ latO A B LA LB (fun u => u ∉ Sf) := by
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, hP, rest⟩
  refine ⟨α, hα, fun v' hv' => hP v' fun h => hv' (h ▸ hv), rest⟩

theorem pair_dbl (A : HSp D) (x y : Fin (dblSp A).rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * (dblSp A).gram i j * y j =
      (∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inl i))) * A.gram i j * y (finSumFinEquiv (Sum.inl j))) -
      ∑ i, ∑ j, star (x (finSumFinEquiv (Sum.inr i))) * A.gram i j * y (finSumFinEquiv (Sum.inr j)) := by
  rw [gram_hdbl]
  simp only [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, dblGram, blkMat, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem selfDual_sumLat {A : HSp D} {L : Lat A} (hL : IsSelfDualC A L) :
    IsSelfDualC (dblSp A) (sumLat finSumFinEquiv L L) := by
  haveI := hL.1
  refine ⟨isLattice_sumLat L L, fun y => ⟨fun hy x hx => ?_, fun H => ?_⟩⟩
  · obtain ⟨b₁, hb₁⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inl i)))).1 hy.1
      (fun i => x (finSumFinEquiv (Sum.inl i))) hx.1
    obtain ⟨b₂, hb₂⟩ := (hL.2 (fun i => y (finSumFinEquiv (Sum.inr i)))).1 hy.2
      (fun i => x (finSumFinEquiv (Sum.inr i))) hx.2
    refine ⟨b₁ - b₂, ?_⟩
    rw [pair_dbl]
    push_cast
    linear_combination hb₁ - hb₂
  · refine ⟨(hL.2 _).2 fun x hx => ?_, (hL.2 _).2 fun x hx => ?_⟩
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv x 0) ((pairVec_mem_sumLat _).2 ⟨hx, zero_mem _⟩)
      rw [pair_dbl] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, sub_zero] at hb
      refine ⟨b, ?_⟩
      show (b : D.host.E) = ∑ i, ∑ j, star (x i) * A.gram i j * y (finSumFinEquiv (Sum.inl j))
      exact hb
    · obtain ⟨b, hb⟩ := H (pairVec finSumFinEquiv 0 x) ((pairVec_mem_sumLat _).2 ⟨zero_mem _, hx⟩)
      rw [pair_dbl] at hb
      simp only [pairVec_inl, pairVec_inr, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_sub] at hb
      refine ⟨-b, ?_⟩
      show ((-b : 𝓞 D.host.E) : D.host.E) = ∑ i, ∑ j, star (x i) * A.gram i j * y (finSumFinEquiv (Sum.inr j))
      push_cast
      linear_combination -hb

theorem doubling_isLatVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (LA : Lat A) (LB : Lat B), IsStdChar D ψ (-1) → IsSelfDualC A LA → IsSelfDualC (dblSp A) (sumLat finSumFinEquiv LA LA) ∧ ∀ (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsSphOff ψ A B LA LB Sf Φ₁ → IsSphOff ψ A B LA LB Sf Φ₂ → ∀ v ∉ Sf, IsLatVac (heisO ψ (dblSp A) B) (latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB fun u => u = v) (delta A B Φ₁ Φ₂) := by
  intro D ψ A B LA LB hψ hLA
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  refine ⟨selfDual_sumLat hLA, ?_⟩
  intro Sf Φ₁ Φ₂ h₁ h₂ v hv
  have mono := latO_mono_at LA LB hv
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · obtain ⟨hL, hR⟩ := res_mem_latO hu
    have eL : resL A B (2 • u) = 2 • resL A B u := by rw [two_nsmul, two_nsmul, resL_add]
    have eR : -resR A B (2 • u) = 2 • (-resR A B u) := by
      rw [two_nsmul, two_nsmul, resR_add, neg_add]
    rw [heisO_delta hn, eL, eR, h₁.1 _ (mono hL), h₂.1 _ (neg_mem (mono hR))]
  · obtain ⟨hL, hR⟩ := res_mem_latO hu
    have hhL : IsHalf e (resL A B u) := fun i j => hh i (finSumFinEquiv (Sum.inl j))
    have hhR : IsHalf e (-resR A B u) := fun i j => by
      show e * -(u i (finSumFinEquiv (Sum.inr j))) = -(u i (finSumFinEquiv (Sum.inr j)))
      rw [mul_neg, hh]
    rw [heisO_delta hn, h₁.2 e he _ (mono hL) hhL, h₂.2 e he _ (neg_mem (mono hR)) hhR]

end GlobalTheory.Core.Rk.VacBox
