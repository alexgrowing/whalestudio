import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsModerateFormAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSig
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairLatticeLocalSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicVectorLatticeLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIwasawaMajorantFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicArchimedeanEigenvectorStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory.IwHtLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem first_column_conj_product {σ : E →ₐ[F] E} {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin (r + 1)) E) :
    cT (σ : E →+* E) (col0 X) * J * col0 Y = Matrix.of fun _ _ => (cT (σ : E →+* E) X * J * Y) 0 0 := by
  ext i j
  simp [col0, cT, Matrix.mul_apply]

theorem cT_mul_swap {σ : E →ₐ[F] E} (hs : ∀ z : E, σ (σ z) = z) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) (x y : Matrix (Fin n) (Fin 1) E) :
    cT (σ : E →+* E) y * J * x = (cT (σ : E →+* E) x * J * y).map σ := by
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp only [cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, AlgHom.coe_toRingHom, map_sum, map_mul, hs,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hJ.1 k l]; ring

theorem exists_isIwaHtG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → IsHermND σ J →
      IsWittFrame σ J X Y → GlobalTheory.EisLine.IsAdapted σ J X Y L a → ∃ h : GAd σ J → ℝ, IsIwaHtG σ J (col0 X) L a h := by
  intro F E _ _ _ _ _ σ n J r X Y L a hσ hu hJ hW hA
  classical
  haveI : L.IsLattice E := hA.lat
  have hs : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hσ.2.2.2, hσ.2.2.2, star_star])
  set xc := col0 X with hxc
  set yc := col0 Y with hyc
  have hxx : cT (σ : E →+* E) xc * J * xc = 0 := by
    rw [hxc, first_column_conj_product, hW.xx]; ext i j; simp
  have hyy : cT (σ : E →+* E) yc * J * yc = 0 := by
    rw [hyc, first_column_conj_product, hW.yy]; ext i j; simp
  have hxy : cT (σ : E →+* E) xc * J * yc = 1 := by
    rw [hxc, hyc, first_column_conj_product, hW.xy]; ext i j; rw [Subsingleton.elim i j]; simp
  have hyx : cT (σ : E →+* E) yc * J * xc = 1 := by
    rw [cT_mul_swap hs hJ, hxy]; ext i j; rw [Subsingleton.elim i j]; simp
  obtain ⟨h, hh⟩ := GlobalTheory.EisLineModel.exists_h_levelAll hσ hyx L a
  refine ⟨h, fun g => ?_, hh⟩
  have loc : ∀ v (y : GLoc σ J v), ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ y = q * k ∧
      ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * xc.map (inclR (F := F) (Fv F v)) =
        xc.map (inclR (F := F) (Fv F v)) * β.1 := fun v y =>
    if hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v then
      GlobalTheory.T.hyperbolic_pair_lattice_local_split F E σ hσ n J hJ xc yc hxx hyy hxy hyx L hA.lat v hv (hA.dual v) y
    else GlobalTheory.T.isotropic_vector_lattice_local F E σ hσ hu n J hJ xc yc hxx hyx L hA.lat v hv (hA.dual v) y
  choose qa ka hka hga βa hβa using fun w => GlobalTheory.T.archimedean_iwasawa_majorant_frame F E σ hσ n J hJ xc yc hxx hyx a hA.maj w
    (projArch σ J w g)
  choose qf kf hkf hgf βf hβf using fun v => loc v (proj σ J v g)
  set S := (Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc σ J L g)).toFinset with hS
  obtain ⟨pa, hpa1, hpa2⟩ := GlobalTheory.IwLine.exists_arch_comp σ J qa
  obtain ⟨pf, hpf1, hpf2⟩ := GlobalTheory.IwLine.exists_fin_comp σ J qf S
  set p := pa * pf with hp
  have pA : ∀ w, projArch σ J w p = qa w := fun w => by rw [hp, map_mul, hpa2 w, hpf1 w, mul_one]
  have pF : ∀ v, proj σ J v p = if v ∈ S then qf v else 1 := fun v => by rw [hp, map_mul, hpa1 v, hpf2 v, one_mul]
  obtain ⟨l, hl⟩ := GlobalTheory.T.parabolic_archimedean_eigenvector F E σ n J xc (cT (σ : E →+* E) yc * J) hyx p
    (fun w => ⟨βa w, by rw [pA w]; exact hβa w⟩) (fun v => by
      rw [pF v]
      split_ifs
      · exact ⟨βf v, hβf v⟩
      · exact ⟨1, by simp⟩)
  refine ⟨p, l, hl, p⁻¹ * g, mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩, by rw [mul_inv_cancel_left]⟩
  · have e1 : proj σ J v (p⁻¹ * g) = (if v ∈ S then qf v else 1)⁻¹ * proj σ J v g := by
      rw [map_mul, map_inv, pF v]
    rw [e1]
    split_ifs with hv
    · rw [hgf v, inv_mul_cancel_left]; exact hkf v
    · rw [inv_one, one_mul]
      by_contra hc
      exact hv ((Set.Finite.mem_toFinset _).2 hc)
  · have e : projArch σ J w (p⁻¹ * g) = ka w := by
      rw [map_mul, map_inv, pA w, hga w, inv_mul_cancel_left]
    rw [e]; exact hka w

end GlobalTheory.IwHtLine
