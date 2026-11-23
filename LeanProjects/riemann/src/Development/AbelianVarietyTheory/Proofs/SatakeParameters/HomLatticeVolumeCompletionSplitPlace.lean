import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumberFieldCompletionRingEquivOfDenseUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemClosureIffMapMemMatrixHomLatticeCompletionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdealMulHomMapMemMatrixHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixHomLatticeLeSpanIdealHomImageStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RelIndexMatrixHomLatticeRatioEqResiduePowStatement

noncomputable section

namespace GlobalTheory.VolAt

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix

theorem latAt_lattice {p : ℕ} [Fact p.Prime] (X : Sys p) (v : X.Pl) (j : ℕ) (L : (X.Pj j).Tup)
    (hL : (X.Pj j).IsLatTup L) :
    ∃ g : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v), IsUnit g.det ∧
      X.latAt v j L = colSpan (X.G.P.W v) g ∧ len X v j L = -ordP (X.G.P.W v) p g.det := by
  have hS := X.G.P.setting v
  haveI := hS.frac_alt
  cases j with
  | zero =>
    have h0 : IsLattice (X.G.P.W v) (X.latAt v 0 L) := hL v
    obtain ⟨g, hg, hL'⟩ := h0
    refine ⟨g, hg, hL', ?_⟩
    change lenLat (X.G.P.W v) p (X.latAt v 0 L) = _
    rw [hL']
    exact lenLat_colSpan hS.p_unif g hg
  | succ j =>
    have h0 : IsLattice (X.G.P.W v) (X.latAt v (j + 1) L) := hL v
    obtain ⟨g, hg, hL'⟩ := h0
    refine ⟨g, hg, hL', ?_⟩
    change lenLat (X.G.P.W v) p (X.latAt v (j + 1) L) = _
    rw [hL']
    exact lenLat_colSpan hS.p_unif g hg

theorem Pj_m_succ {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) : (X.Pj j).m + 1 = NN X.G.P.m X.t j := by
  cases j with
  | zero => simp [NN, Sys.Pj, Fills.Pj]
  | succ j =>
    simp only [NN, Sys.Pj, Fills.Pj, Places.withWt, Sys.t]
    ring

theorem homLat_conj {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (M g : Matrix (Fin k) (Fin k) Qq) (M' g' : Matrix (Fin k') (Fin k') Qq) (hM' : IsUnit M'.det)
    (z : Matrix (Fin k') (Fin k) Qq) :
    z ∈ homLat W (colSpan W (M * g)) (colSpan W (M' * g')) ↔
      ∀ y ∈ colSpan W g, (M'⁻¹ * z * M) *ᵥ y ∈ colSpan W g' := by
  rw [← colSpan_mul, ← colSpan_mul, mem_homLat]
  have hinv : M'⁻¹ * M' = 1 := Matrix.nonsing_inv_mul M' hM'
  have hinv' : M' * M'⁻¹ = 1 := Matrix.mul_nonsing_inv M' hM'
  constructor
  · intro h y hy
    obtain ⟨u, hu, hu'⟩ := h (M *ᵥ y) (Submodule.mem_map_of_mem hy)
    have e : (M'⁻¹ * z * M) *ᵥ y = u := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have : z *ᵥ (M *ᵥ y) = M' *ᵥ u := hu'.symm
      rw [this, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [e]
    exact hu
  · rintro h _ ⟨y, hy, rfl⟩
    have e : z *ᵥ ((M.mulVecLin.restrictScalars W) y) = M' *ᵥ ((M'⁻¹ * z * M) *ᵥ y) := by
      change z *ᵥ (M *ᵥ y) = _
      simp only [Matrix.mulVec_mulVec]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hinv', Matrix.one_mul]
    rw [e]
    exact Submodule.mem_map_of_mem (h y hy)

theorem vol_main : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (v : X.Pl) (j : ℕ) (ρ : D.host.E →+* X.G.P.Qq v) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) → (∀ x : 𝓞 D.host.E, ∃ y : X.G.P.W v, ρ x = algebraMap _ _ y ∧ (x ∈ P.asIdeal ↔ (p : X.G.P.W v) ∣ y)) → (∀ (y : X.G.P.W v) (n : ℕ), ∃ (x : 𝓞 D.host.E) (z : X.G.P.W v), ρ x = algebraMap _ _ (y + (p : X.G.P.W v) ^ n * z)) → ∃ φ : GL3Theta.EP D P ≃+* X.G.P.Qq v, (∀ x : D.host.E, φ (algebraMap _ _ x) = ρ x) ∧ ∀ (M : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (M' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)), IsUnit M.det → IsUnit M'.det → ∀ (N : (X.Pj j).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E)) (N' : (X.Pj (j + 1)).Tup → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E)) (S : Set ((X.Pj j).Tup × (X.Pj (j + 1)).Tup)), (∀ q ∈ S, (X.Pj j).IsLatTup q.1 ∧ (X.Pj (j + 1)).IsLatTup q.2 ∧ TaylorLogMetric.admitted D _ _ (N q.1) (N' q.2) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N q.1 : Set (Fin ((X.Pj j).m + 1) → D.host.E))) = (X.latAt v j q.1).map ((M.mulVecLin).restrictScalars (X.G.P.W v)) ∧ Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N' q.2 : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) = (X.latAt v (j + 1) q.2).map ((M'.mulVecLin).restrictScalars (X.G.P.W v))) → ∀ q ∈ S, (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ X.ind v j q.1 q.2 (M'⁻¹ * y.map φ * M) = 1) ∧ ∀ q₀ ∈ S, GL3Theta.volP (GL3Theta.YP D P (N q₀.1) (N' q₀.2)) (GL3Theta.YP D P (N q.1) (N' q.2)) = (p : ℝ) ^ ((X.G.P.n' v : ℤ) * (volE X v j q.1 q.2 - volE X v j q₀.1 q₀.2)) := by
  intro D p _ X v j ρ P hA h1 h2
  have hS := X.G.P.setting v
  haveI := hS.frac_alt
  obtain ⟨φ, hφ, hop, hnb⟩ := GlobalTheory.T.numberField_completion_ringEquiv_of_dense_unramified P p hS.p_unif hS.eq_sum_herm_smul_frame_of_inW ρ h1 h2
  refine ⟨φ, hφ, ?_⟩
  intro M M' hM hM' N N' S hSq
  have key : ∀ q ∈ S, ∃ (g : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
      (g' : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)),
      IsUnit (M * g).det ∧ IsUnit (M' * g').det ∧
      (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ y.map φ ∈ homLat (X.G.P.W v) (colSpan (X.G.P.W v) (M * g))
        (colSpan (X.G.P.W v) (M' * g'))) ∧
      (∀ z, X.ind v j q.1 q.2 (M'⁻¹ * z * M) = 1 ↔ z ∈ homLat (X.G.P.W v) (colSpan (X.G.P.W v) (M * g))
        (colSpan (X.G.P.W v) (M' * g'))) ∧
      ordP (X.G.P.W v) p (M * g).det = ordP (X.G.P.W v) p M.det - len X v j q.1 ∧
      ordP (X.G.P.W v) p (M' * g').det = ordP (X.G.P.W v) p M'.det - len X v (j + 1) q.2 := by
    intro q hq
    obtain ⟨hL, hL', hAdm, hsp, hsp'⟩ := hSq q hq
    obtain ⟨g, hg, hgL, hlen⟩ := latAt_lattice X v j q.1 hL
    obtain ⟨g', hg', hgL', hlen'⟩ := latAt_lattice X v (j + 1) q.2 hL'
    have hMg : IsUnit (M * g).det := by rw [Matrix.det_mul]; exact hM.mul hg
    have hMg' : IsUnit (M' * g').det := by rw [Matrix.det_mul]; exact hM'.mul hg'
    have hNa : Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N q.1 : Set (Fin ((X.Pj j).m + 1) → D.host.E))) =
        colSpan (X.G.P.W v) (M * g) := by rw [hsp, hgL, colSpan_mul]
    have hNb : Submodule.span (X.G.P.W v) ((fun x k => ρ (x k)) '' (N' q.2 : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) =
        colSpan (X.G.P.W v) (M' * g') := by rw [hsp', hgL', colSpan_mul]
    obtain ⟨-, -, ⟨hFG, hspan, -⟩, ⟨hFG', hspan', -⟩⟩ := hAdm
    refine ⟨g, g', hMg, hMg', fun y => ?_, fun z => ?_, ?_, ?_⟩
    · exact GlobalTheory.T.mem_closure_iff_map_mem_matrixHomLattice_completion P p hS.p_unif ρ h2 φ hφ hop hnb (TaylorLogMetric.YYl D (N q.1) (N' q.2)) _ _ hMg hMg'
        (GlobalTheory.T.ideal_mul_hom_map_mem_matrixHomLattice D P p hS.p_unif ρ hA h1 _ _ _ _ hNa hNb)
        (GlobalTheory.T.matrixHomLattice_le_span_ideal_hom_image D P p hS.p_unif ρ hA h1 _ _ hFG hFG' hspan hspan' _ _ hMg hMg' hNa hNb) y
    · rw [homLat_conj M g M' g' hM' z, ← hgL, ← hgL']
      unfold Sys.ind
      split_ifs with h
      · exact iff_of_true rfl h
      · exact iff_of_false (by norm_num) h
    · rw [Matrix.det_mul, ordP_mul hS.p_unif hM.ne_zero hg.ne_zero, hlen]
      ring
    · rw [Matrix.det_mul, ordP_mul hS.p_unif hM'.ne_zero hg'.ne_zero, hlen']
      ring
  intro q hq
  obtain ⟨g, g', hMg, hMg', hY, hind, ho, ho'⟩ := key q hq
  refine ⟨fun y => (hY y).trans (hind _).symm, fun q₀ hq₀ => ?_⟩
  obtain ⟨g₀, g₀', hMg₀, hMg₀', hY₀, -, ho₀, ho₀'⟩ := key q₀ hq₀
  let e : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (GL3Theta.EP D P) →+
      Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) :=
    φ.toAddEquiv.toAddMonoidHom.mapMatrix
  have he : Function.Surjective e := fun z => ⟨z.map φ.symm, by ext i l; simp [e]⟩
  have hYc : ∀ (A : Submodule (X.G.P.W v) _), (∀ y, y ∈ GL3Theta.YP D P (N q.1) (N' q.2) ↔ y.map φ ∈ A) →
      GL3Theta.YP D P (N q.1) (N' q.2) = A.toAddSubgroup.comap e := fun A h => by
    ext y; exact h y
  have hYc₀ : ∀ (A : Submodule (X.G.P.W v) _), (∀ y, y ∈ GL3Theta.YP D P (N q₀.1) (N' q₀.2) ↔ y.map φ ∈ A) →
      GL3Theta.YP D P (N q₀.1) (N' q₀.2) = A.toAddSubgroup.comap e := fun A h => by
    ext y; exact h y
  have hrel : ∀ A B : AddSubgroup (Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)),
      ((A.comap e).addSubgroupOf (B.comap e)).index = A.relIndex B := fun A B => by
    change (A.comap e).relIndex (B.comap e) = _
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective he]
  unfold GL3Theta.volP
  rw [hYc _ hY, hYc₀ _ hY₀, hrel, hrel,
    GlobalTheory.T.relIndex_matrixHomLattice_ratio_eq_residue_pow p (X.G.P.n' v) hS.p_unif hS.res_card _ _ _ _ hMg₀ hMg hMg₀' hMg', ho, ho', ho₀, ho₀']
  congr 1
  unfold volE
  rw [← Pj_m_succ X j, ← Pj_m_succ X (j + 1)]
  push_cast
  ring

end GlobalTheory.VolAt
