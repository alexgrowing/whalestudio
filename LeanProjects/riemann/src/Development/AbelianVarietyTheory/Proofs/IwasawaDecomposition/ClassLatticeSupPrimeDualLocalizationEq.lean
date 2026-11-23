import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemLatticeOfMemCompletionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCompletionMapsDualLatticesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeUnramifiedUniformizerStatement

noncomputable section

namespace GlobalTheory.LevelHecke

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem nsmul_latS_of_nsmul {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (L M : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ z ∈ M, T • z ∈ L) (w : Fin n → E ⊗[F] v.adicCompletion F)
    (hw : w ∈ latS (F := F) (v.adicCompletion F) (intV E v) M) :
    T • w ∈ latS (F := F) (v.adicCompletion F) (intV E v) L := by
  have key : ∀ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) M,
      T • x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L := by
    intro x hx
    unfold latS at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨T • z, h z hz, ?_⟩
      funext i
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  exact key w hw

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem nsmul_dual_mem_loc {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (hJ : IsUnit J.det)
    (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hy : y ∈ UPts σ J (v.adicCompletion F))
    (hyl : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔
      (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb)
    (z : Fin n → E) (hz : z ∈ dualL (σ : E →+* E) J L) :
    ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • T • z ∈ L := by
  have hLb : Submodule.IsLattice E S.Lb := ⟨Module.Finite.iff_fg.mp S.Lb_fin, S.Lb_span⟩

  have hT : ∀ x ∈ dualL (σ : E →+* E) J S.Lb, T • x ∈ S.Lb := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => rw [← Nat.cast_smul_eq_nsmul E]; exact S.Lb_dual x hx
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  have hdual := GlobalTheory.T.unitary_completion_maps_dualLattices F E σ n J v L S.Lb y hJ hL hLb hy hyl
  have h1 : (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J L) :=
    Submodule.subset_span ⟨z, hz, rfl⟩
  have h2 := nsmul_latS_of_nsmul v T S.Lb (dualL (σ : E →+* E) J S.Lb) hT _ ((hdual _).mp h1)
  rw [← Matrix.mulVec_smul] at h2
  have h3 := (hyl _).mpr h2
  have h4 : (fun a => inclE (F := F) (v.adicCompletion F) ((T • z) a)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) L := by
    convert h3 using 1
    funext a
    simp
  exact GlobalTheory.T.exists_smul_mem_lattice_of_mem_completion F E v n L hL (T • z) h4

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem nsmul_dual_mem_loc_adelic {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (hJ : IsUnit J.det)
    (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hyl : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔
      (y.1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb)
    (z : Fin n → E) (hz : z ∈ dualL (σ : E →+* E) J L) :
    ∃ r : 𝓞 F, r ∉ v.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) r • T • z ∈ L := by
  have hloc : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔
      ((bc (prV (E := E) v) y.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
    intro x
    rw [← map_inv]
    exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.rlv_yloc v y.1 hyl x
  exact nsmul_dual_mem_loc S hJ v L hL _ (Formalism.UG.P.afsplit_bc_mem σ J v y.1 y.2) hloc z hz

end Core

theorem loc_sup_ker_smul {R V k : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k] (res : R →+* k) (t : R)
    (hu : Unram res t) (M N : Submodule R V) (h : ∀ z ∈ N, t • z ∈ loc res M) :
    loc res (M ⊔ RingHom.ker res • N) = loc res M := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_loc res _ x).mp hx
    have hle : M ⊔ RingHom.ker res • N ≤ loc res M := by
      refine sup_le (le_loc res M) ?_
      rw [Submodule.smul_le]
      intro a ha z hz
      obtain ⟨s', b, hs', hsab⟩ := hu.2 a (RingHom.mem_ker.mp ha)
      apply loc_sat res M s' _ hs'
      rw [smul_smul, hsab, mul_comm, ← smul_smul]
      exact Submodule.smul_mem _ b (h z hz)
    exact loc_sat res M s x hs (hle hsx)
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_loc res M x).mp hx
    exact (mem_loc res _ x).mpr ⟨s, hs, Submodule.mem_sup_left hsx⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem loc_lk_eq_loc_cls : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i), loc (A.res v) (Lk A i hi v c) = loc (A.res v) (clsCrd D u i hi c) := by
  intro D u A i hi K v c
  refine loc_sup_ker_smul (A.res v) (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) (GlobalTheory.T.levelPrime_unramifiedUniformizer D u A v) _ _ ?_
  intro z hz
  obtain ⟨r, hr, hrz⟩ := nsmul_dual_mem_loc_adelic K.lev (bwB_gramN_det D i hi) (A.eV v).1
    (clsCrd D u i hi c) (bwB_clsCrd_lat D u i hi c) (K.y c) (K.y_lat c) z hz
  refine (mem_loc _ _ _).mpr ⟨algebraMap _ _ r, fun h0 => hr ((A.res_v v r).mpr h0), ?_⟩
  rwa [Nat.cast_smul_eq_nsmul]

end GlobalTheory.LevelHecke

end
