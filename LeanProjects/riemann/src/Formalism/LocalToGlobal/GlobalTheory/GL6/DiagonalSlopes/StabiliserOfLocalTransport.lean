import Formalism.LocalToGlobal.GlobalTheory.GL6.PKerAtP
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero

noncomputable section

open NumberField Ideal IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.L2.Forms Matrix Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

section Gen

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem class_lattice_le_dual (K : ClsTied u i hi) (c : (D.mem u).C.cls i) : clsCrd D u i hi c ≤ Ld D u i hi c := by
  intro x hx
  apply Submodule.subset_span
  intro x' hx'
  have hglob : ∀ z ∈ clsCrd D u i hi c, z ∈ Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb := by
    intro z hz
    exact (K.y_lat c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hm : ∀ a ∈ K.lev.Lb, ∀ b ∈ K.lev.Lb,
      IsIntegral ℤ (((1 : ℤ) : D.host.E) * Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b) := by
    intro a ha b hb
    obtain ⟨r, hr⟩ := K.lev.Lb_int b hb a ha
    rw [Int.cast_one, one_mul, ← hr]
    exact RingOfIntegers.isIntegral_coe r
  have h := Formalism.UG.P.csScale_glob (sigD D) (gramN D i hi) K.lev.Lb 1 hm (K.y c).1
    (K.y c).2 (hglob x' hx') (hglob x hx)
  rw [Int.cast_one, one_mul] at h
  exact bwL_descent _ _ _ h

set_option maxHeartbeats 1000000 in

theorem dual_base_lattice_full (K : ClsTied u i hi) :
    Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb) := by
  have hLb : Submodule.IsLattice D.host.E K.lev.Lb :=
    ⟨Module.Finite.iff_fg.1 K.lev.Lb_fin, K.lev.Lb_span⟩
  have := Formalism.L2.GlobalTheoryTheory.TraceIntegrality.isLattice_between K.lev.Lb
    (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb) hLb
    (fun x hx => Submodule.subset_span (K.lev.Lb_int x hx)) _ (D.mem u).A.T_prime.ne_zero (by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact K.lev.Lb_dual x hx
      | zero => rw [smul_zero]; exact zero_mem _
      | add x z _ _ hx hz => rw [smul_add]; exact add_mem hx hz
      | smul b x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ b hx)
  exact ⟨Module.Finite.iff_fg.2 this.fg, this.span_eq_top⟩

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem dual_class_lattice_eq_global (K : ClsTied u i hi) (c : (D.mem u).C.cls i) :
    Ld D u i hi c = Formalism.UG.CS.globLat (K.y c).1
      (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb) := by
  have hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat K.lev.Lb := ⟨K.lev.Lb_fin, K.lev.Lb_span⟩
  have hLc := tld_isLat (D := D) (u := u) i hi c
  have hLd : Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) (clsCrd D u i hi c)) := by
    refine ⟨Module.Finite.iff_fg.2 ((rlv_coordFacts (D := D) (u := u) i hi).2.1 c), ?_⟩
    rw [eq_top_iff, ← hLc.2]
    exact Submodule.span_mono (fun x hx => class_lattice_le_dual K c hx)
  have hg := (K.y c).2
  have hc : clsCrd D u i hi c = Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb :=
    Formalism.L2.GlobalTheoryTheory.Comp.eq_glob_of_hat hLc _ (fun x => K.y_lat c x)
  apply le_antisymm
  · have hle1 := Formalism.L2.GlobalTheoryTheory.Comp.glob_dl_le (sigD D) (gramN D i hi) (clsCrd D u i hi c) (K.y c).1⁻¹
      (inv_mem hg)
    have e1 : Formalism.UG.CS.globLat (K.y c).1⁻¹ (clsCrd D u i hi c) = K.lev.Lb := by
      rw [hc]; exact Formalism.L2.GlobalTheoryTheory.Comp.glob_glob_inv hLb _
    rw [e1] at hle1
    have h2 := Formalism.L2.GlobalTheoryTheory.Comp.glob_mono (K.y c).1 hle1
    rwa [Formalism.L2.GlobalTheoryTheory.Comp.glob_inv_glob hLd] at h2
  · have h := Formalism.L2.GlobalTheoryTheory.Comp.glob_dl_le (sigD D) (gramN D i hi) K.lev.Lb (K.y c).1 hg
    rw [← hc] at h
    exact h

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem mem_local_dual_lattice_iff (K : ClsTied u i hi) (c : (D.mem u).C.cls i)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Ld D u i hi c) ↔
      ((bc (prV (E := D.host.E) v) (K.y c).1⁻¹ : GL (Fin (D.R.N i)) _) :
          Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) _) *ᵥ x ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
          (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb) :=
  rlv_yloc v (K.y c).1 (fun x => by
    rw [dual_class_lattice_eq_global K c]
    exact Formalism.L2.GlobalTheoryTheory.Comp.mem_hat_glob (dual_base_lattice_full K) _ x) x

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem mem_local_dual_lattice_iff' (K : ClsTied u i hi) (c : (D.mem u).C.cls i) (v : HeightOneSpectrum (𝓞 D.host.F))
    (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Ld D u i hi c) ↔
      (((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹ : GL (Fin (D.R.N i)) _) :
          Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) _) *ᵥ x ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
          (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb) := by
  simpa only [map_inv] using mem_local_dual_lattice_iff K c v x

end Gen

section Fun

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

set_option maxHeartbeats 20000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem local_dual_lattice_transport {A : AtTTied u} (K : ClsTied u i hi) (L : LvTied u A i hi)
    (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (hfv : FvTie L K fMe)
    (v : (D.mem u).A.vT) (c c2 : (D.mem u).C.cls i) (Γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
    (hF : ∀ z (hz : z ∈ Ld D u i hi c2), ∃ a : 𝓞 D.host.F, a ∉ (A.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • (Γ *ᵥ z) ∈ Ld D u i hi c,
        (D.fm u).fv i v c (L.pr v c ⟨_, h⟩) =
          (D.fm u).fv i v c2 (L.pr v c2 ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • z,
            Submodule.smul_mem _ _ hz⟩)) :
    ∀ z ∈ Ld D u i hi c2, ∃ a : 𝓞 D.host.F, a ∉ (A.eV v).1.asIdeal ∧
      (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • (Γ *ᵥ z) ∈ Ld D u i hi c ∧
      ∀ (h1 : (((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹ : GL (Fin (D.R.N i)) _) :
            Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) _) *ᵥ
          (fun k => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F)
            (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • (Γ *ᵥ z)) k)) ∈
          latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
            (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb))
        (h2 : (((bc (prV (E := D.host.E) (A.eV v).1) (K.y c2).1)⁻¹ : GL (Fin (D.R.N i)) _) :
            Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) _) *ᵥ
          (fun k => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F)
            (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • z) k)) ∈
          latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
            (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb)),
        K.lev.fT (A.eV v).1 (A.eV v).2 ⟨_, h1⟩ = K.lev.fT (A.eV v).1 (A.eV v).2 ⟨_, h2⟩ := by
  intro z hz
  obtain ⟨a, ha, h, hfa⟩ := hF z hz
  exact ⟨a, ha, h, fun h1 h2 => (fMe v).injective
    ((hfv v c ⟨_, h⟩ h1).symm.trans (hfa.trans (hfv v c2 ⟨_, Submodule.smul_mem _ _ hz⟩ h2)))⟩

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem stabiliser_of_local_transport {A : AtTTied u} (K : ClsTied u i hi) (L : LvTied u A i hi)
    (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (hfv : FvTie L K fMe)
    (v : (D.mem u).A.vT) (c c2 : (D.mem u).C.cls i) (Γ : GL (Fin (D.R.N i)) D.host.E)
    (hst : bc (prV (E := D.host.E) (A.eV v).1) ((K.y c).1⁻¹ *
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ * (K.y c2).1) ∈
      stabGL (latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
        (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb)))
    (hF : ∀ z (hz : z ∈ Ld D u i hi c2), ∃ a : 𝓞 D.host.F, a ∉ (A.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • ((Γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ z) ∈
          Ld D u i hi c,
        (D.fm u).fv i v c (L.pr v c ⟨_, h⟩) =
          (D.fm u).fv i v c2 (L.pr v c2 ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • z,
            Submodule.smul_mem _ _ hz⟩)) :
    bc (prV (E := D.host.E) (A.eV v).1) ((K.y c).1⁻¹ *
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ * (K.y c2).1) ∈
      stabFun (latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
        (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb))
        (K.lev.fT (A.eV v).1 (A.eV v).2) :=
  sf_two (F := D.host.F) (E := D.host.E) (A.eV v).1 (Ld D u i hi c) (Ld D u i hi c2)
    (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D i hi) K.lev.Lb) (K.lev.fT (A.eV v).1 (A.eV v).2)
    (bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1) (bc (prV (E := D.host.E) (A.eV v).1) (K.y c2).1)
    (mem_local_dual_lattice_iff' K c (A.eV v).1) (mem_local_dual_lattice_iff' K c2 (A.eV v).1) (Γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) _
    (sf_bc_eq (A.eV v).1 (K.y c).1 (K.y c2).1 Γ) hst (local_dual_lattice_transport K L fMe hfv v c c2 _ hF)

end Fun

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

end
