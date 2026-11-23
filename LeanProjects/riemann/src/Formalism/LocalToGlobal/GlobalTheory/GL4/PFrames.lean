import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrSep
import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrGen
import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieAll
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem isLattice_between {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (A B : Submodule (𝓞 E) W) (hA : Submodule.IsLattice E A) (hAB : A ≤ B) (T : ℕ) (hT : T ≠ 0)
    (hTB : ∀ x ∈ B, (T : E) • x ∈ A) : Submodule.IsLattice E B := by
  let f : W →ₗ[𝓞 E] W := ((T : ℕ) : 𝓞 E) • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : ((T : ℕ) : E) • x = ((T : ℕ) : E) • y := by
      simpa only [f, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using hxy
    exact smul_right_injective W (by exact_mod_cast hT : ((T : ℕ) : E) ≠ 0) h1
  have hmap : B.map f ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hTB x hx
    simpa only [f, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using h1
  haveI : IsNoetherian (𝓞 E) A := isNoetherian_of_fg_of_noetherian A hA.fg
  have hmfg : (B.map f).FG := by
    have h1 := IsNoetherian.noetherian ((B.map f).comap A.subtype)
    have h2 := h1.map A.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hmap] at h2
  exact ⟨Submodule.fg_of_fg_map_injective f hf hmfg,
    eq_top_iff.2 (le_trans (le_of_eq hA.span_eq_top.symm) (Submodule.span_mono (SetLike.coe_subset_coe.2 hAB)))⟩

theorem T_smul_of_disc {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (L D : Submodule (𝓞 E) W) (T : ℕ)
    (e : Nonempty ((D ⧸ L.comap D.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {((T : ℕ) : 𝓞 E)}))) :
    ∀ x ∈ D, (T : E) • x ∈ L := by
  have hk : ∀ z : 𝓞 E ⧸ Ideal.span {((T : ℕ) : 𝓞 E)}, ((T : ℕ) : 𝓞 E) • z = 0 := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H y =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_span_singleton'.2 ⟨y, by rw [smul_eq_mul, mul_comm]⟩
  intro x hx
  obtain ⟨e⟩ := e
  have h1 : ((T : ℕ) : 𝓞 E) • (Submodule.Quotient.mk (⟨x, hx⟩ : D) : D ⧸ L.comap D.subtype) = 0 :=
    e.injective (by rw [map_smul, map_zero, hk])
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
  have h2 : ((T : ℕ) : E) • x = D.subtype (((T : ℕ) : 𝓞 E) • (⟨x, hx⟩ : D)) := by
    simp only [Submodule.subtype_apply, Submodule.coe_smul]
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h2]
  exact h1

end Gen

open Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem M_ne_zero (D : D7) (u : D.what₂.Word) : Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1 ≠ 0 := by
  have h1 := (D.mem u).A.T_prime.ne_zero
  have h2 := (D.host.g_prime 0).ne_zero
  have h3 := (D.host.g_prime 1).ne_zero
  unfold Formalism.MainNotions.flipTwoThree.Tu
  positivity

theorem framesStep_of_gen {D : D7} (X : FullTied D) (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m)
    (hgen : GenMod (dualL D.sp.cm (D.sp.X i) (X.base.lev u i h1 hm).Lb)
      (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1)) : FramesStep D u i := by
  set lev := X.base.lev u i h1 hm
  have hT0 : (D.mem u).A.T ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have hLb : Submodule.IsLattice D.host.E lev.Lb := ⟨Module.Finite.iff_fg.1 lev.Lb_fin, lev.Lb_span⟩
  have hLbd : IsLat (dualL D.sp.cm (D.sp.X i) lev.Lb) := by
    have := isLattice_between lev.Lb _ hLb lev.Lb_int _ hT0 lev.Lb_dual
    exact ⟨Module.Finite.iff_fg.2 this.fg, this.span_eq_top⟩
  have hΔ : ∀ c, Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c)) := by
    intro c
    refine isLattice_between _ _ (D.clsLat_lat u i c) ?_ _ hT0
      (T_smul_of_disc _ _ _ ((X.atT u).disc i hm c))
    intro x hx
    have := clsLat_int X u i hm c x hx
    rw [dualSub_eq] at this
    exact this
  obtain ⟨e, he, hsep⟩ := frames_of_tie (X.base.cls u i h1 hm) hLbd hΔ _ (M_ne_zero D u) hgen
    (fun k hkU hst hcg => stepLevel_mem lev k hkU hst hcg)
  have hr : (D.sp.X i).rank = D.R.N i := D.sp.X_rank i hm
  refine ⟨fun c a => e c (Fin.cast hr.symm a), fun c a => he c _, fun c c' h => hsep c c' ?_⟩
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := h
  refine ⟨γ, hγ1, hγ2, fun a => ?_⟩
  have := hγ3 (Fin.cast hr a)
  simpa using this

theorem framesP_of_gen {D : D7} (X : FullTied D) (u : D.what₂.Word)
    (hgen : GenMod (crdLat D.sp.X' D.sp.X'.L0) (Formalism.MainNotions.flipTwoThree.Tu D u * D.host.g 0 * D.host.g 1)) : FramesP X u := by
  have hsd := coordinate_lattice_self_dual D.sp.cm D.sp.X'
  have hLbd : IsLat (dualL D.sp.cm D.sp.X' (crdLat D.sp.X' D.sp.X'.L0)) := by
    rw [hsd]; exact Fr.isLat_crd _ _ D.sp.X'.standardTuple_isLattice
  have hΔ : ∀ c, Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.dual D.sp.X'.hT ((X.atT u).lattice₂ c)) := by
    intro c
    have h := localLattice_selfDual X u c
    have hle : Formalism.HermitianLatticesTheory.dual D.sp.X'.hT ((X.atT u).lattice₂ c) ≤ (X.atT u).lattice₂ c := by
      have h2 := h.2.2
      rw [dualSub_eq] at h2
      have h3 := AddSubgroup.relIndex_eq_one.1 h2
      intro x hx
      exact h3 hx
    have hge : (X.atT u).lattice₂ c ≤ Formalism.HermitianLatticesTheory.dual D.sp.X'.hT ((X.atT u).lattice₂ c) := by
      intro x hx
      have := h.2.1 x hx
      rw [dualSub_eq] at this
      exact this
    rw [le_antisymm hle hge]
    exact h.1
  rw [← hsd] at hgen
  obtain ⟨e, he, hsep⟩ := frames_of_tie (X.atT u).clsP hLbd hΔ _ (M_ne_zero D u) hgen
    (fun k hkU hst hcg => stepLevel0_mem hsd (X.atT u).levP _ k hkU hst hcg)
  have hr : D.sp.X'.rank = D.R.N D.R.m - 1 := by
    rw [D.sp.X'_rank, factXm D.R]; omega
  refine ⟨fun c a => e c (Fin.cast hr.symm a), fun c a => he c _, fun c c' h => hsep c c' ?_⟩
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := h
  refine ⟨γ, hγ1, hγ2, fun a => ?_⟩
  have := hγ3 (Fin.cast hr a)
  simpa using this

theorem framesStep_pos {D : D7} (X : FullTied D) (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) :
    FramesStep D u i := by
  refine framesStep_of_gen X u i h1 hm (genMod _ (M_ne_zero D u) _ ?_)
  set lev := X.base.lev u i h1 hm
  have hLb : Submodule.IsLattice D.host.E lev.Lb := ⟨Module.Finite.iff_fg.1 lev.Lb_fin, lev.Lb_span⟩
  exact Module.Finite.iff_fg.2
    (isLattice_between lev.Lb _ hLb lev.Lb_int _ (D.mem u).A.T_prime.ne_zero lev.Lb_dual).fg

theorem frames_of_classes {D : D7} (X : FullTied D) (u : D.what₂.Word) : FramesP X u :=
  framesP_of_gen X u (genMod _ (M_ne_zero D u) _ (Fr.isLat_crd _ _ D.sp.X'.standardTuple_isLattice).1)

theorem ClsTieOfTied_of_step0 (h0 : ∀ (D : D7), FullTied D → ∀ u, FramesStep D u 0) : ClassCompatibilityOfRowCompatibility := by
  refine ClsTieOfTied_of_frames (fun D X u i hi => ?_) (fun D X u => frames_of_classes X u)
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · exact h0 D X u
  · exact framesStep_pos X u i h1 hi

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
