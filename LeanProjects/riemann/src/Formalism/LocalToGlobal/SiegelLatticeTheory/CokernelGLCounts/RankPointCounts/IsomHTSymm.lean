import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.YvMemUUE

noncomputable section

open Module
open Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem isom_hT {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (x y : S.V) : S.hT (γ x) (γ y) = S.hT x y := h x y

theorem mapLF_fl {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (L : LFlag S r T') :
    (mapLF γ L).fl = mapFlag γ h L.fl := by
  unfold mapLF; rw [dif_pos h]

theorem mapLF_fl_z {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (L : LFlag S r T') :
    (mapLF γ L).fl.z = γ L.fl.z := by
  rw [mapLF_fl h]; rfl

private theorem mapFlag_fvec' {T0 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) (i : Fin (r + 1)) : (mapFlag γ h F).fvec i = γ (F.fvec i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [FlagG.fvec, mapFlag]
  · simp [FlagG.fvec, mapFlag]

private theorem Zhat_mapFlag' {T0 T1 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) (F' : FlagG S r T1) :
    Zhat (mapFlag γ h F) (mapFlag γ h F') = Zhat F F' := by
  ext a b
  simp [Zhat, brS, mapFlag_fvec', isom_hT h]

private theorem Gflag_mapFlag {T0 T1 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) (F' : FlagG S r T1) :
    Gflag (mapFlag γ h F) (mapFlag γ h F') = Gflag F F' := by
  simp only [Gflag, Dl, Zhat_mapFlag']

private theorem yv_mapFlag {T0 T1 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) (F' : FlagG S r T1) :
    yv (mapFlag γ h F) (mapFlag γ h F') = γ (yv F F') := by
  simp only [yv, omp, Dl, Zhat_mapFlag', mapFlag_fvec']
  simp [map_sum, map_smul, mapFlag]

private theorem mapFlag_X' {T0 : E} {γ : S.V ≃ₗ[E] S.V} (h : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (F : FlagG S r T0) : (mapFlag γ h F).X = F.X.map (γ : S.V →ₗ[E] S.V) := by
  simp only [FlagG.X, mapFlag]
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

private theorem mem_Hp_iff_orthogonal {T0 T1 : E} (Λ : Submodule (NumberField.RingOfIntegers E) S.V)
    (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T0) (F' : LFlag S r T1)
    (hF : IsLift Λ F) (hF' : IsLift Λ F') (h : S.V) :
    h ∈ Hp Λ F F' ↔ ((∀ x ∈ F.fl.X, S.hT x h = 0) ∧ S.hT F.fl.z h = 0 ∧
      (∀ x ∈ F'.fl.X, S.hT x h = 0) ∧ S.hT F'.fl.z h = 0) := by
  constructor
  · intro hh
    exact ⟨fun x hx => hT_UUE_Hp Λ F F' hh (X_le_UUE Λ hΛ F F' hF hF' hx),
      hT_UUE_Hp Λ F F' hh (z_mem_UUE Λ hΛ F F' hF hF'),
      fun x hx => hT_UUE_Hp Λ F F' hh (X'_le_UUE Λ hΛ F F' hF hF' hx),
      hT_UUE_Hp Λ F F' hh (z'_mem_UUE Λ hΛ F F' hF hF')⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hU : UU Λ F F' ≤ (LinearMap.ker (S.hT.flip h)).restrictScalars
        (NumberField.RingOfIntegers E) := by
      unfold UU
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · intro x hx
        simpa using h1 x hx.2
      · rw [Submodule.span_singleton_le_iff_mem, hF.2]
        simpa using h2
      · intro x hx
        simpa using h3 x hx.2
      · rw [Submodule.span_singleton_le_iff_mem, hF'.2]
        simpa using h4
    have key : UUE Λ F F' ≤ LinearMap.ker (S.hT.flip h) := by
      unfold UUE spanE
      rw [Submodule.span_le]
      intro u hu
      exact hU hu
    simp only [Hp, orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro u hu
    simpa using key hu

private theorem isLattice_sup_span_singleton (Λ : Submodule (NumberField.RingOfIntegers E) S.V)
    (hΛ : Submodule.IsLattice E Λ) (v : S.V) :
    Submodule.IsLattice E (Λ ⊔ Submodule.span (NumberField.RingOfIntegers E) {v}) := by
  refine ⟨hΛ.fg.sup (Submodule.fg_span_singleton v), ?_⟩
  rw [eq_top_iff, ← hΛ.span_eq_top]
  exact Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left)

private theorem flagG_ext_of_e_eq_of_z_eq {T0 : E} (F G : FlagG S r T0) (he : F.e = G.e) (hz : F.z = G.z) :
    F = G := by
  cases F
  cases G
  simp only at he hz
  subst he
  subst hz
  rfl

theorem line_pair' (k : ℕ) (hdim : finrank E S.V = k + 2 * r + 1) (Λ : Submodule (NumberField.RingOfIntegers E) S.V)
    (hΛ : Submodule.IsLattice E Λ) (Fl : LFlag S r T) (L0 : LFlag S r T') (γ1 γ2 : S.V ≃ₗ[E] S.V)
    (hγ1 : γ1 ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hγ2 : γ2 ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hL : IsLift Λ Fl) (hL1 : IsLift Λ (mapLF γ1 L0)) (hL2 : IsLift Λ (mapLF γ2 L0))
    (hG1 : Gval Fl (mapLF γ1 L0) ≠ 0) (hG12 : Gval Fl (mapLF γ2 L0) = Gval Fl (mapLF γ1 L0))
    (hT' : T' ≠ 0) (hTs' : star T' = T')
    (hTh : Th Λ Fl (mapLF γ1 L0) (mapLF γ2 L0) (γ2 * γ1⁻¹) = Hp Λ Fl (mapLF γ1 L0)) :
    γ2.symm (yv (mapLF γ2 L0).fl Fl.fl) -
        (brS S (γ2.symm (yv (mapLF γ2 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) /
          brS S (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl))) •
        γ1.symm (yv (mapLF γ1 L0).fl Fl.fl) ∈ L0.fl.X ∧
      (brS S (γ2.symm (yv (mapLF γ2 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) /
          brS S (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl))) *
        star (brS S (γ2.symm (yv (mapLF γ2 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) /
          brS S (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl)) (γ1.symm (yv (mapLF γ1 L0).fl Fl.fl))) = 1 := by
  have hδ : γ1 * γ2⁻¹ ∈ Formalism.HermitianLatticesTheory.isom S.hT := mul_mem hγ1 (inv_mem hγ2)
  set δ := γ1 * γ2⁻¹ with hδd
  set Λ' := Λ ⊔ Submodule.span (NumberField.RingOfIntegers E) {δ Fl.fl.z} with hΛ'd
  have hΛ' : Submodule.IsLattice E Λ' := isLattice_sup_span_singleton Λ hΛ _
  have hle : Λ ≤ Λ' := le_sup_left
  have hL1' : IsLift Λ' (mapLF γ1 L0) := ⟨hle hL1.1, hL1.2⟩
  have hL' : IsLift Λ' Fl := ⟨hle hL.1, hL.2⟩
  have hB : IsLift Λ' (mapLF δ Fl) := by
    refine ⟨?_, ?_⟩
    · rw [mapLF_fl_z hδ]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · simp only [mapLF, dif_pos hδ]
      rw [hL.2]
      rfl
  have eF1 : (mapLF γ1 L0).fl = mapFlag γ1 hγ1 L0.fl := mapLF_fl hγ1 L0
  have eF2 : (mapLF γ2 L0).fl = mapFlag γ2 hγ2 L0.fl := mapLF_fl hγ2 L0
  have eB : (mapLF δ Fl).fl = mapFlag δ hδ Fl.fl := mapLF_fl hδ Fl
  have eflag : mapFlag γ1 hγ1 L0.fl = mapFlag δ hδ (mapFlag γ2 hγ2 L0.fl) := by
    apply flagG_ext_of_e_eq_of_z_eq
    · funext a
      simp [mapFlag, hδd]
    · simp [mapFlag, hδd]
  have hb : yv (mapLF γ1 L0).fl (mapLF δ Fl).fl = δ (yv (mapLF γ2 L0).fl Fl.fl) := by
    rw [eF1, eB, eF2, eflag, yv_mapFlag]
  have hGA : Gval (mapLF γ1 L0) Fl ≠ 0 := by
    simp only [Gval]
    rw [Gflag_swap]
    exact hG1
  have hGB : Gval (mapLF γ1 L0) (mapLF δ Fl) = Gval (mapLF γ1 L0) Fl := by
    have e1 : Gflag (mapLF γ1 L0).fl (mapLF δ Fl).fl = Gflag (mapLF γ2 L0).fl Fl.fl := by
      rw [eF1, eB, eF2, eflag, Gflag_mapFlag]
    have e2 : Gflag (mapLF γ1 L0).fl Fl.fl = Gflag Fl.fl (mapLF γ1 L0).fl := Gflag_swap _ _
    have e3 : Gflag (mapLF γ2 L0).fl Fl.fl = Gflag Fl.fl (mapLF γ2 L0).fl := Gflag_swap _ _
    show Gflag (mapLF γ1 L0).fl (mapLF δ Fl).fl = Gflag (mapLF γ1 L0).fl Fl.fl
    rw [e1, e2, e3]
    exact hG12
  have hTh' : Th Λ' (mapLF γ1 L0) Fl (mapLF δ Fl) δ = Hp Λ' (mapLF γ1 L0) Fl := by
    apply le_antisymm
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hx
      exact hp.1.1.1
    · intro h hh
      have hh1 := (mem_Hp_iff_orthogonal Λ' hΛ' (mapLF γ1 L0) Fl hL1' hL' h).1 hh
      have hh0' : h ∈ Hp Λ (mapLF γ1 L0) Fl := (mem_Hp_iff_orthogonal Λ hΛ (mapLF γ1 L0) Fl hL1 hL h).2 hh1
      have hh0 : h ∈ Hp Λ Fl (mapLF γ1 L0) := by
        rw [Hp_symm]
        exact hh0'
      rw [← hTh] at hh0
      obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 hh0
      obtain ⟨⟨⟨hpa, hpb⟩, hpc⟩, hpd⟩ := hp
      have hp1' : p.1 = h := hp1
      have hpc' : p.1 - p.2 ∈ Fl.fl.X := hpc
      have hpd' : (γ2 * γ1⁻¹) p.1 - p.2 ∈ (mapLF γ2 L0).fl.X := hpd
      have c2 := (mem_Hp_iff_orthogonal Λ hΛ Fl (mapLF γ2 L0) hL hL2 p.2).1 hpb
      have hXF1 : (mapLF γ1 L0).fl.X = ((mapLF γ2 L0).fl.X).map (δ : S.V →ₗ[E] S.V) := by
        rw [eF1, eF2, eflag, mapFlag_X']
      have hXB : (mapLF δ Fl).fl.X = (Fl.fl.X).map (δ : S.V →ₗ[E] S.V) := by
        rw [eB, mapFlag_X']
      have hzF1 : (mapLF γ1 L0).fl.z = δ (mapLF γ2 L0).fl.z := by
        rw [mapLF_fl_z hγ1, mapLF_fl_z hγ2]
        simp [hδd]
      have hzB : (mapLF δ Fl).fl.z = δ Fl.fl.z := mapLF_fl_z hδ Fl
      refine Submodule.mem_map.2 ⟨(h, δ p.2), ⟨⟨⟨hh, ?_⟩, ?_⟩, ?_⟩, rfl⟩
      · refine (mem_Hp_iff_orthogonal Λ' hΛ' (mapLF γ1 L0) (mapLF δ Fl) hL1' hB (δ p.2)).2 ⟨?_, ?_, ?_, ?_⟩
        · intro x hx
          rw [hXF1] at hx
          obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
          rw [show (δ : S.V →ₗ[E] S.V) y = δ y from rfl, isom_hT hδ]
          exact c2.2.2.1 y hy
        · rw [hzF1, isom_hT hδ]
          exact c2.2.2.2
        · intro x hx
          rw [hXB] at hx
          obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
          rw [show (δ : S.V →ₗ[E] S.V) y = δ y from rfl, isom_hT hδ]
          exact c2.1 y hy
        · rw [hzB, isom_hT hδ]
          exact c2.2.1
      · show h - δ p.2 ∈ Xsp (mapLF γ1 L0)
        show h - δ p.2 ∈ (mapLF γ1 L0).fl.X
        rw [hXF1]
        refine Submodule.mem_map.2 ⟨_, hpd', ?_⟩
        rw [← hp1']
        simp [hδd, map_sub]
      · show δ h - δ p.2 ∈ (mapLF δ Fl).fl.X
        rw [hXB]
        refine Submodule.mem_map.2 ⟨_, hpc', ?_⟩
        rw [← hp1']
        simp [map_sub]
  have LP := line_pair k hdim Λ' hΛ' (mapLF γ1 L0) Fl (mapLF δ Fl) δ hL1' hL' hB hGA hGB hT' hTs' hTh'
  rw [hb] at LP
  set w1 := yv (mapLF γ1 L0).fl Fl.fl with hw1
  set w2 := yv (mapLF γ2 L0).fl Fl.fl with hw2
  have hc1 : brS S (δ w2) w1 = brS S (γ2.symm w2) (γ1.symm w1) := by
    simp only [brS]
    rw [← isom_hT hγ1 (γ1.symm w1) (γ2.symm w2)]
    simp [hδd]
  have hc2 : brS S w1 w1 = brS S (γ1.symm w1) (γ1.symm w1) := by
    simp only [brS]
    rw [← isom_hT hγ1 (γ1.symm w1) (γ1.symm w1)]
    simp
  rw [hc1, hc2] at LP
  refine ⟨?_, LP.2⟩
  have hX : (mapLF γ1 L0).fl.X = L0.fl.X.map (γ1 : S.V →ₗ[E] S.V) := by
    rw [eF1, mapFlag_X']
  have h1 := LP.1
  rw [hX] at h1
  obtain ⟨a, ha, hae⟩ := Submodule.mem_map.1 h1
  convert ha using 1
  apply γ1.injective
  rw [show (γ1 : S.V →ₗ[E] S.V) a = γ1 a from rfl] at hae
  rw [hae]
  simp [hδd, map_sub, map_smul]

end Formalism.L2.SG.NGCut.NormalVectorPairings
