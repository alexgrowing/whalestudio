import Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module

section Abstract

variable {O X H : Type} [CommRing O] [AddCommGroup X] [Module O X] [AddCommGroup H] [Module O H]

theorem wachCol_len_transfer (N I : Submodule O X) (f : N →ₗ[O] H) (Hf S : Submodule O H)
    (hr : LinearMap.range f = Hf) (hI : I.comap N.subtype = S.comap f) :
    Module.length O (↥N ⧸ I.comap N.subtype) = Module.length O (↥Hf ⧸ S.comap Hf.subtype) := by
  let g : N →ₗ[O] Hf := LinearMap.codRestrict Hf f (fun x => by rw [← hr]; exact LinearMap.mem_range_self f x)
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [← hr] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  let q : N →ₗ[O] (↥Hf ⧸ S.comap Hf.subtype) := (S.comap Hf.subtype).mkQ ∘ₗ g
  have hq : Function.Surjective q := (Submodule.mkQ_surjective _).comp hg
  have hk : LinearMap.ker q = I.comap N.subtype := by
    ext x
    rw [hI, LinearMap.mem_ker, Submodule.mem_comap]
    simp [q, g]
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans (q.quotKerEquivOfSurjective hq)).length_eq

theorem wachCol_lift_transfer (N I : Submodule O X) (f : N →ₗ[O] H) (Hf S : Submodule O H)
    (hr : LinearMap.range f = Hf) (hI : I.comap N.subtype = S.comap f) (a : O) :
    (∀ m ∈ N, a • m ∈ I) ↔ ∀ x ∈ Hf, a • x ∈ S := by
  have key : ∀ n : N, (a • (n : X) ∈ I ↔ a • f n ∈ S) := by
    intro n
    have h := SetLike.ext_iff.mp hI (a • n)
    simpa using h
  constructor
  · intro h x hx
    rw [← hr] at hx
    obtain ⟨n, rfl⟩ := hx
    exact (key n).mp (h n n.2)
  · intro h m hm
    exact (key ⟨m, hm⟩).mpr (h _ (by rw [← hr]; exact LinearMap.mem_range_self f _))

end Abstract

section WachSide

open Formalism.CoboundaryTransfers

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {Bw : Base O A} {M : ℕ}
  {D D' : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']

theorem wachModule_mem_cocycles_iff (W : WachMod Bw M D) (pr : D × D) :
    pr ∈ W.Z1 ↔ (W.γ pr.1 - pr.1) - (W.φ pr.2 - pr.2) = 0 := by
  unfold WachMod.Z1
  simp
  rw [← neg_sub (W.φ pr.2) pr.2, ← sub_eq_add_neg]

theorem wachModule_coboundaries_le_cocycles (W : WachMod Bw M D) : W.B1 ≤ W.Z1 := by
  intro pr hpr
  rw [wachModule_mem_cocycles_iff]
  unfold WachMod.B1 at hpr
  obtain ⟨d, rfl⟩ := hpr
  have key : W.γ (W.φ d) = W.φ (W.γ d) := by
    first
    | (cases W; simp_all)
    | (cases W; simp_all [LinearMap.ext_iff])
    | (cases W; simp_all [LinearMap.ext_iff, eq_comm])
  simp [key, Function.prod, map_add, map_sub, map_neg, neg_smul, LinearMap.add_apply] <;> abel

theorem wachModule_finiteCocycles_le_cocycles (W : WachMod Bw M D) : W.Zf ≤ W.Z1 := by
  unfold WachMod.Zf
  exact sup_le (Submodule.span_le.mpr (fun x hx => hx.1)) (wachModule_coboundaries_le_cocycles W)

theorem wachHom_prodMap_mem_cocycles {W : WachMod Bw M D} {W' : WachMod Bw M D'} (Fw : Hom W W') (pr : D × D)
    (h : pr ∈ W.Z1) : Fw.f2 pr ∈ W'.Z1 := by
  rw [wachModule_mem_cocycles_iff] at h ⊢
  have := congrArg Fw.f h
  simp only [map_sub, map_zero, Fw.φ_comm, Fw.γ_comm] at this
  exact this

end WachSide

theorem cokernelLengthEqWach_holds : WachCol := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ O _ _ V V'
    _ _ _ _ _ _ _ _ _ _ _ _ ρ ρ' _ _ _ _ _ _ _ L L' F A D D' _ _ _ _ _ _ _ _ _ _
    Bw M W W' Fw cl cl' hp hW hW' hnat
  set S : Submodule O (LatticeCohomology L') := (latticeFiniteCohomology PD L).map F.H1map with hS

  have hZf_le : latticeFiniteCocycles PD L' ≤ latticeCocycles L' := inf_le_left
  let ψ : ↥(latticeFiniteCocycles PD L') →ₗ[O] LatticeCohomology L' := (Submodule.mkQ _) ∘ₗ Submodule.inclusion hZf_le
  have hψr : LinearMap.range ψ = latticeFiniteCohomology PD L' := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]; rfl
  have hψI : (F.ImF PD).comap (latticeFiniteCocycles PD L').subtype = S.comap ψ := by
    ext ⟨c, hc⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      obtain ⟨u, ⟨a, ha, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.1 h
      refine ⟨Submodule.mkQ _ ⟨a, ha.1⟩, ⟨⟨a, ha.1⟩, ha, rfl⟩, ?_⟩
      simp only [ψ, LinearMap.comp_apply, LatHom.H1map, Submodule.mkQ_apply]
      refine (Submodule.Quotient.eq _).2 ?_
      change F.post a - c ∈ latticeCoboundaries L'
      have e : F.post a - c = -b := by rw [← hab]; abel
      rw [e]; exact (latticeCoboundaries L').neg_mem hb
    · rintro ⟨κ, ⟨x, hx, rfl⟩, hκ⟩
      simp only [ψ, LinearMap.comp_apply, LatHom.H1map, Submodule.mkQ_apply] at hκ
      have hb := (Submodule.Quotient.eq _).1 hκ
      change F.post x - c ∈ latticeCoboundaries L' at hb
      refine Submodule.mem_sup.2 ⟨F.post x, ⟨(x : G → V), hx, rfl⟩, c - F.post x, ?_, by abel⟩
      have := (latticeCoboundaries L').neg_mem hb
      rwa [neg_sub] at this

  have hZ' : W'.Zf ≤ W'.Z1 := wachModule_finiteCocycles_le_cocycles W'
  let χ : ↥W'.Zf →ₗ[O] LatticeCohomology L' := cl' ∘ₗ Submodule.inclusion hZ'
  have hχr : LinearMap.range χ = latticeFiniteCohomology PD L' := by
    rw [LinearMap.range_comp, Submodule.range_inclusion]; exact hW'.2
  have hχI : Fw.ImF.comap W'.Zf.subtype = S.comap χ := by
    ext ⟨pr', hpr'⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      obtain ⟨u, ⟨pr, hpr, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.1 h
      have hpr1 : pr ∈ W.Z1 := wachModule_finiteCocycles_le_cocycles W hpr
      have hf1 : Fw.f2 pr ∈ W'.Z1 := wachHom_prodMap_mem_cocycles Fw pr hpr1
      have hb1 : b ∈ W'.Z1 := wachModule_coboundaries_le_cocycles W' hb
      refine ⟨cl ⟨pr, hpr1⟩, ?_, ?_⟩
      · rw [← hW.2]; exact ⟨⟨pr, hpr1⟩, hpr, rfl⟩
      · rw [hnat ⟨pr, hpr1⟩ ⟨Fw.f2 pr, hf1⟩ rfl]
        have e : (⟨pr', hZ' hpr'⟩ : W'.Z1) = ⟨Fw.f2 pr, hf1⟩ + ⟨b, hb1⟩ := by
          apply Subtype.ext
          simp [← hab]
        change _ = cl' ⟨pr', hZ' hpr'⟩
        rw [e, map_add, (hW'.1.2 ⟨b, hb1⟩).2 hb, add_zero]
    · rintro ⟨κ, hκ, hκ'⟩
      rw [← hW.2] at hκ
      obtain ⟨⟨pr, hpr1⟩, hpr, rfl⟩ := hκ
      have hf1 := wachHom_prodMap_mem_cocycles Fw pr hpr1
      rw [hnat ⟨pr, hpr1⟩ ⟨Fw.f2 pr, hf1⟩ rfl] at hκ'
      have h0 : cl' (⟨pr', hZ' hpr'⟩ - ⟨Fw.f2 pr, hf1⟩) = 0 := by
        rw [map_sub]; exact sub_eq_zero.2 hκ'.symm
      have hb := (hW'.1.2 _).1 h0
      exact Submodule.mem_sup.2 ⟨Fw.f2 pr, ⟨pr, hpr, rfl⟩, pr' - Fw.f2 pr, hb, by abel⟩
  have hcolG := wachCol_len_transfer (latticeFiniteCocycles PD L') (F.ImF PD) ψ (latticeFiniteCohomology PD L') S hψr hψI
  have hcolW := wachCol_len_transfer W'.Zf Fw.ImF χ (latticeFiniteCohomology PD L') S hχr hχI
  refine ⟨?_, fun e => ?_⟩
  · unfold LatHom.col Formalism.CoboundaryTransfers.Hom.col
    rw [hcolG, hcolW]
  · have hG := wachCol_lift_transfer (latticeFiniteCocycles PD L') (F.ImF PD) ψ (latticeFiniteCohomology PD L') S hψr hψI
      ((PD.p : O) ^ e)
    have hWl := wachCol_lift_transfer W'.Zf Fw.ImF χ (latticeFiniteCohomology PD L') S hχr hχI ((PD.p : O) ^ e)
    unfold LatHom.LiftF Formalism.CoboundaryTransfers.Hom.LiftF
    rw [hG]
    have hsm : ∀ pr : D' × D', ((Bw.p ^ e : ℕ)) • pr = ((PD.p : O) ^ e) • pr := by
      intro pr
      rw [hp, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
    simp only [hsm]
    exact hWl.symm

end Formalism.WeaklyAdmissibleFiltrations
