import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibPNeZeroOfGenus
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsomFixOfExp

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def cntGe {n : ℕ} (e : Fin n → ℕ) (v : ℕ) : ℕ := (Finset.univ.filter fun i => v ≤ e i).card

theorem cntGe_succ {n : ℕ} (e : Fin n → ℕ) (v : ℕ) :
    cntGe e (v + 1) + ∑ i, min (e i) v = ∑ i, min (e i) (v + 1) := by
  unfold cntGe
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

theorem cntGe_eq {n : ℕ} (e e' : Fin n → ℕ) (H : ∀ j, ∑ i, min (e i) j = ∑ i, min (e' i) j) (v : ℕ) :
    cntGe e v = cntGe e' v := by
  cases v with
  | zero => simp [cntGe]
  | succ w =>
    have h1 := cntGe_succ e w
    have h2 := cntGe_succ e' w
    rw [H w, H (w + 1)] at h1
    omega

theorem card_eq_val {n : ℕ} (e : Fin n → ℕ) (v : ℕ) :
    (Finset.univ.filter fun i => e i = v).card = cntGe e v - cntGe e (v + 1) := by
  have key : cntGe e v = (Finset.univ.filter fun i => e i = v).card + cntGe e (v + 1) := by
    unfold cntGe
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> omega
  omega

theorem exists_perm_of_min {n : ℕ} (e e' : Fin n → ℕ) (H : ∀ j, ∑ i, min (e i) j = ∑ i, min (e' i) j) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, e' (σ i) = e i := by
  classical
  have hc : ∀ v, (Finset.univ.filter fun i => e i = v).card =
      (Finset.univ.filter fun i => e' i = v).card := by
    intro v
    rw [card_eq_val, card_eq_val, cntGe_eq e e' H, cntGe_eq e e' H]
  refine ⟨Equiv.ofFiberEquiv (f := e) (g := e') fun v => Fintype.equivOfCardEq ?_,
    fun i => Equiv.ofFiberEquiv_map _ i⟩
  rw [Fintype.card_subtype, Fintype.card_subtype]
  convert hc v

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem isJordanIn_perm {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} {b : Fin (finrank K X) → V} {a : Fin (finrank K X) → 𝓞 F}
    (hb : IsJordanIn h X L 𝔭 b a) (σ : Equiv.Perm (Fin (finrank K X))) :
    IsJordanIn h X L 𝔭 (b ∘ σ) (a ∘ σ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  have hr : Set.range (b ∘ σ) = Set.range b := σ.surjective.range_comp b
  refine ⟨fun i => h1 _, ?_, fun i j hij => h3 _ _ (σ.injective.ne hij), fun i => h4 _,
    fun i => h5 _⟩
  rw [hr]
  exact h2

theorem nondegOn_orth {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUW : IsCompl U (orthK h U)) : NondegOn h (orthK h U) := by
  intro x hx hxy
  apply hnd
  intro v
  have hv : v ∈ U ⊔ orthK h U := by rw [hUW.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, hxy w hw, add_zero]
  have h1 : h u x = 0 := by
    have hx' := hx
    simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker] at hx'
    exact hx' u hu
  rw [← hs.eq u x, h1, map_zero]

theorem integral_of_fib (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M T : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hfib : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T ≠ 0) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h T := by
  intro x hx y hy
  rw [← Formalism.HermitianLattices.Ext.L3.LocF.iInf_locF (K := K) (F := F) (1 : Submodule (𝓞 K) K),
    Submodule.mem_iInf]
  rintro ⟨𝔭, h𝔭⟩
  have hne := hfib 𝔭 h𝔭
  unfold fibP at hne
  obtain ⟨⟨Λ, _, hdual, _, hΛT⟩⟩ := (Nat.card_ne_zero.1 hne).1
  have hsub : ∀ z ∈ T, z ∈ Λ := fun z hz =>
    (Submodule.mem_inf.1 (hΛT.symm ▸ Formalism.HermitianLattices.Ext.L3.LocF.le_locF 𝔭 T hz :
      z ∈ Λ ⊓ (orthK h U).restrictScalars (𝓞 K))).1
  have hyd : y ∈ dualF h 𝔭 Λ := by
    rw [hdual]
    exact hsub y hy
  exact hyd x (hsub x hx)

theorem genus_of_fib (h1 : JordanExists) (h2 : JordanInv) (h6 : GlueLoc) (hI : IsomFixOfExp)
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hnd : Nondeg h) {U : Submodule K V} (hUc : IsCompl U (orthK h U)) (hpos : PosDefOn h (orthK h U))
    {M : Submodule (𝓞 K) V} (hM : IsLatIn U M) {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Λ₀ ∈ GlueSet h U M)
    {T : Submodule (𝓞 K) V} (hT : IsLatIn (orthK h U) T)
    (hfib : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T ≠ 0) :
    SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) T := by
  intro 𝔭 h𝔭
  have hT₀ : IsLatIn (orthK h U) (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) :=
    isLatIn_cut hΛ₀.1 _
  have hrefl : SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K))
      (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) := fun 𝔮 _ =>
    ⟨1, (isomFix h U).one_mem, by ext z; simp [Formalism.HermitianLatticesTheory.gmap]⟩
  have hfib₀ : ∀ 𝔮 : Ideal (𝓞 F), 𝔮.IsMaximal →
      fibP h U 𝔮 M (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) ≠ 0 := fun 𝔮 h𝔮 =>
    fibP_ne_zero_of_genus hF hs hnd hUc hM hΛ₀ hrefl h𝔮
  have hint := integral_of_fib hF hs hnd hUc hM hT hfib
  have hint₀ := integral_of_fib hF hs hnd hUc hM hT₀ hfib₀
  have hnd' := nondegOn_orth hs hnd hUc
  obtain ⟨b, a, hb⟩ := (h1 K F V hK hF h hs).1 (orthK h U) _ hnd' hT₀ hint₀ 𝔭 h𝔭
  obtain ⟨b', a', hb'⟩ := (h1 K F V hK hF h hs).1 (orthK h U) T hnd' hT hint 𝔭 h𝔭
  obtain ⟨e₀⟩ := ((h6 K F V hK hF h hs hnd U hUc M _ hM hT₀ 𝔭 h𝔭).1 (hfib₀ 𝔭 h𝔭)).1
  obtain ⟨e⟩ := ((h6 K F V hK hF h hs hnd U hUc M T hM hT 𝔭 h𝔭).1 (hfib 𝔭 h𝔭)).1
  have hmin := h2 K F V V hK hF h h hs hs (orthK h U) (orthK h U) _ T hT₀ hT 𝔭 h𝔭 b a b' a'
    hb hb' ⟨e₀.symm.trans e⟩
  obtain ⟨σ, hσ⟩ := exists_perm_of_min (fun i => vF 𝔭 (a i)) (fun i => vF 𝔭 (a' i)) hmin
  exact hI K F V hK hF h hs hnd U hUc hpos _ T hT₀ hT 𝔭 h𝔭 b a (b' ∘ σ) (a' ∘ σ) hb
    (isJordanIn_perm hb' σ) (fun i => (hσ i).symm)

end Formalism.L2.SG.Pf.G8
