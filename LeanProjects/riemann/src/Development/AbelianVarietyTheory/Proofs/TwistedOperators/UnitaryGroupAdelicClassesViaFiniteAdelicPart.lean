import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefFree.AdelCls

open GlobalTheory.Mass

theorem dc_iff {G H : Type} [Group G] [Group H] (f : G →* H) (Γ A L N : Subgroup G) (Q K : Subgroup H)
    (hQ : Γ.map f = Q) (hA : ∀ x, ∃ h ∈ A, f h = x) (hL : ∀ κ, κ ∈ L ↔ κ ∈ A ∧ f κ ∈ K)
    (hN : ∀ h, f h = 1 ↔ h ∈ N) (h h' : G) :
    (∃ x ∈ Q, ∃ k ∈ K, f h' = x * f h * k) ↔ ∃ γ ∈ Γ, ∃ κ ∈ L, ∃ k ∈ N, h' = γ * h * κ * k := by
  constructor
  · rintro ⟨x, hx, k, hk, e⟩
    rw [← hQ] at hx
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨κ, hκA, rfl⟩ := hA k
    refine ⟨γ, hγ, κ, (hL κ).2 ⟨hκA, hk⟩, (γ * h * κ)⁻¹ * h', (hN _).1 ?_,
      (mul_inv_cancel_left (γ * h * κ) h').symm⟩
    simp only [map_mul, map_inv, e, inv_mul_cancel]
  · rintro ⟨γ, hγ, κ, hκ, k, hk, rfl⟩
    refine ⟨f γ, ?_, f κ, ((hL κ).1 hκ).2, ?_⟩
    · rw [← hQ]
      exact Subgroup.mem_map_of_mem f hγ
    · rw [map_mul, map_mul, map_mul, (hN k).2 hk, mul_one]

variable {D : D7}

theorem finU_eq (V : HSp D) {π : GA D V →* HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram}
    (hπ : IsFinProj D.sp.cm.sig V.gram π) (h : GA D V) :
    finU V h = swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π h) := by
  apply Subtype.ext
  rw [coe_finU, coe_swapPts, hπ h]
  rfl

theorem finU_eq_one_iff (V : HSp D) (h : GA D V) : finU V h = 1 ↔ h ∈ GinfC V := by
  have hs : Function.Injective (swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective
  have hb : Function.Injective
      (Formalism.UG.bc (swapAE D) : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →* GL (Fin V.rank) (EAf D)) :=
    Units.map_injective (Matrix.map_injective hs)
  rw [← OneMemClass.coe_eq_one, coe_finU, GinfC, MonoidHom.mem_ker]
  change Formalism.UG.bc (swapAE D) (finHom V h) = 1 ↔ finHom V h = 1
  exact map_eq_one_iff _ hb

theorem exists_fin (V : HSp D) (x : UA D.sp.cm V.gram) : ∃ h ∈ GfC V, finU V h = x := by
  obtain ⟨hsp, hex⟩ := parts_spec (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram
  obtain ⟨y, rfl⟩ := (swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective x
  obtain ⟨g, g1, g2⟩ := hex 1 (HA.mat _ _ _ y)
  have hg : g ∈ HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram := by
    refine (hsp g).2 ⟨?_, ?_⟩
    · rw [g1]
      exact one_mem _
    · rw [g2]
      exact (y : HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).2
  refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.2 g1, ?_⟩
  apply Subtype.ext
  rw [coe_swapPts, ← g2]
  rfl

theorem mem_levA (V : HSp D) (K : Subgroup (GL (Fin V.rank) (EAf D))) (κ : GA D V) :
    κ ∈ levA V K ↔ κ ∈ GfC V ∧ finU V κ ∈ K.subgroupOf (UA D.sp.cm V.gram) := by
  simp only [levA, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_finU]

theorem map_rat (V : HSp D) : (GQ V).map (finU V) = UQ D.sp.cm V.gram := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj (F := D.host.F) D.sp.cm.sig V.gram
  have e : finU V = (swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram :
      HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram →* UA D.sp.cm V.gram).comp π :=
    MonoidHom.ext fun h => finU_eq V hπ h
  have h1 : (GQ V).map π = ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram := hπ.map_ratIn
  rw [e, ← Subgroup.map_map, h1]
  exact map_swapPts_rat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram

theorem rat_mem (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) : finU V γ ∈ UQ D.sp.cm V.gram := by
  rw [← map_rat V]
  exact Subgroup.mem_map_of_mem _ hγ

theorem rat_inj (V : HSp D) (γ : GA D V) (hγ : γ ∈ GQ V) (e : finU V γ = 1) : γ = 1 := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj (F := D.host.F) D.sp.cm.sig V.gram
  rw [finU_eq V hπ, MulEquiv.map_eq_one_iff] at e
  exact hπ.injOn (SetLike.mem_coe.2 hγ) (SetLike.mem_coe.2 (Subgroup.one_mem _)) (by rw [e, map_one])

theorem adelic_classes : ∀ (D : D7) (V : HSp D), (∀ x : UA D.sp.cm V.gram, ∃ h ∈ GfC V, finU V h = x) ∧ (∀ γ ∈ GQ V, finU V γ ∈ UQ D.sp.cm V.gram) ∧ (∀ x ∈ UQ D.sp.cm V.gram, ∃ γ ∈ GQ V, finU V γ = x) ∧ (∀ γ ∈ GQ V, finU V γ = 1 → γ = 1) ∧ ∀ (K : Subgroup (GL (Fin V.rank) (EAf D))) (h h' : GA D V), clsA V K h = clsA V K h' ↔ ∃ γ ∈ GQ V, ∃ κ ∈ levA V K, ∃ k ∈ GinfC V, h' = γ * h * κ * k := by
  intro D V
  refine ⟨exists_fin V, rat_mem V, fun x hx => ?_, rat_inj V, fun K h h' => ?_⟩
  · rw [← map_rat V] at hx
    obtain ⟨γ, hγ, e⟩ := Subgroup.mem_map.1 hx
    exact ⟨γ, hγ, e⟩
  · first
      | rw [clsA, clsA, Quotient.eq'', DoubleCoset.rel_iff]
      | (show DoubleCoset.mk _ _ (finU V h) = DoubleCoset.mk _ _ (finU V h') ↔ _
         rw [DoubleCoset.eq])
    exact dc_iff (finU V) (GQ V) (GfC V) (levA V K) (GinfC V) (UQ D.sp.cm V.gram)
      (K.subgroupOf (UA D.sp.cm V.gram)) (map_rat V) (exists_fin V) (mem_levA V K) (finU_eq_one_iff V) h h'

end GlobalTheory.DefFree.AdelCls
