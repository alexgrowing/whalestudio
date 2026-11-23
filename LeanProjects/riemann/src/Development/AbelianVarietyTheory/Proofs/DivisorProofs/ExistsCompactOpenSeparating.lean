import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAnnihilatorOpenSubgroupFiniteAdeles

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Topology

namespace GlobalTheory.FinSepChar

variable {F : Type} [Field F] [NumberField F]

theorem pairA_zero_zero : pairA F 0 (0 : Af F) = 0 := Prod.ext rfl rfl

theorem pairA_zero_neg (b : Af F) : pairA F 0 (-b) = -pairA F 0 b :=
  Prod.ext (neg_zero (G := Ainf F)).symm rfl

theorem algebraMap_mul_inv {a : F} (ha : a ≠ 0) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) a * algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ ha, map_one]

def ann (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) :
    AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1}
  zero_mem' := fun y _ => by
    show ψ (pairA F 0 (0 ⬝ᵥ y)) = 1
    rw [zero_dotProduct, pairA_zero_zero, AddChar.map_zero_eq_one]
  add_mem' := fun {a b} ha hb y hy => by
    show ψ (pairA F 0 ((a + b) ⬝ᵥ y)) = 1
    rw [add_dotProduct, GlobalTheory.AnnCompactStd.pairA_zero_add, AddChar.map_add_eq_mul, ha y hy, hb y hy, mul_one]
  neg_mem' := fun {a} ha y hy => by
    show ψ (pairA F 0 ((-a) ⬝ᵥ y)) = 1
    rw [neg_dotProduct, pairA_zero_neg, AddChar.map_neg_eq_inv, ha y hy, inv_one]

theorem mem_ann {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ] {L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)}
    {x : κ → FiniteAdeleRing (𝓞 F) F} : x ∈ ann ψ κ L ↔ ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1 := Iff.rfl

def scaledInt (κ : Type) (a : FiniteAdeleRing (𝓞 F) F) : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {y | ∀ i, a * y i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}
  zero_mem' := fun i => by
    show a * 0 ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_zero]; exact Subring.zero_mem _
  add_mem' := fun {u v} hu hv i => by
    show a * (u i + v i) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_add]; exact Subring.add_mem _ (hu i) (hv i)
  neg_mem' := fun {u} hu i => by
    show a * (-u i) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_neg]; exact Subring.neg_mem _ (hu i)

theorem isOpen_scaledInt (κ : Type) [Fintype κ] (a : FiniteAdeleRing (𝓞 F) F) :
    IsOpen (scaledInt κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have h : (scaledInt κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      ⋂ i, (fun y : κ → FiniteAdeleRing (𝓞 F) F => a * y i) ⁻¹'
        (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext y; simp only [Set.mem_iInter, Set.mem_preimage]; exact Iff.rfl
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_const.mul (continuous_apply i))

end GlobalTheory.FinSepChar

namespace GlobalTheory.FinSepChar

variable {F : Type} [Field F] [NumberField F]

theorem exists_compact_open_separating {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (κ : Type) [Fintype κ]
    {N : Set (κ → Af F)} (hN : N ∈ 𝓝 (0 : κ → Af F)) : ∃ U : AddSubgroup (κ → Af F),
      IsOpen (U : Set (κ → Af F)) ∧ IsCompact (U : Set (κ → Af F)) ∧ (U : Set (κ → Af F)) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ y : κ → Af F, (∀ u ∈ U, ψ (pairA F 0 (u ⬝ᵥ y)) = 1) ∧ ψ (pairA F 0 (x₀ ⬝ᵥ y)) ≠ 1 := by
  classical
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hsub⟩ := hN
  have hW : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.mpr ht
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.AnnCompactStd.exists_mul_mem_of_forall hψ
  obtain ⟨e, he0, he⟩ := GlobalTheory.AnnCompactStd.exists_psi_fin_trivial hψ
  have hinj : ∀ a : 𝓞 F, a ≠ 0 → algebraMap (𝓞 F) F a ≠ 0 := fun a ha =>
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha
  set cc := algebraMap (𝓞 F) F c with hcc
  set dd := algebraMap (𝓞 F) F d with hdd
  set ee := algebraMap (𝓞 F) F e with hee
  have hC := algebraMap_mul_inv (F := F) (hinj c hc0)
  have hD := algebraMap_mul_inv (F := F) (hinj d hd0)
  have hE := algebraMap_mul_inv (F := F) (hinj e he0)
  set ι := algebraMap F (FiniteAdeleRing (𝓞 F) F) with hι
  set O := GroundTheory.Global.integralFiniteAdeles (𝓞 F) F with hO

  set L := scaledInt (F := F) κ (ι cc * ι dd) with hL
  have hLo : IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_scaledInt κ _
  refine ⟨ann ψ κ L, ?_, ?_, ?_, ?_⟩
  ·
    set δ := ι ee⁻¹ * (ι cc⁻¹ * ι dd⁻¹) with hδ
    have hVo : IsOpen (scaledInt (F := F) κ δ : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_scaledInt κ _
    have hVU : (scaledInt (F := F) κ δ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ ann ψ κ L := by
      intro x hx y hy
      have hsum : x ⬝ᵥ y = ι ee * ∑ i, (δ * x i) * ((ι cc * ι dd) * y i) := by
        rw [dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hδ]
        linear_combination (-(x i * y i * (ι cc * ι dd) * (ι cc⁻¹ * ι dd⁻¹))) * hE
          + (-(x i * y i * ι dd * ι dd⁻¹)) * hC + (-(x i * y i)) * hD
      rw [hsum]
      exact he _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hx i) (hy i))
    exact AddSubgroup.isOpen_of_mem_nhds _
      (Filter.mem_of_superset (hVo.mem_nhds (scaledInt (F := F) κ δ).zero_mem) hVU)
  · exact GlobalTheory.AnnCompactStd.isCompact_annihilator F ψ hψ κ L hLo
  · intro x hx
    apply hsub
    intro i _
    have hz : ∀ s ∈ O, ψ (pairA F 0 ((ι cc⁻¹ * ι dd⁻¹ * x i) * s)) = 1 := by
      intro s hs
      have hy : (Pi.single i (ι cc⁻¹ * ι dd⁻¹ * s) : κ → FiniteAdeleRing (𝓞 F) F) ∈ L := by
        intro k
        by_cases hk : k = i
        · subst hk
          rw [Pi.single_eq_same]
          have : ι cc * ι dd * (ι cc⁻¹ * ι dd⁻¹ * s) = s := by
            linear_combination (ι dd * ι dd⁻¹ * s) * hC + s * hD
          rw [this]; exact hs
        · rw [Pi.single_eq_of_ne hk, mul_zero]; exact Subring.zero_mem _
      have h1 := hx _ hy
      rw [dotProduct_single] at h1
      rw [show ι cc⁻¹ * ι dd⁻¹ * x i * s = x i * (ι cc⁻¹ * ι dd⁻¹ * s) by ring]
      exact h1
    have h2 := hc _ hz
    have h3 := hd _ h2
    have h4 : ι dd * (ι cc * (ι cc⁻¹ * ι dd⁻¹ * x i)) = x i := by
      linear_combination (ι dd * ι dd⁻¹ * x i) * hC + x i * hD
    rw [h4] at h3
    exact Set.mem_iInter.mp h3 i
  · intro x₀ hx₀
    rw [mem_ann] at hx₀
    push_neg at hx₀
    obtain ⟨y, hy, hne⟩ := hx₀
    exact ⟨y, fun u hu => hu y hy, hne⟩

end GlobalTheory.FinSepChar

theorem GlobalTheory.FinSepChar.finite_chars_separate : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ], ∀ N ∈ nhds (0 : κ → Af F), ∃ U : AddSubgroup (κ → Af F),
      IsOpen (U : Set (κ → Af F)) ∧ IsCompact (U : Set (κ → Af F)) ∧ (U : Set (κ → Af F)) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ y : κ → Af F, (∀ u ∈ U, ψ (pairA F 0 (u ⬝ᵥ y)) = 1) ∧ ψ (pairA F 0 (x₀ ⬝ᵥ y)) ≠ 1 :=
  fun _ _ _ _ hψ κ _ _ hN => GlobalTheory.FinSepChar.exists_compact_open_separating hψ κ hN
