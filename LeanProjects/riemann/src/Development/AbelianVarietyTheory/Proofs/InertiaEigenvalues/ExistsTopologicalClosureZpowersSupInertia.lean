import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgEquivRootOfUnityEqPow

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.FrobGen
open GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

theorem exists_gen_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (J : Subgroup G) [J.Normal] (g : G) (U : Subgroup G) (hU : IsOpen (U : Set G))
    (hg : (Subgroup.zpowers g ⊔ J).topologicalClosure = ⊤) :
    ∃ φ : U, (Subgroup.zpowers φ ⊔ J.subgroupOf U).topologicalClosure = ⊤ := by
  let π : G →* G ⧸ J := QuotientGroup.mk' J
  let S : AddSubgroup ℤ :=
    { carrier := {n | π g ^ n ∈ U.map π}
      add_mem' := fun {a b} ha hb => by
        show π g ^ (a + b) ∈ U.map π
        rw [zpow_add]; exact mul_mem ha hb
      zero_mem' := by
        show π g ^ (0 : ℤ) ∈ U.map π
        rw [zpow_zero]; exact one_mem _
      neg_mem' := fun {a} ha => by
        show π g ^ (-a) ∈ U.map π
        rw [zpow_neg]; exact inv_mem ha }
  obtain ⟨f, hf⟩ := Int.subgroup_cyclic S
  have hfS : f ∈ S := by rw [hf]; exact AddSubgroup.subset_closure rfl
  obtain ⟨φ, hφU, hφ⟩ : π g ^ f ∈ U.map π := hfS
  refine ⟨⟨φ, hφU⟩, ?_⟩
  have hd : Dense ((Subgroup.zpowers g ⊔ J : Subgroup G) : Set G) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hg, Subgroup.coe_top]
  have hd2 := hd.preimage (f := (Subtype.val : U → G)) hU.isOpenMap_subtype_val
  apply SetLike.coe_injective
  rw [Subgroup.topologicalClosure_coe, Subgroup.coe_top, ← dense_iff_closure_eq]
  refine hd2.mono fun y hy => ?_
  have h1 : π y ∈ (Subgroup.zpowers g ⊔ J).map π := ⟨y, hy, rfl⟩
  have h2 : J.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [Subgroup.map_sup, h2, sup_bot_eq, MonoidHom.map_zpowers] at h1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h1
  have hnS : n ∈ S := by
    show π g ^ n ∈ U.map π
    rw [hn]; exact ⟨y, y.2, rfl⟩
  rw [hf, AddSubgroup.mem_closure_singleton] at hnS
  obtain ⟨k, rfl⟩ := hnS
  have h3 : π ((φ ^ k)⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, map_zpow, hφ, ← hn, ← zpow_mul, smul_eq_mul, mul_comm f k, inv_mul_cancel]
  have h4 : (φ ^ k)⁻¹ * (y : G) ∈ J := by
    rw [← QuotientGroup.ker_mk' J]; exact h3
  have h5 : y = (⟨φ, hφU⟩ : U) ^ k * ((((⟨φ, hφU⟩ : U) ^ k))⁻¹ * y) := by
    rw [mul_inv_cancel_left]
  rw [SetLike.mem_coe, h5]
  refine Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ _) ?_
  rw [Subgroup.mem_subgroupOf]
  simpa using h4

variable {l : ℕ} [hl : Fact l.Prime]

theorem root_mem_Kur {ζ : Om l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (h : ζ ^ m = 1) :
    ζ ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, h⟩

theorem normal_fix : (MaximalUnramifiedExtension l).fixingSubgroup.Normal := by
  refine ⟨fun σ hσ h => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  obtain ⟨m, hm, hlm, H⟩ := exists_level hx
  refine H _ 1 fun ζ hζ => ?_
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply,
    hσ _ (root_mem_Kur hm hlm (by rw [← map_pow, hζ, map_one])), ← AlgEquiv.mul_apply,
    mul_inv_cancel]

theorem norm_sub_lt {σ : GQ l} (hσ : σ ∈ (MaximalUnramifiedExtension l).fixingSubgroup) (x : Om l) (hx : ‖x‖ ≤ 1) :
    ‖σ x - x‖ < 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  have key : ∀ y : Om l, ‖y‖ < 1 → ‖σ y - y‖ < 1 := fun y hy => by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_gal]; exact hy
    · rw [norm_neg]; exact hy
  rcases hx.lt_or_eq with h | h
  · exact key x h
  · obtain ⟨ζ, m, hm, hlm, hζ, hn⟩ := FrobLaws.exists_root (l := l) x h
    have := key _ hn
    rw [map_sub, hσ ζ (root_mem_Kur hm hlm hζ)] at this
    simpa using this

theorem exists_gen_top :
    ∃ g : GQ l, (Subgroup.zpowers g ⊔ (MaximalUnramifiedExtension l).fixingSubgroup).topologicalClosure = ⊤ := by
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨g, hg⟩ := exists_ext σ
  refine ⟨g, ?_⟩
  let H : ClosedSubgroup (GQ l) :=
    ⟨(Subgroup.zpowers g ⊔ (MaximalUnramifiedExtension l).fixingSubgroup).topologicalClosure,
      Subgroup.isClosed_topologicalClosure _⟩
  have h1 := InfiniteGalois.fixingSubgroup_fixedField H
  have h2 : IntermediateField.fixedField (H : Subgroup (GQ l)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hK : x ∈ MaximalUnramifiedExtension l := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
      exact fun f hf => hx f (Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hf))
    have hgx : g x = x := hx g (Subgroup.le_topologicalClosure _
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers g)))
    obtain ⟨c, hc⟩ := (frob_laws l σ hσ).2.2 ⟨x, hK⟩ (Subtype.ext (by rw [← hg]; exact hgx))
    rw [IntermediateField.mem_bot]
    exact ⟨c, congrArg Subtype.val hc⟩
  rw [h2, IntermediateField.fixingSubgroup_bot] at h1
  exact h1.symm

end GlobalTheory.FrobGen

theorem GlobalTheory.exists_topologicalClosure_zpowers_sup_inertia (l : ℕ) [Fact l.Prime] (K : FinExt l) :
    ∃ φ : ↥(GK K), (Subgroup.zpowers φ ⊔ IK K).topologicalClosure = ⊤ := by
  obtain ⟨g, hg⟩ := GlobalTheory.FrobGen.exists_gen_top (l := l)
  haveI := GlobalTheory.FrobGen.normal_fix (l := l)
  haveI := K.2
  obtain ⟨φ, hφ⟩ := GlobalTheory.FrobGen.exists_gen_of_isOpen _ g (GK K) K.1.fixingSubgroup_isOpen hg
  refine ⟨φ, eq_top_iff.2 (hφ ▸ ?_)⟩
  refine Subgroup.topologicalClosure_minimal _ ?_ (Subgroup.isClosed_topologicalClosure _)
  refine le_trans (sup_le_sup_left (fun σ hσ => ?_) _) (Subgroup.le_topologicalClosure _)
  exact Subgroup.subset_closure fun x hx => GlobalTheory.FrobGen.norm_sub_lt hσ x hx
