import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeSeqExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapCompAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExcisionConeMapQuasiIsoStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.NatRef

variable {R : Type} [CommRing R]

theorem cpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _
  congr 1; ext1; simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem cpull_inr_map {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (I : Cx R) (n : ℤ) (x : CohomologyClass (mappingCone φ₂) I n) :
    cpull (mappingCone.inr φ₁) I n (cpull (mappingCone.map φ₁ φ₂ a b comm) I n x) =
      cpull b I n (cpull (mappingCone.inr φ₂) I n x) := by
  rw [← cpull_comp, ← cpull_comp]
  congr 2
  simp [mappingCone.map]

theorem cpull_map_fst {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (I : Cx R) (n : ℤ) (x : CohomologyClass K₂ I n) :
    cpull (mappingCone.map φ₁ φ₂ a b comm) I (n + 1) (cpre (mappingCone.fst φ₂) I n (n + 1) (by omega) x) =
      cpre (mappingCone.fst φ₁) I n (n + 1) (by omega) (cpull a I n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _
  congr 1; ext1
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  have key : (Cochain.ofHom (mappingCone.map φ₁ φ₂ a b comm)).comp (mappingCone.fst φ₂).1 (zero_add 1) =
      (mappingCone.fst φ₁).1.comp (Cochain.ofHom a) (add_zero 1) := by
    refine (mappingCone.ext_cochain_from_iff φ₁ 0 1 rfl).2 ⟨?_, ?_⟩
    · rw [← Cochain.comp_assoc _ _ _ (show -1 + 0 = -1 by omega) (zero_add 1) (by omega), ← Cochain.comp_assoc _ _ _ (show -1 + 1 = 0 by omega) (add_zero 1) (by omega)]
      simp [mappingCone.map, Cochain.comp_assoc_of_second_is_zero_cochain]
    · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain]
      simp [mappingCone.map, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, key, Cochain.comp_assoc_of_second_is_zero_cochain]

end GlobalTheory.EtC.NatRef

namespace GlobalTheory.EtC.NatRef
variable {R : Type} [CommRing R]

theorem abstract_nat {K L K' L' : Cx R} (φ : K ⟶ L) (φ' : K' ⟶ L') (a : K' ⟶ K) (b : L' ⟶ L)
    (comm : φ' ≫ b = a ≫ φ) (I : Cx R) (n : ℤ)
    (hbij : Function.Bijective (cpull (mappingCone.map φ' φ a b comm) I (n + 1))) :
    ∃ δ : CohomologyClass K' I n →+ CohomologyClass L I (n + 1),
      Function.Exact δ (fun x : CohomologyClass L I (n + 1) => (cpull φ I (n + 1) x, cpull b I (n + 1) x)) ∧
      ∀ {K₂ L₂ : Cx R} (φ₂ : K₂ ⟶ L₂) (a₂ : K₂ ⟶ K') (b₂ : L₂ ⟶ L') (comm₂ : φ₂ ≫ b₂ = a₂ ≫ φ')
        (a₃ : K₂ ⟶ K) (b₃ : L₂ ⟶ L) (comm₃ : φ₂ ≫ b₃ = a₃ ≫ φ), a₂ ≫ a = a₃ → b₂ ≫ b = b₃ →
        Function.Injective (cpull (mappingCone.map φ₂ φ a₃ b₃ comm₃) I (n + 1)) →
        ∀ (w : CohomologyClass K' I n) (c : CohomologyClass K I n), cpull a₂ I n w = cpull a₃ I n c → δ w = 0 := by
  set m := mappingCone.map φ' φ a b comm
  let e := AddEquiv.ofBijective _ hbij
  have he : ∀ y, cpull m I (n + 1) (e.symm y) = y := e.apply_symm_apply
  have he' : ∀ r, e.symm (cpull m I (n + 1) r) = r := e.symm_apply_apply
  have P1 := (coneSeq_exact R φ I (n + 1)).1
  have P3 := (coneSeq_exact R φ' I n).2.2
  have P3φ := (coneSeq_exact R φ I n).2.2
  refine ⟨(cpull (mappingCone.inr φ) I (n + 1)).comp
    (e.symm.toAddMonoidHom.comp (cpre (mappingCone.fst φ') I n (n + 1) (by omega))), ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hx1 : cpull φ I (n + 1) x = 0 := congrArg Prod.fst hx
      have hx2 : cpull b I (n + 1) x = 0 := congrArg Prod.snd hx
      obtain ⟨r, rfl⟩ := (P1 x).1 hx1
      have h0 : cpull (mappingCone.inr φ') I (n + 1) (cpull m I (n + 1) r) = 0 := by
        rw [cpull_inr_map]; exact hx2
      obtain ⟨w, hw⟩ := (P3 _).1 h0
      refine ⟨w, ?_⟩
      change cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w)) = _
      rw [hw, he']
    · rintro ⟨w, rfl⟩
      refine Prod.ext ((P1 _).2 ⟨_, rfl⟩) ?_
      change cpull b I (n + 1) (cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w))) = 0
      rw [← cpull_inr_map φ' φ a b comm, he]
      exact (P3 _).2 ⟨w, rfl⟩
  · intro K₂ L₂ φ₂ a₂ b₂ comm₂ a₃ b₃ comm₃ ha hb hinj w c hwc
    subst ha hb
    have hM : mappingCone.map φ₂ φ (a₂ ≫ a) (b₂ ≫ b) comm₃ =
        mappingCone.map φ₂ φ' a₂ b₂ comm₂ ≫ m := mappingCone.map_comp φ₂ φ' φ a₂ b₂ comm₂ a b comm
    have hr : e.symm (cpre (mappingCone.fst φ') I n (n + 1) (by omega) w) =
        cpre (mappingCone.fst φ) I n (n + 1) (by omega) c := by
      apply hinj
      rw [cpull_map_fst, ← hwc, hM, cpull_comp, he, cpull_map_fst]
    change cpull (mappingCone.inr φ) I (n + 1) (e.symm (cpre (mappingCone.fst φ') I n (n + 1) _ w)) = 0
    rw [hr]
    exact (P3φ _).2 ⟨c, rfl⟩

end GlobalTheory.EtC.NatRef

namespace GlobalTheory.EtC

open NatRef in

theorem excision_boundary_natural_refine : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → ∀ (n i : ℤ), ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A₂ : Type) [CommRing A₂] [Algebra A A₂] [Algebra A' A₂] [IsScalarTower A A' A₂], IsExcisionNbhd A A₂ f → ∀ (φ : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ∀ (w : Ht q (sp (Localization.Away (algebraMap A A' f))) n i) (b : Ht q (sp (Localization.Away f)) n i), pull _ (spMap φ) _ _ w = pull _ (spMap (Localization.awayMap (algebraMap A A₂) f)) _ _ b → δ w = 0 := by
  intro q A A' _ _ _ f hN n i
  have hbij : ∀ (B : Type) [CommRing B] [Algebra A B], IsExcisionNbhd A B f →
      Function.Bijective (cpull (excisionConeMap (ZMod q) A B f) (res (ZMod q) (tw q i)) (n + 1)) := by
    intro B _ _ hB
    haveI := GlobalTheory.T.excisionConeMap_quasiIso' (ZMod q) A B f hB
    exact quasiIso_hypercohomology_bijective' (ZMod q) (excisionConeMap (ZMod q) A B f) (tw q i) (n + 1)
  obtain ⟨δ, hex, hnat⟩ := abstract_nat _ _ _ _ (excision_square_comm (ZMod q) A A' f) (res (ZMod q) (tw q i)) n
    (hbij A' hN)
  refine ⟨δ, hex, ?_⟩
  intro A₂ _ _ _ _ h₂ φ hφ w b hwb
  refine hnat ((chains (ZMod q)).map (spMap (algebraMap A₂ (Localization.Away (algebraMap A A₂ f)))))
    ((chains (ZMod q)).map (spMap φ)) ((chains (ZMod q)).map (spMap (algebraMap A' A₂))) ?_ _ _
    (excision_square_comm (ZMod q) A A₂ f) ?_ ?_ (hbij A₂ h₂).1 w b hwb
  · rw [chains_spMap_comp, chains_spMap_comp, hφ]
  · rw [chains_spMap_comp]
    congr 2
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    rw [RingHom.comp_assoc, awayMap_comp_algebraMap, awayMap_comp_algebraMap, ← RingHom.comp_assoc, hφ,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  · rw [chains_spMap_comp, ← IsScalarTower.algebraMap_eq]

end GlobalTheory.EtC
