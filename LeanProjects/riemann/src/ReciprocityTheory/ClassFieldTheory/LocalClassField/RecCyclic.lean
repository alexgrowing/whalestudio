import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen
import ReciprocityTheory.ClassFieldTheory.LocalClassField.CyclicBr
import ReciprocityTheory.ClassFieldTheory.LocalClassField.EqZeroOfMemBrKerOfCoprime
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclicB

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

def RecCyc.kerChar (χ : charGrp (GK p K)) : Subgroup (GK p K) where
  carrier := {g | χ.1 (Additive.ofMul g) = 0}
  one_mem' := map_zero χ.1
  mul_mem' := fun {a b} ha hb => by
    show χ.1 (Additive.ofMul a + Additive.ofMul b) = 0
    rw [map_add, show χ.1 (Additive.ofMul a) = 0 from ha, show χ.1 (Additive.ofMul b) = 0 from hb, add_zero]
  inv_mem' := fun {a} ha => by
    show χ.1 (- Additive.ofMul a) = 0
    rw [map_neg, show χ.1 (Additive.ofMul a) = 0 from ha, neg_zero]

theorem exists_field_of_char (hK : FiniteDimensional ℚ_[p] K) (χ : charGrp (GK p K)) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), K ≤ L ∧ FiniteDimensional ℚ_[p] L ∧ ∀ g, χ.1 (Additive.ofMul g) = 0 ↔ g ∈ subG p K L := by
  obtain ⟨L, h, hL, e⟩ := exists_subG_eq_of_isOpen hK (RecCyc.kerChar χ) (χ.2 {0})
  exact ⟨L, h, hL, fun g => by rw [e]; exact Iff.rfl⟩

theorem normal_of_char (χ : charGrp (GK p K)) (hχ : ∀ g, χ.1 (Additive.ofMul g) = 0 ↔ g ∈ subG p K L) :
    (subG p K L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [← hχ] at hn ⊢
  rw [ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg, hn]
  abel

noncomputable def RecCyc.charBar [(subG p K L).Normal] (χ : charGrp (GK p K)) (hχ : TrivOn p K L χ) :
    Additive (GalLK p K L) →+ QZ :=
  MonoidHom.toAdditiveLeft (QuotientGroup.lift (subG p K L) (AddMonoidHom.toMultiplicativeRight χ.1)
    (fun g hg => congrArg Multiplicative.ofAdd (hχ g hg)))

theorem RecCyc.charBar_injective [(subG p K L).Normal] (χ : charGrp (GK p K))
    (hχ : ∀ g, χ.1 (Additive.ofMul g) = 0 ↔ g ∈ subG p K L) :
    Injective (RecCyc.charBar χ (fun g hg => (hχ g).2 hg)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  have ha' : a = Additive.ofMul (QuotientGroup.mk g) := by rw [hg]; rfl
  rw [ha'] at ha
  have ha2 : χ.1 (Additive.ofMul g) = 0 := ha
  rw [hχ] at ha2
  rw [ha']
  exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff g).2 ha2)

theorem cyclic_of_char (hL : FiniteDimensional ℚ_[p] L) (χ : charGrp (GK p K)) (hχ : ∀ g, χ.1 (Additive.ofMul g) = 0 ↔ g ∈ subG p K L)
    [(subG p K L).Normal] : ∃ g₀ : GalLK p K L, ∀ g, g ∈ Subgroup.zpowers g₀ := by
  have := finite_GalLK (K := K) hL
  exact RecCyc.exists_gen_of_injective _ (RecCyc.charBar_injective χ hχ)

theorem RecCyc.cls_layer_eq_zero_iff (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (a : Kˣ) (χ : charGrp (GK p K))
    (hχ : ∀ g, χ.1 (Additive.ofMul g) = 0 ↔ g ∈ subG p K L) [(subG p K L).Normal] [Fintype (GalLK p K L)]
    [DiscreteTopology (GalLK p K L)] (tb : GalLK p K L → ℚ)
    (htχ : ∀ g : GK p K, (QuotientAddGroup.mk (tb (QuotientGroup.mk g)) : QZ) = χ.1 (Additive.ofMul g))
    (mb : (Fin 2 → GalLK p K L) → ℤ) (hmb : ∀ q, (mb q : ℚ) = tb (q 0) + tb (q 1) - tb (q 0 * q 1))
    (z : (layer p K L).coch.X 2) (hza : ∀ q, z.1 q = mb q • RecCyc.kToLayer p K L (Additive.ofMul a)) :
    z ∈ (layer p K L).coch.B 2 ↔ a ∈ normGrp p K L := by
  obtain ⟨g₀, hg⟩ := cyclic_of_char hL χ hχ
  rw [RecCyc.mem_normGrp_iff_layer h]
  refine RecCyc.defect_mem_B_iff (layer p K L) hmb _ (fun g => RecCyc.kToLayer_rho g _) z hza g₀ hg ?_
  rintro e ⟨j, hj⟩
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g₀
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← hχ, ofMul_pow, map_nsmul, ← htχ]
  show (QuotientAddGroup.mk (e • tb (QuotientGroup.mk σ)) : QZ) = 0
  rw [nsmul_eq_mul, hj, QuotientAddGroup.eq_zero_iff]
  exact ⟨j, rfl⟩

theorem pairBr_eq_zero_iff (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (a : Kˣ) (χ : charGrp (GK p K))
    (hχ : ∀ g, χ.1 (Additive.ofMul g) = 0 ↔ g ∈ subG p K L) :
    pairBr p K a χ = 0 ↔ a ∈ normGrp p K L := by
  have hN : (subG p K L).Normal := normal_of_char χ hχ
  have hT : TrivOn p K L χ := fun g hg => (hχ g).2 hg
  have hF := finite_GalLK (K := K) hL
  have hD : DiscreteTopology (GalLK p K L) := discreteTopology_GalLK hL
  obtain ⟨tb, htb, htχ⟩ := RecCyc.exists_lift_layer χ hT
  obtain ⟨mb, hmb⟩ := RecCyc.exists_defect_layer χ tb htχ
  obtain ⟨z, hz, hza⟩ := RecCyc.exists_defect_cocycle (layer p K L) htb hmb (RecCyc.kToLayer p K L (Additive.ofMul a))
    (fun g => RecCyc.kToLayer_rho g _)
  have key := @RecCyc.cls_layer_eq_zero_iff p _ K L hL h a χ hχ hN (Fintype.ofFinite _) hD tb htχ mb hmb z hza
  rw [RecCyc.pairBr_eq_layerInf a χ tb htb htχ mb hmb z hz hza, ← key, ← Cx.cls_eq_zero_iff hz]
  exact ⟨fun h0 => layer_inflation_h2_injective (h0.trans (map_zero _).symm), fun h0 => by rw [h0, map_zero]⟩

theorem pairK_eq_zero_iff (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (a : Kˣ) (χ : charGrp (GK p K))
    (hχ : ∀ g, χ.1 (Additive.ofMul g) = 0 ↔ g ∈ subG p K L) :
    pairK p K a χ = 0 ↔ a ∈ normGrp p K L := by
  rw [← pairBr_eq_zero_iff hK hL h a χ hχ]
  exact map_eq_zero_iff (invBr p K) (invBr_bijective hK).1

theorem index_normGrp_cyclic (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal] (g₀ : GalLK p K L)
    (hg : ∀ g, g ∈ Subgroup.zpowers g₀) : (normGrp p K L).index = degLK p K L := by
  have hF := finite_GalLK (K := K) hL
  let _ : Fintype (GalLK p K L) := Fintype.ofFinite _
  rw [← card_H0hat_layer hK hL h g₀ hg]
  let f : Kˣ →* Multiplicative (Herbrand.TateZerothCohomology (layer p K L).rho g₀) := AddMonoidHom.toMultiplicativeRight
    ((QuotientAddGroup.mk' _).comp ((RecCyc.kToLayer p K L).codRestrict (Herbrand.dHom (layer p K L).rho g₀).ker
      (fun a => (Herbrand.mem_ker_dHom_iff _ g₀ hg _).2 (fun c => RecCyc.kToLayer_rho c a))))
  have hker : f.ker = normGrp p K L := by
    ext a
    rw [MonoidHom.mem_ker, RecCyc.mem_normGrp_iff_layer h]
    refine Iff.trans (Herbrand.mk_eq_zero_iff (D := Herbrand.dHom (layer p K L).rho g₀)
      (N := Herbrand.nHom (layer p K L).rho) _) ?_
    refine exists_congr fun y => ?_
    rw [Herbrand.nHom_apply]
    exact Iff.rfl
  have hsurj : Surjective f := by
    intro x
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd x)
    obtain ⟨a, ha⟩ := RecCyc.exists_ofK_eq w.1.1
      ((layer_invariant_iff w.1).1 ((Herbrand.mem_ker_dHom_iff _ g₀ hg _).1 w.2))
    refine ⟨a, ?_⟩
    rw [← ofAdd_toAdd x, ← hw]
    exact congrArg (fun w => Multiplicative.ofAdd (QuotientAddGroup.mk w)) (Subtype.ext (Subtype.ext ha))
  rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj]
  exact Nat.card_congr Subgroup.topEquiv.toEquiv

theorem eq_zero_of_pairK_eq_zero (hK : FiniteDimensional ℚ_[p] K) (χ : charGrp (GK p K)) (h : ∀ a, pairK p K a χ = 0) : χ = 0 := by
  obtain ⟨L, hKL, hL, hχ⟩ := exists_field_of_char hK χ
  have hN := normal_of_char χ hχ
  obtain ⟨g₀, hg⟩ := cyclic_of_char hL χ hχ
  have h1 : normGrp p K L = ⊤ := eq_top_iff.2 fun a _ => (pairK_eq_zero_iff hK hL hKL a χ hχ).1 (h a)
  have h2 := index_normGrp_cyclic hK hL hKL g₀ hg
  rw [h1, Subgroup.index_top] at h2
  have h3 : subG p K L = ⊤ := Subgroup.index_eq_one.1 h2.symm
  refine Subtype.ext (AddMonoidHom.ext fun g => ?_)
  exact (hχ (Additive.toMul g)).2 (h3 ▸ Subgroup.mem_top _)

end ReciprocityTheory.DiscreteGroups.LocalClassField
