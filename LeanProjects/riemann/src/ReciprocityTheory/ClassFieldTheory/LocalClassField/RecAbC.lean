import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecFunct
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GabLim
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem ofK_injective : Injective (ofK p K) := by
  intro a b hab
  have h1 : (((Additive.toMul a : Kˣ) : K) : PadicAlgCl p) = (((Additive.toMul b : Kˣ) : K) : PadicAlgCl p) :=
    congrArg (fun y : KbarMult p => ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p)) hab
  exact Additive.toMul.injective (Units.ext (Subtype.ext h1))

theorem exists_ofK_eq (y : KbarMult p) (hy : y ∈ multOf p K) : ∃ a : Kˣ, ofK p K (Additive.ofMul a) = y := by
  have hne : (⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩ : K) ≠ 0 := fun h0 =>
    (Additive.toMul y : (PadicAlgCl p)ˣ).ne_zero (congrArg Subtype.val h0)
  exact ⟨Units.mk0 _ hne, Additive.toMul.injective (Units.ext rfl)⟩

theorem exists_normUnits (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    ∃ ν : Lˣ →* Kˣ, ∀ b, ofK p K (Additive.ofMul (ν b)) = normHom p K L (ofK p L (Additive.ofMul b)) := by
  choose ν hν using fun b : Lˣ => exists_ofK_eq _ (normHom_mem hL h _ (ofK_mem p L (Additive.ofMul b)))
  refine ⟨MonoidHom.mk' ν fun a b => ?_, hν⟩
  apply Additive.ofMul.injective
  apply ofK_injective (p := p) (K := K)
  rw [hν, ofMul_mul, ofMul_mul, map_add, map_add, map_add, hν, hν]

theorem mem_normGrp_iff_exists (a : Kˣ) :
    a ∈ normGrp p K L ↔ ∃ b : Lˣ, ofK p K (Additive.ofMul a) = normHom p K L (ofK p L (Additive.ofMul b)) := by
  rw [mem_normGrp_iff]
  constructor
  · rintro ⟨y, hy, hya⟩
    obtain ⟨b, rfl⟩ := exists_ofK_eq y hy
    exact ⟨b, hya.symm⟩
  · rintro ⟨b, hb⟩
    exact ⟨_, ofK_mem p L _, hb.symm⟩

theorem normGrp_eq_range (ν : Lˣ →* Kˣ)
    (hν : ∀ b, ofK p K (Additive.ofMul (ν b)) = normHom p K L (ofK p L (Additive.ofMul b))) :
    normGrp p K L = ν.range := by
  ext a
  rw [mem_normGrp_iff_exists, MonoidHom.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, Additive.ofMul.injective (ofK_injective ((hν b).trans hb.symm))⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, hν b⟩

theorem normGrp_eq_map {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L') (h : K ≤ L) (h' : L ≤ L')
    (ν : Lˣ →* Kˣ) (hν : ∀ b, ofK p K (Additive.ofMul (ν b)) = normHom p K L (ofK p L (Additive.ofMul b))) :
    normGrp p K L' = (normGrp p L L').map ν := by
  ext a
  rw [mem_normGrp_iff_exists, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨b, hb⟩ := exists_ofK_eq _ (normHom_mem (K := L) hL' h' _ (ofK_mem p L' (Additive.ofMul c)))
    refine ⟨b, (mem_normGrp_iff_exists b).2 ⟨c, hb⟩, Additive.ofMul.injective (ofK_injective ?_)⟩
    rw [hν, hb, normHom_trans hL' h h' _ (ofK_mem p L' _), hc]
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨c, hc⟩ := (mem_normGrp_iff_exists b).1 hb
    exact ⟨c, by rw [hν, hc, normHom_trans hL' h h' _ (ofK_mem p L' _)]⟩

theorem index_normGrp_tower_le {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : FiniteDimensional ℚ_[p] L) (hL' : FiniteDimensional ℚ_[p] L')
    (h : K ≤ L) (h' : L ≤ L') :
    (normGrp p K L').index ≤ (normGrp p L L').index * (normGrp p K L).index := by
  obtain ⟨ν, hν⟩ := exists_normUnits hL h
  rw [normGrp_eq_map hL' h h' ν hν, normGrp_eq_range ν hν, Subgroup.index_map]
  have := finiteIndex_normGrp hL hL' h'
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd (Nat.pos_of_ne_zero this.index_ne_zero)
    (Subgroup.index_dvd_of_le le_sup_left))

theorem IsAbLK.base {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL : IsAbLK p K L) (h : K ≤ M) (h' : M ≤ L) : IsAbLK p M L := by
  refine ⟨h', hL.fin, ?_⟩
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  have h1 : ⁅resGK h g₁, resGK h g₂⁆ ∈ subG p K L :=
    hL.comm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  rw [← map_commutatorElement] at h1
  exact h1

theorem resChar_eq_zero (h : K ≤ L) (χ : charGrp (GK p K)) (hχ : TrivOn p K L χ) : resChar h χ = 0 := by
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro s
  exact hχ (resGK h (Additive.toMul s)) ((range_resGK h).le ⟨_, rfl⟩)

theorem local_pairing_eq_zero_of_mem_normGroup (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (a : Kˣ)
    (ha : a ∈ normGrp p K L) (χ : charGrp (GK p K)) (hχ : TrivOn p K L χ) : pairK p K a χ = 0 := by
  obtain ⟨b, hb⟩ := (mem_normGrp_iff_exists a).1 ha
  rw [pairK_norm hK hL h b a hb χ, resChar_eq_zero h χ hχ, pairK_zero]

theorem index_normGrp_le_step (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) (g : GK p K) (χ : charGrp (GK p K))
    (hχ : TrivOn p K L χ) (hg : χ.1 (Additive.ofMul g) ≠ 0) :
    ∃ M : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] M ∧ IsAbLK p M L ∧ degLK p M L < degLK p K L ∧
      degLK p K L = degLK p K M * degLK p M L ∧ (normGrp p K L).index ≤ (normGrp p M L).index * degLK p K M := by
  obtain ⟨M, hKM, hM, hMχ⟩ := exists_field_of_char hK χ
  have hn := normal_of_char χ hMχ
  obtain ⟨g₀, hg₀⟩ := cyclic_of_char hM χ hMχ
  have hML : M ≤ L := by
    have := (subG_le_iff (L' := L) hKM).1 fun s hs => (hMχ s).1 (hχ s hs)
    rwa [sup_eq_right.2 hL.le] at this
  have hdeg := degLK_mul hKM hML
  have h1 : degLK p K M ≠ 1 := fun h1 => by
    have : subG p K M = ⊤ := Subgroup.index_eq_one.1 h1
    exact hg ((hMχ g).2 (this ▸ Subgroup.mem_top g))
  have h2 : 1 < degLK p K M := lt_of_le_of_ne (degLK_pos hM) (Ne.symm h1)
  refine ⟨M, hM, hL.base hKM hML, ?_, hdeg, ?_⟩
  · rw [hdeg]
    exact lt_mul_of_one_lt_left (degLK_pos hL.fin) h2
  · rw [← index_normGrp_cyclic hK hM hKM g₀ hg₀]
    exact index_normGrp_tower_le hM hL.fin hKM hML

end ReciprocityTheory.DiscreteGroups.LocalClassField
