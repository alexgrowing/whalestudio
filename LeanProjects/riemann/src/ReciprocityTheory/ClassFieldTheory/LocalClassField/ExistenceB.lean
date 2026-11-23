import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.PairKEqZeroOfMemNormGrp
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormLimit
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem exists_maximal_exponent_abelian_extension (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hfin : Finite {χ : charGrp (GK p K) // n • χ = 0}) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), IsAbLK p K L ∧ ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0 := by
  let U : Subgroup (GK p K) :=
    { carrier := {g | ∀ χ : charGrp (GK p K), n • χ = 0 → χ.1 (Additive.ofMul g) = 0}
      one_mem' := fun χ _ => map_zero χ.1
      mul_mem' := fun {a b} ha hb χ h => by
        show χ.1 (Additive.ofMul a + Additive.ofMul b) = 0
        rw [map_add, ha χ h, hb χ h, add_zero]
      inv_mem' := fun {a} ha χ h => by
        show χ.1 (- Additive.ofMul a) = 0
        rw [map_neg, ha χ h, neg_zero] }
  have hU : IsOpen (U : Set (GK p K)) := by
    have h1 : (U : Set (GK p K)) = ⋂ χ : {χ : charGrp (GK p K) // n • χ = 0},
        {g : GK p K | χ.1.1 (Additive.ofMul g) = 0} := by
      ext g
      rw [Set.mem_iInter]
      exact ⟨fun h χ => h χ.1 χ.2, fun h χ hχ => h ⟨χ, hχ⟩⟩
    rw [h1]
    exact isOpen_iInter_of_finite fun χ => IsLocallyConstant.isOpen_fiber χ.1.2 0
  obtain ⟨L, hKL, hLfin, hLU⟩ := exists_subG_eq_of_isOpen hK U hU
  refine ⟨L, ⟨hKL, hLfin, ?_⟩, fun χ => ⟨fun hχ => ?_, fun hχ g hg => ?_⟩⟩
  · rw [hLU, commutator_def, Subgroup.commutator_le]
    intro a _ b _ χ _
    show χ.1 (Additive.ofMul a + Additive.ofMul b + - Additive.ofMul a + - Additive.ofMul b) = 0
    rw [map_add, map_add, map_add, map_neg, map_neg]
    abel
  · refine Subtype.ext (AddMonoidHom.ext fun x => ?_)
    show n • χ.1 x = 0
    rw [← map_nsmul]
    refine hχ (Additive.toMul x ^ n) ?_
    rw [hLU]
    intro ψ hψ
    show ψ.1 (n • x) = 0
    rw [map_nsmul]
    exact congrArg (fun f : charGrp (GK p K) => f.1 x) hψ
  · rw [hLU] at hg
    exact hg χ hχ

theorem exists_conj {K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)} (h₀ : K₀ ≤ K) (hK₀ : ∀ (σ : GK p K₀), ∀ x ∈ K, σ x ∈ K)
    (σ : GK p K₀) :
    ∃ c : GK p K →* GK p K, Continuous c ∧ ∀ g, resGK h₀ (c g) = σ * resGK h₀ g * σ⁻¹ := by
  have hn : (subG p K₀ K).Normal := subG_normal_of_stable hK₀
  obtain ⟨e, he, hc, hc'⟩ := exists_equiv_subG h₀
  refine ⟨(e.symm.toMonoidHom.comp (MulAut.conjNormal σ : MulAut (subG p K₀ K)).toMonoidHom).comp e.toMonoidHom, ?_, ?_⟩
  · refine hc'.comp (Continuous.comp ?_ hc)
    refine Continuous.subtype_mk (f := fun h : subG p K₀ K => σ * (h : GK p K₀) * σ⁻¹) ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  · intro g
    show resGK h₀ (e.symm (MulAut.conjNormal σ (e g))) = _
    rw [← he (e.symm _), e.apply_symm_apply, MulAut.conjNormal_apply, he]

theorem maximal_exponent_extension_stable {K₀ : IntermediateField ℚ_[p] (PadicAlgCl p)} (h₀ : K₀ ≤ K) (hK₀ : ∀ (σ : GK p K₀), ∀ x ∈ K, σ x ∈ K) {n : ℕ}
    (hL : IsAbLK p K L) (hL' : ∀ χ : charGrp (GK p K), TrivOn p K L χ ↔ n • χ = 0) (σ : GK p K₀) (x : PadicAlgCl p)
    (hx : x ∈ L) : σ x ∈ L := by
  rw [mem_iff_fixed hL.le]
  intro g hg
  obtain ⟨c, hc, hcg⟩ := exists_conj h₀ hK₀ σ⁻¹
  suffices hmem : c g ∈ subG p K L by
    have h1 : resGK h₀ (c g) x = x := hmem x hx
    rw [hcg, inv_inv] at h1
    have h3 : σ ((σ⁻¹ * resGK h₀ g * σ) x) = g (σ x) := by
      show σ (σ⁻¹ (g (σ x))) = g (σ x)
      exact σ.apply_symm_apply _
    rw [h1] at h3
    exact h3.symm
  by_contra hcon
  obtain ⟨χ, hχ, hne⟩ := exists_char_ne_zero hL (c g) hcon
  let χ' : charGrp (GK p K) := ⟨χ.1.comp (MonoidHom.toAdditive c),
    (show IsLocallyConstant fun g : GK p K => χ.1 (Additive.ofMul g) from χ.2).comp_continuous hc⟩
  have hχ' : n • χ' = 0 := by
    refine Subtype.ext (AddMonoidHom.ext fun y => ?_)
    exact congrArg (fun f : charGrp (GK p K) => f.1 (MonoidHom.toAdditive c y)) ((hL' χ).1 hχ)
  exact hne ((hL' χ').2 hχ' g hg)

theorem mem_subG_adjoin (S : Set (PadicAlgCl p)) (g : GK p K) (h : ∀ x ∈ S, g x = x) :
    g ∈ subG p K (IntermediateField.adjoin ℚ_[p] S) := by
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap x => exact (g.restrictScalars ℚ_[p]).commutes x
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem isAbelian_cyclotomic_extension (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    IsAbLK p K (K ⊔ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ n = 1}) := by
  have : NeZero n := ⟨hn.ne'⟩
  have hfinS : {ζ : PadicAlgCl p | ζ ^ n = 1}.Finite := by
    have h1 : {ζ : PadicAlgCl p | ζ ^ n = 1} = ↑(Polynomial.nthRootsFinset n (1 : PadicAlgCl p)) := by
      ext ζ
      simp [Polynomial.mem_nthRootsFinset hn]
    rw [h1]
    exact Finset.finite_toSet _
  refine ⟨le_sup_left, ?_, ?_⟩
  · have := hK
    have := hfinS.to_subtype
    have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ n = 1}) :=
      IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
    exact IntermediateField.finiteDimensional_sup _ _
  · rw [subG_sup, commutator_def, Subgroup.commutator_le]
    intro σ _ τ _
    refine mem_subG_adjoin _ _ fun ζ hζ => ?_
    have hζ' : ζ ^ n = 1 := hζ
    rw [cycN_spec ⁅σ, τ⁆ ζ hζ', map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _),
      Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ', pow_one]

theorem isSolvable_of_abelian_tower {M : IntermediateField ℚ_[p] (PadicAlgCl p)} (hM : IsAbLK p K M) (hL : IsAbLK p M L) [(subG p K L).Normal] :
    Group.IsSolvable (GalLK p K L) := by
  have h2 : derivedSeries (GK p K) 2 ≤ subG p K L := by
    have h1 : derivedSeries (GK p K) 1 ≤ subG p K M := hM.comm
    rw [derivedSeries_succ]
    refine (Subgroup.commutator_mono h1 h1).trans ?_
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [← range_resGK hM.le] at hg₁ hg₂
    obtain ⟨a, rfl⟩ := hg₁
    obtain ⟨b, rfl⟩ := hg₂
    have h3 : ⁅a, b⁆ ∈ subG p M L :=
      hL.comm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
    rw [← map_commutatorElement]
    intro x hx
    exact h3 x hx
  refine ⟨⟨2, ?_⟩⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (subG p K L)), eq_bot_iff, Subgroup.map_le_iff_le_comap]
  intro g hg
  show QuotientGroup.mk' _ g ∈ (⊥ : Subgroup _)
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff g).2 (h2 hg)

end ReciprocityTheory.DiscreteGroups.LocalClassField
