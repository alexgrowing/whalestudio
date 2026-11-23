import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.OpenIdeleCongr

variable {F : Type} [Field F] [NumberField F]

theorem exists_ne_zero_lt_val_subset_of_mem_nhds {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] {s : Set K} {x : K} :
    s ∈ nhds x → ∃ c : K, c ≠ 0 ∧ {y | Valued.v (y - x) < Valued.v c} ⊆ s := by
  rw [Valued.mem_nhds]
  rintro ⟨γ, hγ⟩
  obtain ⟨c, hc⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass (Valued.v : Valuation K Γ)) γ.1
  have hc' : (Valued.v : Valuation K Γ).restrict c = γ.1 := hc
  refine ⟨c, ?_, fun y hy => hγ ?_⟩
  · rintro rfl
    rw [map_zero] at hc'
    exact γ.ne_zero hc'.symm
  · change (Valued.v : Valuation K Γ).restrict (y - x) < γ.1
    rw [← hc', Valuation.restrict_lt_iff]
    exact hy

theorem exists_exp_of_nhds (v : HeightOneSpectrum (𝓞 F)) (u : Set (v.adicCompletion F)) (hu : u ∈ nhds 1) :
    ∃ M : ℕ, ∀ y : v.adicCompletion F, Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ)) → y ∈ u := by
  obtain ⟨c, hc, hsub⟩ := exists_ne_zero_lt_val_subset_of_mem_nhds hu
  have h0 : Valued.v c ≠ 0 := by simpa using hc
  set k := WithZero.log (Valued.v c) with hkdef
  have hk : Valued.v c = WithZero.exp k := (WithZero.exp_log h0).symm
  refine ⟨(-k).toNat + 1, fun y hy => hsub ?_⟩
  show Valued.v (y - 1) < Valued.v c
  refine lt_of_le_of_lt hy ?_
  rw [hk, WithZero.exp_lt_exp]
  have := Int.self_le_toNat (-k)
  push_cast
  omega

end GlobalTheory.OpenIdeleCongr

namespace GlobalTheory.OpenIdeleCongr

variable {F : Type} [Field F] [NumberField F]

theorem isOpen_adicIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  Valued.isOpen_valuationSubring _

theorem finiteSingle_mem_of_nhds (Vf : Set (FiniteAdeleRing (𝓞 F) F)) (hV : Vf ∈ nhds (1 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 F))) (M : ℕ), S.Finite ∧ ∀ v (y : v.adicCompletion F),
      y ∈ v.adicCompletionIntegers F → (v ∈ S → Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ))) →
      finiteSingle F v y ∈ Vf := by
  classical
  have hσ := RestrictedProduct.isOpenEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) isOpen_adicIntegers
  have h1 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite 1 = 1 :=
    RestrictedProduct.ext _ _ fun i => rfl
  have h2 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite ⁻¹' Vf ∈ nhds 1 := by
    apply hσ.continuous.continuousAt.preimage_mem_nhds
    rw [h1]
    exact hV
  rw [nhds_pi, Filter.mem_pi] at h2
  obtain ⟨I, hI, t, ht, hsub⟩ := h2
  have hM : ∀ i : HeightOneSpectrum (𝓞 F), ∃ M : ℕ, ∀ (y : i.adicCompletion F) (hy : y ∈ i.adicCompletionIntegers F),
      Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ)) → (⟨y, hy⟩ : ((i.adicCompletionIntegers F : Set (i.adicCompletion F)))) ∈ t i := by
    intro i
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).mp (ht i)
    obtain ⟨M, hM⟩ := exists_exp_of_nhds i u hu
    exact ⟨M, fun y hy h => hut (hM y h)⟩
  choose M hMs using hM
  refine ⟨I, hI.toFinset.sup M, hI, fun v y hy hS => ?_⟩
  have hmem : (Pi.mulSingle v (⟨y, hy⟩ : ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) :
      (i : HeightOneSpectrum (𝓞 F)) → ((i.adicCompletionIntegers F : Set (i.adicCompletion F)))) ∈ I.pi t := by
    intro i hi
    by_cases hne : i = v
    · subst hne
      rw [Pi.mulSingle_eq_same]
      refine hMs i y hy ((hS hi).trans ?_)
      rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
      exact Finset.le_sup (hI.mem_toFinset.2 hi)
    · rw [Pi.mulSingle_eq_of_ne hne]
      exact mem_of_mem_nhds (ht i)
  have hg := hsub hmem
  have e : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite (Pi.mulSingle v ⟨y, hy⟩) =
      finiteSingle F v y := by
    apply RestrictedProduct.ext
    intro i
    rw [RestrictedProduct.structureMap_apply]
    show _ = Pi.mulSingle v y i
    by_cases hi : i = v
    · subst hi
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi]
      rfl
  rw [← e]
  exact hg

end GlobalTheory.OpenIdeleCongr

namespace GlobalTheory.OpenIdeleCongr

variable {F : Type} [Field F] [NumberField F]

theorem localIdele_mem_of_isOpen (V : Subgroup (Ideles F)) (hV : IsOpen (V : Set (Ideles F))) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 F))) (M : ℕ), S.Finite ∧ ∀ v (x : (v.adicCompletion F)ˣ),
      Valued.v (x : v.adicCompletion F) = 1 →
      (v ∈ S → Valued.v ((x : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M : ℤ))) → localIdele F v x ∈ V := by
  obtain ⟨W, hWo, hWU⟩ := Units.isInducing_embedProduct.isOpen_iff.mp hV
  have hW1 : Units.embedProduct _ (1 : Ideles F) ∈ W := by
    rw [← Set.mem_preimage, hWU]
    exact V.one_mem
  rw [map_one] at hW1
  obtain ⟨W1, hW1n, W2, hW2n, hprod⟩ := mem_nhds_prod_iff.mp (hWo.mem_nhds hW1)
  have hW2' : MulOpposite.op ⁻¹' W2 ∈ nhds (1 : AdeleRing (𝓞 F) F) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hW2n
  have hN : W1 ∩ MulOpposite.op ⁻¹' W2 ∈ nhds ((1 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) :=
    Filter.inter_mem hW1n hW2'
  obtain ⟨Vi, hVi, Vf, hVf, hVprod⟩ := mem_nhds_prod_iff.mp hN
  obtain ⟨S, M, hS, hSV⟩ := finiteSingle_mem_of_nhds Vf hVf
  refine ⟨S, M, hS, fun v x hx hxS => ?_⟩
  have hin : ∀ y : (v.adicCompletion F)ˣ, Valued.v (y : v.adicCompletion F) = 1 →
      (v ∈ S → Valued.v ((y : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M : ℤ))) →
      ((localIdele F v y : Ideles F) : AdeleRing (𝓞 F) F) ∈ W1 ∩ MulOpposite.op ⁻¹' W2 := fun y hy hyS =>
    hVprod ⟨mem_of_mem_nhds hVi, hSV v _ (by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hy.le) hyS⟩
  have hxi : Valued.v ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  have hxiS : v ∈ S → Valued.v (((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤
      WithZero.exp (-(M : ℤ)) := by
    intro hv
    have e : ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1 =
        ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * -((x : v.adicCompletion F) - 1) := by
      rw [mul_neg, mul_sub, Units.inv_mul, mul_one]; ring
    rw [e, map_mul, Valuation.map_neg, hxi, one_mul]
    exact hxS hv
  have h1 := hin x hx hxS
  have h2 := hin x⁻¹ hxi hxiS
  rw [← SetLike.mem_coe, ← hWU, Set.mem_preimage, Units.embedProduct_apply]
  refine hprod ⟨h1.1, ?_⟩
  have h3 := h2.2
  rw [map_inv] at h3
  exact h3

theorem open_subgroup_contains_congr : ∀ (F : Type) [Field F] [NumberField F] (V : Subgroup (Ideles F)),
    IsOpen (V : Set (Ideles F)) → ∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (M : ℕ), S₀ ⊆ S ∧
      (∀ v ∉ S, ∀ x, IsUnitAt v x → localIdele F v x ∈ V) ∧
      ∀ v ∈ S, ∀ a : Fˣ, v.valuation F ((a : F) - 1) ≤ WithZero.exp (-(M : ℤ)) → locUnit F v a ∈ V := by
  intro F _ _ V hV S₀
  classical
  obtain ⟨S₁, M₁, hS₁, key⟩ := localIdele_mem_of_isOpen V hV
  refine ⟨S₀ ∪ hS₁.toFinset, M₁ + 1, Finset.subset_union_left, fun v hv x hx => ?_, fun v _ a ha => ?_⟩
  · refine key v x hx fun hv' => absurd (Finset.mem_union_right _ (hS₁.mem_toFinset.2 hv')) hv
  · rw [locUnit_apply]
    set x := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a with hxdef
    have hxv : (x : v.adicCompletion F) = ((a : F) : v.adicCompletion F) := rfl
    have hsub : Valued.v ((x : v.adicCompletion F) - 1) = v.valuation F ((a : F) - 1) := by
      have e : (x : v.adicCompletion F) - 1 = (((a : F) - 1 : F) : v.adicCompletion F) := by
        show algebraMap F (v.adicCompletion F) (a : F) - 1 = _
        rw [← map_one (algebraMap F (v.adicCompletion F)), ← map_sub]
        rfl
      rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hle : Valued.v ((x : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M₁ : ℤ)) := by
      rw [hsub]
      refine ha.trans ?_
      rw [WithZero.exp_le_exp]
      push_cast
      omega
    have hlt : Valued.v ((x : v.adicCompletion F) - 1) < 1 := by
      rw [hsub]
      refine lt_of_le_of_lt ha ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      push_cast
      omega
    have hunit : Valued.v (x : v.adicCompletion F) = 1 := by
      have := Valuation.map_one_add_of_lt _ hlt
      rwa [add_sub_cancel] at this
    exact key v x hunit fun _ => hle

end GlobalTheory.OpenIdeleCongr
