import Formalism.SharpRestriction.Divisibility.WeightFamilies

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions NumberField

theorem nonempty_zero_weight (D : D7) (j : ℕ) : Nonempty (Formalism.MainNotions.WeightFamilies.Wt D j) :=
  ⟨{ aP := fun _ _ => 0, aM := fun _ _ => 0, aPlus_antitone := fun _ _ _ _ => le_rfl,
     aM_anti := fun _ _ _ _ => le_rfl, n := 0, n_even := ⟨0, rfl⟩ }⟩

def OsRingOfIntegers (D : D7) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K), Nonempty (𝓞 K ≃+* D.what₂.O)

def OsConcrete (D : D7) : Prop :=
  Function.Injective D.what₂.OtoLL ∧ ∃ K : IntermediateField ℚ D.what₂.LL,
    Set.range D.what₂.OtoLL = {x | x ∈ K ∧ IsIntegral ℤ x}

theorem OsRingOfIntegers_of_concrete (D : D7) (h : OsConcrete D) : OsRingOfIntegers D := by
  obtain ⟨hinj, K, hK⟩ := h
  letI : NumberField D.what₂.LL := D.nfLL
  haveI : FiniteDimensional ℚ K := inferInstance
  haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  let g : 𝓞 K →+* D.what₂.LL := (algebraMap K D.what₂.LL).comp (algebraMap (𝓞 K) K)
  have hg : Function.Injective g :=
    (algebraMap K D.what₂.LL).injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hrange : g.range = D.what₂.OtoLL.range := by
    ext y
    rw [RingHom.mem_range, RingHom.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      have hy : g a ∈ Set.range D.what₂.OtoLL := by
        rw [hK, Set.mem_setOf_eq]
        exact ⟨(algebraMap (𝓞 K) K a).2,
          IsIntegral.algebraMap (R := ℤ) (A := K) (B := D.what₂.LL)
            ((IsIntegralClosure.isIntegral_iff (A := 𝓞 K) (R := ℤ) (B := K)).mpr ⟨a, rfl⟩)⟩
      exact hy
    · rintro ⟨x, rfl⟩
      have hx : D.what₂.OtoLL x ∈ Set.range D.what₂.OtoLL := ⟨x, rfl⟩
      rw [hK, Set.mem_setOf_eq] at hx
      obtain ⟨hxK, hxI⟩ := hx
      have hz : IsIntegral ℤ (⟨D.what₂.OtoLL x, hxK⟩ : K) :=
        (isIntegral_algebraMap_iff (algebraMap K D.what₂.LL).injective).mp hxI
      obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K) (R := ℤ) (B := K)).mp hz
      refine ⟨a, ?_⟩
      show algebraMap K D.what₂.LL (algebraMap (𝓞 K) K a) = _
      rw [ha]
      rfl
  exact ⟨K, inferInstance, inferInstance, ⟨(RingEquiv.ofBijective g.rangeRestrict
    ⟨fun a b hab => hg (by have h := congrArg Subtype.val hab; exact h), g.rangeRestrict_surjective⟩).trans
    ((RingEquiv.subringCongr hrange).trans (RingEquiv.ofBijective D.what₂.OtoLL.rangeRestrict
      ⟨fun a b hab => hinj (by have h := congrArg Subtype.val hab; exact h), D.what₂.OtoLL.rangeRestrict_surjective⟩).symm)⟩⟩

def zeroCuspModel (D : D7) (K : Type) [Field K] [NumberField K] (e : 𝓞 K ≃+* D.what₂.O) : Formalism.MainNotions.WeightFamilies.Prov D where
  KO := K
  eO := e
  Cusp := fun _ _ => PUnit
  Mlat := fun _ _ => ⊤
  supN := fun _ _ _ _ => 0
  supN_nonneg := fun _ _ _ _ => le_rfl
  supN_eq_zero := fun _ _ _ _ => ⟨fun _ => Subsingleton.elim _ _, fun _ => rfl⟩
  supN_smul := fun _ _ _ _ _ => (mul_zero _).symm
  supN_add := fun _ _ _ _ _ => (add_zero (0 : ℝ)).symm.le
  l2NormAlt := fun _ _ _ _ => 0
  l2Norm_nonneg_bis := fun _ _ _ _ => le_rfl
  l2Norm_eq_zero_iff := fun _ _ _ _ => ⟨fun _ => Subsingleton.elim _ _, fun _ => rfl⟩
  l2Norm_smul_alt := fun _ _ _ _ _ => (mul_zero _).symm
  l2Norm_add_le' := fun _ _ _ _ _ => (add_zero (0 : ℝ)).symm.le
  l2Norm_le_supNorm_alt := fun _ _ _ _ => le_rfl
  Cu := fun _ => Empty
  Xc := fun _ c => c.elim
  Xc_lat := fun _ c => c.elim
  FJt := fun _ _ _ _ => PUnit
  sg := fun _ _ _ _ => 0

theorem zero_cusp_model_subsingleton (D : D7) (K : Type) [Field K] [NumberField K] (e : 𝓞 K ≃+* D.what₂.O) (j : ℕ)
    (w : Formalism.MainNotions.WeightFamilies.Wt D j) : Subsingleton ((zeroCuspModel D K e).Cusp j w) :=
  inferInstanceAs (Subsingleton PUnit)

theorem nonempty_cusp_provision (D : D7) (h : OsRingOfIntegers D) : Nonempty (Formalism.MainNotions.WeightFamilies.Prov D) := by
  obtain ⟨K, hf, hn, ⟨e⟩⟩ := h
  exact ⟨zeroCuspModel D K e⟩

theorem nonempty_cusp_provision_iff (D : D7) : Nonempty (Formalism.MainNotions.WeightFamilies.Prov D) ↔ OsRingOfIntegers D :=
  ⟨fun ⟨p⟩ => ⟨p.KO, p.fKO, p.nfKO, ⟨p.eO⟩⟩, nonempty_cusp_provision D⟩

end Formalism.MainNotions.DIV.Inh

end
