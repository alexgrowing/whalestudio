import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLiftDef

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat NumberField Module IsDedekindDomain

section

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem lframe_mem_locP {P : Ideal (𝓞 E)} [P.IsPrime] {M : Submodule (𝓞 E) S.V} {y : S.V} :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ P M ↔ ∃ s : 𝓞 E, s ∉ P ∧ s • y ∈ M := by
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, h⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, h⟩

theorem lframe_local_global (M : Submodule (𝓞 E) S.V) (y : S.V)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • y ∈ M) : y ∈ M := by
  let I : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) S.V y)
  have hI : ∀ s, s ∈ I ↔ s • y ∈ M := fun s => by
    simp [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  by_cases htop : I = ⊤
  · have h1 : (1 : 𝓞 E) ∈ I := by rw [htop]; trivial
    simpa using (hI 1).1 h1
  · obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I htop
    have hne : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)
    obtain ⟨s, hs, hsy⟩ := h ⟨m, hm.isPrime, hne⟩
    exact absurd (hle ((hI s).2 hsy)) hs

theorem lframe_dual {r : ℕ} {T : E} (F : FlagG S r T) (a : Fin r) :
    ∃ φ : S.V →ₗ[E] E, ∀ b, φ (F.e b) = if b = a then 1 else 0 := by
  let B := Basis.span F.e_indep
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (B.coord a)
  refine ⟨φ, fun b => ?_⟩
  have h1 : F.e b = ((B b : Submodule.span E (Set.range F.e)) : S.V) := (congrArg Subtype.val (Basis.span_apply F.e_indep b)).symm
  have h2 : φ ((B b : Submodule.span E (Set.range F.e)) : S.V) = B.coord a (B b) := by
    rw [← hφ]
    rfl
  rw [h1, h2, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

end

theorem l_frame : UnitriangularFrameIntegral := by
  intro E _ _ _ S r T Λ g F F' hF hF' he U hU x hxΛ hxX
  have hXa := tie_Xa_eq F.fl F'.fl he
  have hX : F'.fl.X = F.fl.X := by rw [tie_X_eq_Xa, tie_X_eq_Xa, hXa]
  have hXL : XLam Λ F' = XLam Λ F := by
    unfold XLam
    rw [show Xsp F' = Xsp F from hX]
  apply lframe_local_global
  intro P
  have := P.isPrime
  have h1P : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  obtain ⟨c, _, _, hc⟩ := hF.1 P
  obtain ⟨c', _, _, hc'⟩ := hF'.1 P
  have hA : ∀ a, c a • F'.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F') := by
    intro a
    have h1 : c a • F.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F') := by
      rw [hXL, hc]
      exact lframe_mem_locP.2 ⟨1, h1P, by rw [one_smul]; exact Submodule.subset_span ⟨a, rfl⟩⟩
    rw [hc'] at h1 ⊢
    obtain ⟨t, ht, h2⟩ := lframe_mem_locP.1 h1
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 h2
    obtain ⟨φ, hφ⟩ := lframe_dual F'.fl a
    have hφ0 : ∀ w ∈ F'.fl.Xa a.val, φ w = 0 := by
      have hle : F'.fl.Xa a.val ≤ LinearMap.ker φ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨i, hi, rfl⟩
        show φ (F'.fl.e i) = 0
        rw [hφ, if_neg]
        intro h
        subst h
        exact lt_irrefl i.val hi
      exact fun w hw => hle hw
    have hea : φ (F.fl.e a) = 1 := by
      have h3 : F.fl.e a = F'.fl.e a - (F'.fl.e a - F.fl.e a) := by abel
      rw [h3, map_sub, hφ, if_pos rfl, hφ0 _ (by rw [hXa]; exact he a), sub_zero]
    have key : algebraMap (𝓞 E) E t * c a = algebraMap (𝓞 E) E (o a) * c' a := by
      have h4 := congrArg φ ho
      simp only [map_sum, LinearMap.map_smul_of_tower, map_smul, hφ, hea, smul_eq_mul, Algebra.smul_def, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h4
      exact h4.symm
    refine lframe_mem_locP.2 ⟨t, ht, ?_⟩
    have h5 : t • (c a • F'.fl.e a) = o a • (c' a • F'.fl.e a) := by
      rw [← algebraMap_smul E t, ← algebraMap_smul E (o a), smul_smul, smul_smul, key]
    rw [h5]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hx1 : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) :=
    lframe_mem_locP.2 ⟨1, h1P, by rw [one_smul]; exact ⟨hxΛ, hxX⟩⟩
  rw [hc] at hx1
  obtain ⟨s, hs, h3⟩ := lframe_mem_locP.1 hx1
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 h3
  have hU1 : s • U x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F') := by
    rw [← LinearMap.map_smul_of_tower, ← ho, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smul_of_tower, map_smul, hU]
    exact Submodule.smul_mem _ _ (hA a)
  obtain ⟨t, ht, h4⟩ := lframe_mem_locP.1 hU1
  exact ⟨t * s, fun h => (P.isPrime.mem_or_mem h).elim ht hs, by rw [mul_smul]; exact h4.1⟩

end Formalism.MainNotions.BridgeLemma

end
