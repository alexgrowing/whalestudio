import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace GenericCycleCorresp

section LocalizationLength

variable {S T : Type*} [CommRing S] [CommRing T] [Algebra S T] (M : Submonoid S)
  [IsLocalization M T]

theorem length_eq (J W : Ideal S) [W.IsPrime] (hW : Disjoint (M : Set S) W)
    [(W.map (algebraMap S T)).IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J)) =
      Module.length (Localization.AtPrime (W.map (algebraMap S T)))
        (LocalizedModule (W.map (algebraMap S T)).primeCompl (T ⧸ J.map (algebraMap S T))) := by
  set W' := W.map (algebraMap S T)
  set J' := J.map (algebraMap S T)
  have hcomap : W'.comap (algebraMap S T) = W :=
    IsLocalization.under_map_of_isPrime_disjoint M T ‹_› hW
  have hnot : ∀ x : S, x ∉ W → algebraMap S T x ∉ W' := fun x hx h =>
    hx (hcomap ▸ Ideal.mem_comap.mpr h)
  haveI : IsLocalization.AtPrime (Localization.AtPrime W') W := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime W') W'
    unfold IsLocalization.AtPrime at this ⊢
    convert this using 2
    exact hcomap.symm
  let σ : Localization.AtPrime W ≃ₐ[S] Localization.AtPrime W' :=
    IsLocalization.algEquiv W.primeCompl _ _
  let N := LocalizedModule W'.primeCompl (T ⧸ J')
  letI iAN : Module (Localization.AtPrime W) N :=
    Module.compHom N (σ : Localization.AtPrime W →+* Localization.AtPrime W')
  letI iAB : Algebra (Localization.AtPrime W) (Localization.AtPrime W') :=
    (σ : Localization.AtPrime W →+* Localization.AtPrime W').toAlgebra
  haveI : IsScalarTower (Localization.AtPrime W) (Localization.AtPrime W') N :=
    ⟨fun a b n => mul_smul (σ a) b n⟩
  haveI : IsScalarTower S (Localization.AtPrime W) N := by
    refine ⟨fun s a n => ?_⟩
    calc (s • a) • n = σ (s • a) • n := rfl
      _ = (algebraMap S (Localization.AtPrime W') s * σ a) • n := by
        rw [map_smul, Algebra.smul_def]
      _ = algebraMap S (Localization.AtPrime W') s • (σ a • n) := mul_smul _ _ _
      _ = algebraMap T (Localization.AtPrime W') (algebraMap S T s) • (σ a • n) := by
        rw [← IsScalarTower.algebraMap_apply]
      _ = algebraMap S T s • (σ a • n) := algebraMap_smul _ _ _
      _ = s • (σ a • n) := algebraMap_smul _ _ _
      _ = s • (a • n) := rfl
  let q : (S ⧸ J) →ₐ[S] (T ⧸ J') :=
    Ideal.quotientMapₐ J' (Algebra.ofId S T)
      (fun x hx => Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ hx))
  let g : (S ⧸ J) →ₗ[S] N :=
    { toFun := fun x => LocalizedModule.mk (q x) 1
      map_add' := fun x y => by
        rw [map_add, LocalizedModule.mk_add_mk, one_smul, one_smul, mul_one]
      map_smul' := fun s x => by
        simp only [RingHom.id_apply]
        rw [LocalizedModule.smul'_mk, map_smul] }
  have hm : ∀ m : M, (m : S) ∉ W := fun m hm => Set.disjoint_left.mp hW m.2 hm
  have hden : ∀ (t : T) (b : S) (m' : M), t ∉ W' → t * algebraMap S T m' = algebraMap S T b →
      b ∉ W := by
    intro t b m' ht hb hbW
    have : t * algebraMap S T m' ∈ W' := hb ▸ Ideal.mem_map_of_mem _ hbW
    rcases (inferInstance : W'.IsPrime).mem_or_mem this with h | h
    · exact ht h
    · exact hm m' (hcomap ▸ Ideal.mem_comap.mpr h)
  haveI hg : IsLocalizedModule W.primeCompl g := by
    constructor
    · intro s
      rw [Module.End.isUnit_iff]
      have hu := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap W'.primeCompl (T ⧸ J'))
        (⟨algebraMap S T s, hnot s s.2⟩ : W'.primeCompl)
      rw [Module.End.isUnit_iff] at hu
      convert hu using 1
      funext n
      simp only [Module.algebraMap_end_apply]
      exact (algebraMap_smul T (s : S) n).symm
    · intro n
      induction n using LocalizedModule.induction_on with
      | h y t =>
        obtain ⟨y0, rfl⟩ := Ideal.Quotient.mk_surjective y
        obtain ⟨⟨a, m⟩, hy⟩ := IsLocalization.surj M y0
        obtain ⟨⟨b, m'⟩, ht⟩ := IsLocalization.surj M (t : T)
        simp only at hy ht
        have hb : b ∉ W := hden t b m' t.2 ht
        refine ⟨⟨Ideal.Quotient.mk J (a * m'), ⟨b * m, W.primeCompl.mul_mem hb (hm m)⟩⟩, ?_⟩
        show (b * m) • LocalizedModule.mk (Ideal.Quotient.mk J' y0) t =
          LocalizedModule.mk (Ideal.Quotient.mk J' (algebraMap S T (a * m'))) 1
        rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq, ← algebraMap_smul T (b * m)]
        refine ⟨1, ?_⟩
        rw [one_smul, one_smul, one_smul, Submonoid.smul_def]
        change Ideal.Quotient.mk J' (algebraMap S T (b * m) * y0) =
          Ideal.Quotient.mk J' ((t : T) * algebraMap S T (a * m'))
        congr 1
        simp only [map_mul]
        linear_combination (algebraMap S T b) * hy - (algebraMap S T a) * ht
    · intro x₁ x₂ h
      obtain ⟨x₁, rfl⟩ := Ideal.Quotient.mk_surjective x₁
      obtain ⟨x₂, rfl⟩ := Ideal.Quotient.mk_surjective x₂
      change LocalizedModule.mk (Ideal.Quotient.mk J' (algebraMap S T x₁)) 1 =
        LocalizedModule.mk (Ideal.Quotient.mk J' (algebraMap S T x₂)) 1 at h
      obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp h
      rw [one_smul, one_smul, Submonoid.smul_def, Submonoid.smul_def] at hu
      change Ideal.Quotient.mk J' ((u : T) * algebraMap S T x₁) =
        Ideal.Quotient.mk J' ((u : T) * algebraMap S T x₂) at hu
      rw [Ideal.Quotient.eq] at hu
      obtain ⟨⟨c, m''⟩, hc⟩ := IsLocalization.surj M (u : T)
      simp only at hc
      have hcW : c ∉ W := hden u c m'' u.2 hc
      have hmem : algebraMap S T (c * (x₁ - x₂)) ∈ J' := by
        have := J'.mul_mem_left (algebraMap S T m'') hu
        convert this using 1
        rw [map_mul, map_sub, ← hc]
        ring
      obtain ⟨m3, hm3, hJ⟩ :=
        (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := M) (S := T) J _).mp hmem
      refine ⟨⟨m3 * c, W.primeCompl.mul_mem (hm ⟨m3, hm3⟩) hcW⟩, ?_⟩
      rw [Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq]
      convert hJ using 1
      ring
  let e : LocalizedModule W.primeCompl (S ⧸ J) ≃ₗ[S] N := IsLocalizedModule.iso W.primeCompl g
  rw [(e.extendScalarsOfIsLocalization W.primeCompl (Localization.AtPrime W)).length_eq]
  exact Module.length_eq_of_surjective σ.surjective

end LocalizationLength

section DVR

variable {K : Type*} {ι : K → Type*} {O : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O]

theorem disjoint_nonZeroDivisors {ϖ : O} (hϖ : Irreducible ϖ) (W : Ideal (MRing ι O)) [W.IsPrime]
    (hW : (C ϖ : MRing ι O) ∉ W) :
    Disjoint (((nonZeroDivisors O).map (C (σ := (Σ k, ι k)) (R := O)) : Submonoid (MRing ι O)) :
      Set (MRing ι O)) W := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ haW
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha0 hϖ
  have hpow : (C ϖ : MRing ι O) ^ k ∈ W := by
    rw [← map_pow, ← hu, map_mul]
    exact W.mul_mem_right _ haW
  exact hW (‹W.IsPrime›.mem_of_pow_mem k hpow)

end DVR

end GenericCycleCorresp

attribute [local instance] MvPolynomial.algebraMvPolynomial in

theorem GenericCycleCorresp.proof : GenericCycleCorresp.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P s _ _ _ n
  classical
  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C (σ := (Σ k, ι k)) (R := O))
  have hgen : ∀ W : Ideal (MRing ι O),
      genFib W = W.map (algebraMap (MRing ι O) (MRing ι (FractionRing O))) := fun _ => rfl
  set J := P ⊔ Ideal.span {s}
  set s' := MvPolynomial.map (algebraMap O (FractionRing O)) s
  have hJ : genFib P ⊔ Ideal.span {s'} =
      J.map (algebraMap (MRing ι O) (MRing ι (FractionRing O))) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    rfl
  have hϖM : (C ϖ : MRing ι O) ∈ M := ⟨ϖ, mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero, rfl⟩
  have hcorr : ∀ W : Ideal (MRing ι O), W.IsPrime → (C ϖ : MRing ι O) ∉ W →
      (genFib W).IsPrime ∧
        (genFib W).comap (algebraMap (MRing ι O) (MRing ι (FractionRing O))) = W := by
    intro W hWp hWϖ
    have hd := GenericCycleCorresp.disjoint_nonZeroDivisors hϖ W hWϖ
    exact ⟨IsLocalization.isPrime_of_isPrime_disjoint M _ W hWp hd,
      IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O)) hWp hd⟩
  have hmin : ∀ W : Ideal (MRing ι O), W ∈ J.minimalPrimes → (C ϖ : MRing ι O) ∉ W →
      genFib W ∈ (genFib P ⊔ Ideal.span {s'}).minimalPrimes := by
    intro W hWm hWϖ
    rw [hJ, IsLocalization.minimalPrimes_map M]
    show (genFib W).comap (algebraMap (MRing ι O) (MRing ι (FractionRing O))) ∈ J.minimalPrimes
    rw [(hcorr W hWm.1.1 hWϖ).2]
    exact hWm
  have hkey : ∀ W : Ideal (MRing ι O), W ∈ J.minimalPrimes → (C ϖ : MRing ι O) ∉ W →
      divCycle P s W = divCycle (genFib P) s' (genFib W) := by
    intro W hWm hWϖ
    haveI hWp : W.IsPrime := hWm.1.1
    obtain ⟨hWp', hcomap⟩ := hcorr W hWp hWϖ
    have hrel : IsRelevant (genFib W) ↔ IsRelevant W := by
      refine forall_congr' fun k => exists_congr fun i => not_congr ?_
      have hX : (X ⟨k, i⟩ : MRing ι (FractionRing O)) =
          algebraMap (MRing ι O) (MRing ι (FractionRing O)) (X ⟨k, i⟩) := (MvPolynomial.map_X _ _).symm
      rw [hX, ← Ideal.mem_comap, hcomap]
    have hl : ∀ (h₁ : W.IsPrime) (h₂ : (genFib W).IsPrime),
        @multAt _ _ _ _ J W h₁ = @multAt _ _ _ _ (genFib P ⊔ Ideal.span {s'}) (genFib W) h₂ := by
      intro h₁ h₂
      unfold multAt
      rw [hJ]
      haveI : (W.map (algebraMap (MRing ι O) (MRing ι (FractionRing O)))).IsPrime := h₂
      exact GenericCycleCorresp.length_eq M J W
        (GenericCycleCorresp.disjoint_nonZeroDivisors hϖ W hWϖ)
    unfold divCycle
    by_cases hr : IsRelevant W
    · rw [dif_pos ⟨hWm, hr⟩, dif_pos ⟨hmin W hWm hWϖ, hrel.mpr hr⟩, hl]
    · rw [dif_neg (fun h => hr h.2), dif_neg (fun h => hr (hrel.mp h.2))]
  have hsupp : ∀ (Q : Ideal (MRing ι (FractionRing O))) (x) (W : Ideal (MRing ι (FractionRing O))),
      divCycle Q x W ≠ 0 → W ∈ (Q ⊔ Ideal.span {x}).minimalPrimes := by
    intro Q x W h
    unfold divCycle at h
    split_ifs at h with hh
    · exact hh.1
    · exact absurd rfl h
  have hsupp0 : ∀ W : Ideal (MRing ι O), divCycle P s W ≠ 0 → W ∈ J.minimalPrimes := by
    intro W h
    unfold divCycle at h
    split_ifs at h with hh
    · exact hh.1
    · exact absurd rfl h
  unfold cycEval
  let A : Set (Ideal (MRing ι O)) := {W | W ∈ J.minimalPrimes ∧ (C ϖ : MRing ι O) ∉ W}
  let B : Set (Ideal (MRing ι (FractionRing O))) := (genFib P ⊔ Ideal.span {s'}).minimalPrimes
  have hA : (∑ᶠ W, divCycle P s W * (if (C ϖ : MRing ι O) ∈ W then 0 else n (genFib W))) =
      ∑ᶠ W ∈ A, divCycle P s W * (if (C ϖ : MRing ι O) ∈ W then 0 else n (genFib W)) := by
    rw [finsum_mem_def]
    congr 1
    funext W
    symm
    rw [Set.indicator_apply_eq_self]
    intro hW
    by_cases hϖW : (C ϖ : MRing ι O) ∈ W
    · rw [if_pos hϖW, mul_zero]
    · have : divCycle P s W = 0 := by
        by_contra h
        exact hW ⟨hsupp0 W h, hϖW⟩
      rw [this, zero_mul]
  have hB : (∑ᶠ W, divCycle (genFib P) s' W * n W) = ∑ᶠ W ∈ B, divCycle (genFib P) s' W * n W := by
    rw [finsum_mem_def]
    congr 1
    funext W
    symm
    rw [Set.indicator_apply_eq_self]
    intro hW
    have : divCycle (genFib P) s' W = 0 := by
      by_contra h
      exact hW (hsupp _ _ W h)
    rw [this, zero_mul]
  rw [hA, hB]
  refine finsum_mem_eq_of_bijOn genFib ⟨?_, ?_, ?_⟩ ?_
  · intro W hW
    exact hmin W hW.1 hW.2
  · intro W₁ hW₁ W₂ hW₂ h
    rw [← (hcorr W₁ hW₁.1.1.1 hW₁.2).2, ← (hcorr W₂ hW₂.1.1.1 hW₂.2).2]
    exact congrArg _ h
  · intro W' hW'
    have hW'p : W'.IsPrime := hW'.1.1
    have hW'm := hW'
    change W' ∈ (genFib P ⊔ Ideal.span {s'}).minimalPrimes at hW'm
    rw [hJ, IsLocalization.minimalPrimes_map M] at hW'm
    refine ⟨W'.comap (algebraMap (MRing ι O) (MRing ι (FractionRing O))), ⟨hW'm, ?_⟩, ?_⟩
    · intro h
      rw [Ideal.mem_comap] at h
      exact hW'p.ne_top (Ideal.eq_top_of_isUnit_mem _ h
        (IsLocalization.map_units (MRing ι (FractionRing O)) (⟨_, hϖM⟩ : M)))
    · exact IsLocalization.map_under M (MRing ι (FractionRing O)) W'
  · intro W hW
    rw [if_neg hW.2, hkey W hW.1 hW.2]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
