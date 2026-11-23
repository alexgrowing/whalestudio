import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecChartIso
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

set_option linter.unusedSectionVars false

namespace SpecChart

variable {K : Type} [Field K] [NumberField K] {n e : ℕ} {I : Ideal (MvPolynomial (Fin n) K)} {j : Fin n}
  {v : HeightOneSpectrum (𝓞 K)} {W : Ideal (MvPolynomial (Fin n) (𝓞 K))}

theorem Q_le_comap {𝔫 : Ideal (SecB e I v)} [𝔫.IsPrime] (hj : toSecB e I v (X j) ∉ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) :
    Q e I j W ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫)).comap (Φ hj) := by
  rw [Q_eq, Ideal.map_le_iff_le_comap, Ideal.comap_comap, Wb, Ideal.map_le_iff_le_comap,
    Ideal.comap_comap, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro w hw
  rw [Ideal.mem_comap]
  change Φ hj (C (toBase I j w)) ∈ _
  rw [Φ_C, baseToBn_toBase, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔫) 𝔫, ← h𝔫]
  exact Ideal.mem_map_of_mem _ hw

theorem σ_not_mem {𝔫 : Ideal (SecB e I v)} [𝔫.IsPrime] (hj : toSecB e I v (X j) ∉ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) (s : MvPolynomial (Par e n) (𝓞 K))
    (hs : s ∈ (parPrime e n v).primeCompl) : σ e I j s ∉ Q e I j W := by
  intro hQ
  have h1 := Q_le_comap hj h𝔫 hQ
  rw [Ideal.mem_comap, ← RingHom.comp_apply, Φ_σ] at h1
  simp only [RingHom.comp_apply] at h1
  have hu : IsUnit (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) s) :=
    IsLocalization.map_units (ParDVR e n v) (⟨s, hs⟩ : (parPrime e n v).primeCompl)
  exact IsLocalRing.notMem_maximalIdeal.mpr ((hu.map _).map _) h1

section Back

variable [(Q e I j W).IsPrime]

def ρ (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    ParDVR e n v →+* Localization.AtPrime (Q e I j W) :=
  IsLocalization.lift (M := (parPrime e n v).primeCompl)
    (g := (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp (σ e I j)) fun s => by
      rw [RingHom.comp_apply, ← IsLocalRing.notMem_maximalIdeal,
        IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)]
      exact hσ s s.2

theorem ρ_algebraMap (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (s : MvPolynomial (Par e n) (𝓞 K)) :
    ρ hσ (algebraMap _ (ParDVR e n v) s) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (σ e I j s) :=
  IsLocalization.lift_eq _ _

theorem ρ_parY (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) (p : Par e n) :
    ρ hσ (parY e n v p) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (val e I j p) := by
  rw [parY, ρ_algebraMap, σ_X]

def G' (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    MvPolynomial (Fin n) (ParDVR e n v) →+* Localization.AtPrime (Q e I j W) :=
  eval₂Hom (ρ hσ) fun l => algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (cx e I j l)

theorem G'_map (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (g : MvPolynomial (Fin n) (𝓞 K)) :
    G' hσ (g.map (algebraMap (𝓞 K) (ParDVR e n v))) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g)) := by
  have h : (G' hσ).comp (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v))) =
      (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp (C.comp (toBase I j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, map_C, G', eval₂Hom_C]
      rw [IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v),
        ρ_algebraMap, MvPolynomial.algebraMap_eq, σ_C]
    · intro l
      simp only [RingHom.comp_apply, map_X, G', eval₂Hom_X', cx]
  exact RingHom.congr_fun h g

theorem G'_kills (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    secIdeal (modelR e I v) (parY e n v) ≤ RingHom.ker (G' hσ) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [modelR, Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, G'_map, toBase, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero, map_zero, map_zero]
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    rw [SetLike.mem_coe, RingHom.mem_ker, secForm, linForm, map_sum]
    simp only [map_mul, G', eval₂Hom_C, eval₂Hom_X', ρ_parY]
    have h := congrArg (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))) (sum_val_inl e I j i)
    simpa only [map_sum, map_mul, map_zero] using h
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    rw [SetLike.mem_coe, RingHom.mem_ker, chartForm, linForm, map_sub, map_sum, map_one]
    simp only [map_mul, G', eval₂Hom_C, eval₂Hom_X', ρ_parY]
    have h := congrArg (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))) (sum_val_inr e I j)
    simpa only [map_sum, map_mul, map_sub, map_one, map_zero] using h

def G (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    SecB e I v →+* Localization.AtPrime (Q e I j W) :=
  Ideal.Quotient.lift _ (G' hσ) fun _ ha => RingHom.mem_ker.mp (G'_kills hσ ha)

theorem G_toSecB (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (g : MvPolynomial (Fin n) (𝓞 K)) : G hσ (toSecB e I v g) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g)) := by
  rw [toSecB, RingHom.comp_apply, G, Ideal.Quotient.lift_mk, G'_map]

theorem G_algebraMap (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (r : ParDVR e n v) : G hσ (algebraMap _ (SecB e I v) r) = ρ hσ r := by
  rw [← Ideal.Quotient.mk_algebraMap, G, Ideal.Quotient.lift_mk, MvPolynomial.algebraMap_eq, G', eval₂Hom_C]

theorem G_mem (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    {𝔫 : Ideal (SecB e I v)} (h𝔫 : W.map (toSecB e I v) = 𝔫) {b : SecB e I v} (hb : b ∈ 𝔫) :
    G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) := by
  rw [← h𝔫] at hb
  have h : W.map (toSecB e I v) ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))).comap (G hσ) := by
    rw [Ideal.map_le_iff_le_comap]
    intro w hw
    rw [Ideal.mem_comap, Ideal.mem_comap, G_toSecB, IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)]
    exact C_toBase_mem_Q e j hw
  exact h hb

theorem mem_of_toSecB_mem [W.IsPrime] (hPW : integralModel I ≤ W) (hXj : X j ∉ W)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    {𝔫 : Ideal (SecB e I v)} (h𝔫 : W.map (toSecB e I v) = 𝔫) {g : MvPolynomial (Fin n) (𝓞 K)}
    (hg : toSecB e I v g ∈ 𝔫) : g ∈ W := by
  have h := G_mem hσ h𝔫 hg
  rw [G_toSecB, IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)] at h
  exact mem_of_C_toBase_mem_Q e j hPW hXj h

theorem mem_of_G_mem (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    {𝔫 : Ideal (SecB e I v)} [𝔫.IsMaximal] (h𝔫 : W.map (toSecB e I v) = 𝔫) {b : SecB e I v}
    (hb : G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))) : b ∈ 𝔫 := by
  have h : 𝔫 = (IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))).comap (G hσ) :=
    Ideal.IsMaximal.eq_of_le ‹_› (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
      (fun _ hb => G_mem hσ h𝔫 hb)
  rw [h]
  exact hb

variable {𝔫 : Ideal (SecB e I v)} [𝔫.IsPrime]

def Gloc (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫) :
    Localization.AtPrime 𝔫 →+* Localization.AtPrime (Q e I j W) :=
  IsLocalization.lift (M := 𝔫.primeCompl) (g := G hσ) fun b =>
    IsLocalRing.notMem_maximalIdeal.mp fun h => b.2 (hG _ h)

theorem Gloc_algebraMap (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (b : SecB e I v) : Gloc hσ hG (algebraMap _ _ b) = G hσ b :=
  IsLocalization.lift_eq _ _

theorem Gloc_max (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) {x : Localization.AtPrime 𝔫}
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫)) :
    Gloc hσ hG x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal] at hx
  have h : 𝔫.map (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)) ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))).comap (Gloc hσ hG) := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, Ideal.mem_comap, Gloc_algebraMap]
    exact G_mem hσ h𝔫 hb
  exact h hx

theorem Gloc_Φ (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫) :
    (Gloc hσ hG).comp (Φ hj) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, Φ_C]
    have h : (Gloc hσ hG).comp (baseToBn hj) =
        (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp C := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (integralModel I) (X j)))
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun g => ?_
      change Gloc hσ hG (baseToBn hj (toBase I j g)) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g))
      rw [baseToBn_toBase, Gloc_algebraMap, G_toSecB]
    exact RingHom.congr_fun h b
  · intro y
    simp only [RingHom.comp_apply, Φ_X, parB, Gloc_algebraMap, G_algebraMap, ρ_parY, val_free]

theorem Φ_isUnit (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) (c : Poly e I j) (hc : c ∈ (Q e I j W).primeCompl) :
    IsUnit (Φ hj c) := by
  by_contra hu
  rw [← IsLocalRing.notMem_maximalIdeal, not_not] at hu
  have h2 := Gloc_max hσ hG h𝔫 hu
  rw [← RingHom.comp_apply, Gloc_Φ, IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)] at h2
  exact hc h2

def Φloc (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : Localization.AtPrime (Q e I j W) →+* Localization.AtPrime 𝔫 :=
  IsLocalization.lift (M := (Q e I j W).primeCompl) (g := Φ hj) fun c => Φ_isUnit hj hσ hG h𝔫 c c.2

theorem Φloc_algebraMap (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) (c : Poly e I j) :
    Φloc hj hσ hG h𝔫 (algebraMap _ _ c) = Φ hj c :=
  IsLocalization.lift_eq _ _

theorem Gloc_Φloc (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : (Gloc hσ hG).comp (Φloc hj hσ hG h𝔫) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Q e I j W).primeCompl
  refine RingHom.ext fun c => ?_
  simp only [RingHom.comp_apply, Φloc_algebraMap, RingHom.id_apply]
  rw [← RingHom.comp_apply, Gloc_Φ]

theorem Φloc_Gloc (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : (Φloc hj hσ hG h𝔫).comp (Gloc hσ hG) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext 𝔫.primeCompl
  have hρ : (Φloc hj hσ hG h𝔫).comp (ρ hσ) =
      (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)).comp (algebraMap (ParDVR e n v) (SecB e I v)) := by
    apply IsLocalization.ringHom_ext (parPrime e n v).primeCompl
    refine RingHom.ext fun s => ?_
    simp only [RingHom.comp_apply, ρ_algebraMap, Φloc_algebraMap]
    rw [← RingHom.comp_apply (Φ hj), Φ_σ]
    rfl
  have h : (Φloc hj hσ hG h𝔫).comp (G hσ) = algebraMap (SecB e I v) (Localization.AtPrime 𝔫) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      have := RingHom.congr_fun hρ r
      simp only [RingHom.comp_apply] at this ⊢
      rw [G, Ideal.Quotient.lift_mk, G', eval₂Hom_C, this, ← Ideal.Quotient.mk_algebraMap,
        MvPolynomial.algebraMap_eq]
    · intro l
      simp only [RingHom.comp_apply]
      rw [G, Ideal.Quotient.lift_mk, G', eval₂Hom_X', Φloc_algebraMap, Φ_cx]
      simp [toSecB]
  refine RingHom.ext fun b => ?_
  simp only [RingHom.comp_apply, Gloc_algebraMap, RingHom.id_apply]
  exact RingHom.congr_fun h b

theorem quotToBn_flat (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : RingHom.Flat (R := MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (S := Localization.AtPrime 𝔫) (quotToBn e 𝔫) := by
  have h : quotToBn e 𝔫 = (Φloc hj hσ hG h𝔫).comp
      ((algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp
        ((C : Base I j →+* Poly e I j).comp
          (algebraMap (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (Base I j)))) := by
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun g => ?_
    change quotToBn e 𝔫 (Ideal.Quotient.mk _ g) =
      Φloc hj hσ hG h𝔫 (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g)))
    rw [quotToBn_mk, Φloc_algebraMap, Φ_C, baseToBn_toBase]
  have hbij : Function.Bijective (Φloc hj hσ hG h𝔫) :=
    Function.bijective_iff_has_inverse.mpr ⟨Gloc hσ hG,
      fun x => RingHom.congr_fun (Gloc_Φloc hj hσ hG h𝔫) x,
      fun y => RingHom.congr_fun (Φloc_Gloc hj hσ hG h𝔫) y⟩
  have h1 : (algebraMap (MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (Base I j)).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (Base I j) (Submonoid.powers (Ideal.Quotient.mk (integralModel I) (X j))))
  have h2 : (C : Base I j →+* Poly e I j).Flat := by
    rw [← MvPolynomial.algebraMap_eq]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have h3 : RingHom.Flat (R := Poly e I j) (S := Localization.AtPrime (Q e I j W))
      (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))) :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization.AtPrime (Q e I j W)) (Q e I j W).primeCompl)
  rw [h]
  exact RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.comp h1 h2) h3) (RingHom.Flat.of_bijective hbij)

end Back

theorem contraction_and_flat [W.IsPrime] (𝔫 : Ideal (SecB e I v)) [𝔫.IsMaximal]
    (hPW : integralModel I ≤ W) (h𝔫 : W.map (toSecB e I v) = 𝔫) :
    (∀ g, toSecB e I v g ∈ 𝔫 → g ∈ W) ∧ RingHom.Flat (R := MvPolynomial (Fin n) (𝓞 K) ⧸ integralModel I) (S := Localization.AtPrime 𝔫) (quotToBn e 𝔫) := by
  obtain ⟨j, hj⟩ := exists_secCoord_not_mem e I v 𝔫 (Ideal.IsMaximal.ne_top ‹_›)
  have hXj : X j ∉ W := fun h => hj (h𝔫 ▸ Ideal.mem_map_of_mem _ h)
  have := Q_isPrime e j hPW hXj
  have hσ := σ_not_mem hj h𝔫
  have hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫 :=
    fun b hb => mem_of_G_mem hσ h𝔫 hb
  exact ⟨fun g hg => mem_of_toSecB_mem hPW hXj hσ h𝔫 hg, quotToBn_flat hj hσ hG h𝔫⟩

end SpecChart

end

end GroundTheory.Heights₂.Heights.Vertical
