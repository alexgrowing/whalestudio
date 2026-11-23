import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulTopIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatioHolds
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SumOrbitsEquivariant
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

def extHom (S : VecSplit h h') : (V' ≃ₗ[K] V') →* (V ≃ₗ[K] V) where
  toFun := SplitBAux.extOf S
  map_one' := by
    ext v
    obtain ⟨c, a, rfl⟩ := S.cover v
    rw [SplitBAux.extOf_apply]
    rfl
  map_mul' := by
    intro a b
    ext v
    obtain ⟨c, x, rfl⟩ := S.cover v
    rw [SplitBAux.extOf_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, SplitBAux.extOf_apply,
      SplitBAux.extOf_apply]

theorem extHom_apply (S : VecSplit h h') (g' : V' ≃ₗ[K] V') : extHom S g' = SplitBAux.extOf S g' := rfl

theorem extHom_injective (S : VecSplit h h') : Function.Injective (extHom S) := by
  intro a b e
  ext x
  apply S.inj
  rw [← SplitBAux.extOf_ι, ← SplitBAux.extOf_ι S b, ← extHom_apply, e, extHom_apply]

def autExt (S : VecSplit h h') (M : Submodule (𝓞 K) V) : Subgroup (V' ≃ₗ[K] V') :=
  (autSub h M).comap (extHom S)

def oM (S : VecSplit h h') (M : Submodule (𝓞 K) V) : ℕ :=
  (autExt S M).relIndex (autSub h' (S.cut M))

def nu {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (h₀ : W →ₗ⋆[K] W →ₗ[K] K) (A : Submodule (𝓞 K) W) (𝔭 : Ideal (𝓞 F)) : ℝ :=
  alphaL h₀ A 𝔭 / (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K W * vd h₀ A 𝔭)

def kap (S : VecSplit h h') (M : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F) (J k : ℕ) : ℝ :=
  (cnt h M 𝔭 k n (tube (autSub h M) M 𝔭 J S.x₀) : ℝ) /
    ((Ideal.absNorm 𝔭 : ℝ) ^ vd h M 𝔭 * nu h M 𝔭) * (nu h' (S.cut M) 𝔭 / (oM S M : ℝ))

theorem nu_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : 0 < nu h (locF 𝔭 A₀) 𝔭 := by
  have e : alphaL h (locF 𝔭 A₀) 𝔭 = alphaL h A₀ 𝔭 := by
    unfold alphaL
    congr 1
    ext k
    rw [akCount_locF hF h A₀ 𝔭 h𝔭]
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  unfold nu
  rw [e]
  exact div_pos (alphaL_pos hK hF hs hd hA₀ hA₀i h𝔭) (pow_pos hq _)

theorem nu_mul_relIndex (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀)
    (hB₀ : Submodule.IsLattice K B₀) (hB₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h B₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    nu h (locF 𝔭 A₀) 𝔭 * ((autSub h (locF 𝔭 A₀)).relIndex (autSub h (locF 𝔭 B₀)) : ℝ) =
      nu h (locF 𝔭 B₀) 𝔭 * ((autSub h (locF 𝔭 B₀)).relIndex (autSub h (locF 𝔭 A₀)) : ℝ) := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  have h1 := local_density_ratio_holds K F hK hF V h A₀ B₀ 𝔭 hs hd h𝔭 hA₀ hB₀ hA₀i hB₀i
  rw [orbCount_eq_relIndex, orbCount_eq_relIndex] at h1
  unfold nu
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff (pow_pos hq _).ne' (pow_pos hq _).ne']
  linear_combination h1

theorem autExt_le (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    autExt S M ≤ autSub h' (S.cut M) := by
  intro g' hg
  obtain ⟨h1, h2⟩ : SplitBAux.extOf S g' ∈ Formalism.HermitianLatticesTheory.isom h ∧
    Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M = M := hg
  refine ⟨fun a b => ?_, ?_⟩
  · rw [← S.isom, ← S.isom, ← SplitBAux.extOf_ι, ← SplitBAux.extOf_ι, h1]
  · rw [← StabilizerLattices.cut_gmap_extOf, h2]

theorem inf_fixS_eq_map (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    autSub h M ⊓ fixS S.x₀ = (autExt S M).map (extHom S) := by
  ext g
  constructor
  · rintro ⟨hg, hx⟩
    have hx' : g S.x₀ = S.x₀ := hx
    have e : extHom S (SplitBAux.res S g hg.1 hx') = g := by
      ext v
      obtain ⟨c, a, rfl⟩ := S.cover v
      rw [extHom_apply, SplitBAux.extOf_apply, SplitBAux.res_spec, map_add, map_smul, hx']
    refine ⟨SplitBAux.res S g hg.1 hx', ?_, e⟩
    change extHom S _ ∈ autSub h M
    rw [e]
    exact hg
  · rintro ⟨g', hg', rfl⟩
    exact ⟨hg', SplitBAux.extOf_x₀ S g'⟩

theorem relIndex_fix_eq (hs : h.IsSymm) (S : VecSplit h h') (M₁ M₂ : Submodule (𝓞 K) V) :
    (autSub h M₂ ⊓ fixS S.x₀).relIndex (autSub h M₁ ⊓ fixS S.x₀) =
      (autExt S M₂).relIndex (autExt S M₁) := by
  rw [inf_fixS_eq_map, inf_fixS_eq_map, Subgroup.relIndex_map_map_of_injective _ _ (extHom_injective S)]

theorem oM_ne_zero (hs : h.IsSymm) (S : VecSplit h h') {M₁ : Submodule (𝓞 K) V}
    (hM₁ : Submodule.IsLattice K M₁) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hx : S.x₀ ∈ locF 𝔭 M₁) : oM S (locF 𝔭 M₁) ≠ 0 := by
  have hN : Submodule.IsLattice K (S.adjoin (S.cut M₁)) :=
    (S.isLattice_adjoin_iff' _).mpr (StabilizerLattices.isLattice_cut S hM₁)
  have h1 : (autExt S (locF 𝔭 M₁)).relIndex (autExt S (locF 𝔭 (S.adjoin (S.cut M₁)))) ≠ 0 :=
    Subgroup.relIndex_comap_ne_zero (extHom S) (relIndex_autSub_ne_zero h hN hM₁ h𝔭)
  have h2 : autSub h' (S.cut (locF 𝔭 M₁)) ≤ autExt S (locF 𝔭 (S.adjoin (S.cut M₁))) := by
    rintro g' ⟨hg1, hg2⟩
    refine ⟨SplitBAux.extOf_mem_isom hs S hg1, ?_⟩
    change Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') _ = _
    rw [LocalizedFibreSets.cut_locF, LocalizedFibreSets.gmap_locF] at hg2
    rw [LocalizedFibreSets.gmap_locF, SplitBAux.gmap_extOf S g' rfl]
    have mono : ∀ T T' : Submodule (𝓞 K) V', locF 𝔭 T = locF 𝔭 T' →
        locF 𝔭 (S.adjoin T) ≤ locF 𝔭 (S.adjoin T') := by
      intro T T' e
      rw [← LocalizedFibreSets.locF_idem 𝔭 (S.adjoin T')]
      apply LocF.locF_mono
      unfold VecSplit.adjoin
      refine sup_le ((le_sup_left).trans (LocalizedFibreSets.le_locF 𝔭 _)) ?_
      rw [Submodule.map_le_iff_le_comap]
      intro a ha
      have ha' : a ∈ locF 𝔭 T' := e ▸ LocalizedFibreSets.le_locF 𝔭 T ha
      obtain ⟨s, hs, hsa⟩ := ha'
      refine ⟨s, hs, ?_⟩
      apply Submodule.mem_sup_right
      refine Submodule.mem_map.mpr ⟨s • a, hsa, ?_⟩
      exact LinearMap.map_smul_of_tower _ _ _
    exact le_antisymm (mono _ _ hg2) (mono _ _ hg2.symm)
  intro h0
  exact h1 (Subgroup.relIndex_eq_zero_of_le_right h2 h0)

theorem kap_alg {E₁ E₂ Q₁ Q₂ ν₁ ν₂ μ₁ μ₂ a b c d a' b' o₁ o₂ : ℝ} (hQ₁ : Q₁ ≠ 0) (hQ₂ : Q₂ ≠ 0)
    (hν₁ : ν₁ ≠ 0) (hν₂ : ν₂ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (ha' : a' ≠ 0)
    (ho₁ : o₁ ≠ 0) (ho₂ : o₂ ≠ 0) (h1 : E₁ * Q₂ * b * a' = E₂ * Q₁ * a * b')
    (h2 : ν₁ * b = ν₂ * a) (h3 : μ₁ * d = μ₂ * c) (h4 : a' * o₁ * d = c * o₂ * b') :
    E₁ / (Q₁ * ν₁) * (μ₁ / o₁) = E₂ / (Q₂ * ν₂) * (μ₂ / o₂) := by
  rw [div_mul_div_comm, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hQ₁ hν₁) ho₁) (mul_ne_zero (mul_ne_zero hQ₂ hν₂) ho₂)]
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero hb ha') ha) hd)
  linear_combination (μ₁ * d * ν₂ * a * o₂) * h1 + (E₂ * Q₁ * a * b' * ν₂ * a * o₂) * h3 -
    (E₂ * Q₁ * a * b' * μ₂ * c * o₂) * h2 - (E₂ * μ₂ * Q₁ * ν₁ * b * a) * h4

theorem kap_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h')
    {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₁i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₁) (hM₂ : Submodule.IsLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F}
    (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F)) (hx₁ : S.x₀ ∈ locF 𝔭 M₁)
    (hx₂ : S.x₀ ∈ locF 𝔭 M₂) :
    ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      kap S (locF 𝔭 M₁) 𝔭 n J k = kap S (locF 𝔭 M₂) 𝔭 n J k := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  have hT₁ := StabilizerLattices.isLattice_cut S hM₁
  have hT₂ := StabilizerLattices.isLattice_cut S hM₂
  have hT₁i := UnimodularLocalization.isIntegralLat_cut S hM₁i
  have hT₂i := UnimodularLocalization.isIntegralLat_cut S hM₂i

  set P := autExt S (locF 𝔭 M₁) with hP
  set W := autExt S (locF 𝔭 M₂) with hW
  set Q := autSub h' (S.cut (locF 𝔭 M₁)) with hQ
  set R := autSub h' (S.cut (locF 𝔭 M₂)) with hR
  have hPQ : P ≤ Q := autExt_le S _
  have hWR : W ≤ R := autExt_le S _
  have ho₁ : P.relIndex Q ≠ 0 := oM_ne_zero hs S hM₁ h𝔭 hx₁
  have ho₂ : W.relIndex R ≠ 0 := oM_ne_zero hs S hM₂ h𝔭 hx₂
  have hc : R.relIndex Q ≠ 0 := by
    rw [hR, hQ, LocalizedFibreSets.cut_locF, LocalizedFibreSets.cut_locF]
    exact relIndex_autSub_ne_zero h' hT₁ hT₂ h𝔭
  have hd' : Q.relIndex R ≠ 0 := by
    rw [hR, hQ, LocalizedFibreSets.cut_locF, LocalizedFibreSets.cut_locF]
    exact relIndex_autSub_ne_zero h' hT₂ hT₁ h𝔭
  have hu : W.relIndex Q ≠ 0 := Subgroup.relIndex_ne_zero_trans ho₂ hc
  have ht : Q.relIndex W ≠ 0 := fun h0 => hd' (Subgroup.relIndex_eq_zero_of_le_right hWR h0)
  have ha' : W.relIndex P ≠ 0 := fun h0 => hu (Subgroup.relIndex_eq_zero_of_le_right hPQ h0)
  have c1 := relIndex_cocycle P Q W ha' ho₁ ht
  have c2 := relIndex_cocycle Q R W hu hd' (by rw [Subgroup.relIndex_eq_one.mpr hWR]; exact one_ne_zero)
  rw [Subgroup.relIndex_eq_one.mpr hPQ, one_mul] at c1
  rw [Subgroup.relIndex_eq_one.mpr hWR, mul_one] at c2
  have h4 : W.relIndex P * P.relIndex Q * Q.relIndex R = R.relIndex Q * W.relIndex R * P.relIndex W := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ht)
    calc Q.relIndex W * (W.relIndex P * P.relIndex Q * Q.relIndex R)
        = (P.relIndex Q * Q.relIndex W * W.relIndex P) * Q.relIndex R := by ring
      _ = (Q.relIndex R * W.relIndex Q) * P.relIndex W := by rw [← c1]; ring
      _ = _ := by rw [← c2]; ring
  have h2 := nu_mul_relIndex hK hF hs hd hM₁ hM₁i hM₂ hM₂i h𝔭
  have h3 := nu_mul_relIndex hK hF (S.isSymm hs) (S.isTotPosDef hd) hT₁ hT₁i hT₂ hT₂i h𝔭
  rw [← LocalizedFibreSets.cut_locF, ← LocalizedFibreSets.cut_locF, ← hQ, ← hR] at h3
  filter_upwards [pair hK hF hs hd hM₁ hM₁i hM₂ hM₂i h𝔭 hn hx hx₁ hx₂] with J hJ
  filter_upwards [hJ] with k hk
  rw [relIndex_fix_eq hs, relIndex_fix_eq hs, ← hP, ← hW] at hk
  unfold kap oM
  rw [← hP, ← hW, ← hQ, ← hR]
  refine kap_alg (pow_pos hq _).ne' (pow_pos hq _).ne'
    (nu_pos hK hF hs hd hM₁ hM₁i h𝔭).ne' (nu_pos hK hF hs hd hM₂ hM₂i h𝔭).ne'
    (a := ((autSub h (locF 𝔭 M₂)).relIndex (autSub h (locF 𝔭 M₁)) : ℝ))
    (b := ((autSub h (locF 𝔭 M₁)).relIndex (autSub h (locF 𝔭 M₂)) : ℝ))
    (c := (R.relIndex Q : ℝ)) (d := (Q.relIndex R : ℝ)) (a' := (W.relIndex P : ℝ))
    (b' := (P.relIndex W : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ h2 h3 ?_
  · exact_mod_cast relIndex_autSub_ne_zero h hM₁ hM₂ h𝔭
  · exact_mod_cast relIndex_autSub_ne_zero h hM₂ hM₁ h𝔭
  · exact_mod_cast hd'
  · exact_mod_cast ha'
  · exact_mod_cast ho₁
  · exact_mod_cast ho₂
  · exact_mod_cast hk
  · exact_mod_cast h4

end Formalism.HermitianLattices.Ext.L3.LIOrb
