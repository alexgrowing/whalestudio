import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueTiedOfIsToricElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLNeZeroNat

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.HeckeGal GlobalTheory.ToricDenom GlobalTheory.ToricDistribution
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (lamF upIdele)

namespace GlobalTheory.ToricRational

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

section Core

def IsUnitOver {E : Type} [Field E] [NumberField E] (l : ℕ) (y : (Af E)ˣ) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), Valued.v ((y : Af E) P) = 1 ∧ ((l : 𝓞 E) ∉ P.asIdeal → (y : Af E) P = 1)

theorem isUnitOver_up {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] {l : ℕ}
    {v : HeightOneSpectrum (𝓞 K)} (hv : (l : 𝓞 K) ∈ v.asIdeal) {x : (v.adicCompletion K)ˣ} (hx : Formalism.L2.Host.IsUnitAt v x) :
    IsUnitOver l (upIdele K E (single v x)) := by
  have key : ∀ x : (v.adicCompletion K)ˣ, Formalism.L2.Host.IsUnitAt v x → ∀ P : HeightOneSpectrum (𝓞 E),
      Valued.v ((upIdele K E (single v x) : Af E) P) ≤ 1 := fun x hx P => by
    refine GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_mapsTo K E P (x := (single v x : Af K) (P.under (𝓞 K))) ?_
    show Valued.v ((single v x : Af K) (P.under (𝓞 K))) ≤ 1
    by_cases h : P.under (𝓞 K) = v
    · subst h
      rw [single_self]
      exact le_of_eq hx
    · rw [suppAt_single v x _ h, map_one]
  refine fun P => ⟨le_antisymm (key x hx P) ?_, fun hP => ?_⟩
  · have h1 := key x⁻¹ (by
      show Valued.v _ = 1
      rw [Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (x : v.adicCompletion K) = 1 from hx, inv_one]) P
    rw [map_inv, map_inv, ← coe_coord, Fibre.coord_inv', Units.val_inv_eq_inv_val, map_inv₀,
      inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (Units.ne_zero _)))] at h1
    exact h1
  · show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K E P ((single v x : Af K) (P.under (𝓞 K))) = 1
    rw [suppAt_single v x _ fun h => hP ?_, map_one]
    subst h
    rw [← map_natCast (algebraMap (𝓞 K) (𝓞 E))]
    exact hv

theorem finPart_of_isUnitOver {E : Type} [Field E] [NumberField E] {l : ℕ} {ξ : HChar E}
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → ξ.UnrAt P) {y : (Af E)ˣ} (hy : IsUnitOver l y) :
    finPart ξ y = 1 := by
  refine (Fibre.hasProd_loc ξ y).unique ?_
  have e : (fun P => ξ.loc P (coord P y)) = fun _ => 1 := funext fun P => by
    by_cases hP : (l : 𝓞 E) ∈ P.asIdeal
    · exact h P hP _ (hy P).1
    · rw [show coord P y = 1 from Units.ext ((hy P).2 hP), map_one]
  rw [e]
  exact hasProd_one

variable {R : Ranks} {H : Host R} {I : Type} [Fintype I] {φ : I → H.E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF H.E)} {χ : HChar H.E}

theorem condQ_ne_bot {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h : 𝔣 ≠ ⊥) (Q : Finset (HeightOneSpectrum (OF E))) :
    condQ 𝔣 Q ≠ ⊥ := mul_ne_zero h (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)

theorem partialSum_mem (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hG : RatioConj) (hU : UnramFin H.E) (hD : IsHostDatum H φ s κ 𝔣 χ)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hk : IsAlgClosed (IsLocalRing.ResidueField O)) {l : ℕ} (hl : l ≠ 0) (hO : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (ι : ℂ →+* AlgebraicClosure (FractionRing O))
    (hE : ∀ (σ : H.E →+* ℂ) (x : H.E), ι (σ x) ∈ (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O))).range)
    (S : Finset (HeightOneSpectrum (𝓞 H.E)))
    (hS : ∀ P ∉ S, ι (χ.val P : ℂ) ∈ (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O))).range)
    {T₀ : ℂ} (hT₀ : IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀) (h0 : T₀ ≠ 0)
    {Q : Finset (HeightOneSpectrum (OF H.E))} (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) [Finite (PicO (condQ 𝔣 Q))]
    {T : PicO (condQ 𝔣 Q) → ℂ} (hT : ∀ q, IsClassTerm φ s κ (condQ 𝔣 Q) χ q.out (T q))
    {Δ : Type} [CommGroup Δ] [Fintype Δ] (π : PicO (condQ 𝔣 Q) →* Δ)
    (hπ : ∀ y, IsUnitOver l y → π (QuotientGroup.mk y) = 1) (δ : Δ) :
    (ι T₀)⁻¹ * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q) ∈ (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O))).range := by
  classical
  have : IsCMField H.E := H.isCMField_hostE
  have : CharZero (AlgebraicClosure (FractionRing O)) := ι.charZero_iff ι.injective |>.1 inferInstance
  have : CharZero (FractionRing O) := RingHom.charZero (algebraMap _ (AlgebraicClosure (FractionRing O)))
  have : CharZero O := RingHom.charZero (algebraMap _ (FractionRing O))
  obtain ⟨τ₀, -⟩ := hD.1 H.φ₀
  let Ω := AlgebraicClosure H.K
  let _ : Algebra H.K ℂ := ((φ τ₀).comp (algebraMap H.K H.E)).toAlgebra
  let j : Ω →ₐ[H.K] ℂ := IsAlgClosed.lift
  have hj : ∀ x : H.K, j.toRingHom (algebraMap H.K Ω x) = φ τ₀ x := j.commutes
  obtain ⟨art, ha⟩ := hA H.K Ω
  obtain ⟨ρ, hρ, hg⟩ := hG R H I φ s κ 𝔣 χ hD Ω j.toRingHom τ₀ hj art ha T₀ hT₀ h0 Q hQ inferInstance T hT
  generalize j.toRingHom = j at hj hρ hg
  have := Fintype.ofFinite (PicO (condQ 𝔣 Q))
  obtain ⟨z, hz, hfix⟩ := exists_fixed j (fun δ => (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q) / T₀) (fun r => ρ (r.comp π)) (fun r => by
    rw [hρ, finsum_eq_sum_of_fintype, ← Finset.sum_fiberwise Finset.univ (fun q => π q⁻¹), Finset.sum_div]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [show {q | π q⁻¹ = δ} = ↑(Finset.univ.filter fun q => π q⁻¹ = δ) by ext; simp, finsum_mem_coe_finset,
      ← mul_div_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← (Finset.mem_filter.1 hq).2, map_inv, map_inv, Units.val_inv_eq_inv_val, map_inv₀, MonoidHom.comp_apply]) δ
  obtain ⟨v, A, hv, hA', hτ⟩ := exists_inertia (K := H.K) hk hl hO (ι.comp j) fun x => by
    rw [RingHom.comp_apply, hj]
    exact hE _ _
  have hfin := hT₀.1
  have hval : ∀ y, lamF s χ y ∈ (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O))).fieldRange.comap ι := fun y => by
    refine mul_mem (finPart_mem hD.2.2.2.2.2.2.2.1 (condQ_ne_bot hD.2.2.2.2.1.1 ∅)
      (OrderUnits.finPart_eq_one H.E I φ hD.1 s κ 𝔣 ∅ χ hU hD.2.2.2.2.1 (fun _ h => absurd h (Finset.notMem_empty _))
        hD.2.2.2.2.2) _ hE S hS y) ?_
    rw [Complex.ofReal_pow]
    exact pow_mem (modF_mem _ y) s
  rw [mul_comm, ← div_eq_mul_inv, ← map_div₀, ← hz]
  refine (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 fun τ => ?_
  obtain ⟨g, hgI, hgτ⟩ := hτ τ
  have hfx : ∀ x : Ω, ι (j x) ∈ (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O))).range → g x = x :=
    fun x ⟨y, hy⟩ => (ι.comp j).injective ((hgτ x).trans (by rw [RingHom.comp_apply, ← hy, τ.commutes]))
  obtain ⟨x, hx, hax⟩ := (ha.ine v A hA' _).2 ⟨g⁻¹, inv_mem hgI, rfl⟩
  refine (hgτ z).symm.trans (congrArg (ι.comp j) (hfix g.toRingEquiv fun r => ?_))
  refine (hg g (fun x τ y h => hfx x (h ▸ hE _ _)) (fun x y h => hfx x (h ▸ hval y)) (single v x) hax (r.comp π)).trans ?_
  rw [MonoidHom.comp_apply, hπ _ (isUnitOver_up hv hx), map_one, Units.val_one, map_one, inv_one, one_mul]
  rfl

theorem isCMValueHeckeCharacter_auxiliarySet_of_empty {E : Type} [Field E] [NumberField E] {φ : I → E →+* ℂ} {𝔣 : Ideal (OF E)} {χ : HChar E}
    {Q : Finset (HeightOneSpectrum (OF E))} (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (h : IsValChar φ s κ 𝔣 ∅ χ) : IsValChar φ s κ 𝔣 Q χ := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun v P hP => ⟨fun hv => ?_, fun _ => (h.2.2.2 v P hP).2 (Finset.notMem_empty v)⟩⟩
  refine ((h.2.2.2 v P hP).2 (Finset.notMem_empty v) 1).2 ?_
  rw [expIn, multiplicity_eq_zero.2 (hQ v hv).2]
  exact zero_le_one

theorem exists_classTerms (hL : ToricSumFormula) (hU : UnramFin H.E) (hD : IsHostDatum H φ s κ 𝔣 χ)
    {Q : Finset (HeightOneSpectrum (OF H.E))} (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) :
    Finite (PicO (condQ 𝔣 Q)) ∧ ∃ T : PicO (condQ 𝔣 Q) → ℂ, ∀ q, IsClassTerm φ s κ (condQ 𝔣 Q) χ q.out (T q) := by
  have : IsCMField H.E := H.isCMField_hostE
  have hv := isCMValueHeckeCharacter_auxiliarySet_of_empty hQ hD.2.2.2.2.2
  obtain ⟨Λ, hΛ⟩ := exists_isHeckeL hD.2.2.2.2.1 hQ hv
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hD.2.2.2.2.1.2.1
  obtain ⟨P₀, -⟩ := (hD.2.2.2.2.1.2.2 ⟨M, hM.isPrime, fun h => hD.2.2.2.2.1.1 (le_bot_iff.1 (h ▸ hle))⟩
    (Ideal.dvd_iff_le.2 hle)).1
  have : ∀ q : HeightOneSpectrum (OF H.E), ∃ P, q ∈ Q → Over P q := fun q => by
    by_cases hq : q ∈ Q
    · obtain ⟨P, -, -, hP, -⟩ := (hQ q hq).1
      exact ⟨P, fun _ => hP⟩
    · exact ⟨P₀, fun h => absurd h hq⟩
  choose Pq hPq using this
  obtain ⟨h1, T, hT, -⟩ := (isToricSum_iff _ _ _ _ _ _).1
    (hL _ I φ hD.1 s κ 𝔣 Q χ Pq Λ hU hD.2.2.1 hD.2.2.2.2.1 hQ hv hPq hΛ)
  exact ⟨h1, T, hT⟩

theorem exists_toricSum_ne_zero (hL : ToricSumFormula) (hU : UnramFin H.E) (hD : IsHostDatum H φ s κ 𝔣 χ) :
    ∃ T₀, IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀ ∧ T₀ ≠ 0 := by
  have : IsCMField H.E := H.isCMField_hostE
  have hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 ∅ := fun _ h => absurd h (Finset.notMem_empty _)
  obtain ⟨Λ, hΛ⟩ := exists_isHeckeL hD.2.2.2.2.1 hQ hD.2.2.2.2.2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hD.2.2.2.2.1.2.1
  obtain ⟨P₀, -⟩ := (hD.2.2.2.2.1.2.2 ⟨M, hM.isPrime, fun h => hD.2.2.2.2.1.1 (le_bot_iff.1 (h ▸ hle))⟩
    (Ideal.dvd_iff_le.2 hle)).1
  refine ⟨_, hL _ I φ hD.1 s κ 𝔣 ∅ χ (fun _ => P₀) Λ hU hD.2.2.1 hD.2.2.2.2.1 hQ hD.2.2.2.2.2
    (fun _ h => absurd h (Finset.notMem_empty _)) hΛ, ?_⟩
  rw [Finset.filter_empty, Finset.prod_empty, mul_one]
  refine heckeL_ne_zero_nat exists_isHeckeL_of_hasInf H.E I φ hD.1 _ χ Λ s hD.2.2.2.2.2.1 hD.2.2.2.2.2.2.2.1 (fun i => ?_) hΛ hD.2.2.1
  have := hD.2.2.1
  omega

end Core

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_isRecMap (hA : GlobalTheory.Published.GlobalArtinReciprocity) {i : X.Tw} {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}
    (hQ : BlochKatoReduction.Gen.QOk X i Q) (𝔣 : Ideal (OF D.host.E)) :
    ∃ π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q, IsRecMap X i Q π ∧
      ∀ y, IsUnitOver (X.l i) y → π (QuotientGroup.mk y) = 1 := by
  classical
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨art, ha⟩ := hA D.host.E N.Om
  let θ : (Af D.host.E)ˣ →* X.RCG i Q := (liftOpen (X.art i Q) (X.art_cont i Q)).comp (art.comp (finIdele D.host.E))
  have key : ∀ r : X.RCG i Q →* ℂˣ, ∃ ξ, Corr art (r.comp (X.art i Q)) ξ ∧ ∀ y, r (θ y) = finPart ξ y := fun r => by
    obtain ⟨ξ, hξ⟩ := exists_corr (r := r.comp (X.art i Q)) ha
      (Subgroup.isOpen_mono (fun g hg => by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hg, map_one]) (X.art_cont i Q))
    refine ⟨ξ, hξ, fun y => ?_⟩
    obtain ⟨σ, hσ⟩ := toAb_surjective (art (finIdele D.host.E y))
    show r (liftOpen _ (X.art_cont i Q) (art (finIdele D.host.E y))) = _
    rw [← hσ, liftOpen_toAb]
    exact (hξ _ σ hσ.symm).symm
  have hQl : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((X.l i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → P ∉ Q := fun P hP h =>
    Finset.disjoint_left.1 hQ.2.1 h (X.twistExcludedPlaces_contains_residueChar i hP)
  obtain ⟨n, hn⟩ := exists_exponent X i Q
  have hk : princ ⊔ hatOUnits (condQ 𝔣 (belowSet Q)) ≤ θ.ker := by
    refine sup_le ?_ fun u hu => eq_one_of_chars (Ω := ℂ) fun r => ?_
    · rintro _ ⟨k, rfl⟩
      refine eq_one_of_chars (Ω := ℂ) fun r => ?_
      obtain ⟨ξ, hξ, e⟩ := key r
      have hp := hξ.pow (m := X.l i ^ n) fun σ => by rw [MonoidHom.comp_apply, ← map_pow, hn, map_one]
      have := finPart_mul_inf ξ k
      rwa [inf_of_pow (pow_ne_zero n (X.lPrime i).out.ne_zero) hp, mul_one, ← e] at this
    · obtain ⟨ξ, hξ, e⟩ := key r
      have hp := hξ.pow (m := X.l i ^ n) fun σ => by rw [MonoidHom.comp_apply, ← map_pow, hn, map_one]
      rw [e]
      refine OrderUnits.finPart_eq_one_of_level (trivOnF_of_corr ha hξ) (fun v => ?_) hu
      by_cases hv : v ∈ belowSet Q
      · refine ⟨1, ?_, fun P hP => ?_⟩
        · rw [pow_one]
          exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF D.host.E) => q.asIdeal) hv) _
        · by_cases hPl : ((X.l i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
          · exact fun x hx _ => unrAt_of_corr ha hξ (hQl P hPl) x hx
          · exact levelLe_one_of_pow (X.lPrime i).out hp hPl
      · exact ⟨0, by simp, fun P hP x hx _ => unrAt_of_corr ha hξ
          (fun hm => hv (Finset.mem_image.2 ⟨P, hm, HeightOneSpectrum.ext hP⟩)) x hx⟩
  refine ⟨QuotientGroup.lift _ θ hk, fun P _ hP σ hσ => ?_, fun y hy => eq_one_of_chars (Ω := ℂ) fun r => ?_⟩
  · rw [eq_inv_iff_mul_eq_one]
    refine eq_one_of_chars (Ω := ℂ) fun r => ?_
    obtain ⟨ξ, hξ, e⟩ := key r
    rw [map_mul, QuotientGroup.lift_mk, e, finPart_unifAt, hξ.val ha (N.plOm.2 P) (unrAt_of_corr ha hξ hP) hσ]
    exact inv_mul_cancel _
  · obtain ⟨ξ, hξ, e⟩ := key r
    rw [QuotientGroup.lift_mk, e]
    exact finPart_of_isUnitOver (fun P hP => unrAt_of_corr ha hξ (hQl P hP)) hy

theorem atSide_emb_mem {i : X.Tw} {ι : ℂ →+* Kbar X i}
    (h : ∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) (b : Bool) (σ : D.host.E →+* ℂ) (x : D.host.E) :
    atSide X b ι (σ x) ∈ (algebraMap (FractionRing (X.O i)) (Kbar X i)).range := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have key : ∀ σ : D.host.E →+* ℂ, ι (σ x) ∈ (algebraMap (FractionRing (X.O i)) (Kbar X i)).range := fun σ => by
    let _ : Algebra D.host.E ℂ := D.host.φ₀.toAlgebra
    have : IsScalarTower ℚ D.host.E ℂ := IsScalarTower.of_algebraMap_eq fun q => (map_ratCast D.host.φ₀ q).symm
    have e : D.host.φ₀ (σ.toRatAlgHom.restrictNormal D.host.E x) = σ x := σ.toRatAlgHom.restrictNormal_commutes D.host.E x
    rw [← e, ← D.embE_φ₀]
    exact ⟨_, (h ⟨_, D.hostField_le_fixedField _⟩).symm⟩
  cases b
  · exact key ((starRingEnd ℂ).comp σ)
  · exact key σ

end Record

end GlobalTheory.ToricRational
