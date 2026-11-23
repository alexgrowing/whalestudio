import Development.EtaleCohomology.EtaleSheaves.SysFMPfSys
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut LateralTheory.E.SysFMPf Topology

namespace LateralTheory.E.FMrangePf

def RRsub : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ q : PrimeSpectrum W,
    RR w q ⊆ closure (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal})

theorem range_spec_atPrime {W : Type} [CommRing W] (q : PrimeSpectrum W) :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))).base =
      {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal} := by
  have h := PrimeSpectrum.localization_comap_range (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
  ext p
  change p ∈ Set.range (PrimeSpectrum.comap (algebraMap W (Localization.AtPrime q.asIdeal))) ↔ _
  rw [h]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hd x hx
    by_contra hq
    exact Set.disjoint_left.1 hd (show x ∈ (q.asIdeal.primeCompl : Set W) from hq) hx
  · intro hle
    exact Set.disjoint_left.2 fun x hx hp => hx (hle hp)

theorem mem_basicOpen_toNorm {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (s : Γ(w.normalization, ⊤)) (p : Spec (CommRingCat.of W)) :
    w.toNormalization p ∈ w.normalization.basicOpen s ↔ phi w s ∉ p.asIdeal := by
  change p ∈ w.toNormalization ⁻¹ᵁ w.normalization.basicOpen s ↔ _
  rw [Scheme.preimage_basicOpen_top, AlgebraicGeometry.basicOpen_eq_of_affine']
  rfl

theorem phi_injective {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Function.Injective (phi w) := by
  have h1 : Function.Injective (w.toNormalization.appTop) := w.toNormalization.app_injective ⊤
  have h2 : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).hom :=
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).hom)).1
  exact h2.comp h1

theorem closure_sub_RR {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (q : PrimeSpectrum W) :
    closure (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal}) ⊆ RR w q := by
  intro y hy s hs hsq
  have hid : IsIdempotentElem s := phi_injective w (by rw [map_mul]; exact hs.eq)
  have hcl : IsClosed (w.normalization.basicOpen s : Set w.normalization) := by
    rw [← isOpen_compl_iff]
    have : (w.normalization.basicOpen s : Set w.normalization)ᶜ = w.normalization.basicOpen (1 - s) := by
      ext x
      exact LateralTheory.E.SysFMPfSys.basicOpen_one_sub hid x
    rw [this]
    exact (w.normalization.basicOpen (1 - s)).isOpen
  refine closure_minimal ?_ hcl hy
  rintro _ ⟨p, hp, rfl⟩
  exact (mem_basicOpen_toNorm w s p).2 fun h => hsq (hp h)

def IdemLift : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ e : W, IsIdempotentElem e → ∃ s, phi w s = e

def QcIdem : Prop := ∀ (W : Type) [CommRing W], ProdACF W → ∀ U : (Spec (CommRingCat.of W)).Opens,
  IsCompact (U : Set (Spec (CommRingCat.of W))) → ∃ e : W, IsIdempotentElem e ∧ ∀ p : Spec (CommRingCat.of W),
    p ∈ U ↔ e ∉ p.asIdeal

theorem RRsub_of (hI : IdemLift) (hQ : QcIdem) : RRsub := by
  intro P _ _ W _ w hW q y hy
  by_contra hc
  rw [mem_closure_iff] at hc
  push Not at hc
  obtain ⟨o, ho, hyo, hoT⟩ := hc
  obtain ⟨V, hV, hyV, hVo⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens w.normalization))
    (show y ∈ (⟨o, ho⟩ : TopologicalSpace.Opens w.normalization) from hyo)
  have hVc : IsCompact (w.toNormalization ⁻¹ᵁ V : Set (Spec (CommRingCat.of W))) :=
    QuasiCompact.isCompact_preimage _ V.isOpen (IsAffineOpen.isCompact hV)
  obtain ⟨e, he, hpe⟩ := hQ W hW _ hVc
  have heq : e ∈ q.asIdeal := by
    by_contra hnq
    have hmem : w.toNormalization q ∈ V := (hpe q).2 hnq
    have : w.toNormalization q ∈ o ∩ (w.toNormalization.base '' {p : Spec (CommRingCat.of W) | p.asIdeal ≤ q.asIdeal}) :=
      ⟨hVo hmem, q, show q.asIdeal ≤ q.asIdeal from le_refl _, rfl⟩
    rw [hoT] at this
    exact this
  have hf : IsIdempotentElem (1 - e) := he.one_sub
  have hfq : (1 - e) ∉ q.asIdeal := fun h => q.2.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using q.asIdeal.add_mem heq h))
  obtain ⟨s, hs⟩ := hI W w hW (1 - e) hf
  have hys : y ∈ w.normalization.basicOpen s := hy s (by rw [hs]; exact hf) (by rw [hs]; exact hfq)
  obtain ⟨_, ⟨hz1, hz2⟩, p, rfl⟩ := w.toNormalization.denseRange.inter_open_nonempty
    ((w.normalization.basicOpen s ⊓ V : w.normalization.Opens) : Set w.normalization)
    (w.normalization.basicOpen s ⊓ V).isOpen ⟨y, hys, hyV⟩
  have h1 : phi w s ∉ p.asIdeal := (mem_basicOpen_toNorm w s p).1 hz1
  have h2 : e ∉ p.asIdeal := (hpe p).1 hz2
  rw [hs] at h1
  have : e * (1 - e) ∈ p.asIdeal := by rw [mul_sub, mul_one, he.eq, sub_self]; exact p.asIdeal.zero_mem
  rcases p.2.mem_or_mem this with h | h
  · exact h2 h
  · exact h1 h

theorem FMrange_of (hC : RRsub) : FMrange := by
  intro P _ _ W _ w hW q m e1 e2
  set a := Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal)))
  have : IsIntegralHom (m ≫ w.fromNormalization) := by rw [e2]; infer_instance
  have : IsIntegralHom m := IsIntegralHom.of_comp m w.fromNormalization
  have hcl : IsClosedMap m.base := m.isClosedMap
  have hd : closure (Set.range (a ≫ w).toNormalization.base) = Set.univ :=
    (a ≫ w).toNormalization.denseRange.closure_range
  have himg : m.base '' Set.range (a ≫ w).toNormalization.base =
      w.toNormalization.base '' Set.range a.base := by
    rw [← Set.range_comp, ← Set.range_comp]
    congr 1
    funext x
    simp only [Function.comp_apply]
    rw [← Scheme.Hom.comp_apply, ← e1, Scheme.Hom.comp_apply]
  rw [subset_antisymm (hC W w hW q) (closure_sub_RR w q), ← range_spec_atPrime q, ← Set.image_univ, ← hd,
    ← hcl.closure_image_eq_of_continuous m.continuous, himg]

theorem FMrange_of_leaves (hI : IdemLift) (hQ : QcIdem) : FMrange :=
  FMrange_of (RRsub_of hI hQ)

end LateralTheory.E.FMrangePf
