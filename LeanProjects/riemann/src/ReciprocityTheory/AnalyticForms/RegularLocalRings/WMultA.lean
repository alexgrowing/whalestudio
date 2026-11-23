import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsBasicOpenCover
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial

namespace ReciprocityTheory.AnForm.R.WMult

open AlgebraicGeometry CategoryTheory IsLocalRing

variable {W : Scheme.{0}}

theorem stalkId_eq_map_germ (I : W.IdealSheafData) (y : W) (U : W.affineOpens) (hy : y ∈ U.1) :
    FinalTheorems.stalkId I y = Ideal.map (W.presheaf.germ U.1 y hy).hom (I.ideal U) := by
  have key : ∀ (V V' : W.affineOpens) (h : V' ≤ V) (hyV' : y ∈ V'.1),
      Ideal.map (W.presheaf.germ V.1 y ((show V'.1 ≤ V.1 from h) hyV')).hom (I.ideal V) =
        Ideal.map (W.presheaf.germ V'.1 y hyV').hom (I.ideal V') := by
    intro V V' h hyV'
    rw [← I.map_ideal h, Ideal.map_map]
    congr 1
    rw [← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom (W.presheaf.germ_res (homOfLE (show V'.1 ≤ V.1 from h)) y hyV').symm
  rw [FinalTheorems.stalkId]
  apply le_antisymm
  · refine iSup₂_le fun V hyV => ?_
    obtain ⟨f, g, hfg, hyf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 y ⟨hy, hyV⟩
    have hWU : W.affineBasicOpen f ≤ U := W.basicOpen_le f
    have hWV : W.affineBasicOpen f ≤ V := by
      show W.basicOpen f ≤ V.1
      rw [hfg]
      exact W.basicOpen_le g
    rw [key V _ hWV hyf, key U _ hWU hyf]
  · exact le_iSup₂ (f := fun (V : W.affineOpens) (hV : y ∈ V.1) =>
      Ideal.map (W.presheaf.germ V.1 y hV).hom (I.ideal V)) U hy

theorem mem_support_fromSpec_iff (I : W.IdealSheafData) (U : W.affineOpens) (hU : IsAffineOpen U.1)
    (P : PrimeSpectrum Γ(W, U.1)) :
    hU.fromSpec P ∈ (I.support : Set W) ↔ I.ideal U ≤ P.asIdeal := by
  have hmem : hU.fromSpec P ∈ U.1 := by
    have hr : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rw [hU.range_fromSpec] at hr
    exact hr
  show hU.fromSpec P ∈ I.support ↔ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hmem]
  exact (Set.ext_iff.1 (hU.fromSpec_preimage_zeroLocus (I.ideal U : Set Γ(W, U.1))) P).trans
    ((PrimeSpectrum.mem_zeroLocus _ _).trans SetLike.coe_subset_coe)

private theorem ring_ord_ringEquiv_apply {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (z : A) : Ring.ord B (e z) = Ring.ord A z := by
  have hI : Ideal.comap e (Ideal.span {e z}) = Ideal.span {z} := by
    rw [show Ideal.span {e z} = Ideal.map e (Ideal.span {z}) by rw [Ideal.map_span, Set.image_singleton]]
    exact Ideal.comap_map_of_bijective e e.bijective
  unfold Ring.ord
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  refine Order.krullDim_eq_of_orderIso ?_
  let o3 := Ideal.relIsoOfBijective (e : A →+* B) e.bijective
  have h3 : o3 (Ideal.span {e z}) = Ideal.span {z} := hI
  exact (Submodule.comapMkQRelIso _).trans (((o3.Ici _).trans
    (OrderIso.setCongr _ _ (by rw [h3]))).trans (Submodule.comapMkQRelIso _).symm)

theorem ord_isLocalization_eq_exponent {R : Type*} [CommRing R] [IsRegularLocalRing R] {n : ℕ}
    (f : Fin n → R)
    (hspan : Ideal.span (Set.range f) = maximalIdeal R) (hdim : (n : WithBot ℕ∞) = ringKrullDim R)
    (J : Finset (Fin n)) (u : Rˣ) (m : Fin n → ℕ) (i : Fin n) (hi : i ∈ J)
    [(Ideal.span {f i}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S (Ideal.span {f i})] :
    Ring.ord S (algebraMap R S (u * ∏ j ∈ J, f j ^ m j)) = (m i : ℕ∞) := by
  have hL := ord_localization_eq_exponent f hspan hdim J u m i hi
  let e : Localization.AtPrime (Ideal.span {f i}) ≃ₐ[R] S :=
    IsLocalization.algEquiv (Ideal.span {f i}).primeCompl (Localization.AtPrime (Ideal.span {f i})) S
  rw [← e.commutes, ← hL]
  exact ring_ord_ringEquiv_apply e.toRingEquiv _

end ReciprocityTheory.AnForm.R.WMult
