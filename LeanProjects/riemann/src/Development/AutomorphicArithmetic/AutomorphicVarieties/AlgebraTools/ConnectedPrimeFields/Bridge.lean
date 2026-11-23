import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.etaleCohomology_simplicialCochain_representation_step {R : Type} [CommRing R] (a I : Ideal R) :
    IsConnected (PrimeSpectrum.zeroLocus (a : Set R) \ PrimeSpectrum.zeroLocus (I : Set R)) ↔
    IsConnected ((PrimeSpectrum.zeroLocus
      ((I.map (Ideal.Quotient.mk a) : Ideal (R ⧸ a)) : Set (R ⧸ a)))ᶜ :
        Set (PrimeSpectrum (R ⧸ a))) := by
  have hs : Function.Surjective (Ideal.Quotient.mk a) := Ideal.Quotient.mk_surjective
  have hemb := PrimeSpectrum.isClosedEmbedding_comap_of_surjective (R ⧸ a) (Ideal.Quotient.mk a) hs
  have hr := range_comap_of_surjective (R ⧸ a) (Ideal.Quotient.mk a) hs
  rw [Ideal.mk_ker] at hr
  have hpre : (PrimeSpectrum.zeroLocus
      ((I.map (Ideal.Quotient.mk a) : Ideal (R ⧸ a)) : Set (R ⧸ a))) =
      PrimeSpectrum.comap (Ideal.Quotient.mk a) ⁻¹' PrimeSpectrum.zeroLocus (I : Set R) := by
    ext p
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_preimage, SetLike.coe_subset_coe,
      PrimeSpectrum.comap_asIdeal]
    exact Ideal.map_le_iff_le_comap
  have him : PrimeSpectrum.comap (Ideal.Quotient.mk a) '' ((PrimeSpectrum.zeroLocus
      ((I.map (Ideal.Quotient.mk a) : Ideal (R ⧸ a)) : Set (R ⧸ a)))ᶜ) =
      PrimeSpectrum.zeroLocus (a : Set R) \ PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [hpre, ← Set.preimage_compl, Set.image_preimage_eq_inter_range, hr, Set.diff_eq,
      Set.inter_comm]
  rw [← him]
  unfold IsConnected
  rw [Set.image_nonempty, hemb.isInducing.isPreconnected_image]

theorem UpperTheory.V.AlgebraTools.Conn.bridge :
    ∀ {R : Type} [CommRing R] (a : Ideal R) (k : WithBot ℕ∞), ConnOn a k ↔ ReciprocityTheory.CA.ConnInDim (R ⧸ a) k := by
  intro R _ a k
  constructor
  · intro h J hJ
    have hs : Function.Surjective (Ideal.Quotient.mk a) := Ideal.Quotient.mk_surjective
    have hle : a ≤ J.comap (Ideal.Quotient.mk a) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact J.zero_mem
    have hJ' : (J.comap (Ideal.Quotient.mk a)).map (Ideal.Quotient.mk a) = J :=
      Ideal.map_comap_of_surjective _ hs J
    rw [← hJ'] at hJ ⊢
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hJ
    exact (etaleCohomology_simplicialCochain_representation_step a _).mp (h _ hle hJ)
  · intro h I hle hI
    rw [← ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hI
    exact (etaleCohomology_simplicialCochain_representation_step a I).mpr (h _ hI)
