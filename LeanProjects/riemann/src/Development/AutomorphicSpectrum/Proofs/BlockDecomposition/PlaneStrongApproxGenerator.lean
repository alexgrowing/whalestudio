import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlacesIdempotentMulAbsorbStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecialUnitarySupportProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSpecialUnitarySupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseDiagonalTwoPlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseVectorPairTwoPlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryProductReflectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReflectionsGenerateSubgroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalBasisBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousLocalLiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLiftSpecialSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecialSupportOfLocalLiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicPlaneOpenNearStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftDetOneAdelicApproxStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryQuadraticPairPerturbNearbyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftDetOneApproxPairStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorInvolutionInvolutiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorFieldOrSplitIdempotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneGeneratedOfFieldStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormOneGeneratedOfSplitIdempotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicOfSplitIdempotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropicUnitaryGroupCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOneUnitaryClosedStatement

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

theorem idem_mul_eq : ∀ {F : Type} [Field F] [NumberField F] {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F}, IsPlacesIdem A₁ A₂ a → IsPlacesIdem B₁ B₂ b → A₁ ⊆ B₁ → A₂ ⊆ B₂ → b * a = a :=
  @GlobalTheory.T.places_idempotent_mul_absorb

theorem supp_le_of_single : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (N : Subgroup (HA (AF F) σ J)) {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} {δ : AF F}, IsPlacesIdem T₁ T₂ δ → (∀ w ∈ T₁, ∀ e : AF F, IsPlacesIdem {w} ∅ e → SUSupp σ J e ⊆ N) → (∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → SUSupp σ J e ⊆ N) → SUSupp σ J δ ⊆ N :=
  @GlobalTheory.T.special_unitary_support_product

theorem compact_of_singles : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} {δ : AF F}, IsPlacesIdem T₁ T₂ δ → (∀ w ∈ T₁, ∀ e : AF F, IsPlacesIdem {w} ∅ e → IsCompact (SUSupp σ J e)) → (∀ v ∈ T₂, ∀ e : AF F, IsPlacesIdem ∅ {v} e → IsCompact (SUSupp σ J e)) → IsCompact (SUSupp σ J δ) :=
  @GlobalTheory.T.isCompact_special_unitary_support

theorem dense_pair : ∀ {F : Type} [Field F] [NumberField F] {K₁ K₂ : Type} [Field K₁] [Algebra F K₁] [TopologicalSpace K₁] [Field K₂] [Algebra F K₂] [TopologicalSpace K₂] (P₁ : PlaceMap F K₁) (P₂ : PlaceMap F K₂) {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))}, IsPlacesIdem A₁ A₂ (P₁.inj 1) → IsPlacesIdem B₁ B₂ (P₂.inj 1) → Disjoint A₁ B₁ → Disjoint A₂ B₂ → DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)) :=
  @GlobalTheory.T.dense_diagonal_two_places

theorem dense_rat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {K₁ K₂ : Type} [NontriviallyNormedField K₁] [Algebra F K₁] [NontriviallyNormedField K₂] [Algebra F K₂], DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)) → ∀ M : ℕ, DenseRange (fun p : (Fin M → E) × (Fin M → E) => (((incV K₁ p.1, incV K₁ p.2), (incV K₂ p.1, incV K₂ p.2)) : ((Fin M → K₁ ⊗[F] E) × (Fin M → K₁ ⊗[F] E)) × ((Fin M → K₂ ⊗[F] E) × (Fin M → K₂ ⊗[F] E)))) :=
  @GlobalTheory.T.dense_vector_pair_two_places

theorem refl_list : ∀ {R : Type} [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → NormOneGen c → ∀ {M : ℕ} (Jm : Matrix (Fin M) (Fin M) R), (∀ i j, c (Jm j i) = Jm i j) → ∀ e : Fin M → Fin M → R, (∀ i j, i ≠ j → Formalism.UG.hform c Jm (e i) (e j) = 0) → (∀ i, IsUnit (Formalism.UG.hform c Jm (e i) (e i))) → IsUnit (Matrix.of e).det → ∀ x : GL (Fin M) R, x ∈ Formalism.UG.UJ c Jm → ∃ l : List (GL (Fin M) R), (∀ y ∈ l, y ∈ Formalism.UG.UJ c Jm ∧ IsQR c Jm (y : Matrix (Fin M) (Fin M) R)) ∧ l.prod = x :=
  @GlobalTheory.T.unitary_product_reflections

theorem pair_of_list : ∀ {R : Type} [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → ∀ {M : ℕ} (Jm : Matrix (Fin M) (Fin M) R), (∀ i j, c (Jm j i) = Jm i j) → ∀ a₀ : Fin M → R, IsUnit (Formalism.UG.hform c Jm a₀ a₀) → ∀ H : Subgroup (GL (Fin M) R), (∀ y ∈ Formalism.UG.UJ c Jm, IsQPair c Jm (y : Matrix (Fin M) (Fin M) R) → y ∈ H) → ∀ l : List (GL (Fin M) R), (∀ y ∈ l, y ∈ Formalism.UG.UJ c Jm ∧ IsQR c Jm (y : Matrix (Fin M) (Fin M) R)) → ((l.prod : GL (Fin M) R) : Matrix (Fin M) (Fin M) R).det = 1 → l.prod ∈ H :=
  @GlobalTheory.T.reflections_generate_subgroup

theorem exists_orth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K], ∃ e : Fin M → Fin M → K ⊗[F] E, (∀ i j, i ≠ j → Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e j) = 0) ∧ (∀ i, IsUnit (Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e i))) ∧ IsUnit (Matrix.of e).det :=
  @GlobalTheory.T.orthogonal_basis_base_change

theorem exists_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K), ∃ L : HA K σ J →* HA (AF F) σ J, Continuous L ∧ IsLift P σ J L :=
  @GlobalTheory.T.exists_continuous_local_lift

theorem lift_mem_supp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → ∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1) :=
  @GlobalTheory.T.local_lift_special_support

theorem exists_of_mem_supp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → ∀ g ∈ SUSupp σ J (P.inj 1), ∃ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 ∧ L x = g :=
  @GlobalTheory.T.special_support_of_local_lift

theorem iso_plane : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [ProperSpace K] [Algebra F K], IsoAt K σ J → ∃ a₀ b₀ : Fin M → K ⊗[F] E, ∀ᶠ p in nhds (a₀, b₀), IsoPlane K σ J p.1 p.2 :=
  @GlobalTheory.T.isotropic_plane_open_near

theorem not_compact : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → (∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1)) → ∀ ε : AF F, ε * P.inj 1 = P.inj 1 → ∀ a b : Fin M → E, IsoPlane K σ J (incV K a) (incV K b) → ¬ IsCompact (PlaneSupp σ J ε a b) :=
  @GlobalTheory.T.unitary_lift_det_one_adelic_approx

theorem near_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (a₀ b₀ : Fin M → K ⊗[F] E) (x : HA K σ J), IsQPairOf (sigR K σ) (JR K J) a₀ b₀ ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) → ∀ V ∈ nhds x, ∀ᶠ p in nhds (a₀, b₀), ∃ x' ∈ V, IsQPairOf (sigR K σ) (JR K J) p.1 p.2 ((HA.mat K σ J x').1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) :=
  @GlobalTheory.T.unitary_quadratic_pair_perturb_nearby

theorem lift_plane : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → (∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1)) → ∀ (a b : Fin M → E) (x : HA K σ J), IsQPairOf (sigR K σ) (JR K J) (incV K a) (incV K b) ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) → L x ∈ PlaneSupp σ J (P.inj 1) a b :=
  @GlobalTheory.T.unitary_lift_det_one_approx_pair

theorem sigR_invol : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (t : K ⊗[F] E), sigR K σ (sigR K σ t) = t :=
  @GlobalTheory.T.tensor_involution_involutive

theorem dichotomy : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], IsField (K ⊗[F] E) ∨ ∃ e : K ⊗[F] E, e * e = e ∧ e + sigR K σ e = 1 ∧ e * sigR K σ e = 0 :=
  @GlobalTheory.T.tensor_field_or_split_idempotent

theorem normOne_field : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], IsField (K ⊗[F] E) → NormOneGen (sigR K σ) :=
  @GlobalTheory.T.norm_one_generated_of_field

theorem normOne_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (e : K ⊗[F] E), e * e = e → e + sigR K σ e = 1 → e * sigR K σ e = 0 → NormOneGen (sigR K σ) :=
  @GlobalTheory.T.norm_one_generated_of_split_idempotent

theorem iso_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K] (e : K ⊗[F] E), e * e = e → e + sigR K σ e = 1 → e * sigR K σ e = 0 → IsoAt K σ J :=
  @GlobalTheory.T.isotropic_of_split_idempotent

theorem compact_field : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [ProperSpace K] [Algebra F K], IsField (K ⊗[F] E) → ¬ IsoAt K σ J → IsCompact (Set.univ : Set (HA K σ J)) :=
  @GlobalTheory.T.anisotropic_unitary_group_compact

theorem det_closed : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {K : Type} [NontriviallyNormedField K] [Algebra F K], IsClosed {x : HA K σ J | ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1} :=
  @GlobalTheory.T.det_one_unitary_closed

theorem supp_mono {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) {a b : AF F} (h : b * a = a) : SUSupp σ J a ⊆ SUSupp σ J b := by
  rintro g ⟨h1, h2⟩
  refine ⟨h1, fun i j => ?_⟩
  rw [← h2 i j, ← mul_assoc, ← map_mul, h]

theorem hR_incV {F E : Type} [Field F] [Field E] [Algebra F E] (K : Type) [CommRing K] [Algebra F K]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hR K σ J (incV K x) (incV K y) = inclR K (hf σ J x y) := by
  have hs : ∀ t : E, sigR K σ (inclR K t) = inclR K (σ t) := by
    intro t
    simp [sigR, inclR]
  simp only [hR, Formalism.UG.hform, hf, map_sum, map_mul, incV, hs, JR, Matrix.map_apply]

theorem normOneGen_sigR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hCM : IsCMExt F E σ) (K : Type) [Field K] [Algebra F K] : NormOneGen (sigR K σ) := by
  rcases dichotomy σ hCM K with h | ⟨e, h1, h2, h3⟩
  · exact normOne_field σ hCM K h
  · exact normOne_split σ hCM K e h1 h2 h3

theorem compact_of_not_iso {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hM : 2 ≤ M) (hJ : IsHermND σ J)
    {K : Type} [NontriviallyNormedField K] [ProperSpace K] [Algebra F K] (hni : ¬ IsoAt K σ J) :
    IsCompact (Set.univ : Set (HA K σ J)) := by
  rcases dichotomy σ hCM K with h | ⟨e, h1, h2, h3⟩
  · exact compact_field σ hCM J hJ h hni
  · exact absurd (iso_split σ hCM J hM hJ K e h1 h2 h3) hni

theorem compact_supp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J)
    (hLc : Continuous L) (hL : IsLift P σ J L) (hc : IsCompact (Set.univ : Set (HA K σ J))) :
    IsCompact (SUSupp σ J (P.inj 1)) := by
  have e : SUSupp σ J (P.inj 1) =
      L '' {x : HA K σ J | ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1} := by
    ext g
    constructor
    · intro hg
      obtain ⟨x, hx, rfl⟩ := exists_of_mem_supp σ hCM J P L hL g hg
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact lift_mem_supp σ hCM J P L hL x hx
  rw [e]
  exact (hc.of_isClosed_subset (det_closed σ hCM J) (Set.subset_univ _)).image hLc

theorem local_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hCM : IsCMExt F E σ) {M : ℕ} (hM : 2 ≤ M) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (K : Type) [Field K] [Algebra F K] (H : Subgroup (GL (Fin M) (K ⊗[F] E)))
    (hH : ∀ y ∈ Formalism.UG.UJ (sigR K σ) (JR K J), IsQPair (sigR K σ) (JR K J) (y : Matrix (Fin M) (Fin M) (K ⊗[F] E)) → y ∈ H)
    (x : GL (Fin M) (K ⊗[F] E)) (hx : x ∈ Formalism.UG.UJ (sigR K σ) (JR K J))
    (hd : (x : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1) : x ∈ H := by
  have hc : ∀ t, sigR K σ (sigR K σ t) = t := sigR_invol σ hCM K
  have hJR : ∀ i j, sigR K σ (JR K J j i) = JR K J i j := fun i j => map_mem_HermR K σ J hJ.1 i j
  obtain ⟨e, h1, h2, h3⟩ := exists_orth σ hCM J hJ K
  obtain ⟨l, hl, rfl⟩ := refl_list (sigR K σ) hc (normOneGen_sigR σ hCM K) (JR K J) hJR e h1 h2 h3 x hx
  exact pair_of_list (sigR K σ) hc (JR K J) hJR (e ⟨0, by omega⟩) (h2 _) H hH l hl hd

theorem pair_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (ε : AF F) (N : Subgroup (HA (AF F) σ J)) (hN : IsClosed (N : Set (HA (AF F) σ J)))
    {K₁ K₂ : Type} [NontriviallyNormedField K₁] [Algebra F K₁] [NontriviallyNormedField K₂] [ProperSpace K₂]
    [Algebra F K₂] (P₁ : PlaceMap F K₁) (P₂ : PlaceMap F K₂)
    {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} (hT : IsPlacesIdem T₁ T₂ (P₁.inj 1))
    (hP : ∀ u₀ u₁ : Fin M → E, PlaneND σ J u₀ u₁ → ¬ IsCompact (PlaneSupp σ J ε u₀ u₁) →
      PlaneSupp σ J (P₁.inj 1) u₀ u₁ ⊆ N)
    (hd : DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)))
    (hε : ε * P₂.inj 1 = P₂.inj 1) (hiso : IsoAt K₂ σ J)
    (L : HA K₁ σ J →* HA (AF F) σ J) (hLc : Continuous L) (hL : IsLift P₁ σ J L)
    (x : HA K₁ σ J) (a₀ b₀ : Fin M → K₁ ⊗[F] E)
    (hx : IsQPairOf (sigR K₁ σ) (JR K₁ J) a₀ b₀ ((HA.mat K₁ σ J x).1 : Matrix (Fin M) (Fin M) (K₁ ⊗[F] E))) :
    L x ∈ N := by
  rw [← SetLike.mem_coe, ← hN.closure_eq, mem_closure_iff_nhds]
  intro U hU
  obtain ⟨a₂, b₂, h2⟩ := iso_plane σ hCM J hJ hiso
  obtain ⟨L₂, -, hL₂⟩ := exists_lift σ hCM J hJ P₂
  have h1 := near_pair σ hCM J hJ a₀ b₀ x hx (L ⁻¹' U) (hLc.continuousAt hU)
  have hprod := Filter.Eventually.prod_nhds h1 h2
  obtain ⟨p, ⟨x', hx'U, hx'⟩, hp2⟩ := (dense_rat σ hCM hd M).mem_nhds hprod
  have hND : PlaneND σ J p.1 p.2 := by
    intro h0
    apply hp2.1
    rw [hR_incV, hR_incV, hR_incV, hR_incV, ← map_mul, ← map_mul, ← map_sub, h0, map_zero]
  exact ⟨L x', hx'U, hP _ _ hND (not_compact σ hCM J hJ P₂ L₂ hL₂ (lift_mem_supp σ hCM J P₂ L₂ hL₂) ε hε _ _ hp2)
    (lift_plane σ hCM J hJ P₁ L hL (lift_mem_supp σ hCM J P₁ L hL) _ _ _ hx')⟩

theorem local_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hCM : IsCMExt F E σ) {M : ℕ} (hM : 2 ≤ M) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (ε : AF F) (N : Subgroup (HA (AF F) σ J)) (hN : IsClosed (N : Set (HA (AF F) σ J)))
    {K₁ K₂ : Type} [NontriviallyNormedField K₁] [Algebra F K₁] [NontriviallyNormedField K₂] [ProperSpace K₂]
    [Algebra F K₂] (P₁ : PlaceMap F K₁) (P₂ : PlaceMap F K₂)
    {T₁ : Finset (InfinitePlace F)} {T₂ : Finset (HeightOneSpectrum (𝓞 F))} (hT : IsPlacesIdem T₁ T₂ (P₁.inj 1))
    (hP : ∀ u₀ u₁ : Fin M → E, PlaneND σ J u₀ u₁ → ¬ IsCompact (PlaneSupp σ J ε u₀ u₁) →
      PlaneSupp σ J (P₁.inj 1) u₀ u₁ ⊆ N)
    (hd : DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)))
    (hε : ε * P₂.inj 1 = P₂.inj 1) (hiso : IsoAt K₂ σ J) :
    SUSupp σ J (P₁.inj 1) ⊆ N := by
  obtain ⟨L, hLc, hL⟩ := exists_lift σ hCM J hJ P₁
  intro g hg
  obtain ⟨x, hxd, rfl⟩ := exists_of_mem_supp σ hCM J P₁ L hL g hg
  let Hs : Subgroup (GL (Fin M) (K₁ ⊗[F] E)) := (N.comap L).map (HR K₁ σ J).subtype
  have hmem : (x : HR K₁ σ J).1 ∈ Hs := by
    refine local_gen σ hCM hM J hJ K₁ Hs ?_ _ x.2 hxd
    rintro y hy ⟨a, b, hab⟩
    exact ⟨⟨y, hy⟩, pair_mem σ hCM J hJ ε N hN P₁ P₂ hT hP hd hε hiso L hLc hL ⟨y, hy⟩ a b hab, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hmem
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem idem_unique {F : Type} [Field F] [NumberField F] {A₁ : Finset (InfinitePlace F)}
    {A₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F} (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem A₁ A₂ b) :
    a = b := by
  have h1 := idem_mul_eq ha hb subset_rfl subset_rfl
  have h2 := idem_mul_eq hb ha subset_rfl subset_rfl
  rw [← h1, mul_comm, h2]

theorem exists_iso_place {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (hM : 2 ≤ M) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε)
    (hnc : ¬ IsCompact (SUSupp σ J ε)) :
    ∃ (K : Type) (_ : NontriviallyNormedField K) (_ : ProperSpace K) (_ : Algebra F K) (P : PlaceMap F K)
      (B₁ : Finset (InfinitePlace F)) (B₂ : Finset (HeightOneSpectrum (𝓞 F))),
      B₁ ⊆ S₁ ∧ B₂ ⊆ S₂ ∧ IsPlacesIdem B₁ B₂ (P.inj 1) ∧ IsoAt K σ J := by
  by_contra hno
  apply hnc
  have key : ∀ (B₁ : Finset (InfinitePlace F)) (B₂ : Finset (HeightOneSpectrum (𝓞 F))) (e : AF F),
      B₁ ⊆ S₁ → B₂ ⊆ S₂ → IsPlacesIdem B₁ B₂ e →
      ∀ (K : Type) (_ : NontriviallyNormedField K) (_ : ProperSpace K) (_ : Algebra F K) (P : PlaceMap F K),
        IsPlacesIdem B₁ B₂ (P.inj 1) → IsCompact (SUSupp σ J e) := by
    intro B₁ B₂ e h1 h2 he K n1 n2 n3 P hP
    have hni : ¬ IsoAt K σ J := fun hi => hno ⟨K, n1, n2, n3, P, B₁, B₂, h1, h2, hP, hi⟩
    obtain ⟨L, hLc, hL⟩ := exists_lift σ hCM J hJ P
    have := compact_supp σ hCM J P L hLc hL (compact_of_not_iso σ hCM J hM hJ hni)
    rwa [idem_unique hP he] at this
  refine compact_of_singles σ hCM J hε (fun w hw e he => ?_) (fun v hv e he => ?_)
  · obtain ⟨K, i1, i2, i3, P, hP⟩ := exists_placeMap_inf w
    exact key {w} ∅ e (Finset.singleton_subset_iff.2 hw) (Finset.empty_subset _) he K i1 i2 i3 P hP
  · obtain ⟨K, i1, i2, i3, P, hP⟩ := exists_placeMap_fin v
    exact key ∅ {v} e (Finset.empty_subset _) (Finset.singleton_subset_iff.2 hv) he K i1 i2 i3 P hP

theorem propGen : Sa2.PropGen := by
  intro F E _ _ _ _ _ σ hCM M J hM hJ S₁ S₂ ε hε hnc N hN hSN hP T₁ T₂ δ hδ
  obtain ⟨K₂, i1, i2, i3, P₂, B₁, B₂, hB1, hB2, hB, hiso⟩ := exists_iso_place σ hCM hM J hJ hε hnc
  have hεe : ε * P₂.inj 1 = P₂.inj 1 := idem_mul_eq hB hε hB1 hB2
  have step : ∀ (A₁ : Finset (InfinitePlace F)) (A₂ : Finset (HeightOneSpectrum (𝓞 F))) (e : AF F),
      IsPlacesIdem A₁ A₂ e → (A₁ ⊆ S₁ ∧ A₂ ⊆ S₂ ∨ Disjoint A₁ B₁ ∧ Disjoint A₂ B₂) →
      ∀ (K : Type) (_ : NontriviallyNormedField K) (_ : ProperSpace K) (_ : Algebra F K) (P : PlaceMap F K),
        IsPlacesIdem A₁ A₂ (P.inj 1) → SUSupp σ J e ⊆ N := by
    intro A₁ A₂ e he hc K _ _ _ P hPi
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact (supp_mono σ J (idem_mul_eq he hε h1 h2)).trans hSN
    · rw [idem_unique he hPi]
      exact local_mem σ hCM hM J hJ ε N hN P P₂ hPi
        (fun u₀ u₁ hnd hc' => hP u₀ u₁ hnd hc' _ _ _ hPi) (dense_pair P P₂ hPi hB h1 h2) hεe hiso
  refine supp_le_of_single σ J N hδ (fun w _ e he => ?_) (fun v _ e he => ?_)
  · obtain ⟨K, n1, n2, n3, P, hPi⟩ := exists_placeMap_inf w
    refine step {w} ∅ e he ?_ K n1 n2 n3 P hPi
    by_cases hw : w ∈ S₁
    · exact Or.inl ⟨Finset.singleton_subset_iff.2 hw, Finset.empty_subset _⟩
    · exact Or.inr ⟨Finset.disjoint_singleton_left.2 (fun h => hw (hB1 h)), Finset.disjoint_empty_left _⟩
  · obtain ⟨K, n1, n2, n3, P, hPi⟩ := exists_placeMap_fin v
    refine step ∅ {v} e he ?_ K n1 n2 n3 P hPi
    by_cases hv : v ∈ S₂
    · exact Or.inl ⟨Finset.empty_subset _, Finset.singleton_subset_iff.2 hv⟩
    · exact Or.inr ⟨Finset.disjoint_empty_left _, Finset.disjoint_singleton_left.2 (fun h => hv (hB2 h))⟩

end GlobalTheory.CompanionTheory.SaGen
