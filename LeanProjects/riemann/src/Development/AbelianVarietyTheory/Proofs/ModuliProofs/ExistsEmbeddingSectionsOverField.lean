import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalMultiplicationPullbackThetaEmbeddingI
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapCompRingHomComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalMultiplicationPullbackThetaEmbeddingStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.EmbField

theorem exists_section_spMap {K R' : Type} [Field K] [CommRing R'] (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ))
    (p : Sp K) (hp : p ∈ Set.range (spMap φ)) : ∃ ψ : R' →+* K, spMap ψ ≫ spMap φ = 𝟙 _ := by
  obtain ⟨a, -⟩ := hp
  have hsurj : Surjective (spMap φ) := ⟨fun q => ⟨a, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : IsIso (spMap φ) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hφ, hsurj⟩
  refine ⟨(Spec.preimage (inv (spMap φ))).hom, ?_⟩
  have hinv : spMap (Spec.preimage (inv (spMap φ))).hom = inv (spMap φ) := by
    simp [spMap]
  rw [hinv, IsIso.inv_hom_id]

private theorem projRep_map_of_secCoord_iff {A B σ : Type} [CommRing A] [CommRing B]
    (ψ : A →+* B) (φ : B →+* A) (hψ : spMap ψ ≫ spMap φ = 𝟙 (Sp B))
    {Z Z' : Scheme.{0}} {s : Z ⟶ Sp A} {s' : Z' ⟶ Sp B} (jz : Z' ⟶ Z) [IsIso jz]
    (hjz : jz ≫ s = s' ≫ spMap ψ) {M : LB Z} {M' : LB Z'} {th : σ → M.Sec} {th' : σ → M'.Sec}
    (hM' : M'.IsLB)
    (e : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Z') (w : σ → T),
      SecCoord M' th' y w ↔ SecCoord M th (y ≫ jz) w)
    {I : Ideal (MvPolynomial σ A)} (h : ProjRep I s M th) :
    ProjRep (I.map (MvPolynomial.map ψ)) s' M' th' := by
  obtain ⟨-, hpt, hex⟩ := h
  have hs' : s' = jz ≫ s ≫ spMap φ := by
    rw [reassoc_of% hjz, hψ, Category.comp_id]
  have hcomp : ∀ (T : Type) [CommRing T] (β : B →+* T), spMap β ≫ spMap ψ = spMap (β.comp ψ) := by
    intro T _ β
    exact (spMap_comp β ψ).symm
  have hker : ∀ (T : Type) [CommRing T] (β : B →+* T) (v : σ → T),
      (∀ F ∈ I, MvPolynomial.eval₂ (β.comp ψ) v F = 0) →
        ∀ F ∈ I.map (MvPolynomial.map ψ), MvPolynomial.eval₂ β v F = 0 := by
    intro T _ β v hv F hF
    have hle : I.map (MvPolynomial.map ψ) ≤ RingHom.ker (MvPolynomial.eval₂Hom β v) := by
      refine Ideal.map_le_iff_le_comap.2 fun G hG => ?_
      simp only [Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
      exact hv G hG
    simpa [RingHom.mem_ker] using hle hF
  refine ⟨hM', fun T _ β x v hx hc => ?_, fun T _ β v hv hI => ?_⟩
  · have hx' : (x ≫ jz) ≫ s = spMap (β.comp ψ) := by
      rw [Category.assoc, hjz, ← Category.assoc, hx, hcomp]
    obtain ⟨hspan, hzero⟩ := hpt T (β.comp ψ) (x ≫ jz) v hx' ((e T x v).1 hc)
    exact ⟨hspan, hker T β v hzero⟩
  · have hI' : ∀ F ∈ I, MvPolynomial.eval₂ (β.comp ψ) v F = 0 := by
      intro F hF
      rw [← MvPolynomial.eval₂_map]
      exact hI _ (Ideal.mem_map_of_mem _ hF)
    obtain ⟨x₀, ⟨hx₀, hc₀⟩, hu⟩ := hex T (β.comp ψ) v hv hI'
    refine ⟨x₀ ≫ inv jz, ⟨?_, ?_⟩, fun y hy => ?_⟩
    · simp only [hs', Category.assoc, IsIso.inv_hom_id_assoc]
      rw [← Category.assoc, hx₀, ← hcomp, Category.assoc, hψ, Category.comp_id]
    · exact (e T _ v).2 (by rwa [Category.assoc, IsIso.inv_hom_id, Category.comp_id])
    · have hyx : y ≫ jz = x₀ :=
        hu _ ⟨by rw [Category.assoc, hjz, ← Category.assoc, hy.1, hcomp], (e T y v).1 hy.2⟩
      rw [← hyx, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

theorem exists_emb_field : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (K : Type) [Field K] (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (w : Ix g (N' ^ 2) → K), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh (𝟙 _) w → ∃ (σ : Ix g (N' ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _)))), t.Emb m (Over.mk (𝟙 _)) σ ∧ ProjRep (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ := by
  intro hL hL2 o _ g N' J b K _ s t m w hm h2 hth
  have hLB : (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))).IsLB := by
    exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ t.isLB _ _
  obtain ⟨R', _, φ, σ, hφ, hp, hE, hP⟩ :=
    GlobalTheory.T.exists_local_multiplicationPullback_theta_embedding hL hL2 o g N' J b (Sp K) s t m K (𝟙 _) w hm h2 hth (default : PrimeSpectrum K)
  obtain ⟨ψ, hψ⟩ := exists_section_spMap φ hφ _ hp
  let h : Over.mk (𝟙 (Sp K)) ⟶ Over.mk (spMap φ ≫ 𝟙 (Sp K)) := Over.homMk (spMap ψ) (by simpa using hψ)
  have hA1 : IsAffine (Over.mk (spMap φ ≫ 𝟙 (Sp K))).left :=
    show IsAffine (Spec (CommRingCat.of R')) from inferInstance
  have hA2 : IsAffine (Over.mk (𝟙 (Sp K))).left :=
    show IsAffine (Spec (CommRingCat.of K)) from inferInstance
  obtain ⟨σ', hE', hc⟩ := GlobalTheory.emb_baseChange hL2 o g N' J b (Sp K) s t m _ _ h σ hA1 hA2 hE
  refine ⟨σ', hE', ?_⟩
  have : IsIso (spMap φ) := by
    obtain ⟨a, -⟩ := hp
    exact (isIso_iff_isOpenImmersion_and_surjective _).2
      ⟨hφ, ⟨fun q => ⟨a, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩⟩
  have : IsIso (spMap ψ ≫ spMap φ) := by rw [hψ]; infer_instance
  have : IsIso (spMap ψ) := IsIso.of_isIso_comp_right (spMap ψ) (spMap φ)
  have : IsIso ((Over.forget (Sp K)).map h) := show IsIso (spMap ψ) from inferInstance
  have : IsIso h := isIso_of_reflects_iso h (Over.forget (Sp K))
  have : IsIso (h ▷ t.A).left := show IsIso ((Over.forget (Sp K)).map (h ▷ t.A)) from inferInstance
  have hsq := (GlobalTheory.EmbPull.isPullback_whisker t.A h).w
  have hP' := projRep_map_of_secCoord_iff ψ φ hψ (h ▷ t.A).left hsq hLB hc hP
  exact ideals_homogeneous.2.2 K _ _ _ _ _ _ hP'

end GlobalTheory.ZM.EmbField
end
