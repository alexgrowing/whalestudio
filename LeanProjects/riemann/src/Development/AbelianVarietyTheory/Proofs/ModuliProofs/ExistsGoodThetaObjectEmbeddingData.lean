import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapCompRingHomComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionCoordsThetaTimesRoots
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddedAbelianVarietyCutOutByTorsionForms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEmbeddingSectionsOverFieldStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.GoodFibre

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp [spMap, Sp]

theorem exists_retraction {K R' : Type} [Field K] [CommRing R'] (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ))
    (p : Sp K) (hp : p ∈ Set.range (spMap φ)) : ∃ ψ : R' →+* K, ψ.comp φ = RingHom.id K := by
  have hsurj : Function.Surjective (spMap φ) := by
    intro q
    obtain ⟨r, hr⟩ := hp
    exact ⟨r, Subsingleton.elim _ _⟩
  haveI : Surjective (spMap φ) := ⟨hsurj⟩
  haveI : IsIso (spMap φ) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨hφ, inferInstance⟩
  obtain ⟨ψ', hψ'⟩ := Spec.map_surjective (inv (spMap φ))
  refine ⟨ψ'.hom, ?_⟩
  have key : Spec.map (CommRingCat.ofHom φ ≫ ψ') = Spec.map (𝟙 _) := by
    rw [Spec.map_comp, hψ', Spec.map_id]
    exact IsIso.inv_hom_id (spMap φ)
  have := Spec.map_injective key
  ext a
  exact congrArg (fun f => f.hom a) this

theorem secCoord_of_local {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} {th : I → M.Sec} {K R' : Type} [Field K]
    [CommRing R'] {y : Sp K ⟶ X} {v : I → K} (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ)) (p : Sp K)
    (hp : p ∈ Set.range (spMap φ)) (h : SecCoord M th (spMap φ ≫ y) (fun i => φ (v i))) : SecCoord M th y v := by
  obtain ⟨ψ, hψ⟩ := exists_retraction φ hφ p hp
  have h' := GlobalTheory.ZM.Coord.baseChange h ψ
  have e1 : spMap ψ ≫ spMap φ ≫ y = y := by
    rw [← Category.assoc, GlobalTheory.ZM.spMap_comp_ringHom_comp, hψ, spMap_id, Category.id_comp]
  have e2 : (fun i => ψ (φ (v i))) = v :=
    funext fun i => congrArg (fun f : K →+* K => f (v i)) hψ
  rw [e1, e2] at h'
  exact h'

theorem span_theta (l1 : Out.Laws) (l2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (n : ℕ) (v : Ix g (N' ^ 2) → K)
    (h2 : 2 ≤ n) (hn : n ∣ N') (hth : t.HasTh (𝟙 _) v) : Ideal.span (Set.range v) = ⊤ := by
  by_contra hne
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
  have hc := GlobalTheory.coset_of_hasTh l1 l2 o g N' J b (Sp K) s t n K (𝟙 _) v q h2 hn hth hq.isPrime
  unfold Coset at hc
  obtain ⟨c, hc⟩ := hc 0
  exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))

theorem exists_fibData : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), ∃ (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R) (Hh : Type) (_ : Finite Hh) (hh : Hh → Ix g ((n ^ j) ^ 2)) (Q : Polynomial ℚ) (d : ℕ), FibData b Mat κ β v (n ^ 2) p hh Q d := by
  intro l1 l2 g J _ Mat κ n hn hodd
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.cutBy_embedded_abelian l1 l2 g J Mat κ n hn hodd
  refine ⟨max j₁ 4, fun j hj o _ b R _ β v => ?_⟩
  have hjc : j₁ ≤ j := le_of_max_le_left hj
  have hj4 : 4 ≤ j := le_of_max_le_right hj
  have hoddN : Odd (n ^ j) := hodd.pow
  have hdvd : n ^ 2 ∣ n ^ j := pow_dvd_pow n (by omega)
  have hdvd2 : (n ^ 2) ^ 2 ∣ n ^ j := by
    rw [← pow_mul]
    exact pow_dvd_pow n (by omega)
  have htwo : 2 ≤ n ^ 2 := le_trans hn.two_le (Nat.le_self_pow (by norm_num) n)
  obtain ⟨e, idx, hto⟩ := GlobalTheory.torsion_secCoord l1 l2 g (n ^ 2) (n ^ j) hoddN hdvd2
  obtain ⟨Hh, hfin, hh, Q, d, hcut⟩ := hj₁ j hjc o b
  refine ⟨fun h a => β (b.ζ ^ e a h : oˣ) * v (idx a h), Hh, hfin, hh, Q, d, ?_⟩
  intro K _ _ x s t hgood
  obtain ⟨hs, -, hth⟩ := hgood
  rw [GlobalTheory.ZM.spMap_comp_ringHom_comp] at hs
  subst hs
  obtain ⟨σ, hemb, hproj⟩ := GlobalTheory.T.exists_embeddingSections_over_field l1 l2 o g (n ^ j) J b K _ t (n ^ 2) (fun a => x (v a)) hdvd2 htwo hth
  have hLB := (GlobalTheory.T.thetaSections_veryAmple_periodic l1 l2 o g (n ^ j) J b K (x.comp β) t (n ^ 2) σ hoddN hdvd htwo hemb).2.1
  have hspan : Ideal.span (Set.range fun a => x (v a)) = ⊤ :=
    span_theta l1 l2 t n (fun a => x (v a)) hn.two_le (dvd_pow_self n (by omega)) hth
  have hsec : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left
      (fun a => x (β (b.ζ ^ e a h : oˣ) * v (idx a h))) := by
    intro h
    have hy : ((Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ t.lab h)
        = t.lab h := by
      ext
      simp
    obtain ⟨R', _, φ, hφ, hp, hc⟩ := hto o J b (Sp K) _ t K (x.comp β) (𝟙 _) (fun a => x (v a)) σ
      (Category.id_comp _) hth hspan hemb h _ (by rw [hy]) (IsLocalRing.closedPoint K)
    have key := secCoord_of_local hLB φ hφ _ hp hc
    have hv : (fun a => x (β (b.ζ ^ e a h : oˣ) * v (idx a h)))
        = (fun a => (x.comp β) (b.ζ ^ e a h : oˣ) * x (v (idx a h))) := by
      funext a
      simp
    rw [hv]
    exact key
  refine ⟨σ, _, hemb, hproj, ideals_homogeneous.1 _ _ _ _ _ _ σ _ hLB, ?_, hsec⟩
  exact hcut K (x.comp β) t σ _ hemb fun h => hsec (hh h)

end GlobalTheory.ZM.GoodFibre
end
