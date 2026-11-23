import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisSubfieldConjStable

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.BaseEnl

open GlobalTheory.Mem.BaseExt

section map

variable {L L' : Type} [Field L] [Field L'] [CharZero L] [CharZero L'] (ι : L →ₐ[ℚ] L')
  (K : IntermediateField ℚ L)

def toMap : K →+* K.map ι := (K.equivMap ι).toRingEquiv.toRingHom

theorem coe_toMap (x : K) : (toMap ι K x : L') = ι x := rfl

theorem toMap_surj : Function.Surjective (toMap ι K) := (K.equivMap ι).surjective

theorem image_map {E : Type} [Field E] (𝔞 : Ideal (𝓞 E)) (e : E → L) :
    extend (toMap ι K) (Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : L) = e (a : E)}) =
      Submodule.span (𝓞 (K.map ι)) {x : K.map ι | ∃ a ∈ 𝔞, (x : L') = ι (e (a : E))} := by
  rw [extend_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, hy⟩, rfl⟩
    exact ⟨a, ha, by rw [coe_toMap, hy]⟩
  · rintro ⟨a, ha, hx⟩
    obtain ⟨y, rfl⟩ := toMap_surj ι K x
    exact ⟨y, ⟨a, ha, ι.injective hx⟩, rfl⟩

end map

theorem exists_enl : ∀ (B : Base) (S : Finset ℂ), (∀ z ∈ S, IsAlgebraic ℚ z) →
    ∃ B' : Base, Enl B B' ∧ ∀ z ∈ S, ∃ x : B'.LL, B'.embLL x = z := by
  classical
  intro B S h
  obtain ⟨SE, hSE, hE⟩ := exists_gens B.LL
  obtain ⟨K, hfd, hKgal, hS, -, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable (S ∪ SE) (by
    intro z hz
    rcases Finset.mem_union.1 hz with hz | hz
    exacts [h z hz, hSE z hz])
  have hEK := hE K (fun z hz => hS z (Finset.mem_union_right _ hz)) B.embLL
  have : NumberField K := {}
  let ι : B.LL →ₐ[ℚ] K := (B.embLL.codRestrict K hEK).toRatAlgHom
  have hι : ∀ x, K.val (ι x) = B.embLL x := fun _ => rfl
  have tr : ∀ (F : IntermediateField ℚ B.LL) (w : ℂ), (∃ z ∈ F, B.embLL z = w) →
      ∃ z ∈ F.map ι, K.val z = w := by
    rintro F w ⟨z, hz, rfl⟩
    exact ⟨ι z, ⟨z, hz, rfl⟩, rfl⟩
  have im : ∀ F : IntermediateField ℚ B.LL,
      (K.val : K →+* ℂ) '' (F.map ι : Set K) = B.embLL '' (F : Set B.LL) := by
    intro F
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
    · exact tr F w
  have hg0 := B.coeffGaloisSubfield_isGalois
  let f := toMap ι B.Ks
  refine ⟨{ toPre := B.toPre
            LL := K
            starLL := starOf K hconj
            embLL := K.val
            starLL_cx := fun _ => rfl
            embE := (ι : B.LL →+* K).comp B.embE
            embE_φ₀ := by rw [← B.embE_φ₀]; rfl
            LL0 := B.LL0.map ι
            coeffGaloisSubfield_isGalois := @IsGalois.of_algEquiv ℚ B.LL0 _ _ (B.LL0.map ι) _ _ _ hg0 (B.LL0.equivMap ι)
            Ks := B.Ks.map ι
            Ks_le := IntermediateField.map_mono ι B.Ks_le
            E_le_Ks := fun x => ⟨B.embE x, B.E_le_Ks x, rfl⟩
            roots_Ks := fun N hN => tr _ _ (B.roots_Ks N hN)
            roots_Ks' := fun N hN => tr _ _ (B.roots_Ks' N hN)
            capit := ?_
            kPsi := ?_
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := tr _ _ B.rootOfUnity_eightQ_mem_coeffGaloisSubfield
            roots_LL := fun u => ?_ }, ⟨rfl, im _, im _, ?_⟩, ?_⟩
  · intro 𝔞
    obtain ⟨β, hsp⟩ := B.capit 𝔞
    refine ⟨f β, ?_⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton] at h
    exact h.trans (image_map ι B.Ks 𝔞 B.embE)
  · intro j hj1 hj 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := B.kPsi j hj1 hj 𝔞 h𝔞
    refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton, map_prod] at h
    rw [h]
    refine Finset.prod_congr rfl fun g _ => ?_
    have e1 := image_map ι B.Ks 𝔞 (fun a => B.embE (B.host.sigmaOf g a))
    have e2 := image_map ι B.Ks 𝔞 (fun a => B.embE (B.host.sigmaOf g (B.host.conj a)))
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)
  · obtain ⟨z, hz⟩ := B.roots_LL u
    exact ⟨ι z, hz⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨ι z, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (Finset.mem_union_left _ hz)⟩, rfl⟩

end GlobalTheory.Mem.BaseEnl

end
