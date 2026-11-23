import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PointPropertyEqSizeFree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassNumberDvdHstar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeNormGeneratorOfKummerFieldLeStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.Mem.BaseExt
  GlobalTheory.Mem.FieldsEx
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KsBase

theorem span_eq_of_isPrincipal {E : Type} [Field E] (φ : E →+* ℂ) (F : IntermediateField ℚ ℂ) (hF : ∀ x, φ x ∈ F)
    (𝔞 : Ideal (𝓞 E)) (h : (𝔞.map (RingOfIntegers.mapRingHom (φ.codRestrict F hF))).IsPrincipal) :
    ∃ β : F, Submodule.span (𝓞 F) {β} = Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = φ (a : E)} := by
  obtain ⟨b, hb⟩ := h
  refine ⟨(b : F), ?_⟩
  have h := congrArg (Submodule.map (Algebra.linearMap (𝓞 F) F)) hb
  rw [Submodule.map_span, Set.image_singleton, Ideal.map, Ideal.span, Submodule.map_span, Set.image_image] at h
  refine h.symm.trans (congrArg _ ?_)
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨a, ha, Subtype.ext hx.symm⟩

theorem exists_base_of_contents (B : Pre) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F]
    (hEF : ∀ x, B.host.φ₀ x ∈ F) (hr : rootsField B ≤ F) (hp : rootOne B.host.pde ∈ F)
    (hp' : rootOne B.host.pde' ∈ F) (hh : rootOne (classNumber B.host.E) ∈ F)
    (hc : ∀ 𝔞 : Ideal (𝓞 B.host.E), ∃ β : F,
      Submodule.span (𝓞 F) {β} = Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = B.host.φ₀ (a : B.host.E)})
    (hk : ∀ j, 1 ≤ j → j ≤ B.R.m → ∀ 𝔞 : Ideal (𝓞 B.host.E), 𝔞 ≠ ⊥ → ∃ β : F, β ≠ 0 ∧
      Submodule.span (𝓞 F) {β} = ∏ g : Tau B.R,
        (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = B.host.φ₀ (B.host.sigmaOf g (a : B.host.E))} ^
            (B.R.sigW j).1 *
          Submodule.span (𝓞 F)
            {x : F | ∃ a ∈ 𝔞, (x : ℂ) = B.host.φ₀ (B.host.sigmaOf g (B.host.conj (a : B.host.E)))} ^
            (B.R.sigW j).2) ∧
      ∀ σ : F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((B.R.sigW j).1 + (B.R.sigW j).2)) :
    ∃ B' : Base, B'.toPre = B ∧ B'.KsC = F := by
  classical
  obtain ⟨SF, hSF, hF⟩ := exists_gens_le F
  let A : Finset ℕ := {B.ramOrder} ∪ Finset.univ.image B.T
  let SR : Finset ℂ := A.image fun N : ℕ => Complex.exp (2 * Real.pi * Complex.I / N)
  obtain ⟨K, hfd, hKgal, hS, -, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable (SF ∪ SR) (by
      intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      exacts [hSF z hz, by
        obtain ⟨N, -, rfl⟩ := Finset.mem_image.1 hz
        exact isAlgebraic_exp N])
  simp only [Finset.mem_union] at hS
  have hFK : F ≤ K := hF K fun z hz => hS z (.inl hz)
  have hEK : ∀ x, B.host.φ₀ x ∈ K := fun x => hFK (hEF x)
  have hR : ∀ N ∈ A, Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K := fun N hN => by
    have hz : Complex.exp (2 * Real.pi * Complex.I / N) ∈ SR := Finset.mem_image.2 ⟨N, hN, rfl⟩
    exact hS _ (.inr hz)
  have : NumberField K := {}
  simp only [rootsField, sup_le_iff, cycField_le_iff] at hr
  obtain ⟨⟨⟨⟨hr1, hr2⟩, hr3⟩, hr4⟩, hr5⟩ := hr
  let f := toComap hFK
  refine ⟨{ toPre := B
            LL := K
            starLL := starOf K hconj
            embLL := K.val
            starLL_cx := fun _ => rfl
            embE := B.host.φ₀.codRestrict K hEK
            embE_φ₀ := rfl
            LL0 := ⊤
            coeffGaloisSubfield_isGalois := IsGalois.of_algEquiv IntermediateField.topEquiv.symm
            Ks := F.comap K.val
            Ks_le := le_top
            E_le_Ks := hEF
            roots_Ks := ?_
            roots_Ks' := ?_
            capit := ?_
            kPsi := ?_
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := ⟨⟨_, hR B.ramOrder (by simp [A])⟩, trivial, rfl⟩
            roots_LL := fun u => ⟨⟨_, hR (B.T u) (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (Finset.mem_univ u)))⟩, rfl⟩ }, rfl, IntermediateField.ext fun z => ?_⟩
  · intro N hN
    have h : rootOne N ∈ F := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
      rcases hN with rfl | rfl | rfl | rfl | rfl <;> assumption
    exact ⟨⟨_, hFK h⟩, h, rfl⟩
  · intro N hN
    have h : rootOne N ∈ F := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
      rcases hN with rfl | rfl | rfl <;> assumption
    exact ⟨⟨_, hFK h⟩, h, rfl⟩
  · intro 𝔞
    obtain ⟨β, hsp⟩ := hc 𝔞
    refine ⟨f β, ?_⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton] at h
    exact h.trans (image_comap hFK 𝔞 B.host.φ₀ (B.host.φ₀.codRestrict K hEK) fun _ => rfl)
  · intro j hj1 hj 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := hk j hj1 hj 𝔞 h𝔞
    refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton, map_prod] at h
    refine h.trans (Finset.prod_congr rfl fun g _ => ?_)
    have e1 := image_comap hFK 𝔞 (B.host.φ₀.comp (B.host.sigmaOf g : B.host.E →+* B.host.E))
      (fun a => B.host.φ₀.codRestrict K hEK (B.host.sigmaOf g a)) fun _ => rfl
    have e2 := image_comap hFK 𝔞 ((B.host.φ₀.comp (B.host.sigmaOf g : B.host.E →+* B.host.E)).comp
        (B.host.conj : B.host.E →+* B.host.E))
      (fun a => B.host.φ₀.codRestrict K hEK (B.host.sigmaOf g (B.host.conj a))) fun _ => rfl
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)
  · constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · exact fun hz => ⟨⟨z, hFK hz⟩, hz, rfl⟩

theorem exists_base_listField (hR : RayField) (hP : PrincipalIdealSt) (P : Pre) (f : GlobalTheory.Mem.Top.Fr P)
    (δ : FieldDat P) : listField δ f ≤ δ.Om ∧ ∃ B : Base, B.toPre = P ∧ B.KsC = listField δ f := by
  have hO : listField δ f ≤ δ.Om := listField_le_Om δ f
  have := host_cplx P
  have := finite_Om δ
  have : FiniteDimensional ℚ (listField δ f) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hO).toLinearMap (IntermediateField.inclusion_injective hO)
  obtain ⟨h1, -, h3, h4, -, h6⟩ := (listField_le_iff δ f).1 le_rfl
  have hm : 1 ≤ P.R.m := le_trans one_le_two P.R.two_le_m
  refine ⟨hO, exists_base_of_contents P _ ((imField_le_iff _).1 h1) h4
    (h3 (rootOne_mem_ray _ (modulus_ne_zero P) (pde_dvd P) δ.isRay))
    (h3 (rootOne_mem_ray _ (modulus_ne_zero P) (pde'_dvd P) δ.isRay))
    (cycField_le_iff.1 ((le_sup_right.trans le_sup_left).trans (h6 1 le_rfl hm)))
    (fun 𝔞 => span_eq_of_isPrincipal _ _ _ 𝔞
      (hP.of_isRayFieldIn hR (natIdeal_ne_bot (modulus_ne_zero P)) δ.isRay h3 𝔞))
    fun j hj hj' => GlobalTheory.T.cmTypeNorm_generator_of_kummerField_le P δ _ j (h6 j hj hj')⟩

end GlobalTheory.Mem.KsBase

end
