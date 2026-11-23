import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.BaseExt

namespace GlobalTheory.FieldSize

def toComap (F K : IntermediateField ℚ ℂ) (h : F ≤ K) : F →+* (F.comap K.val : IntermediateField ℚ K) :=
  (IntermediateField.inclusion h : F →+* K).codRestrict (F.comap K.val) fun x => x.2

theorem image_toComap {E : Type} [Field E] (F K : IntermediateField ℚ ℂ) (h : F ≤ K) (𝔞 : Ideal (𝓞 E))
    (c : E → ℂ) (e : E → K) (he : ∀ a, (e a : ℂ) = c a) :
    extend (toComap F K h) (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = c (a : E)}) =
      Submodule.span (𝓞 (F.comap K.val : IntermediateField ℚ K))
        {x : (F.comap K.val : IntermediateField ℚ K) | ∃ a ∈ 𝔞, (x : K) = e (a : E)} := by
  rw [extend_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, hy⟩, rfl⟩
    exact ⟨a, ha, Subtype.ext (hy.trans (he _).symm)⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨⟨(x.1 : ℂ), x.2⟩, ⟨a, ha, (congrArg Subtype.val hx).trans (he _)⟩, rfl⟩

theorem exists_base_of_rich : ∀ (P : Pre) (F : IntermediateField ℚ ℂ), FiniteDimensional ℚ F → Rich P F →
    ∀ S₁ S₂ : Finset ℂ, (∀ z ∈ S₁, IsAlgebraic ℚ z) → (∀ z ∈ S₂, IsAlgebraic ℚ z) →
    ∃ B : Base, B.toPre = P ∧ (∀ z, z ∈ F ↔ ∃ x ∈ B.Ks, B.embLL x = z) ∧
      (∀ z ∈ S₁, ∃ x ∈ B.LL0, B.embLL x = z) ∧ ∀ z ∈ S₂, ∃ x : B.LL, B.embLL x = z := by
  classical
  intro B F hF hr S₁ S₂ h₁ h₂
  have : NumberField F := {}
  obtain ⟨SF, hSF, hE⟩ := exists_gens F
  let A : Finset ℕ := {B.ramOrder} ∪ Finset.univ.image B.T
  let SR : Finset ℂ := A.image fun N : ℕ => Complex.exp (2 * Real.pi * Complex.I / N)
  obtain ⟨K, hfd, hKgal, hS, -, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable
    (S₁ ∪ S₂ ∪ SF ∪ SR) (by
      intro z hz
      simp only [Finset.mem_union] at hz
      rcases hz with ((hz | hz) | hz) | hz
      exacts [h₁ z hz, h₂ z hz, hSF z hz, by
        obtain ⟨N, -, rfl⟩ := Finset.mem_image.1 hz
        exact isAlgebraic_exp N])
  simp only [Finset.mem_union] at hS
  have hFK : F ≤ K := fun z hz => hE K (fun z hz => hS z (.inl (.inr hz))) F.val ⟨z, hz⟩
  have hEK : ∀ x, B.host.φ₀ x ∈ K := fun x => hFK (hr.host x)
  have hR : ∀ N ∈ A, Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K := fun N hN => by
    have hz : Complex.exp (2 * Real.pi * Complex.I / N) ∈ SR := Finset.mem_image.2 ⟨N, hN, rfl⟩
    exact hS _ (.inr hz)
  have : NumberField K := {}
  let f := toComap F K hFK
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
            E_le_Ks := fun x => hr.host x
            roots_Ks := ?_
            roots_Ks' := ?_
            capit := ?_
            kPsi := ?_
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := ⟨⟨_, hR B.ramOrder (by simp [A])⟩, trivial, rfl⟩
            roots_LL := fun u => ⟨⟨_, hR (B.T u) (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (Finset.mem_univ u)))⟩, rfl⟩ }, rfl, ?_, ?_, ?_⟩
  · intro N hN
    have h := hr.roots N (List.mem_append_left [_, _, _, _, _] hN)
    exact ⟨⟨_, hFK h⟩, h, rfl⟩
  · intro N hN
    have h := hr.roots N (List.mem_append_right [_, _, _, _, _] (List.mem_append_left [_, _] hN))
    exact ⟨⟨_, hFK h⟩, h, rfl⟩
  · intro 𝔞
    obtain ⟨β, hsp⟩ := hr.capit 𝔞
    refine ⟨f β, ?_⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton] at h
    exact h.trans (image_toComap F K hFK 𝔞 B.host.φ₀ (B.host.φ₀.codRestrict K hEK) fun _ => rfl)
  · intro j hj1 hj 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := hr.kPsi j hj1 hj 𝔞 h𝔞
    refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton, map_prod] at h
    rw [h]
    refine Finset.prod_congr rfl fun g _ => ?_
    have e1 := image_toComap F K hFK 𝔞 (fun a => B.host.φ₀ (B.host.sigmaOf g a))
      (fun a => B.host.φ₀.codRestrict K hEK (B.host.sigmaOf g a)) fun _ => rfl
    have e2 := image_toComap F K hFK 𝔞 (fun a => B.host.φ₀ (B.host.sigmaOf g (B.host.conj a)))
      (fun a => B.host.φ₀.codRestrict K hEK (B.host.sigmaOf g (B.host.conj a))) fun _ => rfl
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)
  · intro z
    refine ⟨fun hz => ⟨⟨z, hFK hz⟩, hz, rfl⟩, ?_⟩
    rintro ⟨x, hx, rfl⟩
    exact hx
  · exact fun z hz => ⟨⟨z, hS z (.inl (.inl (.inl hz)))⟩, trivial, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (.inl (.inl (.inr hz)))⟩, rfl⟩

end GlobalTheory.FieldSize

end
