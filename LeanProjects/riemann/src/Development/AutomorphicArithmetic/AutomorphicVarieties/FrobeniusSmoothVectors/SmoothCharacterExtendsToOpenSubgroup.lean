import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemPowSmulLe

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.smoothCharacter_extends_to_open_subgroup :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n) (Q : Type) [CommRing Q] [Algebra (ResidueField O) Q] (ξ : S.A →+* Q), S.FPt ξ → (S.u.map ξ).IsBar (algebraMap (ResidueField O) Q) ∧ (∀ i j, IsLocallyConstant fun g => (S.u.map ξ).r g i j) ∧ ∀ ξ' : S.A →+* Q, S.FPt ξ' → (∀ g i j, ξ' (S.u.r g i j) = ξ (S.u.r g i j)) → ξ' = ξ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S Q _ _ ξ hξ
  have hkey : ∀ ζ : S.A →+* Q, S.FPt ζ → ∀ (b : S.B) (c : O), b - algebraMap O S.B c ∈ S.mB →
      ζ (S.inc b) = algebraMap (ResidueField O) Q (residue O c) := by
    intro ζ hζ b c hbc
    have h1 : S.inc (b - algebraMap O S.B c) ∈ S.x0 := Ideal.mem_map_of_mem _ hbc
    have h2 := hζ.x0 h1
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, map_sub, sub_eq_zero] at h2
    rw [h2, hζ.alg]
  have hres : ∀ (b : S.B) (y : ResidueField O), res O S.R b.val = y →
      ∀ ζ : S.A →+* Q, S.FPt ζ → ζ (S.inc b) = algebraMap (ResidueField O) Q y := by
    intro b y hb ζ hζ
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective y
    apply hkey ζ hζ b c
    show (b - algebraMap O S.B c).val ∈ maximalIdeal S.R
    rw [← res_eq_zero_iff O S.R]
    simp [hb]
  refine ⟨⟨fun g i => ?_, fun v i g => ?_⟩, fun i j => ?_, fun ξ' hξ' hag => ?_⟩
  · have h := S.lift.2.1.1 g i
    exact hres (S.aB g i) _ (by simpa [NRep.map, Space.aB] using h) ξ hξ
  · have h := S.lift.2.1.2 v i g
    exact hres (S.ψB v i g) _ (by simpa [NRep.map, Space.ψB] using h) ξ hξ
  · have hc := ((cont_u hF hn S).1.1 i j) 1
    let f := Ideal.Quotient.lift (S.x0 ^ 1) ξ (fun a ha => hξ.x0 (by rwa [pow_one] at ha))
    convert hc.comp f using 1
    funext g
    rfl
  · apply RingHom.ext
    rintro ⟨x, hx⟩
    refine Algebra.adjoin_induction (p := fun x hx => ξ' ⟨x, hx⟩ = ξ ⟨x, hx⟩) ?_ ?_ ?_ ?_ hx
    · rintro x (hxB | ⟨g, i, j, rfl⟩)
      · obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) x
        have hc' : (⟨x, hxB⟩ : S.B) - algebraMap O S.B c ∈ S.mB := hc
        show ξ' (S.inc ⟨x, hxB⟩) = ξ (S.inc ⟨x, hxB⟩)
        rw [hkey ξ' hξ' _ c hc', hkey ξ hξ _ c hc']
      · exact hag g i j
    · intro r
      show ξ' (algebraMap O S.A r) = ξ (algebraMap O S.A r)
      rw [hξ'.alg, hξ.alg]
    · intro x y hx hy h1 h2
      show ξ' ((⟨x, hx⟩ : S.A) + ⟨y, hy⟩) = ξ ((⟨x, hx⟩ : S.A) + ⟨y, hy⟩)
      rw [map_add, map_add, h1, h2]
    · intro x y hx hy h1 h2
      show ξ' ((⟨x, hx⟩ : S.A) * ⟨y, hy⟩) = ξ ((⟨x, hx⟩ : S.A) * ⟨y, hy⟩)
      rw [map_mul, map_mul, h1, h2]
