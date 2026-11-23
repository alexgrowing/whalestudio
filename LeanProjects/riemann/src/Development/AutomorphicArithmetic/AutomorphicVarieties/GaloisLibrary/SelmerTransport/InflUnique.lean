import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

set_option maxHeartbeats 200000 in
theorem UpperTheory.V.Base.inflUnique :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ),
      (∀ x, ∃ y, Infl k D e x y) ∧ ∀ x x' y y', Infl k D e x y → Infl k D e x' y' → (x = x' ↔ y = y') := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e
  obtain ⟨hemb, -, -⟩ := galEmbTop k E Ω
  let ψ : G E Ω →* galOf k E Ω := (galEmb k E Ω).codRestrict _ (galEmb_mem k E Ω)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨τ, hτ⟩
    refine ⟨AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun x => hτ x), ?_⟩
    apply Subtype.ext
    ext x
    rfl
  let Ψ : G E Ω ≃* galOf k E Ω :=
    MulEquiv.ofBijective ψ ⟨fun a b h => hemb.injective (congrArg Subtype.val h), hsurj⟩
  have hΨ : ∀ σ, Ψ σ = ⟨galEmb k E Ω σ, galEmb_mem k E Ω σ⟩ := fun _ => rfl
  have hcont : Continuous (fun u : galOf k E Ω => Ψ.symm u) := by
    rw [hemb.continuous_iff]
    have hc : (galEmb k E Ω) ∘ (fun u : galOf k E Ω => Ψ.symm u) = Subtype.val := by
      funext u
      show ((Ψ (Ψ.symm u) : galOf k E Ω) : G k Ω) = u
      rw [Ψ.apply_symm_apply]
    rw [hc]
    exact continuous_subtype_val
  have hEk : ∀ σ : G E Ω, LDataCardLeFinrank.qzG k Ω l e (galEmb k E Ω σ) = LDataCardLeFinrank.qzG E Ω l e σ := by
    intro σ
    have hχ : (cycZ k Ω l ^ (-e)).comp (galEmb k E Ω) = cycZ E Ω l ^ (-e) := by
      refine MonoidHom.ext fun τ => ?_
      rw [MonoidHom.comp_apply]
      simp only [MonoidHom.zpow_apply]
      rfl
    show scalRep (QZ l) (cycZ k Ω l ^ (-e)) (galEmb k E Ω σ) = scalRep (QZ l) (cycZ E Ω l ^ (-e)) σ
    rw [← hχ]
    rfl
  have hrep : ∀ σ : G E Ω, LDataCardLeFinrank.qzG k Ω l e (galEmb k E Ω σ) = qzTw D e (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) σ) := by
    intro σ
    have h := DFunLike.congr_fun (LDataCardLeFinrank.qzTw_comp_toGS D e) σ
    rw [MonoidHom.comp_apply] at h
    rw [hEk]
    exact h.symm
  have hu : ∀ u : galOf k E Ω, (u : G k Ω) = galEmb k E Ω (Ψ.symm u) := by
    intro u
    conv_lhs => rw [← Ψ.apply_symm_apply u]
    rfl
  have hTs : Function.Surjective (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))) :=
    QuotientGroup.mk'_surjective _
  constructor
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    let f : galOf k E Ω → QZ l := fun u => (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm u))
    have hf : f ∈ Z1U (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω) := by
      refine ⟨z.2.1.comp ((continuous_toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))).comp hcont), ?_⟩
      intro u v
      show (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm (u * v))) =
        (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm u)) +
          ((LDataCardLeFinrank.qzG k Ω l e).comp (galOf k E Ω).subtype u) ((z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm v)))
      rw [map_mul, map_mul, z.2.2, MonoidHom.comp_apply, Subgroup.coe_subtype, hu u, hrep]
    refine ⟨Submodule.Quotient.mk ⟨f, hf⟩, z, ⟨f, hf⟩, rfl, rfl, ?_⟩
    intro σ
    show (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm ⟨galEmb k E Ω σ, _⟩)) = _
    rw [← hΨ, Ψ.symm_apply_apply]
  · rintro x x' y y' ⟨z1, w1, rfl, rfl, h1⟩ ⟨z2, w2, rfl, rfl, h2⟩
    rw [mk_eq_mk, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
    apply exists_congr
    intro m
    constructor
    · intro h u
      obtain ⟨σ, rfl⟩ := Ψ.surjective u
      have h3 := h (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) σ)
      rw [Submodule.coe_sub, Pi.sub_apply] at h3
      rw [hΨ, h1, h2, h3]
      exact congrArg (fun T => T m - m) (hrep σ).symm
    · intro h g
      obtain ⟨σ, rfl⟩ := hTs g
      have h3 := h (Ψ σ)
      rw [hΨ, h1, h2] at h3
      rw [Submodule.coe_sub, Pi.sub_apply, h3]
      exact congrArg (fun T => T m - m) (hrep σ)
