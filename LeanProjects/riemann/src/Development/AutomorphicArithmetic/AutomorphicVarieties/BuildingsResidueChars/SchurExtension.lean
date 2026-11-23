import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchurScalar
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem irr_nontrivial {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) : Nontrivial (Fin n → k) := by
  obtain ⟨hne, -, -⟩ := hirr
  by_contra hc
  rw [not_nontrivial_iff_subsingleton] at hc
  exact hne (Subsingleton.elim _ _)

private theorem smul_one_inj {k : Type} [Field k] {n : ℕ} [Nontrivial (Fin n → k)] (a b : k)
    (h : a • (1 : Matrix (Fin n) (Fin n) k) = b • 1) : a = b := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → k)
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) k => M.mulVec v) h
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec] at h2
  exact smul_left_injective k hv h2

private theorem schur_scalar {Γ k : Type} [Group Γ] [Field k] [IsAlgClosed k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) (g : GL (Fin n) k) (hg : ∀ s, r s * g = g * r s) :
    ∃ c : kˣ, (g : Matrix (Fin n) (Fin n) k) = (c : k) • 1 :=
  _root_.UpperTheory.Reformulated.B.Qi17.schur_scalar r hirr g hg

theorem UpperTheory.schur_extension :
    UpperTheory.V.Af.Sol.SchurExt := by
  intro Γ Γ' k _ _ _ _ n r r₁ φ hN hirr hiso
  obtain ⟨g, hg⟩ := hiso
  have hnt := irr_nontrivial _ hirr
  simp only [MonoidHom.comp_apply] at hg
  have hcomm : ∀ s t, (r.comp φ) t * (r s * (g * r₁ s * g⁻¹)⁻¹) =
      (r s * (g * r₁ s * g⁻¹)⁻¹) * (r.comp φ) t := by
    intro s t
    obtain ⟨u, hu⟩ := hN.conj_mem' (φ t) ⟨t, rfl⟩ s
    have h1 := hg u
    rw [hu] at h1
    simp only [map_mul, map_inv] at h1
    have h2 : r (φ t) * r s = r s * ((r s)⁻¹ * r (φ t) * r s) := by group
    rw [MonoidHom.comp_apply, ← mul_assoc, h2, h1, hg t]
    group
  choose c hc using fun s => schur_scalar _ hirr _ (hcomm s)
  have hr : ∀ s, (r s : Matrix (Fin n) (Fin n) k) =
      (c s : k) • ((g * r₁ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    intro s
    have h1 : r s = (r s * (g * r₁ s * g⁻¹)⁻¹) * (g * r₁ s * g⁻¹) := by group
    rw [h1, Units.val_mul, hc s, Matrix.smul_mul, Matrix.one_mul]
  have huniq : ∀ s (a : kˣ), (r s : Matrix (Fin n) (Fin n) k) =
      (a : k) • ((g * r₁ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) → c s = a := by
    intro s a ha
    apply Units.ext
    apply smul_one_inj (n := n)
    rw [← hc s, Units.val_mul, ha, Matrix.smul_mul, Units.mul_inv]
  have hmul : ∀ s t, c (s * t) = c s * c t := by
    intro s t
    apply huniq
    have h1 : g * r₁ (s * t) * g⁻¹ = (g * r₁ s * g⁻¹) * (g * r₁ t * g⁻¹) := by
      rw [map_mul]; group
    rw [map_mul r, Units.val_mul, hr s, hr t, h1, Units.val_mul (g * r₁ s * g⁻¹), Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Units.val_mul (c s)]
  refine ⟨MonoidHom.mk' c hmul, ?_, g, ?_⟩
  · ext t
    have : c (φ t) = 1 := huniq _ _ (by rw [← hg t]; simp)
    simp [this]
  · intro s
    apply Units.ext
    rw [hr s]
    simp only [Units.val_mul, tw_val, MonoidHom.mk'_apply, Matrix.smul_mul, Matrix.mul_smul]
