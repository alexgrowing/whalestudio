import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.HermitianHalfLattice.ConjHSymmApply
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivGen
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker.TI

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem equiv_osmulW (φ : W ≃ₗ[E] W) (r : 𝓞 E) (x : W) : φ (r • x) = r • φ x := by
  rw [← algebraMap_smul E r x, map_smul, algebraMap_smul]

theorem mem_localization_equiv (φ : W ≃ₗ[E] W) {M M' : Submodule (𝓞 E) W} (hM : ∀ y, y ∈ M' ↔ φ.symm y ∈ M)
    (Q : HeightOneSpectrum (𝓞 E)) (y : W) : y ∈ localization₂ Q.asIdeal M' ↔ φ.symm y ∈ localization₂ Q.asIdeal M := by
  rw [mem_locP, mem_locP]
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [← equiv_osmulW]
    exact (hM _).1 h
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, (hM _).2 ?_⟩
    rw [equiv_osmulW]
    exact h

theorem mem_twO_equiv (φ : W ≃ₗ[E] W) {M M' : Submodule (𝓞 E) W} (hM : ∀ y, y ∈ M' ↔ φ.symm y ∈ M)
    (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (y : W) : y ∈ twist₂ M' c e ↔ φ.symm y ∈ twist₂ M c e := by
  rw [mem_twO, mem_twO]
  refine forall_congr' fun Q => ?_
  rw [mem_localization_equiv φ hM Q, map_smul]

theorem mem_halfAO_equiv {a b : ℕ} (φ : HomE E a b ≃ₗ[E] HomE E a b) {M M' : Submodule (𝓞 E) (HomE E a b)}
    (hM : ∀ y, y ∈ M' ↔ φ.symm y ∈ M) (SS : Finset (HeightOneSpectrum (𝓞 E))) (c : ℕ) (y : HomE E a b) :
    y ∈ halfAO SS M' c ↔ φ.symm y ∈ halfAO SS M c :=
  mem_twO_equiv φ hM c _ y

theorem mem_halfBO_equiv {a b : ℕ} (φ : HomE E a b ≃ₗ[E] HomE E a b) {M M' : Submodule (𝓞 E) (HomE E a b)}
    (hM : ∀ y, y ∈ M' ↔ φ.symm y ∈ M) (SS : Finset (HeightOneSpectrum (𝓞 E))) (c : ℕ) (y : HomE E a b) :
    y ∈ halfBO SS M' c ↔ φ.symm y ∈ halfBO SS M c :=
  mem_twO_equiv φ hM c _ y

theorem mem_mulLat_equiv (φ : W ≃ₗ[E] W) {M M' : Submodule (𝓞 E) W} (hM : ∀ y, y ∈ M' ↔ φ.symm y ∈ M)
    (c : ℕ) (y : W) : y ∈ mulLat c M' ↔ φ.symm y ∈ mulLat c M := by
  simp only [mulLat, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨φ.symm z, (hM z).1 hz, by rw [equiv_osmulW]⟩
  · rintro ⟨z, hz, hzy⟩
    refine ⟨φ z, (hM _).2 (by simpa using hz), ?_⟩
    rw [← equiv_osmulW, hzy, LinearEquiv.apply_symm_apply]

end Gen

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_homO_gmap (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (y : HomE E a b) : y ∈ homO (gmap γ N) (gmap γ' N') ↔ (conjH γ γ').symm y ∈ homO N N' := by
  change (∀ v ∈ gmap γ N, y v ∈ gmap γ' N') ↔ ∀ u ∈ N, ((conjH γ γ').symm y) u ∈ N'
  constructor
  · intro h u hu
    have := h (γ u) ((mem_gmap γ N _).2 (by simpa using hu))
    rw [mem_gmap] at this
    simpa [conjH_symm_apply] using this
  · intro h v hv
    rw [mem_gmap]
    have := h (γ.symm v) ((mem_gmap γ N v).1 hv)
    simpa [conjH_symm_apply] using this

theorem mem_perO_gmap (AA : Submodule (𝓞 E) E) (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (y : HomE E a b) : y ∈ perO AA (gmap γ N) (gmap γ' N') ↔ (conjH γ γ').symm y ∈ perO AA N N' := by
  have key : perO AA (gmap γ N) (gmap γ' N') = (perO AA N N').map (conjE γ γ' : HomE E a b →ₗ[𝓞 E] HomE E a b) := by
    unfold perO
    rw [Submodule.map_span]
    congr 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨r, hr, x, hx, rfl⟩
      refine ⟨r • (conjE γ γ').symm x, ⟨r, hr, _, (mem_homO_gmap γ γ' N N' x).1 hx, rfl⟩, ?_⟩
      show conjH γ γ' (r • (conjH γ γ').symm x) = r • x
      rw [map_smul, LinearEquiv.apply_symm_apply]
    · rintro ⟨w, ⟨r, hr, x, hx, rfl⟩, rfl⟩
      refine ⟨r, hr, conjE γ γ' x, (mem_homO_gmap γ γ' N N' _).2 ?_, ?_⟩
      · show (conjH γ γ').symm (conjH γ γ' x) ∈ homO N N'
        rw [LinearEquiv.symm_apply_apply]; exact hx
      · show conjH γ γ' (r • x) = r • conjH γ γ' x
        rw [map_smul]
  rw [key, Submodule.mem_map_equiv]
  rfl

theorem mem_homAt_gmap (S : Finset (HeightOneSpectrum (𝓞 E))) (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (y : HomE E a b) :
    y ∈ homAt S (gmap γ N) (gmap γ' N') ↔ (conjH γ γ').symm y ∈ homAt S N N' := by
  rw [homAt_gmap, Submodule.mem_map_equiv]
  rfl

end Lat

section Lift

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem isLift_conj (S : Finset (HeightOneSpectrum (𝓞 X.E))) (γ : Sp X.E a ≃ₗ[X.E] Sp X.E a) (γ' : Sp X.E b ≃ₗ[X.E] Sp X.E b)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x s' : HomE X.E a b)
    (h : A.IsLift S (gmap γ N) (gmap γ' N') c (conjH γ γ' x) s') : A.IsLift S N N' c x ((conjH γ γ').symm s') := by
  obtain ⟨⟨c', hc', hs⟩, hx⟩ := h
  refine ⟨⟨c', hc', (mem_halfAO_equiv (conjH γ γ') (mem_perO_gmap A.AA γ γ' N N') S c' s').1 hs⟩, ?_⟩
  have := (mem_mulLat_equiv (conjH γ γ') (mem_homAt_gmap S γ γ' N N') c _).1 hx
  rwa [map_sub, LinearEquiv.symm_apply_apply] at this

end Lift

end Formalism.L2.Ker.TI
