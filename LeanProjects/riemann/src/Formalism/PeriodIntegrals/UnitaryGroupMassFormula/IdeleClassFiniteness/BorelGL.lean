import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.OhatCompact

noncomputable section

namespace PIW.ClassFinD

open NumberField IsDedekindDomain

def IsUpperUni {R : Type} [CommRing R] {n : ℕ} (u : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, j < i → u i j = 0) ∧ ∀ i, u i i = 1

def IsDiagM {R : Type} [CommRing R] {n : ℕ} (t : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, i ≠ j → t i j = 0

def IwasawaAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)),
    ∃ u t k : GL (Fin n) (FiniteAdeleRing (𝓞 F) F),
      IsUpperUni u.val ∧ IsDiagM t.val ∧ k ∈ KGL F n ∧ g = u * t * k

def UnipApprox : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (u t : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)),
    IsUpperUni u.val → IsDiagM t.val →
      ∃ ν : GL (Fin n) F, ∃ w ∈ KGL F n, u = glIncl F n ν * t * w * t⁻¹

def IdeleClassFin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∃ C : Finset (FiniteAdeleRing (𝓞 F) F)ˣ, ∀ a : (FiniteAdeleRing (𝓞 F) F)ˣ,
      ∃ f : Fˣ, ∃ c ∈ C, ∃ e : (FiniteAdeleRing (𝓞 F) F)ˣ,
        (e : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F ∧
        ((e⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F ∧
        a = Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F) : F →* FiniteAdeleRing (𝓞 F) F) f * c * e

def diagGL {R : Type} [CommRing R] (n : ℕ) : (Fin n → Rˣ) →* GL (Fin n) R :=
  (Units.map (Matrix.diagonalRingHom (Fin n) R : (Fin n → R) →* Matrix (Fin n) (Fin n) R)).comp
    (MulEquiv.piUnits.symm : (Fin n → Rˣ) ≃* (Fin n → R)ˣ).toMonoidHom

theorem diagGL_val {R : Type} [CommRing R] (n : ℕ) (τ : Fin n → Rˣ) :
    (diagGL n τ).val = Matrix.diagonal fun i => (τ i : R) := rfl

theorem glIncl_diagGL (F : Type) [Field F] [NumberField F] (n : ℕ) (f : Fin n → Fˣ) :
    glIncl F n (diagGL n f) =
      diagGL n (fun i => Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F) : F →* FiniteAdeleRing (𝓞 F) F) (f i)) := by
  apply Units.ext
  ext i j
  simp [diagGL_val, Matrix.diagonal_apply, glIncl, apply_ite]

theorem diag_eq_diagGL {R : Type} [CommRing R] {n : ℕ} (t : GL (Fin n) R) (ht : IsDiagM t.val) :
    ∃ τ : Fin n → Rˣ, t = diagGL n τ := by
  have hunit : ∀ i, IsUnit (t.val i i) := by
    intro i
    have h : (t⁻¹.val * t.val) i i = (1 : Matrix (Fin n) (Fin n) R) i i := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_apply, Matrix.one_apply_eq,
      Finset.sum_eq_single i (fun k _ hki => by rw [ht k i hki, mul_zero]) (by simp)] at h
    exact ⟨⟨t.val i i, t⁻¹.val i i, (mul_comm _ _).trans h, h⟩, rfl⟩
  refine ⟨fun i => (hunit i).unit, Units.ext ?_⟩
  rw [diagGL_val]
  ext i j
  simp only [Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij
    exact (IsUnit.unit_spec _).symm
  · exact ht i j hij

theorem diagGL_mem_KGL (F : Type) [Field F] [NumberField F] (n : ℕ) (e : Fin n → (FiniteAdeleRing (𝓞 F) F)ˣ)
    (h1 : ∀ i, (e i : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F)
    (h2 : ∀ i, ((e i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ).val ∈ Ohat F) : diagGL n e ∈ KGL F n := by
  have hd : ∀ d : Fin n → FiniteAdeleRing (𝓞 F) F, (∀ i, d i ∈ Ohat F) →
      MatInt (Matrix.diagonal d) := by
    intro d hd i j
    rw [Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij
      exact hd i
    · exact (Ohat F).zero_mem
  show MatInt (diagGL n e).val ∧ MatInt (diagGL n e)⁻¹.val
  constructor
  · rw [diagGL_val]
    exact hd _ h1
  · rw [← map_inv (diagGL (R := FiniteAdeleRing (𝓞 F) F) n), diagGL_val]
    exact hd _ fun i => h2 i

theorem borelKGL_of (hI : IwasawaAf) (hU : UnipApprox) (hC : IdeleClassFin) : BorelKGL := by
  classical
  intro F _ _ n
  obtain ⟨C, hCa⟩ := hC F
  refine ⟨(Fintype.piFinset fun _ : Fin n => C).image (diagGL n), fun x => ?_⟩
  obtain ⟨u, t, k, hu, ht, hk, rfl⟩ := hI F n x
  obtain ⟨ν, w, hw, huν⟩ := hU F n u t hu ht
  obtain ⟨τ, rfl⟩ := diag_eq_diagGL t ht
  choose f c hc e he1 he2 hτ using fun i => hCa (τ i)
  have hsplit : diagGL n τ = glIncl F n (diagGL n f) * diagGL n c * diagGL n e := by
    rw [glIncl_diagGL, ← map_mul (diagGL (R := FiniteAdeleRing (𝓞 F) F) n),
      ← map_mul (diagGL (R := FiniteAdeleRing (𝓞 F) F) n)]
    congr 1
    funext i
    exact hτ i
  refine ⟨ν * diagGL n f, diagGL n c, Finset.mem_image.mpr ⟨c, Fintype.mem_piFinset.mpr hc, rfl⟩,
    diagGL n e * (w * k),
    (KGL F n).mul_mem (diagGL_mem_KGL F n e he1 he2) ((KGL F n).mul_mem hw hk), ?_⟩
  rw [huν, map_mul, hsplit]
  group

end PIW.ClassFinD

end
