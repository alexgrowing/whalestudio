import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.MidLift

open GlobalTheory.DegVol.RealMat

variable {k r j : ℕ}

private lemma Hpk_esI_apply' (a : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) i = if i = eI k r a then 1 else 0 := by
  have ha := a.isLt
  simp only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_esI (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) u (bvec (esI k r a)) = u (eI k r a) := by
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply, Hpk_esI_apply']

theorem coord_eq_zero {g : Mat k r} (hg : g ∈ UH (Hpk k r))
    (hX : ∀ a : Fin r, a.val < j → g⁻¹ *ᵥ bvec (eI k r a) ∈ XstJ k r j ∧ g *ᵥ bvec (eI k r a) ∈ XstJ k r j)
    {u : Fin (2 * r + k + 1) → ℂ} (hu : ∀ a : Fin r, a.val < j → herm (Hpk k r) u (g⁻¹ *ᵥ bvec (eI k r a)) = 0)
    (b : Fin r) (hb : b.val < j) : u (eI k r b) = 0 := by
  have hdet : IsUnit g.det := GlobalTheory.DegVol.RealMat.isUnit_det hg

  have hinj : Function.Injective (Matrix.mulVecLin g⁻¹) := by
    intro x y hxy
    have h := congrArg (fun v => g *ᵥ v) hxy
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet] using h

  have hli : ∀ f : {a : Fin r // a.val < j} → Fin (2 * r + k + 1), Function.Injective f →
      LinearIndependent ℂ (fun a => bvec (f a)) := by
    intro f hf
    have h := (Pi.basisFun ℂ (Fin (2 * r + k + 1))).linearIndependent.comp f hf
    convert h using 1
    funext a
    simp [bvec, Function.comp]
  have hI1 : Function.Injective fun a : {a : Fin r // a.val < j} => eI k r a.1 := by
    intro a a' h
    have h' := congrArg Fin.val h
    simp only [eI, Fin.val_mk] at h'
    exact Subtype.ext (Fin.ext h')
  have hI2 : Function.Injective fun a : {a : Fin r // a.val < j} => esI k r a.1 := by
    intro a a' h
    have h' := congrArg Fin.val h
    simp only [esI, Fin.val_mk] at h'
    have := a.1.isLt
    have := a'.1.isLt
    exact Subtype.ext (Fin.ext (by omega))
  have hl1 : LinearIndependent ℂ (fun a : {a : Fin r // a.val < j} => bvec (eI k r a.1)) := hli _ hI1
  have hl2 : LinearIndependent ℂ (fun a : {a : Fin r // a.val < j} => bvec (esI k r a.1)) := hli _ hI2

  have hle : (XJ k r j).map (Matrix.mulVecLin g⁻¹) ≤ XstJ k r j := by
    unfold XJ
    rw [Submodule.map_span_le]
    rintro _ ⟨a, rfl⟩
    rw [Matrix.mulVecLin_apply]
    exact (hX a.1 a.2).1
  have hrank : Module.finrank ℂ ((XJ k r j).map (Matrix.mulVecLin g⁻¹)) = Module.finrank ℂ (XstJ k r j) := by
    rw [← (Submodule.equivMapOfInjective _ hinj (XJ k r j)).finrank_eq]
    unfold XJ XstJ
    rw [finrank_span_eq_card hl1, finrank_span_eq_card hl2]
  have heq : (XJ k r j).map (Matrix.mulVecLin g⁻¹) = XstJ k r j :=
    Submodule.eq_of_le_of_finrank_eq hle hrank
  have hmem : bvec (esI k r b) ∈ (XJ k r j).map (Matrix.mulVecLin g⁻¹) := by
    rw [heq]
    unfold XstJ
    exact Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 hmem
  have hzero : ∀ x ∈ XJ k r j, herm (Hpk k r) u (g⁻¹ *ᵥ x) = 0 := by
    intro x hx
    unfold XJ at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact hu a.1 a.2
    | zero => simp [herm]
    | add x₁ x₂ _ _ h₁ h₂ => rw [Matrix.mulVec_add, GlobalTheory.DegVol.RealMat.herm_add_right, h₁, h₂, add_zero]
    | smul c y _ h => rw [Matrix.mulVec_smul, GlobalTheory.DegVol.RealMat.herm_smul_right, h, mul_zero]
  rw [← herm_esI u b, ← hxe, Matrix.mulVecLin_apply]
  exact hzero x hx

theorem inWb_of_mem_Wn : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ w ∈ N.Wn, inWb k r (Φ w) := by
  intro K V _ _ _ _ _ _ _ _ H r N k σ ρ β Φ z z' g hρ hF w hw
  unfold IsFrameOf at hF
  obtain ⟨hR, -, -, -, ⟨c, hN⟩, he, hist, -, -⟩ := hF
  unfold IsReal at hR
  obtain ⟨-, -, hiso, -⟩ := hR
  unfold IsNormal0 at hN
  obtain ⟨hgG, -, -, -, -, hX, -, -⟩ := hN
  unfold GlobalTheory.DegCnt.NF.Wn at hw
  rw [GlobalTheory.DegCnt.NFGeom.mem_perp'] at hw

  have hBe : ∀ a : Fin r, H.B w (N.F.e a.castSucc) = 0 := by
    intro a
    have h1 : N.F.e a.castSucc ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
    rw [← H.herm (N.F.e a.castSucc) w, hw _ h1, star_zero]
  have hBe' : ∀ a : Fin r, H.B w (N.F'.e a.castSucc) = 0 := by
    intro a
    have h1 : N.F'.e a.castSucc ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
    rw [← H.herm (N.F'.e a.castSucc) w, hw _ h1, star_zero]
  have hBist : ∀ b : Fin r, N.j ≤ b.val → H.B w (N.ist b) = 0 := by
    intro b hb
    have h1 : N.ist b ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩)
    rw [← H.herm (N.ist b) w, hw _ h1, star_zero]
  have hρ' : ∀ n : ℕ, ((ρ ^ n : ℝ) : ℂ) ≠ 0 := fun n => Complex.ofReal_ne_zero.2 (pow_pos hρ n).ne'

  have hes : ∀ a : Fin r, Φ w (esI k r a) = 0 := by
    intro a
    have h1 := hiso w (N.F.e a.castSucc)
    rw [(he a).1, GlobalTheory.DegVol.RealMat.herm_smul_right, GlobalTheory.DegVol.RealMat.herm_eI, hBe a, map_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left (star_ne_zero.2 (hρ' _))

  have hhi : ∀ b : Fin r, N.j ≤ b.val → Φ w (eI k r b) = 0 := by
    intro b hb
    have h1 := hiso w (N.ist b)
    rw [hist b hb, GlobalTheory.DegVol.RealMat.herm_smul_right, herm_esI, hBist b hb, map_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left
      (star_ne_zero.2 (Complex.ofReal_ne_zero.2 (inv_ne_zero (pow_pos hρ _).ne')))

  have hlo : ∀ b : Fin r, b.val < N.j → Φ w (eI k r b) = 0 := by
    have hdet : IsUnit g.det := GlobalTheory.DegVol.RealMat.isUnit_det hgG
    intro b hb
    refine coord_eq_zero (j := N.j) hgG hX (fun a _ => ?_) b hb
    have h3 : Φ (N.F'.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • (g⁻¹ *ᵥ bvec (eI k r a)) := by
      rw [← Matrix.mulVec_smul, ← (he a).2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mulVec]
    have h2 : g⁻¹ *ᵥ bvec (eI k r a) = (((ρ ^ (r - a.val) : ℝ) : ℂ))⁻¹ • Φ (N.F'.e a.castSucc) := by
      rw [h3, inv_smul_smul₀ (hρ' _)]
    rw [h2, GlobalTheory.DegVol.RealMat.herm_smul_right, hiso, hBe' a, map_zero, mul_zero]
  unfold inWb
  intro i hi
  rcases hi with hi | hi
  · have hb : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
    rw [← hb]
    by_cases hj : i.val < N.j
    · exact hlo ⟨i.val, hi⟩ hj
    · exact hhi ⟨i.val, hi⟩ (not_lt.1 hj)
  · have hlt : 2 * r + k - i.val < r := by
      have := i.isLt
      omega
    have hb : esI k r ⟨2 * r + k - i.val, hlt⟩ = i := by
      apply Fin.ext
      simp only [esI, Fin.val_mk]
      have := i.isLt
      omega
    rw [← hb]
    exact hes _

end GlobalTheory.DegVol.MidLift
