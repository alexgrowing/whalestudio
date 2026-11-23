import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
open Polynomial NumberField
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

noncomputable section

namespace GlobalTheory.CompanionTheory.EllIso

theorem exists_eigvec {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) (hS : S ≠ ⊥)
    (hst : ∀ x ∈ S, G *ᵥ x ∈ S) : ∃ (z : ℂ) (v : Fin n → ℂ), v ∈ S ∧ v ≠ 0 ∧ G *ᵥ v = z • v := by
  haveI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS
  let f : Module.End ℂ S := (Matrix.toLin' G).restrict (fun x hx => by simpa using hst x hx)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨c, v, v.2, fun h => hv.2 (Subtype.ext h), ?_⟩
  have := congrArg Subtype.val hv.apply_eq_smul
  simpa [f] using this

theorem eig_line {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (hs : G.charpoly.Separable) (z : ℂ) (v u : Fin n → ℂ)
    (hv : v ≠ 0) (hGv : G *ᵥ v = z • v) (hGu : G *ᵥ u = z • u) : ∃ c : ℂ, u = c • v := by
  let f : Module.End ℂ (Fin n → ℂ) := Matrix.toLin' G
  have hfc : LinearMap.charpoly f = G.charpoly := by
    simp [f, Matrix.charpoly_toLin']
  have hmem : ∀ w, G *ᵥ w = z • w → w ∈ Module.End.eigenspace f z := fun w hw => by
    rw [Module.End.mem_eigenspace_iff]; simpa [f] using hw
  have h1 : Module.finrank ℂ (Module.End.eigenspace f z) ≤ 1 := by
    have a := Submodule.finrank_mono (Module.End.eigenspace_le_maxGenEigenspace (f := f) (μ := z))
    have b := LinearMap.finrank_maxGenEigenspace_eq f z
    rw [hfc] at b
    have c := Polynomial.rootMultiplicity_le_one_of_separable hs z
    omega
  let v' : Module.End.eigenspace f z := ⟨v, hmem v hGv⟩
  let u' : Module.End.eigenspace f z := ⟨u, hmem u hGu⟩
  have hv' : v' ≠ 0 := fun h => hv (congrArg Subtype.val h)
  have h2 : Module.finrank ℂ (Module.End.eigenspace f z) = 1 := by
    haveI : Nontrivial (Module.End.eigenspace f z) := ⟨v', 0, hv'⟩
    have := Module.finrank_pos (R := ℂ) (M := Module.End.eigenspace f z)
    omega
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v' hv').1 h2 u'
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

open ComplexOrder in

theorem iso_bot_C {n : ℕ} (G B Bi : Matrix (Fin n) (Fin n) ℂ) (hB : B * Bi = 1) (hinv : Gᴴ * B * G = B)
    (hs : G.charpoly.Separable) (hz : ∀ z, G.charpoly.IsRoot z → ‖z‖ = 1) (S : Submodule ℂ (Fin n → ℂ))
    (hst : ∀ x ∈ S, G *ᵥ x ∈ S) (hiso : ∀ x ∈ S, ∀ y ∈ S, star x ⬝ᵥ (B *ᵥ y) = 0) : S = ⊥ := by
  by_contra hS
  obtain ⟨z, v, hvS, hv0, hGv⟩ := exists_eigvec G S hS hst
  have hroot : G.charpoly.IsRoot z := by
    have : (Matrix.scalar (Fin n) z - G).det = 0 := by
      refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, ?_⟩
      rw [Matrix.sub_mulVec, hGv]
      simp [Matrix.scalar_apply, Matrix.smul_mulVec]
    rw [Polynomial.IsRoot, Matrix.eval_charpoly]
    exact this
  have hz1 : star z * z = 1 := by
    have h := hz z hroot
    have : (starRingEnd ℂ) z * z = ((Complex.normSq z : ℝ) : ℂ) := by rw [mul_comm]; exact Complex.mul_conj z
    rw [Complex.normSq_eq_norm_sq, h] at this
    simpa using this
  let l : (Fin n → ℂ) → ℂ := fun y => star v ⬝ᵥ (B *ᵥ y)
  have hladd : ∀ a b, l (a + b) = l a + l b := fun a b => by simp [l, Matrix.mulVec_add, dotProduct_add]
  have hlsmul : ∀ (c : ℂ) a, l (c • a) = c * l a := fun c a => by
    simp [l, Matrix.mulVec_smul, dotProduct_smul]
  have hlG : ∀ y, l (G *ᵥ y) = z * l y := fun y => by
    have h0 : star (G *ᵥ v) ⬝ᵥ (B *ᵥ (G *ᵥ y)) = star v ⬝ᵥ (B *ᵥ y) := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hinv]
    rw [hGv, star_smul, smul_dotProduct] at h0
    have h1 : star z * l (G *ᵥ y) = l y := by simpa [l] using h0
    calc l (G *ᵥ y) = z * (star z * l (G *ᵥ y)) := by
          rw [← mul_assoc, mul_comm z, hz1, one_mul]
      _ = z * l y := by rw [h1]
  have hpoly : ∀ (f : ℂ[X]) y, l (aeval G f *ᵥ y) = f.eval z * l y := by
    intro f
    induction f using Polynomial.induction_on' with
    | add p q hp hq =>
      intro y
      rw [map_add, Matrix.add_mulVec, hladd, hp, hq, Polynomial.eval_add, add_mul]
    | monomial k a =>
      induction k with
      | zero =>
        intro y
        simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, hlsmul]
      | succ k ih =>
        intro y
        have e : aeval G (monomial (k + 1) a) = aeval G (monomial k a) * G := by
          simp [Polynomial.aeval_monomial, pow_succ, mul_assoc]
        rw [e, ← Matrix.mulVec_mulVec, ih, hlG]
        simp [pow_succ]
        ring
  obtain ⟨q, hq⟩ : (X - C z) ∣ G.charpoly := Polynomial.dvd_iff_isRoot.2 hroot
  have hqz : q.eval z ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := Polynomial.dvd_iff_isRoot.2 h0
    have h2 : (X - C z) ^ 2 ∣ G.charpoly := ⟨r, by rw [hq, hr]; ring⟩
    have h3 := (Polynomial.le_rootMultiplicity_iff hs.ne_zero).2 h2
    have h4 := Polynomial.rootMultiplicity_le_one_of_separable hs z
    omega
  have hl0 : ∀ y, l y = 0 := by
    intro y
    have h1 : G *ᵥ (aeval G q *ᵥ y) = z • (aeval G q *ᵥ y) := by
      have h0 : aeval G ((X - C z) * q) = 0 := by rw [← hq]; exact Matrix.aeval_self_charpoly G
      rw [map_mul, map_sub, aeval_X, aeval_C, sub_mul] at h0
      have h2 := congrArg (fun M => M *ᵥ y) h0
      simp only [Matrix.sub_mulVec, Matrix.zero_mulVec, ← Matrix.mulVec_mulVec] at h2
      rw [sub_eq_zero] at h2
      rw [h2]
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    obtain ⟨c, hc⟩ := eig_line G hs z v _ hv0 hGv h1
    have h3 : q.eval z * l y = 0 := by
      rw [← hpoly, hc, hlsmul]
      have : l v = 0 := hiso v hvS v hvS
      rw [this, mul_zero]
    exact (mul_eq_zero.1 h3).resolve_left hqz
  apply hv0
  have h5 := hl0 (Bi *ᵥ v)
  simp only [l, Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] at h5
  exact dotProduct_star_self_eq_zero.1 h5

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem nrm_map (τ : E →+* ℂ) (d : GL (Fin n) E) :
    (nrm d).val.map τ = d.val.map τ * ((d⁻¹ : GL (Fin n) E).val.map τ)ᴴ := by
  have e : (thetaE E n d).val.map τ = ((d⁻¹ : GL (Fin n) E).val.map τ)ᴴ := by
    rw [thetaE, thetaR_val]
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    exact NumberField.IsCMField.complexEmbedding_complexConj E τ _
  rw [nrm, Units.val_mul, Matrix.map_mul, e]

theorem iso_bot (d : GL (Fin n) E) (hd : IsRegEll d) (W : Submodule E (Fin n → E)) (hW : img (nrm d) W = W)
    (hi : W ≤ perpD (conjE E) d W) : W = ⊥ := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  set A := d.val.map τ with hA
  set Ai := (d⁻¹ : GL (Fin n) E).val.map τ with hAi
  have hAA : Ai * A = 1 := by
    rw [hA, hAi, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel]
    simp [Matrix.map_one]
  have hAA' : A * Ai = 1 := by
    rw [hA, hAi, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel]
    simp [Matrix.map_one]
  set G := (nrm d).val.map τ with hG
  have hGe : G = A * Aiᴴ := nrm_map τ d
  have hinv : Gᴴ * Ai * G = Ai := by
    have h1 : Aᴴ * Aiᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hAA, Matrix.conjTranspose_one]
    rw [hGe, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Ai * Aᴴ * Ai * (A * Aiᴴ) = Ai * Aᴴ * (Ai * A) * Aiᴴ := by simp only [Matrix.mul_assoc]
      _ = Ai * (Aᴴ * Aiᴴ) := by rw [hAA, Matrix.mul_one, Matrix.mul_assoc]
      _ = Ai := by rw [h1, Matrix.mul_one]
  have hcp : G.charpoly = (nrm d).val.charpoly.map τ := Matrix.charpoly_map _ _
  have hs : G.charpoly.Separable := by rw [hcp]; exact hd.1.map
  have hz : ∀ z, G.charpoly.IsRoot z → ‖z‖ = 1 := fun z h => hd.2 τ z (hcp ▸ h)
  let S : Submodule ℂ (Fin n → ℂ) := Submodule.span ℂ ((fun w : Fin n → E => τ ∘ w) '' (W : Set (Fin n → E)))
  have hgen : ∀ w ∈ W, τ ∘ w ∈ S := fun w hw => Submodule.subset_span ⟨w, hw, rfl⟩
  have hstab : ∀ w ∈ W, (nrm d).val *ᵥ w ∈ W := fun w hw => by
    have : (nrm d).val *ᵥ w ∈ img (nrm d) W := ⟨w, hw, rfl⟩
    rwa [hW] at this
  have hst : ∀ x ∈ S, G *ᵥ x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨w, hw, rfl⟩ := h
      have : G *ᵥ (τ ∘ w) = τ ∘ ((nrm d).val *ᵥ w) := by
        funext i
        exact (RingHom.map_mulVec τ _ _ i).symm
      rw [this]
      exact hgen _ (hstab w hw)
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact S.add_mem ha hb
    | smul c a _ ha => rw [Matrix.mulVec_smul]; exact S.smul_mem c ha
  have hbase : ∀ x ∈ W, ∀ y ∈ W, star (τ ∘ x) ⬝ᵥ (Ai *ᵥ (τ ∘ y)) = 0 := by
    intro x hx y hy
    obtain ⟨y', hy', hyy⟩ := hi hy
    have hy2 : (d⁻¹ : GL (Fin n) E).val *ᵥ y = y' := by
      rw [← hyy]
      simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    have h0 : ∑ i, conjE E (x i) * y' i = 0 := hy' x hx
    have h1 : Ai *ᵥ (τ ∘ y) = τ ∘ y' := by
      funext i
      rw [← hy2]
      exact (RingHom.map_mulVec τ _ _ i).symm
    rw [h1]
    have h2 := congrArg τ h0
    rw [map_sum, map_zero] at h2
    rw [← h2]
    simp only [dotProduct, Pi.star_apply, Function.comp_apply, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact (NumberField.IsCMField.complexEmbedding_complexConj E τ _).symm
  have hiso : ∀ x ∈ S, ∀ y ∈ S, star x ⬝ᵥ (Ai *ᵥ y) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, ha, rfl⟩ := h
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y h =>
        obtain ⟨b, hb, rfl⟩ := h
        exact hbase a ha b hb
      | zero => simp
      | add p q _ _ hp hq => rw [Matrix.mulVec_add, dotProduct_add, hp, hq, add_zero]
      | smul c p _ hp => rw [Matrix.mulVec_smul, dotProduct_smul, hp, smul_zero]
    | zero => intro y _; simp
    | add p q _ _ hp hq =>
      intro y hy
      rw [star_add, add_dotProduct, hp y hy, hq y hy, add_zero]
    | smul c p _ hp =>
      intro y hy
      rw [star_smul, smul_dotProduct, hp y hy, smul_zero]
  have hS := iso_bot_C G Ai A hAA hinv hs hz S hst hiso
  rw [Submodule.eq_bot_iff]
  intro w hw
  have h1 : τ ∘ w = 0 := by
    have := hgen w hw
    rw [hS] at this
    exact (Submodule.mem_bot ℂ).1 this
  funext i
  exact τ.injective (by simpa using congrFun h1 i)

theorem deg_bot (x : GA E n) : deg x (⊥ : Submodule E (Fin n → E)) = 0 := by
  have key : ∀ (k : ℕ) (_ : k = 0) (M : Matrix (Fin n) (Fin k) E), degM x M = 0 := by
    rintro k rfl M
    exact degM_zero x M
  exact key _ (by simp) _

theorem ellTerm_of_onlyIsotropic : OnlyIsotropic → EllTerm := by
  intro h E _ _ _ n
  obtain ⟨C, hC⟩ := h E n
  refine ⟨C, fun τ x d hd hτ => (hC τ x d hτ).2 fun W hW hi => ?_⟩
  obtain rfl := iso_bot d hd W hW hi
  rw [deg_bot]
  simp [prof]

end GlobalTheory.CompanionTheory.EllIso

end
