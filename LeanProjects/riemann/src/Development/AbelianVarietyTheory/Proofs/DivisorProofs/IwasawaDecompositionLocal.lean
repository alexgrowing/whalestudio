import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemStabLocStdLatticeIffHtFinEqOne

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling

namespace GlobalTheory.Doubling.HgtDenom

theorem det_adjugate_mem {A : Type} [CommRing A] (S : Subring A) {n : ℕ} (M : Matrix (Fin n) (Fin n) A)
    (hM : ∀ i j, M i j ∈ S) : M.det ∈ S ∧ ∀ i j, M.adjugate i j ∈ S := by
  let M' : Matrix (Fin n) (Fin n) S := fun i j => ⟨M i j, hM i j⟩
  have e : M = S.subtype.mapMatrix M' := rfl
  refine ⟨?_, fun i j => ?_⟩
  · rw [e, ← RingHom.map_det]; exact (M'.det).2
  · rw [e, ← RingHom.map_adjugate]; exact (M'.adjugate i j).2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem std_denom {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} (v : HeightOneSpectrum (𝓞 F))
    (M : GL (Fin n) (Fv F v ⊗[F] E)) (hM : ∀ i j, M.1 i j ∈ intLoc F E v) :
    ‖Algebra.norm (Fv F v) M.1.det‖₊ ≤ 1 ∧ ∀ m : ℕ, ‖(m : Fv F v)‖₊ ≤ ‖Algebra.norm (Fv F v) M.1.det‖₊ →
      ∀ y : Fin n → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) → ∀ i, (m • ((M⁻¹).1 *ᵥ y)) i ∈ intLoc F E v := by
  obtain ⟨hd, ha⟩ := det_adjugate_mem _ M.1 hM
  have hN := algebraMap_norm_eq hσ (R := Fv F v) M.1.det
  have hs := sigR_mem_intLoc σ hd
  have hint : ∀ a : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) a ∈ intLoc F E v ↔ ‖a‖₊ ≤ 1 := fun a => by
    rw [mem_intLoc_iff_absFin_le_one, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, absFin_tmul_one]
  have hu : IsUnit M.1.det := (Matrix.isUnit_iff_isUnit_det _).1 M.isUnit
  have h0 : Algebra.norm (Fv F v) M.1.det ≠ 0 := (hu.map (Algebra.norm (Fv F v))).ne_zero
  refine ⟨(hint _).1 (hN ▸ mul_mem hd hs), fun m hm y hy i => ?_⟩
  set c := Algebra.norm (Fv F v) M.1.det
  have ht : algebraMap (Fv F v) (Fv F v ⊗[F] E) (m / c) ∈ intLoc F E v :=
    (hint _).2 (by rw [nnnorm_div]; exact div_le_one_of_le₀ hm zero_le)
  have e1 : M.1.adjugate = M.1.det • (M⁻¹).1 := by
    calc M.1.adjugate = M.1.adjugate * (M.1 * (M⁻¹).1) := by rw [Units.mul_inv, mul_one]
      _ = _ := by rw [← mul_assoc, Matrix.adjugate_mul, smul_mul_assoc, one_mul]
  have e2 : (m : Fv F v ⊗[F] E) =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (m / c) * sigR (Fv F v) σ M.1.det * M.1.det := by
    rw [mul_assoc, mul_comm _ M.1.det, ← hN, ← map_mul, div_mul_cancel₀ _ h0, map_natCast]
  have e3 : (m • ((M⁻¹).1 *ᵥ y)) i =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (m / c) * sigR (Fv F v) σ M.1.det * (M.1.adjugate *ᵥ y) i := by
    rw [e1, Matrix.smul_mulVec, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, e2, mul_assoc]
  rw [e3]
  refine mul_mem (mul_mem ht hs) ?_
  change ∑ j, M.1.adjugate i j * y j ∈ intLoc F E v
  exact sum_mem fun j _ => mul_mem (ha i j) (hy j)

theorem lat_denom {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    [Submodule.IsLattice E L] (v : HeightOneSpectrum (𝓞 F))
    (M : GL (Fin n) (Fv F v ⊗[F] E)) (hM : ∀ x ∈ latLoc F L v, M.1 *ᵥ x ∈ latLoc F L v) :
    ‖Algebra.norm (Fv F v) M.1.det‖₊ ≤ 1 ∧ ∀ m : ℕ, ‖(m : Fv F v)‖₊ ≤ ‖Algebra.norm (Fv F v) M.1.det‖₊ →
      ∀ y ∈ latLoc F L v, m • ((M⁻¹).1 *ᵥ y) ∈ latLoc F L v := by
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have hb := ha v
  set b := Formalism.UG.bc (compFin F E v) a
  have hb' : ∀ y ∈ latLoc F L v, ∀ i, ((b⁻¹).1 *ᵥ y) i ∈ intLoc F E v := fun y hy =>
    (hb _).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])
  have hent : ∀ i j, (b⁻¹ * M * b).1 i j ∈ intLoc F E v := fun i j => by
    have h1 : ∀ k, (Pi.single j 1 : Fin n → Fv F v ⊗[F] E) k ∈ intLoc F E v := fun k => by
      rw [Pi.single_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h2 := hb' _ (hM _ ((hb _).1 h1)) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h2
    exact h2
  have hdet : (b⁻¹ * M * b).1.det = M.1.det := by
    rw [Units.val_mul, Units.val_mul]; exact Matrix.det_units_conj' b M.1
  obtain ⟨h1, h2⟩ := std_denom hσ v _ hent
  rw [hdet] at h1 h2
  refine ⟨h1, fun m hm y hy => ?_⟩
  have h3 := (hb _).1 (h2 m hm _ (hb' y hy))
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul] at h3
  have e : b * (b⁻¹ * M * b)⁻¹ * b⁻¹ = M⁻¹ := by group
  rwa [e] at h3

omit [NumberField E] in

theorem levi_keeps (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F))
    (y : GLoc σ J v) (p : siegelH (Fv F v) σ Q) {k : GLoc σ Q v} (hk : k ∈ KFin σ Q L v)
    (e : ioH _ σ hQ (y, 1) = p * k) {x : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc F L v) :
    (matHom _ σ J y⁻¹).1 *ᵥ (leviMat finSumFinEquiv (matHom _ σ Q p).1 *ᵥ x) ∈ latLoc F L v ∧
      leviMat finSumFinEquiv (matHom _ σ Q p).1 *ᵥ x ∈ latLoc F L v := by
  have hp : KeepsDiag finSumFinEquiv (matHom (Fv F v) σ Q p).1 :=
    (mem_siegelOf (e := finSumFinEquiv) (mat := matHom (Fv F v) σ Q)).1 p.2
  have hk' := inv_mem hk
  have ek : k⁻¹ = ioH _ σ hQ (y⁻¹, 1) * p := by
    have : k = (p : GLoc σ Q v)⁻¹ * ioH _ σ hQ (y, 1) := by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this, mul_inv_rev, inv_inv, ← map_inv, Prod.inv_mk, inv_one]
  have h1 : pairVec finSumFinEquiv x x ∈ latLoc F (sumLat finSumFinEquiv L L) v := by
    rw [latLoc_sumLat]; exact (pairVec_mem_sumLat _).2 ⟨hx, hx⟩
  have h2 := (mem_stabLoc.1 hk' _).1 h1
  have e3 : (matHom _ σ Q (ioH _ σ hQ (y⁻¹, 1))).1 =
      blkMat finSumFinEquiv (matHom _ σ J y⁻¹).1 (matHom _ σ J 1).1 := rfl
  rw [ek, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hp.mulVec_diag, e3, blkMat_mulVec, latLoc_sumLat,
    pairVec_mem_sumLat] at h2
  exact ⟨h2.1, by simpa using h2.2⟩

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 →
    ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L]
      (v : HeightOneSpectrum (𝓞 F)), HasIwasawa σ Q (KFin σ Q L v) → ∀ g : GLoc σ J v,
      ∃ c : Fv F v, c ≠ 0 ∧ ‖c‖₊ ≤ 1 ∧ hgtFin σ Q L v (ioH (Fv F v) σ hQ (g, 1)) = ‖c‖₊ ∧
        ∀ m : ℕ, ‖(m : Fv F v)‖₊ ≤ ‖c‖₊ → ∀ y ∈ latLoc F L v,
          m • ((matHom (Fv F v) σ J g).1 *ᵥ y) ∈ latLoc F L v ∧ m • ((matHom (Fv F v) σ J g⁻¹).1 *ᵥ y) ∈ latLoc F L v := by
  intro F E _ _ _ _ _ σ hσ n J hJ Q hQ L _ v hI g
  obtain ⟨p, k, hk, e⟩ := hI (ioH (Fv F v) σ hQ (g, 1))
  set α := leviOf finSumFinEquiv (matHom (Fv F v) σ Q) p with hα
  set γ := matHom (Fv F v) σ J g with hγ
  have hγ' : matHom (Fv F v) σ J g⁻¹ = γ⁻¹ := map_inv _ _
  have kα : ∀ x ∈ latLoc F L v, α.1 *ᵥ x ∈ latLoc F L v := fun x hx => (levi_keeps σ hQ L v g p hk e hx).2
  have kβ : ∀ x ∈ latLoc F L v, (γ⁻¹ * α).1 *ᵥ x ∈ latLoc F L v := fun x hx => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hγ']; exact (levi_keeps σ hQ L v g p hk e hx).1
  obtain ⟨a1, a2⟩ := lat_denom hσ L v α kα
  obtain ⟨-, b2⟩ := lat_denom hσ L v _ kβ
  have hg1 : ‖Algebra.norm (Fv F v) (γ⁻¹).1.det‖₊ = 1 := by
    have := abs_detH (absEv_conjUnit σ v) hJ g⁻¹
    rwa [absEv_apply, val_detH, hγ'] at this
  rw [Units.val_mul, Matrix.det_mul, map_mul, nnnorm_mul, hg1, one_mul] at b2
  refine ⟨Algebra.norm (Fv F v) α.1.det,
    (((Matrix.isUnit_iff_isUnit_det _).1 α.isUnit).map (Algebra.norm (Fv F v))).ne_zero, a1, ?_,
    fun m hm y hy => ⟨?_, ?_⟩⟩
  · rw [e, hgtFin_mul p hk, absEv_apply]; rfl
  · have := kα _ (b2 m hm y hy)
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul] at this
    have e' : α * (γ⁻¹ * α)⁻¹ = γ := by group
    rwa [e'] at this
  · have := kβ _ (a2 m hm y hy)
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul] at this
    have e' : γ⁻¹ * α * α⁻¹ = γ⁻¹ := by group
    rwa [e', ← hγ'] at this

end GlobalTheory.Doubling.HgtDenom
