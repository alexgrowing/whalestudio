import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open Matrix

section Alg

theorem exists_factor_idem {L : Type} [Field L] {n m : ℕ} (e : Matrix (Fin n) (Fin n) L) (he : e * e = e)
    (N : Submodule L (Fin n → L)) (hN : ∀ v, v ∈ N ↔ e.mulVec v = v) (hr : Module.finrank L N = m) :
    ∃ (U : Matrix (Fin n) (Fin m) L) (V : Matrix (Fin m) (Fin n) L), U * V = e ∧ V * U = 1 := by
  classical
  let b : Module.Basis (Fin m) L N := Module.finBasisOfFinrankEq L N hr
  have hmem : ∀ v, e.mulVec v ∈ N := fun v => (hN _).2 (by rw [Matrix.mulVec_mulVec, he])
  let P : (Fin n → L) →ₗ[L] N := e.mulVecLin.codRestrict N hmem
  refine ⟨LinearMap.toMatrix' (N.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ P), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    have : (N.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ P) = e.mulVecLin := by
      apply LinearMap.ext
      intro v
      simp [P, LinearMap.codRestrict_apply]
      rfl
    rw [this]
    exact LinearMap.toMatrix'_toLin' e
  · rw [← LinearMap.toMatrix'_comp]
    have : (b.equivFun.toLinearMap ∘ₗ P) ∘ₗ (N.subtype ∘ₗ b.equivFun.symm.toLinearMap) = LinearMap.id := by
      apply LinearMap.ext
      intro a
      have h1 : P (b.equivFun.symm a : N) = b.equivFun.symm a :=
        Subtype.ext ((hN _).1 (b.equivFun.symm a).2)
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Submodule.coe_subtype, h1,
        LinearEquiv.apply_symm_apply, LinearMap.id_coe, id_eq]
    rw [this, LinearMap.toMatrix'_id]

theorem sum_minors_of_factor {T : Type} [CommRing T] {n m : ℕ} (U : Matrix (Fin n) (Fin m) T)
    (V : Matrix (Fin m) (Fin n) T) (h : V * U = 1) :
    ∑ S : Set.powersetCard (Fin n) m,
      ((U * V).submatrix (GlobalTheory.subsetEnum S) (GlobalTheory.subsetEnum S)).det = 1 := by
  have h0 := GlobalTheory.det_mul_eq_sum_minors V U
  rw [h, det_one] at h0
  rw [h0]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, det_mul, mul_comm]

theorem det_smul_of_factor {T : Type} [CommRing T] {n m : ℕ} (U : Matrix (Fin n) (Fin m) T)
    (V : Matrix (Fin m) (Fin n) T) (s : Fin m → Fin n) :
    ((U * V).submatrix s s).det • (U * V) =
      (U * V).submatrix id s * ((U * V).submatrix s s).adjugate * (U * V).submatrix s id := by
  rw [Matrix.submatrix_mul _ _ s id s Function.bijective_id, Matrix.submatrix_mul _ _ id id s Function.bijective_id,
    Matrix.submatrix_mul _ _ s id id Function.bijective_id, adjugate_mul_distrib, det_mul]
  simp only [Matrix.submatrix_id_id]
  have e1 : U * V.submatrix id s * ((V.submatrix id s).adjugate * (U.submatrix s id).adjugate) *
      (U.submatrix s id * V) = U * (V.submatrix id s * (V.submatrix id s).adjugate) *
        ((U.submatrix s id).adjugate * U.submatrix s id) * V := by
    simp only [Matrix.mul_assoc]
  rw [e1, mul_adjugate, adjugate_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul, mul_comm]

theorem idem_minors {R L : Type} [CommRing R] [Field L] (φ : R →+* L) (hφ : Function.Injective φ) {n m : ℕ}
    (e : Matrix (Fin n) (Fin n) R) (he : e * e = e) (N : Submodule L (Fin n → L))
    (hN : ∀ v, v ∈ N ↔ (e.map φ).mulVec v = v) (hr : Module.finrank L N = m) :
    (∑ S : Set.powersetCard (Fin n) m, (e.submatrix (GlobalTheory.subsetEnum S) (GlobalTheory.subsetEnum S)).det = 1) ∧
      ∀ s : Fin m → Fin n, (e.submatrix s s).det • e = e.submatrix id s * (e.submatrix s s).adjugate *
        e.submatrix s id := by
  obtain ⟨U, V, hUV, hVU⟩ := exists_factor_idem (e.map φ) (by rw [← Matrix.map_mul, he]) N hN hr
  have hdet : ∀ s : Fin m → Fin n, φ (e.submatrix s s).det = ((e.map φ).submatrix s s).det := fun s => by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]
  refine ⟨hφ ?_, fun s => Matrix.map_injective hφ ?_⟩
  · rw [map_sum, map_one]
    simp only [hdet, ← hUV]
    exact sum_minors_of_factor U V hVU
  · dsimp only
    have h2 := det_smul_of_factor U V s
    rw [hUV] at h2
    have hs : ((e.submatrix s s).det • e).map φ = φ (e.submatrix s s).det • e.map φ := by
      ext i j; simp
    have ha : (e.submatrix s s).adjugate.map φ = ((e.map φ).submatrix s s).adjugate := by
      rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, Matrix.submatrix_map]
    rw [hs, hdet, h2, Matrix.map_mul, Matrix.map_mul, ← Matrix.submatrix_map, ← Matrix.submatrix_map, ha]

theorem exists_split {R S : Type} [CommRing R] [CommRing S] {n m : ℕ} (e : Matrix (Fin n) (Fin n) R)
    (he : e * e = e) (s : Fin m → Fin n)
    (hid : (e.submatrix s s).det • e = e.submatrix id s * (e.submatrix s s).adjugate * e.submatrix s id)
    (φ : R →+* S) (hu : IsUnit (φ (e.submatrix s s).det)) :
    ∃ (u : Matrix (Fin n) (Fin m) S) (w : Matrix (Fin m) (Fin n) S), w * u = 1 ∧ u * w = e.map φ := by
  refine ⟨(e.submatrix id s).map φ,
    (hu.unit⁻¹ : Sˣ).val • ((e.submatrix s s).adjugate * e.submatrix s id).map φ, ?_, ?_⟩
  · have h1 : e.submatrix s id * e.submatrix id s = e.submatrix s s := by
      rw [← Matrix.submatrix_mul _ _ s id s Function.bijective_id, he]
    rw [Matrix.smul_mul, ← Matrix.map_mul, Matrix.mul_assoc, h1, adjugate_mul]
    have hs : ((e.submatrix s s).det • (1 : Matrix (Fin m) (Fin m) R)).map φ =
        φ (e.submatrix s s).det • (1 : Matrix (Fin m) (Fin m) S) := by
      ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [hs, smul_smul, IsUnit.val_inv_mul, one_smul]
  · rw [Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.mul_assoc, ← hid]
    have hs : ((e.submatrix s s).det • e).map φ = φ (e.submatrix s s).det • e.map φ := by
      ext i j; simp
    rw [hs, smul_smul, IsUnit.val_inv_mul, one_smul]

end Alg

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pm_minors (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (M : MChart Y) (σ : E →+* ℂ) :
    LowRank.pm p M σ * LowRank.pm p M σ = LowRank.pm p M σ ∧
    (∑ S : Set.powersetCard (Fin M.n) (Dw.mult σ),
      ((LowRank.pm p M σ).submatrix (GlobalTheory.subsetEnum S) (GlobalTheory.subsetEnum S)).det = 1) ∧
      ∀ s : Fin (Dw.mult σ) → Fin M.n, ((LowRank.pm p M σ).submatrix s s).det • LowRank.pm p M σ =
        (LowRank.pm p M σ).submatrix id s * ((LowRank.pm p M σ).submatrix s s).adjugate *
          (LowRank.pm p M σ).submatrix s id := by
  obtain ⟨L, _, _, y, h, hy, hi⟩ := LowRank.genIn_id Y M
  obtain ⟨h1, h2⟩ := LowRank.pm_gen p M σ hy h
  have he : LowRank.pm p M σ * LowRank.pm p M σ = LowRank.pm p M σ :=
    Matrix.map_injective hi (Matrix.map_mul.trans h2)
  obtain ⟨Λ⟩ := MChart.nonempty_lift E H Dw l Xo c c.F (RingHom.id c.F) Y M L (ev _ M.U h) y hy
    (spMap_ev _ M.hU h).symm
  let N : Submodule L (Fin M.n → L) := Module.End.eigenspace ((LowRank.pm p M σ).map (ev _ M.U h)).mulVecLin 1
  have hN : ∀ v, v ∈ N ↔ ((LowRank.pm p M σ).map (ev _ M.U h)).mulVec v = v := fun v =>
    Module.End.mem_eigenspace_iff.trans (by rw [one_smul]; rfl)
  exact ⟨he, idem_minors _ hi _ he N hN
    (finrank_chart_eig E H Dw l Xo c c.F (RingHom.id c.F) Y M L _ _ Λ σ N fun v => (hN v).trans (h1 v).symm)⟩

theorem exists_eCh_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (M : GChart Y)
    (x : Y.X), x ∈ M.U → ∀ W : Y.X.Opens, x ∈ W → ∃ k : ECh Y p, k.M = M ∧ x ∈ k.V ∧ IsAffineOpen k.V ∧ k.V ≤ W := by
  intro E _ _ _ H Dw l Xo c Y p M x hx W hW
  classical
  have ex : ∀ σ : E →+* ℂ, ∃ s : Fin (Dw.mult σ) → Fin M.n,
      Y.X.evaluation M.U x hx ((LowRank.pm p M.toMChart σ).submatrix s s).det ≠ 0 := fun σ => by
    by_contra h
    push_neg at h
    have := congrArg (Y.X.evaluation M.U x hx) (pm_minors Y p M.toMChart σ).2.1
    rw [map_sum, map_one, Finset.sum_eq_zero fun S _ => h _] at this
    exact zero_ne_one this
  choose s hs using ex
  let d := fun σ => ((LowRank.pm p M.toMChart σ).submatrix (s σ) (s σ)).det
  have hxf : x ∈ Y.X.basicOpen (∏ σ, d σ) := by
    refine (Y.X.evaluation_ne_zero_iff_mem_basicOpen x hx _).1 ?_
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun σ _ => hs σ
  obtain ⟨g, hg, hxg⟩ := M.hU.exists_basicOpen_le (V := W ⊓ Y.X.basicOpen (∏ σ, d σ)) ⟨x, hW, hxf⟩ hx
  have hle : Y.X.basicOpen g ≤ M.U := Y.X.basicOpen_le g
  have hVf : Y.X.basicOpen g ≤ Y.X.basicOpen (∏ σ, d σ) := hg.trans inf_le_right
  have hf : IsUnit (resG Y.X hle (∏ σ, d σ)) := by
    have h1 : IsUnit (resG Y.X (Y.X.basicOpen_le (∏ σ, d σ)) (∏ σ, d σ)) :=
      RingedSpace.isUnit_res_basicOpen Y.X.toRingedSpace _
    have h2 : resG Y.X hle (∏ σ, d σ) = resG Y.X hVf (resG Y.X (Y.X.basicOpen_le (∏ σ, d σ)) (∏ σ, d σ)) := by
      simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    rw [h2]
    exact h1.map _
  have hu : ∀ σ, IsUnit (resG Y.X hle (d σ)) := fun σ =>
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem d (Finset.mem_univ σ))) hf
  choose u w hwu huw using fun σ => exists_split _ (pm_minors Y p M.toMChart σ).1 (s σ)
    ((pm_minors Y p M.toMChart σ).2.2 (s σ)) (resG Y.X hle) (hu σ)
  exact ⟨⟨M, Y.X.basicOpen g, hle, u, w, hwu, huw⟩, rfl, hxg, M.hU.basicOpen g, hg.trans inf_le_left⟩

end Geo

end GlobalTheory.FlagMod.FieldFlag
