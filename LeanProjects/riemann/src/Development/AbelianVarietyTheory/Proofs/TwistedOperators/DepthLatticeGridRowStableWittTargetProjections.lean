import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.ProjTgt

variable {D : D7}

theorem rat_mul_of_tmul {m n : ℕ} (M : Matrix (Fin m) (Fin m) D.host.E) (α : AF D.host.F)
    (x : Matrix (Fin m) (Fin n) D.host.E) :
    HMul.hMul (α := Mx D m m) (β := Mx D m n) (rat M) (Matrix.of fun i j => α ⊗ₜ[D.host.F] x i j) =
      Matrix.of fun i j => α ⊗ₜ[D.host.F] (M * x) i j := by
  ext i j
  simp only [rat, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show (1 : AF D.host.F) ⊗ₜ[D.host.F] M i k * α ⊗ₜ[D.host.F] x k j = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

def mulLeftHom {m n : ℕ} (A : Mx D m m) : Mx D m n →+ Mx D m n where
  toFun u := HMul.hMul (α := Mx D m m) (β := Mx D m n) A u
  map_zero' := Matrix.mul_zero _
  map_add' u v := Matrix.mul_add _ _ _

theorem rat_mul_mem_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} (M : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (hM : ∀ t ∈ LT, M *ᵥ t ∈ LT) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    HMul.hMul (α := Mx D T.rank T.rank) (β := WO S T) (rat M) u ∈ latO S T LS LT P := by
  have key : latO S T LS LT P ≤ (latO S T LS LT P).comap (mulLeftHom (n := S.rank) (rat M)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, M *ᵥ t, hM t ht, ?_⟩
    show HMul.hMul (α := Mx D T.rank T.rank) (β := Mx D T.rank S.rank) (rat M) _ = _
    refine (rat_mul_of_tmul M _ (Matrix.of fun i j => a * t i * ∑ k, star (s k) * S.gram k j)).trans ?_
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  exact AddSubgroup.mem_comap.1 (key hu)

theorem rat_mul_mem_hatMx {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) (M : Matrix (Fin m) (Fin m) D.host.E)
    (hM : ∀ t ∈ Λ', M *ᵥ t ∈ Λ') {u : Mx D m n} (hu : u ∈ hatMx (𝔪 • homLat Λ Λ')) :
    HMul.hMul (α := Mx D m m) (β := Mx D m n) (rat M) u ∈ hatMx (𝔪 • homLat Λ Λ') := by
  have hH : ∀ x ∈ 𝔪 • homLat Λ Λ', M * x ∈ 𝔪 • homLat Λ Λ' := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun y z hy hz => ?_)
    · have e1 : M * (r • y) = r • (M * y) := Matrix.mul_smul M r y
      rw [e1]
      refine Submodule.smul_mem_smul hr ?_
      intro z hz
      rw [← Matrix.mulVec_mulVec]
      exact hM _ (hy z hz)
    · rw [Matrix.mul_add]; exact Submodule.add_mem _ hy hz
  have key : hatMx (𝔪 • homLat Λ Λ') ≤ (hatMx (𝔪 • homLat Λ Λ')).comap (mulLeftHom (n := n) (rat M)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hα, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, M * x, hH x hx, ?_⟩
    exact rat_mul_of_tmul M _ x
  exact AddSubgroup.mem_comap.1 (key hu)

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem rat_mul_mem_depLat (p : Pair T) (M : Matrix (Fin (G.pT p).rank) (Fin (G.pT p).rank) D.host.E)
    (hM : ∀ t ∈ G.latT p, M *ᵥ t ∈ G.latT p) {u : WO (G.pS p) (G.pT p)} (hu : u ∈ depLat G p) :
    HMul.hMul (α := Mx D (G.pT p).rank (G.pT p).rank) (β := WO (G.pS p) (G.pT p)) (rat M) u ∈ depLat G p := by
  refine ⟨rat_mul_mem_latO M hM hu.1, fun e he => ?_⟩
  have e1 : e • HMul.hMul (α := Mx D (G.pT p).rank (G.pT p).rank) (β := WO (G.pS p) (G.pT p)) (rat M) u =
      HMul.hMul (α := Mx D (G.pT p).rank (G.pT p).rank) (β := WO (G.pS p) (G.pT p)) (rat M) (e • u) :=
    (Matrix.mul_smul _ e u).symm
  rw [e1]
  exact rat_mul_mem_hatMx _ M hM (hu.2 e he)

end GlobalTheory.AscFin.ProjTgt

noncomputable section

namespace GlobalTheory.AscFin.ProjTgt

variable {D : D7}

theorem cT_eq_cT {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := Matrix.ext fun _ _ => rfl

theorem gram_herm (V : HSp D) : V.gramᴴ = V.gram :=
  Matrix.ext fun i j => V.herm.eq (V.frame j) (V.frame i)

section SlopeTestRemainingChoices

variable {A B B₀ : HSp D} {c ρ : ℕ} {ε : D.host.E}

theorem orthogonalExtension_conjTranspose_mul_gram_mul_eq_one (a : HermitianOrthogonalExtensionData A B c ε) : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c ε := by
  rw [← cT_eq_cT]; exact a.gram

theorem besselDatum_auxiliaryVector_orthogonal_image (a : HermitianOrthogonalExtensionData A B c ε) : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
  have h := a.perp
  rw [cT_eq_cT] at h
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_herm, Matrix.conjTranspose_zero] at h2
  rw [Matrix.mul_assoc]; exact h2

theorem colsOf_cT_mul {n k m : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (f : Fin k → Fin c) (s : Fin k → D.host.E)
    (N : Matrix (Fin n) (Fin m) D.host.E) :
    (colsOf a f s)ᴴ * N = Matrix.of fun p j => star (s p) * (aᴴ * N) (f p) j := by
  ext p j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, colsOf, Matrix.of_apply, star_mul', Finset.mul_sum, mul_assoc]
  try rfl

theorem colsOf_mulVec {n k : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (f : Fin k → Fin c) (s : Fin k → D.host.E)
    (w : Fin k → D.host.E) : colsOf a f s *ᵥ w = fun i => ∑ p, a i (f p) * (s p * w p) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, colsOf]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem sum_mem_sumLat {n k l : ℕ} (M : Matrix (Fin n) (Fin l) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin l → D.host.E))
    (a : Matrix (Fin n) (Fin c) D.host.E) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (f : Fin k → Fin c)
    (u : Fin c → D.host.E) (hu : ∀ q, u q ∈ 𝔟 q) : (fun i => ∑ p, a i (f p) * u (f p)) ∈ sumLat M Λ a 𝔟 := by
  refine ⟨0, Λ.zero_mem, fun q => ∑ p, if q = f p then u q else 0, fun q => ?_, ?_⟩
  · refine (𝔟 q).val.sum_mem fun p _ => ?_
    split_ifs
    · exact hu q
    · exact (𝔟 q).val.zero_mem
  · funext i
    simp only [Matrix.mulVec_zero, Pi.zero_apply, zero_add, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem antiDiagonalEpsilonGramMatrix_rev_castLE_apply (h : ρ ≤ c) (h2 : 2 * ρ ≤ c) (p : Fin ρ) (q : Fin c) :
    antiDiagonalSignGramMatrix c ε (Fin.castLE h p).rev q = if q = Fin.castLE h p then 1 else 0 := by
  have := p.2; have := q.2
  unfold antiDiagonalSignGramMatrix
  simp only [Fin.val_rev, Fin.val_castLE, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem antiDiagonalEpsilonGramMatrix_castLE_apply (h : ρ ≤ c) (h2 : 2 * ρ ≤ c) (p : Fin ρ) (q : Fin c) :
    antiDiagonalSignGramMatrix c ε (Fin.castLE h p) q = if q = (Fin.castLE h p).rev then 1 else 0 := by
  have := p.2; have := q.2
  unfold antiDiagonalSignGramMatrix
  simp only [Fin.val_rev, Fin.val_castLE, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

end SlopeTestRemainingChoices

end GlobalTheory.AscFin.ProjTgt

noncomputable section

namespace GlobalTheory.AscFin.ProjTgt

variable {D : D7}

section Keep

variable {A B B₀ : HSp D} {c ρ : ℕ} {ε : D.host.E} (a : HermitianOrthogonalExtensionData A B c ε) (d : HypDec B B₀ ρ) (h : ρ ≤ c) (h2 : 2 * ρ ≤ c)
  (s : Fin ρ → D.host.E)

include h2

theorem qX_mul_a (he' : d.e' = colsOf a.a (fun p => (Fin.castLE h p).rev) s) :
    d.qX * a.a = Matrix.of fun p q => star (s p) * (if q = Fin.castLE h p then 1 else 0) := by
  show d.e'ᴴ * B.gram * a.a = _
  rw [Matrix.mul_assoc, he', colsOf_cT_mul, ← Matrix.mul_assoc, orthogonalExtension_conjTranspose_mul_gram_mul_eq_one]
  ext p q
  simp only [Matrix.of_apply, antiDiagonalEpsilonGramMatrix_rev_castLE_apply h h2]

theorem qX_mul_frame (he' : d.e' = colsOf a.a (fun p => (Fin.castLE h p).rev) s) :
    d.qX * frameMat B A a.ι = 0 := by
  show d.e'ᴴ * B.gram * frameMat B A a.ι = _
  rw [Matrix.mul_assoc, he', colsOf_cT_mul, ← Matrix.mul_assoc, besselDatum_auxiliaryVector_orthogonal_image]
  ext p q
  simp only [Matrix.of_apply, Matrix.zero_apply, mul_zero]

theorem qY_mul_a (he : d.e = colsOf a.a (Fin.castLE h) fun p => (-D.host.xi0) ^ (p.1 + 1)) :
    d.qY * a.a = Matrix.of fun p q => star ((-D.host.xi0) ^ (p.1 + 1)) * (if q = (Fin.castLE h p).rev then 1 else 0) := by
  show d.eᴴ * B.gram * a.a = _
  rw [Matrix.mul_assoc, he, colsOf_cT_mul, ← Matrix.mul_assoc, orthogonalExtension_conjTranspose_mul_gram_mul_eq_one]
  ext p q
  simp only [Matrix.of_apply, antiDiagonalEpsilonGramMatrix_castLE_apply h h2]

theorem qY_mul_frame (he : d.e = colsOf a.a (Fin.castLE h) fun p => (-D.host.xi0) ^ (p.1 + 1)) :
    d.qY * frameMat B A a.ι = 0 := by
  show d.eᴴ * B.gram * frameMat B A a.ι = _
  rw [Matrix.mul_assoc, he, colsOf_cT_mul, ← Matrix.mul_assoc, besselDatum_auxiliaryVector_orthogonal_image]
  ext p q
  simp only [Matrix.of_apply, Matrix.zero_apply, mul_zero]

theorem coef_one (he : d.e = colsOf a.a (Fin.castLE h) fun p => (-D.host.xi0) ^ (p.1 + 1))
    (he' : d.e' = colsOf a.a (fun p => (Fin.castLE h p).rev) s) (p : Fin ρ) :
    (-D.host.xi0) ^ (p.1 + 1) * star (s p) = 1 := by
  have h1 := congrFun (congrFun d.e'e p) p
  have h3 : (d.e'ᴴ * B.gram * d.e) p p = (-D.host.xi0) ^ (p.1 + 1) * (d.qX * a.a) p (Fin.castLE h p) := by
    show (d.qX * d.e) p p = _
    conv_lhs => rw [he]
    simp only [Matrix.mul_apply, colsOf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h3, qX_mul_a a d h h2 s he', Matrix.one_apply_eq] at h1
  simpa only [Matrix.of_apply, if_true, mul_one] using h1

theorem keepX (he : d.e = colsOf a.a (Fin.castLE h) fun p => (-D.host.xi0) ^ (p.1 + 1))
    (he' : d.e' = colsOf a.a (fun p => (Fin.castLE h p).rev) s) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ∀ t ∈ a.lat Λ 𝔟, (d.e * d.qX) *ᵥ t ∈ a.lat Λ 𝔟 := by
  rintro _ ⟨y, hy, u, hu, rfl⟩
  have e1 : (d.e * d.qX) *ᵥ (frameMat B A a.ι *ᵥ y + a.a *ᵥ u) =
      fun i => ∑ p, a.a i (Fin.castLE h p) * u (Fin.castLE h p) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
      qX_mul_frame a d h h2 s he', Matrix.mul_zero, Matrix.zero_mulVec, zero_add, ← Matrix.mulVec_mulVec, he, colsOf_mulVec,
      qX_mul_a a d h h2 s he']
    funext i
    refine Finset.sum_congr rfl fun p _ => ?_
    have hc := coef_one a d h h2 s he he' p
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← mul_assoc ((-D.host.xi0) ^ (p.1 + 1)), hc, one_mul]
  rw [e1]
  exact sum_mem_sumLat _ Λ a.a 𝔟 _ u hu

theorem keepY (he : d.e = colsOf a.a (Fin.castLE h) fun p => (-D.host.xi0) ^ (p.1 + 1))
    (he' : d.e' = colsOf a.a (fun p => (Fin.castLE h p).rev) s) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ∀ t ∈ a.lat Λ 𝔟, (d.e' * d.qY) *ᵥ t ∈ a.lat Λ 𝔟 := by
  rintro _ ⟨y, hy, u, hu, rfl⟩
  have e1 : (d.e' * d.qY) *ᵥ (frameMat B A a.ι *ᵥ y + a.a *ᵥ u) =
      fun i => ∑ p, a.a i (Fin.castLE h p).rev * u (Fin.castLE h p).rev := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
      qY_mul_frame a d h h2 he, Matrix.mul_zero, Matrix.zero_mulVec, zero_add, ← Matrix.mulVec_mulVec, he', colsOf_mulVec,
      qY_mul_a a d h h2 he]
    funext i
    refine Finset.sum_congr rfl fun p _ => ?_
    have hc := congrArg star (coef_one a d h h2 s he he' p)
    rw [star_mul', star_star, star_one] at hc
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← mul_assoc (s p), mul_comm (s p), hc, one_mul]
  rw [e1]
  exact sum_mem_sumLat _ Λ a.a 𝔟 _ u hu

end Keep

end GlobalTheory.AscFin.ProjTgt

theorem GlobalTheory.AscFin.latRow_proj_tgt : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (_ : 2 * (σ + 1) + 2 ≤ D.R.m)
    (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2),
      ((F.dB σ h').jX * (F.dB σ h').pX) * u ∈ latRow G (2 * σ + 2) ∧
      ((F.dB σ h').jY * (F.dB σ h').pY) * u ∈ latRow G (2 * σ + 2) := by
  intro D _ T L μ0 _ sc G W M _ F hF σ _ h' u hu
  obtain ⟨h2, he, s, he'⟩ := hF.hB σ h'
  have hL := G.sp.colLat (2 * σ + 2) (by omega) h'
  have hc : σ ≤ 2 * σ + 2 - 1 := by omega
  have kX : ∀ t ∈ G.Λ (.grid (2 * σ + 2) 0),
      ((F.dB σ h').e * (F.dB σ h').qX) *ᵥ t ∈ G.Λ (.grid (2 * σ + 2) 0) := by
    intro t ht
    change t ∈ (vtxOf L G.sp.Vs (2 * σ + 2) 0).lat at ht
    change _ ∈ (vtxOf L G.sp.Vs (2 * σ + 2) 0).lat
    rw [hL] at ht ⊢
    exact GlobalTheory.AscFin.ProjTgt.keepX _ _ hc h2 s he he' _ _ t ht
  have kY : ∀ t ∈ G.Λ (.grid (2 * σ + 2) 0),
      ((F.dB σ h').e' * (F.dB σ h').qY) *ᵥ t ∈ G.Λ (.grid (2 * σ + 2) 0) := by
    intro t ht
    change t ∈ (vtxOf L G.sp.Vs (2 * σ + 2) 0).lat at ht
    change _ ∈ (vtxOf L G.sp.Vs (2 * σ + 2) 0).lat
    rw [hL] at ht ⊢
    exact GlobalTheory.AscFin.ProjTgt.keepY _ _ hc h2 s he he' _ _ t ht
  refine ⟨?_, ?_⟩
  · have e1 : (F.dB σ h').jX * (F.dB σ h').pX = rat ((F.dB σ h').e * (F.dB σ h').qX) := (rat_mul _ _).symm
    rw [e1]
    exact GlobalTheory.AscFin.ProjTgt.rat_mul_mem_depLat (G := G) (.chi (2 * σ + 2) 0) _ kX hu
  · have e1 : (F.dB σ h').jY * (F.dB σ h').pY = rat ((F.dB σ h').e' * (F.dB σ h').qY) := (rat_mul _ _).symm
    rw [e1]
    exact GlobalTheory.AscFin.ProjTgt.rat_mul_mem_depLat (G := G) (.chi (2 * σ + 2) 0) _ kY hu
