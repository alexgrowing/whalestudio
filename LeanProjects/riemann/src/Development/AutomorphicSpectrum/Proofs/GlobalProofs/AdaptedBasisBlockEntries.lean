import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchMatBlockEmbInfGL
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

open GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.CompanionTheory.BlockEntry

theorem sandwich_single_apply {A B : Type} [Fintype A] {d : ℕ} (U : Matrix A (Fin d) ℂ) (W : Matrix (Fin d) B ℂ)
    (i j : Fin d) (z : ℂ) (a : A) (c : B) : (U * Matrix.single i j z * W) a c = U a i * z * W j c := by
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_mul, ite_and]

theorem rows_of_adapted {n m : ℕ} {H P : Matrix (Fin n) (Fin n) ℂ} {X Y : Matrix (Fin n) (Fin m) ℂ}
    (hxx : Xᴴ * H * X = 0) (hyy : Yᴴ * H * Y = 0) (hxy : Xᴴ * H * Y = 1) (hyx : Yᴴ * H * X = 1) (hle : 2 * m ≤ n)
    (cX : ∀ (c : Fin n) (k : Fin m), c.val = k.val → ∀ a, P a c = X a k)
    (cY : ∀ (c : Fin n) (k : Fin m), c.val + k.val + 1 = n → ∀ a, P a c = Y a k)
    (pX : ∀ c : Fin n, m ≤ c.val → c.val + m < n → ∀ k, (Xᴴ * H * P) k c = 0)
    (pY : ∀ c : Fin n, m ≤ c.val → c.val + m < n → ∀ k, (Yᴴ * H * P) k c = 0) (k : Fin m) (c : Fin n) :
    (Yᴴ * H * P) k c = (if c.val = k.val then 1 else 0) ∧
      (Xᴴ * H * P) k c = (if c.val + k.val + 1 = n then 1 else 0) := by
  have hk := k.2
  have hc := c.2
  by_cases h1 : c.val < m
  · have e : ∀ M : Matrix (Fin m) (Fin n) ℂ, (M * P) k c = (M * X) k ⟨c.val, h1⟩ := fun M => by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => by rw [cX c ⟨c.val, h1⟩ rfl a]
    rw [e, e, hyx, hxx, Matrix.one_apply, Matrix.zero_apply]
    refine ⟨?_, ?_⟩
    · by_cases e' : c.val = k.val
      · rw [if_pos e', if_pos (Fin.ext e'.symm)]
      · rw [if_neg e', if_neg fun e'' => e' (congrArg Fin.val e'').symm]
    · rw [if_neg (by omega)]
  · by_cases h2 : c.val + m < n
    · rw [pX c (by omega) h2, pY c (by omega) h2, if_neg (by omega), if_neg (by omega)]
      exact ⟨rfl, rfl⟩
    · have hk' : n - 1 - c.val < m := by omega
      have e : ∀ M : Matrix (Fin m) (Fin n) ℂ, (M * P) k c = (M * Y) k ⟨n - 1 - c.val, hk'⟩ := fun M => by
        simp only [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun a _ => by rw [cY c ⟨n - 1 - c.val, hk'⟩ (by simp only; omega) a]
      rw [e, e, hyy, hxy, Matrix.one_apply, Matrix.zero_apply]
      refine ⟨by rw [if_neg (by omega)], ?_⟩
      by_cases e' : c.val + k.val + 1 = n
      · rw [if_pos e', if_pos (Fin.ext (by simp only; omega))]
      · rw [if_neg e', if_neg fun e'' => e' (by have := congrArg Fin.val e''; simp only at this; omega)]

theorem conj_units_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) {m : ℕ}
    {X Y : Matrix (Fin n) (Fin m) E} (hW : IsWittFrame σ J X Y) {l d : ℕ} (h : l + d ≤ m) {C : GL (Fin n) E}
    (hC : GlobalTheory.BlockForms.IsAdapted σ J X Y C) (τ : E →+* ℂ) (i j : Fin d) (p q p' q' : Fin n)
    (hp : p.val = l + i.val) (hq : q.val = l + j.val) (hp' : p'.val + l + j.val + 1 = n)
    (hq' : q'.val + l + i.val + 1 = n) (z : ℂ) :
    z • (C.1.map τ * Matrix.single p q 1 * (C.1.map τ)⁻¹) -
        (starRingEnd ℂ z) • (C.1.map τ * Matrix.single p' q' 1 * (C.1.map τ)⁻¹) =
      (GlobalTheory.BlockForms.blkCols h X).map τ * Matrix.single i j z * (((GlobalTheory.BlockForms.blkCols h Y).map τ)ᴴ * J.map τ) -
        (GlobalTheory.BlockForms.blkCols h Y).map τ * (Matrix.single i j z)ᴴ * (((GlobalTheory.BlockForms.blkCols h X).map τ)ᴴ * J.map τ) := by
  classical
  set P := C.1.map τ with hP
  have hdet : IsUnit P.det := by
    have e : P.det = τ C.1.det := by rw [hP, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [e]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 C.isUnit).map τ
  obtain ⟨hxx, hyy, hxy⟩ := GlobalTheory.CentreFin.frame_emb hcm hW τ
  have hJh : (J.map τ)ᴴ = J.map τ := GlobalTheory.LeviHC.conjTranspose_map hcm hJ τ
  have hyx := GlobalTheory.CentreFin.dual_swap hJh hxy
  have perp : ∀ (A : Matrix (Fin n) (Fin m) E) (c : Fin n), (Formalism.UG.cT (σ : E →+* E) A * J) *ᵥ (fun k => C.1 k c) = 0 →
      ∀ k, ((A.map τ)ᴴ * J.map τ * P) k c = 0 := fun A c e k => by
    have e1 : ((Formalism.UG.cT (σ : E →+* E) A * J) *ᵥ (fun k => C.1 k c)) k = 0 := by rw [e]; rfl
    have e2 := congrArg τ e1
    rw [map_zero] at e2
    rw [← e2, ← GlobalTheory.CentreFin.map_cT_emb hcm τ A, ← Matrix.map_mul]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hP, map_sum, map_mul]
  have what₂ := rows_of_adapted (P := P) hxx hyy hxy hyx hC.le
    (fun c k e a => by rw [hP, Matrix.map_apply, hC.colX c k e a, Matrix.map_apply])
    (fun c k e a => by rw [hP, Matrix.map_apply, hC.columnBlock c k e a, Matrix.map_apply])
    (fun c h1 h2 => perp X c (hC.perpX c h1 h2)) (fun c h1 h2 => perp Y c (hC.perpY c h1 h2))
  set Xb := (GlobalTheory.BlockForms.blkCols h X).map τ with hXb
  set Yb := (GlobalTheory.BlockForms.blkCols h Y).map τ with hYb
  set R := Xb * Matrix.single i j z * (Ybᴴ * J.map τ) - Yb * (Matrix.single i j z)ᴴ * (Xbᴴ * J.map τ) with hR
  let f : Fin d → Fin m := fun a => ⟨l + a.val, by omega⟩
  have sY : ∀ (a : Fin d) (c : Fin n), (Ybᴴ * J.map τ * P) a c = if c.val = l + a.val then 1 else 0 := fun a c =>
    (what₂ (f a) c).1
  have sX : ∀ (a : Fin d) (c : Fin n), (Xbᴴ * J.map τ * P) a c = if c.val + (l + a.val) + 1 = n then 1 else 0 := fun a c =>
    (what₂ (f a) c).2
  have hRP : R * P = P * (z • Matrix.single p q 1 - (starRingEnd ℂ z) • Matrix.single p' q' 1) := by
    ext a c
    have e1 : R * P = Xb * Matrix.single i j z * (Ybᴴ * J.map τ * P) -
        Yb * Matrix.single j i (starRingEnd ℂ z) * (Xbᴴ * J.map τ * P) := by
      rw [hR, Matrix.sub_mul, Matrix.conjTranspose_single]
      simp only [Matrix.mul_assoc]
      rfl
    have e2 : P a p = Xb a i := by
      rw [hP, Matrix.map_apply, hC.colX p (f i) hp a]; rfl
    have e3 : P a p' = Yb a j := by
      rw [hP, Matrix.map_apply, hC.columnBlock p' (f j) (by simp only [f]; omega) a]; rfl
    rw [e1, Matrix.sub_apply, sandwich_single_apply, sandwich_single_apply, sY, sX, Matrix.mul_sub, Matrix.sub_apply,
      Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_apply, Matrix.smul_apply]
    have e4 : ∀ (u v : Fin n), (P * Matrix.single u v (1 : ℂ)) a c = P a u * (if c = v then 1 else 0) := fun u v => by
      by_cases e : c = v
      · subst e
        simp [Matrix.mul_single_apply_same]
      · have e' : v ≠ c := fun e'' => e e''.symm
        rw [if_neg e, mul_zero, Matrix.mul_apply]
        exact Finset.sum_eq_zero fun b _ => by rw [Matrix.single_apply_of_col_ne _ _ e' _, mul_zero]
    rw [e4, e4, e2, e3]
    have c1 : (c = q) ↔ c.val = l + j.val := by rw [Fin.ext_iff, hq]
    have c2 : (c = q') ↔ c.val + (l + i.val) + 1 = n := by rw [Fin.ext_iff]; omega
    simp only [c1, c2, smul_eq_mul]
    ring
  calc _ = P * (z • Matrix.single p q 1 - (starRingEnd ℂ z) • Matrix.single p' q' 1) * P⁻¹ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = R := by rw [← hRP, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]

theorem lieS_eq_derEnd : ∀ (D : D7) [IsTotallyComplex D.host.E] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (l d : ℕ) (h : l + d ≤ m)
    (ι : GlobalTheory.CuspRep.GA D.host.E d →* GA D V), GlobalTheory.BlockForms.IsBlockEmb D.sp.cm.sig V.gram X Y h ι →
    ∀ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C → ∀ (τ : D.what₂.Tau)
    (F : GlobalTheory.Mem.AutSpace.SmFun θ V) (f : GlobalTheory.CuspRep.Sm D.host.E d), (∀ x, f.1 x = F.1 (ι x)) →
    ∀ (i j : Fin d) (p q p' q' : Fin V.rank), p.val = l + i.val → q.val = l + j.val →
    p'.val + l + j.val + 1 = V.rank → q'.val + l + i.val + 1 = V.rank → ∀ (z : ℂ) (x : GlobalTheory.CuspRep.GA D.host.E d),
      (GlobalTheory.CuspRep.lieS D.host.E d i j (GlobalTheory.CuspRep.atEmb (tauE D τ) z) f).1 x =
        (GlobalTheory.Mem.RealTranslate.derEnd hθ τ (z • (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) -
          (starRingEnd ℂ z) • (C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹)) F).1 (ι x) := by
  intro D _ θ hθ V m X Y hW l d h ι hι C hC τ F f hf i j p q p' q' hp hq hp' hq' z x
  have hcm := isCMExt_host D
  have hJ := GlobalTheory.Doubling.isHermND_gram V
  obtain ⟨e, he⟩ : ∃ e : EmbOver D.host.E (placeOf D τ), e.1 = tauE D τ := ⟨embOverOf D τ, rfl⟩
  have hline := isLineOf_blockEmb_exp' _ D.host.E D.sp.cm.sig hcm V.rank V.gram hJ m X Y hW l d h ι hι (placeOf D τ)
    e (Matrix.single i j z)
  have hmat := conj_units_eq hcm hJ hW h hC (tauE D τ) i j p q p' q' hp hq hp' hq' z
  rw [he, ← hmat] at hline
  have hsk := hline.skew hcm
  rw [he] at hsk
  have hZ : z • (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) -
      (starRingEnd ℂ z) • (C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹) ∈ lieAt V τ := hsk
  have hγ : ∀ t : ℝ, ι (GlobalTheory.CuspRep.infGL D.host.E d (GlobalTheory.CuspRep.expGLi d (t • (Matrix.single i j z).map
      (GlobalTheory.CuspRep.atEmb (tauE D τ))))) = oneP θ V τ (z • (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) -
        (starRingEnd ℂ z) • (C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹)) t := fun t => by
    obtain ⟨y, e1, e2⟩ := hline t
    refine Eq.trans e1 ?_
    rw [oneP, ← e2, GlobalTheory.Orb.archMat_eq_archEquiv _ hcm, atTau_archEquiv hθ V e he]
  have h0 : GlobalTheory.CuspRep.atEmb (tauE D τ) 0 = 0 := by rw [GlobalTheory.CuspRep.atEmb_eq]; simp
  have hs : Matrix.single i j (GlobalTheory.CuspRep.atEmb (tauE D τ) z) = (Matrix.single i j z).map (GlobalTheory.CuspRep.atEmb (tauE D τ)) := by
    ext a b; simp only [Matrix.single_apply, Matrix.map_apply]; split_ifs <;> simp [h0]
  rw [GlobalTheory.CuspRep.lieS_apply, hs, lie_eq_deriv_exp' D.host.E d f _ x]
  change _ = RderC θ V τ _ F.1 (ι x)
  rw [GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hZ]
  simp only [hf, map_mul, hγ]
  rfl

end GlobalTheory.CompanionTheory.BlockEntry
