import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuotStVKer
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipBasis

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj

section FixLoc

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_sub_r' (x a b : Fin n → ℂ) :
    Formalism.L2.SG.HidaSetting.hJ ε x (a - b) = Formalism.L2.SG.HidaSetting.hJ ε x a - Formalism.L2.SG.HidaSetting.hJ ε x b := by
  simp only [Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_sub, dotProduct_sub]

theorem mem_spanLt_r (e : Fin r → Fin n → ℂ) (x : Fin n → ℂ) (hx : x ∈ Formalism.L2.SG.HidaSetting.spanLt e r) :
    ∃ α : Fin r → ℂ, ∑ a, α a • e a = x := by
  have hset : e '' {b : Fin r | b.1 < r} = Set.range e := by
    rw [← Set.image_univ]
    congr 1
    ext b
    simp [b.isLt]
  unfold Formalism.L2.SG.HidaSetting.spanLt at hx
  rw [hset] at hx
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx

theorem fix_loc (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (G Gi Y T : Matrix (Fin n) (Fin n) ℂ)
    (hGGi : G * Gi = 1) (hG : ∀ x x', Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ x) (G *ᵥ x') = Formalism.L2.SG.HidaSetting.hJ ε x x')
    (hee : ∀ a b, Formalism.L2.SG.HidaSetting.hJ ε (e a) (e b) = 0) (hez : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) z = 0)
    (hez' : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) z' = 0)
    (π : Fin (r + 1) → Fin (r + 1)) (hπ : ∀ a, π (π a) = a)
    (hP1 : ∀ c b, RealObj.Zhat ε (fam e z) (fam e z') G c b ≠ 0 ↔ c = π b)
    (hYN : ∀ x, (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) x = 0) → (Y - 1) *ᵥ x ∈ Formalism.L2.SG.HidaSetting.spanLt e r)
    (hTN : ∀ x, (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) x = 0) → (T - 1) *ᵥ x ∈ Formalism.L2.SG.HidaSetting.spanLt e r)
    (hYG : Y * G = G * T)
    (hYF : ∀ a, Y *ᵥ fam e z a = fam e z a) (hYGF : ∀ b, Y *ᵥ (G *ᵥ fam e z' b) = G *ᵥ fam e z' b) :
    Y = 1 := by
  set Z := RealObj.Zhat ε (fam e z) (fam e z') G with hZdef
  have hZne : ∀ b, Z (π b) b ≠ 0 := fun b => (hP1 _ _).2 rfl
  have hZ0 : ∀ c b, c ≠ π b → Z c b = 0 := fun c b h => by by_contra h'; exact h ((hP1 c b).1 h')
  have hπi : Function.Injective π := fun a b h => by rw [← hπ a, h, hπ b]
  have hZe : ∀ i c, Formalism.L2.SG.HidaSetting.hJ ε (fam e z i) (G *ᵥ e c) = Z i c.castSucc := by
    intro i c; simp only [hZdef, RealObj.Zhat, fam_castSucc]
  have hZf : ∀ i j, Formalism.L2.SG.HidaSetting.hJ ε (fam e z i) (G *ᵥ fam e z' j) = Z i j := fun i j => rfl
  have hef : ∀ (w : Fin n → ℂ), (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) w = 0) →
      ∀ a (i : Fin (r + 1)), Formalism.L2.SG.HidaSetting.hJ ε (e a) (fam (fun c => e c) w i) = 0 := by
    intro w hw a i
    induction i using Fin.lastCases with
    | last => rw [fam_last]; exact hw a
    | cast c => rw [fam_castSucc]; exact hee a c
  have hfe' : ∀ i a, Formalism.L2.SG.HidaSetting.hJ ε (fam e z i) (e a) = 0 := by
    intro i a
    rw [hJ_cj', hef z hez a i, map_zero]
  have hGi : ∀ x, G *ᵥ (Gi *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, hGGi, Matrix.one_mulVec]

  have hQ : ∀ q, (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) q = 0) → (∀ a, Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e a) q = 0) →
      Y *ᵥ q = q := by
    intro q h1 h2
    obtain ⟨α, hα⟩ := mem_spanLt_r e _ (hYN q h1)
    have h3 : ∀ a, Formalism.L2.SG.HidaSetting.hJ ε (e a) (Gi *ᵥ q) = 0 := by
      intro a; rw [← hG, hGi]; exact h2 a
    obtain ⟨β, hβ⟩ := mem_spanLt_r e _ (hTN _ h3)
    have hD : (Y - 1) *ᵥ q = ∑ b, β b • (G *ᵥ e b) := by
      have e1 : Y *ᵥ q = G *ᵥ (T *ᵥ (Gi *ᵥ q)) := by
        rw [Matrix.mulVec_mulVec (Gi *ᵥ q) G T, ← hYG, ← Matrix.mulVec_mulVec, hGi]
      have : (Y - 1) *ᵥ q = G *ᵥ ((T - 1) *ᵥ (Gi *ᵥ q)) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, e1, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, hGi]
      rw [this, ← hβ, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
    have hβ0 : ∀ b, β b = 0 := by
      intro b
      have h := congrArg (Formalism.L2.SG.HidaSetting.hJ ε (fam e z (π b.castSucc))) (hα.trans hD)
      rw [hJ_sum_r', hJ_sum_r'] at h
      simp only [hfe', mul_zero, Finset.sum_const_zero, hZe] at h
      rw [Finset.sum_eq_single b] at h
      · rcases mul_eq_zero.1 h.symm with h1 | h1
        · exact h1
        · exact absurd h1 (hZne _)
      · intro c _ hcb
        rw [hZ0 (π b.castSucc) c.castSucc (fun h' => hcb (Fin.castSucc_injective _ (hπi h')).symm), mul_zero]
      · intro h'; exact absurd (Finset.mem_univ b) h'
    have : (Y - 1) *ᵥ q = 0 := by rw [hD]; simp [hβ0]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    exact this

  have hall : ∀ x, Y *ᵥ x = x := by
    intro x
    let s1 : Fin n → ℂ := ∑ a : Fin r,
      (Formalism.L2.SG.HidaSetting.hJ ε (e a) x / Z a.castSucc (π a.castSucc)) • (G *ᵥ fam e z' (π a.castSucc))
    let s2 : Fin n → ℂ := ∑ c : Fin r,
      (Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e c) x / conj (Z (π c.castSucc) c.castSucc)) • fam e z (π c.castSucc)
    have hs1 : Y *ᵥ s1 = s1 := by
      simp only [s1, Matrix.mulVec_sum, Matrix.mulVec_smul, hYGF]
    have hs2 : Y *ᵥ s2 = s2 := by
      simp only [s2, Matrix.mulVec_sum, Matrix.mulVec_smul, hYF]
    have hq1 : ∀ d, Formalism.L2.SG.HidaSetting.hJ ε (e d) (x - s1 - s2) = 0 := by
      intro d
      rw [hJ_sub_r', hJ_sub_r', hJ_sum_r', hJ_sum_r']
      have hz2 : ∀ c : Fin r, Formalism.L2.SG.HidaSetting.hJ ε (e d) (fam e z (π c.castSucc)) = 0 :=
        fun c => hef z hez d _
      simp only [hz2, mul_zero, Finset.sum_const_zero, sub_zero]
      have hd : ∀ a : Fin r, Formalism.L2.SG.HidaSetting.hJ ε (e d) (G *ᵥ fam e z' (π a.castSucc)) =
          Z d.castSucc (π a.castSucc) := by
        intro a; rw [← hZf, fam_castSucc]
      simp only [hd]
      rw [Finset.sum_eq_single d, div_mul_cancel₀ _ ((hP1 _ _).2 (hπ _).symm), sub_self]
      · intro a _ had
        rw [hZ0 d.castSucc (π a.castSucc) (fun h' => had (Fin.castSucc_injective _ (by rw [hπ] at h'; exact h'.symm))), mul_zero]
      · intro h'; exact absurd (Finset.mem_univ d) h'
    have hq2 : ∀ d, Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e d) (x - s1 - s2) = 0 := by
      intro d
      rw [hJ_sub_r', hJ_sub_r', hJ_sum_r', hJ_sum_r']
      have hz1 : ∀ a : Fin r, Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e d) (G *ᵥ fam e z' (π a.castSucc)) = 0 :=
        fun a => by rw [hG]; exact hef z' hez' d _
      have hd2 : ∀ c : Fin r, Formalism.L2.SG.HidaSetting.hJ ε (G *ᵥ e d) (fam e z (π c.castSucc)) =
          conj (Z (π c.castSucc) d.castSucc) := fun c => by rw [hJ_cj', hZe]
      simp only [hz1, mul_zero, Finset.sum_const_zero, sub_zero, hd2]
      rw [Finset.sum_eq_single d, div_mul_cancel₀ _ ((map_ne_zero (starRingEnd ℂ)).2 (hZne _)), sub_self]
      · intro c _ hcd
        rw [hZ0 (π c.castSucc) d.castSucc (fun h' => hcd (Fin.castSucc_injective _ (hπi h'))), map_zero, mul_zero]
      · intro h'; exact absurd (Finset.mem_univ d) h'
    have hq := hQ _ hq1 hq2
    calc Y *ᵥ x = Y *ᵥ ((x - s1 - s2) + s1 + s2) := by congr 1; abel
      _ = (x - s1 - s2) + s1 + s2 := by rw [Matrix.mulVec_add, Matrix.mulVec_add, hq, hs1, hs2]
      _ = x := by abel
  exact Matrix.toLin'.injective (LinearMap.ext fun x => by rw [Matrix.toLin'_apply, hall x, Matrix.toLin'_one]; rfl)

end FixLoc

section FixGlob

variable {D : D7}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stVFix_holds (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : StVFix X u u' := by
  classical
  intro w hw v y hy hF hGF
  set γ := gamW X u u' w with hγdef
  have hγ : IsPtRep X u u' w γ := by
    rw [hγdef, gamW, dif_pos hw.1]; exact hw.1.choose_spec
  set e : Fin D.R.rS → Fin X.B.I.n → ℂ := fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)
  set z := Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)
  set z' := Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u')
  have hee : ∀ a b, Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (e a) (e b) = 0 := by
    intro a b; rw [Formalism.L2.SG.Pf.Level.hJ_rv]
    convert congrArg (X.B.I.φ v) (Formalism.L2.SG.Pf.UnipB.hE_ee X a b) using 1; simp
  have hez : ∀ (u : D.what₂.Word) a,
      Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (e a) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) = 0 := by
    intro u a; rw [Formalism.L2.SG.Pf.Level.hJ_rv]
    convert congrArg (X.B.I.φ v) (Formalism.L2.SG.Pf.UnipB.hE_ez X u a) using 1; simp
  have hGGi : uMat (γ v) * uMat (γ v)⁻¹ = 1 := by simp [uMat]
  have hG : ∀ x x', Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) (uMat (γ v) *ᵥ x) (uMat (γ v) *ᵥ x') =
      Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε v) x x' := by
    intro x x'
    rw [Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.hJ_adj (γ v), Matrix.mulVec_mulVec,
      Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul', Matrix.one_mulVec]
  have hYG : uMat y * uMat (γ v) = uMat (γ v) * uMat ((γ v)⁻¹ * y * γ v) := by
    have e1 : y * γ v = γ v * ((γ v)⁻¹ * y * γ v) := by group
    have e2 : uMat (y * γ v) = uMat (γ v * ((γ v)⁻¹ * y * γ v)) := by rw [e1]
    simpa [uMat] using e2
  have hZ : ZX X u u' 1 γ v = RealObj.Zhat (X.B.I.ε v) (fam e z) (fam e z') (uMat (γ v)) := by
    simp only [ZX, frm, famSc_one]; rfl
  have hO := hγ v
  have hsum : (w.1.map Prod.snd).sum = D.R.rS + 1 := w.2.2
  have hZe : ∀ c b : Fin (D.R.rS + 1), RealObj.Zhat (X.B.I.ε v) (fam e z) (fam e z') (uMat (γ v)) c b =
      (-1 : ℂ) ^ (D.R.rS - b.1) * X.B.I.φ v (X.ιE.symm (if c.val = ptPar w.1 b.val then ptSc w.1 b.val else 0)) := by
    intro c b
    have h1 := congrFun (congrFun hO c) b
    simp only [RealObj.ZhatO, ptC, Matrix.map_apply, ptMat, hZ] at h1
    rw [← ptEntry_eq w.1 c.val b.val (by rw [hsum]; exact b.2), ← h1, ← mul_assoc, ← mul_pow]
    norm_num
  have hne : ∀ b : ℕ, b < D.R.rS + 1 → X.B.I.φ v (X.ιE.symm (ptSc w.1 b)) ≠ 0 := by
    intro b hb
    rw [map_ne_zero, map_ne_zero]
    exact ptSc_ne w.1 w.2.1 b (by rw [hsum]; exact hb)
  let π : Fin (D.R.rS + 1) → Fin (D.R.rS + 1) := fun b =>
    ⟨ptPar w.1 b.val, lt_of_lt_of_eq (ptPar_lt w.1 b.val (by rw [hsum]; exact b.2)) hsum⟩
  have hπ : ∀ a, π (π a) = a := fun a => Fin.ext (ptPar_invol w.1 a.val (by rw [hsum]; exact a.2))
  have hP1 : ∀ c b, RealObj.Zhat (X.B.I.ε v) (fam e z) (fam e z') (uMat (γ v)) c b ≠ 0 ↔ c = π b := by
    intro c b
    rw [hZe]
    by_cases h : c.val = ptPar w.1 b.val
    · rw [if_pos h]
      refine ⟨fun _ => Fin.ext h, fun _ => mul_ne_zero (pow_ne_zero _ (by norm_num)) (hne b.val b.2)⟩
    · rw [if_neg h, map_zero, map_zero, mul_zero]
      exact ⟨fun h' => absurd rfl h', fun h' => absurd (congrArg Fin.val h') h⟩
  have hY1 := fix_loc (X.B.I.ε v) e z z' (uMat (γ v)) (uMat (γ v)⁻¹) (uMat y) (uMat ((γ v)⁻¹ * y * γ v))
    hGGi hG hee (hez u) (hez u') π hπ hP1 hy.1.2 hy.2.2 hYG hF hGF
  apply Subtype.ext
  apply Units.ext
  simpa [uMat] using hY1

theorem stVGeo_of_sec (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (hS : StVSec X u u') :
    StVGeo X u u' := by
  exact stVGeo_of_fix_sec X u u' (stVFix_holds X u u') hS

end FixGlob

end Formalism.L2.SG.Pf.Carrier.JointQuot
