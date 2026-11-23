import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2SGPhiOfNeZeroAndLtInfty

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.QuantumDeterminants Formalism.L2.SG.Pf.WFL
open Matrix

set_option linter.unusedVariables false

namespace Formalism.L2.SG.Pf.EquivPf

variable {k r : ℕ}

theorem frame_of_tr {ε : Fin (2 * r + k + 1) → Bool} {Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) :
    IsFrameJ ε (fun a => Q *ᵥ bvec (eI k r a)) (fun a => Q *ᵥ bvec (esI k r a))
      (fun c => Q *ᵥ bvec (wI k r ⟨c.val, by omega⟩)) (Q *ᵥ bvec (wI k r (Fin.last k))) := by
  have hG : ∀ i j, hJ ε (Q *ᵥ bvec i) (Q *ᵥ bvec j) = Hpk k r i j := by
    intro i j
    rw [hJ_QQ ε Q _ hg]
    show star (Pi.single i (1 : ℂ)) ⬝ᵥ (Hpk k r *ᵥ bvec j) = Hpk k r i j
    rw [star_single_dot]
    exact (mat_apply_bvec (Hpk k r) i j).symm
  exact
    { ee := fun a b => by rw [hG, Hpk_ee]
      ff := fun a b => by rw [hG, Hpk_ff]
      ef := fun a b => by rw [hG, Hpk_ef]
      ez := fun a => by rw [hG, Hpk_ew]
      fz := fun a => by rw [hG, Hpk_fw]
      zz := by rw [hG, Hpk_ww, if_pos rfl, if_pos (by simp)]
      ww := fun a b => by
        rw [hG, Hpk_ww]
        by_cases hab : a = b
        · subst hab; rw [if_pos rfl, if_pos rfl, if_neg (by simp only; omega)]
        · rw [if_neg (fun h => hab (Fin.ext (by simpa using congrArg Fin.val h))), if_neg hab]
      ew := fun c a => by rw [hG, Hpk_ew]
      fw := fun c a => by rw [hG, Hpk_fw]
      zw := fun a => by rw [hG, Hpk_ww, if_neg (fun h => by have := congrArg Fin.val h; simp at this; omega)] }

theorem Qm_of_tr (Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Qm (fun a => Q *ᵥ bvec (eI k r a)) (fun a => Q *ᵥ bvec (esI k r a))
      (fun c : Fin k => Q *ᵥ bvec (wI k r ⟨c.val, by omega⟩)) (Q *ᵥ bvec (wI k r (Fin.last k))) = Q := by
  unfold Qm
  ext i j
  simp only [Matrix.of_apply]
  unfold colQ
  split_ifs with h1 h2 h3 <;> simp only [bvec, eI, esI, wI] <;>
    first
    | (simp [Matrix.mulVec_single]; done)
    | (simp [Matrix.mulVec_single]; congr 1; ext; simp <;> omega)
    | (simp [Matrix.mulVec_single_one]; done)
    | (simp [Matrix.mulVec_single_one]; congr 1; ext; simp <;> omega)
    | (simp [Matrix.mulVec, dotProduct, Pi.single_apply]; done)
    | (simp [Matrix.mulVec, dotProduct, Pi.single_apply]; congr 1; ext; simp <;> omega)
    | (simp [Matrix.mulVec_single]; omega)

theorem Qi_of_tr {ε : Fin (2 * r + k + 1) → Bool} {Q Qi : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) :
    Formalism.L2.SG.Pf.WFL.Qi ε (fun a => Q *ᵥ bvec (eI k r a)) (fun a => Q *ᵥ bvec (esI k r a))
      (fun c : Fin k => Q *ᵥ bvec (wI k r ⟨c.val, by omega⟩)) (Q *ᵥ bvec (wI k r (Fin.last k))) = Qi := by
  have h1 := Qi_mul_Qm (frame_of_tr hg)
  rw [Qm_of_tr] at h1
  calc _ = Formalism.L2.SG.Pf.WFL.Qi ε (fun a => Q *ᵥ bvec (eI k r a)) (fun a => Q *ᵥ bvec (esI k r a))
        (fun c : Fin k => Q *ᵥ bvec (wI k r ⟨c.val, by omega⟩)) (Q *ᵥ bvec (wI k r (Fin.last k))) * (Q * Qi) := by
        rw [h2, Matrix.mul_one]
    _ = Qi := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem spanLt_scale {n : ℕ} (e : Fin r → Fin n → ℂ) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (p : ℕ) :
    spanLt (fun a => c a • e a) p = spanLt e p := by
  unfold spanLt
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    have hea : e a = (c a)⁻¹ • (c a • e a) := by rw [smul_smul, inv_mul_cancel₀ (hc a), one_smul]
    rw [SetLike.mem_coe, hea]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)

theorem inN_scale {n : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0)
    (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    InN ε (fun a => c a • e a) z g → InN ε e z g := by
  have hs : ∀ (a : Fin r) (S : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ), c a • x ∈ S ↔ x ∈ S := fun a S x => Submodule.smul_mem_iff S (hc a)
  have hsp : ∀ p, spanLt (fun a => c a • e a) p = spanLt e p := spanLt_scale e c hc
  unfold InN InS
  intro h
  first
    | simpa [hsp, hs, Matrix.mulVec_smul, hc] using h
    | simpa [hsp, hs, Matrix.mulVec_smul, hc, hJ, dotProduct_smul, smul_dotProduct, mul_eq_zero] using h
    | simpa [hsp, hs, Matrix.mulVec_smul, hc, hJ, Matrix.dotProduct_smul, Matrix.smul_dotProduct, mul_eq_zero] using h
    | (unfold hJ at h ⊢; simp only [hsp, hs, Matrix.mulVec_smul] at h ⊢; done)

theorem inN_loc {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) (e : Fin r → Fin n → ℂ) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0)
    (hcolE : ∀ a, Q *ᵥ Pi.single (eI k r a) 1 = c a • e a) (z : Fin n → ℂ)
    (hzB : ∀ i : Fin (2 * r + k + 1), i.val < r ∨ r + k < i.val → (Qi *ᵥ z) i = 0)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r) :
    InN ε e z (Q * m * Qi) := by
  subst hn
  have hF := frame_of_tr hg
  have hz : Qm (fun a => Q *ᵥ bvec (eI k r a)) (fun a => Q *ᵥ bvec (esI k r a))
      (fun c : Fin k => Q *ᵥ bvec (wI k r ⟨c.val, by omega⟩)) (Q *ᵥ bvec (wI k r (Fin.last k))) *ᵥ (Qi *ᵥ z) = z := by
    rw [Qm_of_tr, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  have h := rev_N hF hz hzB hm
  rw [Qm_of_tr, Qi_of_tr h2 hg] at h
  have hE : (fun a => Q *ᵥ bvec (eI k r a)) = fun a => c a • e a := funext fun a => hcolE a
  rw [hE] at h
  exact inN_scale ε e c hc z _ h

theorem fix_loc {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) (e f : Fin r → Fin n → ℂ) (c d : Fin r → ℂ) (hc : ∀ a, c a ≠ 0)
    (hd : ∀ a, d a ≠ 0) (hcolE : ∀ a, Q *ᵥ Pi.single (eI k r a) 1 = c a • e a)
    (hcolF : ∀ a, Q *ᵥ Pi.single (esI k r a) 1 = d a • f a) (z : Fin n → ℂ)
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r (Qi *ᵥ z)) :
    (∀ a, (Q * h * Qi) *ᵥ e a = e a) ∧ (∀ a, (Q * h * Qi) *ᵥ f a = f a) ∧ (Q * h * Qi) *ᵥ z = z := by
  subst hn
  have hF := frame_of_tr hg
  have hz : Qm (fun a => Q *ᵥ bvec (eI k r a)) (fun a => Q *ᵥ bvec (esI k r a))
      (fun c : Fin k => Q *ᵥ bvec (wI k r ⟨c.val, by omega⟩)) (Q *ᵥ bvec (wI k r (Fin.last k))) *ᵥ (Qi *ᵥ z) = z := by
    rw [Qm_of_tr, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  obtain ⟨hE, hFf, hZ⟩ := rev_UW hF hz hh
  rw [Qm_of_tr, Qi_of_tr h2 hg] at hE hFf hZ
  refine ⟨fun a => ?_, fun a => ?_, hZ⟩
  · have := hE a
    change (Q * h * Qi) *ᵥ (Q *ᵥ Pi.single (eI k r a) 1) = Q *ᵥ Pi.single (eI k r a) 1 at this
    rw [hcolE, Matrix.mulVec_smul] at this
    exact smul_right_injective _ (hc a) this
  · have := hFf a
    change (Q * h * Qi) *ᵥ (Q *ᵥ Pi.single (esI k r a) 1) = Q *ᵥ Pi.single (esI k r a) 1 at this
    rw [hcolF, Matrix.mulVec_smul] at this
    exact smul_right_injective _ (hd a) this

theorem inN_scale' {n : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0)
    (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    InN ε e z g → InN ε (fun a => c a • e a) z g := by
  have hs : ∀ (a : Fin r) (S : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ), c a • x ∈ S ↔ x ∈ S := fun a S x => Submodule.smul_mem_iff S (hc a)
  have hsp : ∀ p, spanLt (fun a => c a • e a) p = spanLt e p := spanLt_scale e c hc
  unfold InN InS
  intro h
  first
    | simpa [hsp, hs, Matrix.mulVec_smul, hc] using h
    | simpa [hsp, hs, Matrix.mulVec_smul, hc, hJ, dotProduct_smul, smul_dotProduct, mul_eq_zero] using h
    | simpa [hsp, hs, Matrix.mulVec_smul, hc, hJ, Matrix.dotProduct_smul, Matrix.smul_dotProduct, mul_eq_zero] using h
    | (unfold hJ at h ⊢; simp only [hsp, hs, Matrix.mulVec_smul] at h ⊢; done)

theorem nset_loc {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) (e : Fin r → Fin n → ℂ) (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0)
    (hcolE : ∀ a, Q *ᵥ Pi.single (eI k r a) 1 = c a • e a) (z : Fin n → ℂ)
    {s : Matrix (Fin n) (Fin n) ℂ} (hU : sᴴ * Formalism.REAL.Jm ε * s = Formalism.REAL.Jm ε) (hN : InN ε e z s) :
    Qi * s * Q ∈ Nset k r := by
  subst hn
  have hF := frame_of_tr hg
  have hE : (fun a => Q *ᵥ bvec (eI k r a)) = fun a => c a • e a := funext fun a => hcolE a
  have hN' : InN ε (fun a => Q *ᵥ bvec (eI k r a)) (Q *ᵥ bvec (wI k r (Fin.last k))) s := by
    rw [hE]
    obtain ⟨⟨ha, -⟩, hy⟩ := inN_scale' ε e c hc z s hN
    refine ⟨⟨ha, ?_⟩, hy⟩
    apply hy
    intro a
    rw [← hE]
    exact hF.ez a
  have h := conj_mem_Nset hF ⟨1, by rw [one_smul]⟩ hU hN'
  rwa [Qm_of_tr, Qi_of_tr h2 hg] at h

theorem uw_loc {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) (e f : Fin r → Fin n → ℂ) (c d : Fin r → ℂ)
    (hcolE : ∀ a, Q *ᵥ Pi.single (eI k r a) 1 = c a • e a)
    (hcolF : ∀ a, Q *ᵥ Pi.single (esI k r a) 1 = d a • f a) (z : Fin n → ℂ)
    {s : Matrix (Fin n) (Fin n) ℂ} (hU : sᴴ * Formalism.REAL.Jm ε * s = Formalism.REAL.Jm ε) (he : ∀ a, s *ᵥ e a = e a)
    (hf : ∀ a, s *ᵥ f a = f a) (hz : s *ᵥ z = z) : Qi * s * Q ∈ UWset k r (Qi *ᵥ z) := by
  subst hn
  have hF := frame_of_tr hg
  have hzQ : Qm (fun a => Q *ᵥ bvec (eI k r a)) (fun a => Q *ᵥ bvec (esI k r a))
      (fun c : Fin k => Q *ᵥ bvec (wI k r ⟨c.val, by omega⟩)) (Q *ᵥ bvec (wI k r (Fin.last k))) *ᵥ (Qi *ᵥ z) = z := by
    rw [Qm_of_tr, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  have he' : ∀ a, s *ᵥ (Q *ᵥ bvec (eI k r a)) = Q *ᵥ bvec (eI k r a) := fun a => by
    show s *ᵥ (Q *ᵥ Pi.single (eI k r a) 1) = Q *ᵥ Pi.single (eI k r a) 1
    rw [hcolE, Matrix.mulVec_smul, he]
  have hf' : ∀ a, s *ᵥ (Q *ᵥ bvec (esI k r a)) = Q *ᵥ bvec (esI k r a) := fun a => by
    show s *ᵥ (Q *ᵥ Pi.single (esI k r a) 1) = Q *ᵥ Pi.single (esI k r a) 1
    rw [hcolF, Matrix.mulVec_smul, hf]
  have h := conj_mem_UWset hF hzQ hU he' hf' hz
  rwa [Qm_of_tr, Qi_of_tr h2 hg] at h

theorem psiR_fix_left {n : ℕ} (ε : Fin n → Bool) (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    {H Y : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε) (hf : ∀ a, H *ᵥ f a = f a) :
    psiR ε gg e f z (H * Y) = psiR ε gg e f z Y := by
  have key : ∀ (a : Fin r) (w : Fin n → ℂ), hJ ε (f a) (H *ᵥ w) = hJ ε (f a) w := by
    intro a w
    first
      | (unfold hJ; conv_lhs => rw [← hf a, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH])
      | (unfold hJ; conv_lhs => rw [← hf a, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hH])
      | (unfold hJ; conv_lhs => rw [← hf a, Matrix.star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH])
      | (unfold hJ; done)
  unfold psiR
  congr 3
  unfold rootCoord
  simp only [← Matrix.mulVec_mulVec, key]

section Assembly

open Formalism.L2.SG.Pf.WuDec

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem inUJ_of_UH (C : Choice X θ) (τ : D.what₂.Tau) {x : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (hx : x ∈ UH (Hpk D.R.k D.R.rS)) :
    (C.Q τ * x * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * x * C.Qi τ) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
  obtain ⟨h1, h2, hg, -⟩ := C.isT τ
  have hx' : xᴴ * Hpk D.R.k D.R.rS * x = Hpk D.R.k D.R.rS := hx
  calc (C.Q τ * x * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * x * C.Qi τ)
      = (C.Qi τ)ᴴ * (xᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * x) * C.Qi τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [hg, hx', qiHqi _ h2 hg]

theorem equivClause (C : Choice X θ) : Formalism.L2.SG.Pf.LocF.EquivClause C := by
  intro u τ h hh m hm g hgU
  set v := vOf X τ
  obtain ⟨h1, h2, hgQ, hcol⟩ := C.isT τ
  have hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0 := fun a => pow_ne_zero _ (frS_ne D)
  have hd : ∀ a : Fin D.R.rS, (star (frS D ^ (D.R.rS - (a : ℕ))))⁻¹ ≠ 0 := fun a => by
    rw [Ne, inv_eq_zero, star_eq_zero]; exact hc a
  have hzB := (Formalism.L2.SG.Pf.zTr C u τ).1
  have hhU : h ∈ UH (Hpk D.R.k D.R.rS) := hh.1
  have hmU : m ∈ UH (Hpk D.R.k D.R.rS) := hm.1
  set H := Formalism.L2.SG.Pf.GoodS.toUJn (C.Q τ * h * C.Qi τ) (inUJ_of_UH C τ hhU)
  set M := Formalism.L2.SG.Pf.GoodS.toUJn (C.Q τ * m * C.Qi τ) (inUJ_of_UH C τ hmU)
  set G := Formalism.L2.SG.Pf.GoodS.toUJn (C.Q τ * g * C.Qi τ) (inUJ_of_UH C τ hgU)
  obtain ⟨hfe, hff, hfz⟩ := fix_loc (n_eq' X) (X.B.I.ε v) (C.Q τ) (C.Qi τ) h1 h2 hgQ
    (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) _ _ hc hd
    (fun a => (hcol a a rfl).1) (fun a => (hcol a a rfl).2) (rv X.B.I v (X.zR u)) hh
  have hH : H ∈ Hloc X u v := by
    rintro y ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hy)
    · exact hfe a
    · exact hff a
    · rw [Set.mem_singleton_iff.mp hy]; exact hfz
  have hM : M ∈ Nloc X u v :=
    inN_loc (n_eq' X) (X.B.I.ε v) (C.Q τ) (C.Qi τ) h1 h2 hgQ (fun a => rv X.B.I v (X.eR a)) _ hc
      (fun a => (hcol a a rfl).1) (rv X.B.I v (X.zR u)) hzB hm
  have hM'' : H * M * H⁻¹ ∈ Nloc X u v := by
    show InN _ _ _ (uMat H * uMat M * uMat H⁻¹)
    exact Formalism.L2.SG.Pf.WFL.HNL.inN_conj H.2 (Formalism.L2.SG.Pf.WFL.HNL.uMat_mul_inv H)
      (Formalism.L2.SG.Pf.WFL.HNL.uMat_inv_mul H) hfe hfz hM
  have key := locEquiv X u v (H * M * H⁻¹) hM'' H hH G
  have e1 : H * M * H⁻¹ * H * G = H * M * G := by group
  have e2 : H * M * H⁻¹ * H = H * M := by group
  rw [e1, e2] at key
  have hW : wT C u τ (h * m * g) = X.Wloc u v (H * M * G) := by
    rw [← Formalism.L2.SG.Pf.WuBL.wT_at C u τ (H * M * G)]
    congr 1
    show h * m * g = C.Qi τ * (C.Q τ * h * C.Qi τ * (C.Q τ * m * C.Qi τ) * (C.Q τ * g * C.Qi τ)) * C.Q τ
    have hQQ : ∀ Y : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
        C.Qi τ * (C.Q τ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hQQ, h1, Matrix.mul_one]
  have hG : X.Wloc u v G = wT C u τ g := by
    rw [← Formalism.L2.SG.Pf.WuBL.wT_at C u τ G]
    congr 1
    show C.Qi τ * (C.Q τ * g * C.Qi τ) * C.Q τ = g
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
  have hpsi : psiV X u v (uMat (H * M)) = psiS D (zB X (C.Qi τ) u τ) m := by
    show psiR (X.B.I.ε v) X.B.g _ _ _ (uMat H * uMat M) = _
    rw [psiR_fix_left (H := uMat H) (Y := uMat M) _ _ _ _ _ H.2 hff]
    exact Formalism.L2.SG.Pf.psiTr C u τ m hm
  have hpi : matW X.B.I (X.wfr u v) v (single X v H) =
      Formalism.L2.SG.RealObj.matQ (X.B.I.ε v) (X.wfr u v) (C.Q τ * h * C.Qi τ) := by
    funext a b
    simp only [matW, Formalism.L2.SG.Pf.WuDec.single, Function.update_self]
    rfl
  rw [hW, key, hpsi, hpi, hG]
  rfl

theorem local_equivalence_all : Formalism.L2.SG.Pf.LocF.EquivAll := fun D X θ C => equivClause C

end Assembly

end Formalism.L2.SG.Pf.EquivPf
