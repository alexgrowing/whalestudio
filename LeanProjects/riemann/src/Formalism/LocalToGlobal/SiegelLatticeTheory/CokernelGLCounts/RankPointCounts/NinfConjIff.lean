import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovariantRepresentation

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.KappaOffDiagonal

open Matrix

namespace Formalism.L2.SG.CovariantRepresentation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {n r : ℕ}

theorem hJ_unitary (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ) (hU : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.REAL.Jm ε)
    (x y : Fin n → ℂ) : hJ ε (P *ᵥ x) (P *ᵥ y) = hJ ε x y := by
  delta hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hU]

theorem fix_span (e : Fin r → Fin n → ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (he : ∀ a, Q *ᵥ e a = e a) (k : ℕ) :
    ∀ x ∈ spanLt e k, Q *ᵥ x = x := by
  delta spanLt
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    exact he a
  | zero => exact Matrix.mulVec_zero Q
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz]
  | smul c y _ hy => rw [Matrix.mulVec_smul, hy]

theorem inN_conj (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (P Q g : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (hU : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.REAL.Jm ε) (he : ∀ a, P *ᵥ e a = e a) (hz : P *ᵥ z = z)
    (hg : InN ε e z g) : InN ε e z (Q * g * P) := by
  have hQv' : ∀ v, Q *ᵥ (P *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  have hQv : ∀ v, P *ᵥ v = v → Q *ᵥ v = v := fun v hv =>
    calc Q *ᵥ v = Q *ᵥ (P *ᵥ v) := by rw [hv]
      _ = v := hQv' v
  have hQe : ∀ a, Q *ᵥ e a = e a := fun a => hQv (e a) (he a)
  have key : ∀ (v : Fin n → ℂ) (k : ℕ), P *ᵥ v = v → (g - 1) *ᵥ v ∈ spanLt e k →
      (Q * g * P - 1) *ᵥ v ∈ spanLt e k := by
    intro v k hv hw
    have h : (Q * g * P - 1) *ᵥ v = Q *ᵥ ((g - 1) *ᵥ v) := by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_sub, hQv v hv]
    rw [h, fix_span e Q hQe k _ hw]
    exact hw
  obtain ⟨⟨h1a, h1b⟩, h2⟩ := hg
  refine ⟨⟨fun a => key (e a) a (he a) (h1a a), key z r hz h1b⟩, fun y hy => ?_⟩
  have hy' : ∀ a, hJ ε (e a) (P *ᵥ y) = 0 := fun a =>
    calc hJ ε (e a) (P *ᵥ y) = hJ ε (P *ᵥ e a) (P *ᵥ y) := by rw [he a]
      _ = hJ ε (e a) y := hJ_unitary ε P hU (e a) y
      _ = 0 := hy a
  have hw := h2 (P *ᵥ y) hy'
  have h : (Q * g * P - 1) *ᵥ y = Q *ᵥ ((g - 1) *ᵥ (P *ᵥ y)) := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, hQv' y]
  rw [h, fix_span e Q hQe r _ hw]
  exact hw

end Mat

section Grp

variable {D : D7} (X : HidaSetting D)

theorem fix_inv (s : X.B.I.Ginf) {v : InfinitePlace X.B.I.F} {x : Fin X.B.I.n → ℂ} (hx : uMat (s v) *ᵥ x = x) :
    uMat (s⁻¹ v) *ᵥ x = x := by
  have h1 : uMat (s⁻¹ v) * uMat (s v) = 1 := by
    delta uMat
    simp
  calc uMat (s⁻¹ v) *ᵥ x = uMat (s⁻¹ v) *ᵥ (uMat (s v) *ᵥ x) := by rw [hx]
    _ = x := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem ninf_conj (u : D.what₂.Word) (s : X.B.I.Ginf)
    (he : ∀ v a, uMat (s v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz : ∀ v, uMat (s v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u))
    {r : X.B.I.Ginf} (hr : r ∈ X.NinfU u) : s⁻¹ * r * s ∈ X.NinfU u := by
  dsimp [HidaSetting.NinfU, Ninf] at hr ⊢
  intro v
  have h1 : uMat (s⁻¹ v) * uMat (s v) = 1 := by
    delta uMat
    simp
  have hmul : uMat ((s v)⁻¹ * r v * s v) = uMat (s⁻¹ v) * uMat (r v) * uMat (s v) := by
    delta uMat
    simp
  have hU : (uMat (s v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (s v) = Formalism.REAL.Jm (X.B.I.ε v) := by
    delta uMat
    first
    | exact (s v).2
    | exact (s v).1.2
    | simpa using (s v).2
  rw [hmul]
  exact inN_conj _ _ _ (uMat (s v)) (uMat (s⁻¹ v)) (uMat (r v)) h1 hU (he v) (hz v) (hr v)

theorem ninf_conj_iff (u : D.what₂.Word) (s : X.B.I.Ginf)
    (he : ∀ v a, uMat (s v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz : ∀ v, uMat (s v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)) (r : X.B.I.Ginf) :
    r ∈ X.NinfU u ↔ s⁻¹ * r * s ∈ X.NinfU u := by
  constructor
  · exact ninf_conj X u s he hz
  · intro h
    have he' : ∀ v a, uMat (s⁻¹ v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
      fun v a => fix_inv X s (he v a)
    have hz' : ∀ v, uMat (s⁻¹ v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) :=
      fun v => fix_inv X s (hz v)
    have h2 := ninf_conj X u s⁻¹ he' hz' h
    simpa [mul_assoc] using h2

end Grp

open Formalism.L2.SG.TermOp.Vanish in

theorem fixNormC : FixNormC := by
  intro D X Y u u' t h hh r
  have hfe : ∀ v a, uMat (h v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
    fun v a => fix_rv hh (basis_mem_fixedSubspace t.rep a) v
  have hfz : ∀ v, uMat (h v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) :=
    fun v => fix_rv hh (zu_mem_fixedSubspaceOfRepresentative t.rep) v
  have hfe' : ∀ v a, uMat ((t.pt.1⁻¹ * h * t.pt.1) v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
    fun v a => fix'_rv hh (ge_mem_fixedSubspace t.rep a) v
  have hfz' : ∀ v, uMat ((t.pt.1⁻¹ * h * t.pt.1) v) *ᵥ rv X.B.I v (X.zR u') = rv X.B.I v (X.zR u') :=
    fun v => fix'_rv hh (gz_mem_fixedSubspace t.rep) v
  have e : t.pt.1⁻¹ * (h⁻¹ * r * h) * t.pt.1 =
      (t.pt.1⁻¹ * h * t.pt.1)⁻¹ * (t.pt.1⁻¹ * r * t.pt.1) * (t.pt.1⁻¹ * h * t.pt.1) := by group
  show (r ∈ X.NinfU u ∧ t.pt.1⁻¹ * r * t.pt.1 ∈ X.NinfU u') ↔
    (h⁻¹ * r * h ∈ X.NinfU u ∧ t.pt.1⁻¹ * (h⁻¹ * r * h) * t.pt.1 ∈ X.NinfU u')
  rw [e, ← ninf_conj_iff X u h hfe hfz r, ← ninf_conj_iff X u' _ hfe' hfz' (t.pt.1⁻¹ * r * t.pt.1)]

end Formalism.L2.SG.CovariantRepresentation
