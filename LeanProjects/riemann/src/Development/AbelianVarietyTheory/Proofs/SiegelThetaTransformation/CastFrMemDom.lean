import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

section Cast

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X' X : Data E r}

theorem SameSp.dmin_castFr (h : SameSp X' X) (x : Frame X'.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (castFr h.psi x) τ i = dmin X'.Gm x ⟨τ.1, h.psi.ge τ.2⟩ i := by
  rw [← h.gm]
  rfl

theorem SameSp.castFr_mem_dom (h : SameSp X' X) {x : Frame X'.Ψ r} (hx : x ∈ X'.dom) :
    castFr h.psi x ∈ X.dom := by
  have hx' : ∀ τ : X'.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X'.p0 i * (dmin X'.Gm x τ i).re := hx
  show ∀ τ : X.Ψ, (mat (castFr h.psi x) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (castFr h.psi x) τ i).re
  intro τ
  obtain ⟨hdet, hpos⟩ := hx' ⟨τ.1, h.psi.ge τ.2⟩
  refine ⟨hdet, fun i => ?_⟩
  rw [h.dmin_castFr, ← h.p0]
  exact hpos i

theorem SameSp.EF_eq (h : SameSp X' X) (u v : Fin r → E) : EF X' u v = EF X u v := by
  rw [EF_def, EF_def, h.gm, h.ka]

private theorem GL_inv_mulVec_mulVec {K : Type} [Field K] {n : ℕ} (ga : GL (Fin n) K) (u : Fin n → K) :
    ((ga⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ((ga : Matrix (Fin n) (Fin n) K) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

private theorem GL_mulVec_inv_mulVec {K : Type} [Field K] {n : ℕ} (ga : GL (Fin n) K) (u : Fin n → K) :
    (ga : Matrix (Fin n) (Fin n) K) *ᵥ (((ga⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

private theorem mem_mapL_iff (ga : GL (Fin r) E) (L : Lt E r) (v : Fin r → E) :
    v ∈ mapL ga L ↔ ∃ u ∈ L, v = (ga : Matrix (Fin r) (Fin r) E) *ᵥ u := by
  unfold mapL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by simp [Matrix.toLin'_apply]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by simp [Matrix.toLin'_apply]⟩

private theorem EF_mulVec_of_isUn {Y : Data E r} {ga : GL (Fin r) E} (hga : IsUn Y ga) (u v : Fin r → E) :
    EF Y ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = EF Y u v := by
  rw [EF_def, EF_def, hga u v]

end Cast

theorem anFib_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X' X : Data E r) (h : SameSp X' X) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X'.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X' bas' idx' e x L y) (ga : GL (Fin r) E), IsSympl X' bas' → IsSympl X bas → x ∈ X'.dom → SelfD X' L → IsUn X ga → (∀ v, pv X' idx' x v = pv X idx (castFr h.psi x) v) → (∀ j, rowType X' (idx' j) = rowType X (idx j)) → lact ga (castFr h.psi x) ∈ X.dom ∧ (IsUnitFr X' x → IsUnitFr X (lact ga (castFr h.psi x))) ∧ SelfD X (mapL ga L) ∧ ∃ A' : AnFib X bas idx e (lact ga (castFr h.psi x)) (mapL ga L) y, (∀ θ, A.Reads 1 y.s θ → A'.Reads 1 y.s θ) ∧ (∀ θ, MeanOne X' bas' idx' x L θ → MeanOne X bas idx (lact ga (castFr h.psi x)) (mapL ga L) θ) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mvMap ga mk) := by
  intro E _ _ _ H Dw l Xo c _ r g X' X h bas' idx' bas idx e x L y A ga hs' hs hxm hL hga hpv hrow
  have hx₀ : castFr h.psi x ∈ X.dom := h.castFr_mem_dom hxm
  obtain ⟨-, -, L3, -, -, -, -, L8⟩ := hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ _ hx₀
  obtain ⟨-, -, L3', -, -, -, -, -⟩ := hx_laws E r X' g bas' idx' 0 hs' ⟨0, rfl⟩ x hxm
  obtain ⟨hdom1, hpv1, hunit1, hhx1⟩ := L8 ga hga
  have pvT : ∀ u, pv X idx (lact ga (castFr h.psi x)) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) =
      pv X' idx' x u := fun u => (hpv1 u).trans (hpv u).symm
  have hxeq : ∀ z w, hx X bas idx (castFr h.psi x) z w = hx X' bas' idx' x z w := by
    intro z w
    rw [hx_eq_hermForm idx, hx_eq_hermForm idx']
    have key := hermForm_eq_of_im (ThFr.Hm X bas idx (castFr h.psi x)) (ThFr.Hm X' bas' idx' x) 1 1
      (Set.range (pv X idx (castFr h.psi x))) (span_range_pv idx hs hx₀) ?_ z w
    · simpa only [_root_.one_mul] using key
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      simp only [_root_.one_mul]
      rw [← hx_eq_hermForm idx, ← hx_eq_hermForm idx', L3 a b, ← hpv a, ← hpv b, L3' a b, h.EF_eq]
  have hxT : ∀ z w, hx X bas idx (lact ga (castFr h.psi x)) z w = hx X' bas' idx' x z w :=
    fun z w => (hhx1 z w).trans (hxeq z w)
  have unit0 : IsUnitFr X' x → IsUnitFr X (castFr h.psi x) := by
    unfold IsUnitFr
    intro hu τ i
    rw [h.dmin_castFr]
    exact hu _ i
  have hSD : SelfD X (mapL ga L) := by
    unfold SelfD at hL ⊢
    obtain ⟨hfg, hmem⟩ := hL
    refine ⟨hfg.map _, fun v => ?_⟩
    rw [mem_mapL_iff]
    constructor
    · rintro ⟨u, hu, rfl⟩ w hw
      obtain ⟨u', hu', rfl⟩ := (mem_mapL_iff ga L w).1 hw
      obtain ⟨k, hk⟩ := (hmem u).1 hu u' hu'
      exact ⟨k, by rw [EF_mulVec_of_isUn hga, ← h.EF_eq]; exact hk⟩
    · intro hv
      refine ⟨((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v, ?_, (GL_mulVec_inv_mulVec ga v).symm⟩
      rw [hmem]
      intro u' hu'
      obtain ⟨k, hk⟩ := hv _ ((mem_mapL_iff ga L _).2 ⟨u', hu', rfl⟩)
      refine ⟨k, ?_⟩
      rw [h.EF_eq, ← EF_mulVec_of_isUn hga (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) u',
        GL_mulVec_inv_mulVec]
      exact hk
  have hT : ∀ z, (∃ v ∈ L, z = pv X' idx' x v) ↔
      ∃ v ∈ mapL ga L, z = pv X idx (lact ga (castFr h.psi x)) v := by
    intro z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, (mem_mapL_iff ga L _).2 ⟨u, hu, rfl⟩, (pvT u).symm⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
      exact ⟨u, hu, pvT u⟩
  refine ⟨hdom1, fun hu => hunit1 (unit0 hu), hSD, ?_⟩
  have hlin : ∀ (a : 𝓞 E) (z : Fin g → ℂ),
      A.ex (fun j => rowType X (idx j) (a : E) * z j) = A.ex z ≫ Xo.univ.t.act.act a := by
    intro a z
    have hfun : (fun j => rowType X (idx j) (a : E) * z j) =
        (fun j => rowType X' (idx' j) (a : E) * z j) := funext fun j => by rw [hrow]
    rw [hfun]
    exact A.ex_lin a z
  have hnorm : ∀ v ∈ mapL ga L, ‖A.χ (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)‖ = 1 := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
    rw [GL_inv_mulVec_mulVec]
    exact A.χ_norm u hu
  refine ⟨
    { ex := A.ex
      ex_add := A.ex_add
      ex_onto := A.ex_onto
      ex_ker := fun z => (A.ex_ker z).trans (hT z)
      ex_lin := hlin
      hol := A.hol
      der := A.der
      fr := A.fr
      fr_hol := A.fr_hol
      fr_ne := A.fr_ne
      fr_g := A.fr_g
      fr_0 := A.fr_0
      χ := fun v => A.χ (((ga⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)
      χ_norm := hnorm
      fr_per := ?_ }, fun θ hθ => hθ, ?_, ?_⟩
  · intro v hv j z hz
    obtain ⟨u, hu, rfl⟩ := (mem_mapL_iff ga L v).1 hv
    simp only [GL_inv_mulVec_mulVec, pvT, hxT]
    exact A.fr_per u hu j z hz
  · intro θ hθ
    unfold MeanOne at hθ ⊢
    obtain ⟨Ag, Fd, hA, hFd, hint⟩ := hθ
    refine ⟨Ag, Fd, fun z => (hA z).trans (hT z), hFd, ?_⟩
    simp only [hxT]
    exact hint
  · intro mk hmk
    unfold AnFib.Marked at hmk ⊢
    intro a ha
    rw [hmk a ha]
    show A.ex _ = A.ex _
    congr 1
    have hmv : mvMap ga mk a = (ga : Matrix (Fin r) (Fin r) E) *ᵥ mk a := by
      simp [mvMap, Matrix.toLin'_apply]
    rw [hmv, ← Matrix.mulVec_smul, pvT]

end GlobalTheory.Dict
