import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatGlueLatIffDual

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GluedCmp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Algebra

variable {A : Type} [CommRing A] {n k : ℕ} (m : Matrix (Fin n) (Fin k) A) (z : Fin n → A) {e t T : A}

theorem unit_fwd (he : e * e = e) (ht : t * T = 1) (x f : Fin k → A) (a : A) :
    e • (m *ᵥ (x + a • f) + (a * t) • z) = m *ᵥ (e • x + (a * (e * t)) • T • f) + (a * (e * t) * e) • z ∧
      e • (e • x + (a * (e * t)) • T • f) = e • x + (a * (e * t)) • T • f := by
  have h1 : a * (e * t) * e = e * (a * t) := by linear_combination (a * t) * he
  have h2 : a * (e * t) * T = e * a := by linear_combination (a * e) * ht
  rw [h1, smul_smul (a * (e * t)) T f, h2]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_smul, smul_add, smul_smul]
  · simp only [smul_add, smul_smul, ← mul_assoc, he]

theorem unit_bwd (he : e * e = e) (ht : t * T = 1) (x f : Fin k → A) (hx : e • x = x) (a : A) :
    m *ᵥ x + (a * e) • z = m *ᵥ ((x - (a * e) • T • f) + (a * e * T) • f) + (a * e * T * t) • z ∧
      e • (m *ᵥ x + (a * e) • z) = m *ᵥ x + (a * e) • z := by
  have h1 : a * e * T * t = a * e := by linear_combination (a * e) * ht
  have h2 : e * (a * e) = a * e := by linear_combination a * he
  refine ⟨?_, ?_⟩
  · rw [h1, smul_smul (a * e) T f, sub_add_cancel]
  · rw [smul_add, ← Matrix.mulVec_smul, hx, smul_smul, h2]

theorem glue_fwd (he : e * e = e) (x f g : Fin k → A) (hg : e • g = g) (a : A) :
    e • (m *ᵥ (x + a • f) + (a * t) • z) = m *ᵥ (e • x - a • (g - e • f)) + a • ((t * e) • z + m *ᵥ g) ∧
      e • (e • x - a • (g - e • f)) = e • x - a • (g - e • f) := by
  have hs : e • (g - e • f) = g - e • f := by rw [smul_sub, hg, smul_smul, he]
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add, smul_sub, smul_smul]
    module
  · rw [smul_sub e (e • x) (a • (g - e • f)), smul_smul e e x, he, smul_comm e a (g - e • f), hs]

theorem glue_bwd (he : e * e = e) (x f g : Fin k → A) (hx : e • x = x) (hg : e • g = g) (a : A) :
    m *ᵥ x + a • ((t * e) • z + m *ᵥ g) = m *ᵥ ((x + a • (g - e • f)) + (a * e) • f) + (a * e * t) • z ∧
      e • (m *ᵥ x + a • ((t * e) • z + m *ᵥ g)) = m *ᵥ x + a • ((t * e) • z + m *ᵥ g) := by
  have h2 : e * (t * e) = t * e := by linear_combination t * he
  refine ⟨?_, ?_⟩
  · simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_add, smul_sub, smul_smul]
    module
  · rw [smul_add e (m *ᵥ x), ← Matrix.mulVec_smul m e x, hx, smul_comm e a, smul_add e ((t * e) • z),
      smul_smul e (t * e) z, h2, ← Matrix.mulVec_smul m e g, hg]

theorem idem_smul_smul (he : e * e = e) (y : Fin n → A) : e • e • y = e • y := by
  rw [smul_smul, he]

end Algebra

variable {D : D7} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word} {L₀ : Lat X} {x₀ : X.V}

theorem fg_glueLat (h : L₀.FG) : (glueLat Y X ι z u L₀ x₀).FG := by
  unfold glueLat
  refine Submodule.FG.sup ?_ (Submodule.fg_span_singleton _)
  refine Submodule.FG.map _ ?_
  rw [show (Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E) =
      (((Formalism.L2.Herm.crd X).restrictScalars (𝓞 D.host.E) : X.V ≃ₗ[𝓞 D.host.E] _) : X.V →ₗ[𝓞 D.host.E] _) from rfl,
    Submodule.comap_equiv_eq_map_symm]
  exact h.map _

theorem cmp_unit (hg : IsGlueVec X u L₀ (vA X x₀)) {w : Pl D.host.E}
    (hw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      ∃ x, InCmp (idem w) L₀ x ∧ ∃ a ∈ OA D, y = mA Y X ι *ᵥ x + (a * idem w) • vA Y z := by
  have he := idem_mul_self w
  have ht := inc_inv_mul u
  have het : idem w * inc D (Tu D u)⁻¹ ∈ OA D := (idem_mul_inv_mem_iff u w).2 hw
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hey⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    obtain ⟨h1, h2⟩ := unit_fwd (mA Y X ι) (vA Y z) he ht x (vA X x₀) a
    refine ⟨idem w • x + (a * (idem w * inc D (Tu D u)⁻¹)) • inc D (Tu D u) • vA X x₀,
      ⟨add_mem_hat (smul_mem_hat hew hx) (smul_mem_hat (mul_mem ha het) hg.mul_mem), h2⟩,
      a * (idem w * inc D (Tu D u)⁻¹), mul_mem ha het, ?_⟩
    rw [← hey, h1]
  · rintro ⟨x, ⟨hx, hex⟩, a, ha, rfl⟩
    obtain ⟨h1, h2⟩ := unit_bwd (mA Y X ι) (vA Y z) he ht x (vA X x₀) hex a
    refine ⟨?_, h2⟩
    rw [h1]
    exact (mem_hat_glueLat _).2 ⟨_, sub_mem_hat hx (smul_mem_hat (mul_mem ha hew) hg.mul_mem), _,
      mul_mem (mul_mem ha hew) (inc_Tu_mem u), rfl⟩

theorem cmp_glue {w : Pl D.host.E} {g : Fin X.rank → EAf D} (h1 : idem w • g = g)
    (h2 : g - idem w • vA X x₀ ∈ hat L₀) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      ∃ x, InCmp (idem w) L₀ x ∧ ∃ a ∈ OA D,
        y = mA Y X ι *ᵥ x + a • ((inc D (Tu D u)⁻¹ * idem w) • vA Y z + mA Y X ι *ᵥ g) := by
  have he := idem_mul_self w
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hey⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    obtain ⟨k1, k2⟩ := glue_fwd (mA Y X ι) (vA Y z) (t := inc D (Tu D u)⁻¹) he x (vA X x₀) g h1 a
    refine ⟨idem w • x - a • (g - idem w • vA X x₀),
      ⟨sub_mem_hat (smul_mem_hat hew hx) (smul_mem_hat ha h2), k2⟩, a, ha, ?_⟩
    rw [← hey, k1]
  · rintro ⟨x, ⟨hx, hex⟩, a, ha, rfl⟩
    obtain ⟨k1, k2⟩ := glue_bwd (mA Y X ι) (vA Y z) (t := inc D (Tu D u)⁻¹) he x (vA X x₀) g hex h1 a
    refine ⟨?_, k2⟩
    rw [k1]
    exact (mem_hat_glueLat _).2 ⟨_, add_mem_hat hx (smul_mem_hat ha h2), _, mul_mem ha hew, rfl⟩

theorem cmp_conj (h : IsLine Y X ι z u) (hg : IsGlueVec X u L₀ (vA X x₀)) (w : Pl D.host.E) (y : Fin Y.rank → EAf D) :
    InCmp (cjA D (idem w)) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y ↔
      cjA D (idem w) • y = y ∧ (∃ (x : Fin X.rank → EAf D) (a : EAf D), y = mA Y X ι *ᵥ x + a • vA Y z) ∧
        ∀ y', InCmp (idem w) (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀)) y' → hA Y y' y ∈ OA D := by
  have hew := idem_mem w
  unfold InCmp
  constructor
  · rintro ⟨hy, hcy⟩
    obtain ⟨x, hx, a, ha, rfl⟩ := (mem_hat_glueLat y).1 hy
    refine ⟨hcy, ⟨x + a • vA X x₀, a * inc D (Tu D u)⁻¹, rfl⟩, ?_⟩
    rintro y' ⟨hy', -⟩
    exact (mem_hat_glueLat_iff_dual h hg _ _).1 hy y' hy'
  · rintro ⟨hcy, ⟨x, a, rfl⟩, hdual⟩
    refine ⟨(mem_hat_glueLat_iff_dual h hg x a).2 ?_, hcy⟩
    intro y'' hy''
    have key : hA Y y'' (mA Y X ι *ᵥ x + a • vA Y z) =
        hA Y (idem w • y'') (mA Y X ι *ᵥ x + a • vA Y z) := by
      conv_lhs => rw [← hcy]
      rw [hA_smul_right, hA_smul_left, cjA_cjA]
    rw [key]
    exact hdual _ ⟨smul_mem_hat hew hy'', idem_smul_smul (idem_mul_self w) y''⟩

theorem isGlued_glueLat : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V)
    (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V) (f₀ : Pl D.host.E → Fin X.rank → EAf D),
    Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) →
    (∀ w : Pl D.host.E, π ∈ w.asIdeal → idem w • f₀ w = f₀ w ∧ f₀ w - idem w • vA X x₀ ∈ hat L₀) →
    IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
  intro D u π Y X ι z h L₀ x₀ f₀ hL hg hf
  unfold IsGlued
  refine ⟨fg_glueLat hL.fg, ?_, ?_⟩
  · intro w e he hw y
    obtain rfl := eq_idem he
    exact cmp_unit hg hw y
  · intro w e he hπ
    obtain rfl := eq_idem he
    exact ⟨fun y => cmp_glue (hf w hπ).1 (hf w hπ).2 y, cmp_conj h hg w⟩

end GlobalTheory.GluedCmp

end
