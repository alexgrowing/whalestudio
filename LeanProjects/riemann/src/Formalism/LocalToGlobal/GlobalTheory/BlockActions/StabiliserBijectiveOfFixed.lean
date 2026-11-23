import Formalism.LocalToGlobal.GlobalTheory.BlockActions.StabRestrict
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassInjectiveOfDegree

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def StabFix (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ (c : (D.fm u).clsP) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)),
    γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range →
    ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1) *ᵥ Tf.til.z0 = Tf.til.z0

theorem span_with_orthogonal_vector (Tf : FormsTiedSym D u Ch chOf) :
    ∀ y, ∃ (x : Fin (D.R.N D.R.m - 1) → D.host.E) (s : D.host.E), y = iXc D x + s • Tf.til.z0 := by
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have ha0 : a ≠ 0 := by
    intro h0
    have hzz := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [ha, h0, zero_smul] at hzz
    apply hT0; rw [← hzz]; simp [hform]
  intro y
  obtain ⟨x, s, hy⟩ := span_iXc_zc D y
  exact ⟨x, s / a, by rw [hy, ha, smul_smul, div_mul_cancel₀ s ha0]⟩

theorem ext_of_fix (Tf : FormsTiedSym D u Ch chOf) (Γ : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E)
    (hΓ : cT (sigD D : D.host.E →+* D.host.E) Γ * gramN D D.R.m le_rfl * Γ = gramN D D.R.m le_rfl)
    (hfix : Γ *ᵥ Tf.til.z0 = Tf.til.z0) :
    ∃ δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E,
      IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ ∧
      ∀ x y, hform (sigD D : D.host.E →+* D.host.E) (gramP D) (δ *ᵥ x) (δ *ᵥ y) =
        hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y := by
  have hC := crdFacts_of Tf
  have hTp : ((D.mem u).A.T : ℕ).Prime := (D.mem u).A.T_prime
  set σ : D.host.E →+* D.host.E := (sigD D : D.host.E →+* D.host.E) with hσdef
  set J := gramN D D.R.m le_rfl with hJ
  set z0 := Tf.til.z0 with hz0
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  rw [← hz0] at ha
  have hzz : hform σ J z0 z0 = (((D.mem u).A.T : ℕ) : D.host.E) := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have horth : ∀ x, hform σ J (iXc D x) z0 = 0 ∧ hform σ J z0 (iXc D x) = 0 := fun x => by
    rw [ha, hform_smul_right, hform_smul_left, (hC.orth x).1, (hC.orth x).2]; simp
  have hγ : ∀ x y, hform σ J (Γ *ᵥ x) (Γ *ᵥ y) = hform σ J x y := fun x y => hform_UJ σ J Γ hΓ x y
  obtain ⟨δ, hδ, hδi⟩ := fix_restrict σ J (gramP D) (iXc D) (iXc_injective D) z0 hC.iso horth (span_with_orthogonal_vector Tf)
    (by rw [hzz]; exact hT0) Γ hγ hfix
  refine ⟨δ, ⟨?_, ?_⟩, hδi⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply, ← mulVec_mulVec]
    show Γ *ᵥ ((iXm D).map (RingHom.id D.host.E) *ᵥ x) = (iXm D).map (RingHom.id D.host.E) *ᵥ (δ *ᵥ x)
    have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
    rw [hm, iXm, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hδ]
  · have : (fun a => (RingHom.id D.host.E) (z0 a)) = z0 := rfl
    rw [this]; exact hfix

theorem ext_unique (Tf : FormsTiedSym D u Ch chOf) {δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E}
    {Γ1 Γ2 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E}
    (h1 : IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ1) (h2 : IsExt D Tf.til.z0 (RingHom.id D.host.E) δ Γ2) : Γ1 = Γ2 := by
  have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
  have hz : (fun a => (RingHom.id D.host.E) (Tf.til.z0 a)) = Tf.til.z0 := rfl
  obtain ⟨a1, b1⟩ := h1
  obtain ⟨a2, b2⟩ := h2
  rw [hm] at a1 a2
  rw [hz] at b1 b2
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro y
  simp only [Matrix.toLin'_apply]
  obtain ⟨x, s, rfl⟩ := span_with_orthogonal_vector Tf y
  have hx : iXc D x = iXm D *ᵥ x := by simp only [iXm, LinearMap.toMatrix'_mulVec]
  rw [hx, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, b1, b2, mulVec_mulVec, mulVec_mulVec, a1, a2]

set_option maxHeartbeats 4000000 in

theorem stab_back (Tf : FormsTiedSym D u Ch chOf) (hF : StabFix Tf) (c : (D.fm u).clsP) :
    ∃ g : (D.mem u).C.stab D.R.m ((D.fm u).til c) → (D.fm u).stabilizer₂ c, Function.Injective g := by
  set Km := Tf.cls D.R.m le_rfl (Or.inr rfl) with hKm
  have key : ∀ s : (D.mem u).C.stab D.R.m ((D.fm u).til c), ∃ (s' : (D.fm u).stabilizer₂ c)
      (δ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E),
      IsExt D Tf.til.z0 (RingHom.id D.host.E) δ
        ((Tf.til.ga c).1.1 * (Km.stabI ((D.fm u).til c) s).1.1 * ((Tf.til.ga c)⁻¹).1.1) ∧
      (Tf.clsP.stabI c s').1.1 = δ := by
    intro s
    set γ := Km.stabI ((D.fm u).til c) s with hγ
    have hU : cT (sigD D : D.host.E →+* D.host.E) ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1) *
        gramN D D.R.m le_rfl * ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1) = gramN D D.R.m le_rfl := by
      have h0 := (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).2
      have e : (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 =
          (Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1 := by
        simp only [Subgroup.coe_mul, Units.val_mul]
      have h1 : cT (sigD D : D.host.E →+* D.host.E) (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 *
          gramN D D.R.m le_rfl * (Tf.til.ga c * γ * (Tf.til.ga c)⁻¹).1.1 = gramN D D.R.m le_rfl := h0
      rwa [e] at h1
    obtain ⟨δ, hδE, hδi⟩ := ext_of_fix Tf _ hU (hF c γ ⟨s, rfl⟩)
    have hΓu : IsUnit ((Tf.til.ga c).1.1 * γ.1.1 * ((Tf.til.ga c)⁻¹).1.1).det := by
      rw [← Units.val_mul, ← Units.val_mul]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
    have hδu := isUnit_of_extE Tf δ _ hΓu hδE
    set Δ : GL (Fin (D.R.N D.R.m - 1)) D.host.E := ((Matrix.isUnit_iff_isUnit_det δ).mpr hδu).unit with hΔdef
    have hΔv : Δ.1 = δ := IsUnit.unit_spec _
    have hΔ : Δ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramP D) := by
      show cT _ Δ.1 * gramP D * Δ.1 = gramP D
      rw [hΔv]; exact unitary_of_hform _ _ _ hδi
    obtain ⟨s', hs'⟩ := stab_restrict Tf c γ ⟨s, rfl⟩ ⟨Δ, hΔ⟩ (by rw [show (⟨Δ, hΔ⟩ : UJ _ _).1.1 = δ from hΔv]; exact hδE)
    exact ⟨s', δ, hδE, by rw [hs']; exact hΔv⟩
  choose g δf hδE hδv using key
  refine ⟨g, fun s1 s2 h12 => ?_⟩
  have hδ12 : δf s1 = δf s2 := by rw [← hδv s1, ← hδv s2, h12]
  have hΓ := ext_unique Tf (hδE s1) (hδ12 ▸ hδE s2)
  apply Km.stabI_inj ((D.fm u).til c)
  apply Subtype.ext
  apply Units.ext
  have hi : ((Tf.til.ga c)⁻¹).1.1 * (Tf.til.ga c).1.1 = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have := congrArg (fun M => ((Tf.til.ga c)⁻¹).1.1 * M * (Tf.til.ga c).1.1) hΓ
  simp only [← Matrix.mul_assoc, hi, Matrix.one_mul] at this
  simp only [Matrix.mul_assoc, hi, Matrix.mul_one] at this
  exact this

theorem stabiliser_bijective_of_fixed
    (hF : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
      StabFix Tf) : StabiliserMapBijective :=
  stabiliser_bijective_of_injection (fun D u Ch chOf Tf c => stab_back Tf (hF D u Ch chOf Tf) c)

end Formalism.L2.GlobalTheoryTheory.Br
