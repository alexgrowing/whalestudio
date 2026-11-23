import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.EqCovol.FullLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma cc_cc' (a : E) : cc (cc a) = a := IsCMField.complexConj_apply_apply E a

lemma herm_sub_left' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (u v y : Fin r → E) :
    herm G (u - v) y = herm G u y - herm G v y := by
  simp [herm, sub_mul, Finset.sum_sub_distrib]

lemma herm_sub_right' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x u v : Fin r → E) :
    herm G x (u - v) = herm G x u - herm G x v := by
  simp [herm, cc, mul_sub, Finset.sum_sub_distrib]

lemma herm_smul_left'' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (u y : Fin r → E) :
    herm G (c • u) y = c * herm G u y := by
  simp [herm, Finset.mul_sum, mul_assoc]

lemma herm_smul_right'' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x v : Fin r → E) :
    herm G x (c • v) = cc c * herm G x v := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, cc, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma oe_smul {r : ℕ} (c : 𝓞 E) (y : Fin r → E) : c • y = (c : E) • y := by
  ext i; rfl

end GlobalTheory.EqCovol.FullLevel

open GlobalTheory.EqCovol.FullLevel in

theorem GlobalTheory.EqCovol.mem_iff_congr_lcm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (l : Level H) (r : ℕ) (Y : Data E r), GlobalTheory.EqCovol.IsLevGrp l Y → GlobalTheory.EqCovol.IsSelfDualTr Y →
    ∀ γ : GL (Fin r) E, γ ∈ Y.Γ ↔ IsUStab Y.Gm Y.Λ γ ∧ ∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ,
      (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.M' • y := by
  intro E _ _ _ H l r Y hL hS γ
  have hM0 : (l.M : E) ≠ 0 := by
    have : l.M ≠ 0 := by have := l.three_le; omega
    exact_mod_cast this
  have hA0 : (l.A : E) ≠ 0 := by exact_mod_cast l.A_pos.ne'
  constructor
  · intro hγ
    obtain ⟨hU, hM, hA⟩ := (hL γ).1 hγ
    obtain ⟨-, hMinv, -⟩ := (hL γ⁻¹).1 (Y.Γ.inv_mem hγ)
    set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg
    set gi : Matrix (Fin r) (Fin r) E := ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hgi
    have hggi : ∀ v, g.mulVec (gi.mulVec v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, hg, hgi, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hunit : ∀ u v, herm Y.Gm (g.mulVec u) v = herm Y.Gm u (gi.mulVec v) := by
      intro u v
      have := hU.1 u (gi.mulVec v)
      rwa [hggi] at this
    have hcop : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.coprime]; exact Submodule.mem_top
    obtain ⟨b', hb', b, hb, hsum⟩ := Submodule.mem_sup.1 hcop
    have hsumE : (b' : E) + (b : E) = 1 := by exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) hsum

    have key : ∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ, g.mulVec x - x = l.M • y := by
      intro x hx
      obtain ⟨y1, hy1, e1⟩ := hM (b • x) (Submodule.smul_mem_smul hb hx)
      set z : Fin r → E := (l.M : E)⁻¹ • ((b' : E) • (g.mulVec x - x)) with hz
      have hzmem : z ∈ Y.Λ := by
        refine (hS z).2 fun y hy => ?_
        have hc : H.bar b' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem _ hb'
        obtain ⟨w, hw, ew⟩ := hMinv (H.bar b' • y) (Submodule.smul_mem_smul hc hy)
        have hbarE : ((H.bar b' : 𝓞 E) : E) = cc (b' : E) := H.bar_eq b'
        rw [oe_smul, hbarE, ← Nat.cast_smul_eq_nsmul E] at ew
        have h1 : herm Y.Gm z y = herm Y.Gm x w := by
          have h2 := congrArg (herm Y.Gm x) ew
          rw [herm_sub_right', ← hunit, herm_smul_right'', herm_smul_right'', herm_smul_right'',
            cc_cc', cc, map_natCast] at h2
          rw [hz, herm_smul_left'', herm_smul_left'', herm_sub_left']
          field_simp
          linear_combination h2
        obtain ⟨n, hn⟩ := (hS x).1 hx w hw
        exact ⟨n, by rw [h1, hn]⟩
      refine ⟨z + y1, Y.Λ.add_mem hzmem hy1, ?_⟩
      rw [oe_smul, Matrix.mulVec_smul] at e1
      rw [smul_add, ← e1, ← Nat.cast_smul_eq_nsmul E, hz, smul_smul,
        mul_inv_cancel₀ hM0, one_smul, ← smul_sub, ← add_smul, hsumE, one_smul]
    refine ⟨hU, fun x hx => ?_⟩
    obtain ⟨y, hy, ey⟩ := key x hx
    obtain ⟨y', hy', ey'⟩ := hA x hx
    refine ⟨Nat.gcdA l.M l.A • y' + Nat.gcdB l.M l.A • y,
      Y.Λ.add_mem (Y.Λ.toAddSubgroup.zsmul_mem hy' _) (Y.Λ.toAddSubgroup.zsmul_mem hy _), ?_⟩
    set t := g.mulVec x - x with ht
    rw [← Nat.cast_smul_eq_nsmul E] at ey ey'
    have hy1 : y = (l.M : E)⁻¹ • t := by rw [ey, smul_smul, inv_mul_cancel₀ hM0, one_smul]
    have hy2 : y' = (l.A : E)⁻¹ • t := by rw [ey', smul_smul, inv_mul_cancel₀ hA0, one_smul]
    have hG : ((Nat.gcd l.M l.A : ℕ) : E) = (l.M : E) * (Nat.gcdA l.M l.A : E) + (l.A : E) * (Nat.gcdB l.M l.A : E) := by
      have := congrArg (Int.cast : ℤ → E) (Nat.gcd_eq_gcd_ab l.M l.A)
      push_cast at this
      exact this
    have hGL : ((Nat.gcd l.M l.A : ℕ) : E) * (l.M' : E) = (l.M : E) * (l.A : E) := by
      unfold Level.M'
      exact_mod_cast Nat.gcd_mul_lcm l.M l.A
    rw [← Nat.cast_smul_eq_nsmul E, ← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, hy1, hy2,
      smul_smul, smul_smul, ← add_smul, smul_smul]
    conv_lhs => rw [← one_smul E t]
    congr 1
    field_simp
    linear_combination hGL.symm + (l.M' : E) * hG
  · rintro ⟨hU, h⟩
    refine (hL γ).2 ⟨hU, fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨y, hy, e⟩ := h x (Submodule.smul_le_right hx)
      obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      exact ⟨k • y, Y.Λ.toAddSubmonoid.nsmul_mem hy k, by rw [e, hk, mul_smul]⟩
    · obtain ⟨y, hy, e⟩ := h x hx
      obtain ⟨k, hk⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
      exact ⟨k • y, Y.Λ.toAddSubmonoid.nsmul_mem hy k, by rw [e, hk, mul_smul]⟩
