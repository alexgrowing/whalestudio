import Formalism.LocalToGlobal.GlobalTheory.BlockActions.StabiliserBijectiveOfFinite

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

theorem mulLat_one {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) :
    mulLat (1 : Matrix (Fin n) (Fin n) E) L = L := by
  unfold mulLat
  convert Submodule.map_id L
  ext x i
  simp

theorem dualL_stable {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (γ γi : Matrix (Fin n) (Fin n) E) (hγi : γi * γ = 1) (hγ' : γ * γi = 1)
    (hU : cT σ γ * J * γ = J) (hL : mulLat γ L = L) :
    ∀ y ∈ dualL σ J L, γ *ᵥ y ∈ dualL σ J L := by
  have hLi : mulLat γi L = L := by
    conv_lhs => rw [← hL]
    rw [mulLat_mulLat, hγi, mulLat_one]
  have hset : ∀ y ∈ dualSet σ J L, γ *ᵥ y ∈ dualSet σ J L := by
    intro y hy x hx
    have hxi : γi *ᵥ x ∈ L := by
      rw [← hLi]; exact Submodule.mem_map_of_mem hx
    have e : x = γ *ᵥ (γi *ᵥ x) := by rw [mulVec_mulVec, hγ', one_mulVec]
    rw [e, hform_UJ σ J γ hU]
    exact hy _ hxi
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span (hset z hz)
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
  | smul r a _ ha =>
    have e : γ *ᵥ (r • a) = r • (γ *ᵥ a) := by
      rw [← algebraMap_smul E r a, mulVec_smul, algebraMap_smul]
    rw [e]; exact Submodule.smul_mem _ r ha

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem stabLF_of (Tf : FormsTiedSym D u Ch chOf)
    (h : ∀ (c : (D.fm u).clsP) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)),
      γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range →
      mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) = clsCrd D u D.R.m le_rfl ((D.fm u).til c) ∧
      ∀ (v : (D.mem u).A.vT) (x : ↥(Ld D u D.R.m le_rfl ((D.fm u).til c)))
        (hx : γ.1.1 *ᵥ x.1 ∈ Ld D u D.R.m le_rfl ((D.fm u).til c)),
        (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ ⟨γ.1.1 *ᵥ x.1, hx⟩) =
          (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ x)) :
    StabLF Tf := by
  intro c γ hγ
  obtain ⟨hL, hf⟩ := h c γ hγ
  refine ⟨hL, ?_, hf⟩
  have h1 : (γ.1⁻¹ : GL _ _).1 * γ.1.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : γ.1.1 * (γ.1⁻¹ : GL _ _).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact dualL_stable _ _ _ γ.1.1 _ h1 h2 γ.2 hL

end Formalism.L2.GlobalTheoryTheory.Br
