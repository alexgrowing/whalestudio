import Formalism.LocalToGlobal.GlobalTheory.BlockActions.DualLStable
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.LatSOfMem

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix
open scoped TensorProduct
open IsDedekindDomain

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prV_tensInt (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hs : s ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) :
    prV (E := E) v s ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · apply Subring.subset_closure
      left
      refine ⟨y, ?_⟩
      simp [prV, evalV, Algebra.TensorProduct.map_tmul]
    · apply Subring.subset_closure
      right
      refine ⟨⟨(y : FiniteAdeleRing (𝓞 F) F) v, y.2 v⟩, ?_⟩
      simp [prV, evalV, Algebra.TensorProduct.map_tmul]
      rfl
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem latS_prV (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hx : x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ) :
    (fun i => prV (E := E) v (x i)) ∈
      latS (F := F) (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact Submodule.subset_span ⟨l, hl, rfl⟩
  | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
  | add a b _ _ ha hb =>
    have e : (fun i => prV (E := E) v ((a + b) i)) = (fun i => prV (E := E) v (a i)) + (fun i => prV (E := E) v (b i)) := by
      funext i; simp
    rw [e]; exact add_mem ha hb
  | smul s a _ ha =>
    have e : (fun i => prV (E := E) v ((s • a) i)) =
        (⟨prV (E := E) v s, prV_tensInt v s.1 s.2⟩ : ↥(tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)) •
          (fun i => prV (E := E) v (a i)) := by
      funext i; simp [Subring.smul_def]
    rw [e]; exact Submodule.smul_mem _ _ ha

end Gen

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem clsCrd_fin (u : D.what₂.Word) (c : (D.mem u).C.cls D.R.m) :
    Module.Finite (𝓞 D.host.E) (clsCrd D u D.R.m le_rfl c) := by
  letI := D.host.cmStar
  rw [Module.Finite.iff_fg]
  exact (D.clsLat_lat u D.R.m c).fg.map _

set_option maxHeartbeats 4000000 in

theorem stab_lat_le (Tf : FormsTiedSym D u Ch chOf) (hLG : LatLocGlob) (hAL : AdLocLat) (c : (D.fm u).clsP)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl))
    (hγ : γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range) :
    mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) ≤ clsCrd D u D.R.m le_rfl ((D.fm u).til c) := by
  set Km := Tf.cls D.R.m le_rfl (Or.inr rfl) with hKm
  rw [Km.stabI_range] at hγ
  obtain ⟨κ, hκ, hκe⟩ := Subgroup.mem_map.mp hγ
  set Y := (Km.y ((D.fm u).til c)).1 with hY
  have hbc : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 = Y * κ * Y⁻¹ := by rw [← hκe]; rfl
  rintro _ ⟨x, hx, rfl⟩
  show γ.1.1 *ᵥ x ∈ _
  apply hLG D.host.F D.host.E _ _ (clsCrd_fin u _)
  have hX := latS_of_mem (F := D.host.F) _ x hx
  have hZ := (Km.y_lat _ _).1 hX
  set Z := (Y⁻¹).1 *ᵥ (fun i => inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) with hZdef
  have hκZ : κ.1 *ᵥ Z ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) Km.lev.Lb := by
    apply hAL D.host.F D.host.E _ _ Km.lev.Lb_fin
    intro v
    have hv := Km.lev.Uloc_lev v (((Km.lev.U_eq κ).1 hκ).2 v)
    have hst := (Subgroup.mem_inf.mp hv).2
    have e : (fun i => prV (E := D.host.E) v ((κ.1 *ᵥ Z) i)) =
        (bc (prV (E := D.host.E) v) κ).1 *ᵥ (fun i => prV (E := D.host.E) v (Z i)) := by
      funext i; exact RingHom.map_mulVec _ _ _ i
    rw [e]
    exact (hst _).1 (latS_prV v _ Z hZ)
  have hw : Y.1 *ᵥ (κ.1 *ᵥ Z) ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) := by
    apply (Km.y_lat _ _).2
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    exact hκZ
  have e2 : Y.1 *ᵥ (κ.1 *ᵥ Z) = fun i => inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ((γ.1.1 *ᵥ x) i) := by
    rw [hZdef, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← hbc]
    funext i
    exact (RingHom.map_mulVec _ _ _ i).symm
  rw [← e2]
  exact hw

theorem stab_lat (Tf : FormsTiedSym D u Ch chOf) (hLG : LatLocGlob) (hAL : AdLocLat) (c : (D.fm u).clsP)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl))
    (hγ : γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range) :
    mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) = clsCrd D u D.R.m le_rfl ((D.fm u).til c) := by
  apply le_antisymm (stab_lat_le Tf hLG hAL c γ hγ)
  have h2 := stab_lat_le Tf hLG hAL c γ⁻¹ (Subgroup.inv_mem _ hγ)
  have e : γ.1.1 * (γ⁻¹).1.1 = 1 := by rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  calc clsCrd D u D.R.m le_rfl ((D.fm u).til c) = mulLat (γ.1.1 * (γ⁻¹).1.1) (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) := by
        rw [e, mulLat_one]
    _ = mulLat γ.1.1 (mulLat (γ⁻¹).1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c))) := by rw [mulLat_mulLat]
    _ ≤ mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) := Submodule.map_mono h2

end Formalism.L2.GlobalTheoryTheory.Br
