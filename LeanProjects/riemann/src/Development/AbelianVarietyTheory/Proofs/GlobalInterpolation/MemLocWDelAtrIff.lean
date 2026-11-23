import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Formalism.LocalToGlobal.Columns.TiedValBwG
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.WeylLocOnePlace

theorem rhoVr_inv_coe {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n : ℕ} (lam : ι → DomWeight n) (B : GL (Fin n) E) (F : Formalism.L2.DIV.VV K lam) :
    (rhoVr emb lam B⁻¹ F).1 = actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 := by
  have e : (invTrK.comp (embGL emb)) B⁻¹ = (vlBdF emb (fun _ : ι => B))⁻¹ := by
    rw [map_inv]
    rfl
  show (rhoK lam ((invTrK.comp (embGL emb)) B⁻¹) F).1 = _
  rw [e]
  rfl

theorem mem_locW_delAtr_iff : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K)), (∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ)) → ∀ {n : ℕ} (lam lam' : ι → DomWeight n), (∀ τ, (lam τ).natW = (lam' τ).natW) → ∀ (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E M → ∀ (w : Pl.Pl) (B : GL (Fin n) E), IsLocBasis (Pl.resChar w) (M : Set (Fin n → E)) B → ∀ F : Formalism.L2.DIV.VV K lam, F ∈ locW Pl w (delAtr emb lam M) ↔ MvPolynomial.map σ (rhoVr emb lam B⁻¹ F).1 ∈ vlIntSpan σ Pl w lam' := by
  intro E K ι _ _ _ _ _ _ _ emb σ Pl pw hval n lam lam' hn M hM w B hB F
  have hbas : ∀ τ, IsBasisAt (pw w) (dualFr (tauLat emb τ M)) (vlBdF emb (fun _ : ι => B) τ) := fun τ =>
    pb_isBasisAt_dualFr (pw w) _ (tauLatticeLattice_holds E K ι n emb τ M hM).fg _
      (vl_isBasisAt_tauLat Pl pw hval emb τ w M B hB)
  have hlat : ∀ τ, Submodule.IsLattice K (dualFr (tauLat emb τ M)) := fun τ =>
    du_dualFr_lattice latticeBasisExists_holds _ (tauLatticeLattice_holds E K ι n emb τ M hM)
  have h0 : F ∈ locW Pl w (delAtr emb lam M) ↔ F ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam M) :=
    vl_mem_span_intW_iff Pl pw hval w _ F
  have hmem : F ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam M) ↔
      actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delStd K lam) := by
    have h1 : F ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delAtr emb lam M) ↔
        F.1 ∈ Formalism.HermitianLatticesTheory.localization₂ (pw w).asIdeal (delP lam fun τ => dualFr (tauLat emb τ M)) := Iff.rfl
    rw [h1, (nablaDeltaLocal_holds K ι n lam _ hlat (pw w) _ hbas).2]
    constructor
    · rintro ⟨G, hG, hGF⟩
      have e : actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 = G := by
        rw [← hGF]
        show actP lam (vlBdF emb (fun _ : ι => B))⁻¹ (actP lam (vlBdF emb (fun _ : ι => B)) G) = G
        rw [← polyAction_mul, inv_mul_cancel, polyAction_one₂]
      rw [e]
      exact hG
    · intro h
      refine ⟨_, h, ?_⟩
      show actP lam (vlBdF emb (fun _ : ι => B)) (actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1) = F.1
      rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]
  rw [h0, hmem, rhoVr_inv_coe]
  constructor
  · intro h
    exact vl_map_mem_intSpan Pl pw hval σ w lam lam' hn h
  · intro h
    obtain ⟨G, hG, hGe⟩ := vl_exists_of_mem_intSpan Pl pw hval σ w lam lam' hn h
    have hG' : actP lam (vlBdF emb (fun _ : ι => B))⁻¹ F.1 = G :=
      (MvPolynomial.map_injective σ σ.injective hGe).symm
    rw [hG']
    exact hG

end GlobalTheory.WeylLocOnePlace
