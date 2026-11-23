import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.ColFormsLemmas

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix

section

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}

omit [NumberField K] [StarRing K] in

theorem GStep.lsh_eq_map (S : GStep E K n) (h : S.Ok) (b : S.β) (g : S.G b) (d : S.D b) :
    S.Lsh b (g • d) = (S.Lsh b d).map
      ((Matrix.mulVecLin (S.gam b g : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E)) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  have e : (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ (((S.gam b g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y = y := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  constructor
  · intro hy
    exact ⟨_, (h.lsh_smul b g d _).1 (by rw [e]; exact hy), e⟩
  · rintro ⟨x, hx, rfl⟩
    exact (h.lsh_smul b g d x).2 hx

omit [StarRing K] [Fintype ι] in

theorem GStep.tauLat_smul (S : GStep E K n) (h : S.Ok) (emb : ι → E →+* K) [Fintype ι] (b : S.β) (g : S.G b) (d : S.D b) (τ : ι) :
    tauLat emb τ (S.Lsh b (g • d)) = gLat (embGL emb (S.gam b g) τ) (tauLat emb τ (S.Lsh b d)) := by
  rw [S.lsh_eq_map h]
  exact tauLatG E K ι n emb τ _ (S.gam b g)

end

theorem fam_ok : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n),
    FOk emb σ → S.Ok → (S.fam emb lam).Ok := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF h b
  have hr : ∀ g : S.G b, ∃ m : ℕ, 0 < m ∧ ((S.chr b g : Kˣ) : K) ^ m = 1 := fun g => by
    obtain ⟨m, hm, hc⟩ := h.root b g
    exact ⟨m, hm, by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]⟩
  refine ⟨h.fin_orb b, h.fin_stab b, ?_, ?_, ?_⟩
  · intro g d
    obtain ⟨m, hm, hc⟩ := hr g
    refine Eq.trans ?_ (map_root_smul _ (rhoVr emb lam (S.gam b g)) hm hc).symm
    show nabAtr emb lam (S.Lsh b (g • d)) = (nabAtr emb lam (S.Lsh b d)).map _
    unfold nabAtr
    simp_rw [S.tauLat_smul h emb b g d, dualFr_gLat]
    exact nabK_gLat lam _ (invTrK (embGL emb (S.gam b g)))
  · intro g d
    obtain ⟨m, hm, hc⟩ := hr g
    refine Eq.trans ?_ (map_root_smul _ (rhoVr emb lam (S.gam b g)) hm hc).symm
    show delAtr emb lam (S.Lsh b (g • d)) = (delAtr emb lam (S.Lsh b d)).map _
    unfold delAtr
    simp_rw [S.tauLat_smul h emb b g d, dualFr_gLat]
    exact delK_gLat lam _ (invTrK (embGL emb (S.gam b g)))
  · intro g x y
    obtain ⟨m, hm, hc⟩ := hr g
    have hU : S.gam b g ∈ Formalism.UG.UJ (starRingEnd E) (1 : Matrix (Fin n) (Fin n) E) := by
      have := h.unit b g
      show _ * _ * _ = _
      rw [Matrix.mul_one]
      exact this
    have hi : pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) (rhoVr emb lam (S.gam b g) x) (rhoVr emb lam (S.gam b g) y) =
        pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) x y :=
      pairInv K ι n lam _ _ (fun τ => (uJUnitary E K ι n emb (starRingEnd E) τ
        (fun x => (hF.emb_star τ x).symm) 1 _ hU).2 (by simp)) x y
    show pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) (((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) x)
      (((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) y) = pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hi, smul_smul]
    show (star ((S.chr b g : Kˣ) : K) * _) • _ = _
    rw [star_mul_root ⟨σ, hF.sig_star⟩ hm hc, one_smul]

end GlobalTheory.Mem.Col2

end
