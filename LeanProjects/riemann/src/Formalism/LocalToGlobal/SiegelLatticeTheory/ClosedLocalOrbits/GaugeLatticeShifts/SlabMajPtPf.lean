import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabMajPtPfSupp
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ColsDim
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLatOfLattice

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.SlabMajPt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem col_val (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) (T : Cu X w hK) (ξ : X.Vpi w) (γ : Gam X w) (x : Hfin X w)
    (κ : Ku X w hK) :
    (T : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, iotaF X w γ * x * (κ : Hfin X w)) =
      ((psiK X w hK κ : ℂˣ) : ℂ) *
        (T : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) (piRep X w (iotaI X w γ)⁻¹ ξ) (1, x) := by
  obtain ⟨hF, hE⟩ := T.2
  obtain ⟨hL, hR⟩ := hF ξ
  have e1 : ((1 : Hinf X w), iotaF X w γ * x * (κ : Hfin X w)) =
      ((1 : Hinf X w), iotaF X w γ * x) * ((1 : Hinf X w), (κ : Hfin X w)) := by simp
  have e2 : ((1 : Hinf X w), iotaF X w γ * x) = (iotaI X w γ, iotaF X w γ) * ((iotaI X w γ)⁻¹, x) := by simp
  have e3 : ((iotaI X w γ)⁻¹, x) = ((1 : Hinf X w), x) * ((iotaI X w γ)⁻¹, (1 : Hfin X w)) := by simp
  rw [e1, hR, e2, hL, e3, ← hE]

theorem norm_psiK (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) (κ : Ku X w hK) : ‖((psiK X w hK κ : ℂˣ) : ℂ)‖ = 1 :=
  hK.2.2.2.2 _ κ.2

theorem col_lower (Y : Full X) (w : D.what₂.Word) :
    ∃ (n : ℕ) (T : Fin n → Cu X w Y.hK), ∀ (ξ : X.Vpi w) (h : Hfin X w),
      ‖ξ‖ₑ ≤ ∑ i, ‖(T i : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ := by
  have hst : Formalism.L2.SG.ColsDim.StabTriv (iotaF X w) (Ku X w Y.hK) :=
    Formalism.L2.SG.PoincareInHH.Cut.neatKu_of_gamUnipKu X w Y.hK (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X w)
      (Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X w Y.hK)
  have hfin : Finite (Formalism.L2.SG.ColsDim.Classes (iotaF X w) (Ku X w Y.hK)) := by
    refine Finite.of_surjective
      (fun ρ : (Y.cs w).Cl => DoubleCoset.mk (iotaF X w).range (Ku X w Y.hK) ((Y.cs w).h ρ)) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h g =>
      obtain ⟨ρ, ⟨γ, κ, hg⟩, _⟩ := Y.colReps w g
      refine ⟨ρ, ?_⟩
      show DoubleCoset.mk _ _ _ = DoubleCoset.mk _ _ g
      rw [DoubleCoset.eq]
      exact ⟨iotaF X w γ, ⟨γ, rfl⟩, κ, κ.2, hg⟩
  have := Fintype.ofFinite (Formalism.L2.SG.ColsDim.Classes (iotaF X w) (Ku X w Y.hK))
  obtain ⟨e, he⟩ := Formalism.L2.SG.ColsDim.columns_decomposition (Gam X w) (Hinf X w) (Hfin X w) ℂ (X.Vpi w) (iotaI X w)
    (iotaF X w) (Ku X w Y.hK) (psiK X w Y.hK) (piRep X w) (fun c => c.out) (fun c => DoubleCoset.out_eq' _ _ c) hst
  obtain ⟨b, -⟩ : ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ (X.Vpi w))) ℂ (X.Vpi w), True :=
    ⟨stdOrthonormalBasis ℂ (X.Vpi w), trivial⟩
  let ι := Formalism.L2.SG.ColsDim.Classes (iotaF X w) (Ku X w Y.hK) × Fin (Module.finrank ℂ (X.Vpi w))
  let f : ι → Cu X w Y.hK := fun p => e.symm (fun c => if c = p.1 then innerₛₗ ℂ (b p.2) else 0)
  have hf : ∀ p ξ, (f p : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, p.1.out) = inner ℂ (b p.2) ξ := by
    intro p ξ
    rw [← he]
    simp only [LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨Fintype.card ι, fun i => f ((Fintype.equivFin ι).symm i), fun ξ h => ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, c = DoubleCoset.mk (iotaF X w).range (Ku X w Y.hK) h := ⟨_, rfl⟩
  obtain ⟨g, ⟨γ, rfl⟩, κ, hκ, hh⟩ := (DoubleCoset.eq _ _ c.out h).1 (by rw [DoubleCoset.out_eq', hc])
  obtain ⟨ξ', hξ'⟩ : ∃ ξ', ξ' = piRep X w (iotaI X w γ)⁻¹ ξ := ⟨_, rfl⟩
  have hn : ‖ξ'‖ = ‖ξ‖ := by
    have h2 : inner ℂ ξ' ξ' = inner ℂ ξ ξ := by
      rw [hξ']
      exact (X.piU_rep w).2.2.1 _ (hinf_le_sinf X w _ ((iotaI X w γ)⁻¹).2) ξ ξ
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) ξ, h2]
  have hval : ∀ j, ‖(f (c, j) : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ = ‖inner ℂ (b j) ξ'‖ₑ := by
    intro j
    rw [hh, col_val Y.hK w (f (c, j)) ξ γ c.out ⟨κ, hκ⟩, ← hξ', hf (c, j) ξ', enorm_mul,
      ← ofReal_norm (((psiK X w Y.hK ⟨κ, hκ⟩ : ℂˣ) : ℂ)), norm_psiK, ENNReal.ofReal_one, one_mul]
  calc ‖ξ‖ₑ = ‖ξ'‖ₑ := by rw [← ofReal_norm, ← ofReal_norm, hn]
    _ = ‖∑ j, inner ℂ (b j) ξ' • b j‖ₑ := by rw [b.sum_repr']
    _ ≤ ∑ j, ‖inner ℂ (b j) ξ' • b j‖ₑ := enorm_sum_le _ _
    _ = ∑ j, ‖inner ℂ (b j) ξ'‖ₑ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [enorm_smul, ← ofReal_norm (b j), b.orthonormal.1 j, ENNReal.ofReal_one, mul_one]
    _ = ∑ j, ‖(f (c, j) : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ :=
        Finset.sum_congr rfl fun j _ => (hval j).symm
    _ ≤ ∑ p : ι, ‖(f p : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ := by
        rw [Fintype.sum_prod_type]
        exact Finset.single_le_sum (f := fun c' => ∑ j, ‖(f (c', j) : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ)
          (fun _ _ => bot_le) (Finset.mem_univ c)
    _ = ∑ i, ‖(f ((Fintype.equivFin ι).symm i) : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ :=
        (Equiv.sum_comp (Fintype.equivFin ι).symm
          (fun p => ‖(f p : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ)).symm

theorem ph_lower (Y : Full X) (w : D.what₂.Word) {n : ℕ} (T : Fin n → Cu X w Y.hK)
    (hT : ∀ (ξ : X.Vpi w) (h : Hfin X w),
      ‖ξ‖ₑ ≤ ∑ i, ‖(T i : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ)
    (x : X.B.I.Ginf) (h : Hfin X w) (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    ‖X.Wu w x‖ₑ ≤ ∑ i, ‖Ph X w Y.hK (T i) (x, (h : X.B.I.Gf) * X.xu w * k)‖ₑ := by
  refine (hT (X.Wu w x) h).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [Formalism.L2.SG.Pf.RegroupPf.ph_col Y.hK (Formalism.L2.SG.Pf.phWellDef_holds X w) (T i) x h k hk, enorm_mul,
    ← ofReal_norm (X.chi2 k), Y.hK.2.2.2.2 k hk, ENNReal.ofReal_one, one_mul]

theorem pointwise_majorant_by_columns : Formalism.L2.SG.Pf.Slab.MajPtC := by
  intro D X Y u u'
  obtain ⟨n, T, hT⟩ := col_lower Y u
  obtain ⟨n', T', hT'⟩ := col_lower Y u'
  refine ⟨n, n', T, T', 1, ENNReal.one_ne_top, fun t x => ?_⟩
  obtain ⟨h, κ, hκ, he⟩ := term_supp Y u u' t
  have h1 := ph_lower Y u T hT x ((Y.cs u).h ((Y.cs u).base t.lam)) 1 Y.hK.1
  have h2 := ph_lower Y u' T' hT' (t.pt.1⁻¹ * x) h κ hκ
  have hb : t.pt⁻¹ * (x, Formalism.L2.SG.Pf.Slab.aB Y u t.lam) = (t.pt.1⁻¹ * x, (h : X.B.I.Gf) * X.xu u' * κ) :=
    Prod.ext rfl he
  have ha : (x, Formalism.L2.SG.Pf.Slab.aB Y u t.lam) =
      (x, ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf) * X.xu u * 1) := by
    rw [mul_one]; rfl
  rw [hb, ha, one_mul]
  exact (mul_le_mul' h1 h2).trans_eq (Finset.sum_mul_sum _ _ _ _)

end Formalism.L2.SG.Pf.SlabMajPt
