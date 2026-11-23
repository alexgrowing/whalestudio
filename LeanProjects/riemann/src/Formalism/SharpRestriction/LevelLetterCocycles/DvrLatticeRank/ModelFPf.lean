import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfG

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules Formalism.MainNotions.N.Ln34.ModelFPf

theorem modelflink_pf : ModelFLinkStep := by
  intro D HW F Cm CA CB CK hA hP l _ hl K LL hG π' E hπ h' hh' c α β hfr T hcry hjmp
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨-, -, -, h4W, h5W, -⟩ := hA.1 l K 1 LL hG
  obtain ⟨h5a, h5b, -⟩ := h5W T (fun _ => h') (fun _ => h') hcry (fun τ _ _ => hjmp τ)
  obtain ⟨hπΔ, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, ⟨w2, hw2⟩, -⟩ := hπ
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  have hQ : ((HW l).W K 1 LL hG).Q = (w : LetA _ _) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' := by
    rw [Q_eq_q _ hs]
    exact hw
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hM : 1 ≤ MK l K h' := by
    refine Nat.one_le_ceil_iff.2 (div_pos ?_ ?_)
    · have : (1 : ℝ) ≤ h' := by exact_mod_cast hh'
      linarith
    · exact_mod_cast hsK
  have hEΔ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ := by
    intro δ hδ
    funext i
    show ((HW l).W K 1 LL hG).γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply]
    exact congrArg (fun t => Polynomial.aeval t (E i)) (congrFun (hπΔ δ hδ) i)
  have hπu : IsUnit (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE π') := by
    rw [hw0, map_mul, map_pow]
    exact (w0.isUnit.map _).mul (((HW l).W K 1 LL hG).EE_π.pow _)
  obtain ⟨u, hu, hγ⟩ := gam_unit ((HW l).W K 1 LL hG) π' E hsK w2 hw2 w0 hw0
  have hpO : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := fun h0 => by
    apply p_ne_zero ((HW l).W K 1 LL hG)
    rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1), h0, map_zero]
  have hnz := Eπ_nzd ((HW l).W K 1 LL hG) hw (q0_ne_two_and_ne_q_and_ne_d ((HW l).W K 1 LL hG) hpO)
  have huΔ := u_mem_AΔ ((HW l).W K 1 LL hG) hEΔ hnz hγ
  have hu'Δ := inv_mem_AΔ ((HW l).W K 1 LL hG) huΔ hu.val_inv_mul
  have hpt : ∀ ζ τ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → ζ ^ ((D.loc l).PD K).p = 1 ∧ ζ ≠ 1 := by
    intro ζ τ hPt
    obtain ⟨τs, hIs, -⟩ := hPt
    have hz1 : (D.loc l).ζQ 1 ^ l = 1 := by
      rw [(D.loc l).ζQ_succ 0, (D.loc l).ζQ_zero]
    have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 :=
      le_sup_right (a := K0 K) (IntermediateField.subset_adjoin _ _ (by rw [pow_one]; exact hz1))
    have hy := hIs.2 ⟨_, hmem⟩ rfl
    have hyl : (⟨_, hmem⟩ : ↥(Ks K 1)) ^ l = 1 := Subtype.ext (by simpa using hz1)
    refine ⟨?_, ?_⟩
    · rw [hp, ← hy, ← map_pow, hyl, map_one]
    · intro h1
      rw [← hy] at h1
      have : (⟨_, hmem⟩ : ↥(Ks K 1)) = 1 := τs.toRingHom.injective (by rw [map_one]; exact h1)
      exact (D.loc l).ζQ_one (congrArg Subtype.val this)
  exact modelF_local ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h'
    (MK l K h') (sigA l (sK l K) h') c α β hfr hcry hjmp hs hM hπΔ hEΔ hπu
    (Units.inv_mul w) hQ hu'Δ hu.val_inv_mul (by rw [hgam]; exact hγ) (h5a c)
    (fun y hy => ninLamPf_local ((HW l).W K 1 LL hG) T _ h' w hs hw h5b c hy) (h4W T hcry)
    hpt (hP l hl K LL hG T h' hh' hcry hjmp)

end Formalism.MainNotions.N.Ln34

end
