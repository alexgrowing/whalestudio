import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.DdSPowLeOne

noncomputable section

open scoped Classical

namespace Formalism.L2.S.Pv.ClassCounting

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.TermsAtPtFiniteW
  PI.TermsAtPtFiniteW.HeisW PI.TermsAtPtFiniteW.LeviW PI.TermsAtPtFiniteW.FrameW Formalism.L2.SG.Saturated

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frameOpFull (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : IsRowLat D F0 Λ)
    (B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (hBlo : ∀ i j, j < i → B i j = 0) (hBd : ∀ i, B i i = 1) :
    ∃ n ∈ NLam Λ (lf D F0), ∀ j,
      n (frame (lf D F0) j) = ∑ c, ((B c j : 𝓞 D.host.E) : D.host.E) • frame (lf D F0) c := by
  obtain ⟨θ, hθ⟩ := PI.UnitaryGroupMassFormula.IdCellInSW.traceOne_holds D
  obtain ⟨f, L, hff, hef, hL, hzL, hΛeq⟩ := split_row_iso D u F0 Λ hΛ
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hΛ.2.1.2.1
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 D.host.E, (o : D.host.E) = (VS D).hT x y :=
    fun x hx y hy => PI.SRW.pair_int _ hU hy hx
  have he : ∀ a, F0.e a ∈ Λ := fun a => by
    rw [hΛeq]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.subset_span ⟨a, 1, one_mem_aaS D a, (one_smul _ _).symm⟩))
  have hLΛ : L ≤ Λ := by
    rw [hΛeq]
    exact le_sup_right.trans le_sup_left
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have hzz : (VS D).hT F0.z F0.z = -((Tu D u : ℕ) : D.host.E) := F0.z_norm

  have horth : ∀ c : D.host.E, c • F0.z ∈ orth (VS D) (Xsp (lf D F0)) := fun c =>
    PI.DCRelEquiv.UnitaryGroupMassFormula.mem_orth_iff.mpr fun x hx =>
      orth_span F0.e (fun a => by rw [map_smul, F0.z_orth, smul_zero]) x hx
  obtain ⟨σ, hσL, hσz⟩ := exists_partner L F0.z hzL (by rw [hzz]; exact neg_ne_zero.mpr hT0)
    (fun x hx y hy => hint x (hLΛ hx) y (hLΛ hy))
    (fun c hc => mem_L_of_dual Λ (aaS D) F0.e f L hU hΛeq F0.e_iso hff hef hL
      (fun a => by rw [map_smul, F0.z_orth, smul_zero])
      (fun a => by rw [map_smul, (hL _ hzL a).2, smul_zero]) hc)
    (fun c hc => hΛ.2.1.2.2.2.2 c ⟨Submodule.mem_sup_left ⟨hLΛ hc, horth c⟩, horth c⟩)
  have hσΛ : σ ∈ Λ := hLΛ hσL

  set β : Fin D.R.rS → D.host.E := fun c => -star ((B (Fin.castSucc c) (Fin.last D.R.rS) : 𝓞 D.host.E) : D.host.E)
    with hβ
  have hβO : ∀ c, ∃ o : 𝓞 D.host.E, (o : D.host.E) = β c := fun c => by
    obtain ⟨o, ho⟩ := PI.SRW.star_int (B (Fin.castSucc c) (Fin.last D.R.rS))
    exact ⟨-o, by simp only [hβ, ← ho]; push_cast; ring⟩
  set a : Fin D.R.rS → (VS D).V := fun c => β c • σ with ha
  have haΛ : ∀ c, a c ∈ Λ := fun c => smul_memO Λ (hβO c) hσΛ
  have hea : ∀ c d, (VS D).hT ((lf D F0).fl.e c) (a d) = 0 := fun c d => by
    show (VS D).hT (F0.e c) (β d • σ) = 0
    rw [map_smul, (hL σ hσL c).1, smul_zero]
  set s : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := fun c d => -(θ : D.host.E) * (VS D).hT (a c) (a d) with hs
  have hsO : ∀ c d, ∃ o : 𝓞 D.host.E, (o : D.host.E) = s c d := fun c d => by
    obtain ⟨o, ho⟩ := hint _ (haΛ c) _ (haΛ d)
    exact ⟨-θ * o, by simp only [hs, ← ho]; push_cast; ring⟩
  have hss : ∀ c d, s c d + star (s d c) = -(VS D).hT (a c) (a d) := fun c d => by
    simp only [hs, star_mul', star_neg, hsym]
    linear_combination (-(VS D).hT (a c) (a d)) * hθ
  obtain ⟨nH, hnH, hnHapp⟩ := heisOp_holds D.host.E (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E) Λ (lf D F0) a s hint he haΛ hea hsO hss
  have hnHe : ∀ j, nH (F0.e j) = F0.e j := fun j => by
    rw [show F0.e j = (lf D F0).fl.e j from rfl, hnHapp]
    have h1 : ∀ c, (VS D).hT ((lf D F0).fl.e c) ((lf D F0).fl.e j) = 0 := fun c => F0.e_iso c j
    have h2 : ∀ c, (VS D).hT (a c) ((lf D F0).fl.e j) = 0 := fun c => by
      rw [← hsym, hea j c, star_zero]
    simp [PI.TermsAtPtFiniteW.heisFun, h1, h2]
  have hnHz : nH F0.z = F0.z + ∑ c, ((B (Fin.castSucc c) (Fin.last D.R.rS) : 𝓞 D.host.E) : D.host.E) • F0.e c := by
    rw [show F0.z = (lf D F0).fl.z from rfl, hnHapp]
    have h1 : ∀ c, (VS D).hT ((lf D F0).fl.e c) ((lf D F0).fl.z) = 0 := fun c => F0.z_orth c
    have h2 : ∀ c, (VS D).hT (a c) ((lf D F0).fl.z) =
        -((B (Fin.castSucc c) (Fin.last D.R.rS) : 𝓞 D.host.E) : D.host.E) := fun c => by
      show (VS D).hT (β c • σ) F0.z = _
      rw [LinearMap.map_smulₛₗ₂, hσz, smul_eq_mul, mul_one, starRingEnd_apply, hβ]
      simp
    simp only [PI.TermsAtPtFiniteW.heisFun, h1, h2, zero_smul, Finset.sum_const_zero, add_zero, mul_zero, neg_smul,
      Finset.sum_neg_distrib, sub_neg_eq_add]

  set U : Matrix (Fin D.R.rS) (Fin D.R.rS) (𝓞 D.host.E) := fun c j => B (Fin.castSucc c) (Fin.castSucc j)
    with hUdef
  have hUlo : ∀ i j, j < i → U i j = 0 := fun i j h =>
    hBlo (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc_lt_castSucc_iff.mpr h)
  have hUd1 : ∀ i, U i i = 1 := fun i => hBd _
  have hdet : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j h => hUlo i j h)]
    exact Finset.prod_eq_one fun i _ => hUd1 i
  haveI : Invertible U.det := by rw [hdet]; exact invertibleOne
  haveI : Invertible U := Matrix.invertibleOfDetInvertible U
  have hUbt : U.BlockTriangular id := fun i j h => hUlo i j h
  have hUibt : (U⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hUbt
  have hUiU : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U (by rw [hdet]; exact isUnit_one)
  set UE : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := fun c j => ((U c j : 𝓞 D.host.E) : D.host.E) with hUE
  set U'E : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E := fun c b => star ((U⁻¹ b c : 𝓞 D.host.E) : D.host.E)
    with hU'E
  have hentry : ∀ b a, ∑ c, ((U⁻¹ b c : 𝓞 D.host.E) : D.host.E) * ((U c a : 𝓞 D.host.E) : D.host.E) =
      if b = a then 1 else 0 := by
    intro b a
    have h := congrArg (fun M : Matrix (Fin D.R.rS) (Fin D.R.rS) (𝓞 D.host.E) =>
      algebraMap (𝓞 D.host.E) D.host.E (M b a)) hUiU
    simp only [Matrix.mul_apply, Matrix.one_apply, map_sum, map_mul] at h
    exact h.trans (by split_ifs <;> simp)
  have hUU : ∀ a b, ∑ c, star (UE c a) * U'E c b = if a = b then 1 else 0 := by
    intro a b
    calc ∑ c, star (UE c a) * U'E c b =
          star (∑ c, ((U⁻¹ b c : 𝓞 D.host.E) : D.host.E) * ((U c a : 𝓞 D.host.E) : D.host.E)) := by
          rw [star_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [hUE, hU'E, star_mul']
          ring
      _ = if a = b then 1 else 0 := by
          rw [hentry]
          rcases eq_or_ne a b with h | h
          · subst h; simp
          · simp [h, Ne.symm h]
  have hisoL := isom_psiF F0.e f F0.e_iso hff hef UE U'E hUU
  let nL : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
    LinearEquiv.ofInjectiveEndo (psiF F0.e f UE U'E) (inj_of_isom _ hisoL)
  have hnL : ∀ v, nL v = psiF F0.e f UE U'E v := fun v =>
    congrFun (LinearEquiv.coe_ofInjectiveEndo _ _) v
  have hLm : ∀ v ∈ Λ, psiF F0.e f UE U'E v ∈ Λ := fun v hv =>
    levi_mem Λ (aaS D) F0.e f L hΛeq F0.e_iso hff hef hL (aaS_mono D) (aaS_ne D) UE U'E
      (fun c a' => ⟨fun h => by simp [hUE, hUlo c a' h], ⟨U c a', rfl⟩⟩)
      (fun c a' => ⟨fun h => by simp [hU'E, hUibt h], PI.SRW.star_int _⟩) hv
  have hnLmem : nL ∈ NLam Λ (lf D F0) := by
    refine ⟨⟨fun x y => by rw [hnL, hnL]; exact hisoL x y, ?_⟩, ?_, ?_⟩
    · exact gmap_of_isom Λ hU nL (fun x y => by rw [hnL, hnL]; exact hisoL x y)
        (fun v hv => by rw [hnL]; exact hLm v hv)
    · intro j x hx
      have hsub : F0.Xa (j + 1) ≤ (F0.Xa j).comap (psiF F0.e f UE U'E - LinearMap.id) := by
        unfold Formalism.MainNotions.S.FlagG.Xa
        rw [Submodule.span_le]
        rintro _ ⟨i, hi, rfl⟩
        simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]
        rw [psiF_e F0.e f hef UE U'E F0.e_iso i, sum_sub_delta]
        refine Submodule.sum_mem _ fun c _ => ?_
        rcases lt_trichotomy c i with h | h | h
        · exact Submodule.smul_mem _ _ (Submodule.subset_span
            ⟨c, show c.1 < j from lt_of_lt_of_le (Fin.lt_def.mp h) (Nat.lt_succ_iff.mp hi), rfl⟩)
        · subst h
          simp [hUE, hUd1]
        · simp [hUE, hUlo c i h, if_neg h.ne']
      have := hsub hx
      rw [hnL]
      exact this
    · intro x hx
      have hφ : ∀ c, (VS D).hT (F0.e c) x = 0 := fun c =>
        (PI.DCRelEquiv.UnitaryGroupMassFormula.mem_orth_iff.mp hx) _ (PI.DCRelEquiv.UnitaryGroupMassFormula.e_mem_X (lf D F0) c)
      rw [hnL, psiF_apply]
      simp only [hφ, zero_smul, Finset.sum_const_zero, add_zero, add_sub_cancel_left]
      refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (PI.DCRelEquiv.UnitaryGroupMassFormula.e_mem_X (lf D F0) c))
        (PI.DCRelEquiv.UnitaryGroupMassFormula.e_mem_X (lf D F0) a))
  refine ⟨nH * nL, PI.DCRelEquiv.UnitaryGroupMassFormula.nlam_mul hnH hnLmem, frame_fin D F0 1 B
    (fun i j => ⟨hBlo i j, fun h => h ▸ hBd i, fun _ => one_dvd _⟩) nH nL hnHe hnHz
    (fun i => by rw [hnL]; exact psiF_e F0.e f hef UE U'E F0.e_iso i)
    (by rw [hnL]; exact psiF_fix F0.e f UE U'E F0.z (fun a => (hL _ hzL a).2) (fun a => F0.z_orth a))⟩

end Formalism.L2.S.Pv.ClassCounting

end
