import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DualWeylZeroConst

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.MainNotions.G.LatticeSystems (lb_D lb_D_det)

section At

variable (p n' : ℕ) {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf]
  [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (TT : Finset (Fin n')) (d : Fin n' → ℕ)
  (rest lam : Fin n' → Fin (m + 1) → ℤ)

def RhoAtG (c0 loss κ : ℕ) (e : Edge W Qq (m + 1)) (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d))) : Prop :=
  ∃ (Ix : Type) (ρ : Ix → (Vsp Kf lam →ₗ[Kf] Vsp Kf (flW (m := m) d))),
    (∀ β, ∀ u ∈ Re p ι σ w r lam e, ρ β u ∈ Re p ι σ w r (flW d) e) ∧
    (∀ β, ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → ∀ u ∈ Re p ι σ w r lam e',
      ρ β u ∈ scale (algebraMap O Kf w ^ (-(loss : ℤ))) (Re p ι σ w r (flW d) e')) ∧
    (∀ β, ∀ u ∈ HL (O := O) ι σ lam e.tgt,
      ρ β u ∈ scale ((p : Kf) ^ Ar r rest * algebraMap O Kf w ^ (-(loss : ℤ))) (HL (O := O) ι σ (flW d) e.tgt)) ∧
    (∀ β (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) (s : Vsp Kf rest) (u : Vsp Kf lam),
      ((u : Vsp Kf lam) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = ((Θ F : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * ((s : Vsp Kf rest) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) →
      ∃ F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
        (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈
          OpCl TT c0 (Submodule.span (KK O) {(F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))}) ∧ ρ β u = Θ F') ∧
    (∀ u ∈ Re p ι σ w r lam e,
      (∀ β, ρ β u ∈ scale (algebraMap O Kf w ^ ((2 * κ + 1 : ℕ) : ℤ)) (Re p ι σ w r (flW d) e)) →
      u ∈ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r lam e))

theorem rhoAt_of_G (lam0 : Fin n' → Fin (m + 1) → ℤ) (c0 loss : ℕ) (bK : ℝ) (e : Edge W Qq (m + 1))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) (dT TT lam0))))
    (κ : ℕ) (hκ : (κ : ℝ) ≤ bK)
    (h : RhoAtG p n' ι σ w r TT (dT TT lam0) (restW TT lam0) lam0 c0 loss κ e Θ) :
    RhoAt p n' ι σ w r TT lam0 c0 loss bK e Θ := by
  obtain ⟨Ix, ρ, h1⟩ := h
  exact ⟨κ, Ix, ρ, hκ, h1⟩

end At

theorem V_flat_supported {Kf : Type} [Field Kf] {n' m : ℕ} (TT : Finset (Fin n')) (d : Fin n' → ℕ)
    (hd0 : ∀ s, s ∉ TT → d s = 0) :
    ∀ y ∈ Vsp Kf (flW (m := m) d), y ∈ supported Kf {v : Fin n' × (Fin (m + 1) × Fin (m + 1)) | v.1 ∈ TT} := by
  intro y hy
  unfold Vsp tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    refine Subalgebra.prod_mem _ fun s _ => ?_
    by_cases hs : s ∈ TT
    · exact blockEmb_supported s _ (fun s => s ∈ TT) hs
    · have h0 : flW (m := m) d s = 0 := by
        unfold flW
        rw [hd0 s hs]
        simp
      have h1 := hF s
      simp only [lamAt_zero h0, if_pos (anti_zero m), nuOf_zero] at h1
      rw [dualWeyl_zero_const _ h1]
      unfold blockEmb
      rw [rename_C]
      exact Subalgebra.algebraMap_mem _ _
  | zero => exact Subalgebra.zero_mem _
  | add a b _ _ ha hb => exact Subalgebra.add_mem _ ha hb
  | smul t a _ ha => exact Subalgebra.smul_mem _ ha t

set_option maxHeartbeats 1600000 in

theorem rho_peel (D : Formalism.BasicNotions.D7) {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : HidaSetting p n' W Qq O Kf ι σ j w) {m : ℕ} (r : ℕ)
    (TT : Finset (Fin n')) (d : Fin n' → ℕ) (hd0 : ∀ s, s ∉ TT → d s = 0)
    (rest lam restT lamT sp : Fin n' → Fin (m + 1) → ℤ) (hPl : Peel TT lam lamT sp) (hPr : Peel TT rest restT sp)
    (hdlT : IsDominant lamT) (hdsp : IsDominant sp) (hlam : lam = lamT + sp)
    (hrest : rest = restT + sp) (c0 lossT κ M : ℕ) (hM : ordMax r sp ≤ M) (e : Edge W Qq (m + 1))
    (he : IsEdge p n' r e) (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hT : RhoAtG p n' ι σ w r TT d restT lamT c0 lossT κ e Θ) :
    RhoAtG p n' ι σ w r TT d rest lam c0 (lossT + M) κ e Θ := by
  classical
  obtain ⟨IxT, ρT, L1, L2, L3, Op, Nd⟩ := hT
  have hw := w_ne_zero h
  have hp0 : (p : Kf) ≠ 0 := by rw [Formalism.L2.G.Model.p_eq h]; exact pow_ne_zero _ hw
  set cw : Kf := algebraMap O Kf w with hcw
  set cp : Kf := (p : Kf) ^ Ar r sp with hcp
  have bp := fun e' (he' : IsEdge p n' r e') => Formalism.L2.G.Model.bePerfect p n' W Qq O Kf ι σ j w h m r sp hdsp e' he'
  have G1 : ∀ G ∈ Re' p ι σ w r sp e, ∀ Q ∈ Re p ι σ w r sp e,
      ∃ a : O, be p r sp Q G = cw ^ (0 : ℤ) * algebraMap O Kf a := by
    intro G hG Q hQ
    obtain ⟨a, ha⟩ := ((bp e he).1 G).1 hG Q hQ
    exact ⟨a, by rw [zpow_zero, one_mul, ha]⟩
  have G0 : ∀ G ∈ Re' p ι σ w r sp e, ∃ G' ∈ dualLat O Kf (HL (O := O) ι σ sp e.tgt), cw ^ (-(M : ℤ)) • G' = G :=
    fun G hG => mem_scale.1 (Re'_le_scale h m r sp hdsp e he M hM hG)
  have G2 : ∀ G ∈ Re' p ι σ w r sp e, ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt →
      ∀ Q ∈ Re p ι σ w r sp e', ∃ a : O, be p r sp Q G = cw ^ (-(M : ℤ)) * algebraMap O Kf a := by
    intro G hG e' he' htg Q hQ
    obtain ⟨G', hG', rfl⟩ := G0 G hG
    have h1 : G' ∈ Re' p ι σ w r sp e' :=
      (Formalism.L2.G.Model.dualInclusionLattices p n' W Qq O Kf ι σ j w h m r sp hdsp e' he').2 (by rw [htg]; exact hG')
    obtain ⟨a, ha⟩ := ((bp e' he').1 G').1 h1 Q hQ
    exact ⟨a, by rw [be_smulK_right, ha]⟩
  have G3 : ∀ G ∈ Re' p ι σ w r sp e, ∀ Q ∈ HL (O := O) ι σ sp e.tgt,
      ∃ a : O, G Q = cw ^ (-(M : ℤ)) * algebraMap O Kf a := by
    intro G hG Q hQ
    obtain ⟨G', hG', rfl⟩ := G0 G hG
    obtain ⟨a, ha⟩ := hG' Q hQ
    exact ⟨a, by rw [LinearMap.smul_apply, smul_eq_mul, ha]⟩
  have hmem0 : ∀ G ∈ Re' p ι σ w r sp e, ∀ u ∈ Re p ι σ w r lam e, peelMap hPl cp G u ∈ Re p ι σ w r lamT e := by
    intro G hG u hu
    obtain ⟨z, hz, hze⟩ := mem_scale.1 (peel_Re h hPl hlam hdlT hdsp r e he 0 G (G1 G hG) u hu)
    rw [zpow_zero, one_smul] at hze
    rw [← hze]
    exact hz
  refine ⟨IxT × {G : Module.Dual Kf (Vsp Kf sp) // G ∈ Re' p ι σ w r sp e},
    fun x => (ρT x.1).comp (peelMap hPl cp x.2.1), ?_, ?_, ?_, ?_, ?_⟩
  · intro β u hu
    exact L1 β.1 _ (hmem0 _ β.2.2 u hu)
  · intro β e' he' htg u hu
    obtain ⟨z, hz, hze⟩ := mem_scale.1 (peel_Re h hPl hlam hdlT hdsp r e' he' (-(M : ℤ)) β.2.1
      (G2 _ β.2.2 e' he' htg) u hu)
    obtain ⟨z2, hz2, hz2e⟩ := mem_scale.1 (L2 β.1 e' he' htg z hz)
    refine mem_scale.2 ⟨z2, hz2, ?_⟩
    rw [LinearMap.comp_apply, ← hze, map_smul, ← hz2e, smul_smul, ← zpow_add₀ hw]
    congr 2
    push_cast
    ring
  · intro β u hu
    obtain ⟨gs, hgs, _, _, h3⟩ := Formalism.L2.G.Model.edgeLat h m r e he
    have hL : ∀ s : Fin n', ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧
        extO O ι σ s.val e.tgt = colSpan O g := fun s =>
      ⟨_, by
        rw [Matrix.det_mul, Matrix.det_mul]
        exact ((hgs _).mul (lb_D_det _ _ _ hw)).mul (lb_D_det _ _ _ hw), h3 s.val⟩
    obtain ⟨z, hz, hze⟩ := mem_scale.1 (peel_HL hPl hdlT hdsp e.tgt hL cp (cw ^ (-(M : ℤ))) β.2.1 (G3 _ β.2.2) u hu)
    obtain ⟨z2, hz2, hz2e⟩ := mem_scale.1 (L3 β.1 z hz)
    refine mem_scale.2 ⟨z2, hz2, ?_⟩
    rw [LinearMap.comp_apply, ← hze, map_smul, ← hz2e, smul_smul]
    congr 1
    have hAr : Ar r rest = Ar r restT + Ar r sp := by rw [hrest]; exact Ar_add r _ _
    rw [hAr, zpow_add₀ hp0, hcp]
    have : cw ^ (-((lossT + M : ℕ) : ℤ)) = cw ^ (-(M : ℤ)) * cw ^ (-(lossT : ℤ)) := by
      rw [← zpow_add₀ hw]
      congr 1
      push_cast
      ring
    rw [this]
    ring
  · intro β F s u hu
    refine Op β.1 F (peelMap hPr cp β.2.1 s) (peelMap hPl cp β.2.1 u) ?_
    rw [peelMap_coe, peelMap_coe, hu, slice_mul_left TT _ _ _ (V_flat_supported TT d hd0 _ (Θ F).2), mul_smul_comm]
  · intro u hu hall
    have hz : ∀ G (hG : G ∈ Re' p ι σ w r sp e), peelMap hPl cp G u ∈ scale (cw ^ (1 : ℤ)) (Re p ι σ w r lamT e) :=
      fun G hG => Nd _ (hmem0 G hG u hu) (fun βT => hall (βT, ⟨G, hG⟩))
    obtain ⟨I, hI, x, π, _, _, _, _, _, c6, c7⟩ := edge_lattice_adapted_basis h m r sp hdsp e he
    cases nonempty_fintype I
    let spv : I → Vsp Kf sp := fun i => (cw ^ (-order r sp (π i))) • x i
    let Gv : I → Module.Dual Kf (Vsp Kf sp) := fun i => (cw ^ (-order r sp (π i)) * (p : Kf) ^ (-π i)) • x.coord i
    have hspv : ∀ i, spv i ∈ Re p ι σ w r sp e := fun i => by rw [← c6]; exact Submodule.subset_span ⟨i, rfl⟩
    have hGv : ∀ i, Gv i ∈ Re' p ι σ w r sp e := fun i => by rw [← c7]; exact Submodule.subset_span ⟨i, rfl⟩
    have hexp : ∀ y ∈ Vsp Kf lam, y = ∑ i, (cp • slice TT (extD (Gv i)) y) * ((spv i : Vsp Kf sp) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
      intro y hy
      unfold Vsp tensorLat at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨F, hF, rfl⟩ := hy
        have hQ : ∏ s, blockEmb Kf s (if s ∈ TT then 1 else F s) ∈ Vsp Kf sp := by
          refine Submodule.subset_span ⟨_, fun s => ?_, rfl⟩
          by_cases hs : s ∈ TT
          · simp only [if_pos hs, lamAt_zero (hPl.top s hs).2, if_pos (anti_zero m), nuOf_zero]
            exact one_mem_dualWeyl
          · have := hF s
            simp only [if_neg hs, lamAt_congr (hPl.off s hs).2]
            exact this
        have hPs : ∏ s, blockEmb Kf s (if s ∈ TT then F s else 1) ∈
            supported Kf {v : Fin n' × (Fin (m + 1) × Fin (m + 1)) | v.1 ∈ TT} := by
          refine Subalgebra.prod_mem _ fun s _ => ?_
          by_cases hs : s ∈ TT
          · rw [if_pos hs]; exact blockEmb_supported s _ (fun s => s ∈ TT) hs
          · rw [if_neg hs, map_one]; exact Subalgebra.one_mem _
        have hQs : ∏ s, blockEmb Kf s (if s ∈ TT then 1 else F s) ∈
            supported Kf {v : Fin n' × (Fin (m + 1) × Fin (m + 1)) | v.1 ∉ TT} := by
          refine Subalgebra.prod_mem _ fun s _ => ?_
          by_cases hs : s ∈ TT
          · rw [if_pos hs, map_one]; exact Subalgebra.one_mem _
          · rw [if_neg hs]; exact blockEmb_supported s _ (fun s => s ∉ TT) hs
        have e1 : (⟨_, hQ⟩ : Vsp Kf sp) = ∑ i, (cp * Gv i ⟨_, hQ⟩) • spv i := by
          conv_lhs => rw [← x.sum_repr ⟨_, hQ⟩]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Gv, spv, LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul, smul_smul]
          congr 1
          have e3 : cp * (cw ^ (-order r sp (π i)) * (p : Kf) ^ (-π i)) * cw ^ (-order r sp (π i)) = 1 := by
            rw [hcp, p_zpow h, p_zpow h, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw]
            unfold order
            have : 2 * Ar r sp + (-(Ar r sp - π i) + 2 * -π i) + -(Ar r sp - π i) = 0 := by ring
            rw [this, zpow_zero]
          calc (x.repr ⟨_, hQ⟩) i = (cp * (cw ^ (-order r sp (π i)) * (p : Kf) ^ (-π i)) * cw ^ (-order r sp (π i))) *
                (x.repr ⟨_, hQ⟩) i := by rw [e3, one_mul]
            _ = _ := by ring
        have e2 := congrArg (fun t : Vsp Kf sp => (t : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) e1
        simp only [Submodule.coe_sum, Submodule.coe_smul] at e2
        rw [prod_split TT F]
        have e4 : ∀ i, slice TT (extD (Gv i)) ((∏ s, blockEmb Kf s (if s ∈ TT then F s else 1)) *
            ∏ s, blockEmb Kf s (if s ∈ TT then 1 else F s)) =
            Gv i ⟨_, hQ⟩ • ∏ s, blockEmb Kf s (if s ∈ TT then F s else 1) := by
          intro i
          rw [slice_mul TT _ _ _ hPs hQs]
          congr 1
          exact extD_spec (Gv i) ⟨_, hQ⟩
        simp only [e4]
        conv_lhs => rw [e2, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, smul_mul_assoc, mul_smul_comm]
      | zero => simp
      | add a b _ _ ha hb =>
        simp only [map_add, smul_add, add_mul, Finset.sum_add_distrib]
        rw [← ha, ← hb]
      | smul t a _ ha =>
        conv_lhs => rw [ha]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_comm cp t]
        simp only [smul_mul_assoc]
    choose z hzR hze using fun i => mem_scale.1 (hz (Gv i) (hGv i))
    refine mem_scale.2 ⟨∑ i, mulV hlam hdlT hdsp (z i) (spv i), Submodule.sum_mem _ fun i _ =>
      edge_lattice_mul_of_weight_sum D (Formalism.L2.G.Model.products_sections_integral D) p ι σ w hw r hlam hdlT hdsp e (mulV_coe hlam hdlT hdsp _ _) (hzR i)
        (hspv i), ?_⟩
    apply Subtype.ext
    rw [hexp u u.2]
    simp only [Submodule.coe_smul, Submodule.coe_sum, mulV_coe, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h5 := congrArg (fun t : Vsp Kf lamT => (t : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) (hze i)
    simp only [Submodule.coe_smul, peelMap_coe] at h5
    rw [← h5, smul_mul_assoc]

end Formalism.MainNotions.TestSideCounting
