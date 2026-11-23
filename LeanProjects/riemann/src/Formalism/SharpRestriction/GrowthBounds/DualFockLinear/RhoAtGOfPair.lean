import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestCloudBOfTop
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideEdge

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

section At

variable (p n' : ℕ) {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf]
  [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (TT : Finset (Fin n')) (d : Fin n' → ℕ)
  (rest lam : Fin n' → Fin (m + 1) → ℤ)

def PairAt (c0 : ℕ) (bK : ℝ) (e : Edge W Qq (m + 1)) (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d))) : Prop :=
  ∃ (κ0 κf : ℕ) (Ψ0 : Module.Dual Kf (Vsp Kf lam) ≃ₗ[Kf] Vsp Kf lam)
    (Ψf : Module.Dual Kf (Vsp Kf (flW (m := m) d)) ≃ₗ[Kf] Vsp Kf (flW (m := m) d)),
    ((κ0 + κf : ℕ) : ℝ) ≤ bK ∧
    (∀ T ∈ dualLat O Kf (HL (O := O) ι σ (flW d) e.tgt), Ψf T ∈ HL (O := O) ι σ (flW d) (latDual e.tgt)) ∧
    (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → ∀ T ∈ Re' p ι σ w r (flW d) e',
      Ψf T ∈ Re p ι σ w r (flW d) e'.dual) ∧
    (∀ y ∈ Re p ι σ w r (flW d) e.dual, Ψf.symm ((p : Kf) ^ κf • y) ∈ Re' p ι σ w r (flW d) e) ∧
    (∀ y ∈ HL (O := O) ι σ lam (latDual e.tgt), Ψ0.symm ((p : Kf) ^ κ0 • y) ∈ dualLat O Kf (HL (O := O) ι σ lam e.tgt)) ∧
    (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → ∀ y ∈ Re p ι σ w r lam e'.dual,
      Ψ0.symm ((p : Kf) ^ κ0 • y) ∈ Re' p ι σ w r lam e') ∧
    (∀ G ∈ Re' p ι σ w r lam e, Ψ0 G ∈ Re p ι σ w r lam e.dual) ∧
    (Re p ι σ w r lam e.dual ≤ Submodule.span O {z : Vsp Kf lam | ∃ y ∈ Re p ι σ w r (flW d) e.dual,
      ∃ β ∈ Re p ι σ w r rest e.dual, (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)}) ∧
    (∀ (β : Vsp Kf rest) (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) (s : Vsp Kf rest) (u : Vsp Kf lam),
      ((u : Vsp Kf lam) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = ((Θ F : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * ((s : Vsp Kf rest) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) →
      ∃ F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
        (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈
          OpCl TT c0 (Submodule.span (KK O) {(F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))}) ∧
        ∀ (T : Module.Dual Kf (Vsp Kf (flW (m := m) d))) (z : Vsp Kf lam),
          (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = ((Ψf T : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) →
          (p : Kf) ^ Ar r rest * ((p : Kf) ^ κ0 * Ψ0.symm z u) = T (Θ F'))

end At

theorem HL_refl {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : HidaSetting p n' W Qq O Kf ι σ j w) {m : ℕ}
    (X : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant X) (L : Submodule W (Fin (m + 1) → Qq)) (hL : IsLattice W L)
    (y : Vsp Kf X) (hy : ∀ T ∈ dualLat O Kf (HL (O := O) ι σ X L), T y ∈ Set.range (algebraMap O Kf)) :
    y ∈ HL (O := O) ι σ X L := by
  obtain ⟨x, hx⟩ := Formalism.L2.G.Model.hlSpans p n' W Qq O Kf ι σ j w h m X hd L hL
  have hc : ∀ i, x.coord i ∈ dualLat O Kf (HL (O := O) ι σ X L) := by
    intro i v hv
    rw [← hx] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, rfl⟩ := hv
      by_cases hik : k = i
      · exact ⟨1, by simp [hik]⟩
      · exact ⟨0, by simp [Finsupp.single_apply, hik]⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by rw [map_add, map_add, ha', hb']⟩
    | smul t a _ ha =>
      obtain ⟨a', ha'⟩ := ha
      exact ⟨t * a', by rw [LinearMap.map_smul_of_tower, ← ha', map_mul, Algebra.smul_def]⟩
  rw [← hx, ← x.sum_repr y]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨a, ha⟩ := hy _ (hc i)
  rw [Module.Basis.coord_apply] at ha
  rw [← ha, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

set_option maxHeartbeats 1600000 in

theorem rhoAtG_of_pair (D : Formalism.BasicNotions.D7) {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : HidaSetting p n' W Qq O Kf ι σ j w) {m : ℕ}
    (r : ℕ) (TT : Finset (Fin n')) (d : Fin n' → ℕ) (rest lam : Fin n' → Fin (m + 1) → ℤ) (hlam : lam = flW d + rest)
    (hdr : IsDominant rest) (c0 loss : ℕ) (hord : ordMax r rest ≤ loss) (bK : ℝ) (e : Edge W Qq (m + 1))
    (he : IsEdge p n' r e) (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hP : PairAt p n' ι σ w r TT d rest lam c0 bK e Θ) :
    ∃ κ : ℕ, (κ : ℝ) ≤ bK ∧ RhoAtG p n' ι σ w r TT d rest lam c0 loss κ e Θ := by
  classical
  obtain ⟨κ0, κf, Ψ0, Ψf, hκ, a1, a2, a3, b1, b2, b3, hon, hop⟩ := hP
  have hw := w_ne_zero h
  have hp0 : (p : Kf) ≠ 0 := by rw [Formalism.L2.G.Model.p_eq h]; exact pow_ne_zero _ hw
  have hfd : IsDominant (flW (m := m) d) := flW_dom _
  have hdl : IsDominant lam := by rw [hlam]; exact isDominant_add hfd hdr
  have hAr : Ar r lam = Ar r (flW (m := m) d) + Ar r rest := by rw [hlam]; exact Ar_add r _ _
  have hM := Formalism.L2.G.Model.products_sections_integral D
  set cw : Kf := algebraMap O Kf w with hcw
  have bpl := fun e' (he' : IsEdge p n' r e') => Formalism.L2.G.Model.bePerfect p n' W Qq O Kf ι σ j w h m r lam hdl e' he'
  have bpf := fun e' (he' : IsEdge p n' r e') =>
    Formalism.L2.G.Model.bePerfect p n' W Qq O Kf ι σ j w h m r (flW (m := m) d) hfd e' he'
  obtain ⟨xb, -⟩ := Formalism.L2.G.Model.hlSpans p n' W Qq O Kf ι σ j w h m (flW (m := m) d) hfd e.tgt he.2.1
  have : Module.Finite Kf (Vsp Kf (flW (m := m) d)) := Module.Finite.of_basis xb
  let mulR : Vsp Kf rest → (Vsp Kf (flW (m := m) d) →ₗ[Kf] Vsp Kf lam) := fun β =>
    (LinearMap.mulRight Kf (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)).restrict (fun x hx => V_mul Kf hlam hfd hdr hx β.2)
  have hmulR : ∀ β y, ((mulR β y : Vsp Kf lam) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := fun β y => rfl
  let Λ : Vsp Kf rest → (Module.Dual Kf (Vsp Kf (flW (m := m) d)) →ₗ[Kf] Module.Dual Kf (Vsp Kf lam)) := fun β =>
    ((p : Kf) ^ κ0) • (Ψ0.symm.toLinearMap ∘ₗ mulR β ∘ₗ Ψf.toLinearMap)
  have hΛ : ∀ β T, Λ β T = Ψ0.symm ((p : Kf) ^ κ0 • mulR β (Ψf T)) := by
    intro β T
    simp only [Λ, LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul]
  have hΛs : ∀ (c : Kf) β T, Λ (c • β) T = c • Λ β T := by
    intro c β T
    have e : mulR (c • β) (Ψf T) = c • mulR β (Ψf T) := Subtype.ext (by
      rw [hmulR, Submodule.coe_smul, Submodule.coe_smul, hmulR, mul_smul_comm])
    rw [hΛ, hΛ, e, smul_comm ((p : Kf) ^ κ0) c, map_smul]
  let ρ : Vsp Kf rest → (Vsp Kf lam →ₗ[Kf] Vsp Kf (flW (m := m) d)) := fun β =>
    (Module.evalEquiv Kf (Vsp Kf (flW (m := m) d))).symm.toLinearMap ∘ₗ
      (((p : Kf) ^ Ar r rest) • Λ β).dualMap ∘ₗ Module.Dual.eval Kf (Vsp Kf lam)
  have hρ : ∀ β T u, T (ρ β u) = (p : Kf) ^ Ar r rest * Λ β T u := by
    intro β T u
    simp only [ρ, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.apply_evalEquiv_symm_apply,
      LinearMap.dualMap_apply, Module.Dual.eval_apply, LinearMap.smul_apply, smul_eq_mul]
  have hI : ∀ β u T, be p r (flW d) (ρ β u) T = be p r lam u (Λ β T) := by
    intro β u T
    unfold be
    rw [map_smul, map_smul, hρ, smul_eq_mul, smul_eq_mul, hAr, zpow_add₀ hp0, mul_assoc]

  have hmem : ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → ∀ β ∈ Re p ι σ w r rest e'.dual,
      ∀ T ∈ Re' p ι σ w r (flW d) e', Λ β T ∈ Re' p ι σ w r lam e' := by
    intro e' he' htg β hβ T hT
    rw [hΛ]
    exact b2 e' he' htg _ (edge_lattice_mul_of_weight_sum D hM p ι σ w hw r hlam hfd hdr e'.dual (hmulR β _) (a2 e' he' htg T hT) hβ)
  have hed := fun e' (he' : IsEdge p n' r e') => (Formalism.L2.G.Model.dual_edge h m r e' he').1

  have hβH : ∀ β ∈ Re p ι σ w r rest e.dual, ∃ β' ∈ HL (O := O) ι σ rest (latDual e.tgt), cw ^ (-(loss : ℤ)) • β' = β :=
    fun β hβ => mem_scale.1 (Re_le_scale_HL h m r rest hdr e.dual (hed e he) loss hord hβ)
  refine ⟨κ0 + κf, hκ, {β : Vsp Kf rest // β ∈ Re p ι σ w r rest e.dual}, fun β => ρ β.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro β u hu
    rw [(bpf e he).2]
    intro T hT
    rw [hI]
    exact ((bpl e he).1 _).1 (hmem e he rfl β.1 β.2 T hT) u hu
  · intro β e' he' htg u hu
    obtain ⟨β', hβ', hβe⟩ := hβH β.1 β.2
    have hβ'' : β' ∈ Re p ι σ w r rest e'.dual :=
      (Formalism.L2.G.Model.dualInclusionLattices p n' W Qq O Kf ι σ j w h m r rest hdr e'.dual (hed e' he')).1 (by
        show β' ∈ HL (O := O) ι σ rest (latDual e'.tgt)
        rw [htg]; exact hβ')
    refine mem_scale.2 ⟨cw ^ (loss : ℤ) • ρ β.1 u, ?_, by
      rw [smul_smul, ← zpow_add₀ hw]; simp⟩
    rw [(bpf e' he').2]
    intro T hT
    rw [be_smulK_left, hI, ← hβe, hΛs, be_smulK_right, ← mul_assoc, ← zpow_add₀ hw]
    simp only [add_neg_cancel, zpow_zero, one_mul]
    exact ((bpl e' he').1 _).1 (hmem e' he' htg β' hβ'' T hT) u hu
  · intro β u hu
    obtain ⟨β', hβ', hβe⟩ := hβH β.1 β.2
    refine mem_scale.2 ⟨((p : Kf) ^ Ar r rest * cw ^ (-(loss : ℤ)))⁻¹ • ρ β.1 u, ?_, by
      rw [smul_smul, mul_inv_cancel₀ (mul_ne_zero (zpow_ne_zero _ hp0) (zpow_ne_zero _ hw)), one_smul]⟩
    apply HL_refl h _ hfd e.tgt he.2.1
    intro T hT
    rw [map_smul, hρ, ← hβe, hΛs, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    have e1 : ((p : Kf) ^ Ar r rest * cw ^ (-(loss : ℤ)))⁻¹ * ((p : Kf) ^ Ar r rest * (cw ^ (-(loss : ℤ)) * Λ β' T u)) =
        Λ β' T u := by
      have h1 := zpow_ne_zero (Ar r rest) hp0
      have h2 := zpow_ne_zero (-(loss : ℤ)) hw
      field_simp
    rw [e1, hΛ]
    have h3 : mulR β' (Ψf T) ∈ HL (O := O) ι σ lam (latDual e.tgt) := by
      have := HL_mul D hM ι σ hlam hfd hdr (latDual e.tgt) cw hw 0 0 (hmulR β' (Ψf T))
        (mem_scale.2 ⟨_, a1 T hT, by simp⟩) (mem_scale.2 ⟨_, hβ', by simp⟩)
      obtain ⟨z, hz, hze⟩ := mem_scale.1 this
      rw [← hze]
      simpa using hz
    exact b1 _ h3 u hu
  · intro β F s u hu
    obtain ⟨F', hF', hT⟩ := hop β.1 F s u hu
    refine ⟨F', hF', ?_⟩
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff Kf]
    intro T
    rw [map_sub, sub_eq_zero, hρ, hΛ, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact hT T _ (hmulR β.1 (Ψf T))
  · intro u hu hall
    refine mem_scale.2 ⟨cw ^ (-(1 : ℤ)) • u, ?_, by rw [smul_smul, ← zpow_add₀ hw]; simp⟩
    rw [(bpl e he).2]
    intro G hG
    have key : ∀ z ∈ Submodule.span O {z : Vsp Kf lam | ∃ y ∈ Re p ι σ w r (flW d) e.dual,
        ∃ β ∈ Re p ι σ w r rest e.dual, (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)},
        be p r lam (cw ^ (-(1 : ℤ)) • u) (Ψ0.symm z) ∈ Set.range (algebraMap O Kf) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨y, hy, β, hβ, hzy⟩ := hz
        have hT := a3 y hy
        obtain ⟨z', hz', hz'e⟩ := mem_scale.1 (hall ⟨β, hβ⟩)
        obtain ⟨a, ha⟩ := ((bpf e he).1 _).1 hT z' hz'
        have e1 : Λ β (Ψf.symm ((p : Kf) ^ κf • y)) = ((p : Kf) ^ κ0 * (p : Kf) ^ κf) • Ψ0.symm z := by
          rw [hΛ, Ψf.apply_symm_apply, map_smul, map_smul, map_smul, smul_smul]
          congr 2
          apply Subtype.ext
          rw [hmulR, hzy]
        have e2 := hI β u (Ψf.symm ((p : Kf) ^ κf • y))
        rw [e1, be_smulK_right] at e2
        have e2' : be p r (flW d) (ρ β u) (Ψf.symm ((p : Kf) ^ κf • y)) =
            cw ^ ((2 * (κ0 + κf) + 1 : ℕ) : ℤ) * algebraMap O Kf a := by
          rw [← hz'e, be_smulK_left, ha]
        rw [e2'] at e2
        refine ⟨a, ?_⟩
        rw [be_smulK_left]
        have e3 : (p : Kf) ^ κ0 * (p : Kf) ^ κf = cw ^ ((2 * (κ0 + κf) : ℕ) : ℤ) := by
          rw [← pow_add, Formalism.L2.G.Model.p_eq h, ← pow_mul, zpow_natCast]
        rw [e3] at e2
        have e4 : cw ^ ((2 * (κ0 + κf) + 1 : ℕ) : ℤ) = cw ^ ((2 * (κ0 + κf) : ℕ) : ℤ) * cw := by
          rw [zpow_natCast, zpow_natCast, pow_succ]
        rw [e4, mul_assoc] at e2
        have e5 := mul_left_cancel₀ (zpow_ne_zero _ hw) e2
        rw [← e5, ← mul_assoc, zpow_neg, zpow_one, inv_mul_cancel₀ hw, one_mul]
      | zero => exact ⟨0, by simp [be]⟩
      | add a b _ _ ha hb =>
        obtain ⟨a', ha'⟩ := ha
        obtain ⟨b', hb'⟩ := hb
        exact ⟨a' + b', by rw [map_add, map_add, be_add_right, ha', hb']⟩
      | smul t a _ ha =>
        obtain ⟨a', ha'⟩ := ha
        exact ⟨t * a', by rw [← algebraMap_smul Kf t a, map_smul, be_smulK_right, ← ha', map_mul]⟩
    have := key _ (hon (b3 G hG))
    rwa [Ψ0.symm_apply_apply] at this

end Formalism.MainNotions.TestSideCounting
