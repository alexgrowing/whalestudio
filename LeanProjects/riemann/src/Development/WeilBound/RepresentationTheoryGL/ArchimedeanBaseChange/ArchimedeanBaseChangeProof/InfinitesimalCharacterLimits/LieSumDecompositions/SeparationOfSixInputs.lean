import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.SplitInv
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PChordA
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTw
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.InfInd2Holds

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

namespace TwistSymmetryDecomposition

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem tw_tw_neg {N : ℕ} (U : Submodule ℂ (Sm E N)) (w : ℂ) : tw (tw U w) (-w) = U := by
  ext ψ
  constructor
  · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    change mulChi N (Model.absC E (-w)) (mulChi N (Model.absC E w) φ) ∈ U
    rw [ParabolicProjection.mulChi_absC_neg]
    exact hφ
  · intro h
    exact ⟨mulChi N (Model.absC E w) ψ, ⟨ψ, h, rfl⟩, ParabolicProjection.mulChi_absC_neg N w ψ⟩

theorem pE_sub_imag (N r : ℕ) (c w : ℂ) (hw : w.re = 0) :
    pE E N r (c - w * r * (Module.finrank ℚ E : ℂ)) = pE E N r c := by
  simp [pE, Complex.sub_re, Complex.mul_re, hw]

theorem central_tw {a : ℕ} (w e : ℂ) (ψ : Sm E a)
    (hψ : ∀ (t : ℝ) m, ψ.1 (splitCentre E a t * m) = Complex.exp (e * t) * ψ.1 m) :
    ∀ (t : ℝ) m, (mulChi a (Model.absC E w) ψ).1 (splitCentre E a t * m) =
      Complex.exp ((e + w * a * (Module.finrank ℚ E : ℂ)) * t) * (mulChi a (Model.absC E w) ψ).1 m := by
  intro t m
  rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hψ, ExponentTwist.splitCentre_eq, ExponentTwist.chiDet_aT le_rfl,
    add_mul, Complex.exp_add]
  ring

theorem hyp_tw {N : ℕ} {τ : E →+* ℂ} {U : Submodule ℂ (Sm E N)} (hU : Hyp τ U) (w : ℂ) (hw : w.re = 0) :
    Hyp τ (tw U w) := by
  obtain ⟨⟨hst, haut⟩, ⟨S, hSU, hS⟩, hnp, ⟨z, hz, hzU⟩, ⟨m, hm, hnd⟩, hreg⟩ := hU
  classical
  refine ⟨⟨ParabolicProjection.isStable_tw hst w, ?_⟩, ⟨S.image (mulChi N (Model.absC E w)), ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact (haut φ hφ).mulChi _
  · intro x hx
    rw [Finset.coe_image] at hx
    obtain ⟨φ, hφ, rfl⟩ := hx
    exact ⟨φ, hSU hφ, rfl⟩
  · intro W' hW' hSW'
    have h1 : U ≤ tw W' (-w) := hS _ (ParabolicProjection.isStable_tw hW' (-w)) fun φ hφ =>
      ⟨mulChi N (Model.absC E w) φ, hSW' (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hφ)),
        ParabolicProjection.mulChi_absC_neg N w φ⟩
    rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨ψ, hψ, e⟩ := h1 hφ
    change mulChi N (Model.absC E w) φ ∈ W'
    rw [← e]
    change mulChi N (Model.absC E w) (mulChi N (Model.absC E (-w)) ψ) ∈ W'
    rw [ParabolicProjection.mulChi_absC_neg']
    exact hψ
  · rintro _ ⟨φ, hφ, rfl⟩ r hr hrN c hc
    have h := expTw_holds E N φ w (haut φ hφ) r hr hrN c hc
    have h2 := hnp φ hφ r hr hrN _ h
    rwa [pE_sub_imag N r c w hw] at h2
  · refine ⟨z + w * N * (Module.finrank ℚ E : ℂ), ?_, ?_⟩
    · simp [Complex.add_re, Complex.mul_re, hz, hw]
    · rintro _ ⟨φ, hφ, rfl⟩ t g
      exact central_tw w z φ (hzU φ hφ) t g
  · exact ⟨_, GlobalTheory.NormIndCap.hasInfCharGL_map_mulChi hm (Model.absC E w), hnd.map (add_left_injective _)⟩
  · intro τ'
    obtain ⟨m', hm', hnd'⟩ := hreg τ'
    exact ⟨_, GlobalTheory.NormIndCap.hasInfCharGL_map_mulChi hm' (Model.absC E w), hnd'.map (add_left_injective _)⟩

theorem core (h1 : SliceU) (h2 : Blocks) (h3 : Leaf) (h4 : Node) (h6 : TwConc) (τ : E →+* ℂ) :
    ∀ (N : ℕ) (U : Submodule ℂ (Sm E N)), 0 < N → Hyp τ U → ∀ φ ∈ U, φ ≠ 0 → Conc U φ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro U hN hU φ hφ hne
  by_cases hneg : ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, pE E N r c < 0
  · exact h3 E N τ hN U hU φ hφ hneg hne
  push_neg at hneg
  obtain ⟨r, hr, hrN, c, hc, hc0⟩ := hneg
  have hc0' : pE E N r c = 0 := le_antisymm (hU.2.2.1 φ hφ r hr hrN c hc) hc0
  obtain ⟨s, rfl⟩ : ∃ s, N = r + s := ⟨N - r, by omega⟩
  have hs : 0 < s := by omega
  obtain ⟨z, hz, hzU⟩ := hU.2.2.2.1
  have hd : (Module.finrank ℚ E : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  have hN0 : ((r + s : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = -z / (((r + s : ℕ) : ℂ) * (Module.finrank ℚ E : ℂ)) := ⟨_, rfl⟩
  have hw : w.re = 0 := by
    have e : (((r + s : ℕ) : ℂ) * (Module.finrank ℚ E : ℂ)) = (((r + s) * Module.finrank ℚ E : ℕ) : ℂ) := by
      push_cast; ring
    rw [hwdef, e, Complex.div_natCast_re, Complex.neg_re, hz, neg_zero, zero_div]
  have hzw : z + w * ((r + s : ℕ) : ℂ) * (Module.finrank ℚ E : ℂ) = 0 := by
    rw [hwdef]
    field_simp
    ring
  have hU' : Hyp τ (tw U w) := hyp_tw hU w hw
  have hsplit : SplitInv (tw U w) := by
    rintro _ ⟨ψ, hψ, rfl⟩ t g
    exact ChordArithmetic.central_twist w z hzw ψ (hzU ψ hψ) t g
  have hφ' : mulChi (r + s) (Model.absC E w) φ ∈ tw U w := ⟨φ, hφ, rfl⟩
  have hne' : mulChi (r + s) (Model.absC E w) φ ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hne
  have hc' : c - -w * r * (Module.finrank ℚ E : ℂ) ∈ Exp r (mulChi (r + s) (Model.absC E w) φ).1 := by
    refine expTw_holds E (r + s) (mulChi (r + s) (Model.absC E w) φ) (-w) ((hU.1.2 φ hφ).mulChi _) r hr hrN c ?_
    rw [ParabolicProjection.mulChi_absC_neg]
    exact hc
  have hpc' : pE E (r + s) r (c - -w * r * (Module.finrank ℚ E : ℂ)) = 0 := by
    rw [pE_sub_imag (r + s) r c (-w) (by simp [hw])]
    exact hc0'
  obtain ⟨T, hT, hTφ⟩ := h1 E r s hr hs (tw U w) hU'.1 hU'.2.1 hsplit hU'.2.2.2.2.2 _ hφ' _ hc'
  obtain ⟨J, P, W₁, W₂, hW, hP, hsum, hind⟩ := h2 E r s τ hr hs (tw U w) hU' hsplit _ T hT hpc'
  obtain ⟨j, hj, hPj⟩ : ∃ j ∈ J, P j (T (mulChi (r + s) (Model.absC E w) φ)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hTφ
    rw [← hsum _ hφ']
    exact Finset.sum_eq_zero hcon
  have hconc' : Conc (tw U w) (mulChi (r + s) (Model.absC E w) φ) := by
    refine h4 E r s hr hs (tw U w) (W₁ j) (W₂ j) (P j ∘ₗ T) hU'.1 (hW j hj).1.1 (hW j hj).2.1 ?_ ?_ ?_ ?_ _ hφ' hPj
    · intro o ψ hψ
      simp only [LinearMap.comp_apply]
      rw [hT.equiv o ψ hψ, hP j hj o ψ hψ]
    · intro ψ hψ
      exact hind j hj ψ hψ
    · intro ψ hψ hψ0
      exact ih r (by omega) (W₁ j) hr (hW j hj).1 ψ hψ hψ0
    · intro ψ hψ hψ0
      exact ih s (by omega) (W₂ j) hs (hW j hj).2 ψ hψ hψ0
  have h := h6 E (r + s) (tw U w) (-w) (by simp [hw]) hU'.1 _ hφ' hconc'
  rwa [tw_tw_neg, ParabolicProjection.mulChi_absC_neg] at h

def evalAt {N : ℕ} (h : GA E N) : Sm E N →ₗ[ℂ] ℂ := (LinearMap.proj h).comp (Sm E N).subtype

theorem typeB_map {N : ℕ} {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)}
    {U : Submodule ℂ (Sm E N)} {T : Sm E N →ₗ[ℂ] Sm E N} (haut : ∀ φ ∈ U, IsAutForm φ)
    (hTe : ∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ)) {φ : Sm E N} (hφ : φ ∈ U) (hT : TypeB K W φ) :
    TypeB K W (T φ) := by
  obtain ⟨hK, hW⟩ := hT
  constructor
  · intro u hu g
    have e1 : act (Op.fin u) φ = φ := Subtype.ext (funext fun x => hK u hu x)
    calc (T φ).1 (g * finGL E N u) = (act (Op.fin u) (T φ)).1 g := rfl
      _ = (T φ).1 g := by rw [← hTe _ φ hφ, e1]
  · intro g
    set V : Submodule ℂ (Sm E N) := Submodule.span ℂ (Set.range fun k => cptRep E N k φ) with hV
    have : FiniteDimensional ℂ V := (haut φ hφ).kfin
    have hF : ∀ k, cptRep E N k φ ∈ V := fun k => Submodule.subset_span ⟨k, rfl⟩
    let Sd : Submodule ℂ (Module.Dual ℂ V) := Submodule.span ℂ (Set.range fun h : GA E N => evalAt h ∘ₗ V.subtype)
    have hco : Sd.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      rw [Submodule.mem_bot]
      apply Subtype.ext
      apply Subtype.ext
      funext h
      exact hv _ (Submodule.subset_span ⟨h, rfl⟩)
    have htop : Sd = ⊤ := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Sd), hco, Submodule.dualAnnihilator_bot]
    have key : ∀ f ∈ Sd, (fun k => f ⟨cptRep E N k φ, hF k⟩) ∈ W := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        exact hW h
      | zero => exact W.zero_mem
      | add x y _ _ hx hy => exact W.add_mem hx hy
      | smul a x _ hx => exact W.smul_mem a hx
    have hℓ := key (evalAt g ∘ₗ T ∘ₗ V.subtype) (htop ▸ Submodule.mem_top)
    convert hℓ using 1
    funext k
    change (T φ).1 (g * infGL E N (Unitary.toUnits k)) = (T (cptRep E N k φ)).1 g
    calc (T φ).1 (g * infGL E N (Unitary.toUnits k)) = (act (Op.cpt k) (T φ)).1 g := rfl
      _ = (T (cptRep E N k φ)).1 g := by rw [← hTe _ φ hφ]; rfl

end TwistSymmetryDecomposition

theorem allLeaves_and {E : Type} [Field E] [NumberField E] [IsCMField E]
    {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} : ∀ {N : ℕ} (t : Tr E N), t.AllLeaves P → t.AllLeaves Q →
      t.AllLeaves (fun M V => P M V ∧ Q M V)
  | _, .leaf _ _, hp, hq => ⟨hp, hq⟩
  | _, .node t₁ t₂, hp, hq => ⟨allLeaves_and t₁ hp.1 hq.1, allLeaves_and t₂ hp.2 hq.2⟩

theorem separation_of_six_inputs (h1 : SliceU) (h2 : Blocks) (h3 : Leaf) (h4 : Node) (h5 : Types) (h6 : TwConc) : Sep4 := by
  intro E _ _ _ N W hW
  obtain ⟨Ω, hΩ, hK⟩ := h5 E N W hW
  refine ⟨Ω, hΩ, fun K hKo => ?_⟩
  obtain ⟨Θ, hΘ, hty⟩ := hK K hKo
  refine ⟨Θ, hΘ, ?_⟩
  intro U hN hst haut hS hnp hci hreg hU0
  obtain ⟨S, hSty, hSU, hSmin⟩ := hS

  obtain ⟨φ, hφS, hne⟩ : ∃ φ ∈ S, φ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hbot : IsStable (⊥ : Submodule ℂ (Sm E N)) := by
      intro o ψ hψ
      rw [Submodule.mem_bot] at hψ ⊢
      rw [hψ, map_zero]
    exact hU0 (eq_bot_iff.2 (hSmin ⊥ hbot fun ψ hψ => (Submodule.mem_bot ℂ).2 (hcon ψ hψ)))
  have hφ : φ ∈ U := hSU hφS
  have hfg : FinGen U := ⟨S, hSU, hSmin⟩
  let τ : E →+* ℂ := Classical.arbitrary _
  obtain ⟨m, hm, hnd⟩ := hreg τ
  obtain ⟨t, T, ht, hpos, hTe, hTs, hTφ⟩ :=
    TwistSymmetryDecomposition.core h1 h2 h3 h4 h6 τ N U hN ⟨⟨hst, haut⟩, hfg, hnp, hci, ⟨m, hm, hnd⟩, hreg⟩ φ hφ hne
  exact ⟨t, T, ht,
    allLeaves_and t hpos (hty t (T φ) ht (hTs φ hφ) hTφ (TwistSymmetryDecomposition.typeB_map haut hTe hφ (hSty φ hφS))), hTe, hTs,
    φ, hφ, hTφ⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
