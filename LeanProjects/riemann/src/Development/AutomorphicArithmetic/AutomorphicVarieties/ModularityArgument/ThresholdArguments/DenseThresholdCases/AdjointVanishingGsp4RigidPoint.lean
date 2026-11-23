import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ExistsPlaceAbovePrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPhiEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWPtAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNiceFour
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private factor_abs irr_conj free_up par' from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.ExistsPlaceAbovePrime
open UpperTheory.GalN.V
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
section Alg
open Matrix
end Alg
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
end Gal
section Core
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
theorem adjoint_vanishing_gsp4_rigid_point (hU : _root_.UpperTheory.V.Ws.UnramifiedInputs) (hAd : _root_.UpperTheory.V.Th.AdjointLiftingTheorem) {D : Raw Ω c} (hG : D.Good) {T : Tower D} (hF : T.Fit) (hD : T.Deep) {c' : Coef l}
    {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (y : X.A →ₐ[c'.O] PadicAlgCl l) (ι : PadicAlgCl l ≃+* ℂ)
    (r r₁ : G ℚ Ω →* M4 (PadicAlgCl l)) (hconj : IsConj4 r r₁)
    (hres : r₁.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r)
    (hw : T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l))) (hc : Continuous r) (hm : D.Mult r)
    (hi : Irr (r.comp T.L.fixingSubgroup.subtype)) (haut : Af.IsAut ι (r.toHomUnits.comp (resQ T.L)))
    (hWit : _root_.UpperTheory.V.Z.Win.WitA ι (r.toHomUnits.comp (resQ T.L))) (hf : FreeAt l (r.toHomUnits.comp (resQ T.K))) :
    ∃ ρ : K.V.frame.G₀ →* GL (Fin 4) (Qbar l), ρ.comp K.V.pr = K.rhoQ 0 (r.comp (resQ T.F)) ∧ AdZero K.V ρ := by
  obtain ⟨⟨B, -⟩, hB⟩ := _root_.UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link hU D T hF hD c' h K X 0
  obtain ⟨φ, hφ⟩ := hB B
  obtain ⟨u, hu⟩ := hconj
  have hcj : ∀ g, K.rhoQ 0 (X.P.map (y : X.A →+* PadicAlgCl l)).r g = u * K.rhoQ 0 (r.comp (resQ T.F)) g * u⁻¹ := fun g => by
    apply Units.ext
    rw [← hres, Units.val_mul, Units.val_mul, K.rho_val, K.rho_val, MonoidHom.comp_apply, MonoidHom.comp_apply, hu,
      Matrix.mul_smul, Matrix.smul_mul]
  have hrep₁ : (Link.pt φ y).IsRep (K.rhoQ 0 _) := auRep D T c' h K X B 0 φ hφ y _ fun _ => rfl
  have hrep : (Link.pt φ y).IsRep (K.rhoQ 0 (r.comp (resQ T.F))) := by
    refine Eq.trans hrep₁ ((AlgebraTools.Det.repApi _).2.2.2.2.2.2.2 _ u fun g => ?_).symm
    exact congrArg Units.val (eq_mul_inv_iff_mul_eq.1 (hcj g)).symm
  have hcρ := Pt.rho_cont K 0 (r := r.comp (resQ T.F)) (hc.comp (Af.continuous_restrictScalarsHom ℚ T.F Ω))
  have hirr : Af.IsIrr (K.rhoQ 0 (r.comp (resQ T.F))) :=
    (auIrr _ (r.comp (resQ T.L)) hi fun g => ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩).2 (K.twc 0)
  have hfull : Eb.Full (K.rhoQ 0 (r.comp (resQ T.F))) :=
    (AlgebraTools.Det.irrIffSpan (W.mat _)).1 fun N hN => hirr.2.2 N le_top fun g v hv => hN g v hv
  obtain ⟨hs, hq, -⟩ := phiKer K.V
  obtain ⟨ρ, hρ, hfull', -⟩ := factor_abs (Link.pt φ y).D K.V.pr hs _ (by norm_num) hfull hrep
  refine ⟨ρ, hρ, ?_⟩
  have hanti : StrictAnti fun i => (D.wts4 i : ℤ) := by
    have := hG.two_le
    refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
    fin_cases i <;> simp [Raw.wts4] <;> omega
  obtain ⟨m, hmm, k, hk, hmk⟩ := Pt.ptWts K X B 0 φ hφ y _ (fun i => by simp) hw
  obtain ⟨π, hreg, hatt⟩ := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hU.pr T.L Ω l ι 4 _).2.1.1 haut
  have haut' : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (K.rhoQ 0 (r.comp (resQ T.F))) := by
    have e : Af.tw ((r.comp (resQ T.F)).comp (resLe T.F_le)).toHomUnits 1 = r.toHomUnits.comp (resQ T.L) := by
      ext g : 2
      rw [Af.tw_val, MonoidHom.one_apply, Units.val_one, one_smul]
      rfl
    refine _root_.UpperTheory.GalN.V.point_automorphy_w_of_gsp_cusp_sub_rank_four hU.pr K 0 ι _ (fun g => hm _) 1 π 0 1 continuous_const one_pos (by simp) (fun A _ s _ => by simp) hreg ?_ ?_ <;>
      rwa [e]
  have hunr := Pt.ptUnr K 0 (X.P.map (y : X.A →+* PadicAlgCl l)).r fun g hg => by
    change (y : X.A →+* PadicAlgCl l).mapMatrix (X.P.r g) = 1
    rw [X.pair.kill g hg, map_one]
  have hfl : ∀ v : W.Vl l T.L, W.HasFlag ((K.rhoQ 0 (r.comp (resQ T.F))).comp (Dec (F := T.L) (K.s.A v)).subtype)
      ((Link.pt φ y).psi v) := fun v => by
    obtain ⟨a, ha⟩ := Pt.ptFlag K X B 0 φ hφ y v
    refine ⟨a * u, fun s => ?_⟩
    have h1 := ha s
    rw [MonoidHom.comp_apply, hcj] at h1
    simpa only [mul_inv_rev, mul_assoc, MonoidHom.comp_apply] using h1
  have hapt : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι (Link.pt φ y) ρ := by
    refine ⟨hq.continuous_iff.2 ?_, hρ ▸ hrep, ?_, hρ ▸ haut', ?_, fun v => ?_⟩
    · have e : (ρ : _ → _) ∘ K.V.pr = K.rhoQ 0 (r.comp (resQ T.F)) := congrArg DFunLike.coe hρ
      exact e ▸ hcρ
    · exact auArith hU.pr.toClassicalTheorems.litN.aut.art D T c' h K X B φ hφ y _ (fun _ => rfl) (Pt.psi_cont _) _ hanti hw
    · rintro _ ⟨g, hg, rfl⟩
      have h1 := hunr g hg
      rw [hcj, mul_inv_eq_one, mul_eq_left] at h1
      exact (DFunLike.congr_fun hρ g).trans h1
    · have h1 := hfl v
      rw [← hρ] at h1
      exact h1
  have hirr₀ : U3.MatIrr ⊤ (W.mat ρ) := fun N hN => (AlgebraTools.Det.irrIffSpan (W.mat ρ)).2 hfull' N fun g v hv => hN g trivial v hv
  have hfree : Free K.V.frame fun v => (Link.pt φ y).psi v := fun v : W.Vl l T.L => by
    obtain ⟨g, hg, hfr⟩ := free_up T.K T.L r.toHomUnits hf (K.twc 0) (K.s.A v) (by simpa using (K.s.hA v _).2 v.2) _ (hfl v)
    refine ⟨g, ?_, hfr⟩
    have e : K.V.ε (toGS Ω K.V.S' (W.resP T.L Ω g)) = cycZ (W.Lp T.L) Ω l (W.resP T.L Ω g) := DFunLike.congr_fun K.V.hε _
    exact e.trans hg
  exact hAd l T.L Ω K.s K.V K.hV K.noMu c' K.large 4 (by omega) le_rfl K.r K.v0 B ι _ ρ
    (_root_.UpperTheory.V.Th.nice0four_alt ι _ ρ hapt hirr₀ hfree (P1.condC D T hF hD c' h K) (P1.condD D T hF hD c' h K))
    (par' _ m (fun v i j hij => by have h1 := hmm v i j; have h2 := hanti hij; simp only at h1 h2; omega) k hk hmk)
end Core
section Rg
open scoped Matrix TensorProduct
section BK
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
end BK
end Rg
end
