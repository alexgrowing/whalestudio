import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColsSharpDictionary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdFormFromEquivariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRepresentsClassesWeightOneStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportCoeffMapBijectiveOntoValuesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRationalPointsStabiliserFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitaryStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDict_bij_of_levelMatch : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictBij X Tr hK := by
  intro D X u F Tr hK hσ hL
  obtain ⟨hψ, -, hEq, hDet, hOnto⟩ := cols_sharp_dictionary D X u hK
  obtain ⟨hJinj, hJsurj⟩ := GlobalTheory.T.transportCoeffMap_bijective_onto_values D X u F Tr
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    have hcls := (GlobalTheory.T.transport_represents_classes_weight_one D X u F Tr hK hσ hL).1
    have h1 : ∀ c, shP X u T.1 (Tr.hc c) = 0 := by
      intro c
      apply hJinj
      rw [map_zero]
      funext y
      have := congrFun (congrFun hT c) (F.val0.eY.symm y)
      simpa [colDictL, dictA] using this
    apply hDet T
    intro x
    obtain ⟨c, ⟨γ, κ, hx⟩, -⟩ := hcls x
    rw [hx, hEq, h1, map_zero, smul_zero]
  · intro φ hφ
    rw [Formalism.L2.Forms.Mu0_iff F.val0] at hφ
    obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hφ
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary D X u Tr.wt Tr.ιA hW hA hσ
    obtain ⟨hΓ, -, hs⟩ := GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ
    have hKm : ∀ h : Hfin X u, h ∈ Ku X u hK ↔ ((Tr.h0⁻¹ * Φ h * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
        F.cls0.lev.U :=
      fun h => (hL.2 h (Φ h) ((hΦ h _).2 rfl)).1
    have hχ : ∀ (h : Hfin X u) (hk : h ∈ Ku X u hK) (hy : ((Tr.h0⁻¹ * Φ h * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
        F.cls0.lev.U), ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ) = ((F.cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) :=
      fun h hk hy => (hL.2 h (Φ h) ((hΦ h _).2 rfl)).2 hk hy
    have hπ : ∀ (γ : Gam X u) (g : GL (Fin (D.R.N 0)) D.host.E),
        (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g →
        ∀ (ξ : X.Vpi u) (y y' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)),
          Formalism.L2.Forms.IsTr (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) g.1) y' y →
          Tr.J (piRep X u (iotaI X u γ) ξ) y = Tr.J ξ y' := by
      intro γ g e ξ y y' hy
      have h2 := hs γ g e
      exact Tr.J_eqv (iotaI X u γ) (iotaI X u γ).2 ξ y y' (by rw [h2]; exact hy)
    rw [Formalism.L2.Forms.lamT_zero] at hJsurj
    obtain ⟨φ', hφ'eq, hφ'g⟩ := GlobalTheory.adForm_from_equivariant _ _ (Formalism.L2.Forms.sigD D) _ _ _ _ _ F.cls0.lev
      (Gam X u) (Hinf X u) (Hfin X u) (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) Φ Tr.h0 _
      (Formalism.L2.Forms.embT D) ((D.fm u).lam 0) (X.Vpi u) (piRep X u) Tr.J hψ hKm hχ hΓ hπ hJinj hJsurj g hg
    obtain ⟨T, hT⟩ := hOnto φ' hφ'eq
    refine ⟨T, ?_⟩
    funext c z
    have hc : Φ (Tr.hc c) = F.cls0.y c * Tr.h0⁻¹ := (hΦ _ _).1 (Tr.hc_rep c)
    have e1 := congrFun (congrFun hres c) (F.val0.eY z)
    have e2 := hφ'g (F.cls0.y c)
    have e3 : Φ.symm (F.cls0.y c * Tr.h0⁻¹) = Tr.hc c := (MulEquiv.symm_apply_eq Φ).2 hc.symm
    rw [e3] at e2
    show Tr.J (shP X u T.1 (Tr.hc c)) (F.val0.eY z) = φ c z
    rw [hT, ← e2]
    simpa [Formalism.L2.Forms.res] using e1

end GlobalTheory.St
