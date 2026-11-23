import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdFormsOfEquivariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColsSharpDictionary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRationalPointsStabiliserFrameStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitaryStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDictInto_of_levelMatch : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictInto X Tr hK := by
  intro D X u F Tr hK hσ hL T
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary D X u Tr.wt Tr.ιA hW hA hσ
  obtain ⟨-, hΓ, hsT⟩ := GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ
  obtain ⟨hψ, -, hφ, -, -⟩ := cols_sharp_dictionary D X u hK
  have key := GlobalTheory.adForms_of_equivariant D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0)
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hinf X u) (Hfin X u)
    (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) Φ Tr.h0 D.what₂.Tau (Formalism.L2.Forms.embT D)
    ((D.fm u).lam 0) (X.Vpi u) (piRep X u) Tr.J hψ
    (fun h => (hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).1)
    (fun h hk hy => (hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).2 hk hy)
    hΓ
    (fun γ g hγ ξ y y' hy => Tr.J_eqv _ (iotaI X u γ).2 ξ y y' (by rw [hsT γ g hγ]; exact hy))
    (fun ξ => by rw [← Formalism.L2.Forms.lamT_zero]; exact Tr.J_val ξ)
    (shP X u T.1) (hφ T)
  rw [Formalism.L2.Forms.Mu0_iff F.val0]
  refine ⟨_, key, ?_⟩
  funext c z
  have hc : Φ.symm (F.cls0.y c * Tr.h0⁻¹) = Tr.hc c :=
    Φ.symm_apply_eq.2 ((hΦ (Tr.hc c) _).1 (Tr.hc_rep c)).symm
  simp only [Formalism.L2.Forms.res, LinearMap.funLeft_apply, hc]
  show Tr.J (shP X u T.1 (Tr.hc c)) z = Tr.J (shP X u T.1 (Tr.hc c)) (F.val0.eY (F.val0.eY.symm z))
  rw [Equiv.apply_symm_apply]

end GlobalTheory.St
