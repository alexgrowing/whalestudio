import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityCharactersFockTensorProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramesFockMapPolynomialLieActionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSubmoduleComapStableSecondMemberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSubmoduleContainsFirstMemberCoinvariantStatement

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
  GlobalTheory.HoweD GlobalTheory.HoweR

namespace GlobalTheory

theorem howeDualityReal_holds : GlobalTheory.Published.HoweDualityReal := by
  intro F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX1 hX2 hW1 hW2 _ _ _ _ hWeil τ hcX hcW
  obtain ⟨P, Q, R, S, A, C, Φ, c, c', hfr, hinj, hrange, hact1, hact2⟩ :=
    GlobalTheory.T.exists_frames_fockMap_polynomial_lie_actions F E σ hCM n d X W M ψ χX χW om hψ hX1 hX2 hW1 hW2 hWeil τ hcX hcW
  obtain ⟨-, hA, hC⟩ := hfr
  have hstab : ∀ N, GlobalTheory.Published.ThetaSubInf M ψ τ om N → ∀ w, Stab (actAt (V := fun w =>
      Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (N.comap Φ) :=
    fun N hN => GlobalTheory.T.thetaLift_submodule_comap_stable_secondMember F E σ n d X W M ψ om τ P Q R S Φ c' N hCM hN C hC hact2
  have hcoinv : ∀ N, GlobalTheory.Published.ThetaSubInf M ψ τ om N →
      tensAny (fun w => coinv (P w) (Q w) (R w) (S w) (-c w)) ≤ N.comap Φ :=
    fun N hN => GlobalTheory.T.thetaLift_submodule_contains_firstMember_coinvariants F E σ n d X W M ψ om τ P Q R S Φ c N hCM hN hrange A hA hact1
  obtain ⟨⟨L, hL⟩, hsum⟩ := GlobalTheory.T.howe_duality_characters_fock_tensor_product (InfinitePlace F) P Q R S (fun w => -c w)
  have hmap : ∀ N, GlobalTheory.Published.ThetaSubInf M ψ τ om N → (N.comap Φ).map Φ = N := by
    intro N hN
    rw [Submodule.map_comap_eq, hrange]
    exact inf_eq_right.mpr hN.1
  refine ⟨⟨L, fun m N hmono hN => hL m (fun i => (N i).comap Φ) ?_
    (fun k => ⟨hstab _ (hN k), hcoinv _ (hN k)⟩)⟩, ?_⟩
  · intro i j hij
    refine lt_of_le_of_ne (Submodule.comap_mono (hmono hij).le) ?_
    intro h
    have h' := congrArg (Submodule.map Φ) h
    rw [hmap _ (hN i), hmap _ (hN j)] at h'
    exact (hmono hij).ne h'
  · intro N N' hN hN' hne hne' heq
    refine hsum (N.comap Φ) (N'.comap Φ) (hstab _ hN) (hcoinv _ hN) ?_ (hstab _ hN') (hcoinv _ hN') ?_ ?_
    · intro h; apply hne; rw [← hmap _ hN, h, Submodule.map_top, hrange]
    · intro h; apply hne'; rw [← hmap _ hN', h, Submodule.map_top, hrange]
    · apply Submodule.map_injective_of_injective hinj
      rw [Submodule.map_sup, hmap _ hN, hmap _ hN', heq, Submodule.map_top, hrange]

end GlobalTheory

end
