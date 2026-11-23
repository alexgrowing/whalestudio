import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExtensionVectorThetaCompatible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
theorem transport_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ sp : SplitPlace D.host.E, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) sp.w → (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) ((P.M.loc i).real (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i))) = s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) • (P.M.loc i).real (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) := by
  intro _ hL D P X A _ _ _ i hμ j hj f y hy h hOps s hEig sp hG hJ ϖ hϖ k hk
  have hn : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hLab := isLab_std A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk
  have hsum := eig_sum X hμ j f y hy h hOps s hEig sp.w hG (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) hLab
  have hGf := GlobalTheory.DefLiftHecke.rep_mem_GfC (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0)
  classical
  let xi : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Vc D j) → Formalism.AUTREP.GAf D.host.E D.R.nV := fun γ =>
    if hγ : γ ∈ Formalism.L2.Theta.GfC (Formalism.IndefR.Links.Vc D j) then ((A.PV j).onto γ hγ).choose else 1
  have hxi : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), (A.PV j).ψ (xi γ) = γ := fun γ hγ => by
    simp only [xi, dif_pos (hGf γ hγ)]
    exact ((A.PV j).onto γ (hGf γ hγ)).choose_spec
  have hT : ∀ x ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k, TrivOutside {sp.v} x := fun x hx => hx.1
  suffices key : ∀ (m : ℕ) (e : j.1 + 1 = m) (p1 : 1 ≤ m) (p2 : m ≤ D.R.m),
      (∀ κ : Formalism.AUTREP.GAf D.host.E D.R.nV, TrivOutside {sp.v} κ →
        (κ ∈ (P.M (D.nd.mu i) m p1 p2).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧
          ∀ hκ : κ ∈ (P.M (D.nd.mu i) m p1 p2).J, (P.M (D.nd.mu i) m p1 p2).χ ⟨κ, hκ⟩ = 1) →
      NG.heckeD (P.M (D.nd.mu i) m p1 p2).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k)
          ((P.M (D.nd.mu i) m p1 p2).real (e ▸ f)) =
        s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) • (P.M (D.nd.mu i) m p1 p2).real (e ▸ f) from key _ hj _ _ hJ
  intro m e
  subst e
  intro p1 p2 hJ
  have hF : ∀ g, (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f g =
      A.eW _ hμ j (X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g))) := fun g => A.real (D.nd.mu i) hμ j f g
  have hinv : ∀ κ (hκ : κ ∈ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J), (P.M (D.nd.mu i) (j.1 + 1) p1 p2).χ ⟨κ, hκ⟩ = 1 →
      ∀ g, (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * κ) = (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f g := by
    intro κ hκ h1 g
    have hmem : (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f ∈ Formalism.L2.NG.TypeSp (P.M (D.nd.mu i) (j.1 + 1) p1 p2).wt.ρ
        (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J (P.M (D.nd.mu i) (j.1 + 1) p1 p2).χ := by
      rw [← (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real_range]
      exact LinearMap.mem_range_self _ _
    have := congrFun (hmem.2 ⟨κ, hκ⟩) g
    rw [h1] at this
    simp only [Units.val_one, one_smul] at this
    exact this
  have hmemT : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), xi γ ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k := by
    intro γ hγ
    refine (tSet_iff A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk _).2 ⟨γ, hγ, ?_⟩
    rw [hxi γ hγ, inv_mul_cancel]
    exact GlobalTheory.DefLiftHecke.one_mem_hyp _ _
  funext g
  show (∑ᶠ c : Formalism.AUTREP.GAf D.host.E D.R.nV ⧸ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J,
      if hc : ∃ x ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k,
          (x : Formalism.AUTREP.GAf D.host.E D.R.nV ⧸ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J) = c then
        (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * hc.choose) else 0) = _
  rw [finsum_cosets (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J _ (GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0)) xi _
    ?h1 ?h2 ?h3 ?h4 g]
  case h1 => exact hmemT
  case h2 =>
    intro x hx
    obtain ⟨γ, hγ, hm⟩ := (tSet_iff A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk x).1 hx
    refine ⟨γ, hγ, ?_⟩
    rw [← hxi γ hγ, ← map_inv, ← map_mul] at hm
    obtain ⟨hU, hT'⟩ := (frame_hyp A.hF (A.PV j) (A.stdV j) sp _).1 hm
    exact (hJ _ hT').1.2 hU
  case h3 =>
    intro γ hγ γ' hγ' hm
    have ht := triv_mul (triv_inv (hT _ (hmemT γ hγ))) (hT _ (hmemT γ' hγ'))
    have hU := (hJ _ ht).1.1 hm
    have hh := (frame_hyp A.hF (A.PV j) (A.stdV j) sp _).2 ⟨hU, ht⟩
    rw [map_mul, map_inv, hxi γ hγ, hxi γ' hγ'] at hh
    exact rep_inj _ _ _ hLab γ hγ γ' hγ' hh
  case h4 =>
    intro y hy y' hy' hm g0
    have ht := triv_mul (triv_inv (hT _ hy)) (hT _ hy')
    have := hinv _ hm ((hJ _ ht).2 hm) (g0 * y)
    rw [mul_assoc, mul_inv_cancel_left] at this
    exact this
  rw [Pi.smul_apply, hF g]
  calc ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * xi γ)
      = ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0),
          A.eW _ hμ j (X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g) * γ)) :=
        Finset.sum_congr rfl fun γ hγ => by rw [hF, ← mul_assoc, map_mul, hxi γ hγ]
    _ = A.eW _ hμ j (∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0),
          X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g) * γ)) := (map_sum _ _ _).symm
    _ = _ := by rw [hsum, map_smul]
end GlobalTheory.EigTransport
end
