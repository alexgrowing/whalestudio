import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleGeometryHermitianForm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SphericalFixesPureVacuumVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleGeometryHermitianFormStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.StabFinAdelic
theorem stabilizer_kappa_of_isThetaSubgroup : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (X : HSp D) (a a' : ℕ) (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ)
    (N' : Submodule ℂ ((Fin a' × Fin (a + a') → AF D.host.F) → ℂ)),
    IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' → ∀ g ∈ GfC X, ∀ Φ ∈ N', om' (1, kapX X e hJ g) Φ ∈ N' := by
  classical
  intro hP D X a a' e Bs Γ Xc om om' hT hJ N' hN g hg Φ hΦ
  have hinf := GlobalTheory.InfKill.smul_mat_kapX_sub_one D X e hJ g hg
  obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.T.spherical_vector_fixes_vacua hP _ _ _ Bs _ _ Γ Xc om om' hT
  have hfix : ∀ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb, ∃ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F), ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F),
      T ⊆ S → S₀ ⊆ S → ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J,
      (∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
      (∀ w ∈ S, ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin D.host.F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V Γ.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V Γ.W w) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V' Γ.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V' Γ.W w) →
      om' (1, k) Ψ = Ψ := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, φ, -, hφ, hcof, rfl⟩ := hx
      refine ⟨hcof.toFinset, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => ?_⟩
      refine (hS₀ S hS₀S k hk1 hk2 hk3 hk4).2 f φ hφ fun w hw => ?_
      by_contra hne
      exact hw (hTS (Set.Finite.mem_toFinset _ |>.2 hne))
    | zero => exact ⟨∅, fun _ _ _ k _ _ _ _ => map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨T₁, h₁⟩ := hx
      obtain ⟨T₂, h₂⟩ := hy
      refine ⟨T₁ ∪ T₂, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => ?_⟩
      rw [map_add, h₁ S (Finset.union_subset_left hTS) hS₀S k hk1 hk2 hk3 hk4,
        h₂ S (Finset.union_subset_right hTS) hS₀S k hk1 hk2 hk3 hk4]
    | smul c x _ hx =>
      obtain ⟨T, hT'⟩ := hx
      exact ⟨T, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => by rw [map_smul, hT' S hTS hS₀S k hk1 hk2 hk3 hk4]⟩
  obtain ⟨T, hTfix⟩ := hfix Φ (hN.le hΦ)
  obtain ⟨S, l, k, hTS, hl, hprod, hkinf, hkS, hkV, hkV'⟩ := GlobalTheory.T.exists_adelicUnitary_prod_localPoints_mul_latticeStabilizer _ _ _ Bs _ _ Γ hT.geo _ hinf (T ∪ S₀)
  have hk : om' (1, k) Φ = Φ :=
    hTfix S (Finset.union_subset_left hTS) (Finset.union_subset_right hTS) k hkinf hkS hkV hkV'
  have split' : ∀ (x y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J) Ψ, om' (1, x * y) Ψ = om' (1, x) (om' (1, y) Ψ) := by
    intro x y Ψ
    rw [show ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V'.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ l' : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J),
      (∀ x ∈ l', x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F x.1)) →
      ∀ Ψ ∈ N', om' (1, (l'.map Prod.snd).prod) Ψ ∈ N' := by
    intro l'
    induction l' with
    | nil =>
      intro _ Ψ hΨ
      simp only [List.map_nil, List.prod_nil]
      rw [Prod.mk_one_one, map_one]
      exact hΨ
    | cons x l' ih =>
      intro hx Ψ hΨ
      simp only [List.map_cons, List.prod_cons]
      rw [split']
      exact hN.stabFin x.1 x.2 (hx x List.mem_cons_self) _
        (ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) Ψ hΨ)
  rw [hprod, split', hk]
  exact key l (fun x hx => (hl x hx).2) Φ hΦ
end GlobalTheory.StabFinAdelic
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_stabilizer_finite_of_theta_subgroup : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (X : HSp D) (a a' : ℕ) (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ)
    (N' : Submodule ℂ ((Fin a' × Fin (a + a') → AF D.host.F) → ℂ)),
    IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' → ∀ g ∈ GfC X, ∀ Φ ∈ N', om' (1, kapX X e hJ g) Φ ∈ N' := by
  first | exact @_root_.GlobalTheory.StabFinAdelic.stabilizer_kappa_of_isThetaSubgroup | exact _root_.GlobalTheory.StabFinAdelic.stabilizer_kappa_of_isThetaSubgroup | (intros; apply _root_.GlobalTheory.StabFinAdelic.stabilizer_kappa_of_isThetaSubgroup <;> assumption)
end
