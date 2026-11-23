import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmVecEqPhaseLetters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section
namespace GlobalTheory.SerIntLetters
open GlobalTheory.AdTh.PhaseMap GlobalTheory.SerLetters

set_option maxHeartbeats 1600000 in

theorem io_eq_phase_smul_harmLetters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → ∀ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank ≃ FVar D (Wc D i).rank (Vc D i).rank, IsLetters (T.Q.Dw ((i : ℕ) + 1)) lt → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∃ J : VsV D i ℂ →ₗ[ℂ] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ, (∀ v, J v ∈ HHa (T.Q.Dw ((i : ℕ) + 1)).mult (Vc D i).rank ℂ ComplexEmbedding.conjugate (InPsi T.Q.H) (fun τ j => wtA (κ i) (τ, j))) ∧ (∀ k : Subfield ℂ, (∀ x ∈ T.Q.c.F, x ∈ k) → ∀ v : VsV D i ℂ, (∀ m, MvPolynomial.coeff m (v : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) ∈ k) → ∀ mo, (J v).coeff mo ∈ k) ∧ ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ v, pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) (c0 v)) = ka • stdF R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) f (MvPolynomial.rename lt (J v)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hLaws hL hGrp hFam hMod hThP hTie i hstd u hu c0 hc lt hlt
  obtain ⟨ka, hka, io, hio, hJ⟩ := io_eq_phase_smul_letters D G Pl0 T0 A T R κ v₀ hL hFam hMod hThP hTie i hstd u hu c0 hc
    (⇑lt) (fun ℓ => hlt ℓ)
  let b : Formalism.L2.DIV.VVIdx (lamV D i) → VsV D i ℂ := fun j =>
    GlobalTheory.AdTh.CoefExt.up (inC T.Q.c) (lamV D i) (Formalism.L2.DIV.bVV T.Q.c.F (lamV D i) j)
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range b) := fun x _ => by
    obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) x
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hli : LinearIndependent ℂ b := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank hsp ?_
    rw [Module.finrank_eq_card_basis (Formalism.L2.DIV.bVV ℂ (lamV D i))]
  let e : Formalism.L2.DIV.VVIdx (lamV D i) → MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ := fun j =>
    MvPolynomial.map (inC T.Q.c) (io (Formalism.L2.DIV.bVV T.Q.c.F (lamV D i) j))
  let J : VsV D i ℂ →ₗ[ℂ] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ := (Module.Basis.mk hli hsp).constr ℂ e
  have hJv : ∀ a : Formalism.L2.DIV.VVIdx (lamV D i) → ℂ, J (∑ j, a j • b j) = ∑ j, a j • e j := fun a => by
    simp only [map_sum, map_smul, J]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show b j = Module.Basis.mk hli hsp j from (Module.Basis.mk_apply hli hsp j).symm, Module.Basis.constr_basis]
  refine ⟨ka, hka, J, fun v => ?_, fun k hk v hv mo => ?_, fun f hf v => ?_⟩
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) v
    rw [hJv]
    refine GlobalTheory.PtId.mem_HHa_of_span _ _ _ _ _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    exact GlobalTheory.SerLetters.map_mem_HHa (inC T.Q.c) (GlobalTheory.PtId.mem_HHa_of_span _ _ _ _ _ _ (hio _))
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) v
    have hF : ∀ x : T.Q.c.F, inC T.Q.c x ∈ k := fun x => hk _ (by rw [show inC T.Q.c x = (x : ℂ) from rfl]; exact x.2)
    let φ : T.Q.c.F →+* k := (inC T.Q.c).codRestrict k hF
    let eK : Formalism.L2.DIV.VVIdx (lamV D i) → Formalism.L2.DIV.Pol k D.what₂.Tau (Vc D i).rank := fun j =>
      MvPolynomial.map φ (Formalism.L2.DIV.bVV T.Q.c.F (lamV D i) j : Formalism.L2.DIV.Pol T.Q.c.F D.what₂.Tau (Vc D i).rank)
    have hmap : ∀ j, MvPolynomial.map k.subtype (eK j) = (b j : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) := fun j => by
      show MvPolynomial.map k.subtype (MvPolynomial.map φ _) = MvPolynomial.map (inC T.Q.c) _
      rw [MvPolynomial.map_map]
      rfl
    have hli' : LinearIndependent ℂ fun j => MvPolynomial.map k.subtype (eK j) := by
      have h2 := hli.map' (Submodule.subtype _) (Submodule.ker_subtype _)
      have e2 : (fun j => MvPolynomial.map k.subtype (eK j)) = (Submodule.subtype _) ∘ b := funext hmap
      rw [e2]
      exact h2
    have hsum : (∑ j, a j • MvPolynomial.map k.subtype (eK j)) =
        ((∑ j, a j • b j : VsV D i ℂ) : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) := by
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, hmap]
    have hcoef : ∀ m, MvPolynomial.coeff m (∑ j, a j • MvPolynomial.map k.subtype (eK j)) ∈ k.subtype.fieldRange := fun m => by
      rw [hsum]
      exact RingHom.mem_fieldRange.2 ⟨⟨_, hv m⟩, rfl⟩
    have ha : ∀ j, a j ∈ k := fun j => by
      obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.1 (coord_mem_fieldRange k.subtype eK hli' a hcoef j)
      rw [← hy]
      exact y.2
    rw [hJv, MvPolynomial.coeff_sum]
    refine Subfield.sum_mem _ fun j _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    exact Subfield.mul_mem _ (ha j) (by rw [MvPolynomial.coeff_map]; exact hF _)
  · obtain ⟨a, rfl⟩ := GlobalTheory.AdTh.CoefExt.exists_coord (inC T.Q.c) (lamV D i) v
    rw [hJv]
    simp only [map_sum, map_smul]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hJ f hf, GlobalTheory.AdTh.PhaseMap.toF_apply, smul_comm]

end GlobalTheory.SerIntLetters
