import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ConstN

open GlobalTheory.CompanionTheory.FourierN

open Pointwise in

theorem setIntegral_add_right {A : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A] (L : AddSubgroup A)
    [Countable L] (lam : Measure A) [lam.IsAddLeftInvariant] {𝓖 : Set A} (hFD : IsAddFundamentalDomain L 𝓖 lam)
    (φ : A → ℂ) (hper : ∀ γ ∈ L, ∀ x, φ (γ + x) = φ x) (b : A) :
    ∫ x in 𝓖, φ (x + b) ∂lam = ∫ x in 𝓖, φ x ∂lam := by
  have hFD' : IsAddFundamentalDomain L (b +ᵥ 𝓖) lam := hFD.vadd_of_comm b
  have hpre : (fun x : A => x + b) ⁻¹' (b +ᵥ 𝓖) = 𝓖 := by
    ext x
    rw [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem]
    simp [add_comm]
  have h := (measurePreserving_add_right lam b).setIntegral_preimage_emb
    (MeasurableEquiv.addRight b).measurableEmbedding φ (b +ᵥ 𝓖)
  rw [hpre] at h
  exact h.trans (hFD'.setIntegral_eq hFD fun γ x => hper γ.1 γ.2 x)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem nb_inv_of_const (D : D7) (p : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (nb : hermA D p → G D p)
    (lam : Measure (hermA D p)) (𝓖 : Set (hermA D p)) (hC : CoefData (D := D) (n := p) nb lam 𝓖)
    (F : G D p → ℂ) (_hF : Continuous F) (hinv : LeftInv (GF D p) F) (β : HermE D p) (hβ : β.1 = 0)
    (hfc : ∀ g, fc ψ lam 𝓖 nb F β g = F g) (b : hermA D p) (g : G D p) : F (nb b * g) = F g := by
  obtain ⟨hnb, hlam, hFD, -⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D p p
  haveI : BorelSpace (Mx D p p) := ⟨rfl⟩
  haveI : BorelSpace (hermA D p) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : DiscreteTopology (ratHerm D p) := discrete_ratHerm
  haveI : Countable (ratHerm D p) := countable_of_Lindelof_of_discrete
  have hone : ∀ h : G D p, fc ψ lam 𝓖 nb F β h = ∫ x in 𝓖, F (nb x * h) ∂lam := by
    intro h
    refine integral_congr_ae (.of_forall fun x => ?_)
    have e : (HMul.hMul (β.1.map (incA D)) x.1 : Mx D p p) = 0 := by
      rw [hβ, Matrix.map_zero _ (map_zero _)]
      exact Matrix.zero_mul _
    show F (nb x * h) * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) x.1 : Mx D p p))) = F (nb x * h)
    rw [e, Matrix.trace_zero, halfTr_zero, neg_zero, AddChar.map_zero_eq_one, mul_one]
  have hper : ∀ γ ∈ ratHerm D p, ∀ x : hermA D p, F (nb (γ + x) * g) = F (nb x * g) := by
    intro γ hγ x
    rw [nb_add hnb, mul_assoc]
    exact hinv _ (nb_rat hnb γ hγ) _
  have e1 : F g = ∫ x in 𝓖, F (nb x * g) ∂lam := (hfc g).symm.trans (hone g)
  have e2 : F (nb b * g) = ∫ x in 𝓖, F (nb (x + b) * g) ∂lam := by
    refine (hfc _).symm.trans ((hone _).trans (integral_congr_ae (.of_forall fun x => ?_)))
    show F (nb x * (nb b * g)) = F (nb (x + b) * g)
    rw [nb_add hnb, mul_assoc]
  rw [e2, e1]
  exact setIntegral_add_right (ratHerm D p) lam hFD (fun y => F (nb y * g)) hper b

end GlobalTheory.CompanionTheory.ConstN
