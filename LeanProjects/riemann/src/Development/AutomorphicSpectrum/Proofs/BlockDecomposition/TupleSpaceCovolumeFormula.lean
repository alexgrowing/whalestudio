import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicMeasureEulerProductDecomposition
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.TupCovolume

open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SiegelND.DxN PositivityTheory.SiegelWeilFormula.KWhit.MeasP
open scoped TensorProduct

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def ratCoord {d M n : ℕ} (b : Module.Basis (Fin d) F E) (Y : Fin n → Fin M → E) : Fin n × (Fin M × Fin d) → F :=
  fun p => b.repr (Y p.1 p.2.1) p.2.2

def ofCoord {d M n : ℕ} (b : Module.Basis (Fin d) F E) (c : Fin n × (Fin M × Fin d) → F) : Fin n → Fin M → E :=
  fun a i => ∑ l, c (a, (i, l)) • b l

theorem ratCoord_ofCoord {d M n : ℕ} (b : Module.Basis (Fin d) F E) (c : Fin n × (Fin M × Fin d) → F) :
    ratCoord b (ofCoord b c) = c := by
  funext p
  obtain ⟨a, i, l⟩ := p
  simp [ratCoord, ofCoord, Finsupp.single_apply]

theorem ratCoord_injective {d M n : ℕ} (b : Module.Basis (Fin d) F E) :
    Function.Injective (ratCoord (M := M) (n := n) b) := by
  intro Y Y' h
  funext a i
  refine b.repr.injective (Finsupp.ext fun l => ?_)
  exact congrFun h (a, (i, l))

theorem cvN_incl_add (R : Type) [CommRing R] [Algebra F R] {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (Y : Fin n → Fin M → E) (X : Fin n → Fin M → R ⊗[F] E) (p : Fin n × (Fin M × Fin d)) :
    cvN R b ((fun a i => inclR R (Y a i)) + X) p = algebraMap F R (ratCoord b Y p) + cvN R b X p := by
  simp [cvN, GlobalTheory.CompanionTheory.SW.BB.cv, ratCoord, inclR, Algebra.TensorProduct.basis_repr_tmul,
    Algebra.algebraMap_eq_smul_one]

end Coord

section Main

open GroundTheory.Global

attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing

theorem tupCovol : TupCovol := by
  intro F E _ _ _ _ _ σ hCM M J hJ ψ hψ n μ hμ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hψ.2.2.2
    apply hx
    rw [hξ x]
    simp
  obtain ⟨e, he, hB⟩ := exists_coordHomeoN σ hCM n M b
  have hdxc := dx_coordN σ hCM J hJ b ψ ξ hξ0 hξ μ hμ e he hB
  have := hB
  have : BorelSpace (AF F) := GroundTheory.Global.borelSpace_adeleRing F
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hD : MeasurableSet (Set.univ.pi fun _ : Fin n × (Fin M × Fin (Module.finrank F E)) => fundamentalSet F) :=
    MeasurableSet.univ_pi fun _ => measurableSet_fundamentalSet F
  have hem : Measurable e := e.continuous.measurable
  have hmem : ∀ (Y : Fin n → Fin M → E) X,
      e ((fun a i => inclR (AF F) (Y a i)) + X) ∈
          (Set.univ.pi fun _ : Fin n × (Fin M × Fin (Module.finrank F E)) => fundamentalSet F) ↔
        ∀ p, algebraMap F (AF F) (ratCoord b Y p) + e X p ∈ fundamentalSet F := by
    intro Y X
    simp only [Set.mem_univ_pi, he, cvN_incl_add]
  refine ⟨e ⁻¹' (Set.univ.pi fun _ => fundamentalSet F), IsAddFundamentalDomain.mk' (hem hD).nullMeasurableSet fun X => ?_, ?_⟩
  · choose k hk huniq using fun p => existsUnique_sub_mem_fundamentalSet F (e X p)
    refine ⟨⟨_, ofCoord b (-k), rfl⟩, ?_, ?_⟩
    · refine (hmem _ X).2 fun p => ?_
      rw [ratCoord_ofCoord]
      have := hk p
      rwa [Pi.neg_apply, map_neg, neg_add_eq_sub]
    · rintro ⟨_, Y, rfl⟩ h
      have h' := (hmem Y X).1 h
      have hY : ratCoord b Y = -k := by
        funext p
        have e1 := huniq p (-(ratCoord b Y p)) (by
          change e X p - algebraMap F (AF F) (-(ratCoord b Y p)) ∈ fundamentalSet F
          rw [map_neg, sub_neg_eq_add, add_comm]; exact h' p)
        rw [Pi.neg_apply, ← e1, neg_neg]
      have : Y = ofCoord b (-k) := ratCoord_injective b (by rw [hY, ratCoord_ofCoord])
      subst this
      rfl
  · rw [← Measure.map_apply hem hD, hdxc, GroundTheory.Automorphic.GJMatrix.adeleMeasurePi, Measure.pi_pi]
    simp [adeleMeasure_fundamentalSet]

end Main

end GlobalTheory.CompanionTheory.SiegelND.TupCovolume

end
