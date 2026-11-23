import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwLat

theorem exists_GLw_lat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ L : Submodule K.O B.A, GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ g : GLw m w, GlobalTheory.TwLat.lat e b g = L := by
  intro E _ _ _ _ w _ K e _ _ _ B m b L hL
  obtain ⟨hfg, hsp⟩ := hL
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors K.O B.A := by
    constructor
    intro c x h
    rw [← algebraMap_smul K.E c x, smul_eq_zero] at h
    rcases h with h | h
    · left; exact (IsFractionRing.injective K.O K.E) (by simpa using h)
    · right; exact h
  haveI : Module.Free K.O L := Module.free_of_finite_type_torsion_free'
  set n := Module.finrank K.O L
  let bL := Module.finBasis K.O L
  let v : Fin n → B.A := fun i => (bL i : B.A)
  have hspanO : Submodule.span K.O (Set.range v) = L := by
    have : Set.range v = L.subtype '' Set.range bL := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bL.span_eq, Submodule.map_subtype_top]
  have hli : LinearIndependent K.E v := by
    rw [← LinearIndependent.iff_fractionRing K.O K.E]
    exact LinearIndependent.map' bL.linearIndependent L.subtype (by simp)
  have hspE : ⊤ ≤ Submodule.span K.E (Set.range v) := by
    rw [← Submodule.span_span_of_tower K.O K.E (Set.range v), hspanO, hsp]
  let bE := Module.Basis.mk hli hspE
  have hnm : n = m := by
    have h1 := Module.finrank_eq_card_basis bE
    have h2 := Module.finrank_eq_card_basis b
    simp only [Fintype.card_fin] at h1 h2
    omega
  let v' : Fin m → B.A := v ∘ finCongr hnm.symm
  let bE' := bE.reindex (finCongr hnm)
  have hv' : ∀ j, bE' j = v' j := by
    intro j; simp [bE', v', bE, Module.Basis.mk_apply]
  let M : Matrix (Fin m) (Fin m) K.E := b.toMatrix bE'
  have hM : IsUnit M := by
    haveI := b.invertibleToMatrix bE'
    exact isUnit_of_invertible M
  have hMe : IsUnit (M.map e) := hM.map e.mapMatrix
  refine ⟨hMe.unit, ?_⟩
  unfold lat
  rw [← hspanO]
  have hcol : (fun j => ∑ i, e.symm ((hMe.unit : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) • b i) = v' := by
    funext j
    simp only [IsUnit.unit_spec, Matrix.map_apply, RingEquiv.symm_apply_apply, M, Module.Basis.toMatrix_apply]
    rw [b.sum_repr, hv']
  rw [hcol]
  congr 1
  exact EquivLike.range_comp v _

end GlobalTheory.TwLat
