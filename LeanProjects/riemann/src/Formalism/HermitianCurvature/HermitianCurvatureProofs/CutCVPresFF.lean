import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
import Formalism.FormalDegreeBessel.FinalG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

theorem isDom_omP {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') :
    Q.IsDom k r z z' 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  refine ⟨?_, ?_⟩
  · have e : {g : Q.Mx k r | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
        ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} =
        {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g} ∩
          ⋂ a : Fin r, {g | Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
      ext g; simp
    rw [e]
    exact (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z')).inter
      (isOpen_iInter_of_finite fun a => isOpen_ne_fun (Formalism.FourierDecayAlt.P.Ux8.cont_Dmin k r z z' _) continuous_const)
  · rintro g ⟨-, hg⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hs : h * m ∈ Sset k r z := ⟨h, hh, m, hm.1, rfl⟩
    have hs' : h' * m' ∈ Sset k r z' := ⟨h', hh', m', hm'.1, rfl⟩
    have hD : ∀ l, Dmin k r z z' (h * m * g * (h' * m')) l = Dmin k r z z' g l :=
      fun l => dInv k r z z' hz hz' _ hs _ hs' g l
    refine ⟨?_, fun a => by rw [hD]; exact hg.2 a⟩
    have e : Gf k r z z' (h * m * g * (h' * m')) = Gf k r z z' g := by
      unfold Gf
      rw [hD, hD]
    rw [e]
    exact hg.1

theorem coefficient_vector_preserves_form : CVPresFF := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ _ v J hJ Y s
  have hz := (T v).base.z_mem
  have hz' := (T v).base.z'_mem
  have hD : Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) := isDom_omP hz hz'
  have hC : Q.CV S.G.k S.G.r (Y : ℂ) J ∈
      Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) :=
    Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms _ _ S.G.k S.G.r _ _ _ _ 0 _ (Y : ℂ) 0 0 hz hz' hD J hJ
  exact Formalism.FourierDecayAlt.P.Qx8.FFl_smul hC s

end Formalism.FourierDecayAlt.P.CutMP
