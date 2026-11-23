import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.ContinuousCj

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem t2k : T2Space k := Asm.t2

theorem tdk : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField

theorem sck : SecondCountableTopology k := (GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).1

theorem continuous_aevalM (P : k[X]) : Continuous fun x : Matrix (Fin n) (Fin n) k => aeval x P := by
  have : T2Space k := t2k
  simp_rw [aeval_eq_sum_range]
  exact continuous_finsetSum _ fun i _ => (continuous_pow i).const_smul (P.coeff i)

theorem isClosed_Tset {F : Set (Matrix (Fin n) (Fin n) k)} (hF : IsClosed F) (P : k[X]) : IsClosed (Tset F P) := by
  have : T2Space k := t2k
  exact hF.inter (isClosed_eq (continuous_aevalM P) continuous_id)

instance t2Space_centralizer_group (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : T2Space (GzS Z) := by
  have : T2Space k := t2k
  infer_instance

instance gzs_td (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : TotallyDisconnectedSpace (GzS Z) := by
  infer_instance

instance gzs_sc (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : SecondCountableTopology (GzS Z) := by
  have : SecondCountableTopology (GL (Fin n) k) := GlobalTheory.SplitFlip.secondCountable_GL
  exact TopologicalSpace.Subtype.secondCountableTopology _

instance gzs_sig (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : SigmaCompactSpace (GzS Z) := by
  infer_instance

end PositivityTheory.RgUd.T.Desc.SLF
