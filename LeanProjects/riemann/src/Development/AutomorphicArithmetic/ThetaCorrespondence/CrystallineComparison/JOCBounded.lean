import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LeafDefs

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem jOC_bounded (n : ℕ) : ∃ N : ℕ, ∀ x : Reformulated.AutPerF.Acris l (Cmp6.OC l), ∃ a : Reformulated.AutPerF.Ainf l (Cmp6.OC l),
    Reformulated.AutPerF.BdRPlus.eval l (Cmp6.OC l) n (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (Cmp6.OC l)) ^ N * jOC l x) =
      Ideal.Quotient.mk _ (algebraMap (Reformulated.AutPerF.Ainf l (Cmp6.OC l)) (Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) a) := by
  obtain ⟨N, hN⟩ := iota_bounded l n
  refine ⟨N, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hN (Cmp6.cA l x)
  refine ⟨Reformulated.AutPerF.Ainf.map l (Cmp6.e l).symm.toRingHom a, ?_⟩
  have hsymm : ∀ z : Formalism.Per6.BdRp l,
      (Cmp6.cP l).symm z = Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom z := by
    intro z
    rw [RingEquiv.symm_apply_eq]
    show z = Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).toRingHom
      (Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom z)
    erw [Reformulated.AutPerF.BdRPlus.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Reformulated.AutPerF.BdRPlus.map_id]
  show Reformulated.AutPerF.BdRPlus.eval l (Cmp6.OC l) n
      (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (Cmp6.OC l)) ^ N * (Cmp6.cP l).symm (iotaP l (Cmp6.cA l x))) = _
  erw [hsymm]
  rw [← map_natCast (Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom) l, ← map_pow]
  have hm := map_mul (Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom)
    (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (NC l)) ^ N) (iotaF l (Cmp6.cA l x))
  erw [← hm, Reformulated.AutPerF.BdRPlus.eval_map]
  erw [ha]
  rw [Ideal.quotientMap_mk, Reformulated.AutPerF.AinfInv.map_algebraMap]

end Formalism.BasicNotions.CmpTie.Incl
