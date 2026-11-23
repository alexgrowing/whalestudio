import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.BumpLat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame

open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA

open scoped TensorProduct
open PositivityTheory.ThKH.Iwas (at_sg ev_sg mul_sg)

private theorem e0 {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (a : AF F) (x : E) :
    a • inclR (F := F) (AF F) x = a ⊗ₜ[F] x := by
  change (a * 1) ⊗ₜ[F] x = _
  rw [mul_one]

private theorem unit_at {F : Type} [Field F] [NumberField F] (v : Pl F) {s : 𝓞 F} (hs : s ∉ v.asIdeal) :
    ∃ t : Fv F v, t ∈ v.adicCompletionIntegers F ∧ (s : F) • sg v t = sg v 1 := by
  have hs0 : (s : F) ≠ 0 := fun h => hs (by
    rw [show s = 0 from RingOfIntegers.coe_injective (by simpa using h)]; exact zero_mem _)
  refine ⟨algebraMap F (Fv F v) (s : F)⁻¹, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : v.valuation F (s : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v).2 hs
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (s : F)⁻¹
    exact (h2.trans ((map_inv₀ _ _).trans ((congrArg _ h1).trans inv_one))).le
  · rw [← map_smul, Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hs0, map_one]

private theorem key {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : Pl F) {s : F} {t : Fv F v}
    (h : s • sg v t = sg v 1) (x : E) :
    sg v t • inclR (F := F) (AF F) (algebraMap F E s * x) = sg v 1 • inclR (F := F) (AF F) x := by
  rw [e0, e0, ← Algebra.smul_def, ← TensorProduct.smul_tmul, h]

private theorem at_one {F : Type} [Field F] [NumberField F] (v : Pl F) {M : Type} [AddCommGroup M] [Module (AF F) M] (m : M) :
    At (evFin F v) (sg v 1 • m) := fun u hu => by
  rw [smul_smul, mul_sg, hu, zero_mul, map_zero, zero_smul]

theorem UpperTheory.unitaryLattice_exists_frame :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (X : Spc F E n) (v : Pl F), X.L.IsLattice E → ∃ b c, IsFr X v b c := by
  intro F E _ _ _ _ _ n X v hL
  haveI := hL
  obtain ⟨P, h1, h2⟩ := GlobalTheory.AdelicU.Frames.exists_rational_frame (F := F) X.L v
  have hss : sg v 1 * sg v 1 = sg v 1 := by rw [mul_sg, ev_sg, mul_one]
  have hPQ : incM F P.1 * incM F (P⁻¹).1 = 1 := by
    rw [incM, incM, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP : incM F (P⁻¹).1 * incM F P.1 = 1 := by
    rw [incM, incM, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨sg v 1 • incM F P.1, sg v 1 • incM F (P⁻¹).1, ⟨at_one v _, at_one v _, ?_, ?_, ?_, ?_⟩⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, hPQ]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, hQP]
  · intro j
    obtain ⟨s, hs, hy⟩ := h1 j
    obtain ⟨t, ht, hst⟩ := unit_at v hs
    refine AddSubgroup.subset_closure ⟨sg v t, at_sg t, by rwa [ev_sg], _, hy, funext fun i => ?_⟩
    exact (key v hst (P.1 i j)).symm
  · intro z hz i
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, ha', x, hx, rfl⟩ := hy
      obtain ⟨s, hs, hsx⟩ := h2 x hx
      obtain ⟨t, ht, hst⟩ := unit_at v hs
      obtain ⟨o, ho⟩ := hsx i (Set.mem_univ i)
      refine AddSubgroup.subset_closure ⟨a * sg v t, ?_, ?_, o, ?_⟩
      · exact fun u hu => by rw [smul_eq_mul, mul_comm u, mul_assoc, mul_comm _ u, ← smul_eq_mul u, at_sg t u hu, mul_zero]
      · rw [map_mul, ev_sg]
        exact mul_mem ha' ht
      · have ho' : ((o : 𝓞 E) : E) = algebraMap F E (s : F) * ((P⁻¹).1 *ᵥ x) i := by
          simpa using ho
        rw [ho', mul_smul, key v hst]
        simp only [Matrix.mulVec, dotProduct, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, Matrix.smul_apply, smul_mul_assoc, mul_smul_comm, smul_comm]
        rfl
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
    | neg y _ hy => rw [Matrix.mulVec_neg]; exact neg_mem hy
