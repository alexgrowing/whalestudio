import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem span_joint (g : ℕ) (I : Type) (M : I → Matrix (Fin g) (Fin g) ℂ)
    (hc : ∀ i j, M i * M j = M j * M i)
    (hp : ∀ i, ∃ p : ℂ[X], p.Separable ∧ aeval (M i) p = 0) :
    Submodule.span ℂ {v : Fin g → ℂ | ∃ c : I → ℂ, ∀ i, (M i).mulVec v = c i • v} = ⊤ := by
  classical
  let f : I → Module.End ℂ (Fin g → ℂ) := fun i => Matrix.toLinAlgEquiv' (M i)
  have hss : ∀ i, (f i).IsFinitelySemisimple := by
    intro i
    obtain ⟨p, hsep, hpz⟩ := hp i
    apply Module.End.IsSemisimple.isFinitelySemisimple
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree
    show aeval (Matrix.toLinAlgEquiv' (M i)) p = 0
    rw [Polynomial.aeval_algEquiv]
    simp [hpz]
  have hcomm : Pairwise fun i j => Commute (f i) (f j) := by
    intro i j _
    show Matrix.toLinAlgEquiv' (M i) * Matrix.toLinAlgEquiv' (M j) =
      Matrix.toLinAlgEquiv' (M j) * Matrix.toLinAlgEquiv' (M i)
    rw [← map_mul, ← map_mul, hc]
  have htop : ∀ i, iSup (fun t => (f i).maxGenEigenspace t) = ⊤ :=
    fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i)
  have hall := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f hcomm htop
  rw [eq_top_iff, ← hall]
  refine iSup_le fun χ => ?_
  intro v hv
  apply Submodule.subset_span
  refine ⟨χ, fun i => ?_⟩
  have hvi : v ∈ (f i).maxGenEigenspace (χ i) := (Submodule.mem_iInf _).1 hv i
  rw [(hss i).maxGenEigenspace_eq_eigenspace, Module.End.mem_eigenspace_iff] at hvi
  simpa [f] using hvi

theorem UpperTheory.Gal.W2.simDiag_of :
    UpperTheory.Gal.W2.SimDiag := by
  intro g I M hc hp
  classical
  have hspan := span_joint g I M hc hp
  obtain ⟨b, hbS, hbspan, hli⟩ :=
    exists_linearIndependent ℂ {v : Fin g → ℂ | ∃ c : I → ℂ, ∀ i, (M i).mulVec v = c i • v}
  let B := Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hbspan, hspan]))
  let B' := B.reindex (B.indexEquiv (Pi.basisFun ℂ (Fin g)))
  have hmem : ∀ k, ∃ c : I → ℂ, ∀ i, (M i).mulVec (B' k) = c i • B' k := by
    intro k
    have : B' k ∈ b := by
      simp only [B', B, Module.Basis.reindex_apply, Module.Basis.mk_apply]
      exact Subtype.mem _
    exact hbS this
  choose c hc' using hmem
  refine ⟨(Pi.basisFun ℂ (Fin g)).toMatrix B', fun i k => c k i, ?_, fun i => ?_⟩
  · rw [← Module.Basis.det_apply]
    exact ((Pi.basisFun ℂ (Fin g)).isUnit_det B').ne_zero
  · ext r k
    rw [Matrix.mul_diagonal]
    have h := congr_fun (hc' k i) r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    simp only [Matrix.mul_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h, mul_comm]
