import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
private theorem cent_comm_of {F R : Type} [Field F] [CharZero F] [CommRing R] (hC : CentComm) (f : F →+* R) {n : ℕ}
    (γ : GL (Fin n) F) (hγ : (γ : Matrix (Fin n) (Fin n) F).charpoly.Separable) (D : GL (Fin n) R)
    (hD : (D : Matrix (Fin n) (Fin n) R) = (γ : Matrix (Fin n) (Fin n) F).map f) (s t : GL (Fin n) R)
    (hs : s * D = D * s) (ht : t * D = D * t) : s * t = t * s := by
  have hs' : (s : Matrix (Fin n) (Fin n) R) * (γ : Matrix (Fin n) (Fin n) F).map f =
      (γ : Matrix (Fin n) (Fin n) F).map f * (s : Matrix (Fin n) (Fin n) R) := by
    rw [← hD]
    exact congrArg Units.val hs
  have ht' : (t : Matrix (Fin n) (Fin n) R) * (γ : Matrix (Fin n) (Fin n) F).map f =
      (γ : Matrix (Fin n) (Fin n) F).map f * (t : Matrix (Fin n) (Fin n) R) := by
    rw [← hD]
    exact congrArg Units.val ht
  exact Units.ext (hC F R f n _ hγ _ _ hs' ht')

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.torusCommutative_of_centralizerCommutative :
    CentComm → TComm := by
  intro hC F _ _ n γ hγ
  have hsep : (γ : Matrix (Fin n) (Fin n) F).charpoly.Separable := hγ
  have hA : ∀ s t : GA F n, s * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * s →
      t * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * t → s * t = t * s := by
    refine cent_comm_of hC (algebraMap F _) γ hsep _ ?_
    ext a b
    rfl
  refine ⟨fun s t => ?_, fun s t => ?_, fun v s t => ?_, fun γ₁ h₁ s t => ?_⟩
  · exact Subtype.ext (hA _ _ (Subgroup.mem_centralizer_singleton_iff.1 s.2)
      (Subgroup.mem_centralizer_singleton_iff.1 t.2))
  · refine Subtype.ext (cent_comm_of hC (algebraMap F (InfiniteAdeleRing F)) γ hsep _ ?_ _ _
      (Subgroup.mem_centralizer_singleton_iff.1 s.2) (Subgroup.mem_centralizer_singleton_iff.1 t.2))
    ext a b
    rfl
  · refine Subtype.ext (cent_comm_of hC (algebraMap F (v.adicCompletion F)) γ hsep _ ?_ _ _
      (Subgroup.mem_centralizer_singleton_iff.1 s.2) (Subgroup.mem_centralizer_singleton_iff.1 t.2))
    ext a b
    rfl
  · have key : ∀ u : Subgroup.centralizer {γ₁}, u.1.1 * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * u.1.1 := by
      intro u
      rw [← h₁]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 u.2)
    exact Subtype.ext (Subtype.ext (hA _ _ (key s) (key t)))
