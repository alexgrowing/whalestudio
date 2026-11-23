import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qh27.Jm :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Matrix.diagonal (Fin n) Complex (instDecidableEqFin n) Complex.instZero fun (a : Fin n) ↦
        @ite Complex (@Eq Bool (ε a) Bool.true) (instDecidableEqBool (ε a) Bool.true)
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@Neg.neg Complex Complex.instNeg (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))

noncomputable def UpperTheory.Reformulated.B.Qh27.inUJ :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex → Prop :=
    fun {n : Nat} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) Complex) ↦
      @Eq (Matrix (Fin n) (Fin n) Complex)
        (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
            Complex.instAddCommMonoid)
          (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
              Complex.instAddCommMonoid)
            (@Matrix.conjTranspose (Fin n) (Fin n) Complex
              (@InvolutiveStar.toStar Complex
                (@StarAddMonoid.toInvolutiveStar Complex
                  (@AddCommMonoid.toAddMonoid Complex
                    (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))))
                  (@StarRing.toStarAddMonoid Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                    Complex.instStarRing)))
              g)
            (@UpperTheory.Reformulated.B.Qh27.Jm n ε))
          g)
        (@UpperTheory.Reformulated.B.Qh27.Jm n ε)

noncomputable def UpperTheory.Reformulated.B.Qh27.SmoothOnG :
    {n : Nat} → (Fin n → Bool) → (Matrix (Fin n) (Fin n) Complex → Complex) → Prop :=
    fun {n : Nat} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) Complex → Complex) ↦
      ∀ (g₀ : Matrix (Fin n) (Fin n) Complex),
        @UpperTheory.Reformulated.B.Qh27.inUJ n ε g₀ →
          ∃ (U : Set (Matrix (Fin n) (Fin n) Complex)) (F : Matrix (Fin n) (Fin n) Complex → Complex),
            And
              (@IsOpen (Matrix (Fin n) (Fin n) Complex)
                (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
                  (@UniformSpace.toTopologicalSpace Complex
                    (@PseudoMetricSpace.toUniformSpace Complex
                      (@SeminormedRing.toPseudoMetricSpace Complex
                        (@SeminormedCommRing.toSeminormedRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
                U)
              (And
                (@Membership.mem (Matrix (Fin n) (Fin n) Complex) (Set (Matrix (Fin n) (Fin n) Complex))
                  (@Set.instMembership (Matrix (Fin n) (Fin n) Complex)) U g₀)
                (And
                  (@ContDiffOn Real (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField)
                    (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.normedAddCommGroup (Fin n) (Fin n) Complex (Fin.fintype n) (Fin.fintype n)
                      Complex.instNormedAddCommGroup)
                    (@Matrix.normedSpace Real (Fin n) (Fin n) Complex (Fin.fintype n) (Fin.fintype n)
                      (@NontriviallyNormedField.toNormedField Real
                        (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField))
                      (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                      (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                        instInnerProductSpaceRealComplex))
                    Complex Complex.instNormedAddCommGroup
                    (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                      instInnerProductSpaceRealComplex)
                    (@WithTop.some ENat (@Top.top ENat instTopENat)) F U)
                  (∀ (g : Matrix (Fin n) (Fin n) Complex),
                    @Membership.mem (Matrix (Fin n) (Fin n) Complex) (Set (Matrix (Fin n) (Fin n) Complex))
                        (@Set.instMembership (Matrix (Fin n) (Fin n) Complex)) U g →
                      @UpperTheory.Reformulated.B.Qh27.inUJ n ε g → @Eq Complex (f g) (F g))))

theorem UpperTheory.Reformulated.B.Qh27.smooth_on_group_sum.{u_1} :
    ∀ {n : Nat} {ε : Fin n → Bool} {ι : Type u_1} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) Complex → Complex),
      (∀ (i : ι),
          @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s i →
            @UpperTheory.Reformulated.B.Qh27.SmoothOnG n ε (f i)) →
        @UpperTheory.Reformulated.B.Qh27.SmoothOnG n ε fun (x : Matrix (Fin n) (Fin n) Complex) ↦ ∑ i ∈ s, f i x := by
  intro n ε ι s f h g₀ hg₀
  letI := @Matrix.normedAddCommGroup (Fin n) (Fin n) Complex _ _ _
  letI := @Matrix.normedSpace Real (Fin n) (Fin n) Complex _ _ _ _ _
  choose! U F hU hmem hF heq using fun i hi ↦ h i hi g₀ hg₀
  refine ⟨⋂ i ∈ s, U i, fun x ↦ ∑ i ∈ s, F i x, isOpen_biInter_finset hU,
    Set.mem_iInter₂.2 hmem, ?_, ?_⟩
  · exact ContDiffOn.sum fun i hi ↦ (hF i hi).mono (Set.biInter_subset_of_mem (Finset.mem_coe.2 hi))
  · intro g hg hgu
    exact Finset.sum_congr rfl fun i hi ↦ heq i hi g (Set.mem_iInter₂.1 hg i hi) hgu
