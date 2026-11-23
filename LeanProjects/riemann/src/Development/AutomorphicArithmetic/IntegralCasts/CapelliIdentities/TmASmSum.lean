import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qf26.Jm :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Matrix.diagonal (Fin n) Complex (instDecidableEqFin n) Complex.instZero fun (a : Fin n) ↦
        @ite Complex (@Eq Bool (ε a) Bool.true) (instDecidableEqBool (ε a) Bool.true)
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@Neg.neg Complex Complex.instNeg (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))

noncomputable def UpperTheory.Reformulated.B.Qf26.inUJ :
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
            (@UpperTheory.Reformulated.B.Qf26.Jm n ε))
          g)
        (@UpperTheory.Reformulated.B.Qf26.Jm n ε)

noncomputable def UpperTheory.Reformulated.B.Qf26.SmoothOnG :
    {n : Nat} → (Fin n → Bool) → (Matrix (Fin n) (Fin n) Complex → Complex) → Prop :=
    fun {n : Nat} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) Complex → Complex) ↦
      ∀ (g₀ : Matrix (Fin n) (Fin n) Complex),
        @UpperTheory.Reformulated.B.Qf26.inUJ n ε g₀ →
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
                      @UpperTheory.Reformulated.B.Qf26.inUJ n ε g → @Eq Complex (f g) (F g))))

theorem UpperTheory.Reformulated.B.Qf26.tmA_sm_sum.{u_1} :
    ∀ {n : Nat} {ε : Fin n → Bool} {ι : Type u_1} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) Complex → Complex),
      (∀ (i : ι),
          @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s i →
            @UpperTheory.Reformulated.B.Qf26.SmoothOnG n ε (F i)) →
        @UpperTheory.Reformulated.B.Qf26.SmoothOnG n ε fun (x : Matrix (Fin n) (Fin n) Complex) ↦ ∑ i ∈ s, F i x := by
  intro n ε ι s F h g₀ hg
  classical
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  choose! U G hUo hUm hG hE using fun i hi => h i hi g₀ hg
  refine ⟨⋂ i ∈ s, U i, fun x => ∑ i ∈ s, G i x, isOpen_biInter_finset hUo, ?_, ?_, ?_⟩
  · exact Set.mem_iInter₂.2 hUm
  · exact ContDiffOn.sum fun i hi => (hG i hi).mono (Set.biInter_subset_of_mem hi)
  · intro g hgU hgJ
    exact Finset.sum_congr rfl fun i hi => hE i hi g (Set.mem_iInter₂.1 hgU i hi) hgJ
