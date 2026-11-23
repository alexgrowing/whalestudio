import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ExistsSecNotMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.SameDegreeZeroOfRestriction
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.PrimeMaximalOrKernel
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.TspHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.GrEqRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FgHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.HomHolds

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem irr_fg {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (𝒜 : Deg k → Submodule B R) (h : ∀ i, (𝒜 (e i)).FG) : (Irr 𝒜).FG := by
  unfold Irr
  refine Finset.prod_induction _ Ideal.FG (fun a b ha hb => Submodule.FG.mul ha hb) ?_ fun i _ => ?_
  · rw [Ideal.one_eq_top]; exact ⟨{1}, by simp⟩
  · obtain ⟨t, ht⟩ := h i
    refine ⟨t, ?_⟩
    rw [← ht]
    exact (Submodule.span_span_of_tower B R (t : Set R)).symm

private theorem mN_fg {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A)
    [GradedAlgebra 𝒜] (h : ∀ j, (oz 𝒜 j).FG) (F : A) : ∀ i, (mN 𝒜 F i).FG := by
  intro i
  fin_cases i
  · exact h (-2)
  · exact h 2
  · exact Submodule.FG.sup (Submodule.fg_span_singleton _) (((h (-2)).mul (h (-2))).mul (h 2))

theorem UpperTheory.V.Alg.M.admissibility_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    SpansCot x 𝒜 (-1) Q.F → SpansCot x 𝒜 (-2) Q.G → M2 𝒜 Q.ideal → M3 𝒜 K x Q.ideal →
    ∀ a : 𝒜 0, M5 𝒜 K x Q.ideal a → ∀ J : Ideal (mR Q), (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ J) →
      admitted (mGr Q) (ts Q ++ [(0, algebraMap (𝒜 0) (mR Q) a)]) J := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q hF hG h2 h3 a h5 J hJ
  have hstd : Std (mGr Q) := std_holds (𝒜 0) A 3 _ (mN_fg 𝒜 (fg_holds O A 𝒜 x hW) _)
  have hfg : ((maximalIdeal (𝒜 0)).map (algebraMap (𝒜 0) (mR Q)) * Irr (mGr Q)).FG :=
    Submodule.FG.mul (Ideal.FG.map (IsNoetherian.noetherian _) _) (irr_fg _ hstd.fg)
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ hfg
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro p ⟨hle, hp⟩
  by_cases hirr : Irr (mGr Q) ≤ p
  · exact Ideal.mul_le_right.trans hirr
  refine Ideal.mul_le_left.trans ?_
  have hsec : secs (ts Q) ≤ p := by
    refine le_trans (Ideal.span_mono ?_) (le_sup_right.trans hle)
    rintro t ⟨d, hd⟩
    exact ⟨d, List.mem_append_left _ hd⟩
  have ha : algebraMap (𝒜 0) (mR Q) a ∈ p :=
    (le_sup_right.trans hle) (Ideal.subset_span ⟨0, List.mem_append_right _ (List.mem_singleton_self _)⟩)
  have hZ : ∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ p := fun i => hle (Ideal.mem_sup_left (hJ i))
  have hzi := (zi_holds O A 𝒜 x hW r s r' s' m Q p hp hirr hsec hZ).1
  have hP : (p.comap (algebraMap (𝒜 0) (mR Q))).IsPrime := Ideal.comap_isPrime _ _
  rcases emb_holds O K A 𝒜 x Q.ideal h2 _ hP hzi with h | ⟨_, σ, hσ⟩
  · rw [Ideal.map_le_iff_le_comap, h]
  refine zii_holds O K A 𝒜 x hW r s r' s' m Q hF hG h2 h3 p hp hirr hsec hZ ?_
  rw [Ideal.map_le_iff_le_comap, ← hσ, idD, Ideal.span_le]
  rintro b ⟨f, hf, g, hg, hb⟩
  by_contra hne
  obtain ⟨ξ, hξ, hres⟩ := tsp_holds O K A 𝒜 x hW Q.ideal (hom_holds O A 𝒜 x hW r s r' s' m Q).1 σ
    (fun b hb => by
      have : b ∈ RingHom.ker σ := by rw [hσ]; exact hzi b hb
      exact this)
  have hval : ∀ c : 𝒜 0, ξ c = σ c := fun c => by rw [← hres]; rfl
  have hfg0 : ξ f * ξ g ≠ 0 := by
    rw [← map_mul, ← hb, hval]
    exact hne
  refine h5.2.2 ξ hξ ⟨fun h => ?_, fun h => ?_⟩ ?_
  · exact left_ne_zero_of_mul hfg0 (h (-2) (by norm_num) f hf)
  · exact right_ne_zero_of_mul hfg0 (h 2 (by norm_num) g hg)
  · rw [hval]
    have : a ∈ RingHom.ker σ := by rw [hσ]; exact ha
    exact this
