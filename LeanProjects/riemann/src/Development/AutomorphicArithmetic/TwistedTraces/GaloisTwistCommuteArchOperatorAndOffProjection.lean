import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistPerm
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensOp
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistYA
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

set_option maxHeartbeats 1600000 in
theorem UpperTheory.galoisTwist_commute_archOperator_and_offProjection :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ k n : ℕ,
        ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
        ∀ (D : InfD σ k) (s : Fin (k + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
        ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n)
          (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
        ∀ (q : Pl F) (w₀ : PlacesOver E q) (T : Ty σ n q w₀),
          Commute θ.U (Oinf μ νE aE) ∧ Commute θ.U (prj (offN μ T)) := by
  intro F E _ _ _ _ _ _ σ hσ k n μ _ θ hθ D s hs hposition νE _ νF _ b a aE aF hA q w₀ T
  obtain ⟨tp1, -, tp3⟩ := twistPerm F E σ hσ k n μ θ hθ
  refine ⟨?_, tp3 q w₀ T (nsS T : Set (Pl F))⟩
  obtain ⟨-, -, ag3, -⟩ := archBasic F E σ k D n
  let O : Fin (k + 1) → LL μ →L[ℂ] LL μ := fun i => OComponent μ (s i) (hs i) νF a
  have hOi : Oinf μ νE aE = (List.ofFn O).prod :=
    tensOp F E σ k D n νE νF hA.meas s hs hposition (LL μ) _ (fun _ => a) aE hA.tens
  have hss : ∀ i j, i ≠ j → ∀ g h, Commute (s i g) (s j h) := fun i j hij g h => by
    rw [hposition, hposition]
    show _ * _ = _ * _
    rw [← ag3, ← ag3]
    exact congrArg _ (Pi.mulSingle_commute (f := fun _ : Fin (k + 1) => archGroup F n) hij g h).eq
  have hOc : ∀ (B : LL μ →L[ℂ] LL μ) i, (∀ g, Commute B (rightRegularRep (rationalGLOne E n) μ (archP E n (s i g)))) →
      Commute B (O i) := fun B i h => ContinuousLinearMap.ext fun v =>
    UpperTheory.ConvolutionTheory.L1.TY.operatorAt_int μ (hs i) (hs i) νF a B (fun x u => DFunLike.congr_fun (h x).eq u) v
  have hrep : ∀ x y : normOneGL E n, Commute x y →
      Commute (rightRegularRep (rationalGLOne E n) μ x) (rightRegularRep (rationalGLOne E n) μ y) := fun x y h =>
    ContinuousLinearMap.ext fun v => by
      simp only [ContinuousLinearMap.mul_apply]
      rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, h.eq]
  have hOa : ∀ i j, i ≠ j → ∀ g, Commute (O i) (rightRegularRep (rationalGLOne E n) μ (archP E n (s j g))) :=
    fun i j hij g => (hOc _ i fun x => hrep _ _ ((hss j i hij.symm g x).map _)).symm
  have hOO : ∀ i j, Commute (O i) (O j) := fun i j => by
    by_cases e : i = j
    · rw [e]
    · exact hOc _ j (hOa i j e)
  have hUO : ∀ i, θ.U * O (i + 1) = O i * θ.U := fun i => ContinuousLinearMap.ext fun v =>
    UpperTheory.ConvolutionTheory.L1.TY.operatorAt_int μ (hs _) (hs _) νF a θ.U (tp1 D s hposition i) v
  have key : ∀ l : List (Fin (k + 1)), θ.U * (l.map fun i => O (i + 1)).prod = (l.map O).prod * θ.U := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [← mul_assoc, hUO, mul_assoc, ih, mul_assoc]
  have hperm : (List.ofFn fun i => O (i + 1)).prod = (List.ofFn O).prod := by
    refine List.Perm.prod_eq' (Equiv.Perm.ofFn_comp_perm (Equiv.addRight (1 : Fin (k + 1))) O) ?_
    rw [List.ofFn_eq_map, List.pairwise_map]
    exact List.pairwise_of_forall fun x y => hOO _ _
  have h := key (List.finRange (k + 1))
  rw [← List.ofFn_eq_map, ← List.ofFn_eq_map, hperm] at h
  rw [hOi]
  exact h
