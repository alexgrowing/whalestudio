import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] {a b : ℕ}

private theorem bval (x : GL (Fin a) R) (y : GL (Fin b) R) :
    (PositivityTheory.Rg.Tf.Adel.blk x y).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val 0 0 y.val) := rfl

private def bHom : GL (Fin a) R × GL (Fin b) R →* GL (Fin (a + b)) R where
  toFun p := PositivityTheory.Rg.Tf.Adel.blk p.1 p.2
  map_one' := by
    apply Units.ext
    simp only [bval, Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.fromBlocks_one, Matrix.reindex_apply,
      Matrix.submatrix_one_equiv]
  map_mul' p q := by
    apply Units.ext
    simp only [Units.val_mul, Prod.fst_mul, Prod.snd_mul, bval, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

private theorem bHom_map (f : R →+* S) (x : GL (Fin a) R) (y : GL (Fin b) R) :
    Matrix.GeneralLinearGroup.map f (bHom (x, y)) =
      bHom (Matrix.GeneralLinearGroup.map f x, Matrix.GeneralLinearGroup.map f y) := by
  apply Units.ext
  ext i j
  change f ((PositivityTheory.Rg.Tf.Adel.blk x y).val i j) = (PositivityTheory.Rg.Tf.Adel.blk _ _).val i j
  simp only [bval, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

private theorem bHom_cont [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (bHom : GL (Fin a) R × GL (Fin b) R → GL (Fin (a + b)) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Continuous.matrix_fromBlocks (Units.continuous_val.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_val.comp continuous_snd)).matrix_reindex _ _
  · exact (Continuous.matrix_fromBlocks (Units.continuous_coe_inv.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_coe_inv.comp continuous_snd)).matrix_reindex _ _

private theorem bHom_ent (O : Subring S) (x : GL (Fin a) S) (y : GL (Fin b) S) (hx : ∀ i j, x i j ∈ O)
    (hy : ∀ i j, y i j ∈ O) (i j : Fin (a + b)) : bHom (x, y) i j ∈ O := by
  change (PositivityTheory.Rg.Tf.Adel.blk x y).val i j ∈ O
  simp only [bval, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [hx, hy]

end SlopeTestRemainingChoices

section Glob

variable {K : Type} [Field K] [NumberField K] {a b : ℕ}

private theorem bHom_int (v : Pl K) {x : Gw a v} {y : Gw b v} (hx : x ∈ GLnLocal.integralGL (v.adicCompletion K) a)
    (hy : y ∈ GLnLocal.integralGL (v.adicCompletion K) b) :
    bHom (x, y) ∈ GLnLocal.integralGL (v.adicCompletion K) (a + b) := by
  rw [GLnLocal.mem_integralGL_iff, ← map_inv]
  have h1 := (GLnLocal.mem_integralGL_iff _ _).1 hx
  have h2 := (GLnLocal.mem_integralGL_iff _ _).1 hy
  exact ⟨bHom_ent _ _ _ h1.1 h2.1, bHom_ent _ _ _ h1.2 h2.2⟩

private theorem finAt_bHom (v : Pl K) (x : AdelicGLn.AdelicGL K a) (y : AdelicGLn.AdelicGL K b) :
    finAt v (bHom (x, y)) = bHom (finAt v x, finAt v y) :=
  bHom_map (finEval v) x y

private theorem finEmb_bHom (x : FA K a) (y : FA K b) :
    finEmb K (a + b) (bHom (x, y)) = bHom (finEmb K a x, finEmb K b y) := by
  apply (AdelicGLn.prodEquiv K (a + b)).injective
  rw [prodEquiv_finEmb]
  have e1 : ∀ {c : ℕ} (p : AdelicGLn.AdelicGL K c), (AdelicGLn.prodEquiv K c p).1 =
      Matrix.GeneralLinearGroup.map (show AdeleRing (𝓞 K) K →+* InfiniteAdeleRing K from RingHom.fst _ _) p :=
    fun p => Units.ext (Matrix.ext fun _ _ => rfl)
  have e2 : ∀ {c : ℕ} (p : AdelicGLn.AdelicGL K c), (AdelicGLn.prodEquiv K c p).2 =
      Matrix.GeneralLinearGroup.map (show AdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 K) K from RingHom.snd _ _) p :=
    fun p => Units.ext (Matrix.ext fun _ _ => rfl)
  have h1 : ∀ (p : AdelicGLn.AdelicGL K a) (q : AdelicGLn.AdelicGL K b),
      (AdelicGLn.prodEquiv K (a + b) (bHom (p, q))).1 =
        bHom ((AdelicGLn.prodEquiv K a p).1, (AdelicGLn.prodEquiv K b q).1) := by
    intro p q
    rw [e1, e1, e1, bHom_map]
  have h2 : ∀ (p : AdelicGLn.AdelicGL K a) (q : AdelicGLn.AdelicGL K b),
      (AdelicGLn.prodEquiv K (a + b) (bHom (p, q))).2 =
        bHom ((AdelicGLn.prodEquiv K a p).2, (AdelicGLn.prodEquiv K b q).2) := by
    intro p q
    rw [e2, e2, e2, bHom_map]
  refine Prod.ext ?_ ?_
  · rw [h1, prodEquiv_finEmb, prodEquiv_finEmb]
    exact (map_one bHom).symm
  · rw [h2, prodEquiv_finEmb, prodEquiv_finEmb]

private theorem coe_finite_adele_inclusion {n : ℕ} {u : FA K n} (hu : u ∈ AdelicGLn.integralFiniteGL K n) :
    ((fin1 u : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n u :=
  congrArg Subtype.val (MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact hu)))

private theorem zt0 : zt K 0 = 1 := by
  rw [zt, ← map_one (centralSection K 2)]
  exact congrArg _ (Subtype.ext Real.exp_zero)

end Glob

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.levBlock :
    ∀ {K : Type} [Field K] [NumberField K] {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₄ →
      ∀ U : ∀ v : Pl K, Subgroup (Gw (2 + 2) v), Lev U → ∀ g, ∃ U₂ : ∀ v : Pl K, Subgroup (Gw 2 v), Lev U₂ ∧ ∀ u₁ ∈ levOn (im w) U₂, ∀ u₂ ∈ levOn (im w) U₂,
        ∃ u ∈ levOn (im w) U, ∀ k : archCompact K (2 + 2), lv (fin1 u₁) (fin1 u₂) 0 * arc1 k * fin1 (ι₄ g) = arc1 k * fin1 (ι₄ g) * fin1 u := by
  intro K _ _ r w ι hw hι U hU g
  obtain ⟨h4, -, hcomm, -, -, hconj⟩ := levLaws (K := K) (2 + 2) (im w)
  obtain ⟨U', hU', hc⟩ := hconj w ι hw hι rfl U hU g
  let U₂ : ∀ v : Pl K, Subgroup (Gw 2 v) := fun v =>
    GLnLocal.integralGL (v.adicCompletion K) 2 ⊓
      ((U' v).comap (bHom.comp (MonoidHom.inl _ _)) ⊓ (U' v).comap (bHom.comp (MonoidHom.inr _ _)))
  have hU₂ : Lev U₂ := by
    intro v
    have ho : IsOpen (U₂ v : Set (Gw 2 v)) :=
      (GLnLocal.isOpen_integralGL _ _).inter
        (((hU' v).1.2.preimage (bHom_cont.comp (continuous_id.prodMk continuous_const))).inter
          ((hU' v).1.2.preimage (bHom_cont.comp (continuous_const.prodMk continuous_id))))
    exact ⟨⟨(GLnLocal.isCompact_integralGL _ _).of_isClosed_subset ((U₂ v).isClosed_of_isOpen ho)
      (fun x hx => hx.1), ho⟩, inf_le_left⟩
  refine ⟨U₂, hU₂, fun u₁ h₁ u₂ h₂ => ?_⟩
  have hm : bHom (u₁, u₂) ∈ levOn (im w) U' := by
    intro v
    have e₁ := h₁ v
    have e₂ := h₂ v
    rw [finEmb_bHom, finAt_bHom]
    by_cases hv : v ∈ im w
    · simp only [hv, if_true] at e₁ e₂ ⊢
      have := (U' v).mul_mem e₁.2.1 e₂.2.2
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul] at this
      simpa using this
    · simp only [hv, if_false] at e₁ e₂ ⊢
      exact bHom_int v e₁ e₂
  have hl : lv (fin1 u₁) (fin1 u₂) 0 = fin1 (bHom (u₁, u₂)) := by
    have h2 := ((levLaws (K := K) 2 (im w)).1 U₂ hU₂).2
    apply Subtype.ext
    rw [blkLaws.1, neg_zero, zt0, mul_one, mul_one, coe_finite_adele_inclusion (h2 h₁), coe_finite_adele_inclusion (h2 h₂), coe_finite_adele_inclusion ((h4 U' hU').2 hm),
      finEmb_bHom]
    rfl
  refine ⟨_, hc _ hm, fun k => ?_⟩
  rw [hl, ← (hcomm k _).eq, mul_assoc, mul_assoc, ← map_mul, ← map_mul]
  congr 2
  group
