import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws

section Par

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem unip_corner {a b : ℕ} {R : Type} [CommRing R] (X : UPos (a + b) a → R) :
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 1 ((unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ 0 (1 : Matrix (Fin b) (Fin b) R) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [unipMatrix, blockEntry_apply, Matrix.one_apply, Matrix.toBlocks₁₂, Fin.ext_iff] <;> omega

private theorem unip_any {a b : ℕ} {R : Type} [CommRing R] (B : Matrix (Fin a) (Fin b) R) : ∃ X : UPos (a + b) a → R,
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks 1 B 0 (1 : Matrix (Fin b) (Fin b) R) := by
  refine ⟨fun p => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 B 0 0) p.1.1 p.1.2, ?_⟩
  rw [unip_corner]
  congr 1
  ext i j
  have : (Fin.castAdd b i : Fin (a + b)) ≠ Fin.natAdd a j := by
    simp [Fin.ext_iff]; omega
  simp [unipMatrix, blockEntry_apply, Matrix.toBlocks₁₂, this]

private theorem split_par {a b : ℕ} {R : Type} [CommRing R] (g : GL (Fin (a + b)) R)
    (h : (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ (c : GL (Fin a) R) (d : GL (Fin b) R) (X : UPos (a + b) a → R), g = unipGL X * blk c d := by
  have e1 : g.val.submatrix finSumFinEquiv finSumFinEquiv * g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv =
      (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) := by
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hg : ∀ M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R, g.val.submatrix finSumFinEquiv finSumFinEquiv = M →
      g.val = M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rintro _ rfl
    simp
  generalize g.val.submatrix finSumFinEquiv finSumFinEquiv = M at *
  generalize g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv = N at *
  have hM := (Matrix.fromBlocks_toBlocks M).symm
  rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N, h, h', Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at e1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e1
  obtain ⟨e1, -, -, e2⟩ := e1
  obtain ⟨X, hX⟩ := unip_any (M.toBlocks₁₂ * N.toBlocks₂₂)
  refine ⟨⟨_, _, e1, mul_eq_one_comm.1 e1⟩, ⟨_, _, e2, mul_eq_one_comm.1 e2⟩, X, Units.ext ?_⟩
  have hX' : unipMatrix X = (Matrix.fromBlocks 1 (M.toBlocks₁₂ * N.toBlocks₂₂) 0 1).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hX]; simp
  rw [Units.val_mul, coe_unipGL, hX', hg M rfl]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_assoc, mul_eq_one_comm.1 e2, Matrix.mul_one]
  rw [← h, ← hM]

private theorem par_of_low {K : Type} [Field K] [NumberField K] (s : G1 K (2 + 2))
    (h : ((s : AdelicGLn.AdelicGL K (2 + 2)).val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : ((s : AdelicGLn.AdelicGL K (2 + 2))⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ X m₁ m₂ t, s = nn X * lv m₁ m₂ t := by
  obtain ⟨hlv, -, -, -, hdet, -⟩ := blkLaws (K := K)
  obtain ⟨a, d, X, hX⟩ := split_par (s : AdelicGLn.AdelicGL K (2 + 2)) h h'
  refine ⟨X, retractOne a, retractOne d, Real.log (detModule K 2 a).1, ?_⟩
  have h1 : detModule K 2 a * detModule K 2 d = 1 := by
    have := mem_normOneGL_iff_detModule.1 s.2
    rwa [hX, map_mul, mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL _), one_mul, hdet] at this
  have z1 : zt K (Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 a) := by
    unfold zt
    congr 1
    exact Subtype.ext (Real.exp_log (detModule K 2 a).2)
  have z2 : zt K (-Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 d) := by
    unfold zt
    congr 1
    refine Subtype.ext ?_
    rw [eq_inv_of_mul_eq_one_right h1]
    show Real.exp (-Real.log _) = _
    rw [Real.exp_neg, Real.exp_log (detModule K 2 a).2]
    rfl
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, hlv, z1, z2, coe_retractOne, coe_retractOne, inv_mul_cancel_right, inv_mul_cancel_right]
  exact hX

private theorem low_of_borel {K : Type} [Field K] [NumberField K] {b : AdelicGLn.AdelicGL K (2 + 2)} (hb : b ∈ adelicBorel) :
    (b.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
  ext i j
  refine mem_adelicBorel.1 hb ?_
  show finSumFinEquiv (Sum.inl j) < finSumFinEquiv (Sum.inr i)
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  omega

end Par

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical NumberField.AdeleRing

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem snd_entry (x : AdelicGLn.FiniteAdelicGL K n) (a b : Fin n) :
    ((finEmb K n x : AdelicGLn.AdelicGL K n) a b).2 = x a b := by
  have h := AdelicGLn.prodEquiv_apply_snd K n (finEmb K n x) a b
  rw [prodEquiv_finEmb] at h
  exact h.symm

private theorem cf_snd (v : Pl K) (x : AdelicGLn.AdelicGL K n) : GM.cf v (AdelicGLn.prodEquiv K n x).2 = finAt v x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change ((finEmb K n (AdelicGLn.prodEquiv K n x).2 : AdelicGLn.AdelicGL K n) a b).2 v = (x a b).2 v
  rw [snd_entry, AdelicGLn.prodEquiv_apply_snd]

private theorem cf_mul (v : Pl K) (x y : AdelicGLn.FiniteAdelicGL K n) : GM.cf v (x * y) = GM.cf v x * GM.cf v y := by
  unfold GM.cf
  rw [map_mul, finAt_mul]

private theorem central_borel (s : {r : ℝ // 0 < r}) : centralSection K n s ∈ adelicBorel := by
  refine mem_adelicBorel.2 ?_
  rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits]
  exact Matrix.blockTriangular_diagonal _

private theorem fin_borel (y : AdelicGLn.FiniteAdelicGL K n)
    (hy : ∀ v : Pl K, ∀ i j : Fin n, j < i → GM.cf v y i j = 0) : finEmb K n y ∈ adelicBorel := by
  refine mem_adelicBorel.2 fun i j hij => ?_
  have hij' : j < i := hij
  refine adele_ext (fun w => ?_) fun v => ?_
  · have e1 : (finEmb K n y i j).1 = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) i j :=
      congrArg (fun z => z.1 i j) (prodEquiv_finEmb y)
    rw [e1, Matrix.one_apply_ne hij'.ne']
    rfl
  · exact hy v i j hij'

private theorem proj_borel (y : AdelicGLn.FiniteAdelicGL K n) (h : finEmb K n y ∈ adelicBorel) :
    (MultiplicityOne.finProj K n y : AdelicGLn.AdelicGL K n) ∈ adelicBorel := by
  rw [MultiplicityOne.coe_finProj]
  exact mul_mem h (inv_mem (central_borel _))

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.finIwa :
    ∀ {K : Type} [Field K] [NumberField K] {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₄ →
      ∀ (h : FA K (2 + 2)) (k : archCompact K (2 + 2)), ∃ X m₁ m₂ t g u, (∀ U, u ∈ levOn (im w) U) ∧
        arc1 k * fin1 h = nn X * lv m₁ m₂ t * arc1 k * fin1 (ι₄ g) * fin1 u := by
  intro K _ _ r w ι hw hι h k
  obtain ⟨-, -, hoff, hdec, hcomm, -⟩ := (embEx (K := K) (2 + 2) w hw).2 ι hι
  obtain ⟨b, hb, c, hc, e⟩ := exists_adelicBorel_mul_maxCompact (finEmb K (2 + 2) h)
  have hh : h = (AdelicGLn.prodEquiv K (2 + 2) b).2 * (AdelicGLn.prodEquiv K (2 + 2) c).2 := by
    have := congrArg (fun x => (AdelicGLn.prodEquiv K (2 + 2) x).2) e
    simpa [prodEquiv_finEmb, map_mul] using this
  obtain ⟨g₁, b', eb, hb'⟩ := hdec (AdelicGLn.prodEquiv K (2 + 2) b).2
  obtain ⟨g₂, u, eu, hu⟩ := hdec (AdelicGLn.prodEquiv K (2 + 2) c).2
  have hcb : ι g₂ * b' = b' * ι g₂ := (hcomm g₂ b' hb').eq
  have hh2 : h = ι (g₁ * g₂) * b' * u := by
    rw [hh, eb, eu, map_mul, mul_assoc (ι g₁), ← mul_assoc b', ← hcb]
    simp only [mul_assoc]

  have hb1 : ∀ v ∉ im w, GM.cf v b' = finAt v b := fun v hv => by
    rw [← cf_snd, eb, cf_mul, hoff g₁ v hv, one_mul]
  have hu1 : ∀ v ∉ im w, GM.cf v u = finAt v c := fun v hv => by
    rw [← cf_snd, eu, cf_mul, hoff g₂ v hv, one_mul]
  have hup : finEmb K (2 + 2) b' ∈ adelicBorel := by
    refine fin_borel b' fun v i j hij => ?_
    by_cases hv : v ∈ im w
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hb' l]
      exact Matrix.one_apply_ne hij.ne'
    · rw [hb1 v hv]
      change (b i j).2 v = 0
      rw [mem_adelicBorel.1 hb hij]
      rfl
  have hs := proj_borel b' hup
  obtain ⟨X, m₁, m₂, t, hX⟩ := par_of_low (fin1 b') (low_of_borel hs) (low_of_borel (inv_mem hs))
  refine ⟨X, m₁, m₂, t, g₁ * g₂, u, fun U v => ?_, ?_⟩
  · by_cases hv : v ∈ im w
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hv
      beta_reduce
      rw [if_pos hv]
      change GM.cf (w l) u ∈ U (w l)
      rw [hu l]
      exact one_mem _
    · beta_reduce
      rw [if_neg hv]
      change GM.cf v u ∈ _
      rw [hu1 v hv]
      exact hc.2 v
  · have c1 : Commute (arc1 k) (fin1 b') := (levLaws (K := K) (2 + 2) (im w)).2.2.1 k b'
    have c2 : fin1 (ι (g₁ * g₂)) * fin1 b' = fin1 b' * fin1 (ι (g₁ * g₂)) := by
      rw [← map_mul, ← map_mul, (hcomm (g₁ * g₂) b' hb').eq]
    have e3 : fin1 (ι (g₁ * g₂) * b' * u) = fin1 (ι (g₁ * g₂)) * fin1 b' * fin1 u :=
      (map_mul _ _ _).trans (congrArg (· * fin1 u) (map_mul _ _ _))
    rw [← hX, hh2, e3, c2, ← c1.eq]
    simp only [mul_assoc]
