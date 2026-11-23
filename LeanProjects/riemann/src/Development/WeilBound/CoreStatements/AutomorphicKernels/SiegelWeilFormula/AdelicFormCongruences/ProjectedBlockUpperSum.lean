import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseRationalsPlusSinglePlaceAdelesStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.UnipotentLeDiagonalStabiliser

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Afc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Alg

variable {d : SD σ} (L : LD d)

def uN (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := ∑ j, Matrix.single L.i₀ (L.em j) (u j)

theorem em_ne (j : Fin L.n) : L.em j ≠ L.i₀ := (L.rng (L.em j)).2 ⟨j, rfl⟩

theorem uN_mul (u v : Fin L.n → AE F E) : uN L u * uN L v = 0 := by
  simp only [uN, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => by simp [em_ne L]

theorem uN_add (u v : Fin L.n → AE F E) : uN L (u + v) = uN L u + uN L v := by
  simp only [uN, Pi.add_apply, Matrix.single_add, Finset.sum_add_distrib]

theorem uN_zero : uN L 0 = 0 := by
  simp [uN]

theorem mapc_mulU {ι : Type} [Fintype ι] (X Y : Matrix ι ι (AE F E)) : (X * Y).map (cA σ) = X.map (cA σ) * Y.map (cA σ) :=
  Matrix.map_mul (f := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E))

theorem mapc_add {ι κ : Type} (X Y : Matrix ι κ (AE F E)) : (X + Y).map (cA σ) = X.map (cA σ) + Y.map (cA σ) :=
  Matrix.map_add _ (map_add _) _ _

theorem mapc_one {ι : Type} [DecidableEq ι] : (1 : Matrix ι ι (AE F E)).map (cA σ) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

def uD (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := 1 - ((uN L u).map (cA σ))ᵀ

def uZ (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 + uN L u) 0 0 (uD L u)

theorem uZ_mul (u v : Fin L.n → AE F E) : uZ L u * uZ L v = uZ L (u + v) := by
  have h1 : (1 + uN L u) * (1 + uN L v) = 1 + uN L (u + v) := by
    rw [uN_add, add_mul, mul_add, mul_add, uN_mul]
    simp only [one_mul, mul_one, add_zero]
    abel
  have h2 : uD (σ := σ) L u * uD L v = uD L (u + v) := by
    simp only [uD, uN_add, mapc_add, Matrix.transpose_add]
    have : ((uN L u).map (cA σ))ᵀ * ((uN L v).map (cA σ))ᵀ = 0 := by
      rw [← Matrix.transpose_mul, ← mapc_mulU, uN_mul, Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]
    rw [sub_mul, mul_sub, mul_sub, this]
    simp only [one_mul, mul_one, sub_zero]
    abel
  simp only [uZ, Matrix.fromBlocks_multiply, h1, h2, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem uZ_zero : uZ (σ := σ) L 0 = 1 := by
  simp [uZ, uD, uN_zero, Matrix.fromBlocks_one]

def Qa (ε : ℤˣ) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks 0 1 (inclR (F := F) (E := E) (AF F) ((ε : ℤ) : E) • 1) 0

theorem uZ_unitary (ε : ℤˣ) (u : Fin L.n → AE F E) : (uZ L u)ᵀ * Qa (d := d) ε * (uZ L u).map (cA σ) = Qa ε := by
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  have hcc := GlobalTheory.EisBL.DoubledUnipotentRadical.cA_cA σ hσ
  have hD : (uD (σ := σ) L u).map (cA σ) = 1 - (uN L u)ᵀ := by
    ext i j
    simp only [uD, Matrix.map_apply, Matrix.sub_apply, Matrix.transpose_apply, map_sub, hcc, Matrix.one_apply]
    split_ifs <;> simp
  have k1 : (1 + uN L u)ᵀ * (1 - (uN L u)ᵀ) = 1 := by
    rw [Matrix.transpose_add, Matrix.transpose_one, add_mul, one_mul, mul_sub, mul_one,
      ← Matrix.transpose_mul, uN_mul, Matrix.transpose_zero, sub_zero]
    abel
  have k2 : (uD (σ := σ) L u)ᵀ * (1 + uN L u).map (cA σ) = 1 := by
    rw [uD, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_transpose, mapc_add, mapc_one, sub_mul,
      one_mul, mul_add, mul_one, ← mapc_mulU, uN_mul, Matrix.map_zero _ (map_zero _), add_zero]
    abel
  simp only [uZ, Qa, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map, hD,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, k1]
  congr 1
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, k2]

end Alg

section Pts

variable {d : SD σ} (L : LD d)

theorem conj_mem {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (Z : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (hZ : Zᵀ * Qa (d := d) ε * Z.map (cA σ) = Qa ε) :
    (incM F d.b.1 * Z * incM F (d.b⁻¹).1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1 * Z * incM F (d.b⁻¹).1).map (cA σ) =
      dbl (incM F d.Y.J) := by
  have hF := SiegelEisensteinSeries.Grp.frame_adelic (F := F) hε
  have hZ' : Zᵀ * Matrix.fromBlocks 0 1 (inclR (F := F) (E := E) (AF F) ((ε : ℤ) : E) • 1) 0 * Z.map (cA σ) =
      Matrix.fromBlocks 0 1 (inclR (F := F) (E := E) (AF F) ((ε : ℤ) : E) • 1) 0 := hZ
  have h1 : (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, SiegelEisensteinSeries.Grp.incM_mul_inv, Matrix.transpose_one]
  have h2 : (incM F d.b.1).map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ) = 1 := by
    rw [← SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.incM_mul_inv, mapc_one]
  rw [SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.map_cA_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  calc (incM F (d.b⁻¹).1)ᵀ * (Zᵀ * (incM F d.b.1)ᵀ) * dbl (incM F d.Y.J) *
        ((incM F d.b.1).map (cA σ) * Z.map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ))
      = (incM F (d.b⁻¹).1)ᵀ * (Zᵀ * ((incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ)) *
          Z.map (cA σ)) * (incM F (d.b⁻¹).1).map (cA σ) := by simp only [Matrix.mul_assoc]
    _ = (incM F (d.b⁻¹).1)ᵀ * ((incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ)) *
          (incM F (d.b⁻¹).1).map (cA σ) := by rw [hF, hZ']
    _ = ((incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ) * dbl (incM F d.Y.J) *
          ((incM F d.b.1).map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ)) := by simp only [Matrix.mul_assoc]
    _ = dbl (incM F d.Y.J) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem unitary_of_mem {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (x : d.G) : (inFrame d.b x)ᵀ * Qa (d := d) ε * (inFrame d.b x).map (cA σ) = Qa ε := by
  have hF := SiegelEisensteinSeries.Grp.frame_adelic (F := F) hε
  have hU : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J) := x.2
  rw [SiegelEisensteinSeries.Grp.matrix_eq_frame_conjugate d.b x] at hU
  have h1 : (incM F d.b.1)ᵀ * (incM F (d.b⁻¹).1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.transpose_one]
  have h2 : (incM F (d.b⁻¹).1).map (cA σ) * (incM F d.b.1).map (cA σ) = 1 := by
    rw [← SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.incM_inv_mul, mapc_one]
  unfold Qa
  rw [← hF]
  conv_rhs => rw [← hU]
  rw [SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.map_cA_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_one, ← Matrix.mul_assoc (incM F d.b.1)ᵀ (incM F (d.b⁻¹).1)ᵀ, h1, Matrix.one_mul]

def uU (u : Fin L.n → AE F E) : GL (Fin d.n ⊕ Fin d.n) (AE F E) where
  val := incM F d.b.1 * uZ L u * incM F (d.b⁻¹).1
  inv := incM F d.b.1 * uZ L (-u) * incM F (d.b⁻¹).1
  val_inv := (SiegelEisensteinSeries.Grp.conj_mul_conj d.b _ _).trans (by
    rw [uZ_mul, add_neg_cancel, uZ_zero, Matrix.mul_one, SiegelEisensteinSeries.Grp.incM_mul_inv])
  inv_val := (SiegelEisensteinSeries.Grp.conj_mul_conj d.b _ _).trans (by
    rw [uZ_mul, neg_add_cancel, uZ_zero, Matrix.mul_one, SiegelEisensteinSeries.Grp.incM_mul_inv])

theorem uU_mem (u : Fin L.n → AE F E) : uU L u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  exact conj_mem hε _ (uZ_unitary L ε u)

def unipotentPoint (u : Fin L.n → AE F E) : d.G := ⟨uU L u, uU_mem L u⟩

theorem inFrame_unipotentPoint (u : Fin L.n → AE F E) : inFrame d.b (unipotentPoint L u) = uZ L u := by
  show incM F (d.b⁻¹).1 * (incM F d.b.1 * uZ L u * incM F (d.b⁻¹).1) * incM F d.b.1 = uZ L u
  simp only [Matrix.mul_assoc]
  rw [SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.one_mul]

theorem unipotentPoint_add (u v : Fin L.n → AE F E) : unipotentPoint L (u + v) = unipotentPoint L u * unipotentPoint L v := by
  refine kfour.inFrame_injective d.b ?_
  rw [SiegelEisensteinSeries.Grp.inFrame_mul, inFrame_unipotentPoint, inFrame_unipotentPoint, inFrame_unipotentPoint, uZ_mul]

theorem unipotentPoint_zero : unipotentPoint L 0 = 1 := by
  refine kfour.inFrame_injective d.b ?_
  rw [SiegelEisensteinSeries.Grp.inFrame_one, inFrame_unipotentPoint, uZ_zero]

theorem uN_eq_sum (u : Fin L.n → AE F E) : uN L u = ∑ j, u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
  simp only [uN, Matrix.smul_single, smul_eq_mul, mul_one]

theorem continuous_uN : Continuous (uN L) := by
  rw [show uN L = fun u => ∑ j, u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) from funext (uN_eq_sum L)]
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const

theorem continuous_uZ : Continuous (uZ (σ := σ) L) := by
  have hD : Continuous (uD (σ := σ) L) :=
    continuous_const.sub (((continuous_uN L).matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)).matrix_transpose)
  exact (continuous_const.add (continuous_uN L)).matrix_fromBlocks continuous_const continuous_const hD

theorem continuous_unipotentPoint : Continuous (unipotentPoint (σ := σ) L) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (continuous_const.matrix_mul (continuous_uZ L)).matrix_mul continuous_const
  · exact (continuous_const.matrix_mul ((continuous_uZ L).comp continuous_neg)).matrix_mul continuous_const

theorem projected_block_upper_sum {ε : ℤˣ} (A D : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (h : (Matrix.fromBlocks A 0 0 D)ᵀ * Qa (d := d) ε * (Matrix.fromBlocks A 0 0 D).map (cA σ) = Qa ε) :
    Aᵀ * D.map (cA σ) = 1 := by
  have h' := congrArg Matrix.toBlocks₁₂ h
  simpa [Qa, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero _)] using h'

theorem uM_eq {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤) : uM = unipotentPoint L := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  have hcc := GlobalTheory.EisBL.DoubledUnipotentRadical.cA_cA σ hσ
  funext u
  obtain ⟨a', ha'⟩ := h.1 u
  refine kfour.inFrame_injective d.b ?_
  rw [inFrame_unipotentPoint, ha']
  have e1 := projected_block_upper_sum _ _ (ha' ▸ unitary_of_mem hε (uM u))
  have e2 := projected_block_upper_sum _ _ (uZ_unitary L ε u)
  have e3 : a'.map (cA σ) = (uD L u).map (cA σ) := by
    have e1' : a'.map (cA σ) * (1 + uN L u)ᵀ = 1 := mul_eq_one_comm.1 e1
    calc a'.map (cA σ) = a'.map (cA σ) * ((1 + uN L u)ᵀ * (uD L u).map (cA σ)) := by rw [e2, Matrix.mul_one]
      _ = (uD L u).map (cA σ) := by rw [← Matrix.mul_assoc, e1', Matrix.one_mul]
  have e4 : a' = uD L u := by
    ext i j
    have := congrArg (cA σ) (congrFun (congrFun e3 i) j)
    simpa [hcc] using this
  rw [e4]
  rfl

end Pts

section Meas

variable {d : SD σ} (L : LD d)

theorem incV_apply {k : ℕ} (e : Fin k → E) (i : Fin k) : GlobalTheory.ThK.incV F e i = inclR (F := F) (AF F) (e i) := rfl

theorem mem_ratV (v : Fin L.n → AE F E) : v ∈ L.ratV ↔ ∃ e, GlobalTheory.ThK.incV F e = v := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, funext fun i => by rw [incV_apply]; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨X, rfl⟩ := hx
      obtain ⟨Z, rfl⟩ := hy
      exact ⟨X + Z, funext fun i => by simp [incV_apply, map_add]⟩
    | neg x _ hx =>
      obtain ⟨X, rfl⟩ := hx
      exact ⟨-X, funext fun i => by simp [incV_apply, map_neg]⟩
  · rintro ⟨X, rfl⟩
    exact AddSubgroup.subset_closure ⟨X, rfl⟩

theorem ratV_discrete : DiscreteTopology L.ratV := by
  obtain ⟨V, hV, hV0⟩ := kfour.exists_nhds_inclR (F := F) (E := E)
  have hW : (⋂ i, (fun M : Fin L.n → AE F E => M i) ⁻¹' V) ∈ 𝓝 (0 : Fin L.n → AE F E) := by
    refine Filter.iInter_mem.2 fun i => ?_
    exact (continuous_apply i).continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨O, hOW, hO, h0⟩ := mem_nhds_iff.1 hW
  refine discreteTopology_of_isOpen_singleton_zero ?_
  convert hO.preimage (continuous_subtype_val (p := fun x => x ∈ L.ratV)) using 1
  ext ⟨x, hx⟩
  constructor
  · intro h
    have h1 : x = 0 := congrArg Subtype.val (Set.mem_singleton_iff.1 h)
    subst h1
    exact h0
  · intro h
    obtain ⟨X, rfl⟩ := (mem_ratV L _).1 hx
    have h2 : X = 0 := by
      funext i
      exact hV0 _ (Set.mem_iInter.1 (hOW h) i)
    subst h2
    exact Set.mem_singleton_iff.2 (Subtype.ext (funext fun i => show inclR (F := F) (AF F) ((0 : Fin L.n → E) i) = 0 by simp))

theorem ratV_cocompact : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ x, ∃ γ ∈ L.ratV, γ + x ∈ K := by
  obtain ⟨C, hC, hCx⟩ := kfour.exists_compact_AE (F := F) (E := E)
  refine ⟨Set.univ.pi fun _ => C, isCompact_univ_pi fun _ => hC, fun x => ?_⟩
  choose e he using fun i => hCx (x i)
  exact ⟨GlobalTheory.ThK.incV F e, (mem_ratV L _).2 ⟨e, rfl⟩, fun i _ => he i⟩

theorem exists_udata : ∃ uM ν 𝓤, L.UData uM ν 𝓤 := by
  haveI := ratV_discrete L
  obtain ⟨K, hK, hc⟩ := ratV_cocompact L
  obtain ⟨ν, 𝓤, hν, h𝓤, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (Fin L.n → AE F E) L.ratV K hK hc).1
  exact ⟨unipotentPoint L, ν, 𝓤, fun u => ⟨uD L u, inFrame_unipotentPoint L u⟩, hν, h𝓤, h1⟩

end Meas

section Dens

variable (d : SD σ)

def Sw (w : InfinitePlace F) : Set (AE F E) := {z | (∀ w', w' ≠ w → piInf (d.B.emb w') z = 0) ∧ finOne F • z = 0}

theorem finOne_mul {a : AF F} (ha : a.2 = 0) : finOne F * a = 0 :=
  Prod.ext (by change (0 : InfiniteAdeleRing F) * a.1 = 0; rw [zero_mul]) (by change (1 : Af F) * a.2 = 0; rw [ha, mul_zero])

theorem sum_mem_Sw (w : InfinitePlace F) (s : Fin (Module.finrank F E) → AF F) (hs : ∀ k, (s k).2 = 0 ∧ ∀ w', w' ≠ w → (s k).1 w' = 0) :
    ∑ k, s k • kfour.bsA F E k ∈ Sw d w := by
  refine ⟨fun w' hw' => ?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [St.piInf_smul, (hs k).2 w' hw', map_zero, zero_mul]
  · rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_smul, finOne_mul (hs k).1, zero_smul]

theorem dense_Sw (w : InfinitePlace F) : Dense {z : AE F E | ∃ e : E, ∃ s ∈ Sw d w, inclR (F := F) (AF F) e + s = z} := by
  have hA := GlobalTheory.T.dense_rationals_plus_single_place_adeles F w
  let Φ : (Fin (Module.finrank F E) → AF F) → AE F E := fun a => ∑ k, a k • kfour.bsA F E k
  have hΦc : Continuous Φ := continuous_finsetSum _ fun k _ => (continuous_apply k).smul continuous_const
  have hΦs : Function.Surjective Φ := fun z => ⟨fun k => (kfour.bsA F E).repr z k, (kfour.bsA F E).sum_repr z⟩
  have hd : Dense (Set.univ.pi fun _ : Fin (Module.finrank F E) =>
      (Set.range (algebraMap F (AF F)) + {a : AF F | a.2 = 0 ∧ ∀ w', w' ≠ w → a.1 w' = 0})) :=
    dense_pi _ fun k _ => hA
  refine (hΦs.denseRange.dense_image hΦc hd).mono ?_
  rintro _ ⟨a, ha, rfl⟩
  choose x hx s hs hxs using fun k => Set.mem_add.1 (ha k (Set.mem_univ k))
  choose q hq using hx
  refine ⟨∑ k, q k • kfour.bsE F E k, ∑ k, s k • kfour.bsA F E k, sum_mem_Sw d w s hs, ?_⟩
  have h1 : inclR (F := F) (AF F) (∑ k, q k • kfour.bsE F E k) = ∑ k, algebraMap F (AF F) (q k) • kfour.bsA F E k := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.basis_apply, algebraMap_smul, kfour.inclR_eq, TensorProduct.tmul_smul]
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_smul, hq, hxs]

theorem dense_vec (k : ℕ) (w : InfinitePlace F) :
    Dense {v : Fin k → AE F E | ∃ e : Fin k → E, ∃ s : Fin k → AE F E, (∀ j, s j ∈ Sw d w) ∧ GlobalTheory.ThK.incV F e + s = v} := by
  refine (dense_pi Set.univ fun j _ => dense_Sw d w).mono ?_
  intro v hv
  choose e s hs hes using fun j => hv j (Set.mem_univ j)
  exact ⟨e, s, hs, funext fun j => hes j⟩

end Dens

section Real

variable {d : SD σ} (L : LD d)

theorem cw_uN (w' : InfinitePlace F) (u : Fin L.n → AE F E) :
    d.cw w' (uN L u) = ∑ j, Matrix.single L.i₀ (L.em j) (piInf (d.B.emb w') (u j)) := by
  ext a b
  simp only [SD.cw, uN, Matrix.map_apply, Matrix.sum_apply, map_sum, Matrix.single_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem fin_uN (u : Fin L.n → AE F E) : finOne F • uN L u = ∑ j, Matrix.single L.i₀ (L.em j) (finOne F • u j) := by
  simp only [uN, Finset.smul_sum, Matrix.smul_single]

theorem cw_uZ (w' : InfinitePlace F) (u : Fin L.n → AE F E) :
    d.cw w' (uZ L u) = Matrix.fromBlocks (1 + d.cw w' (uN L u)) 0 0 (1 - ((d.cw w' (uN L u)).map star)ᵀ) := by
  have e1 : d.cw w' (1 + uN L u) = 1 + d.cw w' (uN L u) := by
    rw [SD.cw, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have e2 : d.cw w' (uD L u) = 1 - ((d.cw w' (uN L u)).map star)ᵀ := by
    rw [SD.cw, uD, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), ← Matrix.transpose_map,
      Place.map_cA d.cm]
    rfl
  rw [uZ, ← e1, ← e2]
  simp only [SD.cw, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]

theorem fin_uZ (u : Fin L.n → AE F E) :
    finOne F • uZ L u = Matrix.fromBlocks (finOne F • 1 + finOne F • uN L u) 0 0
      (finOne F • 1 - ((finOne F • uN L u).map (cA σ))ᵀ) := by
  rw [uZ, uD, Matrix.fromBlocks_smul, smul_zero, smul_add, smul_sub, Krd.map_cA_smul, Matrix.transpose_smul]

end Real

theorem exists_iota {d : SD σ} (R : RD d) (L : LD d) (w : InfinitePlace F) (u : Fin L.n → AE F E) (hu : ∀ j, u j ∈ Sw d w) :
    ∃ y, unipotentPoint L u = R.ι w y := by
  have h0 := Krd.zeta_ne R.hζ
  set Z := d.cw w (uZ L u) with hZdef
  set Z' := d.cw w (uZ L (-u)) with hZ'def
  have hZZ : Z * Z' = 1 := by rw [hZdef, hZ'def, ← Krd.cw_mul, uZ_mul, add_neg_cancel, uZ_zero, Krd.cw_one]
  have hZZ' : Z' * Z = 1 := by rw [hZdef, hZ'def, ← Krd.cw_mul, uZ_mul, neg_add_cancel, uZ_zero, Krd.cw_one]
  have hq : d.cw w (Qa (d := d) R.ε) = Krd.Qc d.n R.ε := by
    ext (i | i) (j | j) <;> simp [Qa, Krd.Qc, SD.cw, Matrix.one_apply] <;> split_ifs <;> simp
  have hQ : Zᵀ * Krd.Qc d.n R.ε * Z.map star = Krd.Qc d.n R.ε := by
    have h := congrArg (d.cw w) (uZ_unitary L R.ε u)
    rw [Krd.cw_mul, Krd.cw_mul, Krd.cw_transpose, Place.cw_cA, hq] at h
    exact h
  let y : GR d.n := ⟨⟨dZ d.n R.ζ * Z * dZ d.n R.ζ⁻¹, dZ d.n R.ζ * Z' * dZ d.n R.ζ⁻¹, by
      rw [show dZ d.n R.ζ * Z * dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * Z' * dZ d.n R.ζ⁻¹) =
        dZ d.n R.ζ * Z * (dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) * Z' * dZ d.n R.ζ⁻¹ by simp only [Matrix.mul_assoc],
        Krd.dZ_inv_mul h0, Matrix.mul_one, Matrix.mul_assoc (dZ d.n R.ζ), hZZ, Matrix.mul_one, Krd.dZ_mul_inv h0], by
      rw [show dZ d.n R.ζ * Z' * dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * Z * dZ d.n R.ζ⁻¹) =
        dZ d.n R.ζ * Z' * (dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) * Z * dZ d.n R.ζ⁻¹ by simp only [Matrix.mul_assoc],
        Krd.dZ_inv_mul h0, Matrix.mul_one, Matrix.mul_assoc (dZ d.n R.ζ), hZZ', Matrix.mul_one, Krd.dZ_mul_inv h0]⟩,
    Krd.inG_conj R.hζ Z hQ⟩
  refine ⟨y, kfour.inFrame_injective d.b ?_⟩
  rw [inFrame_unipotentPoint]
  refine Place.cw_ext d (fun w' => ?_) ?_
  · by_cases hw' : w' = w
    · subst hw'
      have h1 := R.at_w w' y
      have h2 : dZ d.n R.ζ * d.cw w' (inFrame d.b (R.ι w' y)) = dZ d.n R.ζ * Z := by
        rw [h1]
        show dZ d.n R.ζ * Z * dZ d.n R.ζ⁻¹ * dZ d.n R.ζ = dZ d.n R.ζ * Z
        rw [Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.mul_one]
      have h3 := congrArg (fun M => dZ d.n R.ζ⁻¹ * M) h2
      simp only [← Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.one_mul] at h3
      exact h3.symm
    · have hN : d.cw w' (uN L u) = 0 := by
        rw [cw_uN]
        exact Finset.sum_eq_zero fun j _ => by rw [(hu j).1 w' hw', Matrix.single_zero]
      rw [R.off_w w w' y hw', cw_uZ, hN]
      simp [Matrix.fromBlocks_one]
  · have hN : finOne F • uN L u = 0 := by
      rw [fin_uN]
      exact Finset.sum_eq_zero fun j _ => by rw [(hu j).2, Matrix.single_zero]
    rw [R.off_f w y, fin_uZ, hN]
    simp only [Matrix.map_zero _ (map_zero _), Matrix.transpose_zero, sub_zero, add_zero]
    conv_rhs => rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]

theorem uEx : UEx := by
  intro F E _ _ _ _ _ σ d R L
  refine ⟨exists_udata L, ?_⟩
  intro uM ν 𝓤 hU w φ hφ hrat hw u x
  have he := uM_eq L hU
  subst he
  haveI := (kfour.doubled_group_topological_properties σ d.Y).1
  let S : AddSubgroup (Fin L.n → AE F E) :=
    { carrier := {u | ∀ x, φ (unipotentPoint L u * x) = φ x}
      add_mem' := fun {a b} ha hb x => by
        show φ (unipotentPoint L (a + b) * x) = φ x
        rw [unipotentPoint_add, mul_assoc, ha, hb]
      zero_mem' := fun x => by
        show φ (unipotentPoint L 0 * x) = φ x
        rw [unipotentPoint_zero, one_mul]
      neg_mem' := fun {a} ha x => by
        show φ (unipotentPoint L (-a) * x) = φ x
        have := ha (unipotentPoint L (-a) * x)
        rw [← mul_assoc, ← unipotentPoint_add, add_neg_cancel, unipotentPoint_zero, one_mul] at this
        exact this.symm }
  have hS : IsClosed (S : Set (Fin L.n → AE F E)) := by
    have : (S : Set (Fin L.n → AE F E)) = ⋂ x, {u | φ (unipotentPoint L u * x) = φ x} := by
      ext u
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    rw [this]
    exact isClosed_iInter fun x => isClosed_eq (hφ.comp ((continuous_unipotentPoint L).mul continuous_const)) continuous_const
  have hT : {v : Fin L.n → AE F E | ∃ e : Fin L.n → E, ∃ s : Fin L.n → AE F E, (∀ j, s j ∈ Sw d w) ∧
      GlobalTheory.ThK.incV F e + s = v} ⊆ S := by
    rintro _ ⟨e, s, hs, rfl⟩
    refine S.add_mem (fun x => hrat _ ((mem_ratV L _).2 ⟨e, rfl⟩) x) ?_
    obtain ⟨y, hy⟩ := exists_iota R L w s hs
    exact fun x => hw s y hy x
  have hu : u ∈ S := by
    have h1 := closure_minimal hT hS
    rw [(dense_vec d L.n w).closure_eq] at h1
    exact h1 (Set.mem_univ u)
  exact hu x

end PositivityTheory.SiegelWeilFormula.Afc

end
