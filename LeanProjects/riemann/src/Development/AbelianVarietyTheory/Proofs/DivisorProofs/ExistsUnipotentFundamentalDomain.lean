import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactLatticeUnitCovolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteRationalPointsSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactFundamentalSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergMatrixPreservesFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergMatrixMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR (σ : E →ₐ[F] E) (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  show Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] a) = (1 : AF F) ⊗ₜ[F] σ a
  simp

theorem cA_cA {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => show Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x; simp [hσ]

theorem hA_skew {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → AE F E) : cA σ (hA σ J v w) = -hA σ J w v := by
  simp only [hA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_cA hσ, incM, Matrix.map_apply, cA_inclR]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hJ y x, map_neg]
  ring

theorem hA_incV (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    hA σ J (incV F v) (incV F w) = inclR (F := F) (AF F) (form σ J v w) := by
  simp only [hA, form, incV, incM, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, cA_inclR]

theorem incM_mulVec_incV {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incM F A *ᵥ incV F v = incV F (A *ᵥ v) := by
  ext i
  simp only [incM, incV, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem hA_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    hA σ J (v + v') w = hA σ J v w + hA σ J v' w := add_dotProduct _ _ _

theorem hA_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w w' : Fin n → AE F E) :
    hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  simp only [hA, Pi.add_apply, map_add]
  rw [show (fun i => cA σ (w i) + cA σ (w' i)) = (fun i => cA σ (w i)) + fun i => cA σ (w' i) from rfl,
    Matrix.mulVec_add, dotProduct_add]

theorem hA_neg_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → AE F E) :
    hA σ J (-v) w = -hA σ J v w := neg_dotProduct _ _

theorem hA_neg_right' (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → AE F E) :
    hA σ J v (-w) = -hA σ J v w := by
  simp only [hA, Pi.neg_apply, map_neg]
  rw [show (fun i => -cA σ (w i)) = -(fun i => cA σ (w i)) from rfl, Matrix.mulVec_neg, dotProduct_neg]

theorem hA_zero_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Fin n → AE F E) :
    hA σ J v 0 = 0 := by
  simp only [hA, Pi.zero_apply, map_zero]
  rw [show (fun _ : Fin n => (0 : AE F E)) = 0 from rfl, Matrix.mulVec_zero, dotProduct_zero]

theorem hA_zero_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Fin n → AE F E) :
    hA σ J 0 v = 0 := by simp [hA]

theorem nmat_rat (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x u : Fin n → E) (c : E) :
    nmat σ J (incV F x) (incV F u) (inclR (F := F) (AF F) c) =
      (1 - Matrix.vecMulVec (u + c • x) (J *ᵥ fun i => σ (x i)) - Matrix.vecMulVec x (J *ᵥ fun i => σ (u i))).map
        (inclR (F := F) (AF F)) := by
  ext i j
  simp only [nmat, incV, incM, Matrix.map_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    map_sub, map_mul, map_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, cA_inclR, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.UnipMass

namespace GlobalTheory.UnipMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem nmat_zero (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → AE F E) :
    nmat σ J x 0 0 = 1 := by
  simp only [nmat, zero_smul, add_zero, Pi.zero_apply, map_zero]
  rw [show (fun _ : Fin n => (0 : AE F E)) = 0 from rfl, Matrix.mulVec_zero]
  simp

structure Hyp (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Prop where
  σσ : ∀ a, σ (σ a) = a
  skew : ∀ i j, σ (W.J j i) = -W.J i j
  xx : hA σ W.J (incV F H'.x) (incV F H'.x) = 0
  ιx : ∀ z, hA σ W.J (incM F H'.ι *ᵥ z) (incV F H'.x) = 0

variable {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁}

theorem Hyp.xι (h : Hyp σ W H') (z : Fin d₁ → AE F E) : hA σ W.J (incV F H'.x) (incM F H'.ι *ᵥ z) = 0 := by
  have := hA_skew h.σσ h.skew (incM F H'.ι *ᵥ z) (incV F H'.x)
  rw [h.ιx z, map_zero] at this
  exact neg_eq_zero.1 this.symm

theorem mem_unip (h : Hyp σ W H') (g : UA σ W.J) (b : Fin d₁ → AE F E) (c : AE F E)
    (hg : mat g = nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c) : g ∈ unip σ W H' := by
  refine Subgroup.subset_closure ⟨?_, fun z => ⟨-hA σ W.J (incM F H'.ι *ᵥ z) (incM F H'.ι *ᵥ b), ?_⟩⟩
  · rw [hg, nmat_mulVec, h.xx, h.xι]; simp
  · rw [hg, nmat_mulVec, h.ιx]; simp [sub_eq_add_neg]

theorem nmat_mul (h : Hyp σ W H') (b b' : Fin d₁ → AE F E) (c c' : AE F E) :
    nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c * nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b') c' =
      nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ (b + b')) (c + c' - hA σ W.J (incM F H'.ι *ᵥ b') (incM F H'.ι *ᵥ b)) := by
  rw [GlobalTheory.T.heisenberg_matrix_mul F E σ h.σσ d W.J h.skew _ _ _ c c' h.xx (h.ιx b) (h.ιx b'), Matrix.mulVec_add]

def elt (h : Hyp σ W H') (b : Fin d₁ → AE F E) (c : AE F E)
    (hc : c - cA σ c = -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b)) : unip σ W H' :=
  ⟨⟨⟨nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c,
    nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ -b) (-c - hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b)),
    by rw [nmat_mul h, add_neg_cancel, Matrix.mulVec_neg, hA_neg_left, show c + (-c - hA σ W.J (incM F H'.ι *ᵥ b)
        (incM F H'.ι *ᵥ b)) - -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b) = 0 by ring, Matrix.mulVec_zero, nmat_zero],
    by rw [nmat_mul h, neg_add_cancel, Matrix.mulVec_neg, hA_neg_right', show -c - hA σ W.J (incM F H'.ι *ᵥ b)
        (incM F H'.ι *ᵥ b) + c - -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b) = 0 by ring, Matrix.mulVec_zero, nmat_zero]⟩,
    GlobalTheory.T.heisenberg_matrix_preserves_form F E σ h.σσ d W.J h.skew _ _ c h.xx (h.ιx b) hc⟩,
    mem_unip h _ b c rfl⟩

theorem mat_elt (h : Hyp σ W H') (b : Fin d₁ → AE F E) (c : AE F E) (hc) :
    mat ((elt h b c hc : unip σ W H') : UA σ W.J) = nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c := rfl

theorem unip_ext {g g' : unip σ W H'} (e : mat (g : UA σ W.J) = mat (g' : UA σ W.J)) : g = g' :=
  Subtype.ext (Subtype.ext (Units.ext e))

end GlobalTheory.UnipMass

namespace GlobalTheory.UnipMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_range_of {n : ℕ} (g : GL (Fin n) (AE F E)) (M M' : Matrix (Fin n) (Fin n) E)
    (h1 : (g : Matrix (Fin n) (Fin n) (AE F E)) = M.map (inclR (F := F) (AF F)))
    (h2 : ((g⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = M'.map (inclR (F := F) (AF F))) :
    g ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range := by
  have inj : Function.Injective fun N : Matrix (Fin n) (Fin n) E => N.map (inclR (F := F) (AF F)) :=
    Matrix.map_injective (Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F))
  have e1 : M * M' = 1 := inj (by
    simp only
    rw [Matrix.map_mul (f := inclR (F := F) (AF F)), ← h1, ← h2, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have e2 : M' * M = 1 := inj (by
    simp only
    rw [Matrix.map_mul (f := inclR (F := F) (AF F)), ← h1, ← h2, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  exact ⟨⟨M, M', e1, e2⟩, Units.ext (by simp [Matrix.GeneralLinearGroup.map, h1])⟩

def nE (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x u : Fin n → E) (c : E) : Matrix (Fin n) (Fin n) E :=
  1 - Matrix.vecMulVec (u + c • x) (J *ᵥ fun i => σ (x i)) - Matrix.vecMulVec x (J *ᵥ fun i => σ (u i))

variable {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁}

theorem elt_rat (h : Hyp σ W H') (b₀ : Fin d₁ → E) (c₀ : E) (hc) :
    ((elt h (incV F b₀) (inclR (F := F) (AF F) c₀) hc : unip σ W H') : UA σ W.J) ∈ ratU σ W.J := by
  refine Subgroup.mem_subgroupOf.2 (mem_range_of _ (nE σ W.J H'.x (H'.ι *ᵥ b₀) c₀)
    (nE σ W.J H'.x (H'.ι *ᵥ -b₀) (-c₀ - form σ W.J (H'.ι *ᵥ b₀) (H'.ι *ᵥ b₀))) ?_ ?_)
  · exact (congrArg (fun u => nmat σ W.J (incV F H'.x) u _) (incM_mulVec_incV _ _)).trans (nmat_rat σ W.J _ _ c₀)
  · show nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ -incV F b₀) (-inclR (F := F) (AF F) c₀ -
      hA σ W.J (incM F H'.ι *ᵥ incV F b₀) (incM F H'.ι *ᵥ incV F b₀)) = _
    rw [show -incV F b₀ = incV F (-b₀) from funext fun i => (map_neg (inclR (F := F) (AF F)) (b₀ i)).symm, incM_mulVec_incV, incM_mulVec_incV,
      hA_incV, ← map_neg, ← map_sub]
    exact nmat_rat σ W.J _ _ _

end GlobalTheory.UnipMass

namespace GlobalTheory.UnipMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hA_incM_incV (σ : E →ₐ[F] E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin m) E)
    (z : Fin m → AE F E) (v : Fin n → E) :
    hA σ J (incM F A *ᵥ z) (incV F v) = ∑ j, z j * inclR (F := F) (AF F) (form σ J (fun i => A i j) v) := by
  simp only [hA, form, dotProduct, Matrix.mulVec, incM, incV, Matrix.map_apply, cA_inclR, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem topUA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsTopologicalGroup (UA σ J) ∧ LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧
      T2Space (UA σ J) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hs : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) := Units.continuous_val
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hs))
      continuous_const
  exact ⟨inferInstance, hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology,
    inferInstanceAs (T2Space (UG (cA σ) (incM F J)))⟩

theorem countable_ratU' (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (N : Subgroup (UA σ J)) :
    Countable ((ratU σ J).subgroupOf N) := by
  haveI : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j)
      fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  haveI := (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))).to_subtype
  exact Function.Injective.countable
    (f := fun γ : (ratU σ J).subgroupOf N => (⟨γ.1.1.1, Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 γ.2)⟩ :
      Set.range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))))
    fun γ γ' h => Subtype.val_injective (Subtype.val_injective (Subtype.val_injective (congrArg Subtype.val h :)))

theorem continuous_nmat (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → AE F E) {X : Type}
    [TopologicalSpace X] {u : X → Fin n → AE F E} {c : X → AE F E} (hu : Continuous u) (hc : Continuous c) :
    Continuous fun p => nmat σ J x (u p) (c p) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hs : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  unfold nmat
  refine (continuous_const.sub ?_).sub ?_
  · exact (hu.add (hc.smul continuous_const)).matrix_vecMulVec continuous_const
  · exact continuous_const.matrix_vecMulVec
      (continuous_const.matrix_mulVec (continuous_pi fun i => hs.comp ((continuous_apply i).comp hu)))

end GlobalTheory.UnipMass

namespace GlobalTheory.UnipMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁}

theorem cocompact (h : Hyp σ W H') (hxx : form σ W.J H'.x H'.x = 0) (hyy : form σ W.J H'.y H'.y = 0)
    (hxy : form σ W.J H'.x H'.y = 1)
    (horth : ∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 ∧ form σ W.J (H'.ι *ᵥ u) H'.y = 0)
    (hspan : ∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y) :
    ∃ K : Set (unip σ W H'), IsCompact K ∧
      ∀ g : unip σ W H', ∃ γ : (ratU σ W.J).subgroupOf (unip σ W H'), γ • g ∈ K := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hs : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  obtain ⟨KE, hKE, hcov⟩ := GlobalTheory.T.adele_quotient_compact_fundamental_set F E
  set ι := incM F H'.ι with hι
  set half : AE F E := inclR (F := F) (AF F) (2⁻¹ : E) with hhalf_def
  have hhalf : (2 : AE F E) * half = 1 := by
    rw [hhalf_def, ← map_ofNat (inclR (F := F) (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hσhalf : cA σ half = half := by rw [hhalf_def, cA_inclR, map_inv₀, map_ofNat]
  have hsk : ∀ v w, cA σ (hA σ W.J v w) = -hA σ W.J w v := hA_skew h.σσ h.skew
  let cf : (Fin d₁ → AE F E) → AE F E → AE F E :=
    fun b k => half * (k + cA σ k) - half * hA σ W.J (ι *ᵥ b) (ι *ᵥ b)
  have hcf : ∀ b k, cf b k - cA σ (cf b k) = -hA σ W.J (ι *ᵥ b) (ι *ᵥ b) := by
    intro b k
    simp only [cf, map_sub, map_mul, map_add, hσhalf, cA_cA h.σσ, hsk]
    linear_combination (-hA σ W.J (ι *ᵥ b) (ι *ᵥ b)) * hhalf
  let Q : (Fin d₁ → AE F E) × AE F E → unip σ W H' := fun p => elt h p.1 (cf p.1 p.2) (hcf p.1 p.2)
  have hcfc : Continuous fun p : (Fin d₁ → AE F E) × AE F E => cf p.1 p.2 := by
    have hh : Continuous fun p : (Fin d₁ → AE F E) × AE F E => hA σ W.J (ι *ᵥ p.1) (ι *ᵥ p.1) := by
      unfold hA
      exact (continuous_const.matrix_mulVec continuous_fst).dotProduct (continuous_const.matrix_mulVec
        (continuous_pi fun i => hs.comp ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_fst))))
    exact (continuous_const.mul (continuous_snd.add (hs.comp continuous_snd))).sub (continuous_const.mul hh)
  have hQ : Continuous Q := by
    refine Continuous.subtype_mk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _) _
    · exact continuous_nmat σ W.J _ (continuous_const.matrix_mulVec continuous_fst) hcfc
    · have hh : Continuous fun p : (Fin d₁ → AE F E) × AE F E => hA σ W.J (ι *ᵥ p.1) (ι *ᵥ p.1) := by
        unfold hA
        exact (continuous_const.matrix_mulVec continuous_fst).dotProduct (continuous_const.matrix_mulVec
          (continuous_pi fun i => hs.comp ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_fst))))
      exact continuous_nmat σ W.J _ (continuous_const.matrix_mulVec continuous_fst.neg) (hcfc.neg.sub hh)
  refine ⟨Q '' (Set.univ.pi (fun _ => KE) ×ˢ KE), ((isCompact_univ_pi fun _ => hKE).prod hKE).image hQ, fun g => ?_⟩
  obtain ⟨b, c, hc, hg⟩ := GlobalTheory.T.hyperbolic_pair_decomposition F E σ h.σσ d d₁ W H' h.skew hxx hyy hxy horth hspan g g.2
  choose e he using fun j => hcov (b j)
  set u₀ := ι *ᵥ incV F (-e) with hu₀
  set c₁E : E := -(2⁻¹ * form σ W.J (H'.ι *ᵥ -e) (H'.ι *ᵥ -e)) with hc₁E
  have hhu₀ : hA σ W.J u₀ u₀ = inclR (F := F) (AF F) (form σ W.J (H'.ι *ᵥ -e) (H'.ι *ᵥ -e)) := by
    rw [hu₀, hι, incM_mulVec_incV, hA_incV]
  have hc₁ : inclR (F := F) (AF F) c₁E - cA σ (inclR (F := F) (AF F) c₁E) = -hA σ W.J u₀ u₀ := by
    have e1 : inclR (F := F) (AF F) c₁E = -(half * hA σ W.J u₀ u₀) := by
      rw [hhu₀, hc₁E, map_neg, map_mul, hhalf_def]
    rw [e1, map_neg, map_mul, hσhalf, hsk]
    linear_combination (-hA σ W.J u₀ u₀) * hhalf
  let γ₁ : (ratU σ W.J).subgroupOf (unip σ W H') := ⟨elt h (incV F (-e)) _ hc₁, elt_rat h _ _ hc₁⟩
  set c₂ := inclR (F := F) (AF F) c₁E + c - hA σ W.J (ι *ᵥ b) u₀ with hc₂_def
  set b' : Fin d₁ → AE F E := incV F (-e) + b with hb'_def
  have hm1 : mat ((γ₁ • g : unip σ W H') : UA σ W.J) = nmat σ W.J (incV F H'.x) (ι *ᵥ b') c₂ := by
    show nmat σ W.J (incV F H'.x) u₀ (inclR (F := F) (AF F) c₁E) * mat (g : UA σ W.J) = _
    rw [hg, hu₀, nmat_mul h]
  have hc₂ : c₂ - cA σ c₂ = -hA σ W.J (ι *ᵥ b') (ι *ᵥ b') := by
    rw [hb'_def, Matrix.mulVec_add, ← hu₀, hA_add_left, hA_add_right, hA_add_right, hc₂_def]
    simp only [map_add, map_sub]
    linear_combination hc₁ + hc + hsk (ι *ᵥ b) u₀
  set s := half * (c₂ + cA σ c₂) with hs_def
  have hσs : cA σ s = s := by rw [hs_def, map_mul, hσhalf, map_add, cA_cA h.σσ, add_comm (cA σ c₂)]
  obtain ⟨e', he'⟩ := hcov s
  set k := s - inclR (F := F) (AF F) e' with hk_def
  set e₀ : E := -(2⁻¹ * (e' + σ e')) with he₀_def
  have hσe₀ : σ e₀ = e₀ := by
    rw [he₀_def, map_neg, map_mul, map_add, h.σσ, map_inv₀, map_ofNat, add_comm (σ e')]
  have h0 : incV F (0 : Fin d₁ → E) = 0 := funext fun _ => map_zero _
  have hc₃ : inclR (F := F) (AF F) e₀ - cA σ (inclR (F := F) (AF F) e₀) =
      -hA σ W.J (ι *ᵥ incV F 0) (ι *ᵥ incV F 0) := by
    rw [cA_inclR, hσe₀, sub_self, h0, Matrix.mulVec_zero, hA_zero_left, neg_zero]
  let γ₂ : (ratU σ W.J).subgroupOf (unip σ W H') := ⟨elt h (incV F 0) _ hc₃, elt_rat h _ _ hc₃⟩
  have key : inclR (F := F) (AF F) e₀ + c₂ = cf b' k := by
    have he₀' : inclR (F := F) (AF F) e₀ =
        -(half * (inclR (F := F) (AF F) e' + inclR (F := F) (AF F) (σ e'))) := by
      rw [he₀_def, map_neg, map_mul, map_add, hhalf_def]
    have hσk : cA σ k = s - inclR (F := F) (AF F) (σ e') := by rw [hk_def, map_sub, hσs, cA_inclR]
    simp only [cf]
    linear_combination he₀' + (-half) * hk_def + (-half) * hσk + half * hc₂ -
      (c₂ * (1 + half) + half * cA σ c₂) * hhalf + (-2 * half) * hs_def
  refine ⟨γ₂ * γ₁, (b', k), ⟨fun j _ => ?_, he'⟩, ?_⟩
  · have : b' j = b j - inclR (F := F) (AF F) (e j) := by
      rw [hb'_def, Pi.add_apply, show incV F (-e) j = -inclR (F := F) (AF F) (e j) from map_neg _ _]
      ring
    show b' j ∈ KE
    rw [this]
    exact he j
  · apply unip_ext
    rw [mul_smul]
    show nmat σ W.J (incV F H'.x) (ι *ᵥ b') (cf b' k) =
      nmat σ W.J (incV F H'.x) (ι *ᵥ incV F 0) (inclR (F := F) (AF F) e₀) * mat ((γ₁ • g : unip σ W H') : UA σ W.J)
    rw [hm1, nmat_mul h, h0, zero_add, Matrix.mulVec_zero, hA_zero_right, sub_zero, key]

end GlobalTheory.UnipMass

namespace GlobalTheory.UnipMass

theorem exists_haar_unip_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om', IsTriple B G X om om' →
      ∃ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' hT
  have hσ : ∀ a, σ (σ a) = a := cm_conj_conj hT.base.cm
  have hW := hT.geo.hW
  have hH := hC.hH'
  have hspan : ∀ v : Fin (b + 2 + a') → E, ∃ (s t : E) (u : Fin (b + a') → E),
      v = s • H'.x + H'.ι *ᵥ u + t • H'.y := by
    intro v
    have hv : v ∈ Submodule.span E (G.W.L : Set (Fin (b + 2 + a') → E)) := by
      rw [hW.lat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, u, -, -, -, hz⟩ := hH.split z hz
      exact ⟨s, t, u, hz⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, t, u, rfl⟩ := hy
      obtain ⟨s', t', u', rfl⟩ := hz
      exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
    | smul a y _ hy =>
      obtain ⟨s, t, u, rfl⟩ := hy
      exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩
  have horthA : ∀ z, hA σ G.W.J (incM F H'.ι *ᵥ z) (incV F H'.x) = 0 := by
    intro z
    rw [hA_incM_incV]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 := (hH.orth (Pi.single j 1)).1
    rw [Matrix.mulVec_single_one] at h1
    rw [show (fun i => H'.ι i j) = H'.ι.col j from rfl, h1, map_zero, mul_zero]
  have h : Hyp σ G.W H' := ⟨hσ, hW.skew, by rw [hA_incV, hH.xx, map_zero], horthA⟩
  have hx0 : H'.x ≠ 0 := fun h0 => by
    have h1 := hH.xy
    rw [h0] at h1
    simp [form] at h1
  obtain ⟨hTG, hLC, hSC, hT2⟩ := topUA σ G.W.J
  haveI := hTG
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  have hcl := GlobalTheory.T.unipotent_radical_closed_nonzero F E σ _ _ G.W H' hx0
  haveI : LocallyCompactSpace (unip σ G.W H') := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ G.W H') :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := countable_ratU' σ G.W.J (unip σ G.W H')
  haveI := GlobalTheory.T.discrete_rational_points_subgroup F E σ _ G.W.J (unip σ G.W H')
  obtain ⟨K, hK, hcov⟩ := cocompact h hH.xx hH.yy hH.xy hH.orth hspan
  exact GlobalTheory.T.cocompact_lattice_unit_covolume _ _ K hK hcov

end GlobalTheory.UnipMass
