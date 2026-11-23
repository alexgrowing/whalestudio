import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRight
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SkewLeviNear

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.SkewLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem continuous_atPlace : Continuous (atPlace (F := F) v) :=
  Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v)

theorem continuous_linear_prod (f : Fv F v × Fv F v →ₗ[Fv F v] Fv F v) : Continuous f := by
  have e : ∀ p : Fv F v × Fv F v, f p = p.1 * f (1, 0) + p.2 * f (0, 1) := by
    intro p
    rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have : (f : Fv F v × Fv F v → Fv F v) = fun p => p.1 * f (1, 0) + p.2 * f (0, 1) := funext e
  rw [this]
  exact (continuous_fst.mul continuous_const).add (continuous_snd.mul continuous_const)

theorem continuous_tensAt_split (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) :
    Continuous fun p : Fv F v × Fv F v => tensAt E v ((splitAlgEquiv h t).symm p) := by
  let b := Module.Free.chooseBasis F E
  let bv := Algebra.TensorProduct.basis (Fv F v) b
  have key : ∀ y : TensorProduct F (Fv F v) E,
      tensAt E v y = ∑ i, atPlace v (bv.repr y i) • ((1 : AF F) ⊗ₜ[F] b i) := by
    intro y
    conv_lhs => rw [← bv.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, tensAt_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have : (fun p : Fv F v × Fv F v => tensAt E v ((splitAlgEquiv h t).symm p)) =
      fun p => ∑ i, atPlace v (bv.repr ((splitAlgEquiv h t).symm p) i) • ((1 : AF F) ⊗ₜ[F] b i) :=
    funext fun p => key _
  rw [this]
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  refine continuous_finsetSum _ fun i _ => ?_
  have hc : Continuous fun p : Fv F v × Fv F v => atPlace v (bv.repr ((splitAlgEquiv h t).symm p) i) :=
    continuous_atPlace.comp (continuous_linear_prod ((bv.coord i).comp (splitAlgEquiv h t).symm.toLinearMap))
  exact hc.smul (continuous_const : Continuous fun _ : Fv F v × Fv F v => ((1 : AF F) ⊗ₜ[F] b i : AE F E))

end GlobalTheory.SkewLeviNear

namespace GlobalTheory.SkewLeviNear

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.SkewLevi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem continuous_lift_locMat (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) :
    Continuous fun g : GL (Fin n) (Fv F v) => lift v (locMat h t J g) := by
  have hc : Continuous fun g : GL (Fin n) (Fv F v) => conjComp t J g :=
    (continuous_const.matrix_mul Units.continuous_coe_inv.matrix_transpose).matrix_mul continuous_const
  refine continuous_matrix fun i j => ?_
  have e : (fun g : GL (Fin n) (Fv F v) => lift v (locMat h t J g) i j) = fun g : GL (Fin n) (Fv F v) =>
      (1 : Matrix (Fin n) (Fin n) (AE F E)) i j +
        (tensAt E v ((splitAlgEquiv h t).symm ((g : Matrix (Fin n) (Fin n) (Fv F v)) i j, conjComp t J g i j)) +
          -tensAt E v ((1 : Matrix (Fin n) (Fin n) (TensorProduct F (Fv F v) E)) i j)) := by
    funext g
    simp only [lift, ext0, Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, map_sub]
    rw [sub_eq_add_neg]
    rfl
  rw [e]
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  refine continuous_const.add (Continuous.add ?_ continuous_const)
  refine (continuous_tensAt_split h t).comp (Continuous.prodMk ?_ ?_)
  · exact (Units.continuous_val.matrix_elem i j)
  · exact hc.matrix_elem i j

end GlobalTheory.SkewLeviNear

namespace GlobalTheory.SkewLeviNear

open GlobalTheory.EmbChart GlobalTheory.LeviAtPlace GlobalTheory.SkewLevi

theorem near_one_det : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v), ∀ U ∈ 𝓝 (1 : UA σ G.W.J), ∃ V ∈ 𝓝 (1 : (Fv F v)ˣ), ∀ x ∈ V,
      ∃ h ∈ UAt σ G.W (evFin F v), h ∈ U ∧ ((mat h).map (piW t)).det = (x : Fv F v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v _ t U hU
  have h := hTr.base.cm
  have hJ : IsUnit (G.W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hTr.geo.hW.sig (InfinitePlace.mk φ))
    have h1 : G.W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show G.W.J.map _ = RingHom.mapMatrix _ G.W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show G.W.J.map t = (t : E →+* Fv F v).mapMatrix G.W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  let Ψ : GL (Fin (a + a')) (Fv F v) → UA σ G.W.J := fun g =>
    ⟨adelicGL h t G.W.J hJ g, lift_unitary v σ G.W.J _ (locMat_unitary_skew h t G.W.J hJ hTr.geo.hW.skew g)⟩
  have hΨc : Continuous Ψ := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨continuous_lift_locMat h t G.W.J, ?_⟩) _
    exact (continuous_lift_locMat h t G.W.J).comp continuous_inv
  have hΨ1 : Ψ 1 = 1 := Subtype.ext (Units.ext (by
    change lift v (LeviAtPlace.locMat h t G.W.J 1) = 1
    rw [locMat_one h t G.W.J hJ, lift_one]))
  have hΨt : ∀ g, (mat (Ψ g)).map (piW t) = g.1 := by
    intro g
    change (lift v (LeviAtPlace.locMat h t G.W.J g)).map (piW t) = g.1
    have key : (lift v (LeviAtPlace.locMat h t G.W.J g)).map (piW t) =
        (LeviAtPlace.locMat h t G.W.J g).map (splitProj t) := by
      conv_rhs => rw [← compFin_lift v (LeviAtPlace.locMat h t G.W.J g), Matrix.map_map]
      rfl
    rw [key]
    exact pairMat_fst h t _ _
  have i0 : Fin (a + a') := ⟨0, by have := hTr.geo.lt; omega⟩
  let D : (Fv F v)ˣ →* GL (Fin (a + a')) (Fv F v) :=
    Units.map ((Matrix.diagonalRingHom (Fin (a + a')) (Fv F v)).toMonoidHom.comp
      (MonoidHom.mulSingle (fun _ => Fv F v) i0))
  have hDv : ∀ x : (Fv F v)ˣ, ((D x : GL (Fin (a + a')) (Fv F v)) : Matrix (Fin (a + a')) (Fin (a + a')) (Fv F v)) =
      Matrix.diagonal (Pi.mulSingle i0 (x : Fv F v)) := fun x => rfl
  have hDc : Continuous D := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have : (Units.val ∘ D) = fun x : (Fv F v)ˣ => Matrix.diagonal (Pi.mulSingle i0 (x : Fv F v)) := funext hDv
      rw [this]
      exact (continuous_mulSingle i0 |>.comp Units.continuous_val).matrix_diagonal
    · have : (fun x => ((D x)⁻¹ : GL (Fin (a + a')) (Fv F v)).1) =
          fun x : (Fv F v)ˣ => Matrix.diagonal (Pi.mulSingle i0 ((x⁻¹ : (Fv F v)ˣ) : Fv F v)) := by
        funext x; rw [← map_inv]; rfl
      rw [this]
      exact (continuous_mulSingle i0 |>.comp Units.continuous_coe_inv).matrix_diagonal
  have hf : Continuous fun x => Ψ (D x) := hΨc.comp hDc
  have hf1 : Ψ (D 1) = 1 := by rw [map_one, hΨ1]
  refine ⟨(fun x => Ψ (D x)) ⁻¹' U, hf.continuousAt.preimage_mem_nhds (by rw [hf1]; exact hU), fun x hx => ?_⟩
  refine ⟨Ψ (D x), lift_sub_one_at v _, hx, ?_⟩
  rw [hΨt, hDv, Matrix.det_diagonal]
  simp

end GlobalTheory.SkewLeviNear
