import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PositionOf

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

noncomputable section

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

open mixedEmbedding

section mk

variable {K : Type} [Field K] [NumberField K] {ι : Type}

private def entM (c : mixedSpace K ≃+* (ι → ℂ)) (n : ℕ) :
    Matrix (Fin n) (Fin n) (mixedSpace K) ≃+* (ι → Matrix (Fin n) (Fin n) ℂ) where
  toFun X i := Matrix.of fun a b => c (X a b) i
  invFun Y := Matrix.of fun a b => c.symm fun i => Y i a b
  left_inv X := by
    ext1 a b
    exact c.symm_apply_apply (X a b)
  right_inv Y := by
    funext i
    ext a b
    simp
  map_mul' X Y := by
    funext i
    ext a b
    simp [Matrix.mul_apply, map_sum, Finset.sum_apply]
  map_add' X Y := by
    funext i
    ext a b
    simp

private def entC (c : mixedSpace K ≃+* (ι → ℂ)) (n : ℕ) : ArchMatrix K n ≃+* (ι → Matrix (Fin n) (Fin n) ℂ) := entM c n

private theorem continuous_entC {c : mixedSpace K ≃+* (ι → ℂ)} (hc : Continuous c) (n : ℕ) : Continuous (entC c n) := by
  refine continuous_pi fun i => ?_
  refine continuous_matrix fun a b => ?_
  have h : Continuous fun X : Matrix (Fin n) (Fin n) (mixedSpace K) => X a b := continuous_id.matrix_elem a b
  exact (continuous_apply i).comp (hc.comp h)

private theorem continuous_entC_symm {c : mixedSpace K ≃+* (ι → ℂ)} (hs : Continuous c.symm) (n : ℕ) :
    Continuous (entC c n).symm := by
  change Continuous fun Y : ι → Matrix (Fin n) (Fin n) ℂ =>
    (Matrix.of fun a b => c.symm fun i => Y i a b : Matrix (Fin n) (Fin n) (mixedSpace K))
  refine continuous_matrix fun a b => ?_
  exact hs.comp (continuous_pi fun i => ((continuous_apply i).matrix_elem a b))

private def psiC (c : mixedSpace K ≃+* (ι → ℂ)) (hc : Continuous c) (hs : Continuous c.symm) (n : ℕ) :
    archGroup K n ≃ₜ* (ι → GL (Fin n) ℂ) :=
  (ContinuousMulEquiv.trans
    { toMulEquiv := Subgroup.topEquiv
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
    (unitsCongr (entC c n).toMulEquiv (continuous_entC hc n) (continuous_entC_symm hs n))).trans
    ContinuousMulEquiv.piUnits

private theorem psiC_val (c : mixedSpace K ≃+* (ι → ℂ)) (hc : Continuous c) (hs : Continuous c.symm) (n : ℕ)
    (g : archGroup K n) (i : ι) :
    ((psiC c hc hs n g i : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = entC c n ((g : (ArchMatrix K n)ˣ) : ArchMatrix K n) i := rfl

private theorem continuous_toUnits (n : ℕ) :
    Continuous fun u : unitaryGroup (Fin n) ℂ => (Unitary.toUnits u : GL (Fin n) ℂ) := by
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  exact continuous_star.comp continuous_subtype_val

private def mkCo (c : mixedSpace K ≃+* (ι → ℂ)) (hc : Continuous c) (hs : Continuous c.symm)
    (hu : ∀ (n : ℕ) (g : archGroup K n), g ∈ archCompact K n ↔
      ∀ i, entC c n ((g : (ArchMatrix K n)ˣ) : ArchMatrix K n) i ∈ unitaryGroup (Fin n) ℂ) : Co K ι where
  c := c
  Ψ := psiC c hc hs
  Φ n :=
    { toFun := fun k i => ⟨_, (hu n k.1).1 k.2 i⟩
      invFun := fun u => ⟨(psiC c hc hs n).symm fun i => Unitary.toUnits (u i), (hu n _).2 fun i => by
        rw [← psiC_val c hc hs, ContinuousMulEquiv.apply_symm_apply]
        exact (u i).2⟩
      left_inv := fun k => by
        refine Subtype.ext ?_
        change (psiC c hc hs n).symm _ = k.1
        rw [ContinuousMulEquiv.symm_apply_eq]
        funext i
        exact Units.ext rfl
      right_inv := fun u => by
        funext i
        refine Subtype.ext ?_
        change ((psiC c hc hs n ((psiC c hc hs n).symm fun i => Unitary.toUnits (u i)) i : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = _
        rw [ContinuousMulEquiv.apply_symm_apply]
        rfl
      map_mul' := fun k l => by
        funext i
        refine Subtype.ext ?_
        change ((psiC c hc hs n (k.1 * l.1) i : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = _
        rw [map_mul]
        rfl
      continuous_toFun := by
        refine continuous_pi fun i => Continuous.subtype_mk ?_ _
        exact Units.continuous_val.comp ((continuous_apply i).comp
          ((psiC c hc hs n).continuous.comp continuous_subtype_val))
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        exact (psiC c hc hs n).symm.continuous.comp
          (continuous_pi fun i => (continuous_toUnits n).comp (continuous_apply i)) }
  Ψ_val n g i a b := rfl
  Φ_val n k i := rfl

end mk

section co

private def cF (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] : mixedSpace F ≃+* (InfinitePlace F → ℂ) where
  toFun a w := a.2 ⟨w, IsTotallyComplex.isComplex w⟩
  invFun z := (fun v => absurd v.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v.1)), fun v => z v.1)
  left_inv a := Prod.ext (funext fun v => absurd v.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v.1))) rfl
  right_inv z := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]

private theorem continuous_cF : Continuous (cF F) := by
  refine continuous_pi fun w => ?_
  exact continuous_complexComp ⟨w, IsTotallyComplex.isComplex w⟩

private theorem continuous_cF_symm : Continuous (cF F).symm := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => continuous_apply _)
  exact absurd v.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v.1))

private theorem unitary_cF (n : ℕ) (g : archGroup F n) : g ∈ archCompact F n ↔
    ∀ w, entC (cF F) n ((g : (ArchMatrix F n)ˣ) : ArchMatrix F n) w ∈ unitaryGroup (Fin n) ℂ := by
  constructor
  · intro h w
    exact complexCompM_mem_unitaryGroup h ⟨w, IsTotallyComplex.isComplex w⟩
  · intro h
    exact mem_archCompact_of_unitary g
      (fun v => absurd v.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v.1))) fun v => h v.1

private theorem continuous_psi (K : Type) [Field K] [NumberField K] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  have e : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace K) = ⇑(GroundTheory.Global.homeomorphMixedSpace K) :=
    funext fun x => (GroundTheory.Global.homeomorphMixedSpace_apply K x).symm
  rw [e]
  exact (GroundTheory.Global.homeomorphMixedSpace K).continuous

private theorem continuous_psi_symm (K : Type) [Field K] [NumberField K] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  have e : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace K).symm = ⇑(GroundTheory.Global.homeomorphMixedSpace K).symm := by
    funext x
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
    rw [RingEquiv.apply_symm_apply, ← GroundTheory.Global.homeomorphMixedSpace_apply, Homeomorph.apply_symm_apply]
  rw [e]
  exact (GroundTheory.Global.homeomorphMixedSpace K).symm.continuous

variable {F} {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E ≃ₐ[F] E}

private def unc (κ ι : Type) : (κ → ι → ℂ) ≃+* (κ × ι → ℂ) where
  toFun f p := f p.1 p.2
  invFun z s u := z (s, u)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private def cE (D : InfD σ 1) : mixedSpace E ≃+* (Fin 2 × InfinitePlace F → ℂ) :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm.trans D.e).trans
    ((RingEquiv.piCongrRight fun _ : Fin (1 + 1) => (InfiniteAdeleRing.ringEquiv_mixedSpace F).trans (cF F)).trans
      (unc (Fin (1 + 1)) (InfinitePlace F)))

private theorem continuous_cE (D : InfD σ 1) : Continuous (cE D) := by
  refine continuous_pi fun p => ?_
  exact (continuous_apply p.2).comp ((continuous_cF F).comp ((continuous_psi F).comp
    ((continuous_apply p.1).comp (D.cont.comp (continuous_psi_symm E)))))

private theorem continuous_cE_symm (D : InfD σ 1) : Continuous (cE D).symm := by
  refine (continuous_psi E).comp (D.cont_symm.comp (continuous_pi fun s => ?_))
  exact (continuous_psi_symm F).comp ((continuous_cF_symm F).comp
    (continuous_pi fun u => continuous_apply (s, u)))

private theorem ent_comp (D : InfD σ 1) (n : ℕ) (g : archGroup E n) (s : Fin 2) (u : InfinitePlace F) :
    entC (cF F) n (((compA D n s g : archGroup F n) : (ArchMatrix F n)ˣ) : ArchMatrix F n) u =
      entC (cE D) n ((g : (ArchMatrix E n)ˣ) : ArchMatrix E n) (s, u) := rfl

private theorem unitary_cE (D : InfD σ 1) (n : ℕ) (g : archGroup E n) : g ∈ archCompact E n ↔
    ∀ p, entC (cE D) n ((g : (ArchMatrix E n)ˣ) : ArchMatrix E n) p ∈ unitaryGroup (Fin n) ℂ := by
  rw [(UpperTheory.ConvolutionTheory.L1.positionOf F E σ 1 D).2 n g]
  constructor
  · rintro h ⟨s, u⟩
    rw [← ent_comp]
    exact (unitary_cF F n _).1 (h s) u
  · intro h s
    refine (unitary_cF F n _).2 fun u => ?_
    rw [ent_comp D n g s u]
    exact h (s, u)

end co

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E] (σ : E ≃ₐ[F] E) (D : InfD σ 1), ∃ (CF : Co F (InfinitePlace F)) (CE : Co E (Fin 2 × InfinitePlace F)),
      ∀ n (g : archGroup E n) s u, CE.Ψ n g (s, u) = CF.Ψ n (compA D n s g) u := by
  intro F E _ _ _ _ _ _ _ σ D
  refine ⟨mkCo (cF F) (continuous_cF F) (continuous_cF_symm F) (unitary_cF F),
    mkCo (cE D) (continuous_cE D) (continuous_cE_symm D) (unitary_cE D), fun n g s u => ?_⟩
  exact Units.ext (ent_comp D n g s u).symm
