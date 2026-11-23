import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdelicSplit
import GroundTheory.HeightsAndTheta.Theta.RealPlace

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField NumberField.InfinitePlace GroundTheory.Automorphic GroundTheory.Heights₂.Theta Module Matrix
  Topology TensorProduct NumberField.InfinitePlace.Completion

open scoped NumberField.AdeleRing

noncomputable section

attribute [local instance] tensorTopology isModuleTopology_tensor isTopologicalRing_tensor

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]

theorem isNonsplitAt_of_isTotallyComplex (u : InfinitePlace F) : IsNonsplitAt E u := by
  have hu : u.IsReal := IsTotallyReal.isReal u
  rw [isNonsplitAt_iff hu]
  by_contra hnn
  push Not at hnn
  let ρ := ringEquivRealOfIsReal hu
  letI : Algebra u.Completion ℝ := (ρ : u.Completion →+* ℝ).toAlgebra
  have hs : Real.sqrt (ρ (algebraMap F u.Completion (quadD F E u))) *
      Real.sqrt (ρ (algebraMap F u.Completion (quadD F E u))) =
      algebraMap F u.Completion (quadD F E u) • (1 : ℝ) +
        (0 : u.Completion) • Real.sqrt (ρ (algebraMap F u.Completion (quadD F E u))) := by
    have hnn' : 0 ≤ ρ (algebraMap F u.Completion (quadD F E u)) := hnn
    rw [Real.mul_self_sqrt hnn', zero_smul, add_zero, Algebra.smul_def, mul_one]
    rfl
  let f := QuadraticAlgebra.lift ⟨_, hs⟩
  let σ : E →+* ℂ := Complex.ofRealHom.comp ((f : _ →+* ℝ).comp
    ((realPlaceTensorEquiv (E := E) (w := u)).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : E →ₐ[F] u.Completion ⊗[F] E).toRingHom))
  apply IsTotallyComplex.complexEmbedding_not_isReal σ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp [σ, ComplexEmbedding.conjugate_coe_eq, Complex.conj_ofReal]

def placeEmbedding (u : InfinitePlace F) : E →+* ℂ :=
  (realPlaceEquiv (IsTotallyReal.isReal u)
      (isNonsplitAt_of_isTotallyComplex (E := E) u)).toRingHom.comp
    (Algebra.TensorProduct.includeRight : E →ₐ[F] u.Completion ⊗[F] E).toRingHom

theorem norm_placeEmbedding_algebraMap (u : InfinitePlace F) (x : F) :
    ‖placeEmbedding (E := E) u (algebraMap F E x)‖ = u x := by
  have hu := IsTotallyReal.isReal u
  simp only [placeEmbedding, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.toRingHom_eq_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply F u.Completion (u.Completion ⊗[F] E),
    realPlaceEquiv_algebraMap,
    Complex.norm_real, ringEquivRealOfIsReal_apply]
  erw [extensionEmbeddingOfIsReal_coe hu]
  exact norm_embedding_of_isReal hu x

def placeAbove (u : InfinitePlace F) : InfinitePlace E :=
  InfinitePlace.mk (placeEmbedding u)

theorem comap_placeAbove (u : InfinitePlace F) :
    (placeAbove (E := E) u).comap (algebraMap F E) = u := by
  apply InfinitePlace.ext
  intro x
  rw [placeAbove, comap_mk, InfinitePlace.apply, RingHom.comp_apply]
  exact norm_placeEmbedding_algebraMap u x

theorem placeAbove_injective : Function.Injective (placeAbove (F := F) (E := E)) := by
  intro a b hab
  rw [← comap_placeAbove (E := E) a, ← comap_placeAbove (E := E) b, hab]

theorem card_infinitePlace :
    Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace E) := by
  have h1 := card_add_two_mul_card_eq_rank F
  have h2 := card_add_two_mul_card_eq_rank E
  have h3 := Module.finrank_mul_finrank ℚ F E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two F E] at h3
  have h4 : nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
  have h5 : nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

def placeAboveEquiv : InfinitePlace F ≃ InfinitePlace E :=
  Equiv.ofBijective placeAbove
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨placeAbove_injective, card_infinitePlace⟩)

theorem placeAboveEquiv_apply (u : InfinitePlace F) :
    placeAboveEquiv (E := E) u = placeAbove u := rfl

theorem exists_completionTensorEquiv (u : InfinitePlace F) :
    ∃ Ψ : u.Completion ⊗[F] E ≃+* ℂ, Continuous Ψ ∧ Continuous Ψ.symm ∧
      (∀ z, Ψ (conjBase F E u.Completion z) = starRingEnd ℂ (Ψ z)) ∧
      ∀ e, Ψ (Algebra.TensorProduct.includeRight e) = (placeAbove u).embedding e := by
  have hu := IsTotallyReal.isReal u
  have hE := isNonsplitAt_of_isTotallyComplex (E := E) u
  rcases embedding_mk_eq (placeEmbedding (E := E) u) with h | h
  · refine ⟨realPlaceEquiv hu hE, continuous_realPlaceEquiv hu hE,
      continuous_realPlaceEquiv_symm hu hE, realPlaceEquiv_conjBase hu hE, fun e => ?_⟩
    rw [placeAbove, h]
    rfl
  · refine ⟨(realPlaceEquiv hu hE).trans (starRingAut : RingAut ℂ), ?_, ?_, fun z => ?_,
      fun e => ?_⟩
    · exact Complex.continuous_conj.comp (continuous_realPlaceEquiv hu hE)
    · refine ((continuous_realPlaceEquiv_symm hu hE).comp Complex.continuous_conj).congr fun z => ?_
      rfl
    · simp [realPlaceEquiv_conjBase]
    · rw [placeAbove, h, ComplexEmbedding.conjugate_coe_eq]
      rfl

def completionTensorEquiv (u : InfinitePlace F) : u.Completion ⊗[F] E ≃+* ℂ :=
  (exists_completionTensorEquiv u).choose

theorem continuous_completionTensorEquiv (u : InfinitePlace F) :
    Continuous (completionTensorEquiv (E := E) u) :=
  (exists_completionTensorEquiv u).choose_spec.1

theorem continuous_completionTensorEquiv_symm (u : InfinitePlace F) :
    Continuous (completionTensorEquiv (E := E) u).symm :=
  (exists_completionTensorEquiv u).choose_spec.2.1

theorem completionTensorEquiv_conjBase (u : InfinitePlace F) (z : u.Completion ⊗[F] E) :
    completionTensorEquiv u (conjBase F E u.Completion z) =
      starRingEnd ℂ (completionTensorEquiv u z) :=
  (exists_completionTensorEquiv u).choose_spec.2.2.1 z

theorem completionTensorEquiv_includeRight (u : InfinitePlace F) (e : E) :
    completionTensorEquiv u (Algebra.TensorProduct.includeRight e) = (placeAbove u).embedding e :=
  (exists_completionTensorEquiv u).choose_spec.2.2.2 e

section Unitary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

def unitaryPointsComplexEquiv {R : Type*} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (H : Matrix ι ι E) (Ψ : R ⊗[F] E ≃+* ℂ) (hc : Continuous Ψ)
    (hc' : Continuous Ψ.symm) (hs : ∀ z, Ψ (conjBase F E R z) = starRingEnd ℂ (Ψ z))
    {H' : Matrix ι ι ℂ}
    (hH : (H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E)).map Ψ = H') :
    unitaryPoints F E H R ≃ₜ* unitaryGroupMatrix (starRingEnd ℂ) H' where
  toMulEquiv := unitaryGroupMatrixCongr Ψ hs hH
  continuous_toFun := by
    have hv : Continuous fun g : unitaryPoints F E H R =>
        ((g : GL ι (R ⊗[F] E)) : Matrix ι ι (R ⊗[F] E)) :=
      Units.continuous_val.comp continuous_subtype_val
    have h1 : Continuous fun g : unitaryPoints F E H R =>
        ((g : GL ι (R ⊗[F] E)) : Matrix ι ι (R ⊗[F] E)).map Ψ :=
      hv.matrix_map hc
    have h2 : Continuous fun g : unitaryPoints F E H R =>
        ((((g : GL ι (R ⊗[F] E))⁻¹ : GL ι (R ⊗[F] E))) : Matrix ι ι (R ⊗[F] E)).map Ψ :=
      ((Units.continuous_coe_inv.comp continuous_subtype_val)).matrix_map hc
    exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨h1, h2⟩) _
  continuous_invFun := by
    have h1 : Continuous fun g : unitaryGroupMatrix (starRingEnd ℂ) H' =>
        ((g : GL ι ℂ) : Matrix ι ι ℂ).map Ψ.symm :=
      (Units.continuous_val.comp continuous_subtype_val).matrix_map hc'
    have h2 : Continuous fun g : unitaryGroupMatrix (starRingEnd ℂ) H' =>
        ((((g : GL ι ℂ))⁻¹ : GL ι ℂ) : Matrix ι ι ℂ).map Ψ.symm :=
      (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map hc'
    exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨h1, h2⟩) _

variable {W : Type*} [AddCommGroup W] [Module E W]

theorem map_completionTensorEquiv_gram (h : HermitianForm F E W) (v : Basis ι E W)
    (u : InfinitePlace F) :
    ((gram h.toSesq v).map (Algebra.TensorProduct.includeRight : E →ₐ[F] u.Completion ⊗[F] E)).map
      (completionTensorEquiv u) = gramAt h v (placeAboveEquiv u) := by
  ext i j
  simp only [Matrix.map_apply, gramAt, placeAboveEquiv_apply]
  exact completionTensorEquiv_includeRight u _

def unitaryPointsPlaceEquiv (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) :
    unitaryPoints F E (gram h.toSesq v) ((placeAboveEquiv (F := F) (E := E)).symm w).Completion ≃ₜ*
      unitaryGroupMatrix (starRingEnd ℂ) (gramAt h v w) :=
  unitaryPointsComplexEquiv (gram h.toSesq v)
    (completionTensorEquiv ((placeAboveEquiv (F := F) (E := E)).symm w))
    (continuous_completionTensorEquiv _) (continuous_completionTensorEquiv_symm _)
    (completionTensorEquiv_conjBase _)
    (by rw [map_completionTensorEquiv_gram, Equiv.apply_symm_apply])

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

def piUnitaryEquivArch (h : HermitianForm F E W) (v : Basis ι E W) :
    (∀ w : InfinitePlace E, unitaryGroupMatrix (starRingEnd ℂ) (gramAt h v w)) ≃ₜ*
      archUnitary h v where
  toFun g := ⟨fun w => (g w : GL ι ℂ), (Subgroup.mem_pi _).2 fun w _ => (g w).2⟩
  invFun g := fun w => ⟨g.1 w, (Subgroup.mem_pi _).1 g.2 w (Set.mem_univ _)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_pi fun w => continuous_subtype_val.comp (continuous_apply w)) _
  continuous_invFun := continuous_pi fun w =>
    Continuous.subtype_mk ((continuous_apply w).comp continuous_subtype_val) _

def piCongrRightEquiv {α : Type*} {X Y : α → Type*} [∀ a, Mul (X a)] [∀ a, Mul (Y a)]
    [∀ a, TopologicalSpace (X a)] [∀ a, TopologicalSpace (Y a)] (f : ∀ a, X a ≃ₜ* Y a) :
    (∀ a, X a) ≃ₜ* ∀ a, Y a where
  toFun g a := f a (g a)
  invFun g a := (f a).symm (g a)
  left_inv g := funext fun a => (f a).symm_apply_apply (g a)
  right_inv g := funext fun a => (f a).apply_symm_apply (g a)
  map_mul' g g' := funext fun a => map_mul (f a) (g a) (g' a)
  continuous_toFun := continuous_pi fun a => (f a).continuous.comp (continuous_apply a)
  continuous_invFun := continuous_pi fun a => (f a).symm.continuous.comp (continuous_apply a)

def piReindexEquiv {α β : Type*} (e : α ≃ β) (Y : β → Type*) [∀ b, Group (Y b)]
    [∀ b, TopologicalSpace (Y b)] : (∀ b, Y b) ≃ₜ* ∀ a, Y (e a) where
  toFun g a := g (e a)
  invFun := Homeomorph.piCongrLeft e
  left_inv g := (Homeomorph.piCongrLeft e).apply_symm_apply g
  right_inv z := (Homeomorph.piCongrLeft e).symm_apply_apply z
  map_mul' _ _ := rfl
  continuous_toFun := (Homeomorph.piCongrLeft e).symm.continuous
  continuous_invFun := (Homeomorph.piCongrLeft e).continuous

def infiniteUnitaryEquiv (h : HermitianForm F E W) (v : Basis ι E W) :
    unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ≃ₜ* archUnitary h v :=
  ((unitaryCongr (gram h.toSesq v) (infiniteAdeleRingEquivPi F) (by exact continuous_id)
      (by exact continuous_id)).trans
    ((unitaryPiEquiv F (gram h.toSesq v) (fun u : InfinitePlace F => u.Completion)
      (isUnit_det_gram h v)).trans
    (piReindexEquiv placeAboveEquiv.symm _))).trans
    ((piCongrRightEquiv (unitaryPointsPlaceEquiv h v)).trans (piUnitaryEquivArch h v))

end Unitary

section Compat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [AddCommGroup W] [Module E W]

theorem adeleSplit_hermitianDiagonal_fst (h : HermitianForm F E W) (v : Basis ι E W)
    (γ : h.unitaryGroup) (i j : ι) :
    (((adeleSplit h v (hermitianDiagonal h v γ)).1 : GL ι (InfiniteAdeleRing F ⊗[F] E)) :
      Matrix ι ι (InfiniteAdeleRing F ⊗[F] E)) i j =
      (1 : InfiniteAdeleRing F) ⊗ₜ
        ((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E) i j := by
  change tensorMap E
      (AlgHom.fst F (InfiniteAdeleRing F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
    (tensorMap E (adeleRingEquivProd F : 𝔸[F] →ₐ[F] _) (tensorMap E (Algebra.ofId F 𝔸[F])
      ((Algebra.TensorProduct.lid F E).symm
        (((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E) i j)))) = _
  rw [Algebra.TensorProduct.lid_symm_apply, tensorMap_tmul, tensorMap_tmul, tensorMap_tmul, map_one,
    map_one, map_one]

theorem infiniteUnitaryEquiv_hermitianDiagonal (h : HermitianForm F E W) (v : Basis ι E W)
    (γ : h.unitaryGroup) :
    infiniteUnitaryEquiv h v (adeleSplit h v (hermitianDiagonal h v γ)).1 = archEmbed h v γ := by
  apply Subtype.ext
  funext w
  apply Units.ext
  ext i j
  have hx := adeleSplit_hermitianDiagonal_fst h v γ i j
  change completionTensorEquiv ((placeAboveEquiv (F := F) (E := E)).symm w)
      (tensorMap E (Pi.evalAlgHom F (fun u : InfinitePlace F => u.Completion)
          ((placeAboveEquiv (F := F) (E := E)).symm w))
        (tensorMap E (infiniteAdeleRingEquivPi F : InfiniteAdeleRing F →ₐ[F] _)
          ((((adeleSplit h v (hermitianDiagonal h v γ)).1 : GL ι (InfiniteAdeleRing F ⊗[F] E)) :
            Matrix ι ι (InfiniteAdeleRing F ⊗[F] E)) i j))) =
    w.embedding (((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E) i j)
  rw [hx, tensorMap_tmul, tensorMap_tmul, map_one, map_one,
    ← Algebra.TensorProduct.includeRight_apply, completionTensorEquiv_includeRight,
    ← placeAboveEquiv_apply, Equiv.apply_symm_apply]

end Compat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [AddCommGroup W] [Module E W]

theorem ArchimedeanUnitaryEquiv.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchimedeanUnitaryEquiv.Statement h v :=
  ⟨infiniteUnitaryEquiv h v, infiniteUnitaryEquiv_hermitianDiagonal h v⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
