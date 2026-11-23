import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsB

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.NormSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ColLatRepSPf

theorem basicNotions_bridge_star : Formalism.BasicNotions.bridge_star := by
  intro R H x
  have := H.isCMField_hostE
  apply H.φ₀.injective
  change H.φ₀ (NumberField.IsCMField.complexConj H.E x) = H.φ₀ (H.conj x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj]
  exact (Formalism.HC.HostAx.conjE_apply H.toHostAx H.φ₀ x).symm

section Mat

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def matL (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) D.host.E) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  X.bas.equivFun.symm.toLinearMap ∘ₗ Matrix.toLin' A ∘ₗ X.bas.equivFun.toLinearMap

theorem matL_repr (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) D.host.E) (y : (VS D).V) :
    X.bas.equivFun (matL X A y) = A *ᵥ X.bas.equivFun y := by
  simp only [matL, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    Matrix.toLin'_apply]

theorem matL_mul (A B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) D.host.E) :
    matL X (A * B) = matL X A ∘ₗ matL X B := by
  apply LinearMap.ext
  intro y
  apply X.bas.equivFun.injective
  rw [LinearMap.comp_apply, matL_repr, matL_repr, matL_repr, Matrix.mulVec_mulVec]

theorem matL_one : matL X 1 = LinearMap.id := by
  apply LinearMap.ext
  intro y
  apply X.bas.equivFun.injective
  rw [matL_repr, Matrix.one_mulVec, LinearMap.id_apply]

abbrev mapM : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E →+* Matrix (Fin X.B.I.n) (Fin X.B.I.n) D.host.E :=
  (X.ιE : X.B.I.E →+* D.host.E).mapMatrix

def matE (M : GL (Fin X.B.I.n) X.B.I.E) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (matL X (mapM X (M : Matrix _ _ _)))
    (matL X (mapM X ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix _ _ _)))
    (by rw [← matL_mul, ← map_mul, M.mul_inv, map_one, matL_one])
    (by rw [← matL_mul, ← map_mul, M.inv_mul, map_one, matL_one])

theorem matE_repr (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.bas.equivFun (matE X M y) = mapM X (M : Matrix _ _ _) *ᵥ X.bas.equivFun y :=
  matL_repr X _ y

theorem matE_crd (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (matE X M y) = (M : Matrix _ _ _) *ᵥ X.crd y := by
  funext i
  simp only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf]
  rw [← Module.Basis.equivFun_apply, matE_repr]
  simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, map_sum, map_mul,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply, Module.Basis.equivFun_apply]
  rfl

theorem matE_incl (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    incl X.B.I (X.crd (matE X M y)) =
      (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ incl X.B.I (X.crd y) := by
  rw [matE_crd]
  funext i
  simp only [Formalism.L2.SG.HidaSetting.incl, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

theorem hT_expand (x y : (VS D).V) :
    (VS D).hT x y =
      ∑ i, ∑ j, star (X.bas.equivFun x i) * (X.bas.equivFun y j * (VS D).hT (X.bas i) (X.bas j)) := by
  conv_lhs => rw [← X.bas.sum_equivFun x, ← X.bas.sum_equivFun y]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, starRingEnd_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [RingHom.id_apply]
  ring

theorem qform (a c : Fin X.B.I.n → D.host.E) :
    ∑ i, ∑ j, star (a i) * (c j * X.ιE (X.B.I.J i j)) = star a ⬝ᵥ (mapM X X.B.I.J *ᵥ c) := by
  simp only [dotProduct, Matrix.mulVec, RingHom.mapMatrix_apply, Matrix.map_apply, Pi.star_apply,
    Finset.mul_sum, RingEquiv.coe_toRingHom]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

theorem mapM_unitary (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    (mapM X (M : Matrix _ _ _))ᴴ * mapM X X.B.I.J * mapM X (M : Matrix _ _ _) = mapM X X.B.I.J := by
  have hM' : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix _ _ _) * X.B.I.J * (M : Matrix _ _ _) =
      X.B.I.J := hM
  have hc : mapM X (Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix _ _ _)) =
      (mapM X (M : Matrix _ _ _))ᴴ := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply,
      Matrix.conjTranspose_apply, starRingEnd_apply, RingEquiv.coe_toRingHom]
    rw [X.ιE_conj]
    exact (basicNotions_bridge_star _ _ _).symm
  have h := congrArg (mapM X) hM'
  rw [map_mul, map_mul, hc] at h
  exact h

theorem matE_isom (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    matE X M ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  have key : ∀ a b : (VS D).V,
      (VS D).hT a b = star (X.bas.equivFun a) ⬝ᵥ (mapM X X.B.I.J *ᵥ X.bas.equivFun b) := by
    intro a b
    rw [hT_expand X, ← qform X]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [X.J_eq]
  show ∀ x y, (VS D).hT (matE X M x) (matE X M y) = (VS D).hT x y
  intro x y
  rw [key, key, matE_repr, matE_repr, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mapM_unitary X M hM]

theorem af_nontriv (F : Type) [Field F] [NumberField F] : Nontrivial (Af F) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  have hne : M ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨M, hM.isPrime, hne⟩
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h1 := congrArg (fun x : Af F => x v) h
  first
  | exact one_ne_zero h1
  | (simp only [RestrictedProduct.one_apply, RestrictedProduct.zero_apply] at h1
     exact one_ne_zero h1)

theorem inclE_inj :
    Function.Injective (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) : X.B.I.E → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
  haveI := af_nontriv X.B.I.F
  exact Algebra.TensorProduct.includeLeft_injective (S := X.B.I.F) (RingHom.injective _)

theorem gamIsom (u : D.what₂.Word) (g : Gam X u) :
    ∃ γ : (VS D).V ≃ₗ[D.host.E] (VS D).V, γ ∈ stabF D (X.Fu u) ∧
      ∀ y, incl X.B.I (X.crd (γ y)) = X.B.I.fmat (g : X.B.I.GA).2 *ᵥ incl X.B.I (X.crd y) := by
  obtain ⟨hGF, hH⟩ := Subgroup.mem_inf.1 g.2
  have hGF' : (g : X.B.I.GA) ∈ X.B.I.GFset := hGF
  obtain ⟨M, hM, -, hf⟩ := hGF'
  have hfin := (Subgroup.mem_prod.1 hH).2
  have hincl : ∀ y, incl X.B.I (X.crd (matE X M y)) = X.B.I.fmat (g : X.B.I.GA).2 *ᵥ incl X.B.I (X.crd y) :=
    fun y => by rw [matE_incl, hf]
  have hfix : ∀ y, X.crd y ∈ fixSet X u → matE X M y = y := by
    intro y hy
    have h1 : incl X.B.I (X.crd (matE X M y)) = incl X.B.I (X.crd y) := by
      rw [hincl]
      exact hfin _ hy
    apply X.bas.equivFun.injective
    funext i
    exact X.ιE.symm.injective (inclE_inj X (congrFun h1 i))
  refine ⟨matE X M, ⟨matE_isom X M hM, fun j => ?_, ?_⟩, hincl⟩
  · unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro a _
    rw [X.Fu_e u]
    exact hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))
  · show matE X M (X.Fu u).z = (X.Fu u).z
    rw [X.flagZVector u]
    exact hfix _ (Or.inr rfl)

theorem one_mem_stabF (u : D.what₂.Word) : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D (X.Fu u) :=
  ⟨(Formalism.HermitianLatticesTheory.isom _).one_mem, fun j => Submodule.map_id _, rfl⟩

theorem gmap_one (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) Λ = Λ := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

theorem fmat_mul (a b : X.B.I.Gf) : X.B.I.fmat (a * b) = X.B.I.fmat a * X.B.I.fmat b := rfl

theorem fmat_one : X.B.I.fmat 1 = 1 := by
  rfl

theorem fmat_inv_mul (a : X.B.I.Gf) : X.B.I.fmat a⁻¹ * X.B.I.fmat a = 1 := by
  rw [← fmat_mul, inv_mul_cancel, fmat_one]

theorem kset_iff {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kset) (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    X.B.I.fmat k *ᵥ w ∈ X.B.I.Lf ↔ w ∈ X.B.I.Lf :=
  (hk w).symm

theorem kset_inv_iff {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kset) (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    X.B.I.fmat k⁻¹ *ᵥ w ∈ X.B.I.Lf ↔ w ∈ X.B.I.Lf := by
  exact ((Formalism.UG.stabGL X.B.I.Lf).inv_mem hk w).symm

end Mat

end ColLatRepSPf

open ColLatRepSPf

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u : D.what₂.Word}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem column_lattice_representatives (cs : ColSys X u what₂) (hK : X.LevelSubgroupCharacter) (hR : IsRowReps D (X.Fu u) what₂) :
    ColLatRepS cs hK := by
  intro q h ρ γ κ hc hh
  obtain ⟨g, hg, hgc⟩ := gamIsom X u γ

  have h1 : ∀ y, y ∈ q.1 ↔
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf := by
    intro y
    have e := cs.lat_eq (cs.base q.1) y
    rw [cs.base_lam q.1 q.2] at e
    rw [e]
    have ec : ((cs.h (cs.base q.1) : X.B.I.Gf) * X.xu u)⁻¹ =
        colDS (cs.h (cs.base q.1)) h * ((h : X.B.I.Gf) * X.xu u)⁻¹ := by
      unfold colDS
      group
    rw [ec, fmat_mul, ← Matrix.mulVec_mulVec]
    exact kset_iff X hc _

  have hk : (X.xu u)⁻¹ * (κ : X.B.I.Gf) * X.xu u ∈ X.B.I.Kset := (κ.2 : _ ∈ X.K2).1
  have hginv : ∀ y, X.B.I.fmat ((γ : X.B.I.GA).2)⁻¹ *ᵥ incl X.B.I (X.crd y) =
      incl X.B.I (X.crd (g.symm y)) := by
    intro y
    have h2 := hgc (g.symm y)
    rw [g.apply_symm_apply] at h2
    rw [h2, Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec]
  have egrp : ((h : X.B.I.Gf) * X.xu u)⁻¹ =
      ((X.xu u)⁻¹ * (κ : X.B.I.Gf) * X.xu u)⁻¹ *
        (((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ((γ : X.B.I.GA).2)⁻¹) := by
    rw [hh]
    show ((γ : X.B.I.GA).2 * (cs.h ρ : X.B.I.Gf) * (κ : X.B.I.Gf) * X.xu u)⁻¹ = _
    group

  have h2 : ∀ y, y ∈ Formalism.HermitianLatticesTheory.gmap g (cs.lamOf ρ) ↔ y ∈ q.1 := by
    intro y
    have hmap : y ∈ Formalism.HermitianLatticesTheory.gmap g (cs.lamOf ρ) ↔ g.symm y ∈ cs.lamOf ρ := by
      simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hy
        exact ⟨g.symm y, hy, by simp⟩
    rw [hmap, cs.lat_eq ρ, h1, egrp, fmat_mul, ← Matrix.mulVec_mulVec, kset_inv_iff X hk, fmat_mul,
      ← Matrix.mulVec_mulVec, hginv]
  have heq : Formalism.HermitianLatticesTheory.gmap g (cs.lamOf ρ) = q.1 := by
    ext y
    exact h2 y
  exact (hR.2 q.1 (hR.1 q.1 q.2)).unique ⟨cs.lam_mem ρ, g, hg, heq⟩
    ⟨q.2, 1, one_mem_stabF X u, gmap_one q.1⟩

end Formalism.L2.SG.Pf.NormSteps
