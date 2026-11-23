import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.ChiProofs
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.CuspFormLaws
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.RightInvariantOfCovolume
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite

noncomputable section

namespace GlobalTheory.CoreLawsCompare

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix

section Gen

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ} (V : ConjugateFieldNorm.HSpace E r)

theorem hermA_eq (A : Type) [CommRing A] [Algebra F A] (x y : Fin r → A ⊗[F] E) :
    ConjugateFieldNorm.hermA F A V x y = Formalism.UG.hform (sigR A (ConjugateFieldNorm.cjF F)) (JR A V.Gmᵀ) y x := by
  unfold ConjugateFieldNorm.hermA Formalism.UG.hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  change x a * inclR A (V.Gm a b) * sigR A (ConjugateFieldNorm.cjF F) (y b) = sigR A (ConjugateFieldNorm.cjF F) (y b) * inclR A (V.Gm a b) * x a
  ring

theorem mem_UA_iff (A : Type) [CommRing A] [Algebra F A] (g : GL (Fin r) (A ⊗[F] E)) :
    g ∈ ConjugateFieldNorm.UA F A V ↔ g ∈ HR A (ConjugateFieldNorm.cjF F) V.Gmᵀ := by
  change (∀ x y, ConjugateFieldNorm.hermA F A V (g.val.mulVec x) (g.val.mulVec y) = ConjugateFieldNorm.hermA F A V x y) ↔
    Formalism.UG.cT _ g.val * _ * g.val = _
  simp only [hermA_eq, Formalism.UG.P.hform_mulVec]
  constructor
  · intro h
    ext i j
    have := h (Pi.single j 1) (Pi.single i 1)
    rwa [Formalism.UG.P.hform_single, Formalism.UG.P.hform_single] at this
  · intro h x y
    rw [h]

def crdA (A : Type) [CommRing A] [Algebra F A] (φ : E →ₗ[F] F) : A ⊗[F] E →ₗ[A] A :=
  (TensorProduct.AlgebraTensorModule.rid F A A).toLinearMap ∘ₗ LinearMap.baseChange A φ

omit [NumberField F] [IsTotallyReal F] [NumberField E] [IsCMField E] in
theorem crdA_eq (A : Type) [CommRing A] [Algebra F A] (φ : E →ₗ[F] F) (z : A ⊗[F] E) :
    TensorProduct.rid F A (LinearMap.lTensor A φ z) = crdA A φ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [crdA]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [IsTotallyReal F] [IsCMField E] in
theorem sum_crdA (A : Type) [CommRing A] [Algebra F A] (z : A ⊗[F] E) :
    ∑ i, crdA A ((Module.finBasis F E).coord i) z • ((1 : A) ⊗ₜ[F] Module.finBasis F E i) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    conv_rhs => rw [← (Module.finBasis F E).sum_repr x, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp [crdA]
  | add x y hx hy => simp only [map_add, add_smul, Finset.sum_add_distrib, hx, hy]

omit [IsTotallyReal F] [IsCMField E] in
theorem continuous_iff_crdA (A : Type) [CommRing A] [Algebra F A] [TopologicalSpace A] [IsTopologicalRing A]
    {X : Type} [TopologicalSpace X] (f : X → A ⊗[F] E) :
    Continuous f ↔ ∀ φ : E →ₗ[F] F, Continuous fun x => crdA A φ (f x) := by
  have : IsModuleTopology A (A ⊗[F] E) := ⟨rfl⟩
  have := IsModuleTopology.toContinuousAdd A (A ⊗[F] E)
  have := IsModuleTopology.toContinuousSMul (R := A) (A := A ⊗[F] E)
  refine ⟨fun h φ => (IsModuleTopology.continuous_of_linearMap (crdA A φ)).comp h, fun h => ?_⟩
  have : f = fun x => ∑ i, crdA A ((Module.finBasis F E).coord i) (f x) • ((1 : A) ⊗ₜ[F] Module.finBasis F E i) :=
    funext fun x => (sum_crdA A (f x)).symm
  rw [this]
  exact continuous_finsetSum _ fun i _ => (h _).fun_smul continuous_const

theorem continuous_sigR (A : Type) [CommRing A] [Algebra F A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (sigR A (ConjugateFieldNorm.cjF F : E →ₐ[F] E)) := by
  have : IsModuleTopology A (A ⊗[F] E) := ⟨rfl⟩
  have := IsModuleTopology.toContinuousAdd A (A ⊗[F] E)
  have := IsModuleTopology.toContinuousSMul (R := A) (A := A ⊗[F] E)
  refine (IsModuleTopology.continuous_of_linearMap
    (LinearMap.baseChange A (ConjugateFieldNorm.cjF F : E →ₐ[F] E).toLinearMap)).congr fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem inv_eq_adjoint (A : Type) [CommRing A] [Algebra F A] (g : ConjugateFieldNorm.UA F A V) :
    (g.1⁻¹).val = JR A (V.Gmᵀ)⁻¹ * Formalism.UG.cT (sigR A (ConjugateFieldNorm.cjF F)) g.1.val * JR A V.Gmᵀ := by
  have h : Formalism.UG.cT (sigR A (ConjugateFieldNorm.cjF F)) g.1.val * JR A V.Gmᵀ * g.1.val = JR A V.Gmᵀ := (mem_UA_iff V A g.1).1 g.2
  have hu : IsUnit (V.Gmᵀ).det := by rw [Matrix.det_transpose]; exact V.Gm_det.isUnit
  have h1 : JR A (V.Gmᵀ)⁻¹ * JR A V.Gmᵀ = (1 : Matrix (Fin r) (Fin r) (A ⊗[F] E)) := by
    unfold JR
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  refine Units.inv_eq_of_mul_eq_one_left ?_
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.UG.cT _ _), h, h1]

theorem topU_eq (A : Type) [CommRing A] [Algebra F A] [TopologicalSpace A] [IsTopologicalRing A] :
    AutomorphismGroupTopologies.topU F A V = instTopologicalSpaceSubtype := by
  have : IsModuleTopology A (A ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (A ⊗[F] E) := IsModuleTopology.isTopologicalRing A _
  apply le_antisymm
  · letI := AutomorphismGroupTopologies.topU F A V
    have hv : Continuous fun g : ConjugateFieldNorm.UA F A V => g.1.val := by
      refine continuous_matrix fun a b => (continuous_iff_crdA A _).2 fun φ => ?_
      simp only [← crdA_eq]
      exact continuous_iff_le_induced.2 (iInf_le_of_le a (iInf_le_of_le b (iInf_le _ φ)))
    refine continuous_iff_le_induced.1 (Units.continuous_iff.2 ⟨hv, ?_⟩)
    simp only [Function.comp_def, inv_eq_adjoint]
    exact (continuous_const.matrix_mul (hv.matrix_map (continuous_sigR A)).matrix_transpose).matrix_mul
      continuous_const
  · refine le_iInf fun a => le_iInf fun b => le_iInf fun φ => continuous_iff_le_induced.1 ?_
    simp only [crdA_eq]
    exact (continuous_iff_crdA A _).1 ((Units.continuous_val.comp continuous_subtype_val).matrix_elem a b) φ

abbrev pInf : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
abbrev pFin : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

theorem map_sigR {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B) (z : A ⊗[F] E) :
    (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A (ConjugateFieldNorm.cjF F) z) =
      sigR B (ConjugateFieldNorm.cjF F) ((Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_unit {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (p : A →ₐ[F] B)
    (J : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (A ⊗[F] E)) :
    (Formalism.UG.cT (sigR A (ConjugateFieldNorm.cjF F)) g * JR A J * g).map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom =
      Formalism.UG.cT (sigR B (ConjugateFieldNorm.cjF F)) (g.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom) * JR B J *
        g.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom ∧
    (JR A J).map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = JR B J := by
  have h2 : (JR A J).map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = JR B J := by
    ext i j; simp [JR, inclR]
  refine ⟨?_, h2⟩
  rw [Matrix.map_mul, Matrix.map_mul, h2]
  congr 2
  ext i j
  exact map_sigR p _

theorem exists_groupEquiv : ∃ ψ : ConjugateFieldNorm.GA F V ≃* HA (AF F) (ConjugateFieldNorm.cjF F) V.Gmᵀ,
    (∀ g, (HA.mat _ _ _ (ψ g)).val.map pInf = g.1.1.val ∧ (HA.mat _ _ _ (ψ g)).val.map pFin = g.2.1.val) ∧
    AutomorphismGroupTopologies.topG F V = TopologicalSpace.induced ψ inferInstance := by
  obtain ⟨e, he, hc, hc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have ext : ∀ {M N : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}, M.map pInf = N.map pInf → M.map pFin = N.map pFin →
      M = N := fun {M N} h1 h2 => by
    ext i j
    refine e.injective (Prod.ext ?_ ?_)
    · rw [(he _).1, (he _).1]; exact congrFun (congrFun h1 i) j
    · rw [(he _).2, (he _).2]; exact congrFun (congrFun h2 i) j
  let gl : Matrix (Fin r) (Fin r) (Ainf F ⊗[F] E) → Matrix (Fin r) (Fin r) (Af F ⊗[F] E) →
      Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := fun M N => Matrix.of fun i j => e.symm (M i j, N i j)
  have g1 : ∀ M N, (gl M N).map pInf = M := fun M N => by
    ext i j
    exact ((he _).1.symm.trans (congrArg Prod.fst (e.apply_symm_apply _)))
  have g2 : ∀ M N, (gl M N).map pFin = N := fun M N => by
    ext i j
    exact ((he _).2.symm.trans (congrArg Prod.snd (e.apply_symm_apply _)))
  let χ : HA (AF F) (ConjugateFieldNorm.cjF F) V.Gmᵀ →* ConjugateFieldNorm.GA F V :=
    { toFun := fun h => (⟨Formalism.UG.bc pInf (HA.mat _ _ _ h), (mem_UA_iff V _ _).2 (by
          have := congrArg (fun M => M.map pInf) (show Formalism.UG.cT _ _ * _ * _ = _ from h.2)
          rw [(map_unit (fstA F) _ _).1, (map_unit (fstA F) V.Gmᵀ 1).2] at this
          exact this)⟩,
        ⟨Formalism.UG.bc pFin (HA.mat _ _ _ h), (mem_UA_iff V _ _).2 (by
          have := congrArg (fun M => M.map pFin) (show Formalism.UG.cT _ _ * _ * _ = _ from h.2)
          rw [(map_unit (sndA F) _ _).1, (map_unit (sndA F) V.Gmᵀ 1).2] at this
          exact this)⟩)
      map_one' := Prod.ext (Subtype.ext (map_one (Formalism.UG.bc pInf))) (Subtype.ext (map_one (Formalism.UG.bc pFin)))
      map_mul' := fun a b => Prod.ext (Subtype.ext (map_mul (Formalism.UG.bc pInf) _ _))
        (Subtype.ext (map_mul (Formalism.UG.bc pFin) _ _)) }
  let ω : ConjugateFieldNorm.GA F V → HA (AF F) (ConjugateFieldNorm.cjF F) V.Gmᵀ := fun g =>
    (⟨⟨gl g.1.1.val g.2.1.val, gl g.1.1.inv g.2.1.inv,
      ext (by rw [Matrix.map_mul, g1, g1, g.1.1.val_inv]; simp) (by rw [Matrix.map_mul, g2, g2, g.2.1.val_inv]; simp),
      ext (by rw [Matrix.map_mul, g1, g1, g.1.1.inv_val]; simp) (by rw [Matrix.map_mul, g2, g2, g.2.1.inv_val]; simp)⟩,
      ext (by
        rw [(map_unit (fstA F) _ _).1, (map_unit (fstA F) V.Gmᵀ 1).2]
        simp only [g1]
        exact (mem_UA_iff V _ _).1 g.1.2) (by
        rw [(map_unit (sndA F) _ _).1, (map_unit (sndA F) V.Gmᵀ 1).2]
        simp only [g2]
        exact (mem_UA_iff V _ _).1 g.2.2)⟩ : HR (AF F) (ConjugateFieldNorm.cjF F) V.Gmᵀ)
  have l1 : Function.LeftInverse ω χ := fun h => Subtype.ext (Units.ext (ext (g1 _ _) (g2 _ _)))
  have l2 : Function.RightInverse ω χ := fun g =>
    Prod.ext (Subtype.ext (Units.ext (g1 _ _))) (Subtype.ext (Units.ext (g2 _ _)))
  let ψ : HA (AF F) (ConjugateFieldNorm.cjF F) V.Gmᵀ ≃* ConjugateFieldNorm.GA F V := { χ with invFun := ω, left_inv := l1, right_inv := l2 }
  refine ⟨ψ.symm, fun g => ⟨g1 _ _, g2 _ _⟩, ?_⟩
  have ht : AutomorphismGroupTopologies.topG F V = instTopologicalSpaceProd := by
    unfold AutomorphismGroupTopologies.topG; rw [topU_eq, topU_eq]; rfl
  rw [ht]
  have hp1 : Continuous (pInf (F := F) (E := E)) := (continuous_fst.comp hc).congr fun z => (he z).1
  have hp2 : Continuous (pFin (F := F) (E := E)) := (continuous_snd.comp hc).congr fun z => (he z).2
  have hv : Continuous fun h : HA (AF F) (ConjugateFieldNorm.cjF F) V.Gmᵀ => HA.mat _ _ _ h := continuous_subtype_val
  have c1 : Continuous ψ := by
    refine Continuous.prodMk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _)
      (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _)
    · exact (Units.continuous_val.comp hv).matrix_map hp1
    · exact (Units.continuous_coe_inv.comp hv).matrix_map hp1
    · exact (Units.continuous_val.comp hv).matrix_map hp2
    · exact (Units.continuous_coe_inv.comp hv).matrix_map hp2
  have c2 : Continuous ψ.symm := by
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · refine continuous_matrix fun i j => hc'.comp (Continuous.prodMk ?_ ?_)
      · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)).matrix_elem i j
      · exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_elem i j
    · refine continuous_matrix fun i j => hc'.comp (Continuous.prodMk ?_ ?_)
      · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)).matrix_elem i j
      · exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)).matrix_elem i j
  exact (Homeomorph.mk ψ.symm.toEquiv c2 c1).isInducing.eq_induced

end Gen

section Rec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

instance totallyReal_host (D : D7) : IsTotallyReal D.host.F := D.sp.cm.totReal

variable {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r)

def crdR : V.V ≃ₗ[D.host.E] (Fin r → D.host.E) := (V.frame.reindex (finCongr hr)).equivFun

def gramR : Matrix (Fin r) (Fin r) D.host.E := (Matrix.reindex (finCongr hr) (finCongr hr) V.gram)ᵀ

theorem herm_crdR (x y : V.V) : herm (gramR V hr) (crdR V hr x) (crdR V hr y) = V.hT y x := by
  subst hr
  rw [Formalism.L2.Herm.hT_crd D.sp.cm V]
  unfold herm Formalism.UG.hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [crdR, gramR, finCongr_refl, Matrix.reindex_refl_refl, Module.Basis.reindex_refl]
  change _ * V.gram b a * cc _ = cc _ * V.gram b a * _
  unfold Formalism.L2.Herm.crd
  ring

theorem mem_one_iff (z : D.host.E) : z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  exact ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩

def spOf : ConjugateFieldNorm.HSpace D.host.E r where
  Gm := gramR V hr
  Gm_herm a b := V.herm.eq _ _
  Gm_det h := by
    obtain ⟨v, hv, h0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
    obtain ⟨x, rfl⟩ := (crdR V hr).surjective v
    refine hv ((congrArg _ (V.nondeg.2 x fun y => ?_)).trans (map_zero _))
    rw [← herm_crdR V hr, herm, Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_mul, show ∑ a, crdR V hr x a * gramR V hr a b = 0 from congrFun h0 b, zero_mul]
  L := V.L0.map ((crdR V hr).toLinearMap.restrictScalars (𝓞 D.host.E))
  L_fg := V.standardTuple_isLattice.fg.map _
  L_span := by
    have := congrArg (Submodule.map (crdR V hr).toLinearMap) V.standardTuple_isLattice.span_eq_top
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at this
    exact this
  L_dual v := by
    obtain ⟨x, rfl⟩ := (crdR V hr).surjective v
    have h1 : crdR V hr x ∈ V.L0.map ((crdR V hr).toLinearMap.restrictScalars (𝓞 D.host.E)) ↔ x ∈ V.L0 :=
      ⟨fun ⟨y, hy, e⟩ => (crdR V hr).injective e ▸ hy, fun h => ⟨x, h, rfl⟩⟩
    have h2 : x ∈ V.L0 ↔ ∀ y ∈ V.L0, IsIntegral ℤ (V.hT y x) := by
      conv_lhs => rw [← V.baseLattice_isUnimodular]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, mem_one_iff]
      rfl
    rw [h1, h2]
    constructor
    · rintro h _ ⟨y, hy, rfl⟩
      exact (herm_crdR V hr x y).symm ▸ h y hy
    · intro h y hy
      exact herm_crdR V hr x y ▸ h _ ⟨y, hy, rfl⟩

structure IsCoord (V' : ConjugateFieldNorm.HSpace D.host.E r) (ψ : ConjugateFieldNorm.GA D.host.F V' ≃* GA D V) : Prop where
  sp : V' = spOf V hr
  inf : ∀ g, Matrix.reindex (finCongr hr) (finCongr hr) (infHom V (ψ g)).val = g.1.1.val
  fin : ∀ g, Matrix.reindex (finCongr hr) (finCongr hr) (finHom V (ψ g)).val = g.2.1.val
  top : AutomorphismGroupTopologies.topG D.host.F V' = TopologicalSpace.induced ψ inferInstance

theorem exists_isCoord {W : HSp D} (e : V = W) (hW : W.rank = r) :
    ∃ ψ, IsCoord V (e ▸ hW) (spOf W hW) ψ := by
  subst e hW
  have key : ∀ (σ : D.host.E →ₐ[D.host.F] D.host.E) (J : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
      σ = ConjugateFieldNorm.cjF D.host.F → J = (spOf V rfl).Gmᵀ →
      ∃ ψ : ConjugateFieldNorm.GA D.host.F (spOf V rfl) ≃* HA (AF D.host.F) σ J,
      (∀ g, (HA.mat _ _ _ (ψ g)).val.map pInf = g.1.1.val ∧ (HA.mat _ _ _ (ψ g)).val.map pFin = g.2.1.val) ∧
      AutomorphismGroupTopologies.topG D.host.F (spOf V rfl) = TopologicalSpace.induced ψ inferInstance := by
    rintro _ _ rfl rfl
    exact exists_groupEquiv _
  obtain ⟨ψ, h1, h2⟩ := key D.sp.cm.sig V.gram (AlgHom.ext fun _ => rfl) rfl
  exact ⟨ψ, rfl, fun g => (h1 g).1, fun g => (h1 g).2, h2⟩

variable {V hr} {V' : ConjugateFieldNorm.HSpace D.host.E r} {ψ : ConjugateFieldNorm.GA D.host.F V' ≃* GA D V}

theorem IsCoord.mem_GfC (h : IsCoord V hr V' ψ) (g) : ψ g ∈ GfC V ↔ g.1 = 1 := by
  subst hr
  rw [GfC, MonoidHom.mem_ker, Subtype.ext_iff, Units.ext_iff, Units.ext_iff, ← h.inf g]
  rfl

theorem IsCoord.mem_GinfC (h : IsCoord V hr V' ψ) (g) : ψ g ∈ GinfC V ↔ g.2 = 1 := by
  subst hr
  rw [GinfC, MonoidHom.mem_ker, Subtype.ext_iff, Units.ext_iff, Units.ext_iff, ← h.fin g]
  rfl

theorem IsCoord.mem_GQ (h : IsCoord V hr V' ψ) (g) : ψ g ∈ GQ V ↔ g ∈ AutomorphismGroupTopologies.ratG D.host.F V' := by
  subst hr
  have h1 : (HA.mat _ _ _ (ψ g)).val.map pInf = g.1.1.val := h.inf g
  have h2 : (HA.mat _ _ _ (ψ g)).val.map pFin = g.2.1.val := h.fin g
  constructor
  · rintro ⟨γ, -, e⟩
    have e' : (HA.mat _ _ _ (ψ g)).val = γ.val.map (inclR (AF D.host.F)) := (congrArg Units.val e).symm
    refine ⟨γ, ?_, ?_⟩
    · rw [← h1, e']; ext i j; simp [inclR, ConjugateFieldNorm.incl]
    · rw [← h2, e']; ext i j; simp [inclR, ConjugateFieldNorm.incl]
  · rintro ⟨γ, e1, e2⟩
    obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
    have e' : (HA.mat _ _ _ (ψ g)).val = γ.val.map (inclR (AF D.host.F)) := by
      ext i j
      refine e.injective (Prod.ext ?_ ?_)
      · rw [(he _).1, (he _).1]
        refine (congrFun (congrFun (h1.trans e1) i) j).trans ?_
        rfl
      · rw [(he _).2, (he _).2]
        refine (congrFun (congrFun (h2.trans e2) i) j).trans ?_
        rfl
    refine ⟨γ, ?_, Units.ext e'.symm⟩
    have hu : Formalism.UG.cT (sigR _ D.sp.cm.sig) (HA.mat _ _ _ (ψ g)).val * JR _ V.gram * (HA.mat _ _ _ (ψ g)).val =
      JR _ V.gram := (ψ g).2
    have hinj : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
      Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
    change Formalism.UG.cT _ γ.val * V.gram * γ.val = V.gram
    refine Matrix.map_injective hinj ?_
    change (_ : Matrix _ _ _).map _ = JR _ V.gram
    rw [← hu, e', Matrix.map_mul, Matrix.map_mul]
    congr 2

theorem latHat_spOf (V : HSp D) : ConjugateFieldNorm.latHat D.host.F (spOf V rfl).L = Formalism.L2.Pj.latHat V := by
  unfold ConjugateFieldNorm.latHat Formalism.L2.Pj.latHat
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, e⟩
    exact ⟨a, ha, x, hx, by rw [e]; simp [crdR]⟩
  · rintro ⟨a, ha, x, hx, e⟩
    exact ⟨a, ha, _, ⟨x, hx, rfl⟩, by rw [e]; simp [crdR]⟩

theorem IsCoord.isLevelK_iff (h : IsCoord V hr V' ψ) (N : ℕ) (Kf : Subgroup (GA D V)) :
    Formalism.L2.Pj.IsLevelK V N Kf ↔
      Kf.comap ψ.toMonoidHom = ConjugateFieldNorm.levelK D.host.F V' N ∧ ConjugateFieldNorm.LevelByCongruence D.host.F V' N := by
  have hf := h.mem_GfC
  subst hr
  obtain rfl := h.sp
  have h2 : ∀ g, (finHom V (ψ g)).val = g.2.1.val := h.fin
  have key : Formalism.L2.Pj.IsLevelK V N Kf ↔ ∀ k, ψ k ∈ Kf ↔ k.1 = 1 ∧ ∀ z ∈ ConjugateFieldNorm.latHat D.host.F (spOf V rfl).L,
      ∃ w ∈ ConjugateFieldNorm.latHat D.host.F (spOf V rfl).L, k.2.1.val.mulVec z - z = N • w := by
    unfold Formalism.L2.Pj.IsLevelK
    rw [ψ.surjective.forall]
    simp only [hf, h2, latHat_spOf]
  rw [key]
  constructor
  · intro hk
    have hl : ConjugateFieldNorm.LevelByCongruence D.host.F (spOf V rfl) N := fun k => by
      refine ⟨fun hh => ⟨hh.1, hh.2.2⟩, fun hh => ⟨hh.1, fun z => ⟨fun hz => ?_, fun hz => ?_⟩, hh.2⟩⟩
      · obtain ⟨w, hw, e⟩ := hh.2 z hz
        rw [eq_add_of_sub_eq e]
        exact add_mem (nsmul_mem hw N) hz
      · have hi : ψ k⁻¹ ∈ Kf := by rw [map_inv]; exact Kf.inv_mem ((hk k).2 hh)
        obtain ⟨w, hw, e⟩ := ((hk _).1 hi).2 _ hz
        have e1 : (k⁻¹).2.1.val * k.2.1.val = 1 := Units.inv_mul _
        rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec] at e
        rw [eq_add_of_sub_eq e]
        exact add_mem (nsmul_mem hw N) hz
    exact ⟨Subgroup.ext fun k => (hk k).trans (hl k).symm, hl⟩
  · rintro ⟨e, hl⟩ k
    rw [← hl k, ← e]
    rfl

def IsCoord.quotEquiv (h : IsCoord V hr V' ψ) : AutomorphismGroupTopologies.AutQ D.host.F V' ≃ᵐ Formalism.L2.Pj.AutQ V where
  toEquiv := Quotient.congr ψ.toEquiv fun a b => by
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, ← h.mem_GQ, map_mul, map_inv]
    rfl
  measurable_toFun s hs := by
    change MeasurableSet[@borel _ (AutomorphismGroupTopologies.topG D.host.F V')] (ψ ⁻¹' (Formalism.L2.Pj.autMk V ⁻¹' s))
    rw [h.top, borel_comap]
    exact ⟨_, hs, rfl⟩
  measurable_invFun s hs := by
    have hs' : MeasurableSet[@borel _ (AutomorphismGroupTopologies.topG D.host.F V')] (AutomorphismGroupTopologies.autMk D.host.F V' ⁻¹' s) := hs
    rw [h.top, borel_comap] at hs'
    obtain ⟨t, ht, e⟩ := hs'
    change MeasurableSet (ψ.symm ⁻¹' (AutomorphismGroupTopologies.autMk D.host.F V' ⁻¹' s))
    rw [← e, ← Set.preimage_comp]
    simpa using ht

theorem IsCoord.quotEquiv_mk (h : IsCoord V hr V' ψ) (g) :
    h.quotEquiv (AutomorphismGroupTopologies.autMk D.host.F V' g) = Formalism.L2.Pj.autMk V (ψ g) := rfl

theorem IsCoord.onQ_eq (h : IsCoord V hr V' ψ) (φ : GA D V → ℂ) (hφ : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) :
    AutomorphismGroupTopologies.onQ D.host.F V' (fun g => φ (ψ g)) = Formalism.L2.Pj.onQ V φ ∘ h.quotEquiv := by
  funext q
  obtain ⟨g, rfl⟩ := Quotient.exists_rep q
  refine (AutomorphismGroupTopologies.onQ_mk D.host.F V' _ (fun γ hγ g => ?_) g).trans ?_
  · rw [map_mul, hφ _ ((h.mem_GQ γ).2 hγ)]
  · have e : (QuotientGroup.rightRel (GQ V)) (ψ g) (Quotient.out (Formalism.L2.Pj.autMk V (ψ g))) :=
      Quotient.exact (Quotient.out_eq (Formalism.L2.Pj.autMk V (ψ g))).symm
    rw [QuotientGroup.rightRel_apply] at e
    rw [← hφ _ e (ψ g), inv_mul_cancel_right]
    rfl

def RightInv (V : HSp D) (ν : Measure (Formalism.L2.Pj.AutQ V)) : Prop :=
  ∀ (h : GA D V) (ρ : Formalism.L2.Pj.AutQ V → Formalism.L2.Pj.AutQ V),
    (∀ g : GA D V, ρ (Quotient.mk _ g) = Quotient.mk _ (g * h)) → ∀ s, MeasurableSet s → ν (ρ ⁻¹' s) = ν s

theorem IsCoord.isAutProb_iff (h : IsCoord V hr V' ψ) (ν : Measure (AutomorphismGroupTopologies.AutQ D.host.F V')) :
    AutomorphismGroupTopologies.IsAutProb D.host.F V' ν ↔ IsProbabilityMeasure (ν.map h.quotEquiv) ∧ RightInv V (ν.map h.quotEquiv) := by
  refine and_congr ?_ ⟨fun H k ρ hρ s hs => ?_, fun H k s hs => ?_⟩
  · rw [isProbabilityMeasure_iff, isProbabilityMeasure_iff, MeasurableEquiv.map_apply, Set.preimage_univ]
  · obtain ⟨k, rfl⟩ := ψ.surjective k
    rw [MeasurableEquiv.map_apply, MeasurableEquiv.map_apply, ← H k _ (h.quotEquiv.measurable hs)]
    congr 1
    ext q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    change ρ (Quotient.mk _ (ψ g)) ∈ s ↔ Quotient.mk _ (ψ (g * k)) ∈ s
    rw [hρ, map_mul]
  · have := H (ψ k) (h.quotEquiv ∘ AutomorphismGroupTopologies.autRt D.host.F V' k ∘ h.quotEquiv.symm) (fun g => by
      obtain ⟨g, rfl⟩ := ψ.surjective g
      change h.quotEquiv (AutomorphismGroupTopologies.autRt _ _ k (h.quotEquiv.symm (h.quotEquiv (AutomorphismGroupTopologies.autMk D.host.F V' g)))) = _
      rw [MeasurableEquiv.symm_apply_apply, AutomorphismGroupTopologies.autRt_mk, h.quotEquiv_mk, map_mul]) _
      (h.quotEquiv.symm.measurable hs)
    rw [MeasurableEquiv.map_apply, MeasurableEquiv.map_apply] at this
    simpa [← Set.preimage_comp, Function.comp_def] using this

end Rec

end GlobalTheory.CoreLawsCompare
