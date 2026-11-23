import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MExistsCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NumFieldHosCountable
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MeasCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MeasInfCut
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.Meas

open Formalism.L2.SG.Measures

section Ring

variable {F E : Type} [Field F] [Field E] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem repr_tensMap (b : Module.Basis ι F E) {R R' : Type} [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (y : R ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis R' b).repr (tensMap (E := E) φ y) i =
      φ ((Algebra.TensorProduct.basis R b).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp [tensMap, Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

end Ring

section Adele

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {ι : Type} [Fintype ι]
  [DecidableEq ι]

theorem split_inj (b : Module.Basis ι F E) (y : AF F ⊗[F] E) (h1 : tensMap (E := E) (fstA F) y = 0)
    (h2 : tensMap (E := E) (sndA F) y = 0) : y = 0 := by
  apply (Algebra.TensorProduct.basis (AF F) b).repr.injective
  ext i
  have e1 := repr_tensMap b (fstA F) y i
  have e2 := repr_tensMap b (sndA F) y i
  rw [h1, map_zero, Finsupp.zero_apply] at e1
  rw [h2, map_zero, Finsupp.zero_apply] at e2
  rw [map_zero, Finsupp.zero_apply]
  exact Prod.ext e1.symm e2.symm

theorem split_surj (b : Module.Basis ι F E) (y1 : Ainf F ⊗[F] E) (y2 : Af F ⊗[F] E) :
    ∃ y : AF F ⊗[F] E, tensMap (E := E) (fstA F) y = y1 ∧ tensMap (E := E) (sndA F) y = y2 := by
  let c : ι → AF F := fun i =>
    ((Algebra.TensorProduct.basis (Ainf F) b).repr y1 i, (Algebra.TensorProduct.basis (Af F) b).repr y2 i)
  have hc : ∀ i, (Algebra.TensorProduct.basis (AF F) b).repr
      ((Algebra.TensorProduct.basis (AF F) b).equivFun.symm c) i = c i := by
    intro i
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨(Algebra.TensorProduct.basis (AF F) b).equivFun.symm c, ?_, ?_⟩
  · apply (Algebra.TensorProduct.basis (Ainf F) b).repr.injective
    ext i
    rw [repr_tensMap, hc]
    rfl
  · apply (Algebra.TensorProduct.basis (Af F) b).repr.injective
    ext i
    rw [repr_tensMap, hc]
    rfl

theorem mat_ext (b : Module.Basis ι F E) {m : Type} {X Y : Matrix m m (AF F ⊗[F] E)}
    (h1 : X.map (tensMap (E := E) (fstA F)) = Y.map (tensMap (E := E) (fstA F)))
    (h2 : X.map (tensMap (E := E) (sndA F)) = Y.map (tensMap (E := E) (sndA F))) : X = Y := by
  ext i j
  have a1 := congrFun (congrFun h1 i) j
  have a2 := congrFun (congrFun h2 i) j
  simp only [Matrix.map_apply] at a1 a2
  exact sub_eq_zero.mp (split_inj b _ (by rw [map_sub, a1, sub_self]) (by rw [map_sub, a2, sub_self]))

def liftM (b : Module.Basis ι F E) {m : Type} (X : Matrix m m (Ainf F ⊗[F] E)) (Y : Matrix m m (Af F ⊗[F] E)) :
    Matrix m m (AF F ⊗[F] E) :=
  fun i j => (split_surj b (X i j) (Y i j)).choose

theorem liftM_fst (b : Module.Basis ι F E) {m : Type} (X : Matrix m m (Ainf F ⊗[F] E)) (Y : Matrix m m (Af F ⊗[F] E)) :
    (liftM b X Y).map (tensMap (E := E) (fstA F)) = X := by
  ext i j
  exact (split_surj b (X i j) (Y i j)).choose_spec.1

theorem liftM_snd (b : Module.Basis ι F E) {m : Type} (X : Matrix m m (Ainf F ⊗[F] E)) (Y : Matrix m m (Af F ⊗[F] E)) :
    (liftM b X Y).map (tensMap (E := E) (sndA F)) = Y := by
  ext i j
  exact (split_surj b (X i j) (Y i j)).choose_spec.2

end Adele

section Grp

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem ha_ext {R : Type} [CommRing R] [Algebra F R] {g h : HA R σ J}
    (e : ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) : g = h :=
  Subtype.ext (Units.ext e)

theorem haMap_mat {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R')
    (g : HA R σ J) :
    ((HA.mat R' σ J (haMap σ J φ g) : GL (Fin M) (R' ⊗[F] E)) : Matrix (Fin M) (Fin M) (R' ⊗[F] E)) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (tensMap φ) :=
  rfl

theorem one_mat {R : Type} [CommRing R] [Algebra F R] :
    ((HA.mat R σ J 1 : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = 1 :=
  rfl

theorem JR_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R') :
    (JR R J).map (tensMap (E := E) φ) = JR R' J := by
  ext i j
  simp [JR, tensMap_inclR]

theorem splitA_injective {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E) :
    Function.Injective (splitA (F := F) σ J) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 := congrArg (fun k : HA (Ainf F) σ J × HA (Af F) σ J =>
    ((HA.mat (Ainf F) σ J k.1 : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E))) hg
  have h2 := congrArg (fun k : HA (Ainf F) σ J × HA (Af F) σ J =>
    ((HA.mat (Af F) σ J k.2 : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))) hg
  simp only [splitA, MonoidHom.prod_apply, Prod.fst_one, Prod.snd_one] at h1 h2
  rw [haMap_mat, one_mat] at h1 h2
  apply ha_ext
  rw [one_mat]
  apply mat_ext b
  · rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

theorem splitA_surjective {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E) :
    Function.Surjective (splitA (F := F) σ J) := by
  rintro ⟨a, c⟩
  let A : GL (Fin M) (Ainf F ⊗[F] E) := HA.mat _ σ J a
  let C : GL (Fin M) (Af F ⊗[F] E) := HA.mat _ σ J c
  have hmul : liftM b (A : Matrix (Fin M) (Fin M) _) (C : Matrix (Fin M) (Fin M) _) *
      liftM b ((A⁻¹ : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) ((C⁻¹ : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) = 1 := by
    apply mat_ext b
    · rw [Matrix.map_mul, liftM_fst, liftM_fst, Matrix.map_one _ (map_zero _) (map_one _)]
      exact A.mul_inv
    · rw [Matrix.map_mul, liftM_snd, liftM_snd, Matrix.map_one _ (map_zero _) (map_one _)]
      exact C.mul_inv
  have hmul' : liftM b ((A⁻¹ : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) ((C⁻¹ : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) *
      liftM b (A : Matrix (Fin M) (Fin M) _) (C : Matrix (Fin M) (Fin M) _) = 1 := by
    apply mat_ext b
    · rw [Matrix.map_mul, liftM_fst, liftM_fst, Matrix.map_one _ (map_zero _) (map_one _)]
      exact A.inv_mul
    · rw [Matrix.map_mul, liftM_snd, liftM_snd, Matrix.map_one _ (map_zero _) (map_one _)]
      exact C.inv_mul
  let u : GL (Fin M) (AF F ⊗[F] E) := ⟨_, _, hmul, hmul'⟩
  have hA : Formalism.UG.cT (sigR (Ainf F) σ) (A : Matrix (Fin M) (Fin M) _) * JR (Ainf F) J * (A : Matrix (Fin M) (Fin M) _) =
      JR (Ainf F) J := a.2
  have hC : Formalism.UG.cT (sigR (Af F) σ) (C : Matrix (Fin M) (Fin M) _) * JR (Af F) J * (C : Matrix (Fin M) (Fin M) _) =
      JR (Af F) J := c.2
  have hu : u ∈ HR (AF F) σ J := by
    show Formalism.UG.cT (sigR (AF F) σ) (u : Matrix (Fin M) (Fin M) _) * JR (AF F) J * (u : Matrix (Fin M) (Fin M) _) =
      JR (AF F) J
    apply mat_ext b
    · rw [Matrix.map_mul, Matrix.map_mul, ← Formalism.UG.P.incl_cT_map _ (sigR (Ainf F) σ) _ (tensMap_sigR _ σ),
        JR_map]
      show Formalism.UG.cT _ ((liftM b _ _).map _) * _ * (liftM b _ _).map _ = _
      rw [liftM_fst]
      exact hA
    · rw [Matrix.map_mul, Matrix.map_mul, ← Formalism.UG.P.incl_cT_map _ (sigR (Af F) σ) _ (tensMap_sigR _ σ),
        JR_map]
      show Formalism.UG.cT _ ((liftM b _ _).map _) * _ * (liftM b _ _).map _ = _
      rw [liftM_snd]
      exact hC
  refine ⟨⟨u, hu⟩, ?_⟩
  refine Prod.ext (ha_ext σ J ?_) (ha_ext σ J ?_)
  · exact liftM_fst b _ _
  · exact liftM_snd b _ _

end Grp

end Formalism.L2.SG.Pf.Meas

open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.Meas

open Formalism.L2.SG.Measures

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem tensMap_cont (b : Module.Basis ι F E) {R R' : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing R'] [Algebra F R'] [TopologicalSpace R'] [IsTopologicalRing R']
    (φ : R →ₐ[F] R') (hφ : Continuous φ) : Continuous (tensMap (E := E) φ) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology R' (R' ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  have : ContinuousAdd (R' ⊗[F] E) := IsModuleTopology.toContinuousAdd R' (R' ⊗[F] E)
  let e := (Algebra.TensorProduct.basis R b).equivFun
  let e' := (Algebra.TensorProduct.basis R' b).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he' : Continuous e'.symm := IsModuleTopology.continuous_of_linearMap e'.symm.toLinearMap
  have hfun : (tensMap (E := E) φ : R ⊗[F] E → R' ⊗[F] E) = e'.symm ∘ (fun c i => φ (c i)) ∘ e := by
    funext y
    apply e'.injective
    funext i
    simp only [Function.comp_apply, LinearEquiv.apply_symm_apply]
    simp only [e, e', Module.Basis.equivFun_apply, repr_tensMap]
  rw [hfun]
  exact he'.comp ((continuous_pi fun i => hφ.comp (continuous_apply i)).comp he)

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem haMap_cont {R R' : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [CommRing R'] [Algebra F R'] [TopologicalSpace R'] (φ : R →ₐ[F] R') (hf : Continuous (tensMap (E := E) φ)) :
    Continuous (haMap σ J φ) := by
  have hs : Continuous (fun g : ↥(HR R σ J) => (g : GL (Fin M) (R ⊗[F] E))) := continuous_subtype_val
  have hv : Continuous (fun g : ↥(HR R σ J) =>
      ((g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) :=
    Units.continuous_val.comp hs
  have hi : Continuous (fun g : ↥(HR R σ J) =>
      (((g : GL (Fin M) (R ⊗[F] E))⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E))) :=
    Units.continuous_coe_inv.comp hs
  have hb : Continuous (fun g : ↥(HR R σ J) => Formalism.UG.bc (tensMap (E := E) φ) (g : GL (Fin M) (R ⊗[F] E))) := by
    rw [Units.continuous_iff]
    exact ⟨hv.matrix_map hf, hi.matrix_map hf⟩
  show Continuous (fun g : ↥(HR R σ J) =>
    (⟨Formalism.UG.bc (tensMap (E := E) φ) (g : GL (Fin M) (R ⊗[F] E)), (haMap σ J φ g).2⟩ : ↥(HR R' σ J)))
  exact hb.subtype_mk _

end Top

end Formalism.L2.SG.Pf.Meas

open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.Meas

open Formalism.L2.SG.Measures Formalism.IndefR.Eqv.G5

section Iso

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem splitA_cont {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E) :
    Continuous (splitA (F := F) σ J) := by
  have h1 : Continuous (fstA F) := continuous_fst
  have h2 : Continuous (sndA F) := continuous_snd
  exact (haMap_cont σ J _ (tensMap_cont b _ h1)).prodMk (haMap_cont σ J _ (tensMap_cont b _ h2))

theorem grp_facts (hE : Module.finrank F E = 2) :
    (IsTopologicalGroup (HA (AF F) σ J) ∧ T2Space (HA (AF F) σ J) ∧ LocallyCompactSpace (HA (AF F) σ J) ∧
      SecondCountableTopology (HA (AF F) σ J) ∧ BorelSpace (HA (AF F) σ J)) ∧
    (IsTopologicalGroup (HA (Ainf F) σ J) ∧ T2Space (HA (Ainf F) σ J) ∧ LocallyCompactSpace (HA (Ainf F) σ J) ∧
      SecondCountableTopology (HA (Ainf F) σ J) ∧ BorelSpace (HA (Ainf F) σ J)) ∧
    (IsTopologicalGroup (HA (Af F) σ J) ∧ T2Space (HA (Af F) σ J) ∧ LocallyCompactSpace (HA (Af F) σ J) ∧
      SecondCountableTopology (HA (Af F) σ J) ∧ BorelSpace (HA (Af F) σ J)) := by
  obtain ⟨a1, a2, a3⟩ := af_facts F
  have : T2Space (Ainf F) := t2Space_Ainf
  have : SecondCountableTopology (Ainf F) := ainf_secondCountable
  have : T2Space (Af F) := finite_adeles_t2
  have : LocallyCompactSpace (Af F) := af_locallyCompact
  have : SecondCountableTopology (Af F) := af_secondCountable
  exact ⟨ha_facts (AF F) hE σ J, ha_facts (Ainf F) hE σ J, ha_facts (Af F) hE σ J⟩

def sA (hE : Module.finrank F E = 2) : HA (AF F) σ J ≃ₜ* HA (Ainf F) σ J × HA (Af F) σ J :=
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ hE
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hE
  { toMulEquiv := MulEquiv.ofBijective (splitA σ J) ⟨splitA_injective σ J b, splitA_surjective σ J b⟩
    continuous_toFun := splitA_cont σ J b
    continuous_invFun := by
      obtain ⟨⟨g1, g2, g3, g4, g5⟩, ⟨h1, h2, h3, h4, h5⟩, ⟨k1, k2, k3, k4, k5⟩⟩ := grp_facts σ J hE
      have ho : IsOpenMap (splitA (F := F) σ J) :=
        MonoidHom.isOpenMap_of_sigmaCompact _ (splitA_surjective σ J b) (splitA_cont σ J b)
      exact ((MulEquiv.ofBijective (splitA σ J) ⟨splitA_injective σ J b,
        splitA_surjective σ J b⟩).toEquiv.toHomeomorphOfContinuousOpen (splitA_cont σ J b) ho).symm.continuous }

theorem sA_apply (hE : Module.finrank F E = 2) (g : HA (AF F) σ J) : sA σ J hE g = splitA σ J g := rfl

end Iso

end Formalism.L2.SG.Pf.Meas

open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.Meas

open Formalism.L2.SG.Measures Formalism.L2.SG.AdBridge Formalism.MainNotions.S

variable (I : AutInst)

theorem finrank_two : Module.finrank I.F I.E = 2 := by
  rw [Module.finrank_eq_card_basis (Formalism.L2.SG.Pf.bas I)]
  simp

theorem tauF_eq (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    tauF I y = Algebra.TensorProduct.comm I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af I.F) I.E (tensMap (E := I.E) (sndA I.F) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul]
    simp [tensMap]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable (hb : AdBridgeIso I)

theorem cross_fin (s : I.Ginf) : (splitA I.cm.sig I.J (toHA I hb (s, 1))).2 = 1 := by
  have hB := (toHA_isBridge I hb (s, 1)).2
  apply ha_ext
  show (hmat I (toHA I hb (s, 1))).map (tensMap (E := I.E) (sndA I.F)) = 1
  ext i j
  apply (Algebra.TensorProduct.comm I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af I.F) I.E).injective
  have h := congrFun (congrFun hB i) j
  simp only [ofHAFin, Matrix.map_apply] at h
  rw [Matrix.map_apply, ← tauF_eq, ← h]
  show I.fmat (1 : I.Gf) i j = _
  have h1 : I.fmat (1 : I.Gf) = 1 := by simp [AutInst.fmat]
  rw [h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem theta_zero_fst (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) (h : ∀ v, thetaV I v y = 0) :
    tensMap (E := I.E) (fstA I.F) y = 0 := by
  have hc : ∀ k, fstA I.F ((Formalism.L2.SG.Pf.alg_B I).repr y k) = 0 := by
    intro k
    funext v
    have := Formalism.L2.SG.Pf.alg_inf_inj I v _ _ (by rw [← Formalism.L2.SG.Pf.alg_theta]; exact h v)
    fin_cases k
    · exact this.1
    · exact this.2
  apply (Algebra.TensorProduct.basis (Ainf I.F) (Formalism.L2.SG.Pf.bas I)).repr.injective
  ext k
  rw [repr_tensMap, map_zero, Finsupp.zero_apply]
  exact hc k

theorem cross_inf (x : I.Gf) : (splitA I.cm.sig I.J (toHA I hb (1, x))).1 = 1 := by
  apply ha_ext
  show (hmat I (toHA I hb (1, x))).map (tensMap (E := I.E) (fstA I.F)) = 1
  have hM : ∀ v, (hmat I (toHA I hb (1, x))).map (thetaV I v) = 1 := by
    intro v
    have hB := (toHA_isBridge I hb (1, x)).1 v
    have h1 : uMat ((1 : I.Ginf) v) = 1 := by simp [uMat]
    have hB' : uMat (((1, x) : I.GA).1 v) = 1 := h1
    rw [hB'] at hB
    have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    have := congrArg (fun Q => I.P v * Q * (I.P v)⁻¹) hB
    simp only [ofHAInf] at this
    rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hP] at this
    have e : I.P v * ((I.P v)⁻¹ * (hmat I (toHA I hb (1, x))).map (thetaV I v) * I.P v) * (I.P v)⁻¹ =
        (hmat I (toHA I hb (1, x))).map (thetaV I v) := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one,
        Matrix.mul_nonsing_inv_cancel_left _ _ hP]
    exact e.symm.trans this.symm
  ext i j
  rw [Matrix.map_apply]
  have h0 : tensMap (E := I.E) (fstA I.F) (hmat I (toHA I hb (1, x)) i j - (1 : Matrix (Fin I.n) (Fin I.n) _) i j) = 0 := by
    apply theta_zero_fst
    intro v
    have := congrFun (congrFun (hM v) i) j
    rw [Matrix.map_apply] at this
    rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Formalism.L2.SG.Pf.Meas

open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.Meas

open Formalism.L2.SG.Measures Formalism.L2.SG.AdBridge Formalism.L2.SG.MExistsCut Formalism.IndefR.Eqv.G5

variable (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I)

def Phi : I.GA ≃ₜ* HA (Ainf I.F) I.cm.sig I.J × HA (Af I.F) I.cm.sig I.J :=
  (toHA I hb).trans (sA I.cm.sig I.J (finrank_two I))

theorem Phi_apply (p : I.GA) : Phi I hb p = splitA I.cm.sig I.J (toHA I hb p) := rfl

theorem toFinI_one : toFinI I hb 1 = 1 := by
  unfold toFinI
  have : ((1 : I.Ginf), (1 : I.Gf)) = (1 : I.GA) := rfl
  rw [this, map_one, map_one]
  rfl

theorem toInfI_one : toInfI I hb 1 = 1 := by
  unfold toInfI
  have : ((1 : I.Ginf), (1 : I.Gf)) = (1 : I.GA) := rfl
  rw [this, map_one, map_one]
  rfl

theorem Phi_pair (s : I.Ginf) (x : I.Gf) : Phi I hb (s, x) = (toInfI I hb s, toFinI I hb x) := by
  have hsx : ((s, x) : I.GA) = (s, 1) * (1, x) := by simp
  rw [hsx, map_mul, Phi_apply, Phi_apply]
  refine Prod.ext ?_ ?_
  · show (splitA I.cm.sig I.J (toHA I hb (s, 1))).1 * (splitA I.cm.sig I.J (toHA I hb (1, x))).1 = _
    rw [cross_inf I hb x, mul_one]
    rfl
  · show (splitA I.cm.sig I.J (toHA I hb (s, 1))).2 * (splitA I.cm.sig I.J (toHA I hb (1, x))).2 = _
    rw [cross_fin I hb s, one_mul]
    rfl

def eInf : I.Ginf ≃ₜ* HA (Ainf I.F) I.cm.sig I.J where
  toFun := toInfI I hb
  invFun k := ((Phi I hb).symm (k, 1)).1
  left_inv s := by
    show ((Phi I hb).symm (toInfI I hb s, 1)).1 = s
    rw [← toFinI_one I hb, ← Phi_pair, ContinuousMulEquiv.symm_apply_apply]
  right_inv k := by
    show toInfI I hb ((Phi I hb).symm (k, 1)).1 = k
    have := Phi_pair I hb ((Phi I hb).symm (k, 1)).1 ((Phi I hb).symm (k, 1)).2
    rw [Prod.mk.eta, ContinuousMulEquiv.apply_symm_apply] at this
    exact (congrArg Prod.fst this).symm
  map_mul' s t := by
    show (splitA I.cm.sig I.J (toHA I hb (s * t, 1))).1 =
      (splitA I.cm.sig I.J (toHA I hb (s, 1))).1 * (splitA I.cm.sig I.J (toHA I hb (t, 1))).1
    have : ((s * t, 1) : I.GA) = (s, 1) * (t, 1) := by simp
    rw [this, map_mul, map_mul]
    rfl
  continuous_toFun := continuous_fst.comp ((Phi I hb).continuous.comp (continuous_id.prodMk continuous_const))
  continuous_invFun := continuous_fst.comp ((Phi I hb).symm.continuous.comp (continuous_id.prodMk continuous_const))

def eFin : I.Gf ≃ₜ* HA (Af I.F) I.cm.sig I.J where
  toFun := toFinI I hb
  invFun k := ((Phi I hb).symm (1, k)).2
  left_inv x := by
    show ((Phi I hb).symm (1, toFinI I hb x)).2 = x
    rw [← toInfI_one I hb, ← Phi_pair, ContinuousMulEquiv.symm_apply_apply]
  right_inv k := by
    show toFinI I hb ((Phi I hb).symm (1, k)).2 = k
    have := Phi_pair I hb ((Phi I hb).symm (1, k)).1 ((Phi I hb).symm (1, k)).2
    rw [Prod.mk.eta, ContinuousMulEquiv.apply_symm_apply] at this
    exact (congrArg Prod.snd this).symm
  map_mul' x y := by
    show (splitA I.cm.sig I.J (toHA I hb (1, x * y))).2 =
      (splitA I.cm.sig I.J (toHA I hb (1, x))).2 * (splitA I.cm.sig I.J (toHA I hb (1, y))).2
    have : ((1, x * y) : I.GA) = (1, x) * (1, y) := by simp
    rw [this, map_mul, map_mul]
    rfl
  continuous_toFun := continuous_snd.comp ((Phi I hb).continuous.comp (continuous_const.prodMk continuous_id))
  continuous_invFun := continuous_snd.comp ((Phi I hb).symm.continuous.comp (continuous_const.prodMk continuous_id))

theorem eInf_coe : (eInf I hb : I.Ginf → _) = toInfI I hb := rfl
theorem eFin_coe : (eFin I hb : I.Gf → _) = toFinI I hb := rfl

theorem Phi_eq : (Phi I hb : I.GA → _) = Prod.map (eInf I hb) (eFin I hb) := by
  funext p
  obtain ⟨s, x⟩ := p
  exact Phi_pair I hb s x

end Formalism.L2.SG.Pf.Meas

open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.Meas

open Formalism.L2.SG.Measures Formalism.L2.SG.AdBridge Formalism.L2.SG.MExistsCut Formalism.IndefR.Eqv.G5 Formalism.L2.SG.Sub

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem fv_grp (hE : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) :
    IsTopologicalGroup (HA (Fv F v) σ J) ∧ T2Space (HA (Fv F v) σ J) ∧ LocallyCompactSpace (HA (Fv F v) σ J) ∧
      SecondCountableTopology (HA (Fv F v) σ J) ∧ BorelSpace (HA (Fv F v) σ J) := by
  have := fv_locallyCompact (F := F) v
  have := fv_secondCountable (F := F) v
  exact ha_facts (Fv F v) hE σ J

theorem stabT_closed (hE : Module.finrank F E = 2) {a : ℕ} (X0 : Fin a → Fin M → E) :
    IsClosed (stabT (AF F) σ J X0 : Set (HA (AF F) σ J)) := by
  obtain ⟨a1, a2, a3⟩ := af_facts F
  obtain ⟨t1, t2, -, -, -⟩ := tens_facts (E := E) (AF F) hE
  have hs : Continuous (fun g : ↥(HR (AF F) σ J) => (g : GL (Fin M) (AF F ⊗[F] E))) := continuous_subtype_val
  have hv : Continuous (fun g : HA (AF F) σ J =>
      ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) :=
    Units.continuous_val.comp hs
  have hset : (stabT (AF F) σ J X0 : Set (HA (AF F) σ J)) = ⋂ b, {g : HA (AF F) σ J |
      Matrix.mulVec ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))
        (ratV (F := F) (AF F) (X0 b)) = ratV (F := F) (AF F) (X0 b)} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    rw [mem_stabT]
    rfl
  rw [hset]
  exact isClosed_iInter fun b => isClosed_eq (hv.matrix_mulVec continuous_const) continuous_const

theorem stabT_facts (hE : Module.finrank F E = 2) {a : ℕ} (X0 : Fin a → Fin M → E) :
    IsTopologicalGroup (stabT (AF F) σ J X0) ∧ LocallyCompactSpace (stabT (AF F) σ J X0) ∧
      BorelSpace (stabT (AF F) σ J X0) := by
  obtain ⟨⟨g1, g2, g3, g4, g5⟩, -, -⟩ := grp_facts σ J hE
  exact ⟨inferInstance, (stabT_closed σ J hE X0).isClosedEmbedding_subtypeVal.locallyCompactSpace, inferInstance⟩

def haarV (hE : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) : Measure (HA (Fv F v) σ J) :=
  haveI := (fv_grp σ J hE v).1
  haveI := (fv_grp σ J hE v).2.2.1
  haveI := (fv_grp σ J hE v).2.2.2.2
  Measure.haar

theorem haarV_isHaar (hE : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) : (haarV σ J hE v).IsHaarMeasure := by
  have := (fv_grp σ J hE v).1
  have := (fv_grp σ J hE v).2.2.1
  have := (fv_grp σ J hE v).2.2.2.2
  unfold haarV
  infer_instance

def haarB (hE : Module.finrank F E = 2) {a : ℕ} (X0 : Fin a → Fin M → E) : Measure (stabT (AF F) σ J X0) :=
  haveI := (stabT_facts σ J hE X0).1
  haveI := (stabT_facts σ J hE X0).2.1
  haveI := (stabT_facts σ J hE X0).2.2
  Measure.haar

theorem haarB_isHaar (hE : Module.finrank F E = 2) {a : ℕ} (X0 : Fin a → Fin M → E) :
    (haarB σ J hE X0).IsHaarMeasure := by
  have := (stabT_facts σ J hE X0).1
  have := (stabT_facts σ J hE X0).2.1
  have := (stabT_facts σ J hE X0).2.2
  unfold haarB
  infer_instance

end Loc

end Formalism.L2.SG.Pf.Meas

open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.Meas

open Formalism.L2.SG.Measures Formalism.L2.SG.AdBridge Formalism.L2.SG.MExistsCut Formalism.IndefR.Eqv.G5

variable (I : Formalism.MainNotions.S.AutInst) (hb : AdBridgeIso I)

def mG (μf : Measure I.Gf) [SigmaFinite μf] (r : ℕ) : MeasG I.cm.sig I.J r where
  μG := (I.muA μf).map (toHA I hb)
  μGinf := (Formalism.L2.SG.ProjRows.muInf I).map (toInfI I hb)
  μGf := μf.map (toFinI I hb)
  μGv := fun v => haarV I.cm.sig I.J (finrank_two I) v
  μB := fun X0 => haarB I.cm.sig I.J (finrank_two I) X0

section Norm

variable (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]

theorem muA_map_toHA :
    (I.muA μf).map (toHA I hb) =
      (((Formalism.L2.SG.ProjRows.muInf I).map (toInfI I hb)).prod (μf.map (toFinI I hb))).map
        (sA I.cm.sig I.J (finrank_two I)).symm := by
  obtain ⟨⟨g1, g2, g3, g4, g5⟩, ⟨h1, h2, h3, h4, h5⟩, ⟨k1, k2, k3, k4, k5⟩⟩ := grp_facts I.cm.sig I.J (finrank_two I)
  have hΦ : (I.muA μf).map (Phi I hb) =
      ((Formalism.L2.SG.ProjRows.muInf I).map (toInfI I hb)).prod (μf.map (toFinI I hb)) := by
    rw [Phi_eq]
    have : SigmaFinite (Formalism.L2.SG.ProjRows.muInf I) := inferInstance
    exact (Measure.map_prod_map (Formalism.L2.SG.ProjRows.muInf I) μf (map_continuous (eInf I hb)).measurable
      (map_continuous (eFin I hb)).measurable).symm
  rw [← hΦ, Measure.map_map (map_continuous (sA I.cm.sig I.J (finrank_two I)).symm).measurable
    (map_continuous (Phi I hb)).measurable]
  congr 1
  funext p
  show toHA I hb p = (sA I.cm.sig I.J (finrank_two I)).symm (sA I.cm.sig I.J (finrank_two I) (toHA I hb p))
  rw [ContinuousMulEquiv.symm_apply_apply]

theorem mG_norm (r : ℕ) : (mG I hb μf r).IsTextNorm := by
  obtain ⟨⟨g1, g2, g3, g4, g5⟩, ⟨h1, h2, h3, h4, h5⟩, ⟨k1, k2, k3, k4, k5⟩⟩ := grp_facts I.cm.sig I.J (finrank_two I)
  have hinf : ((Formalism.L2.SG.ProjRows.muInf I).map (toInfI I hb)).IsHaarMeasure := by
    show ((Formalism.L2.SG.ProjRows.muInf I).map (eInf I hb)).IsHaarMeasure
    have : (Formalism.L2.SG.ProjRows.muInf I).IsHaarMeasure := inferInstance
    have : BorelSpace I.Ginf := inferInstance
    have : IsTopologicalGroup I.Ginf := inferInstance
    exact ContinuousMulEquiv.isHaarMeasure_map _ (eInf I hb)
  have hfin : (μf.map (toFinI I hb)).IsHaarMeasure := by
    show (μf.map (eFin I hb)).IsHaarMeasure
    exact ContinuousMulEquiv.isHaarMeasure_map _ (eFin I hb)
  refine ⟨?_, hinf, hfin, fun v => haarV_isHaar I.cm.sig I.J (finrank_two I) v,
    fun X0 => haarB_isHaar I.cm.sig I.J (finrank_two I) X0, ?_⟩
  · show ((I.muA μf).map (toHA I hb)).IsHaarMeasure
    rw [muA_map_toHA]
    infer_instance
  · show ((I.muA μf).map (toHA I hb)).map (splitA I.cm.sig I.J) = _
    rw [muA_map_toHA, Measure.map_map (splitA_cont I.cm.sig I.J (Formalism.L2.SG.Pf.bas I)).measurable
      (map_continuous (sA I.cm.sig I.J (finrank_two I)).symm).measurable]
    have : (splitA I.cm.sig I.J ∘ (sA I.cm.sig I.J (finrank_two I)).symm) = id := by
      funext k
      show sA I.cm.sig I.J (finrank_two I) ((sA I.cm.sig I.J (finrank_two I)).symm k) = k
      exact ContinuousMulEquiv.apply_symm_apply _ k
    rw [this, Measure.map_id]
    rfl

end Norm

end Formalism.L2.SG.Pf.Meas

namespace Formalism.L2.SG.Pf

theorem multiplicity_G_exists : Formalism.L2.SG.MExistsCut.MGExists := by
  intro I μf _ _ r
  exact ⟨Formalism.L2.SG.Closed.AdBridgeIso_holds I, Meas.mG I _ μf r, Meas.mG_norm I _ μf r, rfl, rfl, rfl⟩

end Formalism.L2.SG.Pf

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.MExistsCut

namespace Formalism.L2.SG.Pf.Meas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cmExt (I : AutInst) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt I.F I.E I.cm.sig :=
  ⟨I.cm.totReal, I.cm.cmUnram.1, I.cm.deg2, fun τ x => I.cm.cmUnram.2.1 τ x⟩

theorem hermND (I : AutInst) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND I.cm.sig I.J := by
  refine ⟨fun i j => ?_, I.J_det⟩
  have h := congrFun (congrFun I.J_herm i) j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at h
  exact h

variable {D : D7}

theorem hform_crdA (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    A.ιE (Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← A.bas.sum_repr v, ← A.bas.sum_repr w]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, A.ιE_conj, RingEquiv.apply_symm_apply,
    A.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem hE_crdA (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE A.I.cm.sig A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w) =
      A.ιE.symm ((VS D).hT v w) := by
  show Formalism.UG.hform (starRingEnd A.I.E) A.I.J _ _ = _
  rw [← hform_crdA A v w, RingEquiv.symm_apply_apply]

theorem frame_std (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (u : D.what₂.Word) :
    (⟨eC A L, fC A L, zC A L u⟩ : Formalism.L2.SG.Sub.Frame A.I.E A.I.n D.R.rS).IsStd A.I.cm.sig A.I.J
      (((D.mem u).A.T : ℕ) : A.I.F) := by
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun a => ?_, ?_, ?_⟩
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE _ _ (crdOf A.I A.ιE A.bas (L.eX a)) (crdOf A.I A.ιE A.bas (L.eX b)) = 0
    rw [hE_crdA, L.ee, map_zero]
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE _ _ (crdOf A.I A.ιE A.bas (L.fY a)) (crdOf A.I A.ιE A.bas (L.fY b)) = 0
    rw [hE_crdA, L.ff, map_zero]
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE _ _ (crdOf A.I A.ιE A.bas (L.eX a)) (crdOf A.I A.ιE A.bas (L.fY b)) = _
    rw [hE_crdA, L.ef]
    split_ifs <;> simp
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE _ _ (crdOf A.I A.ιE A.bas (L.eX a)) (crdOf A.I A.ιE A.bas (L.zu u)) = 0
    rw [hE_crdA, (L.zu_orth u a).1, map_zero]
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE _ _ (crdOf A.I A.ιE A.bas (L.fY a)) (crdOf A.I A.ιE A.bas (L.zu u)) = 0
    rw [hE_crdA, (L.zu_orth u a).2, map_zero]
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE _ _ (crdOf A.I A.ιE A.bas (L.zu u)) (crdOf A.I A.ιE A.bas (L.zu u)) = _
    rw [hE_crdA, L.zu_norm]
    simp
  · exact Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero

end Formalism.L2.SG.Pf.Meas

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def MWExistsStd : Prop :=
  ∀ (I : AutInst) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (T : I.F), (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r).IsStd I.cm.sig I.J T →
    ∀ (muN muH : Measure I.Ginf),
    IsHaarOnSet I (Ninf I e z) muN → IsHaarOnSet I (Hset I (Set.range e ∪ Set.range f ∪ {z})) muH →
    ∃ W : Formalism.L2.SG.Measures.MeasW I.cm.sig I.J (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r), W.IsTextNorm ∧
      Formalism.L2.SG.Measures.amb W.μNinf = muN.map (toInfI I hb) ∧ Formalism.L2.SG.Measures.amb W.μHinf = muH.map (toInfI I hb)

theorem mWExistsStd_of (hC : Formalism.L2.SG.Pf.MeasCore.MWCore) (hT : Formalism.L2.SG.Pf.MeasInf.InfTransfer) :
    MWExistsStd := by
  intro I hb r e f z T hS muN muH hN hH
  obtain ⟨μNinf, μHinf, h1, h2, h3, h4⟩ := hT I hb r e f z T hS muN muH hN hH
  obtain ⟨W, hW, hW1, hW2⟩ := hC I.F I.E I.cm.sig I.n I.J r ⟨e, f, z⟩ T (Meas.cmExt I) (Meas.hermND I) hS μNinf μHinf h1 h2
  exact ⟨W, hW, by rw [hW1]; exact h3, by rw [hW2]; exact h4⟩

variable (D : D7)

theorem mExistsCore_of_std (hW : MWExistsStd) : MExistsCore D := by
  intro A L μf _ _ muN muH hN hH
  obtain ⟨hb, M, hM, h1, h2, h3⟩ := multiplicity_G_exists A.I μf D.R.rS
  choose W hW1 hW2 hW3 using fun u => hW A.I hb D.R.rS (eC A L) (fC A L) (zC A L u) _ (Meas.frame_std A L u)
    (muN u) (muH u) (hN u) (hH u)
  exact ⟨⟨M, hM, W, hW1⟩, hb, h1, h2, h3, fun u => ⟨hW2 u, hW3 u⟩⟩

theorem mExists_of_std (hW : MWExistsStd) : MExists D :=
  mExists_of_core D (mExistsCore_of_std D hW)

theorem mExists_of_cuts (hC : Formalism.L2.SG.Pf.MeasCore.MWCore) (hT : Formalism.L2.SG.Pf.MeasInf.InfTransfer) : MExists D :=
  mExists_of_std D (mWExistsStd_of hC hT)

end Formalism.L2.SG.Pf
