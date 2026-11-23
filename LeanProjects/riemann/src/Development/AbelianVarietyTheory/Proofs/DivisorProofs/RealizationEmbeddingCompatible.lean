import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BigOn.Exp

section Generic

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}

def readExt (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
    (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c)) : L ⊗[O] M →+ (G → ℂ) :=
  TensorProduct.liftAddHom
    { toFun := fun b => (DistribSMul.toAddMonoidHom _ (eL b)).comp rd.toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun c b f => by
      change eL (c • b) • rd f = eL b • rd (c • f)
      rw [← algebraMap_smul (FractionRing O) c f, LinearMap.map_smulₛₗ rd, Algebra.smul_def c b, map_mul, hL, smul_smul, mul_comm]

variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))

theorem readExt_tmul (b : L) (f : M) : readExt rd eL hL (b ⊗ₜ f) = eL b • rd f := rfl

theorem readExt_smul (b : L) (x : L ⊗[O] M) : readExt rd eL hL (b • x) = eL b • readExt rd eL hL x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul a f =>
    rw [TensorProduct.smul_tmul', readExt_tmul, readExt_tmul, smul_eq_mul, map_mul, mul_smul]

theorem readExt_injective
    (hF : ∀ (n : ℕ) (v : Fin n → M), LinearIndependent (FractionRing O) v → LinearIndependent ℂ fun c => rd (v c)) :
    Function.Injective (readExt rd eL hL) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  let v := Module.finBasis (FractionRing O) M
  have key : ∀ x : L ⊗[O] M, ∃ d : O, d ≠ 0 ∧ ∃ c : _ → L, d • x = ∑ a, c a ⊗ₜ v a := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | add x y hx hy =>
      obtain ⟨d, hd, c, e⟩ := hx
      obtain ⟨d', hd', c', e'⟩ := hy
      refine ⟨d * d', mul_ne_zero hd hd', d' • c + d • c', ?_⟩
      rw [smul_add, mul_smul d d' y, mul_comm, mul_smul, e, e']
      simp [Finset.smul_sum, TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.smul_tmul']
    | tmul a f =>
      obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c
      choose y hy using hd
      refine ⟨d, nonZeroDivisors.coe_ne_zero d, fun c => y c • a, ?_⟩
      rw [← TensorProduct.tmul_smul]
      conv_lhs => rw [← v.sum_repr f]
      rw [Finset.smul_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing O) (y c), hy, smul_assoc]
  obtain ⟨d, hd, c, e⟩ := key x
  have h1 : ∑ a, eL (c a) • rd (v a) = 0 := by
    have := congrArg (readExt rd eL hL) e
    rw [← algebraMap_smul L d x, readExt_smul, hx, smul_zero, map_sum] at this
    exact this.symm
  have h2 : ∀ a, c a = 0 := fun a => eL.injective
    ((Fintype.linearIndependent_iff.1 (hF _ v v.linearIndependent) _ h1 a).trans (map_zero _).symm)
  have h3 : d • x = 0 := by simp [e, h2]
  have h4 : ∀ x : L ⊗[O] M,
      LinearMap.lTensor L (((algebraMap O (FractionRing O) d)⁻¹ • LinearMap.id :
        Module.End (FractionRing O) M).restrictScalars O) (d • x) = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add, hx, hy]
    | tmul a f =>
      rw [← TensorProduct.tmul_smul, LinearMap.lTensor_tmul]
      congr 1
      change (algebraMap O (FractionRing O) d)⁻¹ • d • f = f
      rw [← algebraMap_smul (FractionRing O) d f, inv_smul_smul₀ (by simpa using hd)]
  rw [← h4 x, h3, map_zero]

end Generic

set_option maxHeartbeats 4000000 in

theorem descent_of_reading : AtFit fun Fm x hx i p w j ρ hρ ν rd => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ (z : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w) ⊗[(Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w)] (Fm.D x i).nexp.Fm ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w))
    (n : ℕ) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL), (∀ k, y k ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _))) →
    rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) →
    incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w) ((Fm.ex x hx i).nch.k' w) z = ∑ k, a k • rd (y k) := by
  unfold AtFit AtTw AtPts
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j ρ hρ ν rd hfit hcan => ?_⟩⟩⟩
  intro e he1 he2 z n a y hy hz
  have hν : ν ≠ 0 := hfit.2.1.1
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  have hF : Faithful (rdAt p w j hρ ν) := GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ
    ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ν hν hU hW (Z.vec j) hK
  have hL : ∀ c : (Fm.D x i).ntw.O ((Fm.ex x hx i).nch.twI w),
      e (algebraMap _ (FractionRing ((Fm.ex x hx i).nch.Oe w)) c) =
        ρ.e ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) (algebraMap _ (FractionRing _) c) := fun c => by
    rw [IsScalarTower.algebraMap_apply _ ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)),
      IsScalarTower.algebraMap_apply _ ((Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w)) ((Fm.ex x hx i).nch.Oe w),
      he2, hρ.ek_e]
    rfl
  set R := readExt (rdAt p w j hρ ν) e hL with hRdef
  have hRinj : Function.Injective R := readExt_injective _ e hL hF
  have hinc : ∀ z, R (incl (Fm.D x i).nexp ((Fm.ex x hx i).nch.twI w) _ ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.Oe w)
      ((Fm.ex x hx i).nch.k' w) z) = rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
    | tmul c f =>
      rw [rdK_tmul, ← he2]
      rfl
  have hgen : ∀ f : NX.FmK p.Sx ((j : ℕ) + 1), R (rd ((p.nexp.fi j).e (Subtype.val f))) =
      ν⁻¹ • adForm (R2 p) j ((p.nexp.fi j).e (Subtype.val f)) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun f => by
    rw [hcan f, hRdef, readExt_tmul, map_one, one_smul]
    erw [realRd_tmul]
    erw [map_one, mul_one]
    rfl
  have hA0 : adForm (R2 p) j 0 (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) = 0 := by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ 0) (p.v₀ j _) = 0
    rw [map_zero, map_zero]
    rfl
  have hAadd : ∀ u v, adForm (R2 p) j (u + v) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) + adForm (R2 p) j v (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u v => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (u + v)) (p.v₀ j _) = _
    rw [map_add, map_add]
    rfl
  have hs : sg0 (Fm.D x i) p.P.A3.A = (Fm.D x i).what₂.embLL := sgAt_mk _ (R2 p).hv0
  have hAsmul : ∀ (c : (Fm.D x i).what₂.LL) u, adForm (R2 p) j (c • u) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) =
      (Fm.D x i).what₂.embLL c • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun c u => by
    change ((R2 p).HW j _).e (((R2 p).FW j).j _ (c • u)) (p.v₀ j _) = _
    rw [LinearMap.map_smulₛₗ, map_smul]
    exact congrArg (fun s : ℂ => s • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A))) (DFunLike.congr_fun hs c)
  have hrd : ∀ u ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)),
      R (rd u) = ν⁻¹ • adForm (R2 p) j u (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨f, hf, rfl⟩ := hu
      exact hgen ⟨f, hf⟩
    | zero =>
      erw [LinearMap.map_zero rd]
      rw [AddMonoidHom.map_zero R]
      erw [hA0]
      rw [smul_zero]
    | add u v _ _ hu hv =>
      erw [LinearMap.map_add rd]
      rw [AddMonoidHom.map_add R, hu, hv]
      erw [hAadd]
      rw [smul_add]
    | smul c u _ hu =>
      erw [LinearMap.map_smulₛₗ rd]
      rw [hRdef, readExt_smul, ← hRdef, hu, he1]
      erw [hAsmul]
      rw [smul_comm]
  apply hRinj
  rw [hinc, hz, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← algebraMap_smul (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k) (rd (y k)), hRdef, readExt_smul, ← hRdef,
    hrd _ (hy k), mul_smul]

end GlobalTheory.BigOn.Exp
