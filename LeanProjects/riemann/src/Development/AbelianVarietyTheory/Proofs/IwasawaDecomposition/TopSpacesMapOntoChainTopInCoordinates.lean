import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumsEqPairingsTopChainLiftsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section
namespace GlobalTheory.TopRead

section Gen
variable {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def constrOf (j : (Fin n → K) →ₛₗ[σ] V) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) (a : (Fin n → K) →ₛₗ[σ] W) : V →ₗ[ℂ] W :=
  (Module.Basis.mk hli hsp.ge).constr ℂ (fun k => a (Pi.single k 1))

theorem single_decomp (x : Fin n → K) : x = ∑ k, x k • (Pi.single k 1 : Fin n → K) := by
  ext i; simp [Finset.sum_apply, Pi.single_apply]

theorem semi_decomp {U : Type} [AddCommGroup U] [Module ℂ U] (f : (Fin n → K) →ₛₗ[σ] U) (x : Fin n → K) :
    f x = ∑ k, σ (x k) • f (Pi.single k 1) := by
  conv_lhs => rw [single_decomp x]
  simp only [map_sum, LinearMap.map_smulₛₗ]

theorem constrOf_apply (j : (Fin n → K) →ₛₗ[σ] V) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) (a : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    constrOf σ j hli hsp a (j x) = a x := by
  rw [semi_decomp σ j x, semi_decomp σ a x, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smul]
  unfold constrOf
  congr 1
  have : j (Pi.single k 1) = Module.Basis.mk hli hsp.ge k := (Module.Basis.mk_apply hli hsp.ge k).symm
  rw [this, Module.Basis.constr_basis]

theorem constrOf_range (j : (Fin n → K) →ₛₗ[σ] V) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) (a : (Fin n → K) →ₛₗ[σ] W) :
    LinearMap.range (constrOf σ j hli hsp a) = Submodule.span ℂ (Set.range a) := by
  unfold constrOf
  rw [Module.Basis.constr_range]
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [semi_decomp σ a x]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Gen
end GlobalTheory.TopRead

namespace GlobalTheory.TopRead
section Iso
variable {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem constrOf_props (j : (Fin n → K) →ₛₗ[σ] V) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) (a : (Fin n → K) →ₛₗ[σ] W)
    (S C : Submodule ℂ W) (ip : W → W → ℂ) (hC : PeterssonHilbertSpace.IsHermPos C ip) (hSC : S ≤ C)
    (hspan : Submodule.span ℂ (Set.range a) = S) (hip : ∀ x y, ip (a x) (a y) = inner ℂ (j x) (j y)) :
    Function.Injective (constrOf σ j hli hsp a) ∧ LinearMap.range (constrOf σ j hli hsp a) = S ∧
      ∀ v v', inner ℂ v v' = ip (constrOf σ j hli hsp a v) (constrOf σ j hli hsp a v') := by
  set J := constrOf σ j hli hsp a with hJ
  have hR : LinearMap.range J = S := by rw [hJ, constrOf_range, hspan]
  have mem : ∀ v, J v ∈ C := fun v => hSC (hR ▸ LinearMap.mem_range_self J v)
  have add1 : ∀ v₁ v₂ v', ip (J (v₁ + v₂)) (J v') = ip (J v₁) (J v') + ip (J v₂) (J v') := fun v₁ v₂ v' => by
    rw [map_add]; exact hC.add ⟨_, mem v₁⟩ ⟨_, mem v₂⟩ ⟨_, mem v'⟩
  have smul1 : ∀ (c : ℂ) v v', ip (J (c • v)) (J v') = starRingEnd ℂ c * ip (J v) (J v') := fun c v v' => by
    rw [map_smul]; exact hC.smul c ⟨_, mem v⟩ ⟨_, mem v'⟩
  have herm : ∀ v v', ip (J v) (J v') = starRingEnd ℂ (ip (J v') (J v)) := fun v v' =>
    (hC.herm ⟨_, mem v'⟩ ⟨_, mem v⟩).symm
  have add2 : ∀ v v₁ v₂, ip (J v) (J (v₁ + v₂)) = ip (J v) (J v₁) + ip (J v) (J v₂) := fun v v₁ v₂ => by
    rw [herm, add1, map_add, ← herm, ← herm]
  have smul2 : ∀ (c : ℂ) v v', ip (J v) (J (c • v')) = c * ip (J v) (J v') := fun c v v' => by
    rw [herm, smul1, map_mul, Complex.conj_conj, ← herm]
  let B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun v v' => ip (J v) (J v'))
    add1 smul1 add2 smul2
  let bas := Module.Basis.mk hli hsp.ge
  have hB : innerₛₗ ℂ = B := by
    refine LinearMap.ext_basis bas bas fun k l => ?_
    simp only [B, LinearMap.mk₂'ₛₗ_apply, bas, Module.Basis.mk_apply, hJ, constrOf_apply, hip]
    rfl
  have hI : ∀ v v', inner ℂ v v' = ip (J v) (J v') := fun v v' => by
    have := congrArg (fun f => f v v') hB
    simpa [B] using this
  refine ⟨fun v v' h => ?_, hR, hI⟩
  have h0 : ip 0 0 = 0 := by
    have := hC.smul 0 ⟨0, C.zero_mem⟩ ⟨0, C.zero_mem⟩
    simpa using this
  have : inner ℂ (v - v') (v - v') = (0 : ℂ) := by
    rw [hI, map_sub, h, sub_self, h0]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

end Iso
end GlobalTheory.TopRead

namespace GlobalTheory.TopRead

set_option maxHeartbeats 4000000 in

theorem top_read : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (b : Bool) (m : D.what₂.Tup → Mat1 D.what₂.LL G) (s : D.what₂.Tup → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tA : ∀ μ, Tie1 D.what₂.embLL (m μ) (s μ)) (hA : ∀ t, m (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t), ∃ jX : ∀ μ, (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX, (∀ μ, y.Us μ → Function.Injective (jX μ) ∧ LinearMap.range (jX μ) = (y.C F.lv2).CCXP b μ ∧ ∀ x x', ⟪x, x'⟫_ℂ = (y.C F.lv2).ipXP b μ (jX μ x) (jX μ x')) ∧ ∀ t, y.Us (y.tup t) → ∀ x, jX (y.tup t) (((tA (y.tup t)).cast (hA t)).j x) = R.toRealDat.cX.toMap R.toRealDat.prX ((R.toRealDat.HX t).e (R.toRealDat.jX t (rowForm A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t x))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH y b m s tA hA
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  have hT := GlobalTheory.T.classSums_eq_pairings_topChain_lifts D G Pl0 T A3.A Ks R.toRealDat F.lv2 y.tupT y.hm y.hTop y.hinj hB hP.keep.prX hH.ok.ok2
  have hHil := GlobalTheory.HilbertLevels.spaces_hilbert D G Pl0 T A3.A Ks R.toRealDat F.lv2 y.tupT y.hm y.hTop y.hinj hI hB
  let aS : ∀ t, (Fin (rDim D A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] (y.C F.lv2).AmbX := fun t =>
    ((R.toRealDat.cX.toMap R.toRealDat.prX).comp (R.toRealDat.HX t).e).comp
      ((R.toRealDat.jX t).comp (((A3.A.fam.R t).S.basis.equivFun.symm.toLinearMap).comp
        ((A3.A.fam.R t).S.lvlE (A3.A.fam.R t).r (A3.A.fam.lvl (levP F.lv2 b).1 (levP F.lv2 b).2).P
          (A3.A.fam.lvl (levP F.lv2 b).1 (levP F.lv2 b).2).ψ).mulVecLin))
  have haS : ∀ t x, aS t x = R.toRealDat.cX.toMap R.toRealDat.prX ((R.toRealDat.HX t).e (R.toRealDat.jX t
      (rowForm A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t x))) := fun t x => rfl
  let tie : ∀ t, Tie1 D.what₂.embLL (rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t) (s (y.tup t)) := fun t => (tA (y.tup t)).cast (hA t)
  let J' : ∀ t, (s (y.tup t)).A.T →ₗ[ℂ] (y.C F.lv2).AmbX := fun t =>
    constrOf D.what₂.embLL (tie t).j (tie t).forms.li (tie t).forms.span (aS t)
  classical
  let jX : ∀ μ, (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX := fun μ =>
    if h : y.tup (y.tupT μ) = μ then (cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) h) (J' (y.tupT μ)) : (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) else 0
  have hcast : ∀ t₁ t₂ (e : t₁ = t₂) (h : y.tup t₁ = y.tup t₂), (cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) h) (J' t₁) : (s (y.tup t₂)).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) = J' t₂ := by
    intro t₁ t₂ e h; subst e; rfl
  have hused : ∀ μ, y.Us μ → y.tup (y.tupT μ) = μ := by
    rintro μ (rfl | ⟨w, rfl⟩)
    · rw [← y.tup0, y.tupT_tup]
    · rw [y.tupT_tup]
  have hTb : ∀ μ, Submodule.span ℂ (Set.range (aS (y.tupT μ))) = (y.C F.lv2).CCXP b μ ∧ ∀ x x',
      (y.C F.lv2).ipXP b μ (aS (y.tupT μ) x) (aS (y.tupT μ) x') =
        D.what₂.embLL (Formalism.DivisionValues.hform (rH D A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 (y.tupT μ)) x x') := by
    intro μ
    cases b
    · exact (hT μ).2.1
    · exact (hT μ).1
  clear_value aS
  clear hT
  refine ⟨jX, fun μ hμ => ?_, fun t ht x => ?_⟩
  · have key : ∀ ν (h : ν = μ) (L : (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX), (Function.Injective L ∧ LinearMap.range L = (y.C F.lv2).CCXP b μ ∧ ∀ x x', ⟪x, x'⟫_ℂ = (y.C F.lv2).ipXP b μ (L x) (L x')) → (Function.Injective (cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) h) L : (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) ∧ LinearMap.range (cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) h) L : (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) = (y.C F.lv2).CCXP b μ ∧ ∀ x x', ⟪x, x'⟫_ℂ = (y.C F.lv2).ipXP b μ ((cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) h) L : (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) x) ((cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) h) L : (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) x')) := by
      intro ν h L hL; subst h; exact hL
    have e : jX μ = (cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) (hused μ hμ)) (J' (y.tupT μ)) : (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) := dif_pos (hused μ hμ)
    rw [e]
    refine key _ (hused μ hμ) (J' (y.tupT μ)) ?_
    have hHb := (hHil.1 b).2 μ
    exact constrOf_props D.what₂.embLL _ _ _ (aS (y.tupT μ)) _ _ _ hHb.2.2.1 hHb.2.1 (hTb μ).1 fun x x' => by
      rw [(hTb μ).2]
      exact ((tie (y.tupT μ)).forms.inner x x').symm
  · show jX (y.tup t) ((tie t).j x) = _
    have e : jX (y.tup t) = (cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) (hused _ ht)) (J' (y.tupT (y.tup t))) : (s (y.tup t)).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) := dif_pos (hused _ ht)
    rw [e, hcast _ _ (y.tupT_tup t) (hused _ ht)]
    exact (constrOf_apply D.what₂.embLL (tie t).j (tie t).forms.li (tie t).forms.span (aS t) x).trans (haS t x)

end GlobalTheory.TopRead
