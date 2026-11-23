import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WittIndexAddOfIsWittLower

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitStab

open scoped Matrix

theorem exists_basis_adapted {k : Type} [Field k] {r : ℕ} (U : Submodule k (Fin r → k)) :
    ∃ b : Module.Basis (Fin r) k (Fin r → k),
      (∀ j : Fin r, j.val < Module.finrank k U → b j ∈ U) ∧
      ∀ x ∈ U, ∀ i : Fin r, Module.finrank k U ≤ i.val → b.repr x i = 0 := by
  obtain ⟨C, hC⟩ := U.exists_isCompl
  set a := Module.finrank k U with ha
  have hsum : a + Module.finrank k C = r := by
    rw [ha, Submodule.finrank_add_eq_of_isCompl hC, Module.finrank_fin_fun]
  have hCr : Module.finrank k C = r - a := by omega
  let bU : Module.Basis (Fin a) k U := Module.finBasisOfFinrankEq k U rfl
  let bC : Module.Basis (Fin (r - a)) k C := Module.finBasisOfFinrankEq k C hCr
  let B : Module.Basis (Fin a ⊕ Fin (r - a)) k (Fin r → k) := (bU.prod bC).map (U.prodEquivOfIsCompl C hC)
  let e : Fin a ⊕ Fin (r - a) ≃ Fin r := finSumFinEquiv.trans (finCongr (by omega))
  refine ⟨B.reindex e, fun j hj => ?_, fun x hx i hi => ?_⟩
  · have hj' : e.symm j = Sum.inl ⟨j.val, hj⟩ := by
      rw [Equiv.symm_apply_eq]; ext; simp [e]
    rw [Module.Basis.reindex_apply, hj']
    simp [B]
  · have hi' : e.symm i = Sum.inr ⟨i.val - a, by omega⟩ := by
      rw [Equiv.symm_apply_eq]; ext; simp [e]; omega
    rw [Module.Basis.repr_reindex_apply, hi']
    simp only [B, Module.Basis.map_repr, LinearEquiv.trans_apply]
    rw [show x = ((⟨x, hx⟩ : U) : Fin r → k) from rfl, Submodule.prodEquivOfIsCompl_symm_apply_left,
      Module.Basis.prod_repr_inr]
    simp

theorem inConjParabolic_of_maps {k : Type} [Field k] {r : ℕ} (H : Subgroup (GL (Fin r) k))
    (U : Submodule k (Fin r → k)) (hH : ∀ p ∈ H, ∀ u ∈ U, (p : Matrix (Fin r) (Fin r) k) *ᵥ u ∈ U) :
    InConjParabolic H (Module.finrank k U) := by
  obtain ⟨b, hb1, hb2⟩ := exists_basis_adapted U
  let φ : (Fin r → k) ≃ₗ[k] (Fin r → k) := b.equivFun.symm
  let g : GL (Fin r) k :=
    ⟨LinearMap.toMatrix' φ.toLinearMap, LinearMap.toMatrix' φ.symm.toLinearMap,
      by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  refine ⟨g, fun p hp i j hj hi => ?_⟩
  have key : ((g⁻¹ * p * g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) i j =
      b.repr ((p : Matrix (Fin r) (Fin r) k) *ᵥ b j) i := by
    have := congrFun (Matrix.mulVec_single_one ((g⁻¹ * p * g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) j) i
    rw [Matrix.col_apply] at this
    rw [← this, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change (LinearMap.toMatrix' φ.symm.toLinearMap *ᵥ ((p : Matrix (Fin r) (Fin r) k) *ᵥ
      (LinearMap.toMatrix' φ.toLinearMap *ᵥ Pi.single j 1))) i = _
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    simp [φ]
  rw [key]
  exact hb2 _ (hH p hp _ (hb1 j hj)) i hi

end GlobalTheory.SplitStab

namespace GlobalTheory.SplitStab

open scoped Matrix TensorProduct
open GlobalTheory.AutFunCompare (colSpan exists_colSpan mem_extSub_colSpan)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : HeightOneSpectrum (𝓞 F)}

omit [NumberField E] in

theorem splitVec_map_inclR_mulVec (τ : E →ₐ[F] Fv F v) {n r : ℕ} (C : Matrix (Fin n) (Fin r) E)
    (a : Fin r → Fv F v ⊗[F] E) :
    splitVec τ ((C.map (inclR (Fv F v))) *ᵥ a) = (C.map τ) *ᵥ fun k => splitProj τ (a k) := by
  funext i
  simp [splitVec, Matrix.mulVec, dotProduct, map_sum, map_mul, splitProj_inclR]

end GlobalTheory.SplitStab

namespace GlobalTheory.SplitStab

open scoped Matrix TensorProduct
open GlobalTheory.AutFunCompare (colSpan exists_colSpan mem_extSub_colSpan)

theorem inConjParabolic_parab (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (W : Submodule D.host.E V.V) :
    InConjParabolic ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v) W).map
        (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) (Module.finrank D.host.E W) := by
  obtain ⟨r', C, hC, rfl⟩ := exists_colSpan V W
  have hfin : Module.finrank D.host.E (colSpan V C) = r' := by
    have hli : LinearIndependent D.host.E fun k => GlobalTheory.AutFunCompare.vecOf V (Cᵀ k) :=
      hC.map' (V.frame.equivFun.symm.toLinearMap) (LinearEquiv.ker _)
    rw [colSpan, finrank_span_eq_card hli]
    simp
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective C.mulVecLin
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 hC))
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin r') (Fin V.rank) D.host.E, L * C = 1 :=
    ⟨LinearMap.toMatrix' l, by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]; exact hl⟩
  set τ := s.emb
  let U : Submodule (Fv D.host.F v) (Fin V.rank → Fv D.host.F v) := LinearMap.range (C.map τ).mulVecLin
  have hinj : Function.Injective (C.map τ).mulVecLin := fun c d e => by
    have h1 : (L.map τ * C.map τ) *ᵥ c = (L.map τ * C.map τ) *ᵥ d := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; exact congrArg _ e
    have hm : (L * C).map τ = L.map τ * C.map τ := Matrix.map_mul (f := (τ : D.host.E →+* Fv D.host.F v))
    rwa [← hm, hL, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.one_mulVec, Matrix.one_mulVec] at h1
  have hU : Module.finrank (Fv D.host.F v) U = r' := by
    rw [LinearMap.finrank_range_of_inj hinj]; simp
  have hmaps : ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v) (colSpan V C), ∀ u ∈ U,
      ((splitHom D.sp.cm.sig V.gram τ x : GL (Fin V.rank) (Fv D.host.F v)) : Matrix _ _ _) *ᵥ u ∈ U := by
    rintro x hx _ ⟨c, rfl⟩
    let y : Fin V.rank → Fv D.host.F v ⊗[D.host.F] D.host.E :=
      (C.map (inclR (Fv D.host.F v))) *ᵥ fun k => algebraMap (Fv D.host.F v) _ (c k)
    have hy : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub V (Fv D.host.F v) (colSpan V C) :=
      (mem_extSub_colSpan V _ C y).2 ⟨_, rfl⟩
    obtain ⟨a', ha'⟩ := (mem_extSub_colSpan V _ C _).1 (GlobalTheory.Cusp.mem_parab_iff_maps.1 hx y hy)
    have e1 : splitVec τ y = (C.map τ) *ᵥ c := by
      rw [splitVec_map_inclR_mulVec]
      congr 1
      funext k
      exact (splitProj τ).commutes (c k)
    have e2 := splitVec_matHom_mulVec τ x y
    change splitVec τ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act D.sp.cm V x y) = _ at e2
    rw [ha', splitVec_map_inclR_mulVec, e1] at e2
    exact ⟨fun k => splitProj τ (a' k), e2⟩
  obtain ⟨g, hg⟩ := inConjParabolic_of_maps
    ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v) (colSpan V C)).map (splitHom D.sp.cm.sig V.gram τ)) U
    (by
      rintro _ ⟨x, hx, rfl⟩ u hu
      exact hmaps x hx u hu)
  have hdim : Module.finrank D.host.E (colSpan V C) = Module.finrank (Fv D.host.F v) U := hfin.trans hU.symm
  rw [hdim]
  refine ⟨s.basis⁻¹ * g, fun p hp => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hp
  have := hg _ ⟨x, hx, rfl⟩
  convert this using 1
  change (s.basis⁻¹ * g)⁻¹ * splitEquivIn s.cm s.herm s.emb s.basis x * (s.basis⁻¹ * g) = _
  rw [splitEquivIn_apply]
  change _ = g⁻¹ * splitHom D.sp.cm.sig V.gram s.emb x * g
  group

end GlobalTheory.SplitStab

namespace GlobalTheory.SplitStab

theorem splitStab : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (W : Submodule D.host.E V.V), GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W →
    InConjParabolic ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v) W).map
        (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) (Module.finrank D.host.E W) ∧
      InConjParabolic ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v) W).map
        (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) (V.rank - Module.finrank D.host.E W) := by
  intro D V v s W _
  refine ⟨inConjParabolic_parab D V v s W, ?_⟩
  have h := inConjParabolic_parab D V v s (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W)
  have hr : Module.finrank D.host.E (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W) = V.rank - Module.finrank D.host.E W := by
    have := GlobalTheory.Cusp.WittIdx.finrank_add_finrank_perp W
    omega
  rw [hr] at h
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun p hp => hg p (Subgroup.map_mono GlobalTheory.Cusp.parab_le_perp hp)⟩

end GlobalTheory.SplitStab
