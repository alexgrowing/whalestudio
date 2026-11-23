import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Formalism.LocalToGlobal.Columns.RecLevelTop

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceCoord

theorem isOpen_isCompact_of_comm {K : Type} [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K]
    {m n : ℕ} (O : AddSubgroup K) (ho : IsOpen (O : Set K)) (hc : IsCompact (O : Set K))
    (A : AddSubgroup (Matrix (Fin m) (Fin n) K)) {k M : ℕ} (hk : 0 < k) (hM : 0 < M)
    (h1 : ∀ y : Matrix (Fin m) (Fin n) K, (∀ i j, y i j ∈ O) → k • y ∈ A)
    (h2 : ∀ y ∈ A, ∀ i j, (M : K) * y i j ∈ O) :
    IsOpen (A : Set (Matrix (Fin m) (Fin n) K)) ∧ IsCompact (A : Set (Matrix (Fin m) (Fin n) K)) := by
  have hk' : (k : K) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hM' : (M : K) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hU : IsOpen {y : Matrix (Fin m) (Fin n) K | ∀ i j, (k : K)⁻¹ * y i j ∈ O} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      ho.preimage (f := fun y : Matrix (Fin m) (Fin n) K => (k : K)⁻¹ * y i j) (by fun_prop)
  have hA : IsOpen (A : Set (Matrix (Fin m) (Fin n) K)) := by
    refine A.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (hU.mem_nhds fun i j => by simp) fun y hy => ?_)
    have := h1 ((k : K)⁻¹ • y) hy
    rwa [← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ hk', one_smul] at this
  refine ⟨hA, ?_⟩
  have hC : IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin n => (fun x => (M : K)⁻¹ * x) '' O) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc.image (by fun_prop)
  refine IsCompact.of_isClosed_subset (s := Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin n => (fun x => (M : K)⁻¹ * x) '' O) hC (A.isClosed_of_isOpen hA) fun y hy i _ j _ => ⟨_, h2 y hy i j, ?_⟩
  simp only [inv_mul_cancel_left₀ hM']

def mulHomeo {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {m n : ℕ} (P : GL (Fin m) K)
    (Q : GL (Fin n) K) : Matrix (Fin m) (Fin n) K ≃ₜ Matrix (Fin m) (Fin n) K where
  toFun x := P.val * x * Q.val
  invFun x := (P⁻¹).val * x * (Q⁻¹).val
  left_inv x := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv x := by
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

variable {D : D7}

theorem toEAf_mem {w : AE D} (hw : finPart D w ∈ intAE D) : toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have key : ∀ z ∈ intAE D, Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E z ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, rfl⟩ := hz
      exact GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  exact key _ hw

variable {v : FinPl D} {S T : HSp D} {e : AE D} {π : AE D →+* Fv D.host.F v}

theorem exists_half (hπ : GlobalTheory.SplitHecke.Chart e v π) (he : e * e = e) (h1 : π e = 1)
    (y : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) : ∃ t : WO S T, IsHalf e t ∧ t.map π = y := by
  choose s hs using hπ.1
  refine ⟨Matrix.of fun i j => e * s (y i j), fun i j => ?_, Matrix.ext fun i j => ?_⟩
  · rw [Matrix.of_apply, ← mul_assoc, he]
  · rw [Matrix.map_apply, Matrix.of_apply, RingHom.map_mul, h1, one_mul, hs]

theorem bijOn_map (hπ : GlobalTheory.SplitHecke.Chart e v π) (he : e * e = e) (h1 : π e = 1) :
    Set.BijOn (fun t : WO S T => t.map π) {t | IsHalf e t} Set.univ := by
  refine ⟨Set.mapsTo_univ _ _, fun x hx y hy h => Matrix.ext fun i j => ?_, fun y _ => exists_half hπ he h1 y⟩
  have h0 : π (x i j - y i j) = 0 := by
    rw [RingHom.map_sub, sub_eq_zero]; exact congrFun (congrFun h i) j
  rw [hπ.2.1, mul_sub, hx i j, hy i j, sub_eq_zero] at h0
  exact h0

theorem isOpen_isCompact_map {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : Submodule.IsLattice D.host.E ΛS)
    (hT : Submodule.IsLattice D.host.E ΛT) (hπ : GlobalTheory.SplitHecke.Chart e v π) (he : e * e = e) (h1 : π e = 1)
    (hinf : infPart D e = 0) :
    IsOpen ((fun t : WO S T => t.map π) '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t}) ∧
    IsCompact ((fun t : WO S T => t.map π) '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t}) := by
  haveI : CharZero (Fv D.host.F v) := charZero_of_injective_algebraMap (algebraMap D.host.F _).injective
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.fg hT.fg
  obtain ⟨k, hk, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS hT
  have hset : ((fun t : WO S T => t.map π) '' {t | t ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf e t}) =
      (((latO S T ΛS ΛT fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T e).map π.toAddMonoidHom.mapMatrix :
        AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v))) := by
    rw [AddSubgroup.coe_map]
    congr 1
    ext t
    exact and_congr_right fun _ => GlobalTheory.PlaceModel.isHalf_iff S T
  rw [hset]
  refine isOpen_isCompact_of_comm (v.adicCompletionIntegers D.host.F).toSubring.toAddSubgroup
    (Valued.isOpen_valuationSubring _) (isCompact_iff_compactSpace.2 (Formalism.L2.Col.rlt_compact_int v)) _ hk hM
    (fun y hy => ?_) ?_
  · obtain ⟨t, ht, rfl⟩ := exists_half hπ he h1 y
    refine ⟨k • t, ⟨hmul t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht) fun i j => toEAf_mem ?_,
      nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 ht) k⟩, map_nsmul _ _ _⟩
    rw [← ht i j]
    exact (hπ.2.2.2 _).2 (GlobalTheory.SplitHecke.isInt_Ov.2 (hy i j))
  · rintro _ ⟨t, ⟨ht, ht'⟩, rfl⟩ i j
    have h2 : toEAf D ((M : AE D) * t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [RingHom.map_mul, map_natCast]; exact hden t ht i j
    have h3 : finPart D (e * ((M : AE D) * t i j)) ∈ intAE D := by
      rw [mul_left_comm, (GlobalTheory.PlaceModel.isHalf_iff S T).2 ht' i j]
      exact GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h2
    have h4 := GlobalTheory.SplitHecke.isInt_Ov.1 ((hπ.2.2.2 _).1 h3)
    rw [RingHom.map_mul, map_natCast] at h4
    exact h4

theorem infPart_split (he : IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨a1, a2, v, ε, ⟨β, rfl, -⟩, a3⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have hi' : e * (e + cA D e) = e := by rw [mul_add, a1, a2, add_zero]
  rw [← hi', a3, RingHom.map_mul, h0, mul_zero]

theorem isCoord_mapCo : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), IsCoord e (latO S T ΛS ΛT fun _ => True) (mapCo φ S T BS BT) ∧ ∀ (g : GA D S) (h : GA D T) (t : WO S T), mapCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ T BT h)⁻¹).val * mapCo φ S T BS BT t * (grpCo φ S BS g).val := by
  intro D S T ΛS ΛT hS hT v φ e he BS BT
  have hπ := (GlobalTheory.T.splitProjAdeleComponent_chart_properties D v φ e he).1
  have hcomp : mapCo φ S T BS BT = mulHomeo BT⁻¹ BS ∘ fun t : WO S T => t.map (rdA φ) := rfl
  have hoc := isOpen_isCompact_map (S := S) (T := T) hS.1 hT.1 hπ he.1.1 he.2.2 (infPart_split he.1)
  refine ⟨⟨fun x y => ?_, ?_, ?_, ?_⟩, fun g h t => ?_⟩
  · unfold mapCo
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]
  · rw [hcomp]
    exact (Set.bijOn_univ.2 (mulHomeo BT⁻¹ BS).bijective).comp (bijOn_map hπ he.1.1 he.2.2)
  · rw [hcomp, Set.image_comp]
    exact (mulHomeo BT⁻¹ BS).isOpenMap _ hoc.1
  · rw [hcomp, Set.image_comp]
    exact hoc.2.image (mulHomeo BT⁻¹ BS).continuous
  · have e1 : ((grpCo φ T BT h)⁻¹).val = (BT⁻¹).val * (mt T h⁻¹).map (rdA φ) * BT.val := by
      have : (grpCo φ T BT h)⁻¹ = grpCo φ T BT h⁻¹ := by
        unfold grpCo
        rw [map_inv, map_inv, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, mul_assoc]
      rw [this]; rfl
    have e2 : (grpCo φ S BS g).val = (BS⁻¹).val * (mt S g).map (rdA φ) * BS.val := rfl
    rw [e1, e2]
    unfold mapCo actO
    rw [inv_inv, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
    rw [← Matrix.mul_assoc BT.val, Units.mul_inv, Matrix.one_mul]

end GlobalTheory.PlaceCoord

end
