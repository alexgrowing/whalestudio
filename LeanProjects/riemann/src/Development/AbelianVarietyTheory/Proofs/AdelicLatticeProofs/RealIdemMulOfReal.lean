import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmooth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitScalar

open GlobalTheory.LatVac GlobalTheory.DualPairCheck

variable {D : D7}

theorem gramInv_star (S : HSp D) (i j : Fin S.rank) : star (S.gram⁻¹ i j) = S.gram⁻¹ j i := by
  have h : S.gramᴴ = S.gram := Matrix.ext fun i j => GlobalTheory.LatVac.gram_star S j i
  have h2 : (S.gram⁻¹)ᴴ = S.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, h]
  exact congrFun (congrFun h2 j) i

theorem hO_herm (S T : HSp D) (x y : WO S T) : cA D (hO S T x y) = hO S T y x := by
  unfold hO
  simp only [map_sum, RingHom.map_mul, cA_incA, GlobalTheory.DualPairCheck.cA_cA, gramInv_star, GlobalTheory.LatVac.gram_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem symplO_skew (S T : HSp D) (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  unfold symplO
  rw [← trace_cA, RingHom.map_mul, cA_incA, star_purely_imaginary_eq_neg, hO_herm, RingHom.map_neg, neg_mul, map_neg]

theorem hO_smul_left (S T : HSp D) (a : AE D) (x y : WO S T) : hO S T (a • x) y = a * hO S T x y := by
  simp only [hO, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem hO_smul_right (S T : HSp D) (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  simp only [hO, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem symplO_smul (S T : HSp D) (a : AE D) (x y : WO S T) :
    symplO S T (a • x) y = symplO S T x (cA D a • y) := by
  rw [symplO, symplO, hO_smul_left, hO_smul_right, GlobalTheory.DualPairCheck.cA_cA]

theorem symplO_zero_left (S T : HSp D) (y : WO S T) : symplO S T 0 y = 0 := by
  rw [← symplHom_apply, map_zero]; rfl

theorem symplO_zero_right (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  rw [← symplHom_apply, map_zero]

theorem symplO_sub_left (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x - x') y = symplO S T x y - symplO S T x' y := by
  rw [← symplHom_apply, map_sub]; rfl

theorem isHalf_iff {m n : ℕ} (e : AE D) (u : Mx D m n) : IsHalf e u ↔ e • u = u :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem symplO_eq_zero (S T : HSp D) {a b : AE D} (hab : cA D a * b = 0) {x y : WO S T} (hx : IsHalf a x)
    (hy : IsHalf b y) : symplO S T x y = 0 := by
  rw [← (isHalf_iff _ _).1 hx, ← (isHalf_iff _ _).1 hy, symplO_smul, smul_smul, hab, zero_smul, symplO_zero_right]

theorem symplOH_add_left (S T : HSp D) (x x' y : WO S T) :
    symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  simp only [symplOH, symplO_add_left, mul_add]

theorem symplOH_add_right (S T : HSp D) (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  simp only [symplOH, symplO_add_right, mul_add]

theorem symplOH_add_self (S T : HSp D) (x y : WO S T) :
    symplOH S T x y + symplOH S T x y = symplO S T x y := by
  rw [symplOH, ← add_mul, ← map_add, add_halves, map_one, one_mul]

theorem symplOH_skew (S T : HSp D) (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  rw [symplOH, symplOH, symplO_skew, mul_neg]

theorem heisO_heisO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w w' : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (heisO ψ S T w' f) = ψ (symplOH S T w w') • heisO ψ S T (w + w') f := by
  funext u
  simp only [heisO, Pi.smul_apply, smul_eq_mul, symplOH_add_left, symplOH_add_right, AddChar.map_add_eq_mul,
    add_assoc]
  ring

theorem heisO_add_of_orth (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {w w' : WO S T} (h : symplO S T w w' = 0)
    (f : WO S T → ℂ) : heisO ψ S T (w + w') f = heisO ψ S T w (heisO ψ S T w' f) := by
  rw [heisO_heisO, symplOH, h, mul_zero, AddChar.map_zero_eq_one, one_smul]

theorem heisO_comm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w w' : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (heisO ψ S T w' f) = ψ (symplO S T w w') • heisO ψ S T w' (heisO ψ S T w f) := by
  rw [heisO_heisO, heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, add_comm w' w, ← symplOH_add_self,
    symplOH_skew S T w w', add_neg_cancel_right]

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext u
  simp only [heisO, symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]

def heisL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) : Module.End ℂ (WO S T → ℂ) where
  toFun := heisO ψ S T w
  map_add' f g := by funext u; simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by funext u; simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem heisL_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisL ψ S T w f = heisO ψ S T w f := rfl

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (c • f) = c • heisO ψ S T w f := (heisL ψ S T w).map_smul c f

theorem heisO_sum (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) {ι : Type} (s : Finset ι)
    (f : ι → WO S T → ℂ) : heisO ψ S T w (∑ i ∈ s, f i) = ∑ i ∈ s, heisO ψ S T w (f i) :=
  map_sum (heisL ψ S T w) f s

def realIdem (D : D7) : AE D := pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E)

theorem cA_realIdem : cA D (realIdem D) = realIdem D := by
  show pairA D.host.F 1 0 ⊗ₜ[D.host.F] D.sp.cm.sig (1 : D.host.E) = _
  rw [map_one]; rfl

theorem infPart_realIdem : infPart D (realIdem D) = 1 := rfl

theorem finPart_realIdem : finPart D (realIdem D) = 0 := TensorProduct.zero_tmul _ _

theorem adele_ext {a b : AE D} (h1 : infPart D a = infPart D b) (h2 : finPart D a = finPart D b) : a = b :=
  sub_eq_zero.1 (GlobalTheory.FockCompare.RealChart.adele_tensor_ext (a - b)
    (show infPart D (a - b) = 0 by rw [RingHom.map_sub, h1, sub_self])
    (show finPart D (a - b) = 0 by rw [RingHom.map_sub, h2, sub_self]))

theorem realIdem_mul_of_fin {a : AE D} (h : infPart D a = 0) : realIdem D * a = 0 :=
  adele_ext (by rw [RingHom.map_mul, h, mul_zero, RingHom.map_zero])
    (by rw [RingHom.map_mul, finPart_realIdem, zero_mul, RingHom.map_zero])

theorem realIdem_mul_of_real {a : AE D} (h : finPart D a = 0) : realIdem D * a = a :=
  adele_ext (by rw [RingHom.map_mul, infPart_realIdem, one_mul])
    (by rw [RingHom.map_mul, h, mul_zero])

theorem symplO_real_fin (S T : HSp D) {x y : WO S T} (hx : x.map (finPart D) = 0) (hy : y.map (infPart D) = 0) :
    symplO S T x y = 0 := by
  have h1 : realIdem D • x = x := Matrix.ext fun i j => realIdem_mul_of_real (congrFun (congrFun hx i) j)
  have h2 : realIdem D • y = 0 := Matrix.ext fun i j => realIdem_mul_of_fin (congrFun (congrFun hy i) j)
  rw [← h1, symplO_smul, cA_realIdem, h2, symplO_zero_right]

theorem latO_fin {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) : u.map (infPart D) = 0 := by
  refine latO_induction (p := fun u => u.map (infPart D) = 0) (fun α _ M _ => ?_) ?_ (fun x y hx hy => ?_)
    (fun x hx => ?_) hu
  · ext i j
    exact TensorProduct.zero_tmul _ _
  · ext i j
    exact (infPart D).map_zero
  · ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
    show infPart D (x i j + y i j) = 0
    rw [RingHom.map_add, h1, h2, add_zero]
  · ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    show infPart D (-x i j) = 0
    rw [RingHom.map_neg, h1, neg_zero]

theorem isSplitIdem_conj {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, h3, h4⟩ := he
  refine ⟨by rw [← RingHom.map_mul, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2], v, ε, h3, ?_⟩
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h4]

theorem infPart_splitIdem {e : AE D} (he : IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h4⟩ := he
  have h5 : infPart D (e + cA D e) = 0 := by
    rw [h4]
    exact TensorProduct.zero_tmul _ _
  have h6 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
  rw [h6, RingHom.map_mul, h5, mul_zero]

theorem half_fin {m n : ℕ} {e : AE D} (he : IsSplitIdem D e) {u : Mx D m n} (hu : IsHalf e u) :
    u.map (infPart D) = 0 := by
  ext i j
  show infPart D (u i j) = 0
  rw [← hu i j, RingHom.map_mul, infPart_splitIdem he, zero_mul]

theorem continuous_symplO (S T : HSp D) {X : Type} [TopologicalSpace X] {x y : X → WO S T} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplO S T (x t) (y t) := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hy' : ∀ i j, Continuous fun t => cA D (y t i j) := fun i j =>
    GlobalTheory.FockCompare.ThetaCont.continuous_conj.comp ((continuous_apply j).comp ((continuous_apply i).comp hy))
  have hx' : ∀ i j, Continuous fun t => x t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hx)
  refine ht.comp (continuous_const.mul ?_)
  exact continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ =>
      continuous_finset_sum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul (hx' _ _)

theorem exists_nsmul_mem {m n : ℕ} (U : AddSubgroup (Mx D m n)) (hU : IsOpen (U : Set (Mx D m n))) {y : Mx D m n}
    (hy : y.map (infPart D) = 0) : ∃ N : ℕ, 0 < N ∧ N • y ∈ U := by
  let φ : Af D.host.F → Mx D m n := fun α => Matrix.of fun i j => pairA D.host.F 0 α • y i j
  have hp : Continuous fun α : Af D.host.F => pairA D.host.F 0 α := continuous_const.prodMk continuous_id
  have hφ : Continuous φ := continuous_pi fun i => continuous_pi fun j => hp.smul continuous_const
  have h0 : φ 0 = 0 := Matrix.ext fun i j => zero_smul (AF D.host.F) (y i j)
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele D.host.F (φ ⁻¹' U)
    (hφ.continuousAt.preimage_mem_nhds (hU.mem_nhds (h0 ▸ U.zero_mem)))
  refine ⟨N, hN, ?_⟩
  have h1 : φ (N • 1) ∈ U := h 1 fun v => one_mem _
  have h2 : φ (N • 1) = N • y := by
    refine Matrix.ext fun i j => ?_
    have e1 : pairA D.host.F 0 (N • 1) = N • (1 - pairA D.host.F 1 0) :=
      Prod.ext (show (0 : Ainf D.host.F) = N • (1 - 1) by rw [sub_self, smul_zero])
        (show (N • 1 : Af D.host.F) = N • (1 - 0) by rw [sub_zero])
    have e2 : pairA D.host.F 1 0 • y i j = 0 := by
      rw [Algebra.smul_def]
      exact realIdem_mul_of_fin (congrFun (congrFun hy i) j)
    show pairA D.host.F 0 (N • 1) • y i j = N • y i j
    rw [e1, smul_assoc, sub_smul, one_smul, e2, sub_zero]
  rwa [h2] at h1

end GlobalTheory.SplitScalar

end
