import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkThetaStatementFamily
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.ZeroInjectionMemFourthPower

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions

namespace Formalism.L2.Ker.KS.Lat

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.Th1.H
open Formalism.L2.AlgTh (hSc)
open Formalism.L2.Th1.F (cmTheta)

section Gen

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [FiniteDimensional ℂ W] {H : Sesq V} {H' : Sesq W} (g : V ≃ₗ[ℂ] W)

theorem img_comap (Λ' : AddSubgroup W) :
    imgLat (g : V →ₗ[ℂ] W) (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) = Λ' := by
  unfold Formalism.L2.Th1.H.imgLat
  exact AddSubgroup.map_comap_eq_self_of_surjective g.surjective _

theorem selfDual_comap (hI : IsIsom H H' (g : V →ₗ[ℂ] W)) {Λ' : AddSubgroup W} (h : IsSelfDual H' Λ') :
    IsSelfDual H (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) := by
  have hI' : IsIsom H' H ((g.symm : W ≃ₗ[ℂ] V) : W →ₗ[ℂ] V) := by
    intro x y
    have h1 := hI (g.symm x) (g.symm y)
    simpa using h1.symm
  have h1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.selfDual_img H' H g.symm hI' Λ' h
  have h2 : Formalism.L2.Th1.H.imgLat ((g.symm : W ≃ₗ[ℂ] V) : W →ₗ[ℂ] V) Λ' =
      Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom := by
    ext x
    simp only [Formalism.L2.Th1.H.imgLat, AddSubgroup.mem_map, AddSubgroup.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨g x, hx, by simp⟩
  rw [← h2]
  exact h1

theorem isLat_comap {Λ' : AddSubgroup W} (h : IsLat Λ') : IsLat (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · have hc : Continuous (g : V → W) := (g : V →ₗ[ℂ] W).continuous_of_finiteDimensional
    exact DiscreteTopology.of_continuous_injective
      (f := fun x : Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom => (⟨g x, x.2⟩ : Λ'))
      ((hc.comp continuous_subtype_val).subtype_mk (fun x => x.2))
      (fun x y hxy => Subtype.ext (g.injective (congrArg Subtype.val hxy)))
  · have hset : ((Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom : AddSubgroup V) : Set V) =
        ((g.symm.restrictScalars ℝ : W ≃ₗ[ℝ] V).toLinearMap : W → V) '' (Λ' : Set W) := by
      ext x
      simp only [AddSubgroup.coe_comap, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
      constructor
      · intro hx
        exact ⟨g x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [hset, Submodule.span_image (g.symm.restrictScalars ℝ : W ≃ₗ[ℝ] V).toLinearMap, h2, Submodule.map_top,
      LinearMap.range_eq_top.mpr (g.symm.restrictScalars ℝ : W ≃ₗ[ℝ] V).surjective]

theorem th_comap (hI : IsIsom H H' (g : V →ₗ[ℂ] W)) {Λ' : AddSubgroup W} {α' : W → ℂ} {G : W → ℂ} (hG : G ∈ Th H' α' Λ') :
    (fun v => G (g v)) ∈ Th H (fun v => α' (g v)) (Λ'.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) := by
  obtain ⟨hG1, hG2⟩ := hG
  have hG2' : ∀ x ∈ Λ', ∀ z, α' x * Formalism.L2.Th1.H.opU H' x G z = G z := hG2
  have hI' : ∀ u v, H' (g u) (g v) = H u v := hI
  refine ⟨fun z _ => ?_, ?_⟩
  · have hga : AnalyticAt ℂ (fun v => g v) z :=
      (LinearMap.toContinuousLinearMap (g : V →ₗ[ℂ] W)).analyticAt z
    exact (hG1 (g z) (Set.mem_univ _)).comp hga
  · intro x hx z
    have hx' : g x ∈ Λ' := hx
    have h := hG2' (g x) hx' (g z)
    simp only [Formalism.L2.Th1.H.opU] at h ⊢
    rw [hI' z x, hI' x x] at h
    rw [map_add]
    exact h

theorem relIdx_comap (Λ₁ Λ₂ : AddSubgroup W) :
    relIdx (Λ₁.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) (Λ₂.comap (g : V →ₗ[ℂ] W).toAddMonoidHom) = relIdx Λ₁ Λ₂ := by
  unfold Formalism.L2.Th1.H.relIdx
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective g.surjective]

theorem alphaQ_isom (hI : IsIsom H H' (g : V →ₗ[ℂ] W)) (c : ℝ) (v : V) : alphaQ c H' (g v) = alphaQ c H v := by
  unfold Formalism.L2.Th1.H.alphaQ Formalism.L2.Th1.H.qOf
  have hI' : ∀ u w, H' (g u) (g w) = H u w := hI
  rw [hI' v v]

end Gen

section Form

variable {D : D7} {X : Fields} (s : Seam D X)

theorem form_flat (A : ℝ) (a b : ℕ) (x y : DVar X.Tau a b → ℂ) :
    matH (hSc X.Tau a b A⁻¹) x y = formV A D.what₂.Tau a b (s.flatV a b x) (s.flatV a b y) := by
  have hL : (matH (hSc X.Tau a b A⁻¹)) x y = ∑ k, x k * conj (y k) * ((A⁻¹ : ℝ) : ℂ) := by
    simp only [Formalism.L2.Th1.H.matH, LinearMap.mk₂'ₛₗ_apply, Formalism.L2.AlgTh.hSc, Matrix.diagonal_apply, mul_ite, ite_mul,
      mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hL]
  simp only [formV, LinearMap.mk₂'ₛₗ_apply]
  have hsum : ∑ τ, ∑ i, ∑ j, (s.flatV a b x) τ i j * conj ((s.flatV a b y) τ i j) =
      ∑ k, x k * conj (y k) := by
    simp only [Seam.flatV, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Equiv.sum_comp s.iT.symm (fun t => ∑ i, ∑ j, x (t, i, j) * conj (y (t, i, j)))]
    simp only [← Fintype.sum_prod_type']
  rw [hsum, div_eq_mul_inv, Finset.sum_mul, Complex.ofReal_inv]

theorem isom_flat (A : ℝ) (a b : ℕ) :
    IsIsom (matH (hSc X.Tau a b A⁻¹)) (formV A D.what₂.Tau a b)
      ((s.flatV a b : (DVar X.Tau a b → ℂ) ≃ₗ[ℂ] TaylorLogMetric.VC D a b) : (DVar X.Tau a b → ℂ) →ₗ[ℂ] TaylorLogMetric.VC D a b) := by
  intro x y
  exact (form_flat s A a b x y).symm

theorem matH_hSc (sc : ℝ) (a b : ℕ) (x y : DVar X.Tau a b → ℂ) :
    matH (hSc X.Tau a b sc) x y = (sc : ℂ) * ∑ k, x k * conj (y k) := by
  simp only [Formalism.L2.Th1.H.matH, LinearMap.mk₂'ₛₗ_apply, Formalism.L2.AlgTh.hSc, Matrix.diagonal_apply, mul_ite, ite_mul,
    mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem herm_hSc (sc : ℝ) (a b : ℕ) : IsHerm (matH (hSc X.Tau a b sc)) := by
  intro x y
  rw [matH_hSc, matH_hSc, map_mul, Complex.conj_ofReal, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [map_mul, Complex.conj_conj, mul_comm]

theorem posDef_hSc {sc : ℝ} (hsc : 0 < sc) (a b : ℕ) : IsPosDef (matH (hSc X.Tau a b sc)) := by
  intro x hx
  rw [matH_hSc]
  have h1 : ∀ k, x k * conj (x k) = ((Complex.normSq (x k) : ℝ) : ℂ) := fun k => Complex.mul_conj (x k)
  simp only [h1]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  apply mul_pos hsc
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hx
  exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _) ⟨k, Finset.mem_univ _, Complex.normSq_pos.mpr hk⟩

end Form

section Lat

variable {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

include B in

theorem sc_pos : 0 < (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ := by
  rw [show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L from B.areaOK]
  exact inv_pos.2 (Formalism.L2.Th1.F.areaPos_thm B.L)

theorem delta_ne (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 :=
  Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.delta_nonzero_link D cc hcc δ hδ

variable {a b : ℕ} {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}

theorem isLat_La (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : TaylorLogMetric.admitted D a b L L') :
    IsLat (TaylorLogMetric.La D B.tor L L') := by
  have hL := B.latAll hcc hδ (delta_ne hcc hδ)
  have h0 : IsLat (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b)) :=
    Formalism.L2.PairingIndexBounds.Eq.J.lat0IsLat (B.stdOK hcc hδ) a b
  have hc := hL.2 a b _ _ _ _ (Base.first_coordinate_admissible hA) hA
  exact KR.isLat_of_comm h0 hc.2 hc.1

theorem isLat_laF (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : TaylorLogMetric.admitted D a b L L') :
    IsLat (s.laF B.tor L L') := by
  exact isLat_comap (s.flatV a b) (isLat_La B hcc hδ hA)

theorem selfDual_laF (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : TaylorLogMetric.admitted D a b L L') :
    IsSelfDual (matH (hSc X.Tau a b (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)) (s.laF B.tor L L') :=
  selfDual_comap (s.flatV a b) (isom_flat s _ a b) ((B.latAll hcc hδ (delta_ne hcc hδ)).1 a b L L' hA).1

theorem La_theta {x : TaylorLogMetric.VC D a b} (hx : x ∈ TaylorLogMetric.La D B.tor L L') : cmTheta 1 D.host.d • x ∈ TaylorLogMetric.La D B.tor L L' := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨cmTheta 1 D.host.d * w, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.lam_theta hw, A, hA, ?_⟩
    rw [smul_smul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

theorem theta_laF {b₀ : ℤ} (hb : Odd b₀) {x : DVar X.Tau a b → ℂ} (hx : x ∈ s.laF B.tor L L') :
    cmTheta b₀ D.host.d • x ∈ s.laF B.tor L L' := by
  obtain ⟨k, hk⟩ := hb
  have hx' : s.flatV a b x ∈ TaylorLogMetric.La D B.tor L L' := hx
  show s.flatV a b (cmTheta b₀ D.host.d • x) ∈ TaylorLogMetric.La D B.tor L L'
  have hc : cmTheta b₀ D.host.d = cmTheta 1 D.host.d + (k : ℂ) := by
    simp only [Formalism.L2.Th1.F.cmTheta, hk]
    push_cast
    ring
  rw [map_smul, hc, add_smul]
  refine add_mem (La_theta B hx') ?_
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx' k

theorem odd_of_cmOK {a₀ : ℕ} {b₀ c₀ : ℤ} {d : ℕ} (h : CmOK a₀ b₀ c₀ d) : Odd b₀ := by
  obtain ⟨h1, -, h3, -⟩ := h
  rcases Int.even_or_odd b₀ with ⟨k, hk⟩ | hb
  · exfalso
    have e1 : (4 : ℤ) * a₀ * c₀ = 4 * ((a₀ : ℤ) * c₀) := by ring
    have e2 : b₀ ^ 2 = 4 * (k * k) := by rw [hk]; ring
    rw [e1, e2] at h1
    have h4 : (d : ℤ) % 8 = 7 := by exact_mod_cast h3
    generalize (a₀ : ℤ) * c₀ = f at h1
    generalize k * k = e at h1
    omega
  · exact hb

theorem al_eq_La (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : TaylorLogMetric.admitted D a b L L') :
    ∀ x ∈ TaylorLogMetric.La D B.tor L L', TaylorLogMetric.al D B.tor x =
      alphaQ (Real.sqrt D.host.d / 2) (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) x := by
  intro x hx
  obtain ⟨m, hm⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B a b L L' hA x hx
  exact al_eq D B.tor x m hm

theorem th_laF (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : TaylorLogMetric.admitted D a b L L') {G : TaylorLogMetric.VC D a b → ℂ}
    (hG : G ∈ Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L L')) :
    (fun z => G (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹))) (s.laF B.tor L L') := by
  have hT := th_comap (s.flatV a b) (isom_flat s (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) a b) hG
  obtain ⟨h1, h2⟩ := hT
  refine ⟨h1, ?_⟩
  have h2' : ∀ x ∈ s.laF B.tor L L', ∀ z, TaylorLogMetric.al D B.tor (s.flatV a b x) *
      Formalism.L2.Th1.H.opU (matH (hSc X.Tau a b (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)) x (fun z => G (s.flatV a b z)) z =
      G (s.flatV a b z) := h2
  intro x hx z
  have hx' : s.flatV a b x ∈ TaylorLogMetric.La D B.tor L L' := hx
  have e : alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)) x =
      TaylorLogMetric.al D B.tor (s.flatV a b x) := by
    rw [← alphaQ_isom (s.flatV a b) (isom_flat s _ a b), al_eq_La B hcc hδ hA _ hx']
  rw [e]
  exact h2' x hx z

theorem thZero_laF (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (ha : Even a) (hb : Even b) :
    (fun z => B.thZero a b (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)))
      (s.laF B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b)) :=
  th_laF s B hcc hδ (Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D a b ha hb) (B.thZeroMem (B.stdOK hcc hδ) a b)

theorem thHalf_laF (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : TaylorLogMetric.admitted D a b L L') :
    (fun z => B.thHalf a b L (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)))
      (s.laF B.tor L (StandardLatticesGL3.stdL D b)) :=
  th_laF s B hcc hδ (Base.isAdmissible_flagPair_of_unitriangular_left_automorphism hA) (B.thHalf_mem (B.stdOK hcc hδ) (B.latAll hcc hδ (delta_ne hcc hδ)) hA)

theorem thMoved_laF (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : TaylorLogMetric.admitted D a b L L') :
    (fun z => B.thMoved a b L L' (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹))) (s.laF B.tor L L') :=
  th_laF s B hcc hδ hA (B.thMoved_mem (B.latAll hcc hδ (delta_ne hcc hδ)) (B.thZeroMem (B.stdOK hcc hδ) a b) hA)

theorem eNat_laF (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (hA : TaylorLogMetric.admitted D a b L L') :
    (fun z => B.eNat χ a b L L' (s.flatV a b z)) ∈ Th (matH (hSc X.Tau a b (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hSc X.Tau a b (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹))) (s.laF B.tor L L') :=
  Submodule.smul_mem _ (Base.chiFac χ a b L L') (thMoved_laF s B hcc hδ hA)

theorem relIdx_laF (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    {L₁ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L₁' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (hA : TaylorLogMetric.admitted D a b L L') (hA₁ : TaylorLogMetric.admitted D a b L₁ L₁') :
    relIdx (s.laF B.tor L L') (s.laF B.tor L₁ L₁') ≠ 0 := by
  unfold Seam.laF
  rw [relIdx_comap]
  exact ((B.latAll hcc hδ (delta_ne hcc hδ)).2 a b _ _ _ _ hA hA₁).1

theorem relIdx_laF_eq {L₁ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L₁' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} :
    relIdx (s.laF B.tor L L') (s.laF B.tor L₁ L₁') = relIdx (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L₁') := by
  exact relIdx_comap (s.flatV a b) _ _

end Lat

end Formalism.L2.Ker.KS.Lat
