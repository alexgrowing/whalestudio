import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartHolomorphicOnCover

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0 dflat herm)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas IsType IsReal Alt delAt dbarAt)
open GlobalTheory.ConjChart (conjCoord conjPts conjChart)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

namespace GlobalTheory.PeriodChartChange

theorem gram_herm (g : ℕ) (τ τ' M K : Matrix (Fin g) (Fin g) ℂ) (hτ : IsSiegel τ) (hτ' : IsSiegel τ')
    (hK : IsUnit K.det)
    (h : ∀ a b, HermFrame.form ((2 : ℂ) • τ'.map (fun t => (t.im : ℂ))) (K a) (K b) =
      HermFrame.form ((2 : ℂ) • τ.map (fun t => (t.im : ℂ))) (M *ᵥ K a) (M *ᵥ K b)) :
    ∀ s t : Fin g → ℂ, herm τ' (s ᵥ* M) (t ᵥ* M) = herm τ s t := by
  classical
  have cast : ∀ T : Matrix (Fin g) (Fin g) ℂ, IsSiegel T →
      ((T.map Complex.im)⁻¹).map (fun t : ℝ => (t : ℂ)) = (T.map (fun t => (t.im : ℂ)))⁻¹ ∧
      IsUnit (T.map (fun t => (t.im : ℂ))).det ∧
      (T.map (fun t => (t.im : ℂ)))ᵀ = T.map (fun t => (t.im : ℂ)) := by
    intro T hT
    have hd : IsUnit (T.map Complex.im).det := hT.2.det_pos.ne'.isUnit
    have e : T.map (fun t => (t.im : ℂ)) = (T.map Complex.im).map Complex.ofRealHom := by
      ext i j; simp
    refine ⟨?_, ?_, ?_⟩
    · rw [e]
      symm
      apply Matrix.inv_eq_left_inv
      change ((T.map Complex.im)⁻¹).map Complex.ofRealHom * (T.map Complex.im).map Complex.ofRealHom = 1
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hd, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [e]
      have := hd.map Complex.ofRealHom
      rwa [RingHom.map_det] at this
    · rw [← Matrix.transpose_map, hT.1.eq]
  obtain ⟨ei, hd, hs⟩ := cast τ hτ
  obtain ⟨ei', hd', hs'⟩ := cast τ' hτ'
  intro s t
  unfold herm
  rw [ei, ei']
  set Y := τ.map (fun t => (t.im : ℂ)) with hYdef
  set Y' := τ'.map (fun t => (t.im : ℂ)) with hY'def
  have hK' : IsUnit K := (Matrix.isUnit_iff_isUnit_det K).2 hK
  have hN : IsUnit Kᵀᴴᵀ := (Matrix.isUnit_iff_isUnit_det _).2 (by
    rw [det_transpose, det_conjTranspose, det_transpose]; exact hK.star)
  have hG : (2 : ℂ) • Y' = HermFrame.chg M ((2 : ℂ) • Y) := by
    have e : HermFrame.chg Kᵀ ((2 : ℂ) • Y') = HermFrame.chg Kᵀ (HermFrame.chg M ((2 : ℂ) • Y)) := by
      ext a b
      rw [HermFrame.chg_apply, HermFrame.chg_apply]
      exact (h a b).trans (HermFrame.form_chg M _ (K a) (K b)).symm
    simp only [HermFrame.chg, transpose_transpose] at e
    exact hK'.mul_left_cancel (hN.mul_right_cancel e)
  have hY' : Y' = Mᵀ * Y * Mᴴᵀ := by
    rw [HermFrame.chg, Matrix.mul_smul, Matrix.smul_mul] at hG
    exact smul_right_injective _ (two_ne_zero' ℂ) hG
  have hY'' : Y' = Mᴴ * Y * M := by
    rw [← hs', hY']
    simp only [transpose_mul, transpose_transpose, hs, Matrix.mul_assoc]
  have hM : IsUnit M.det := by
    have := hd'
    rw [hY'', det_mul] at this
    exact isUnit_of_mul_isUnit_right this
  have hMu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 hM
  have hkey : M * Y'⁻¹ * Mᴴ = Y⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    apply hMu.mul_right_cancel
    rw [Matrix.one_mul]
    calc M * Y'⁻¹ * Mᴴ * Y * M = M * (Y'⁻¹ * (Mᴴ * Y * M)) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [← hY'', Matrix.nonsing_inv_mul _ hd', Matrix.mul_one]
  rw [star_vecMul, dotProduct_mulVec, vecMul_vecMul, vecMul_vecMul, ← Matrix.mul_assoc, hkey]

theorem fibre_transfer : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (A : Over S) [GrpObj A] (g : ℕ) (w : VMetric p (omega A) g) (σ : k →+* ℂ) (D : ℕ) (c c' : AlgChart p σ D) (τ τ' : V D → Matrix (Fin g) (Fin g) ℂ) (ex ex' : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex → IsPeriodChart w c' τ' ex' → ∀ P ∈ cov c.e.target g, ∀ ψ : Pt (V D) g → Pt (V D) g, (∀ᶠ Q in 𝓝 P, ψ Q ∈ cov c'.e.target g ∧ ex' (ψ Q) = ex Q) → c'.e.symm (ψ P).1 = c.e.symm P.1 ∧ ∀ᶠ u in 𝓝 (0 : Fin g → ℂ), (ψ (P.1, P.2 + u)).1 = (ψ P).1 ∧ ex' ((ψ P).1, (ψ (P.1, P.2 + u)).2 - (ψ P).2) = ex (P.1, u) := by
  intro k _ S p A _ g w σ D c c' τ τ' ex ex' HP HP' P hP ψ hev
  have hv : P.1 ∈ c.e.target := hP.1
  have hPQ := hev.self_of_nhds
  have hv' : (ψ P).1 ∈ c'.e.target := hPQ.1.1
  have hov : ∀ Q : Pt (V D) g, ψ Q ∈ cov c'.e.target g → ex' (ψ Q) = ex Q → Q.1 ∈ c.e.target →
      c'.e.symm (ψ Q).1 = c.e.symm Q.1 := by
    intro Q hQ he hQ1
    apply Subtype.ext
    rw [← (HP'.2.2 _ hQ.1).1 (ψ Q).2, ← (HP.2.2 _ hQ1).1 Q.2]
    exact congrArg (fun y => y.1 ≫ A.hom) he
  have hsymm := hov P hPQ.1 hPQ.2 hv
  refine ⟨hsymm, ?_⟩
  have ht : Tendsto (fun u : Fin g → ℂ => ((P.1, P.2 + u) : Pt (V D) g)) (𝓝 0) (𝓝 P) := by
    have : Continuous (fun u : Fin g → ℂ => ((P.1, P.2 + u) : Pt (V D) g)) := by fun_prop
    simpa using this.tendsto 0
  have ho : ∀ z, (ex (P.1, z)).1 ≫ A.hom = (c.e.symm P.1).1 := (HP.2.2 _ hv).1
  have ho' : ∀ z, (ex' ((ψ P).1, z)).1 ≫ A.hom = (c.e.symm P.1).1 := fun z => by
    rw [(HP'.2.2 _ hv').1 z, hsymm]
  let e : (Fin g → ℂ) → (Over.mk (c.e.symm P.1).1 ⟶ A) := fun z => Over.homMk (ex (P.1, z)).1 (ho z)
  let e' : (Fin g → ℂ) → (Over.mk (c.e.symm P.1).1 ⟶ A) := fun z => Over.homMk (ex' ((ψ P).1, z)).1 (ho' z)
  have hm : ∀ z z', e z * e z' = e (z + z') := fun z z' =>
    Over.OverMorphism.ext ((HP.2.2 _ hv).2.1 z z' _ _ rfl rfl)
  have hmul' := (HP'.2.2 _ hv').2.1
  rw [hsymm] at hmul'
  have hm' : ∀ z z', e' z * e' z' = e' (z + z') := fun z z' =>
    Over.OverMorphism.ext (hmul' z z' _ _ rfl rfl)
  have a0 : e' (ψ P).2 = e P.2 := Over.OverMorphism.ext (by
    show (ex' ((ψ P).1, (ψ P).2)).1 = (ex (P.1, P.2)).1
    exact congrArg Subtype.val hPQ.2)
  filter_upwards [ht.eventually hev] with u hu
  obtain ⟨hQ, he⟩ := hu
  have h1 : (ψ (P.1, P.2 + u)).1 = (ψ P).1 :=
    c'.e.symm.injOn hQ.1 hv' ((hov _ hQ he hv).trans hsymm.symm)
  refine ⟨h1, ?_⟩
  have hψQ : ψ (P.1, P.2 + u) = ((ψ P).1, (ψ (P.1, P.2 + u)).2) := Prod.ext h1 rfl
  have a1 : e' (ψ (P.1, P.2 + u)).2 = e (P.2 + u) := Over.OverMorphism.ext (by
    show (ex' ((ψ P).1, (ψ (P.1, P.2 + u)).2)).1 = (ex (P.1, P.2 + u)).1
    rw [← hψQ, he])
  have key : e' ((ψ (P.1, P.2 + u)).2 - (ψ P).2) = e u := by
    apply mul_left_cancel (a := e P.2)
    rw [hm, ← a0, hm', add_sub_cancel, a1]
  exact Subtype.ext (congrArg (fun x => x.left) key)

theorem cot_comp : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (A : Over S) [GrpObj A] (g : ℕ) (w : VMetric p (omega A) g) (σ : k →+* ℂ) (D : ℕ) (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex e₁ : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex → ∀ v ∈ c.e.target, ∀ (v₁ : V D) (χ : (Fin g → ℂ) → Fin g → ℂ) (C : (Fin g → ℂ) →L[ℂ] Fin g → ℂ), χ 0 = 0 → HasFDerivAt χ C 0 → (∀ᶠ u in 𝓝 (0 : Fin g → ℂ), ex (v, χ u) = e₁ (v₁, u)) → ∀ (W : A.left.Opens) (f : Γ(A.left, W)), ex (v, 0) ∈ ptsIn (A.hom ≫ p) σ W → cot e₁ W f v₁ = fun a => ∑ b, C (Pi.single a 1) b * cot ex W f v b := by
  intro k _ S p A _ g w σ D c τ ex e₁ HP v hv v₁ χ C hχ0 hχ hev W f hW
  obtain ⟨ho, hd⟩ := HP.2.1 W f
  let F : Pt (V D) g → ℂ := fun x => ev (A.hom ≫ p) σ W f (ex x)
  have hF : DifferentiableAt ℂ F (v, 0) := by
    have hm : ((v, 0) : Pt (V D) g) ∈ {b ∈ cov c.e.target g | ⊤ ≤ (ex b).1 ⁻¹ᵁ W} := ⟨⟨hv, trivial⟩, hW⟩
    exact hd.differentiableAt (ho.mem_nhds hm)
  let F₀ : (Fin g → ℂ) → ℂ := fun z => ev (A.hom ≫ p) σ W f (ex (v, z))
  have hF₀ : HasFDerivAt F₀ (fderiv ℂ F₀ 0) 0 :=
    (hF.comp (0 : Fin g → ℂ) ((differentiableAt_const v).prodMk differentiableAt_id)).hasFDerivAt
  have h0 : HasFDerivAt F₀ (fderiv ℂ F₀ 0) (χ 0) := by rw [hχ0]; exact hF₀
  have hG : HasFDerivAt (fun u => ev (A.hom ≫ p) σ W f (e₁ (v₁, u))) ((fderiv ℂ F₀ 0).comp C) 0 :=
    (h0.comp 0 hχ).congr_of_eventuallyEq (hev.mono fun u hu => by
      show _ = ev (A.hom ≫ p) σ W f (ex (v, χ u))
      rw [hu])
  funext a
  show fderiv ℂ (fun z => ev (A.hom ≫ p) σ W f (e₁ (v₁, z))) 0 (Pi.single a 1) = _
  rw [hG.fderiv, ContinuousLinearMap.comp_apply]
  have hs : C (Pi.single a 1) = ∑ b, C (Pi.single a 1) b • (Pi.single b (1 : ℂ) : Fin g → ℂ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hs, map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

theorem herm_fderiv_vert : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (A : Over S) [GrpObj A] [QuasiSeparated A.hom] (g : ℕ) (w : VMetric p (omega A) g) (σ : k →+* ℂ) (D : ℕ) (c c' : AlgChart p σ D) (τ τ' : V D → Matrix (Fin g) (Fin g) ℂ) (ex ex' : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex → IsPeriodChart w c' τ' ex' → ∀ P ∈ cov c.e.target g, ∀ ψ : Pt (V D) g → Pt (V D) g, DifferentiableAt ℂ ψ P → (∀ᶠ Q in 𝓝 P, ContinuousAt ψ Q ∧ ψ Q ∈ cov c'.e.target g ∧ ex' (ψ Q) = ex Q) → ∀ s t : Fin g → ℂ, (fderiv ℂ ψ P (0, s)).1 = 0 ∧ herm (τ' (ψ P).1) (fderiv ℂ ψ P (0, s)).2 (fderiv ℂ ψ P (0, t)).2 = herm (τ P.1) s t := by
  intro k _ S p A _ _ g w σ D c c' τ τ' ex ex' HP HP' P hP ψ hψd hev s t
  have hev' : ∀ᶠ Q in 𝓝 P, ψ Q ∈ cov c'.e.target g ∧ ex' (ψ Q) = ex Q := hev.mono fun Q h => h.2
  obtain ⟨hsymm, hfib⟩ := fibre_transfer k S p A g w σ D c c' τ τ' ex ex' HP HP' P hP ψ hev'
  have hPQ := hev'.self_of_nhds
  have hv' : (ψ P).1 ∈ c'.e.target := hPQ.1.1
  have hv : P.1 ∈ c.e.target := hP.1
  let φ : (Fin g → ℂ) → Pt (V D) g := fun u => (P.1, P.2 + u)
  have hφ0 : φ 0 = P := Prod.ext rfl (add_zero _)
  let L : (Fin g → ℂ) →L[ℂ] Pt (V D) g := (0 : (Fin g → ℂ) →L[ℂ] V D).prod (ContinuousLinearMap.id ℂ _)
  have hφ : HasFDerivAt φ L 0 := (hasFDerivAt_const P.1 0).prodMk ((hasFDerivAt_id (0 : Fin g → ℂ)).const_add P.2)
  have hψ1 : HasFDerivAt ψ (fderiv ℂ ψ P) (φ 0) := by rw [hφ0]; exact hψd.hasFDerivAt
  have hψφ : HasFDerivAt (ψ ∘ φ) ((fderiv ℂ ψ P).comp L) 0 := hψ1.comp 0 hφ
  have hL : ∀ s, L s = (0, s) := fun s => rfl
  have hfst : HasFDerivAt (fun u => (ψ (φ u)).1) ((ContinuousLinearMap.fst ℂ (V D) (Fin g → ℂ)).comp ((fderiv ℂ ψ P).comp L)) 0 :=
    hasFDerivAt_fst.comp 0 hψφ
  have hconst : HasFDerivAt (fun u => (ψ (φ u)).1) (0 : (Fin g → ℂ) →L[ℂ] V D) 0 :=
    (hasFDerivAt_const (ψ P).1 0).congr_of_eventuallyEq (hfib.mono fun u h => h.1)
  have h1 : ∀ s : Fin g → ℂ, (fderiv ℂ ψ P (0, s)).1 = 0 := fun s => by
    have := congrArg (· s) (hfst.unique hconst)
    simpa [hL] using this
  let χ : (Fin g → ℂ) → Fin g → ℂ := fun u => (ψ (φ u)).2 - (ψ P).2
  let C : (Fin g → ℂ) →L[ℂ] Fin g → ℂ := (ContinuousLinearMap.snd ℂ (V D) (Fin g → ℂ)).comp ((fderiv ℂ ψ P).comp L)
  have hχ : HasFDerivAt χ C 0 := (hasFDerivAt_snd.comp 0 hψφ).sub_const _
  have hχ0 : χ 0 = 0 := by simp only [χ, hφ0, sub_self]
  have hC : ∀ s, C s = (fderiv ℂ ψ P (0, s)).2 := fun s => rfl
  have hχev : ∀ᶠ u in 𝓝 (0 : Fin g → ℂ), ex' ((ψ P).1, χ u) = ex (P.1, u) := hfib.mono fun u h => h.2
  obtain ⟨W, f, hW, hdet⟩ := PeriodChartOnto.exists_frame_cot k S p A g w σ D c' τ' ex' HP' (ψ P).1 hv'
  let M : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun a b => C (Pi.single a 1) b
  let K : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun a b => cot ex' W (f a) (ψ P).1 b
  have hcot : ∀ a, cot ex W (f a) P.1 = M *ᵥ K a := fun a => by
    rw [cot_comp k S p A g w σ D c' τ' ex' ex HP' (ψ P).1 hv' P.1 χ C hχ0 hχ hχev W (f a) hW]
    funext i
    simp [M, K, mulVec, dotProduct]
  have e0 : (ex' ((ψ P).1, 0)).1 = (c'.e.symm (ψ P).1).1 ≫ unitSec A :=
    ((HP'.2.2 _ hv').2.2.2.1 0).2 ⟨0, zero_mem _, by funext i; simp [GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.per, vecMul, dotProduct]⟩
  have hU' : c'.e.symm (ψ P).1 ∈ ptsIn p σ (unitSec A ⁻¹ᵁ W) := by
    have hW' : ⊤ ≤ (ex' ((ψ P).1, 0)).1 ⁻¹ᵁ W := hW
    rw [e0] at hW'
    exact hW'
  have hU : c.e.symm P.1 ∈ ptsIn p σ (unitSec A ⁻¹ᵁ W) := hsymm ▸ hU'
  have hgram : ∀ a b, HermFrame.form ((2 : ℂ) • (τ' (ψ P).1).map (fun t => (t.im : ℂ))) (K a) (K b) =
      HermFrame.form ((2 : ℂ) • (τ P.1).map (fun t => (t.im : ℂ))) (M *ᵥ K a) (M *ᵥ K b) := fun a b => by
    have e1 := (HP.2.2 P.1 hv).2.2.2.2 (unitSec A ⁻¹ᵁ W) W le_rfl (f a) (f b) hU
    have e2 := (HP'.2.2 _ hv').2.2.2.2 (unitSec A ⁻¹ᵁ W) W le_rfl (f a) (f b) hU'
    rw [hsymm] at e2
    rw [← hcot, ← hcot]
    exact e2.symm.trans e1
  have hCv : ∀ s : Fin g → ℂ, (fderiv ℂ ψ P (0, s)).2 = s ᵥ* M := fun s => by
    rw [← hC]
    have hs : s = ∑ a, s a • (Pi.single a (1 : ℂ) : Fin g → ℂ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hs]
    funext b
    simp [M, vecMul, dotProduct, Finset.sum_apply]
  refine ⟨h1 s, ?_⟩
  rw [hCv s, hCv t]
  exact gram_herm g (τ P.1) (τ' (ψ P).1) M K (HP.1.2.2 P.1 hv) (HP'.1.2.2 _ hv') hdet hgram s t

end GlobalTheory.PeriodChartChange
