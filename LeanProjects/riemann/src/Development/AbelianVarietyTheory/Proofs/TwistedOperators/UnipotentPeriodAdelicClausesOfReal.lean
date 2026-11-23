import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableScalarActionMultiplicityMapValuesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryHaarEqMapProdRealFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruencePreimageVolumeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIdealSmulAdelicPointRationalLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer.AdelicFromReal

variable {D : D7}

theorem cmp_of_mem_GfC (θ : InfFam D) {V : HSp D} {b : GA D V} (hb : b ∈ GfC V) (τ : D.what₂.Tau) : cmp θ τ b = 1 := by
  have h1 : infHom V b = 1 := hb
  have h2 := congrArg Units.val h1
  simp only [infHom, MonoidHom.comp_apply, Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Units.val_one] at h2
  have h4 : (matHom V b).1.map (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) = 1 := h2
  have h3 : cmp θ τ b = ((matHom V b).1.map (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E))).map (θ τ) := rfl
  rw [h3, h4]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem finE_of_mem_GinfC {V : HSp D} {a : GA D V} (ha : a ∈ GinfC V) : Lev.finE V a = 1 := by
  have h1 : finHom V a = 1 := ha
  simp only [Lev.finE, MonoidHom.comp_apply, h1, map_one]

end GlobalTheory.SepPer.AdelicFromReal

namespace GlobalTheory.SepPer.AdelicFromReal

variable {D : D7}

theorem map_mulVec_ratV {V : HSp D} (g : GA D V) {y y' : Fin V.rank → D.host.E} (h : mt V g *ᵥ ratV y = ratV y')
    {R : Type} [CommRing R] (φ : AE D →+* R) :
    (mt V g).map φ *ᵥ (fun i => φ (incA D (y i))) = fun i => φ (incA D (y' i)) := by
  funext i
  have := congrArg (fun v => φ (v i)) h
  rw [RingHom.map_mulVec] at this
  exact this

theorem finE_mulVec {V : HSp D} (g : GA D V) {y y' : Fin V.rank → D.host.E} (h : mt V g *ᵥ ratV y = ratV y') :
    (Lev.finE V g).1 *ᵥ (fun i => y i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) =
      fun i => y' i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) := by
  let φ : AE D →+* Lev.EAf D := (Lev.swapAE D).comp
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have e1 : (Lev.finE V g).1 = (mt V g).map φ := by
    show (((matHom V g).1.map _).map _) = _
    rw [Matrix.map_map]; rfl
  have e2 : ∀ x : D.host.E, φ (incA D x) = x ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) := fun x => by
    show Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have := map_mulVec_ratV g h φ
  simp only [e2] at this
  rw [e1]; exact this

theorem cmp_mulVec (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} (g : GA D V) {y y' : Fin V.rank → D.host.E}
    (h : mt V g *ᵥ ratV y = ratV y') (τ : D.what₂.Tau) :
    cmp θ τ g *ᵥ (fun i => tauE D τ (y i)) = fun i => tauE D τ (y' i) := by
  let φ : AE D →+* ℂ := (θ τ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have e1 : cmp θ τ g = (mt V g).map φ := by
    show (((matHom V g).1.map _).map _) = _
    rw [Matrix.map_map]; rfl
  have e2 : ∀ x : D.host.E, φ (incA D x) = tauE D τ x := fun x => by
    show θ τ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    exact (hθ τ).1 x
  have := map_mulVec_ratV g h φ
  simp only [e2] at this
  rw [e1]; exact this

end GlobalTheory.SepPer.AdelicFromReal

namespace GlobalTheory.SepPer.AdelicFromReal

variable {D : D7}

theorem unitaryEmbedding_fixes_vectors {Y V : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData Y V c ε) (h : GA D Y) (j : Fin c) :
    mt V (stabilizerEmbedding d h) *ᵥ ratV (fun i => d.a i j) = ratV (fun i => d.a i j) := by
  have hq : GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ (fun i => d.a i j) = 0 := by
    have hp : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V Y d.ι) * V.gram) *ᵥ (fun i => d.a i j) = 0 := by
      funext k
      have := congrFun (congrFun d.perp k) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    rw [GlobalTheory.UnitaryEmbeddingProperties.qM, ← Matrix.mulVec_mulVec, hp, Matrix.mulVec_zero]
  have hQ : (GlobalTheory.UnitaryEmbeddingProperties.qM d).map (incA D) *ᵥ ratV (fun i => d.a i j) = 0 := by
    funext k
    have := RingHom.map_mulVec (incA D) (GlobalTheory.UnitaryEmbeddingProperties.qM d) (fun i => d.a i j) k
    rw [hq] at this
    have e : ratV (fun i => d.a i j) = (incA D) ∘ (fun i => d.a i j) := rfl
    rw [e]
    simpa using this.symm
  show (matHom V (stabilizerEmbedding d h)).1 *ᵥ _ = _
  rw [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_matrix_formula]
  simp only [GlobalTheory.UnitaryEmbeddingProperties.ex, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hQ, Matrix.mulVec_zero, add_zero]

theorem summandEmbedding_mem_infiniteCompact {Y V : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData Y V c ε) {a : GA D Y} (ha : a ∈ GinfC Y) :
    stabilizerEmbedding d a ∈ GinfC V := by
  show finHom V (stabilizerEmbedding d a) = 1
  apply Units.ext
  show ((matHom V (stabilizerEmbedding d a)).1).map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom = 1
  rw [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_matrix_formula, GlobalTheory.UnitaryEmbeddingProperties.ex_map]
  have h1 : ((matHom Y a).1).map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom = 1 :=
    congrArg Units.val ha
  rw [h1, GlobalTheory.UnitaryEmbeddingProperties.ex_one]

theorem summandEmbedding_mem_finiteCompact {Y V : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData Y V c ε) {b : GA D Y} (hb : b ∈ GfC Y) :
    stabilizerEmbedding d b ∈ GfC V := by
  show infHom V (stabilizerEmbedding d b) = 1
  apply Units.ext
  show ((matHom V (stabilizerEmbedding d b)).1).map (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom = 1
  rw [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_matrix_formula, GlobalTheory.UnitaryEmbeddingProperties.ex_map]
  have h1 : ((matHom Y b).1).map (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom = 1 :=
    congrArg Units.val hb
  rw [h1, GlobalTheory.UnitaryEmbeddingProperties.ex_one]

theorem summandEmbedding_inv {Y V : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData Y V c ε) (x : GA D Y) :
    stabilizerEmbedding d x⁻¹ = (stabilizerEmbedding d x)⁻¹ :=
  map_inv (MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)) x

theorem coefR_mul_fin (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (v a : ∀ τ, M.H τ)
    (g : GA D V) {b : GA D V} (hb : b ∈ GfC V) : coefR θ M v a (g * b) = coefR θ M v a g := by
  unfold coefR
  congr 1
  funext τ
  rw [show cmp θ τ (g * b) = cmp θ τ g * cmp θ τ b from GlobalTheory.PointAtPlaceHom.infMat_mul V (θ τ) g b,
    cmp_of_mem_GfC θ hb τ, Matrix.mul_one]

theorem multT_lev (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V))
    {t : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)} (ht : t ∈ MultT θ M J 1) (w : M.Vec) {k : GA D V} (hk : k ∈ J)
    (g : GA D V) : t (PiTensorProduct.tprod ℂ w) (g * k) = t (PiTensorProduct.tprod ℂ w) g := by
  have h1 := (mem_multT θ M J 1 t).1 ht
  have e : ∀ u, t (PiTensorProduct.tprod ℂ u) = (PiTensorProduct.lift.symm t) u := fun u => by
    simp [PiTensorProduct.lift_symm]
  suffices key : ∀ T ∈ Mult θ M J 1, ∀ g, T w (g * k) = T w g by rw [e]; exact key _ h1 g
  intro T hT
  induction hT using Submodule.span_induction with
  | mem T hT => intro g; rw [hT.lev w k hk g, Pi.one_apply, one_mul]
  | zero => intro g; simp
  | add T T' _ _ h h' => intro g; simp [h g, h' g]
  | smul a T _ h => intro g; simp [h g]

end GlobalTheory.SepPer.AdelicFromReal

namespace GlobalTheory.SepPer.AdelicFromReal

variable {D : D7}

open Classical in

theorem coef_split (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (u : ∀ τ, M.H τ) (g : GA D V) (a : GinfC Y) (b : GfC Y) :
    coef θ M K u u (g * stabilizerEmbedding d ((a : GA D Y) * b)) =
      coefR θ M u u (g * stabilizerEmbedding d a) * (if Lev.finE V (g * stabilizerEmbedding d b) ∈ K then (1 : ℂ) else 0) := by
  have ha := summandEmbedding_mem_infiniteCompact d a.2
  have hb := summandEmbedding_mem_finiteCompact d b.2
  have e1 : g * stabilizerEmbedding d ((a : GA D Y) * b) = g * stabilizerEmbedding d a * stabilizerEmbedding d b := by
    rw [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul, mul_assoc]
  have e2 : Lev.finE V (g * stabilizerEmbedding d a * stabilizerEmbedding d b) = Lev.finE V (g * stabilizerEmbedding d b) := by
    rw [map_mul, map_mul, finE_of_mem_GinfC ha, mul_one, map_mul]
  rw [e1, coef, e2, coefR_mul_fin θ M _ _ _ hb]
  split_ifs <;> simp

open Classical in

theorem one_clause (θ : InfFam D) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (u : ∀ τ, M.H τ) (φ : GA D Y → ℂ) (ν : Measure (GA D Y))
    [ν.IsMulLeftInvariant] (m : Measure (GinfC Y)) (μ : Measure (GfC Y)) [SigmaFinite m] [SigmaFinite μ]
    (hemb : MeasurableEmbedding (fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2))
    (hνe : ν = (m.prod μ).map (fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2))
    (K' : Set (GfC Y)) (hK' : ∀ b, b ∈ K' ↔ Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ K) (hK'm : MeasurableSet K')
    (hinv : ∀ b ∈ K', ∀ g, φ (g * b) = φ g) (c₀ : ℂ)
    (hrep : ∀ x, ∫ h, coefR θ M u u (stabilizerEmbedding d h) * φ (x * h) ∂m = c₀ * φ x) (x : GA D Y) :
    ∫ h, coef θ M K u u (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d h) * φ h ∂ν = ((μ K').toReal * c₀) * φ x := by
  have step1 : ∫ h, coef θ M K u u (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d h) * φ h ∂ν =
      ∫ h, coef θ M K u u (1 * stabilizerEmbedding d h) * φ (x * h) ∂ν := by
    rw [← integral_mul_left_eq_self (fun h => coef θ M K u u (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d h) * φ h) x]
    congr 1
    funext h
    rw [← GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul, inv_mul_cancel_left, one_mul]
  rw [step1, hνe, hemb.integral_map]
  have pw : ∀ q : GinfC Y × GfC Y, coef θ M K u u (1 * stabilizerEmbedding d ((q.1 : GA D Y) * q.2)) * φ (x * ((q.1 : GA D Y) * q.2)) =
      (coefR θ M u u (stabilizerEmbedding d q.1) * φ (x * q.1)) * K'.indicator (fun _ => (1 : ℂ)) q.2 := by
    intro q
    rw [coef_split θ d M K u 1 q.1 q.2, one_mul, one_mul, Set.indicator_apply]
    by_cases hq : q.2 ∈ K'
    · have hq' := (hK' q.2).1 hq
      rw [if_pos hq', if_pos hq, ← mul_assoc x, hinv q.2 hq]
      ring
    · have hq' : Lev.finE V (stabilizerEmbedding d (q.2 : GA D Y)) ∉ K := fun h => hq ((hK' q.2).2 h)
      rw [if_neg hq', if_neg hq]
      ring
  simp_rw [pw]
  rw [integral_prod_mul (fun a : GinfC Y => coefR θ M u u (stabilizerEmbedding d a) * φ (x * a)) (K'.indicator (fun _ => (1 : ℂ))), hrep,
    integral_indicator_const _ hK'm]
  simp only [Measure.real, Complex.real_smul, mul_one]
  ring

end GlobalTheory.SepPer.AdelicFromReal

namespace GlobalTheory.SepPer.AdelicFromReal

variable {D : D7}

theorem mulVec_sub_mem_of_triple_product_fixing {n : ℕ} {R : Type} [CommRing R] (A B C : Matrix (Fin n) (Fin n) R) (u0 u1 : Fin n → R) (H : Set (Fin n → R))
    (hk : (A * B * C) *ᵥ u0 - u0 ∈ H) (hC : C *ᵥ u0 = u0) (hB : B *ᵥ u0 = u1) (hA : A *ᵥ u0 = u0) : A *ᵥ (u1 - u0) ∈ H := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hC, hB] at hk
  rw [Matrix.mulVec_sub, hA]
  exact hk

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem vanish {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)) (hΛ : IsSelfDualC V Λ)
    (hz : zv d ∈ Λ) (x : GA D Y) (γ : GA D V) (z : Fin V.rank → D.host.E) (hzγ : mt V γ *ᵥ ratV (zv d) = ratV z)
    (h : GA D Y) (hk : Lev.finE V (stabilizerEmbedding d x⁻¹ * γ * stabilizerEmbedding d h) ∈ congLev D.sp.cm V.gram Λ 𝔪) :
    z - zv d ∈ 𝔪 • latAt Λ (stabilizerEmbedding d x) := by
  have hu0 : (fun i => zv d i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    Submodule.subset_span ⟨zv d, hz, rfl⟩
  have h3 := hk.2.2 _ hu0
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul] at h3
  have f1 := finE_mulVec (stabilizerEmbedding d h) (unitaryEmbedding_fixes_vectors d h 0)
  have f2 := finE_mulVec (stabilizerEmbedding d x⁻¹) (unitaryEmbedding_fixes_vectors d x⁻¹ 0)
  have f3 := finE_mulVec γ hzγ
  have h4 := mulVec_sub_mem_of_triple_product_fixing _ _ _ _ _ _ h3 f1 f3 f2
  have e : (fun i => z i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) - (fun i => zv d i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) =
      fun i => (z - zv d) i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) := by
    funext i
    simp only [Pi.sub_apply, TensorProduct.sub_tmul]
  rw [e, summandEmbedding_inv] at h4
  exact GlobalTheory.T.mem_ideal_smul_adelicPointRationalLattice D V Λ 𝔪 hΛ (stabilizerEmbedding d x) (z - zv d) h4

end GlobalTheory.SepPer.AdelicFromReal

namespace GlobalTheory.SepPer.AdelicFromReal

variable {D : D7}

open Classical in

theorem term_clause (θ : InfFam D) (hθ : IsInfFam θ) {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (u : ∀ τ, M.H τ) (B : Fr V) (Q : ℝ) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)) (hΛ : IsSelfDualC V Λ)
    (hz : zv d ∈ Λ) (ν : Measure (GA D Y)) (m : Measure (GinfC Y)) (μ : Measure (GfC Y)) [SigmaFinite m] [SigmaFinite μ]
    [μ.IsMulLeftInvariant]
    (hemb : MeasurableEmbedding (fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2))
    (hνe : ν = (m.prod μ).map (fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2))
    (K' : Set (GfC Y)) (hK' : ∀ b, b ∈ K' ↔ Lev.finE V (stabilizerEmbedding d (b : GA D Y)) ∈ congLev D.sp.cm V.gram Λ 𝔪)
    (hK'm : MeasurableSet K') (hK'top : μ K' < ⊤) (c₀ : ℂ)
    (hfar : ∀ g : GA D V, Integrable (fun h : GinfC Y => coefR θ M u u (g * stabilizerEmbedding d h)) m ∧
      (∫ h : GinfC Y, ‖coefR θ M u u (g * stabilizerEmbedding d h)‖ ∂m) * (∏ τ, nrm θ B g⁻¹ τ (zv d)) ^ (2 * V.rank + 5) ≤
        Real.exp Q * ‖c₀‖)
    (x : GA D Y) (γ : GA D V) (z : Fin V.rank → D.host.E) (hzγ : mt V γ *ᵥ ratV (zv d) = ratV z) :
    Integrable (fun h => coef θ M (congLev D.sp.cm V.gram Λ 𝔪) u u (stabilizerEmbedding d x⁻¹ * γ * stabilizerEmbedding d h)) ν ∧
    (∫ h, ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) u u (stabilizerEmbedding d x⁻¹ * γ * stabilizerEmbedding d h)‖ ∂ν) *
      (∏ τ, nrm θ B (stabilizerEmbedding d x) τ z) ^ (2 * V.rank + 5) ≤ Real.exp Q * ‖((μ K').toReal : ℂ) * c₀‖ ∧
    (z - zv d ∉ 𝔪 • latAt Λ (stabilizerEmbedding d x) →
      ∀ h, coef θ M (congLev D.sp.cm V.gram Λ 𝔪) u u (stabilizerEmbedding d x⁻¹ * γ * stabilizerEmbedding d h) = 0) := by
  obtain ⟨K, hK⟩ : ∃ K, K = congLev D.sp.cm V.gram Λ 𝔪 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = stabilizerEmbedding d x⁻¹ * γ := ⟨_, rfl⟩
  rw [← hK, ← hg]
  rw [← hK] at hK'
  let Sg : Set (GfC Y) := {b : GfC Y | Lev.finE V (g * stabilizerEmbedding d (b : GA D Y)) ∈ K}
  have hS : MeasurableSet Sg ∧ μ Sg ≤ μ K' := by
    by_cases hne : Sg.Nonempty
    · obtain ⟨b₀, hb₀⟩ := hne
      have hb₀' : Lev.finE V (g * stabilizerEmbedding d (b₀ : GA D Y)) ∈ K := hb₀
      have e : Sg = (fun b => b₀⁻¹ * b) ⁻¹' K' := by
        ext b
        rw [Set.mem_preimage, hK']
        have e1 : g * stabilizerEmbedding d (b : GA D Y) = (g * stabilizerEmbedding d (b₀ : GA D Y)) * stabilizerEmbedding d ((b₀⁻¹ * b : GfC Y) : GA D Y) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul, summandEmbedding_inv, mul_assoc, mul_inv_cancel_left]
        show Lev.finE V (g * stabilizerEmbedding d (b : GA D Y)) ∈ K ↔ _
        rw [e1, map_mul]
        exact K.mul_mem_cancel_left hb₀'
      rw [e]
      exact ⟨(measurable_const_mul b₀⁻¹) hK'm, (measure_preimage_mul μ b₀⁻¹ K').le⟩
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]
      exact ⟨MeasurableSet.empty, by simp⟩
  have hSfin : μ Sg < ⊤ := hS.2.trans_lt hK'top
  have pw : ∀ q : GinfC Y × GfC Y, coef θ M K u u (g * stabilizerEmbedding d ((q.1 : GA D Y) * q.2)) =
      coefR θ M u u (g * stabilizerEmbedding d q.1) * Sg.indicator (fun _ => (1 : ℂ)) q.2 := by
    intro q
    rw [coef_split θ d M K u g q.1 q.2, Set.indicator_apply]
    rfl
  have hF := hfar g
  have hind : Integrable (Sg.indicator (fun _ => (1 : ℂ))) μ :=
    (integrable_indicator_iff hS.1).2 (by first | exact integrableOn_const.2 (Or.inr hSfin) | exact integrableOn_const hSfin.ne)
  refine ⟨?_, ?_, ?_⟩
  · rw [hνe, hemb.integrable_map_iff]
    have e : ((fun h => coef θ M K u u (g * stabilizerEmbedding d h)) ∘ fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2) =
        fun q => coefR θ M u u (g * stabilizerEmbedding d q.1) * Sg.indicator (fun _ => (1 : ℂ)) q.2 := funext pw
    rw [e]
    first | exact hF.1.mul_prod hind | exact hF.1.prod_mul hind
  · have hnorm : ∫ h, ‖coef θ M K u u (g * stabilizerEmbedding d h)‖ ∂ν =
        (∫ a, ‖coefR θ M u u (g * stabilizerEmbedding d a)‖ ∂m) * (μ Sg).toReal := by
      rw [hνe, hemb.integral_map]
      have e : ∀ q : GinfC Y × GfC Y, ‖coef θ M K u u (g * stabilizerEmbedding d ((q.1 : GA D Y) * q.2))‖ =
          ‖coefR θ M u u (g * stabilizerEmbedding d q.1)‖ * Sg.indicator (fun _ => (1 : ℝ)) q.2 := by
        intro q
        rw [pw, norm_mul]
        congr 1
        simp only [Set.indicator_apply]
        split_ifs <;> simp
      simp_rw [e]
      rw [integral_prod_mul (fun a : GinfC Y => ‖coefR θ M u u (g * stabilizerEmbedding d a)‖) (Sg.indicator (fun _ => (1 : ℝ))),
        integral_indicator_const _ hS.1]
      simp [Measure.real]
    have hN : ∏ τ, nrm θ B g⁻¹ τ (zv d) = ∏ τ, nrm θ B (stabilizerEmbedding d x) τ z := by
      refine Finset.prod_congr rfl fun τ _ => ?_
      unfold nrm
      rw [inv_inv, hg, show cmp θ τ (stabilizerEmbedding d x⁻¹ * γ) = cmp θ τ (stabilizerEmbedding d x⁻¹) * cmp θ τ γ from
        GlobalTheory.PointAtPlaceHom.infMat_mul V (θ τ) _ _, ← Matrix.mulVec_mulVec, cmp_mulVec θ hθ γ hzγ τ, summandEmbedding_inv]
    have hP : 0 ≤ (∏ τ, nrm θ B (stabilizerEmbedding d x) τ z) ^ (2 * V.rank + 5) :=
      pow_nonneg (Finset.prod_nonneg fun τ _ => Real.sqrt_nonneg _) _
    have hI : 0 ≤ ∫ a, ‖coefR θ M u u (g * stabilizerEmbedding d a)‖ ∂m := integral_nonneg fun _ => norm_nonneg _
    have hs : (μ Sg).toReal ≤ (μ K').toReal := ENNReal.toReal_mono hK'top.ne hS.2
    have h2 := hF.2
    rw [hN] at h2
    rw [hnorm, norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    calc (∫ a, ‖coefR θ M u u (g * stabilizerEmbedding d a)‖ ∂m) * (μ Sg).toReal * (∏ τ, nrm θ B (stabilizerEmbedding d x) τ z) ^ (2 * V.rank + 5)
        = (μ Sg).toReal * ((∫ a, ‖coefR θ M u u (g * stabilizerEmbedding d a)‖ ∂m) * (∏ τ, nrm θ B (stabilizerEmbedding d x) τ z) ^ (2 * V.rank + 5)) := by
          ring
      _ ≤ (μ K').toReal * (Real.exp Q * ‖c₀‖) :=
          mul_le_mul hs h2 (mul_nonneg hI hP) ENNReal.toReal_nonneg
      _ = Real.exp Q * ((μ K').toReal * ‖c₀‖) := by ring
  · intro hnot h
    by_contra hne
    unfold coef at hne
    split_ifs at hne with hk
    swap
    · exact hne rfl
    apply hnot
    rw [hK, hg] at hk
    exact vanish d Λ 𝔪 hΛ hz x γ z hzγ h hk

end GlobalTheory.SepPer.AdelicFromReal

namespace GlobalTheory.SepPer.AdelicFromReal

theorem adelicAt_of_real : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S') (M : DSModel V S) (p : Pack M₀ M) (Q : ℝ), p.Is θ d Q → ∀ (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → zv d ∈ Λ → ∀ (J : Set (GA D Y)), (∀ k ∈ GfC Y, Lev.finE V (stabilizerEmbedding d k) ∈ congLev D.sp.cm V.gram Λ 𝔪 → k ∈ J) → ∀ t ∈ MultT θ M₀ J 1, ∀ ν : Measure (GA D Y), ν.IsHaarMeasure → ∃ c, p.AdelicAt θ d Q Λ 𝔪 ν (t (PiTensorProduct.tprod ℂ p.w)) c := by
  intro hP D θ hθ Y V d S S' M₀ M p Q hp Λ 𝔪 hΛ h𝔪 hz J hJ t ht ν hν
  obtain ⟨m, μ, hm, hμ, hmσ, hμσ, hemb, hνe⟩ := GlobalTheory.T.adelicUnitaryHaar_eq_map_prod_real_finite D Y ν hν
  haveI := hmσ
  haveI := hμσ
  obtain ⟨c₀, hc⟩ := hp.2 m hm
  obtain ⟨hK'm, hK'0, hK'top⟩ := GlobalTheory.T.congruence_preimage_volume_finite D Y V d Λ 𝔪 hΛ h𝔪 μ hμ
  have hκ := ENNReal.toReal_pos hK'0.ne' hK'top.ne
  have hα : Integrable (fun h : GinfC Y => coefR θ M (p.v θ) (p.v θ) (stabilizerEmbedding d h)) m := by
    simpa using (hc.far 1).1
  refine ⟨_, mul_ne_zero (Complex.ofReal_ne_zero.2 hκ.ne') hc.ne, fun x => ?_, fun x γ z _ hzγ => ?_⟩
  · exact one_clause θ d M _ (p.v θ) _ ν m μ hemb hνe _ (fun _ => Iff.rfl) hK'm
      (fun b hb g => multT_lev θ M₀ J ht p.w (hJ _ b.2 hb) g) c₀
      (fun x => GlobalTheory.T.integrable_scalar_action_multiplicityMap_values hP D θ hθ Y S' M₀ J 1 t ht p.w m hm _ c₀ hα hc.act x) x
  · exact term_clause θ hθ d M (p.v θ) p.B Q Λ 𝔪 hΛ hz ν m μ hemb hνe _ (fun _ => Iff.rfl) hK'm hK'top c₀ hc.far x γ z hzγ

end GlobalTheory.SepPer.AdelicFromReal
