import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhere
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureTransportStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresSupportStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatrixEulerProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RightMultiplicationEulerProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightMulActionLawsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMeanValueNonnegativeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitProductClosurePropertiesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Scale

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def rE {M n : ℕ} (X : Fin n → Fin M → E) (G : Matrix (Fin n) (Fin n) E) : Fin n → Fin M → E :=
  fun a i => ∑ c, X c i * G c a

theorem rE_eq {M n : ℕ} (X : Fin n → Fin M → E) (G : Matrix (Fin n) (Fin n) E) :
    Matrix.of (rE X G) = Gᵀ * Matrix.of X := by
  ext a i
  simp [rE, Matrix.mul_apply, mul_comm]

theorem rE_rE {M n : ℕ} (X : Fin n → Fin M → E) (G G' : Matrix (Fin n) (Fin n) E) :
    rE (rE X G) G' = rE X (G * G') := by
  have : Matrix.of (rE (rE X G) G') = Matrix.of (rE X (G * G')) := by
    rw [rE_eq, rE_eq, rE_eq, Matrix.transpose_mul, Matrix.mul_assoc]
  exact Matrix.of.injective this

theorem rE_one {M n : ℕ} (X : Fin n → Fin M → E) : rE X (1 : Matrix (Fin n) (Fin n) E) = X := by
  have : Matrix.of (rE X (1 : Matrix (Fin n) (Fin n) E)) = Matrix.of X := by
    rw [rE_eq, Matrix.transpose_one, Matrix.one_mul]
  exact Matrix.of.injective this

theorem gramE_eq (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → E) :
    gramE σ J X = (Matrix.of X).map (σ : E →+* E) * J * (Matrix.of X)ᵀ := by
  ext a b
  simp only [gramE, hE, hform, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem gramE_rE (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → E)
    (G : Matrix (Fin n) (Fin n) E) :
    gramE σ J (rE X G) = cT (σ : E →+* E) G * gramE σ J X * G := by
  rw [gramE_eq, gramE_eq, rE_eq, Matrix.transpose_mul, Matrix.transpose_transpose, cT,
    Matrix.map_mul, Matrix.transpose_map]
  simp only [Matrix.mul_assoc]

variable (R : Type) [CommRing R] [Algebra F R]

theorem ratTup_rE {M n : ℕ} (X : Fin n → Fin M → E) (G : Matrix (Fin n) (Fin n) E) :
    ratTup (F := F) R (rE X G) = rmul R (ratTup R X) (G.map (inclR R)) := by
  funext a i
  simp [ratTup, rE, rmul, map_sum, map_mul]

theorem cT_map_incl (σ : E →ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) :
    cT (sigR R σ) (G.map (inclR R)) = (cT (σ : E →+* E) G).map (inclR R) := by
  ext a b
  simp [cT, sigR, inclR]

def tauH (σ : E →ₐ[F] E) (hinv : ∀ x, σ (σ x) = x) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (S : HermR R σ n) : HermR R σ n :=
  ⟨cT (sigR R σ) G * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * G, by
    have hS : cT (sigR R σ) (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = S := by
      ext a b
      exact S.2 a b
    have hG : cT (sigR R σ) (cT (sigR R σ) G) = G := by
      ext a b
      exact HaarCoord.sigR_sigR R hinv (G a b)
    have key : cT (sigR R σ) (cT (sigR R σ) G * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * G) =
        cT (sigR R σ) G * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * G := by
      rw [cT_mul, cT_mul, hS, hG, Matrix.mul_assoc]
    intro a b
    exact congrFun (congrFun key a) b⟩

theorem tauH_hermOf (σ : E →ₐ[F] E) (hinv : ∀ x, σ (σ x) = x) {n : ℕ}
    (H T T' : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b)
    (hT' : ∀ a b, σ (T' b a) = T' a b) (hrel : cT (σ : E →+* E) H * T' * H = T) :
    tauH R σ hinv (H.map (inclR R)) (hermOf R σ T' hT') = hermOf R σ T hT := by
  apply Subtype.ext
  change cT (sigR R σ) (H.map (inclR R)) * T'.map (inclR R) * H.map (inclR R) = T.map (inclR R)
  rw [cT_map_incl, ← hrel, Matrix.map_mul, Matrix.map_mul]

end Alg

section Top

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem measurable_rmul (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R]
    [T2Space R] (n M : ℕ) (G : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Measurable (fun X : Fin n → Fin M → R ⊗[F] E => rmul R X G) := by
  obtain ⟨t1, -, t3, -, -, -, -, t8, -, -⟩ := TopK.topTens_props F E σ hcm R
  haveI := t8 n M
  have hc : Continuous (fun X : Fin n → Fin M → R ⊗[F] E => rmul R X G) :=
    continuous_pi fun a => continuous_pi fun i => continuous_finset_sum _ fun c _ => by
      have h : Continuous fun X : Fin n → Fin M → R ⊗[F] E => X c i :=
        (continuous_apply i).comp (continuous_apply c)
      exact h.mul continuous_const
  exact hc.measurable

theorem unitary_conjugate_local (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (hinv : ∀ x, σ (σ x) = x) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) {n d : ℕ}
    (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hm : IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m)
    (H T T' : Matrix (Fin n) (Fin n) E) (hH : H.det ≠ 0) (hT : ∀ a b, σ (T b a) = T a b)
    (hT' : ∀ a b, σ (T' b a) = T' a b) (hrel : cT (σ : E →+* E) H * T' * H = T)
    (a c : ℝ≥0) (hc : c ≠ 0)
    (ha : ∀ μ : Measure (Fin n → Fin M → R ⊗[F] E), μ.IsAddHaarMeasure →
      μ.map (fun X => rmul R X (H.map (inclR R))) = a • μ)
    (hc' : ∀ ν : Measure (HermR R σ n), ν.IsAddHaarMeasure → ∀ τ : HermR R σ n → HermR R σ n,
      (∀ S, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) (H.map (inclR R)) *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * H.map (inclR R)) → ν.map τ = c • ν) :
    (m (hermOf R σ T' hT')).map (fun X => rmul R X (H.map (inclR R))) =
      (a / c) • m (hermOf R σ T hT) := by
  have hR' := hR
  obtain ⟨r1, r2, r3, r4, -⟩ := hR'
  obtain ⟨-, hW, hHm⟩ := coord_measures_haar F E σ hcm R d b lam hlam
  have hμ := hW n M
  have hν := hHm n
  have hdet : IsUnit (H.map (inclR (F := F) R)).det := by
    have h1 : IsUnit ((inclR (F := F) R) H.det) := (IsUnit.mk0 _ hH).map (inclR (F := F) R)
    rw [RingHom.map_det] at h1
    exact h1
  let τ := tauH R σ hinv (H.map (inclR R))
  have key := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hcm M J hJ R hR n _ _ m hμ hν hm (H.map (inclR R)) hdet τ
    (fun S => rfl) a c (ha _ hμ) (hc' _ hν τ (fun S => rfl)) (hermOf R σ T' hT')
  have hτ : τ (hermOf R σ T' hT') = hermOf R σ T hT := tauH_hermOf R σ hinv H T T' hT hT' hrel
  rw [hτ] at key
  rw [div_eq_inv_mul, mul_smul, key, inv_smul_smul₀ hc]

theorem projInf_rmul {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) (G : Matrix (Fin n) (Fin n) E) :
    projInf (rmul (AF F) X (G.map (inclR (AF F)))) = rmul (Ainf F) (projInf X) (G.map (inclR (Ainf F))) := by
  funext a i
  simp [projInf, rmul, map_sum, map_mul, inclR]

theorem projV_rmul (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E)
    (G : Matrix (Fin n) (Fin n) E) :
    projV v (projFin (rmul (AF F) X (G.map (inclR (AF F))))) =
      rmul (Fv F v) (projV v (projFin X)) (G.map (inclR (Fv F v))) := by
  funext a i
  simp [projV, projFin, rmul, map_sum, map_mul, inclR]

end Top

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem theta_map (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J))
    (hH : IsHaarH F E σ M J μ) (hF : IsFDH F E σ M J μ 𝓕) {n : ℕ}
    (G H T T' : Matrix (Fin n) (Fin n) E) (hGH : G * H = 1) (hHG : H * G = 1)
    (h1 : cT (σ : E →+* E) H * T' * H = T) (h2 : cT (σ : E →+* E) G * T * G = T')
    (he : Measurable fun X : Fin n → Fin M → AF F ⊗[F] E =>
      rmul (AF F) X (H.map (inclR (F := F) (AF F)))) :
    (thetaMeas σ J μ 𝓕 {X : Fin n → Fin M → E | gramE σ J X = T'}).map
        (fun X => rmul (AF F) X (H.map (inclR (F := F) (AF F)))) =
      thetaMeas σ J μ 𝓕 {X : Fin n → Fin M → E | gramE σ J X = T} := by
  refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
  rw [lintegral_map hΦ he,
    GlobalTheory.T.siegel_mean_value_nonnegative F E σ hcm M J hJ μ 𝓕 hH hF n _
      (fun X => Φ (rmul (AF F) X (H.map (inclR (F := F) (AF F))))) (hΦ.comp he),
    GlobalTheory.T.siegel_mean_value_nonnegative F E σ hcm M J hJ μ 𝓕 hH hF n _ Φ hΦ]
  congr 1
  refine lintegral_congr fun h => ?_
  let eqv : ({X : Fin n → Fin M → E | gramE σ J X = T'} : Set _) ≃
      ({X : Fin n → Fin M → E | gramE σ J X = T} : Set _) :=
    { toFun := fun X => ⟨rE X.1 H, by
        have hX : gramE σ J X.1 = T' := X.2
        change gramE σ J (rE X.1 H) = T
        rw [gramE_rE, hX, h1]⟩
      invFun := fun X => ⟨rE X.1 G, by
        have hX : gramE σ J X.1 = T := X.2
        change gramE σ J (rE X.1 G) = T'
        rw [gramE_rE, hX, h2]⟩
      left_inv := fun X => Subtype.ext (by
        change rE (rE X.1 H) G = X.1
        rw [rE_rE, hHG, rE_one])
      right_inv := fun X => Subtype.ext (by
        change rE (rE X.1 G) H = X.1
        rw [rE_rE, hGH, rE_one]) }
  rw [← eqv.tsum_eq (fun X => Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))))]
  refine tsum_congr fun X => ?_
  change Φ (rmul (AF F) (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) (H.map (inclR (F := F) (AF F)))) =
    Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (rE X.1 H)))
  rw [ratTup_rE]
  unfold actW
  rw [(GlobalTheory.T.gram_right_mul_action_laws F E σ hcm (AF F) M n J (ratTup (AF F) X.1)
    (H.map (inclR (F := F) (AF F))) 1).2.2.2 _]

end Main

theorem sw_scale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (g : GL (Fin n) E) (T' : Matrix (Fin n) (Fin n) E) (hT' : ∀ a b, σ (T' b a) = T' a b), T' = cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * g → SWMeas σ J T' hT' → SWMeas σ J T hT := by
  intro F E _ _ _ _ _ σ hcm M J hJ n T hT _ g T' hT' hrel hSW d b laminf lam hinf hv μ 𝓕 hH hF minf m
    hminf hm
  have hinv := (HaarCoord.conj_facts hcm).1
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin n) (Fin n) E, G = (g : Matrix (Fin n) (Fin n) E) := ⟨_, rfl⟩
  obtain ⟨H, hHd⟩ : ∃ H : Matrix (Fin n) (Fin n) E, H = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) :=
    ⟨_, rfl⟩
  have hGH : G * H = 1 := by rw [hG, hHd]; exact Units.mul_inv g
  have hHG : H * G = 1 := by rw [hG, hHd]; exact Units.inv_mul g
  rw [← hG] at hrel
  have hdetH : H.det ≠ 0 := by
    intro h0
    have : H.det * G.det = 1 := by rw [← Matrix.det_mul, hHG, Matrix.det_one]
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hrel' : cT (σ : E →+* E) H * T' * H = T := by
    rw [hrel]
    calc cT (σ : E →+* E) H * (cT (σ : E →+* E) G * T * G) * H
        = (cT (σ : E →+* E) H * cT (σ : E →+* E) G) * T * (G * H) := by
          simp only [Matrix.mul_assoc]
      _ = T := by rw [← cT_mul, hGH, cT_one, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨ai, a, hau, hai, hav⟩ := GlobalTheory.T.right_multiplication_euler_product F E σ hcm n M H hdetH
  obtain ⟨ci, c, hcu, hci, hcv⟩ := GlobalTheory.T.hermitian_matrix_euler_product F E σ hcm n H hdetH
  obtain ⟨-, -, -, -, hq, -⟩ := GlobalTheory.T.unit_product_closure_properties F ai ci a c hau hcu
  obtain ⟨hci0, hc0, -⟩ := GlobalTheory.T.unit_product_closure_properties F ci ai c a hcu hau
  have hrI : IsLocR (Ainf F) := isLocR_Ainf F hcm.1
  have hrV : ∀ v, IsLocR (Fv F v) := fun v => LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have sInf := unitary_conjugate_local σ hcm hinv J hJ (Ainf F) hrI b laminf hinf.1 minf hminf H T T' hdetH hT hT'
    hrel' ai ci hci0 hai hci
  have sV := fun v => unitary_conjugate_local σ hcm hinv J hJ (Fv F v) (hrV v) b (lam v) (hv v).1 (m v) (hm v) H T T'
    hdetH hT hT' hrel' (a v) (c v) (hc0 v) (hav v) (hcv v)
  obtain ⟨⟨t1, t2, t3⟩, -⟩ := AdeleTop.adele_top F
  have me := measurable_rmul σ hcm (AF F) n M (H.map (inclR (F := F) (AF F)))
  have mi : Measurable fun X : Fin n → Fin M → Ainf F ⊗[F] E =>
      rmul (Ainf F) X (H.map (inclR (F := F) (Ainf F))) := by
    obtain ⟨r1, r2, r3, r4, -⟩ := hrI
    exact measurable_rmul σ hcm (Ainf F) n M _
  have mv : ∀ v, Measurable fun X : Fin n → Fin M → Fv F v ⊗[F] E =>
      rmul (Fv F v) X (H.map (inclR (F := F) (Fv F v))) := by
    intro v
    obtain ⟨r1, r2, r3, r4, -⟩ := hrV v
    exact measurable_rmul σ hcm (Fv F v) n M _
  have hE := hSW d b laminf lam hinf hv μ 𝓕 hH hF minf m hminf hm
  have hth := theta_map σ hcm J hJ μ 𝓕 hH hF G H T T' hGH hHG hrel' hrel.symm me
  have hlat := (GlobalTheory.T.adelic_tuple_projections F E σ hcm d b n M).2.2.2
  have hfin : ∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤ := by
    intro v
    obtain ⟨r1, r2, r3, r4, -⟩ := id (hrV v)
    obtain ⟨-, hW, hHm⟩ := coord_measures_haar F E σ hcm (Fv F v) d b (lam v) (hv v).1
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm M J hJ (Fv F v) (hrV v) n _ _ (m v) (hW n M) (hHm n) (hm v)
      (hermOf (Fv F v) σ T hT)).1
    exact (hlat.1 v).1.measure_lt_top
  rw [← hth]
  exact GlobalTheory.T.euler_product_measure_transport F E σ hcm d b n M _ (minf (hermOf (Ainf F) σ T' hT')) (minf (hermOf (Ainf F) σ T hT))
    (fun v => m v (hermOf (Fv F v) σ T' hT')) (fun v => m v (hermOf (Fv F v) σ T hT))
    (fun X => rmul (AF F) X (H.map (inclR (F := F) (AF F))))
    (fun X => rmul (Ainf F) X (H.map (inclR (F := F) (Ainf F))))
    (fun v X => rmul (Fv F v) X (H.map (inclR (F := F) (Fv F v)))) me mi mv
    (fun X => ⟨projInf_rmul X H, fun v => projV_rmul v X H⟩)
    ((LatRat.latV_rational F E σ hcm d b n M).1 H hdetH)
    (ai / ci) (fun v => a v / c v) hq sInf sV hfin hE

end GlobalTheory.CompanionTheory.SW.Scale
