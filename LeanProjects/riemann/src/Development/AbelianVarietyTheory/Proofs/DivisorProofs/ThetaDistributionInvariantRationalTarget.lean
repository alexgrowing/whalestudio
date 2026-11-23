import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDetSmulSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussSumNondegenerateFiniteHermitianModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexMapNsmulComapEqAbsNormDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLatticeSelfDualFgFullIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGaussianRealIsometryNoFixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaTildeHeckeCharSplitMulSignOfNormFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionCommQuasiReflectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsometryVacuumScalarGaussSumIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSubstitutionThetaHeisenbergUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCharacter
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatAut

open GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.SplitScalar

variable {D : D7}

section Main

open GlobalTheory.SplitDetChar

theorem cut_add {R : Type} [CommRing R] {a b : R} (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0)
    (h : (a + b) * (a + b) = a + b) (u : Rˣ) : cut _ h u = cut a ha u * cut b hb u := Units.ext (by
  rw [Units.val_mul, cut_val, cut_val, cut_val]
  linear_combination (-((u : R) - 1) ^ 2) * hab)

theorem phase_identity {G H : Type} [CommGroup G] [CommGroup H] (φ φ' : G →* H) (st : G → G)
    (h : ∀ u, φ' u * φ (st u) = φ u) {x y s N : G} {z : H} (h0 : z * φ x = 1) (h1 : x * st x = 1) (h2 : x * st y = s * y) :
    z * φ' (N * x) = φ s * φ' (N * y) := by
  have v1 := congrArg φ h1
  have v2 := congrArg φ h2
  simp only [map_mul, map_one] at v1 v2 ⊢
  rw [eq_inv_of_mul_eq_one_left h0, eq_mul_inv_of_mul_eq (h x), eq_mul_inv_of_mul_eq (h y),
    eq_inv_of_mul_eq_one_right v1, eq_inv_mul_of_mul_eq v2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_idempotentUnitEmbeddings_character_relation {R E H : Type} [CommRing R] [Field E] [StarRing E] [CommGroup H] (σ : R →+* R)
    (hσ : ∀ x, σ (σ x) = x) (j : E →+* R) (hj : ∀ x, σ (j x) = j (star x)) (η : Rˣ →* H)
    (hη : ∀ x y : Rˣ, (y : R) = x * σ x → η y = 1) {ε : R} (h1 : ε * ε = ε) (h2 : ε * σ ε = 0) :
    ∃ (c c' : Eˣ →* Rˣ), (∀ u, (c u : R) = ε * j u + (1 - ε)) ∧
      (∀ u, (c' u : R) = (ε + σ ε) * j u + (1 - (ε + σ ε))) ∧ ∀ u, η (c' u) * η (c (star u)) = η (c u) := by
  have h3 : σ ε * σ ε = σ ε := by rw [← map_mul, h1]
  have h4 : (ε + σ ε) * (ε + σ ε) = ε + σ ε := by linear_combination h1 + h3 + 2 * h2
  let i : Eˣ →* Rˣ := Units.map j.toMonoidHom
  refine ⟨(cut ε h1).comp i, (cut _ h4).comp i, fun _ => rfl, fun _ => rfl, fun u => ?_⟩
  have e1 := cut_add h1 h3 h2 h4 (i u)
  have e3 : (cut ε h1 (i (star u)) : R) = σ (cut _ h3 (i u) : R) := by
    show ε * j (star (u : E)) + (1 - ε) = σ (σ ε * j u + (1 - σ ε))
    rw [map_add, map_mul, map_sub, map_one, hσ, hj]
  have e2 := hη (cut _ h3 (i u)) (cut _ h3 (i u) * cut ε h1 (i (star u))) (by rw [Units.val_mul, e3])
  show η (cut _ h4 (i u)) * η (cut ε h1 (i (star u))) = η (cut ε h1 (i u))
  rw [e1, map_mul, mul_assoc, ← map_mul, e2, mul_one]

theorem exists_phi {η : (AE D)ˣ →* Circle} (hη : ResEta D η 1) {ε : AE D} (hε : IsHalfIdem D ε) :
    ∃ (c c' : D.host.Eˣ →* (AE D)ˣ), (∀ u, (c u : AE D) = ε * incA D u + (1 - ε)) ∧
      (∀ u, (c' u : AE D) = (ε + cA D ε) * incA D u + (1 - (ε + cA D ε))) ∧
      ∀ u, η (c' u) * η (c (star u)) = η (c u) :=
  exists_idempotentUnitEmbeddings_character_relation (cA D) GlobalTheory.DualPairCheck.cA_cA (incA D) GlobalTheory.DualPairCheck.cA_incA η (char_norm hη) hε.1 hε.2.1

variable {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {η : (AE D)ˣ →* Circle} {of oi : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}

theorem hecke_pow (hη : IsEtaTilde D η) (n : ℕ) : IsHeckeChar D (η ^ n) ∧ ResEta D (η ^ n) n :=
  ⟨⟨hη.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, hη.1.2, one_pow]⟩, hη.2.2.1.1, fun e he a => by
    rw [MonoidHom.pow_apply, hη.2.2.1.2 e he, pow_one]⟩

theorem oi_vac (hi : IsInfWeil ψ θ S T oi) (cS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ))
    (cT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) (g : GA D S) (h : GA D T)
    (hg : ∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt S g) = compAt θ τ (Formalism.L2.Theta.mt S g) * sS τ)
    (hh : ∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) :
    oi (g, h) f = (∏ τ, detPlus (sS τ) (sT τ) (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹))
      (compAt θ τ (Formalism.L2.Theta.mt T h))) • f := by
  obtain ⟨a, k, a1, a2, k1, k2, e1, -⟩ := exists_parts (g, h)
  have e2 : g = a.1 * k.1 := congrArg Prod.fst e1
  have e3 : h = a.2 * k.2 := congrArg Prod.snd e1
  have c1 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt S g) = compAt θ τ (Formalism.L2.Theta.mt S a.1) := fun τ => by
    rw [e2, compAt_mul, compAt_fin θ τ k1, Matrix.mul_one]
  have c2 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T a.2) := fun τ => by
    rw [e3, compAt_mul, compAt_fin θ τ k2, Matrix.mul_one]
  have c3 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt S g⁻¹) = compAt θ τ (Formalism.L2.Theta.mt S a.1⁻¹) := fun τ => by
    rw [e2, _root_.mul_inv_rev, compAt_mul, compAt_fin θ τ (inv_mem k1), Matrix.one_mul]
  simp only [c1, c2, c3] at hg hh ⊢
  rw [e1, map_mul, Module.End.mul_apply, hi.triv k.1 k1 k.2 k2 f hf]
  exact hi.vac sS sT cS cT a.1 a1 a.2 a2 hg hh f hf hv

theorem final_algebra {c δ z ln li lc I P Q Z e y₁ y₂ s : ℂ} {r₁ r₂ r₃ r₄ : ℝ} {n : ℕ} (p₁ : 0 < r₁) (p₂ : 0 < r₂)
    (p₃ : 0 < r₃) (p₄ : 0 < r₄) (hn : n ≠ 0) (hc : c ≠ 0) (hδ : δ ≠ 0) (hz : z ≠ 0)
    (h1 : ln * I = r₁ * (c⁻¹ * δ * z * li⁻¹)) (h2 : I * P = r₂ * e * (Q * δ))
    (h3 : y₁ * (lc * ln) * (Z * P) = r₃) (h4 : y₂ * (lc * li) * (Z * Q) = r₄) (h5 : ln ^ 2 = n) (h6 : z * y₂ = s * y₁) :
    ∃ r : ℝ, 0 < r ∧ c * e = r * s := by
  have q₁ : (r₁ : ℂ) ≠ 0 := by exact_mod_cast p₁.ne'
  have q₂ : (r₂ : ℂ) ≠ 0 := by exact_mod_cast p₂.ne'
  have q₃ : (r₃ : ℂ) ≠ 0 := by exact_mod_cast p₃.ne'
  have q₄ : (r₄ : ℂ) ≠ 0 := by exact_mod_cast p₄.ne'
  have qn : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hli : li ≠ 0 := by
    rintro rfl
    apply q₄
    rw [← h4]; ring
  have h7 : c * li * ln * I = r₁ * δ * z := by
    rw [mul_assoc, h1]; field_simp
  have h8 : c * li * ln * r₂ * e * Q = r₁ * z * P := by
    refine mul_right_cancel₀ hδ ?_
    linear_combination P * h7 - c * li * ln * h2
  refine ⟨r₁ * r₃ / (r₂ * r₄ * n), by positivity, ?_⟩
  push_cast
  field_simp
  linear_combination (ln * y₂ * lc * Z) * h8 - (c * e * r₂ * n) * h4 + (r₁ * s) * h3 + (r₁ * ln * lc * Z * P) * h6
    - (c * e * r₂ * y₂ * lc * li * Z * Q) * h5

set_option maxHeartbeats 1000000 in

theorem scalar_const (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hη : IsEtaTilde D η) (hf : IsFinWeil ψ S T ΛS ΛT (η ^ S.rank) (η ^ T.rank) of) (hi : IsInfWeil ψ θ S T oi)
    (cS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (cT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) :
    ∃ e s : ℂ, s ≠ 0 ∧ ∀ g h a b, IsRat S g a → IsRat T h⁻¹ b →
      (∀ τ, sS τ * a.map (tauE D τ) = a.map (tauE D τ) * sS τ) → (∀ τ, sT τ * b.map (tauE D τ) = b.map (tauE D τ) * sT τ) →
      (b ⊗ₖ aᵀ - 1).det ≠ 0 → ∀ c : ℂ, c ≠ 0 → IsScalar ψ of oi (g, h) c → ∃ r : ℝ, 0 < r ∧ c * e = r * s := by
  obtain ⟨lam, hlam, hsq⟩ := exists_goodNorm D
  obtain ⟨w, Om, hO⟩ := exists_isLatRep hψ hS hT hlam
  obtain ⟨ε, hε⟩ := exists_isHalfIdem D
  obtain ⟨κ, κ', k1, k2, k3⟩ := exists_phi hη.2.2.1 hε
  obtain ⟨e, he⟩ := GlobalTheory.T.integral_gaussian_real_isometry_no_fixed D S T sS sT cS cT
  refine ⟨e, η (κ ((-1) ^ Fintype.card (Fin T.rank × Fin S.rank))), Circle.coe_ne_zero _,
    fun g h a b ha hb sa sb hd c hc H => ?_⟩
  obtain ⟨d1, d2⟩ := det_unitary_sub_one (P := T.gram ⊗ₖ S.gram⁻¹ᵀ) (by
    rw [Matrix.det_kronecker, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (GlobalTheory.LatVac.gram_det_isUnit T).ne_zero)
      (pow_ne_zero _ (Matrix.isUnit_nonsing_inv_det _ (GlobalTheory.LatVac.gram_det_isUnit S)).ne_zero))
    (kronecker_unitary (GlobalTheory.LatVac.gram_det_isUnit S) ha.unitary hb.unitary)
  have hΔ := left_ne_zero_of_mul_eq_one d1
  obtain ⟨hbij, n, t, c₀, N, M, hn, hc₀, hN, t1, t2, g1, g2, i1, i2⟩ := finite_data hψ hS hT hlam hO.hw ha hb hΔ hd
  have hk : ∀ τ, b.map (tauE D τ) ⊗ₖ (a.map (tauE D τ))ᵀ = (tauE D τ).mapMatrix (b ⊗ₖ aᵀ) := fun τ => by
    ext i j
    exact ((tauE D τ).map_mul _ _).symm
  have hk1 : ∀ τ, (b.map (tauE D τ) ⊗ₖ (a.map (tauE D τ))ᵀ).det = tauE D τ (b ⊗ₖ aᵀ).det := fun τ => by
    rw [hk, RingHom.map_det]
  have hk2 : ∀ τ, (b.map (tauE D τ) ⊗ₖ (a.map (tauE D τ))ᵀ - 1).det = tauE D τ (b ⊗ₖ aᵀ - 1).det := fun τ => by
    rw [hk, RingHom.map_det, map_sub, map_one]
  have hb' : ∀ τ, b.map (tauE D τ) * compAt θ τ (Formalism.L2.Theta.mt T h) = 1 := fun τ => by
    rw [← hb.compAt hθ, ← compAt_mul, inv_mul_cancel, compAt_fin θ τ (one_mem _)]
  obtain ⟨hI, r₂, p₂, h2⟩ := he (fun τ => a.map (tauE D τ)) (fun τ => compAt θ τ (Formalism.L2.Theta.mt S g⁻¹))
    (fun τ => b.map (tauE D τ)) (fun τ => compAt θ τ (Formalism.L2.Theta.mt T h)) fun τ =>
    ⟨by rw [← ha.compAt hθ, ← compAt_mul, mul_inv_cancel, compAt_fin θ τ (one_mem _)], hb' τ,
      map_tau_unitary ha.unitary τ, map_tau_unitary hb.unitary τ, sa τ, sb τ,
      by rw [hk2]; exact (map_ne_zero _).2 hd⟩
  simp only [hk1, hk2, Finset.prod_mul_distrib] at h2
  have hv := oi_vac hi cS cT g h (fun τ => by rw [ha.compAt hθ]; exact sa τ) fun τ => by
    have e1 := mul_eq_one_comm.1 (hb' τ)
    calc _ = compAt θ τ (Formalism.L2.Theta.mt T h) * (b.map (tauE D τ) * sT τ) * compAt θ τ (Formalism.L2.Theta.mt T h) := by
          rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
      _ = _ := by rw [← sb, Matrix.mul_assoc, Matrix.mul_assoc, hb', Matrix.mul_one]
  set δ := ∏ τ, detPlus (sS τ) (sT τ) (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h)) with hδ
  have hδ0 : δ ≠ 0 := fun h0 => by
    obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T sS sT cS cT ΛS ΛT hS hT
    have h1 := hf 1
    simp only [one_mul] at h1
    have h3 := hv f h1.1 h1.2.2
    rw [h0, zero_smul] at h3
    apply f0
    have h4 : oi ((g, h)⁻¹ * (g, h)) f = 0 := by rw [map_mul, Module.End.mul_apply, h3, map_zero]
    rwa [inv_mul_cancel, map_one] at h4
  have da : a.det ≠ 0 := left_ne_zero_of_mul_eq_one
    (det_unitary_sub_one (GlobalTheory.LatVac.gram_det_isUnit S).ne_zero ha.unitary).1
  have db : b.det ≠ 0 := left_ne_zero_of_mul_eq_one
    (det_unitary_sub_one (GlobalTheory.LatVac.gram_det_isUnit T).ne_zero hb.unitary).1
  have hof := GlobalTheory.T.finiteWeilRep_eq_latticeIntertwiner_mul_character D ψ hψ S T ΛS ΛT hS hT _ _ _ _ (hecke_pow hη _).1 (hecke_pow hη _).1 (hecke_pow hη _).2
    (hecke_pow hη _).2 of hf lam hlam hsq w Om hO ε hε g h (κ (Units.mk0 _ da)) (κ (Units.mk0 _ db)⁻¹)
    (by rw [k1, show Formalism.L2.Theta.mt S g = _ from ha, Units.val_mk0, RingHom.map_det]; rfl)
    (by
      have e1 := congrArg Matrix.det (mt_mul_inv T h)
      rw [Matrix.det_mul, Matrix.det_one, show Formalism.L2.Theta.mt T h⁻¹ = _ from hb, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at e1
      rw [k1, Units.val_inv_eq_inv_val, Units.val_mk0]
      congr 2
      rw [← one_mul (incA D _), ← e1, mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ db, RingHom.map_one, mul_one])
  set z := ((η ^ T.rank) (κ (Units.mk0 _ da)))⁻¹ * (η ^ S.rank) (κ (Units.mk0 _ db)⁻¹) with hz
  obtain ⟨r₁, p₁, h1⟩ := GlobalTheory.T.rationalIsometry_vacuumScalar_gaussSum_integral D ψ hψ θ hθ S T sS sT cS cT ΛS ΛT hS hT w hO.hw g h a b ha hb hbij hI
    (c⁻¹ * δ * z * (lam (idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h)))))⁻¹)
    (fun f f1 f2 x => by
      have e1 := congrFun (H f f.2) x
      rw [hv f f.2 f2, map_smul, hof, hO.vac _ f f1, normOp, Submodule.coe_smul] at e1
      simp only [Pi.smul_apply, smul_eq_mul, subst_apply] at e1
      rw [← one_mul (f.1 _), ← inv_mul_cancel₀ hc, mul_assoc, ← e1]
      ring) n t t1 t2
  rw [g1] at h1
  have hN' : (N : D.host.E) ^ M ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN)
  obtain ⟨r₃, p₃, h3⟩ := GlobalTheory.T.etaTildeHeckeChar_split_mul_sign_of_norm_formula D η hη lam hlam hsq ε hε _ _ (mul_ne_zero hN' hd) i1
    (κ' (Units.mk0 _ hN' * Units.mk0 _ hd)) (k2 _)
  obtain ⟨r₄, p₄, h4⟩ := GlobalTheory.T.etaTildeHeckeChar_split_mul_sign_of_norm_formula D η hη lam hlam hsq ε hε _ _ (mul_ne_zero hN' hΔ) i2
    (κ' (Units.mk0 _ hN' * Units.mk0 _ hΔ)) (k2 _)
  simp only [map_mul (tauE D _), map_mul lam, Finset.prod_mul_distrib] at h3 h4
  refine final_algebra p₁ p₂ p₃ p₄ hn hc hδ0 (Circle.coe_ne_zero z) h1 h2 h3 h4 g2 ?_
  rw [← Circle.coe_mul, ← Circle.coe_mul]
  congr 1
  have u0 : Units.mk0 _ hΔ = Units.mk0 _ db ^ S.rank * Units.mk0 _ da ^ T.rank := Units.ext (by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0, Units.val_mk0,
      Matrix.det_kronecker, Matrix.det_transpose, Fintype.card_fin, Fintype.card_fin])
  have u1 : Units.mk0 _ hΔ * star (Units.mk0 _ hΔ) = 1 := Units.ext d1
  have u2 : Units.mk0 _ hΔ * star (Units.mk0 _ hd) = (-1) ^ Fintype.card (Fin T.rank × Fin S.rank) * Units.mk0 _ hd :=
    Units.ext (by simpa using d2)
  have v0 : z * η (κ (Units.mk0 _ hΔ)) = 1 := by
    rw [hz, u0]
    simp only [MonoidHom.pow_apply, map_mul, map_pow, map_inv]
    group
  exact phase_identity (η.comp κ) (η.comp κ') star k3 v0 u1 u2

end Main

section Final

variable {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {η : (AE D)ˣ →* Circle} {of oi : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}

theorem of_oi_comm (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hη : IsEtaTilde D η) (hf : IsFinWeil ψ S T ΛS ΛT (η ^ S.rank) (η ^ T.rank) of) (hi : IsInfWeil ψ θ S T oi)
    (p q : GA D S × GA D T) (f : WO S T → ℂ) (h : IsThetaFunO ψ S T f) : of p (oi q f) = oi q (of p f) := by
  obtain ⟨lam, hlam, hsq⟩ := exists_goodNorm D
  obtain ⟨w, Om, hO⟩ := exists_isLatRep hψ hS hT hlam
  obtain ⟨ε, hε⟩ := exists_isHalfIdem D
  exact oi_comm hψ hi hO (fun p => ⟨_, GlobalTheory.T.finiteWeilRep_eq_latticeIntertwiner_mul_character D ψ hψ S T ΛS ΛT hS hT _ _ _ _ (hecke_pow hη _).1 (hecke_pow hη _).1
    (hecke_pow hη _).2 (hecke_pow hη _).2 of hf lam hlam hsq w Om hO ε hε p.1 p.2
    (GlobalTheory.SplitDetChar.cut ε hε.1 (Matrix.GeneralLinearGroup.det (matHom S p.1)))
    (GlobalTheory.SplitDetChar.cut ε hε.1 (Matrix.GeneralLinearGroup.det (matHom T p.2))) rfl rfl⟩) p q f h

set_option maxHeartbeats 1000000 in

theorem isScalar_one_of_comm (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hη : IsEtaTilde D η) (hf : IsFinWeil ψ S T ΛS ΛT (η ^ S.rank) (η ^ T.rank) of) (hi : IsInfWeil ψ θ S T oi)
    (cS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (cT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {g : GA D S} {h : GA D T} {a b} (ha : IsRat S g a) (hb : IsRat T h⁻¹ b)
    (sa : ∀ τ, sS τ * a.map (tauE D τ) = a.map (tauE D τ) * sS τ)
    (sb : ∀ τ, sT τ * b.map (tauE D τ) = b.map (tauE D τ) * sT τ) : IsScalar ψ of oi (g, h) 1 := by
  obtain ⟨e, s, hs, H⟩ := scalar_const hψ hθ hS hT hη hf hi cS cT
  obtain ⟨t, ht, ht'⟩ := (infinite_norm_one D).exists_notMem_finite
    ((finite_det_smul_sub_one (b ⊗ₖ aᵀ)).union (finite_det_smul_sub_one
      ((1 : Matrix (Fin T.rank) (Fin T.rank) D.host.E) ⊗ₖ (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E)ᵀ)))
  rw [Set.mem_union, not_or] at ht'
  obtain ⟨k, hk, rk⟩ := exists_of_unitary T (a := t • 1) (by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul, show t * star t = 1 from ht, one_smul])
  have hsm : ∀ (m : Matrix (Fin T.rank) (Fin T.rank) D.host.E) τ,
      (t • m).map (tauE D τ) = tauE D τ t • m.map (tauE D τ) := fun m τ => by
    ext i j
    exact (tauE D τ).map_mul _ _
  have hone : ∀ (n : ℕ) τ, (1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = 1 := fun n τ =>
    Matrix.map_one _ (tauE D τ).map_zero (tauE D τ).map_one
  have hh : h ∈ GQ T := (inv_mem_iff).1 hb.mem
  obtain ⟨c, hc, sc⟩ := exists_isScalar (p := (g, h)) hψ hf hi ha.mem hh
  obtain ⟨c', hc', sc'⟩ := exists_isScalar (p := (1, k⁻¹)) hψ hf hi (one_mem _) (inv_mem hk)
  have hc0 : c ≠ 0 := norm_ne_zero_iff.1 (hc ▸ one_ne_zero)
  have hc0' : c' ≠ 0 := norm_ne_zero_iff.1 (hc' ▸ one_ne_zero)
  obtain ⟨r', p', e'⟩ := H 1 k⁻¹ 1 (t • 1) (isRat_one S) (by rwa [inv_inv])
    (fun τ => by rw [hone, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hsm, hone, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
    (by rw [Matrix.smul_kronecker]; exact ht'.2) c' hc0' sc'
  obtain ⟨r, p, e''⟩ := H (g * 1) (h * k⁻¹) a (t • b) (by rwa [mul_one])
    (by
      have := rk.mul hb
      rwa [Matrix.smul_mul, Matrix.one_mul, ← inv_inv k, ← _root_.mul_inv_rev] at this)
    sa (fun τ => by rw [hsm, Matrix.mul_smul, Matrix.smul_mul, sb])
    (by rw [Matrix.smul_kronecker]; exact ht'.1) (c * c') (mul_ne_zero hc0 hc0')
    (sc.mul hψ hi (of_oi_comm hψ hS hT hη hf hi) sc' (one_mem _) (inv_mem hk))
  have q' : (r' : ℂ) ≠ 0 := by exact_mod_cast p'.ne'
  have e1 : c = ((r / r' : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, eq_div_iff q']
    refine mul_right_cancel₀ hs ?_
    rw [← e'', mul_assoc, ← e', mul_assoc]
  have e2 : r / r' = 1 := by
    rw [e1, Complex.norm_real, Real.norm_of_nonneg (div_pos p p').le] at hc
    exact hc
  rwa [e1, e2, Complex.ofReal_one] at sc

theorem exists_cartan_refl (V : HSp D) (x : Fin V.rank → D.host.E) (c : D.host.E) (hx : star x ⬝ᵥ V.gram *ᵥ x ≠ 0)
    (τ : D.what₂.Tau) : ∃ s, IsCartanInv (gramAt D V τ) s ∧
      s * (1 + c • Matrix.vecMulVec x (star x ᵥ* V.gram)).map (tauE D τ) =
        (1 + c • Matrix.vecMulVec x (star x ᵥ* V.gram)).map (tauE D τ) * s := by
  have e0 : star (tauE D τ ∘ x) = tauE D τ ∘ star x := funext fun i => (tauE_star τ (x i)).symm
  obtain ⟨s, h1, h2⟩ := GlobalTheory.T.exists_cartanInvolution_comm_quasiReflection _ (gramAt D V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
    (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ).ne_zero (tauE D τ ∘ x) (by
      have : star (tauE D τ ∘ x) ⬝ᵥ gramAt D V τ *ᵥ (tauE D τ ∘ x) = tauE D τ (star x ⬝ᵥ V.gram *ᵥ x) := by
        rw [e0, RingHom.map_dotProduct]
        congr 1
        funext i
        exact (RingHom.map_mulVec (tauE D τ) V.gram x i).symm
      rw [this]
      exact (map_ne_zero _).2 hx)
  refine ⟨s, h1, ?_⟩
  have e : (1 + c • Matrix.vecMulVec x (star x ᵥ* V.gram)).map (tauE D τ) =
      1 + tauE D τ c • Matrix.vecMulVec (tauE D τ ∘ x) (star (tauE D τ ∘ x) ᵥ* gramAt D V τ) := by
    rw [← RingHom.mapMatrix_apply, map_add, map_one, e0]
    congr 1
    ext i j
    show tauE D τ (c * (x i * (star x ᵥ* V.gram) j)) = _
    rw [map_mul, map_mul, RingHom.map_vecMul]
    rfl
  rw [e]
  exact h2 _

theorem of_oi_eq_subst (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hη : IsEtaTilde D η) (hf : IsFinWeil ψ S T ΛS ΛT (η ^ S.rank) (η ^ T.rank) of) (hi : IsInfWeil ψ θ S T oi)
    {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T) (f : WO S T → ℂ) (h : IsThetaFunO ψ S T f) :
    of (γ, γ') (oi (γ, γ') f) = fun w => f (actO S T γ⁻¹ γ'⁻¹ w) := by
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hs using hc
  have hone : ∀ (V : HSp D) τ, s V τ * (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D τ) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D τ) * s V τ := fun V τ => by
    rw [Matrix.map_one _ (tauE D τ).map_zero (tauE D τ).map_one, Matrix.mul_one, Matrix.one_mul]
  have hm := fun {p q : GA D S × GA D T} (h1 : IsScalar ψ of oi p 1) (h2 : IsScalar ψ of oi q 1) a b =>
    mul_one (1 : ℂ) ▸ h1.mul hψ hi (of_oi_comm hψ hS hT hη hf hi) h2 a b
  have r1 : IsRat T (1 : GA D T)⁻¹ 1 := by rw [inv_one]; exact isRat_one T
  have h1 : IsScalar ψ of oi (1, 1) 1 :=
    isScalar_one_of_comm hψ hθ hS hT hη hf hi (hs S) (hs T) (isRat_one S) r1 (hone S) (hone T)
  have hA : IsScalar ψ of oi (γ, 1) 1 := by
    refine rat_induction S (fun g => IsScalar ψ of oi (g, 1) 1) h1 (fun g _ g' hg' a b => ?_) (fun g x c hx hg => ?_) γ hγ
    · have := hm a b hg' (one_mem _)
      rwa [Prod.mk_mul_mk, mul_one] at this
    · choose s' a b using exists_cartan_refl S x c hx
      exact isScalar_one_of_comm hψ hθ hS hT hη hf hi a (hs T) hg r1 b (hone T)
  have hB : IsScalar ψ of oi (1, γ'⁻¹⁻¹) 1 := by
    refine rat_induction T (fun g => IsScalar ψ of oi (1, g⁻¹) 1) (by rw [inv_one]; exact h1)
      (fun g hg g' _ a b => ?_) (fun g x c hx hg => ?_) _ (inv_mem hγ')
    · have := hm b a (one_mem _) (inv_mem hg)
      rwa [Prod.mk_mul_mk, mul_one, ← _root_.mul_inv_rev] at this
    · choose s' a b using exists_cartan_refl T x c hx
      exact isScalar_one_of_comm hψ hθ hS hT hη hf hi (hs S) a (isRat_one S) (by rwa [inv_inv]) (hone S) b
  rw [inv_inv] at hB
  have := hm hA hB (one_mem _) hγ' f h
  rwa [Prod.mk_mul_mk, mul_one, one_mul, one_smul] at this

theorem of_oi_apply_zero (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hη : IsEtaTilde D η) (hf : IsFinWeil ψ S T ΛS ΛT (η ^ S.rank) (η ^ T.rank) of) (hi : IsInfWeil ψ θ S T oi)
    {γ : GA D S} (hγ : γ ∈ GQ S) {γ' : GA D T} (hγ' : γ' ∈ GQ T) (f : WO S T → ℂ) (h : IsThetaFunO ψ S T f) :
    of (γ, γ') (oi (γ, γ') f) 0 = f 0 := by
  rw [of_oi_eq_subst hψ hθ hS hT hη hf hi hγ hγ' f h]
  show f (actO S T γ⁻¹ γ'⁻¹ 0) = f 0
  rw [actO, Matrix.mul_zero, Matrix.zero_mul]

end Final

theorem automorphy_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ η, IsEtaTilde D η → ∀ (of oi : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsFinWeil ψ S T ΛS ΛT (η ^ S.rank) (η ^ T.rank) of → IsInfWeil ψ θ S T oi → ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → of (1, γ') (oi (1, γ') f) 0 = f 0 :=
  fun _ _ hψ _ _ _ hθ _ _ hS hT _ hη _ _ hf hi _ hγ' f h =>
    of_oi_apply_zero hψ hθ hS hT hη hf hi (one_mem _) hγ' f h

end GlobalTheory.RatAut

end
