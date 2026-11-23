import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMatInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceFormLinearIsometryEqMulNormOneTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitsOfIsCompactClosureZpowersMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersMulIntegralUnitStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat

theorem twCent_iff_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (β : B.A), IsUnit (GlobalTheory.TwLat.gram e b β) → ∀ g : GLw m w, g ∈ twCent (thL m w) (GlobalTheory.TwLat.dlt e b β) ↔ g.valᵀ * GlobalTheory.TwLat.gram e b β * g.val.map (cj w) = GlobalTheory.TwLat.gram e b β := by
  intro E _ _ _ w hw K e B m b β hG g
  have hth : thL m w = thetaGL m (cj w) := by rw [thL, if_neg hw]
  have hd : dlt e b β = invT m _ hG.unit * (PhiU m _)⁻¹ := by rw [dlt, dif_pos hG]
  rw [hth, hd]
  change g * _ = _ * _ ↔ _
  rw [Units.ext_iff]
  set G := gram e b β with hGdef
  set Φ := GlobalTheory.Tw.Phi m (w.adicCompletion E) with hΦdef
  have hΦ' : Φᵀ * Φ = 1 := mul_eq_one_comm.1 (Phi_mul_transpose m _)
  set Gi := (hG.unit⁻¹).val with hGidef
  have hGi1 : G * Gi = 1 := hG.unit.mul_inv
  have hGi2 : Gi * G = 1 := hG.unit.inv_mul
  set H := g.val.map (cj w) with hHdef
  set Hi := (g⁻¹ : GLw m w).val.map (cj w) with hHidef
  have hH : H * Hi = 1 := by
    rw [hHdef, hHidef, show g.val.map (cj w) = (cj w).mapMatrix g.val from rfl,
      show (g⁻¹ : GLw m w).val.map (cj w) = (cj w).mapMatrix (g⁻¹ : GLw m w).val from rfl, ← map_mul, Units.mul_inv,
      map_one]
  have hL : (g * (invT m _ hG.unit * (PhiU m _)⁻¹)).val = g.val * (Giᵀ * Φᵀ) := rfl
  have hR : (invT m _ hG.unit * (PhiU m _)⁻¹ * thetaGL m (cj w) g).val = Giᵀ * Φᵀ * (Φ * Hiᵀ * Φᵀ) := rfl
  rw [hL, hR]
  have hA : Giᵀ * Φᵀ * (Φ * Hiᵀ * Φᵀ) = Giᵀ * Hiᵀ * Φᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Φᵀ Φ, hΦ', Matrix.one_mul]
  rw [hA]
  have hB : g.val * (Giᵀ * Φᵀ) = Giᵀ * Hiᵀ * Φᵀ ↔ g.val * Giᵀ = Giᵀ * Hiᵀ := by
    constructor
    · intro h
      have := congrArg (· * Φ) h
      simp only [Matrix.mul_assoc, hΦ', Matrix.mul_one] at this
      simpa only [Matrix.mul_assoc] using this
    · intro h
      rw [← Matrix.mul_assoc, h]
  rw [hB]
  have hC : g.val * Giᵀ = Giᵀ * Hiᵀ ↔ Gi * g.valᵀ = Hi * Gi := by
    rw [← Matrix.transpose_inj]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hC]
  constructor
  · intro h
    calc g.valᵀ * G * H = (G * Gi) * g.valᵀ * G * H := by rw [hGi1, Matrix.one_mul]
      _ = G * (Gi * g.valᵀ) * G * H := by simp only [Matrix.mul_assoc]
      _ = G * Hi * (Gi * G) * H := by rw [h]; simp only [Matrix.mul_assoc]
      _ = G * (Hi * H) := by rw [hGi2, Matrix.mul_one, Matrix.mul_assoc]
      _ = G := by rw [mul_eq_one_comm.1 hH, Matrix.mul_one]
  · intro h
    calc Gi * g.valᵀ = Gi * g.valᵀ * ((G * H) * Hi * Gi) := by
          rw [Matrix.mul_assoc G, hH, Matrix.mul_one, hGi1, Matrix.mul_one]
      _ = Gi * (g.valᵀ * G * H) * Hi * Gi := by simp only [Matrix.mul_assoc]
      _ = Hi * Gi := by rw [h, hGi2, Matrix.one_mul]

theorem herm_finsum_left {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (β : B.A) {ι : Type} (s : Finset ι)
    (v : ι → K.E) (x : ι → B.A) (z : B.A) :
    B.herm β (∑ i ∈ s, v i • x i) z = ∑ i ∈ s, v i * B.herm β (x i) z := by
  simp only [GlobalTheory.UnitLemma.InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc,
    map_smul, smul_eq_mul]

theorem herm_finsum_right {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (β y : B.A) {ι : Type} (s : Finset ι)
    (r : ι → K.E) (x : ι → B.A) :
    B.herm β y (∑ i ∈ s, r i • x i) = ∑ i ∈ s, K.c (r i) * B.herm β y (x i) := by
  simp only [GlobalTheory.UnitLemma.InvAlg.herm, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, RingEquiv.map_mul B.σ, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul]

theorem gram_isometry_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (β : B.A) (f : B.A →ₗ[K.E] B.A), ((LinearMap.toMatrix b b f).map e)ᵀ * GlobalTheory.TwLat.gram e b β * ((LinearMap.toMatrix b b f).map e).map (cj w) = GlobalTheory.TwLat.gram e b β ↔ ∀ y z, B.herm β (f y) (f z) = B.herm β y z := by
  intro E _ _ _ w K e hec B m b β f
  set M := LinearMap.toMatrix b b f with hM
  have hf : ∀ i, f (b i) = ∑ k, M k i • b k := by
    intro i
    simp only [hM, LinearMap.toMatrix_apply]
    exact (b.sum_repr (f (b i))).symm
  have hent : ∀ i j, ((M.map e)ᵀ * gram e b β * (M.map e).map (cj w)) i j = e (B.herm β (f (b i)) (f (b j))) := by
    intro i j
    rw [hf i, hf j, herm_finsum_left]
    simp only [herm_finsum_right, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, gram, Matrix.of_apply,
      Finset.mul_sum, Finset.sum_mul, map_sum, map_mul, hec]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  constructor
  · intro h y z
    have hij : ∀ i j, B.herm β (f (b i)) (f (b j)) = B.herm β (b i) (b j) := by
      intro i j
      apply e.injective
      rw [← hent, h]
      rfl
    rw [← b.sum_repr y, ← b.sum_repr z]
    simp only [map_sum, map_smul, herm_finsum_left, herm_finsum_right, hij]
  · intro h
    ext i j
    rw [hent, h]
    rfl

theorem twCent_equiv_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u β : B.A, IsUnit β → B.σ β = β * ((-1) ^ (m - 1) * u) → Algebra.adjoin K.E {u} = ⊤ → IsUnit (GlobalTheory.TwLat.gram e b β) → ∃ φ : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β) ≃* B.T, (∀ t : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β), (t : GLw m w).val = GlobalTheory.TwLat.mulMat e b (((φ t : B.T) : B.Aˣ) : B.A)) ∧ ∀ t : twCent (thL m w) (GlobalTheory.TwLat.dlt e b β), ((t : GLw m w) ∈ cptPart (twCent (thL m w) (GlobalTheory.TwLat.dlt e b β)) ↔ ((φ t : B.T) : B.Aˣ) ∈ GlobalTheory.UnitLemma.intUnits K.O B.A) := by
  intro E _ _ _ hE w hw K e hec hint hval B m b u β hβu hβ hadj hG

  have hnd : ∀ y, (∀ z, B.herm β y z = 0) → y = 0 := by
    intro y hy
    have hsum : ∀ z, B.herm β y z = ∑ i, b.repr y i * B.herm β (b i) z := by
      intro z
      conv_lhs => rw [← b.sum_repr y]
      simp only [GlobalTheory.UnitLemma.InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm,
        smul_mul_assoc, map_smul, smul_eq_mul]
    have h1 : Matrix.vecMul (fun i => e (b.repr y i)) (gram e b β) = 0 := by
      funext j
      have := congrArg e (hsum (b j))
      rw [hy, map_zero, map_sum] at this
      simp only [Matrix.vecMul, dotProduct, gram, Matrix.of_apply, Pi.zero_apply]
      rw [this]
      simp only [map_mul]
    have hGi : gram e b β * (gram e b β)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hG)
    have h2 : (fun i => e (b.repr y i)) = 0 := by
      rw [← Matrix.vecMul_one (fun i => e (b.repr y i)), ← hGi, ← Matrix.vecMul_vecMul, h1, Matrix.zero_vecMul]
    have h3 : b.repr y = 0 := by
      ext i
      have := congrFun h2 i
      simpa using this
    simpa using h3

  have hT : ∀ t : B.Aˣ, t ∈ B.T → mulU e b t ∈ twCent (thL m w) (dlt e b β) := by
    intro t ht
    have ht' : (t : B.A) * B.σ (t : B.A) = 1 := ht
    rw [twCent_iff_gram E w hw K e B m b β hG]
    refine (gram_isometry_iff E w K e hec B m b β (LinearMap.mulLeft K.E (t : B.A))).2 fun y z => ?_
    simp only [LinearMap.mulLeft_apply, GlobalTheory.UnitLemma.InvAlg.herm]
    rw [map_mul B.σ, show β * ((t : B.A) * y) * (B.σ t * B.σ z) = β * y * B.σ z * ((t : B.A) * B.σ t) by ring,
      ht', mul_one]

  have hsurj : ∀ g : GLw m w, g ∈ twCent (thL m w) (dlt e b β) → ∃ t : B.Aˣ, t ∈ B.T ∧ mulU e b t = g := by
    intro g hg
    have hg1 := (twCent_iff_gram E w hw K e B m b β hG g).1 hg
    let em := (e.symm : w.adicCompletion E →+* K.E).mapMatrix (m := Fin m)
    let f : B.A →ₗ[K.E] B.A := Matrix.toLin b b (em g.val)
    have hfM : (LinearMap.toMatrix b b f).map e = g.val := by
      simp only [f, LinearMap.toMatrix_toLin, em, RingHom.mapMatrix_apply, Matrix.map_map]
      ext i j; simp
    have hiso := (gram_isometry_iff E w K e hec B m b β f).1 (by rw [hfM]; exact hg1)
    have hfs : Function.Surjective f := by
      intro y
      refine ⟨Matrix.toLin b b (em (g⁻¹ : GLw m w).val) y, ?_⟩
      rw [← LinearMap.comp_apply, ← Matrix.toLin_mul, ← map_mul, Units.mul_inv, map_one, Matrix.toLin_one,
        LinearMap.id_apply]
    obtain ⟨a, haT, hfa⟩ := GlobalTheory.T.traceForm_linearIsometry_eq_mul_normOneTorus K B (m - 1) u β hβ hadj hnd f hfs hiso
    refine ⟨a, haT, Units.ext ?_⟩
    rw [mulU_val, ← hfM]
    have : LinearMap.mulLeft K.E (a : B.A) = f := LinearMap.ext fun y => (hfa y).symm
    rw [mulMat, this]
  let ψ : B.T →* twCent (thL m w) (dlt e b β) :=
    { toFun := fun t => ⟨mulU e b t, hT t t.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun s t => Subtype.ext (by simp) }
  have hψ : Function.Bijective ψ := by
    refine ⟨fun s t h => Subtype.ext (mulU_injective e b (congrArg Subtype.val h)), ?_⟩
    rintro ⟨g, hg⟩
    obtain ⟨t, ht, rfl⟩ := hsurj g hg
    exact ⟨⟨t, ht⟩, rfl⟩
  let φ := (MulEquiv.ofBijective ψ hψ).symm
  have hφ : ∀ t : twCent (thL m w) (dlt e b β), (t : GLw m w) = mulU e b ((φ t : B.T) : B.Aˣ) := by
    intro t
    have := congrArg Subtype.val ((MulEquiv.ofBijective ψ hψ).apply_symm_apply t)
    exact this.symm
  refine ⟨φ, fun t => by rw [hφ t, mulU_val], fun t => ?_⟩

  have hset : {t | t ∈ twCent (thL m w) (dlt e b β) ∧
      IsCompact (closure (Subgroup.zpowers t : Set (GLw m w)))} =
      (((GlobalTheory.UnitLemma.intUnits K.O B.A) ⊓ B.T).map (mulU e b) : Set (GLw m w)) := by
    ext g
    constructor
    · rintro ⟨hg, hc⟩
      obtain ⟨a, haT, rfl⟩ := hsurj g hg
      exact ⟨a, ⟨GlobalTheory.T.integralUnits_of_isCompact_closure_zpowers_mul E hE w hw K e hec hint hval B m b a hc, haT⟩, rfl⟩
    · rintro ⟨a, ⟨hai, haT⟩, rfl⟩
      exact ⟨hT a haT, GlobalTheory.T.isCompact_closure_zpowers_mul_integralUnit E hE w hw K e hec hint hval B m b a hai⟩
  rw [cptPart, hset, Subgroup.closure_eq, hφ t]
  constructor
  · rintro ⟨a, ⟨hai, -⟩, ha⟩
    rwa [← mulU_injective e b ha]
  · intro h
    exact ⟨_, ⟨h, (φ t).2⟩, rfl⟩

end GlobalTheory.TwLat
