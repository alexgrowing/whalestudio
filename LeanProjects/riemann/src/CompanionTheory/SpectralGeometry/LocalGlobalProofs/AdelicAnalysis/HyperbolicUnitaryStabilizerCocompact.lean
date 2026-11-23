import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicPrimitiveVectorCompactRescaleStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramOrbitCompactRepresentativeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicAndBlockOneNondegenerateStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Iwa

section Alg

variable {K : Type} [CommRing K] {N : ℕ}

theorem hform_eq (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (x y : Fin N → K) :
    hform s L x y = (fun i => s (x i)) ⬝ᵥ (L *ᵥ y) := by
  simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_sub_right (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (x y w : Fin N → K) :
    hform s L x (y - w) = hform s L x y - hform s L x w := by
  simp [hform_eq, Matrix.mulVec_sub, dotProduct_sub]

theorem hform_smul_right (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (c : K) (x y : Fin N → K) :
    hform s L x (c • y) = c * hform s L x y := by
  simp [hform_eq, Matrix.mulVec_smul, dotProduct_smul]

theorem hform_sub_left (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (x w y : Fin N → K) :
    hform s L (x - w) y = hform s L x y - hform s L w y := by
  simp only [hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_smul_left (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (c : K) (x y : Fin N → K) :
    hform s L (c • x) y = s c * hform s L x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_conj (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (hs : ∀ x, s (s x) = x)
    (hL : ∀ i j, s (L j i) = L i j) (x y : Fin N → K) :
    s (hform s L x y) = hform s L y x := by
  simp only [hform, map_sum, map_mul, hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hL]; ring

def dualV (s : K →+* K) (Li : Matrix (Fin N) (Fin N) K) (z : Fin N → K) : Fin N → K :=
  fun i => s ((z ᵥ* Li) i)

theorem hform_dual (s : K →+* K) (L Li : Matrix (Fin N) (Fin N) K) (hs : ∀ x, s (s x) = x)
    (hLi : Li * L = 1) (z w : Fin N → K) : hform s L (dualV s Li z) w = z ⬝ᵥ w := by
  have h : hform s L (dualV s Li z) w = (z ᵥ* Li) ⬝ᵥ (L *ᵥ w) := by
    simp only [hform_eq, dualV, hs]
  rw [h, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hLi, Matrix.vecMul_one]

def partner (s : K →+* K) (L Li : Matrix (Fin N) (Fin N) K) (half : K) (z w : Fin N → K) : Fin N → K :=
  dualV s Li z - (half * hform s L (dualV s Li z) (dualV s Li z)) • w

theorem partner_spec (s : K →+* K) (L Li : Matrix (Fin N) (Fin N) K) (half : K)
    (hs : ∀ x, s (s x) = x) (hL : ∀ i j, s (L j i) = L i j) (hLi : Li * L = 1)
    (hh : s half = half) (h2 : 2 * half = 1) (z w : Fin N → K) (hw : hform s L w w = 0)
    (hz : z ⬝ᵥ w = 1) :
    hform s L w (partner s L Li half z w) = 1 ∧ hform s L (partner s L Li half z w) w = 1 ∧
      hform s L (partner s L Li half z w) (partner s L Li half z w) = 0 := by
  set u := dualV s Li z with hu
  set A := hform s L u u with hA
  have huw : hform s L u w = 1 := by rw [hu, hform_dual s L Li hs hLi, hz]
  have hwu : hform s L w u = 1 := by rw [← hform_conj s L hs hL u w, huw, map_one]
  have hsA : s A = A := hform_conj s L hs hL u u
  have hc : s (half * A) = half * A := by rw [map_mul, hh, hsA]
  have hp : partner s L Li half z w = u - (half * A) • w := rfl
  have e1 : hform s L w (u - (half * A) • w) = 1 := by
    rw [hform_sub_right, hform_smul_right, hwu, hw]; ring
  have e2 : hform s L (u - (half * A) • w) w = 1 := by
    rw [hform_sub_left, hform_smul_left, huw, hw]; ring
  have e3 : hform s L u (u - (half * A) • w) = A - half * A := by
    rw [hform_sub_right, hform_smul_right, huw, ← hA]; ring
  rw [hp]
  refine ⟨e1, e2, ?_⟩
  rw [hform_sub_left, hform_smul_left, e1, e3, hc]
  linear_combination (-A) * h2

theorem hform_single (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    hform s L (Pi.single i 1) (Pi.single j 1) = L i j := by
  simp [hform_eq, Matrix.mulVec_single_one, dotProduct, Pi.single_apply, apply_ite s]

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem continuous_hform (s : K →+* K) (hs : Continuous s) (L : Matrix (Fin N) (Fin N) K) :
    Continuous fun p : (Fin N → K) × (Fin N → K) => hform s L p.1 p.2 := by
  unfold hform
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  have h1 : Continuous fun p : (Fin N → K) × (Fin N → K) => p.1 i :=
    (continuous_apply i).comp continuous_fst
  have h2 : Continuous fun p : (Fin N → K) × (Fin N → K) => p.2 j :=
    (continuous_apply j).comp continuous_snd
  exact ((hs.comp h1).mul continuous_const).mul h2

theorem continuous_dualV (s : K →+* K) (hs : Continuous s) (Li : Matrix (Fin N) (Fin N) K) :
    Continuous (dualV s Li) := by
  refine continuous_pi fun i => hs.comp ?_
  exact (continuous_apply i).comp (continuous_id.matrix_vecMul continuous_const)

theorem continuous_partner (s : K →+* K) (hs : Continuous s) (L Li : Matrix (Fin N) (Fin N) K)
    (half : K) : Continuous fun p : (Fin N → K) × (Fin N → K) => partner s L Li half p.1 p.2 := by
  have hd : Continuous fun p : (Fin N → K) × (Fin N → K) => dualV s Li p.1 :=
    (continuous_dualV s hs Li).comp continuous_fst
  have hf : Continuous fun p : (Fin N → K) × (Fin N → K) =>
      hform s L (dualV s Li p.1) (dualV s Li p.1) :=
    (continuous_hform s hs L).comp (hd.prodMk hd)
  unfold partner
  exact hd.sub ((continuous_const.mul hf).smul continuous_snd)

end Alg

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_invol (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (a : R ⊗[F] E) : sigR R σ (sigR R σ a) = a := by
  induction a with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add x y hx hy => simp [map_add, hx, hy]

theorem sigR_incl (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (e : E) :
    sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem gramR_ratTup (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {N n : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (X : Fin n → Fin N → E) :
    gramR R σ J (ratTup R X) = (gramE σ J X).map (inclR R) := by
  ext a b
  simp only [gramR, hR, hform, ratTup, JR, sigR_incl, Matrix.map_apply, gramE, hE, map_sum, map_mul]
  rfl

theorem actW_smul (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {N n : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (g : HA R σ J) (a : R ⊗[F] E) (X : Fin n → Fin N → R ⊗[F] E) :
    actW R σ J g (a • X) = a • actW R σ J g X := by
  funext i
  simp [actW, actTup, Matrix.mulVec_smul]

end Tens

def frame (E : Type) [Field E] (M : ℕ) : Fin 2 → Fin (M + 2) → E :=
  ![Pi.single 0 1, Pi.single (Fin.succ 0) 1]

theorem gram_frame {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) :
    gramE σ (hypJ J) (frame E M) = !![0, 1; 1, 0] := by
  have h : ∀ i j : Fin (M + 2), hE σ (hypJ J) (Pi.single i 1) (Pi.single j 1) = hypJ J i j :=
    fun i j => hform_single (σ : E →+* E) (hypJ J) i j
  ext a b
  fin_cases a <;> fin_cases b
  · exact (h 0 0).trans (by simp [hypJ])
  · exact (h 0 (Fin.succ 0)).trans (by simp [hypJ])
  · exact (h (Fin.succ 0) 0).trans (by simp [hypJ])
  · exact (h (Fin.succ 0) (Fin.succ 0)).trans (by simp [hypJ])

theorem eOne_eq_frame {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (M : ℕ) (a : Fin 1) :
    eOne (R ⊗[F] E) (M + 1) a = ratTup R (frame E M) 0 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [eOne, ratTup, frame]
  · simp [eOne, ratTup, frame, Pi.single_apply, Fin.succ_ne_zero]

section Core

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {N : ℕ}

theorem continuous_pair (s : K →+* K) (hs : Continuous s) (L Li : Matrix (Fin N) (Fin N) K) (half : K) :
    Continuous fun p : (Fin 1 → Fin N → K) × (Fin 1 → Fin N → K) =>
      (![p.1 0, partner s L Li half (p.2 0) (p.1 0)] : Fin 2 → Fin N → K) := by
  have c1 : Continuous fun p : (Fin 1 → Fin N → K) × (Fin 1 → Fin N → K) => p.1 0 :=
    (continuous_apply 0).comp continuous_fst
  have c2 : Continuous fun p : (Fin 1 → Fin N → K) × (Fin 1 → Fin N → K) => p.2 0 :=
    (continuous_apply 0).comp continuous_snd
  have c3 := (continuous_partner s hs L Li half).comp (c2.prodMk c1)
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact c1
  · exact c3

theorem gram_pair (s : K →+* K) (L : Matrix (Fin N) (Fin N) K) (w p : Fin N → K)
    (h00 : hform s L w w = 0) (h01 : hform s L w p = 1) (h10 : hform s L p w = 1)
    (h11 : hform s L p p = 0) (a b : Fin 2) :
    hform s L ((![w, p] : Fin 2 → Fin N → K) a) ((![w, p] : Fin 2 → Fin N → K) b) =
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) a b := by
  fin_cases a <;> fin_cases b
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem iwa_core {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (s : K →+* K) (hsc : Continuous s) (hs : ∀ x, s (s x) = x) (L Li : Matrix (Fin N) (Fin N) K)
    (hL : ∀ i j, s (L j i) = L i j) (hLi : Li * L = 1) (half : K) (hh : s half = half)
    (h2 : 2 * half = 1) (act : H → (Fin N → K) → Fin N → K)
    (hmul : ∀ g k v, act (g * k) v = act g (act k v)) (hone : ∀ v, act 1 v = v)
    (hsmul : ∀ g (a : K) v, act g (a • v) = a • act g v)
    (hpres : ∀ g x y, hform s L (act g x) (act g y) = hform s L x y)
    (X : Fin 2 → Fin N → K) (hX : ∀ a b, hform s L (X a) (X b) = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) a b)
    (Ω : Set (Fin 1 → Fin N → K)) (hΩ : IsCompact Ω)
    (hprim : ∀ y : Fin 1 → Fin N → K, (∃ z : Fin N → K, z ⬝ᵥ y 0 = 1) →
      ∃ (a : Kˣ) (z : Fin 1 → Fin N → K), (a : K) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : K) • y) 0 = 1)
    (hproper : ∀ Ω₂ : Set (Fin 2 → Fin N → K), IsCompact Ω₂ → ∃ C : Set H, IsCompact C ∧ ∀ Y ∈ Ω₂,
      (∀ a b, hform s L (Y a) (Y b) = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) a b) →
        ∃ c ∈ C, ∀ i, act c (X i) = Y i) :
    ∃ C : Set H, IsCompact C ∧ ∀ h : H, ∃ c ∈ C, ∃ a : Kˣ, act (h * c⁻¹) (X 0) = (a : K) • X 0 := by
  obtain ⟨C₀, hC₀, hprop⟩ := hproper _ ((hΩ.prod hΩ).image (continuous_pair s hsc L Li half))
  refine ⟨Inv.inv '' C₀, hC₀.image continuous_inv, fun h => ?_⟩
  have hG00 : hform s L (act h⁻¹ (X 0)) (act h⁻¹ (X 0)) = 0 := by
    rw [hpres, hX]; rfl
  have hG10 : hform s L (act h⁻¹ (X 1)) (act h⁻¹ (X 0)) = 1 := by
    rw [hpres, hX]; rfl
  have hunim : ∃ z : Fin N → K, z ⬝ᵥ (fun _ : Fin 1 => act h⁻¹ (X 0)) 0 = 1 := by
    refine ⟨(fun i => s (act h⁻¹ (X 1) i)) ᵥ* L, ?_⟩
    rw [← Matrix.dotProduct_mulVec, ← hform_eq]
    exact hG10
  obtain ⟨a, z, hay, hz, hza⟩ := hprim (fun _ => act h⁻¹ (X 0)) hunim
  have hww : hform s L ((a : K) • act h⁻¹ (X 0)) ((a : K) • act h⁻¹ (X 0)) = 0 := by
    rw [hform_smul_left, hform_smul_right, hG00, mul_zero, mul_zero]
  have hza' : z 0 ⬝ᵥ ((a : K) • act h⁻¹ (X 0)) = 1 := hza
  obtain ⟨p1, p2, p3⟩ := partner_spec s L Li half hs hL hLi hh h2 (z 0) ((a : K) • act h⁻¹ (X 0)) hww hza'
  have hmem : (![((a : K) • act h⁻¹ (X 0)), partner s L Li half (z 0) ((a : K) • act h⁻¹ (X 0))] : Fin 2 → Fin N → K)
      ∈ (fun p : (Fin 1 → Fin N → K) × (Fin 1 → Fin N → K) =>
      (![p.1 0, partner s L Li half (p.2 0) (p.1 0)] : Fin 2 → Fin N → K)) '' (Ω ×ˢ Ω) :=
    ⟨((a : K) • (fun _ => act h⁻¹ (X 0)), z), ⟨hay, hz⟩, rfl⟩
  obtain ⟨c, hc, hcY⟩ := hprop _ hmem (gram_pair s L _ _ hww p1 p2 p3)
  refine ⟨c⁻¹, ⟨c, hc, rfl⟩, a, ?_⟩
  have h0 : act c (X 0) = (a : K) • act h⁻¹ (X 0) := hcY 0
  rw [inv_inv, hmul, h0, hsmul, ← hmul, mul_inv_cancel, hone]

end Core

def actV {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (g : HA R σ J) (v : Fin N → R ⊗[F] E) :
    Fin N → R ⊗[F] E :=
  (HA.mat R σ J g : Matrix (Fin N) (Fin N) (R ⊗[F] E)).mulVec v

theorem map_hyp {E K : Type} [Field E] [CommRing K] (φ : E →+* K) :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E).map φ = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ C : Set (HA (AF F) σ (hypJ J)), IsCompact C ∧ ∀ h : HA (AF F) σ (hypJ J), ∃ c ∈ C, ∃ a : (AF F ⊗[F] E)ˣ, actW (AF F) σ _ (h * c⁻¹) (eOne _ (M + 1)) = (a : AF F ⊗[F] E) • eOne _ (M + 1) := by
  intro F E _ _ _ _ _ σ hCM M J hJ
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have hJ' : IsHermND σ (hypJ J) := (GlobalTheory.T.hyperbolic_and_block_one_nondegenerate F E σ hCM M J hJ).1
  obtain ⟨⟨lc, sc, t2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := lc
  haveI := sc
  haveI := t2
  obtain ⟨hTG, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 2) (hypJ J) hJ' (AF F)
  obtain ⟨hTR, -, -, -, hsc, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := hTG
  haveI := hTR
  obtain ⟨Ω, hΩ, hprim⟩ := GlobalTheory.T.adelic_primitive_vector_compact_rescale F E σ hCM (M + 2)
  have hLh : ∀ i j, sigR (AF F) σ (JR (F := F) (AF F) (hypJ J) j i) = JR (F := F) (AF F) (hypJ J) i j := by
    intro i j
    simp only [JR, Matrix.map_apply, sigR_incl, hJ'.1 i j]
  have hLi : ((hypJ J)⁻¹).map (inclR (F := F) (AF F)) * JR (F := F) (AF F) (hypJ J) = 1 := by
    have hu : IsUnit (hypJ J).det := isUnit_iff_ne_zero.mpr hJ'.2
    have h1 : ((hypJ J)⁻¹ * hypJ J).map (inclR (F := F) (AF F)) = 1 := by
      rw [Matrix.nonsing_inv_mul _ hu]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [← h1, Matrix.map_mul]
    rfl
  have hh : sigR (AF F) σ (inclR (F := F) (AF F) (1 / 2 : E)) = inclR (F := F) (AF F) (1 / 2 : E) := by
    have e : σ (1 / 2 : E) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
    rw [sigR_incl, e]
  have h2 : 2 * inclR (F := F) (AF F) (1 / 2 : E) = 1 := by
    have h3 : inclR (F := F) (AF F) (2 * (1 / 2 : E)) = 1 := by
      rw [mul_one_div_cancel two_ne_zero, map_one]
    rw [map_mul, map_ofNat] at h3
    exact h3
  have hdet : (gramE σ (hypJ J) (frame E M)).det ≠ 0 := by
    rw [gram_frame, Matrix.det_fin_two_of]
    simp
  have hmapG : (gramE σ (hypJ J) (frame E M)).map (inclR (F := F) (AF F)) = !![0, 1; 1, 0] := by
    rw [gram_frame, map_hyp]
  have hX : ∀ a b, hform (sigR (AF F) σ) (JR (F := F) (AF F) (hypJ J)) (ratTup (AF F) (frame E M) a)
      (ratTup (AF F) (frame E M) b) = (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E)) a b := by
    intro a b
    rw [← hmapG, ← gramR_ratTup]
    rfl
  obtain ⟨C, hC, hCh⟩ := iwa_core (H := HA (AF F) σ (hypJ J)) (sigR (AF F) σ) hsc
    (sigR_invol (AF F) σ hσ) (JR (F := F) (AF F) (hypJ J)) _ hLh hLi _ hh h2
    (actV (AF F) σ (hypJ J))
    (fun g k v => congrFun ((hact 1).2.2.1 g k (fun _ => v)) 0)
    (fun v => congrFun ((hact 1).2.1 (fun _ => v)) 0)
    (fun g a v => Matrix.mulVec_smul _ a v)
    (fun g x y => congrFun (congrFun ((hact 2).2.2.2 g ![x, y]) 0) 1)
    (ratTup (AF F) (frame E M)) hX Ω hΩ hprim
    (fun Ω₂ hΩ₂ => by
      obtain ⟨C, hC, hp⟩ := GlobalTheory.T.gram_orbit_compact_representative F E σ hCM (M + 2) (hypJ J) hJ' 2 (frame E M) hdet Ω₂ hΩ₂
      refine ⟨C, hC, fun Y hY hg => ?_⟩
      obtain ⟨c, hc, hcY⟩ := hp Y hY (by
        rw [hmapG]
        funext a b
        exact hg a b)
      exact ⟨c, hc, fun i => congrFun hcY i⟩)
  refine ⟨C, hC, fun h => ?_⟩
  obtain ⟨c, hc, a, hca⟩ := hCh h
  refine ⟨c, hc, a, funext fun i => ?_⟩
  have e1 := eOne_eq_frame (F := F) (E := E) (AF F) M i
  show actV (AF F) σ (hypJ J) (h * c⁻¹) (eOne _ (M + 1) i) = (a : AF F ⊗[F] E) • eOne _ (M + 1) i
  rw [e1]
  exact hca

end GlobalTheory.CompanionTheory.SW.Iwa
