import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNormOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneOfCompleteTwoNeZero

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm Topology
open scoped TensorProduct

namespace GlobalTheory.PlaneNormApprox

variable {F E : Type} [Field F] [Field E] [Algebra F E]

section Alg

variable (K : Type) [Field K] [Algebra F K]

theorem sigR_inclR' (σ : E →ₐ[F] E) (e : E) : sigR K σ (inclR (F := F) K e) = inclR K (σ e) := by
  simp [sigR, inclR]

theorem sigR_algebraMap' (σ : E →ₐ[F] E) (k : K) :
    sigR K σ (algebraMap K (K ⊗[F] E) k) = algebraMap K (K ⊗[F] E) k := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem hR_incl (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hR K σ J (fun i => inclR K (x i)) (fun i => inclR K (y i)) = inclR K (hE σ J x y) := by
  simp [hR, hE, Formalism.UG.hform, JR, map_sum, map_mul, sigR_inclR']

theorem hermitianGramDetTwoVectorsTensor_incl (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    gram2R K σ J (fun i => inclR K (x i)) (fun i => inclR K (y i)) = inclR K (gram2E σ J x y) := by
  simp only [gram2R, gram2E, hR_incl, map_sub, map_mul]

theorem sigR_sigR {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) (u : K ⊗[F] E) : sigR K σ (sigR K σ u) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul k e => simp [sigR, hσ]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem sigR_hR {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin M → K ⊗[F] E) :
    sigR K σ (hR K σ J a b) = hR K σ J b a := by
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_sigR K hσ, JR, Matrix.map_apply, sigR_inclR', hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sigR_gram2R {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin M → K ⊗[F] E) :
    sigR K σ (gram2R K σ J a b) = gram2R K σ J a b := by
  simp only [gram2R, map_sub, map_mul, sigR_hR K hσ hJ]
  ring

theorem exists_lam [NumberField F] [NumberField E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ lam : K ⊗[F] E →ₗ[K] K, ∀ u, u + sigR K σ u = algebraMap K (K ⊗[F] E) (lam u) := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.2 (algebraMap F E).injective)
  let φ' : E →ₗ[F] F := φ ∘ₗ (LinearMap.id + σ.toLinearMap)
  have hφ' : ∀ e, algebraMap F E (φ' e) = e + σ e := by
    intro e
    obtain ⟨f, hf⟩ := GlobalTheory.HermLineZeros.exists_of_fixed h (e + σ e)
      (by rw [map_add, GlobalTheory.HermLineZeros.conj_invol h, add_comm])
    have h1 : φ' e = φ (e + σ e) := rfl
    rw [h1, ← hf]
    have := LinearMap.congr_fun hφ f
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, LinearMap.id_apply] at this
    rw [this]
  refine ⟨(TensorProduct.AlgebraTensorModule.rid F K K).toLinearMap ∘ₗ φ'.baseChange K, fun u => ?_⟩
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul k e =>
    have h2 : sigR K σ (k ⊗ₜ[F] e) = k ⊗ₜ[F] σ e := rfl
    rw [h2, ← TensorProduct.tmul_add, ← hφ', Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
    simp [Algebra.TensorProduct.algebraMap_apply]
  | add a b ha hb => rw [map_add, map_add, map_add, ← ha, ← hb]; abel

theorem two_ne_zero' (F₀ K₀ : Type) [Field F₀] [CharZero F₀] [Field K₀] [Algebra F₀ K₀] : (2 : K₀) ≠ 0 := by
  have : (2 : K₀) = algebraMap F₀ K₀ 2 := (map_ofNat (algebraMap F₀ K₀) 2).symm
  rw [this]
  exact (map_ne_zero _).2 two_ne_zero

end Alg

section Top

variable [NumberField F] [NumberField E] (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K]

def sigRK (σ : E →ₐ[F] E) : K ⊗[F] E →ₗ[K] K ⊗[F] E where
  toFun := sigR K σ
  map_add' := map_add _
  map_smul' k u := by
    rw [Algebra.smul_def, map_mul, sigR_algebraMap', RingHom.id_apply, Algebra.smul_def]

variable [IsModuleTopology K (K ⊗[F] E)] [IsTopologicalRing (K ⊗[F] E)]

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR K σ) :=
  IsModuleTopology.continuous_of_linearMap (sigRK K σ)

theorem continuous_hR {X : Type} [TopologicalSpace X] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    {f g : X → Fin M → K ⊗[F] E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t => hR K σ J (f t) (g t) := by
  unfold hR Formalism.UG.hform
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (((continuous_sigR K σ).comp ((continuous_apply i).comp hf)).mul continuous_const).mul
    ((continuous_apply j).comp hg)

theorem continuous_gram2R {X : Type} [TopologicalSpace X] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    {f g : X → Fin M → K ⊗[F] E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t => gram2R K σ J (f t) (g t) := by
  unfold gram2R
  exact ((continuous_hR K σ J hf hf).mul (continuous_hR K σ J hg hg)).sub
    ((continuous_hR K σ J hf hg).mul (continuous_hR K σ J hg hf))

theorem isUnitNorm_nhds {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {a₀ : K ⊗[F] E} (ha : IsUnitNorm K σ a₀)
    (hfix : sigR K σ a₀ = a₀) : ∀ᶠ b in 𝓝 a₀, sigR K σ b = b → IsUnitNorm K σ b := by
  obtain ⟨lam, hlam⟩ := exists_lam K h
  have h2 := two_ne_zero' F K
  set ι := algebraMap K (K ⊗[F] E) with hι
  have hcancel : ∀ b c : K ⊗[F] E, b + b = c + c → b = c := by
    intro b c hbc
    have e1 : ι 2 * b = ι 2 * c := by rw [map_ofNat, two_mul, two_mul, hbc]
    have hu : IsUnit (ι 2) := (IsUnit.mk0 _ h2).map ι
    exact hu.mul_left_cancel e1
  set k₀ := lam a₀ with hk₀def
  have hk₀ : ι k₀ = a₀ + a₀ := by rw [hk₀def, ← hlam, hfix]
  have hk0 : k₀ ≠ 0 := by
    intro hk
    have : a₀ = 0 := hcancel _ _ (by rw [← hk₀, hk, map_zero, add_zero])
    exact ha.isUnit.ne_zero this
  obtain ⟨U, hU, hUsq⟩ := GlobalTheory.sqOpen_of_two_ne_zero K h2 {μ | μ ≠ 0} (isOpen_ne.mem_nhds one_ne_zero)
  have hc : Continuous fun b => lam b / k₀ := (IsModuleTopology.continuous_of_linearMap lam).div_const k₀
  have hmem : (fun b => lam b / k₀) ⁻¹' U ∈ 𝓝 a₀ :=
    hc.continuousAt.preimage_mem_nhds (by simpa [← hk₀def, div_self hk0] using hU)
  filter_upwards [hmem] with b hb hbfix
  obtain ⟨μ, hμ0, hμ⟩ := hUsq _ hb
  obtain ⟨s, hs, hss⟩ := ha
  refine ⟨ι μ * s, ((IsUnit.mk0 _ hμ0).map ι).mul hs, ?_⟩
  apply hcancel
  rw [map_mul, sigR_algebraMap']
  have e2 : ι (lam b) = b + b := by rw [← hlam, hbfix]
  have e3 : lam b = μ ^ 2 * k₀ := by rw [hμ]; field_simp
  rw [← e2, e3, map_mul, hk₀, ← hss, map_pow]
  ring

theorem isOpen_unitNorm {X : Type} [TopologicalSpace X] {σ : E →ₐ[F] E} (h : IsCMExt F E σ)
    {f : X → K ⊗[F] E} (hf : Continuous f) (hfix : ∀ t, sigR K σ (f t) = f t) :
    IsOpen {t | IsUnitNorm K σ (f t)} := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  filter_upwards [hf.continuousAt.eventually (isUnitNorm_nhds K h ht (hfix t))] with s hs using hs (hfix s)

theorem dense_inclR (hd : DenseRange (algebraMap F K)) : Dense (Set.range (inclR (F := F) (E := E) K)) := by
  let S : AddSubgroup (K ⊗[F] E) := (inclR (F := F) (E := E) K).range.toAddSubgroup
  have hS : (S.topologicalClosure : Set (K ⊗[F] E)) = closure (Set.range (inclR (F := F) (E := E) K)) := by
    rw [AddSubgroup.topologicalClosure_coe]
    rfl
  intro u
  rw [← hS]
  induction u using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add a b ha hb => exact add_mem ha hb
  | tmul k e =>
    refine hd.induction_on (p := fun k => k ⊗ₜ[F] e ∈ S.topologicalClosure) k ?_ ?_
    · have hc : Continuous fun k : K => k ⊗ₜ[F] e := by
        have : (fun k : K => k ⊗ₜ[F] e) = fun k => k • ((1 : K) ⊗ₜ[F] e) := by
          funext k; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact (continuous_id : Continuous fun k : K => k).smul (continuous_const : Continuous fun _ : K => (1 : K) ⊗ₜ[F] e)
      exact S.isClosed_topologicalClosure.preimage hc
    · intro c
      apply S.le_topologicalClosure
      refine ⟨c • e, ?_⟩
      simp [inclR, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem dense_ratVec (hd : DenseRange (algebraMap F K)) (M : ℕ) :
    Dense (Set.range fun z : Fin M → E => fun i => inclR (F := F) K (z i)) := by
  have e1 : (Set.range fun z : Fin M → E => fun i => inclR (F := F) K (z i)) =
      Set.univ.pi (fun _ => Set.range (inclR (F := F) (E := E) K)) := by
    ext v
    simp only [Set.mem_range, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨z, rfl⟩ i
      exact ⟨z i, rfl⟩
    · intro hv
      choose z hz using hv
      exact ⟨z, funext hz⟩
  rw [e1]
  intro v
  rw [closure_pi_set]
  intro i _
  rw [(dense_inclR K hd).closure_eq]
  trivial

end Top

section Expand

variable {A : Type} [CommRing A] {M : ℕ}

theorem hform_add_smul_right (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (a b d : Fin M → A) (c : A) :
    Formalism.UG.hform s J a (b + c • d) = Formalism.UG.hform s J a b + c * Formalism.UG.hform s J a d := by
  simp only [Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_add_smul_left (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (a b d : Fin M → A) (c : A) :
    Formalism.UG.hform s J (b + c • d) a = Formalism.UG.hform s J b a + s c * Formalism.UG.hform s J d a := by
  simp only [Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    map_add, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Expand

theorem approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [Algebra F K],
    DenseRange (algebraMap F K) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ x y : Fin M → E, hE σ J x x ≠ 0 → ∀ w : Fin M → K ⊗[F] E,
    IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (x i)) w)) →
    IsUnitNorm K σ (-(gram2R K σ J w (fun i => inclR K (y i)))) →
    ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ IsUnitNorm K σ (-(inclR K (gram2E σ J x z))) ∧
      IsUnitNorm K σ (-(inclR K (gram2E σ J z y))) := by
  intro F E _ _ _ _ _ σ h K _ _ _ hd M J hJ x y hxx w h1 h2
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (K ⊗[F] E) := IsModuleTopology.isTopologicalRing K _
  have hσ := GlobalTheory.HermLineZeros.conj_invol h
  set xb : Fin M → K ⊗[F] E := fun i => inclR K (x i) with hxb
  set yb : Fin M → K ⊗[F] E := fun i => inclR K (y i) with hyb
  set ι := algebraMap K (K ⊗[F] E) with hι

  set U1 := {v : Fin M → K ⊗[F] E | IsUnitNorm K σ (-(gram2R K σ J xb v))} with hU1def
  set U2 := {v : Fin M → K ⊗[F] E | IsUnitNorm K σ (-(gram2R K σ J v yb))} with hU2def
  have hU1 : IsOpen U1 := isOpen_unitNorm K h
    ((continuous_gram2R K σ J continuous_const continuous_id).neg)
    (fun v => by rw [map_neg, sigR_gram2R K hσ hJ.1])
  have hU2 : IsOpen U2 := isOpen_unitNorm K h
    ((continuous_gram2R K σ J continuous_id continuous_const).neg)
    (fun v => by rw [map_neg, sigR_gram2R K hσ hJ.1])

  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.2 (algebraMap F E).injective)
  have hφ1 : φ 1 = 1 := by simpa using LinearMap.congr_fun hφ 1
  let ψ : E →ₗ[F] F := φ ∘ₗ LinearMap.mulLeft F (hE σ J x x)⁻¹
  have hψ : ψ (hE σ J x x) = 1 := by
    change φ ((hE σ J x x)⁻¹ * hE σ J x x) = 1
    rw [inv_mul_cancel₀ hxx, hφ1]
  let lam : K ⊗[F] E →ₗ[K] K := (TensorProduct.AlgebraTensorModule.rid F K K).toLinearMap ∘ₗ ψ.baseChange K
  have hlamι : ∀ e, lam (inclR K e) = algebraMap F K (ψ e) := by
    intro e
    simp [lam, inclR, Algebra.algebraMap_eq_smul_one]
  have hlamA : lam (hR K σ J xb xb) = 1 := by
    rw [hxb, hR_incl, hlamι, hψ, map_one]
  have hlamsmul : ∀ (k : K) (u : K ⊗[F] E), lam (ι k * u) = k * lam u := by
    intro k u
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]

  let wε : K → Fin M → K ⊗[F] E := fun ε => w + ι ε • xb
  have hsig : ∀ ε, sigR K σ (ι ε) = ι ε := sigR_algebraMap' K σ
  have hg1 : ∀ ε, gram2R K σ J xb (wε ε) = gram2R K σ J xb w := by
    intro ε
    simp only [wε, gram2R, hR, hform_add_smul_right, hform_add_smul_left, GlobalTheory.HermLineZeros.hform_expand]
    rw [hsig]
    ring
  have hpoly : ∀ ε, lam (hR K σ J (wε ε) (wε ε)) =
      ε ^ 2 + lam (hR K σ J w xb + hR K σ J xb w) * ε + lam (hR K σ J w w) := by
    intro ε
    have e1 : hR K σ J (wε ε) (wε ε) = hR K σ J w w + ι ε * (hR K σ J w xb + hR K σ J xb w)
        + ι ε * (ι ε * hR K σ J xb xb) := by
      simp only [wε, hR, GlobalTheory.HermLineZeros.hform_expand]
      rw [hsig]
      ring
    rw [e1, map_add, map_add, hlamsmul, hlamsmul, hlamsmul, hlamA]
    ring

  set P : Polynomial K := Polynomial.X ^ 2 + Polynomial.C (lam (hR K σ J w xb + hR K σ J xb w)) * Polynomial.X
    + Polynomial.C (lam (hR K σ J w w)) with hP
  have hP0 : P ≠ 0 := by
    intro h0
    have := congrArg (fun p => Polynomial.coeff p 2) h0
    simp [hP, Polynomial.coeff_X, Polynomial.coeff_C] at this
  have hZ : {ε : K | P.IsRoot ε}.Countable := (Polynomial.finite_setOf_isRoot hP0).countable
  have hD : Dense {ε : K | P.IsRoot ε}ᶜ := hZ.dense_compl K
  have hcι : Continuous ι :=
    ((continuous_id : Continuous fun k : K => k).smul
      (continuous_const : Continuous fun _ : K => (1 : K ⊗[F] E))).congr
      (fun k => (Algebra.algebraMap_eq_smul_one k).symm)
  have hcw : Continuous wε := continuous_const.add (hcι.smul continuous_const)
  have hV : IsOpen (wε ⁻¹' U2) := hU2.preimage hcw
  have h0 : (0 : K) ∈ wε ⁻¹' U2 := by
    change IsUnitNorm K σ (-(gram2R K σ J (w + ι 0 • xb) yb))
    rw [map_zero, zero_smul, add_zero]
    exact h2
  obtain ⟨ε, hεD, hεV⟩ := hD.exists_mem_open hV ⟨0, h0⟩

  set U3 := {v : Fin M → K ⊗[F] E | lam (hR K σ J v v) ≠ 0} with hU3def
  have hU3 : IsOpen U3 := isOpen_ne.preimage
    ((IsModuleTopology.continuous_of_linearMap lam).comp (continuous_hR K σ J continuous_id continuous_id))
  have hO : IsOpen (U1 ∩ U2 ∩ U3) := (hU1.inter hU2).inter hU3
  have hmem : wε ε ∈ U1 ∩ U2 ∩ U3 := by
    refine ⟨⟨?_, hεV⟩, ?_⟩
    · change IsUnitNorm K σ (-(gram2R K σ J xb (wε ε)))
      rw [hg1]
      exact h1
    · change lam (hR K σ J (wε ε) (wε ε)) ≠ 0
      rw [hpoly]
      intro h0
      apply hεD
      change P.IsRoot ε
      simp only [hP, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      rw [← h0]
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := (dense_ratVec K hd M).exists_mem_open hO ⟨_, hmem⟩
  refine ⟨z, ?_, ?_, ?_⟩
  · intro h0
    apply hz.2
    change lam (hR K σ J (fun i => inclR K (z i)) (fun i => inclR K (z i))) = 0
    rw [hR_incl, h0, map_zero, map_zero]
  · rw [← hermitianGramDetTwoVectorsTensor_incl]
    exact hz.1.1
  · rw [← hermitianGramDetTwoVectorsTensor_incl]
    exact hz.1.2

end GlobalTheory.PlaneNormApprox
