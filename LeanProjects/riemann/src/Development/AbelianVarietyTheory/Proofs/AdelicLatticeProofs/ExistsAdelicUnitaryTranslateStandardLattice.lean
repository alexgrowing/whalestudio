import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUnitaryOfSelfDual

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped TensorProduct Matrix

namespace GlobalTheory.AdelTranslate

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def tv (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) : Fin n → RA F E := fun i => a ⊗ₜ[F] x i

theorem tv_nsmul_left (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) : tv (d • a) x = d • tv a x := by
  funext i
  simp only [tv, Pi.smul_apply]
  induction d with
  | zero => simp
  | succ d ih => rw [succ_nsmul, succ_nsmul, TensorProduct.add_tmul, ih]

theorem tv_nsmul_right (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) : tv a (d • x) = d • tv a x :=
  cap_tmul_nsmul F d a x

theorem tv_mul_mem {L : Set (Fin n → E)} {a b : FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) (hb : ∀ v, b v ∈ v.adicCompletionIntegers F) {x : Fin n → E}
    (hx : x ∈ L) : tv (a * b) x ∈ hat F L := by
  have h : ∀ v : HeightOneSpectrum (𝓞 F), (a * b) v ∈ v.adicCompletionIntegers F := fun v => by
    change a v * b v ∈ _
    exact mul_mem (ha v) (hb v)
  exact cap_gen_mem F L (a * b) h x hx

def glue (e : FiniteAdeleRing (𝓞 F) F) (γ : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) (RA F E) :=
  (e ⊗ₜ[F] (1 : E) : RA F E) • fm F γ + (1 - e ⊗ₜ[F] (1 : E) : RA F E) • (1 : Matrix (Fin n) (Fin n) (RA F E))

theorem glue_mulVec_tv (e a : FiniteAdeleRing (𝓞 F) F) (γ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    glue e γ *ᵥ tv a x = tv (e * a) (γ *ᵥ x) + tv ((1 - e) * a) x := by
  rw [glue, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  funext i
  simp only [tv, fm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Finset.mul_sum, TensorProduct.tmul_sum, sub_mul,
    TensorProduct.sub_tmul]

theorem fm_mul (γ δ : Matrix (Fin n) (Fin n) E) : fm F γ * fm F δ = fm F (γ * δ) :=
  (Matrix.map_mul (f := (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E))).symm

theorem fm_one : fm F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (by simp) (Algebra.TensorProduct.one_def).symm

theorem glue_mul {e : FiniteAdeleRing (𝓞 F) F} (he : e * e = e) {γ δ : Matrix (Fin n) (Fin n) E}
    (h : γ * δ = 1) : glue e γ * glue e δ = 1 := by
  have hε : (e ⊗ₜ[F] (1 : E) : RA F E) * (e ⊗ₜ[F] (1 : E)) = e ⊗ₜ[F] (1 : E) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, he, one_mul]
  unfold glue
  generalize (e ⊗ₜ[F] (1 : E) : RA F E) = ε at hε
  have h1 : (1 - ε) * ε = 0 := by linear_combination -hε
  have h2 : ε * (1 - ε) = 0 := by linear_combination -hε
  have h3 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, fm_mul, h,
    fm_one, Matrix.mul_one, Matrix.one_mul, hε, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

theorem glue_map_sg (c : E ≃ₐ[F] E) (e : FiniteAdeleRing (𝓞 F) F) (γ : Matrix (Fin n) (Fin n) E) :
    ((glue e γ).map (sg (FiniteAdeleRing (𝓞 F) F) c))ᵀ = glue e (γ.map c)ᵀ := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [glue, fm, sg]
  · simp [glue, fm, sg, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem isUnA_of (c : E ≃ₐ[F] E) {g : Matrix (Fin n) (Fin n) (RA F E)}
    (h : (g.map (sg (FiniteAdeleRing (𝓞 F) F) c))ᵀ * g = 1) : IsUnA c (1 : Matrix (Fin n) (Fin n) E) g := by
  have hA : ∀ x y : Fin n → RA F E, hermA c (1 : Matrix (Fin n) (Fin n) E) x y =
      (fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b)) ⬝ᵥ x := fun x y => by
    simp only [hermA, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [Matrix.one_apply_eq, ← Algebra.TensorProduct.one_def, mul_one, mul_comm]
    · intro b _ hb
      rw [Matrix.one_apply_ne hb.symm]
      simp
    · simp
  intro x y
  have : (fun b => sg (FiniteAdeleRing (𝓞 F) F) c ((g *ᵥ y) b)) =
      g.map (sg (FiniteAdeleRing (𝓞 F) F) c) *ᵥ fun b => sg (FiniteAdeleRing (𝓞 F) F) c (y b) :=
    funext fun i => RingHom.map_mulVec (sg (FiniteAdeleRing (𝓞 F) F) c : RA F E →+* RA F E) g y i
  rw [hA, hA, this, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]

theorem exists_div (d : ℕ) (e : FiniteAdeleRing (𝓞 F) F) (he : ∀ v, e v ∈ v.adicCompletionIntegers F)
    (hd : ∀ v : HeightOneSpectrum (𝓞 F), (d : 𝓞 F) ∈ v.asIdeal → e v = 0) :
    ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ d • a = e := by
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · refine ⟨0, fun v => (v.adicCompletionIntegers F).zero_mem, ?_⟩
    rw [zero_smul]
    refine DFunLike.ext _ _ fun v => ?_
    exact (hd v (by simp)).symm
  have hd0 : (d : F) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  refine ⟨algebraMap F _ (d : F)⁻¹ * e, fun v => ?_, ?_⟩
  · change algebraMap F (v.adicCompletion F) (d : F)⁻¹ * e v ∈ _
    by_cases h : (d : 𝓞 F) ∈ v.asIdeal
    · rw [hd v h, mul_zero]
      exact zero_mem _
    · refine mul_mem ?_ (he v)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have h1 : v.valuation F (algebraMap (𝓞 F) F (d : 𝓞 F)) = 1 := by
        refine le_antisymm (v.valuation_le_one _) (not_lt.1 fun h' => h ?_)
        exact (v.valuation_lt_one_iff_mem _).1 h'
      rw [map_natCast] at h1
      have h2 := v.valuedAdicCompletion_eq_valuation' (d : F)⁻¹
      exact le_of_eq (h2.trans (by rw [map_inv₀, h1, inv_one]))
  · rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul,
      mul_inv_cancel₀ hd0, map_one, one_mul]

open Classical in

def idem (F : Type) [Field F] [NumberField F] (k : ℕ) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if (k : 𝓞 F) ∈ v.asIdeal then 1 else 0, Filter.Eventually.of_forall fun v => by
    dsimp only
    split_ifs
    · exact (v.adicCompletionIntegers F).one_mem
    · exact (v.adicCompletionIntegers F).zero_mem⟩

open Classical in
theorem idem_apply (k : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    idem F k v = if (k : 𝓞 F) ∈ v.asIdeal then 1 else 0 := rfl

theorem idem_mul (k : ℕ) : idem F k * idem F k = idem F k := by
  refine DFunLike.ext _ _ fun v => ?_
  change idem F k v * idem F k v = idem F k v
  rw [idem_apply]
  split_ifs <;> simp

theorem idem_int (k : ℕ) (v : HeightOneSpectrum (𝓞 F)) : idem F k v ∈ v.adicCompletionIntegers F := by
  rw [idem_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem exists_div_idem {k d : ℕ} (h : d.Coprime k) :
    ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ d • a = idem F k := by
  refine exists_div d _ (idem_int k) fun v hv => ?_
  rw [idem_apply, if_neg]
  intro hk
  obtain ⟨a, b, hab⟩ : IsCoprime (d : 𝓞 F) (k : 𝓞 F) := Nat.Coprime.cast h
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ add_mem (v.asIdeal.mul_mem_left a hv) (v.asIdeal.mul_mem_left b hk)))

theorem exists_div_one_sub_idem (k : ℕ) :
    ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ k • a = 1 - idem F k := by
  refine exists_div k _ (fun v => ?_) fun v hv => ?_
  · change 1 - idem F k v ∈ _
    exact sub_mem (one_mem _) (idem_int k v)
  · change 1 - idem F k v = 0
    rw [idem_apply, if_pos hv, sub_self]

theorem glue_mem_hat {L₁ L₂ : Set (Fin n → E)} {k k' : ℕ} (hk : k'.Coprime k) {γ : Matrix (Fin n) (Fin n) E}
    (h₁ : ∀ x ∈ L₁, k' • γ *ᵥ x ∈ L₂) (h₂ : ∀ x ∈ L₁, k • x ∈ L₂) :
    ∀ z ∈ hat F L₁, glue (idem F k) γ *ᵥ z ∈ hat F L₂ := by
  obtain ⟨a, ha, ea⟩ := exists_div_idem (F := F) hk
  obtain ⟨b, hb, eb⟩ := exists_div_one_sub_idem (F := F) k
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hz
    change glue (idem F k) γ *ᵥ tv c x ∈ _
    rw [glue_mulVec_tv, ← eb, ← ea, smul_mul_assoc, smul_mul_assoc, tv_nsmul_left, tv_nsmul_left,
      ← tv_nsmul_right, ← tv_nsmul_right]
    exact add_mem (tv_mul_mem ha hc (h₁ x hx)) (tv_mul_mem hb hc (h₂ x hx))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem exists_factor {k M : ℕ} (h : k.Coprime M) (D : ℕ) (hD : 0 < D) :
    ∃ D₁ D₂ : ℕ, D = D₁ * D₂ ∧ D₁.Coprime M ∧ D₂.Coprime k := by
  induction D using Nat.recOnMul with
  | zero => exact absurd hD (lt_irrefl 0)
  | one => exact ⟨1, 1, rfl, by simp, by simp⟩
  | prime p hp =>
    by_cases hpk : p ∣ k
    · exact ⟨p, 1, by simp, Nat.Coprime.coprime_dvd_left hpk h, by simp⟩
    · exact ⟨1, p, by simp, by simp, (Nat.Prime.coprime_iff_not_dvd hp).2 hpk⟩
  | mul a b ha hb =>
    obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := ha (Nat.pos_of_mul_pos_right hD)
    obtain ⟨b₁, b₂, rfl, h₃, h₄⟩ := hb (Nat.pos_of_mul_pos_left hD)
    exact ⟨a₁ * b₁, a₂ * b₂, by ring, Nat.Coprime.mul_left h₁ h₃, Nat.Coprime.mul_left h₂ h₄⟩

theorem congAtA_glue (L : Submodule (𝓞 E) (Fin n → E)) {k k' M : ℕ} (hk : k'.Coprime k) (hM : k.Coprime M)
    {γ : Matrix (Fin n) (Fin n) E} (h : ∀ x ∈ L, (k * k') • γ *ᵥ x ∈ L) (D : ℕ) (hD : 0 < D) :
    CongAtA F L M D (glue (idem F k) γ) := by
  obtain ⟨D₁, D₂, rfl, h₁, h₂⟩ := exists_factor hM D hD
  obtain ⟨a, ha, ea⟩ := exists_div_idem (F := F) (Nat.Coprime.mul_left h₂ hk)
  refine ⟨D₁ * k, Nat.Coprime.mul_left h₁ hM, fun z hz => ?_⟩
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hz
    refine ⟨tv (a * c) ((k * k') • (γ *ᵥ x - x)), tv_mul_mem ha hc ?_, ?_⟩
    · rw [smul_sub]
      exact L.sub_mem (h x hx) (nsmul_mem hx _)
    · change (D₁ * k) • (glue (idem F k) γ *ᵥ tv c x - tv c x) = _
      have e1 : glue (idem F k) γ *ᵥ tv c x - tv c x = tv (idem F k * c) (γ *ᵥ x - x) := by
        rw [glue_mulVec_tv]
        funext i
        simp only [tv, Pi.add_apply, Pi.sub_apply, sub_mul, one_mul, TensorProduct.sub_tmul,
          TensorProduct.tmul_sub]
        abel
      rw [e1, ← ea, smul_mul_assoc, tv_nsmul_left, tv_nsmul_right, smul_smul, smul_smul]
      congr 1
      ring
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add z z' _ _ hz hz' =>
    obtain ⟨w, hw, e⟩ := hz
    obtain ⟨w', hw', e'⟩ := hz'
    refine ⟨w + w', add_mem hw hw', ?_⟩
    rw [smul_add, ← e, ← e', ← smul_add, Matrix.mulVec_add]
    congr 1
    abel
  | neg z _ hz =>
    obtain ⟨w, hw, e⟩ := hz
    refine ⟨-w, neg_mem hw, ?_⟩
    rw [smul_neg, ← e, ← smul_neg, Matrix.mulVec_neg]
    congr 1
    abel

end General

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem span_eq_top (Λ : GenLat E n) (hU : Λ.Unimod) : Submodule.span E (Λ.La : Set (Fin n → E)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let v : Fin n → E := fun j => IsCMField.complexConj E (φ (Pi.single j 1))
  have hv : ∀ w : Fin n → E, ∑ j, IsCMField.complexConj E (v j) * w j = φ w := fun w => by
    rw [LinearMap.pi_apply_eq_sum_univ φ w]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (fun i => if j = i then (1 : E) else 0) = Pi.single j 1 := by
      funext i
      simp [Pi.single_apply, eq_comm]
    simp [v, this, mul_comm]
  have h0 : ∀ w ∈ Λ.La, φ w = 0 := fun w hw => hφ (Submodule.subset_span hw)
  have hvΛ : v ∈ Λ.La := (hU v).2 fun w hw => by
    rw [hv, h0 w hw]
    exact zero_mem _
  have h1 : ∑ j, IsCMField.complexConj E (v j) * v j = 0 := (hv v).trans (h0 v hvΛ)
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h2 : ∑ j, Complex.normSq (σ (v j)) = 0 := by
    have := congrArg σ h1
    simp only [map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_zero,
      ← Complex.normSq_eq_conj_mul_self] at this
    exact_mod_cast this
  have h3 : ∀ j, v j = 0 := fun j => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).1 h2 j (Finset.mem_univ j)
    simpa using this
  refine hφ0 (LinearMap.ext fun w => ?_)
  rw [← hv]
  simp [h3]

omit [IsCMField E] in
theorem span_smul_le_iff (k : ℕ) (L₁ L₂ : Submodule (𝓞 E) (Fin n → E)) :
    Ideal.span {(k : 𝓞 E)} • L₁ ≤ L₂ ↔ ∀ x ∈ L₁, k • x ∈ L₂ := by
  constructor
  · intro h x hx
    have := h (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hx)
    rwa [Nat.cast_smul_eq_nsmul] at this
  · intro h
    refine Submodule.smul_le.2 fun r hr x hx => ?_
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
    exact L₂.smul_mem a (h x hx)

theorem exists_pos (Λ : GenLat E n) (hU : Λ.Unimod) {M : ℕ} (hT : Λ.TrivAt M) :
    ∃ k : ℕ, 0 < k ∧ k.Coprime M ∧ (∀ x ∈ Λ.La, k • x ∈ stdLat E n) ∧ ∀ x ∈ stdLat E n, k • x ∈ Λ.La := by
  classical
  obtain ⟨k, hk, h₁, h₂⟩ := hT
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · obtain rfl : M = 1 := by simpa using hk
    choose d hd hdx using fun j : Fin n => cap_exists_denom Λ.La (span_eq_top Λ hU) (Pi.single j 1)
    have hs : ∀ j, (∏ i, d i) • (Pi.single j 1 : Fin n → E) ∈ Λ.La := fun j => by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ j)
      rw [hc, mul_comm, mul_smul]
      exact nsmul_mem (hdx j) c
    refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, by simp, fun x hx j _ => ?_, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := (hU _).1 (hs j) x hx
      refine Submodule.mem_one.2 ⟨a, ha.trans ?_⟩
      simp [Pi.single_apply, apply_ite]
    · rw [← Finset.univ_sum_single x, Finset.smul_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hx j (Set.mem_univ j))
      convert Λ.La.smul_mem a (hs j) using 1
      rw [smul_comm a]
      congr 1
      funext i
      simp [Pi.single_apply, Algebra.smul_def, ← ha]
  · exact ⟨k, hpos, hk, (span_smul_le_iff _ _ _).1 h₁, (span_smul_le_iff _ _ _).1 h₂⟩

end Lattice

theorem exists_adelic_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n M : ℕ) (Λ : GenLat E n), 0 < M → Λ.Unimod → Λ.TrivAt M → ∃ g : GL (Fin n) (RA (maximalRealSubfield E) E), IsUnA (IsCMField.complexConj E) (1 : Matrix (Fin n) (Fin n) E) g.1 ∧ (Λ.La : Set (Fin n → E)) = latOf (maximalRealSubfield E) g.1 (stdLat E n : Set (Fin n → E)) ∧ ∀ D : ℕ, 0 < D → CongAtA (maximalRealSubfield E) (stdLat E n) M D g.1 := by
  intro E _ _ _ H n M Λ _ hU hT
  obtain ⟨k, hk0, hkM, h₁, h₂⟩ := exists_pos Λ hU hT
  have hle := (span_smul_le_iff k _ _).2 h₂
  obtain ⟨k', γ, hk', hγ, h₃, h₄⟩ := GlobalTheory.AdaptUnitary.exists_unitary_adapted E H n Λ k hU hk0 hle k hk0
  obtain ⟨Λ', hΛ', -⟩ := GlobalTheory.AdaptUnitary.exists_lat Λ hU hk0 hle
  have hcap := (hat_rational_points_and_approx (maximalRealSubfield E) E n Λ.La (hΛ' ▸ Λ'.fg)
    (span_eq_top Λ hU)).1
  set c := IsCMField.complexConj E with hc
  set δ : Matrix (Fin n) (Fin n) E := (γ.map c)ᵀ with hδ
  have hδγ : δ * γ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← hγ i j]
    rfl
  have hγδ : γ * δ = 1 := mul_eq_one_comm.1 hδγ
  have hδc : (δ.map c)ᵀ = γ := by
    ext i j
    simp [hδ, hc]
  have h₅ : ∀ x ∈ stdLat E n, k' • δ *ᵥ x ∈ Λ.La := fun x hx => by
    obtain ⟨w, hw, e⟩ := h₄ x hx
    rwa [← Nat.cast_smul_eq_nsmul E, ← Matrix.mulVec_smul, e, Matrix.mulVec_mulVec, hδγ, Matrix.one_mulVec]
  have h₆ : ∀ x ∈ Λ.La, k' • γ *ᵥ x ∈ stdLat E n := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul E]
    exact h₃ x hx
  have he := idem_mul (F := maximalRealSubfield E) k
  refine ⟨⟨glue (idem _ k) δ, glue (idem _ k) γ, glue_mul he hδγ, glue_mul he hγδ⟩, isUnA_of c ?_, ?_,
    congAtA_glue _ hk' hkM fun x hx => ?_⟩
  · change ((glue (idem _ k) δ).map _)ᵀ * glue (idem _ k) δ = 1
    rw [glue_map_sg, hδc]
    exact glue_mul he hγδ
  · ext v
    constructor
    · intro hv
      refine ⟨_, glue_mem_hat hk' h₆ h₁ _ (cap_fv_mem (maximalRealSubfield E) _ v hv), ?_⟩
      change glue (idem _ k) δ *ᵥ _ = _
      rw [Matrix.mulVec_mulVec, glue_mul he hδγ, Matrix.one_mulVec]
    · rintro ⟨z, hz, e⟩
      exact (hcap v).1 (e ▸ glue_mem_hat hk' h₅ h₂ z hz)
  · rw [mul_smul]
    exact h₁ _ (h₅ x hx)

end GlobalTheory.AdelTranslate
