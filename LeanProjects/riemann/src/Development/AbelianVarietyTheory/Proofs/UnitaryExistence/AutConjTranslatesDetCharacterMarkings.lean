import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ConjugationActsOnCmTorsionByMultiplicationStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingConjugateComponentAdelicStatement

namespace GlobalTheory.DetTranslate

section Adelic

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_mem_int {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (G : Matrix (Fin n) (Fin n) (RA F E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hg : ∀ z ∈ hat F (L : Set (Fin n → E)), G *ᵥ z ∈ hat F (L : Set (Fin n → E))) :
    G.det ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have key' : ∀ w, P *ᵥ w ∈ hat F (L : Set (Fin n → E)) ↔ ∀ a, w a ∈ hat1 F (cI a : Set E) := by
    intro w; rw [hP]; exact key w
  let k : Matrix (Fin n) (Fin n) (RA F E) := Q * G * P
  have hPk : P * k = G * P := by
    simp only [k, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hkdet : k.det = G.det := by
    have : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
    simp only [k, Matrix.det_mul]
    linear_combination G.det * this
  have hk : ∀ i j, k i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    refine mem_adelicCompletion_mul_inv_fractionalIdeal F _ _ _ (hc j) fun x hx => ?_
    have h1 : P *ᵥ (Pi.single j ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x)) ∈
        hat F (L : Set (Fin n → E)) := by
      rw [key']
      intro a
      by_cases ha : a = j
      · subst ha
        rw [Pi.single_eq_same]
        exact one_tmul_mem_adelicCompletionOfElementSet F hx
      · rw [Pi.single_eq_of_ne ha]
        exact zero_mem _
    have h2 := hg _ h1
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, key'] at h2
    have h3 := h2 i
    rwa [Matrix.mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at h3
  have hd := det_mem_adelicCompletionOfElementSet F cI (fun j => (cI j)⁻¹) k hk
  rw [← Finset.prod_mul_distrib, Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hc i), hkdet] at hd
  have e1 : ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) = Set.range (algebraMap (𝓞 E) E) := by
    ext x
    exact FractionalIdeal.mem_one_iff _
  rwa [e1] at hd

omit [NumberField E] in

theorem int_mul_mem (I : Ideal (𝓞 E)) {x y : RA F E} (hx : x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (hy : y ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E)))) :
    x * y ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E))) := by
  refine mul_mem_adelicCompletionOfElementSet_of_mul_mem F ?_ hx hy
  rintro _ ⟨a, rfl⟩ _ ⟨b, hb, rfl⟩
  exact ⟨a * b, I.mul_mem_left a hb, map_mul _ _ _⟩

omit [NumberField E] in

theorem exists_nsmul_of_mem (M : ℕ) {x : RA F E}
    (hx : x ∈ hat1 F (algebraMap (𝓞 E) E '' (Ideal.span {(M : 𝓞 E)} : Ideal (𝓞 E)))) :
    ∃ w ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), x = M • w := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩ := hz
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.1 hb
    refine ⟨_, tmul_mem_adelicCompletion_of_integral F ha ⟨t, rfl⟩, ?_⟩
    rw [map_mul, map_natCast, ← nsmul_eq_mul, TensorProduct.tmul_smul]
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨u + w, add_mem hu hw, (smul_add _ _ _).symm⟩
  | neg x _ hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨-u, neg_mem hu, (smul_neg _ _).symm⟩

omit [NumberField E] in

theorem quot_cong_one (c : E ≃ₐ[F] E) (M : ℕ) (I I' : Ideal (𝓞 E)) (hsup : I ⊔ I' = ⊤)
    (hmul : I * I' = Ideal.span {(M : 𝓞 E)}) (hc : ∀ b ∈ I, ∃ b' ∈ I', ((b' : 𝓞 E) : E) = c (b : E))
    (d₁ d₂ S : RA F E) (h₁ : d₁ ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (h₂ : d₂ ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (n₁ : d₁ * sg (FiniteAdeleRing (𝓞 F) F) c d₁ = 1) (n₂ : d₂ * sg (FiniteAdeleRing (𝓞 F) F) c d₂ = 1)
    (s₁ : d₁ * S - 1 ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E))))
    (s₂ : d₂ * S - 1 ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E)))) :
    ∃ w ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), d₁ * sg (FiniteAdeleRing (𝓞 F) F) c d₂ - 1 = M • w := by
  have hO : ∀ x ∈ Set.range (algebraMap (𝓞 E) E), c x ∈ Set.range (algebraMap (𝓞 E) E) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨c y, (RingOfIntegers.isIntegral_coe y).map c.toRingEquiv.toRingHom.toIntAlgHom⟩, rfl⟩
  have h₂' := galoisAut_mem_adelicCompletionOfElementSet F c hO h₂
  set s := sg (FiniteAdeleRing (𝓞 F) F) c with hs
  have he : d₁ * s d₂ ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) :=
    mul_mem_adelicCompletionOfElementSet_of_mul_mem F (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩) h₁ h₂'
  have hI : d₁ * s d₂ - 1 ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E))) := by
    have := int_mul_mem F I h₂' (sub_mem (int_mul_mem F I h₂ s₁) (int_mul_mem F I h₁ s₂))
    convert this using 1
    linear_combination n₂
  have hI' : d₁ * s d₂ - 1 ∈ hat1 F (algebraMap (𝓞 E) E '' (I' : Set (𝓞 E))) := by
    have h3 : s (d₁ * s d₂ - 1) ∈ hat1 F (algebraMap (𝓞 E) E '' (I' : Set (𝓞 E))) := by
      refine galoisAut_mem_adelicCompletionOfElementSet F c ?_ hI
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨b', hb', e⟩ := hc b hb
      exact ⟨b', hb', e⟩
    have n₃ := congrArg s n₂
    rw [map_mul, map_one] at n₃
    have := neg_mem (int_mul_mem F I' he h3)
    convert this using 1
    rw [map_sub, map_mul, map_one]
    linear_combination (s d₂ * s (s d₂)) * n₁ + n₃
  obtain ⟨b, hb, b', hb', hbb⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hsup)
  have hβ : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) : RA F E) +
      (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b' : E) = 1 := by
    rw [← TensorProduct.tmul_add, Algebra.TensorProduct.one_def]
    congr 1
    have := congrArg (fun x : 𝓞 E => (x : E)) hbb
    simpa using this
  apply exists_nsmul_of_mem F M
  rw [← hmul]
  have hK : ∀ x ∈ algebraMap (𝓞 E) E '' (I : Set (𝓞 E)), ∀ y ∈ algebraMap (𝓞 E) E '' (I' : Set (𝓞 E)),
      x * y ∈ algebraMap (𝓞 E) E '' ((I * I' : Ideal (𝓞 E)) : Set (𝓞 E)) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x * y, Ideal.mul_mem_mul hx hy, map_mul _ _ _⟩
  have t₁ := mul_mem_adelicCompletionOfElementSet_of_mul_mem F hK (one_tmul_mem_adelicCompletionOfElementSet F ⟨b, hb, rfl⟩) hI'
  have t₂ := mul_mem_adelicCompletionOfElementSet_of_mul_mem F hK hI (one_tmul_mem_adelicCompletionOfElementSet F ⟨b', hb', rfl⟩)
  convert add_mem t₁ t₂ using 1
  linear_combination (1 - d₁ * s d₂) * hβ

end Adelic

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

theorem gLat_mul {D : D7} (V : HSp D) (u v : GA D V) :
    gLat V (u * v) = (finHom V u).1.mulVec '' gLat V v := by
  unfold gLat
  rw [Set.image_image, map_mul, Units.val_mul]
  exact Set.image_congr fun z _ => (Matrix.mulVec_mulVec _ _ _).symm

theorem gLat_one {D : D7} (V : HSp D) : gLat V 1 = latHat V := by
  unfold gLat
  rw [map_one, Units.val_one]
  exact (Set.image_congr fun z _ => Matrix.one_mulVec z).trans (Set.image_id' _)

theorem gLat_mul_inv {D : D7} (V : HSp D) {u v : GA D V} (hu : gLat V u = latHat V) (hv : gLat V v = latHat V) :
    gLat V (u * v⁻¹) = latHat V := by
  have h : gLat V v⁻¹ = latHat V := by
    have h1 := gLat_mul V v⁻¹ v
    rw [inv_mul_cancel, gLat_one, hv] at h1
    exact h1.symm
  rw [gLat_mul, h]
  exact hu

theorem det_int_of_gLat {D : D7} (V : HSp D) {u : GA D V} (hu : gLat V u = latHat V) :
    (finHom V u).1.det ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
  obtain ⟨h1, -, h2, h3, -⟩ := latHat_eq_hat_and_gram D V
  refine det_mem_int D.host.F (latC V) _ h2 h3 fun z hz => ?_
  rw [← h1] at hz ⊢
  have : (finHom V u).1 *ᵥ z ∈ gLat V u := ⟨z, hz, rfl⟩
  rw [hu] at this
  exact this

set_option maxHeartbeats 1600000 in

theorem conj_translates_det : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → (Dw.p = 0 ∨ Dw.q = 0 ∨ 3 ≤ Dw.p + Dw.q) → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → FixesCurve H τ 1 → ∀ π : Fin C.F.n → Fin C.F.n, ConjugationPermutesPeriods C.F τ π → ∀ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ, (∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom V (u)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V (u))) = 1) → (∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V (γ))) = 1) → ∃ κ : ℂˣ, (∃ u : GA D V, κ = xi (Matrix.GeneralLinearGroup.det (finHom V (u)))) ∧ ∀ h γ k h' γ', C.Mark h k γ → C.Mark h' (π k) γ' → xi (Matrix.GeneralLinearGroup.det (finHom V (γ' * h'))) = κ * xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) := by
  intro D H Dw l Xo c σ V r C hC hpq τ hτ hfix π hπ xi hK hQ
  obtain ⟨Cv, io, hio, -⟩ := hfix
  obtain ⟨⟨s, hs⟩, -⟩ := GlobalTheory.T.conjugation_acts_on_cm_torsion_by_multiplication D.host.E H Cv τ hτ io hio l.M (lt_of_lt_of_le (by norm_num) l.three_le)
  have step := GlobalTheory.T.marking_conjugate_component_adelic D H Dw l Xo c σ V r C hC hpq τ hτ Cv io s π hs hπ
  by_cases hex : ∃ h γ k h' γ', C.Mark h k γ ∧ C.Mark h' (π k) γ'
  · obtain ⟨h₀, γ₀, k₀, h₀', γ₀', m₀, m₀'⟩ := hex
    obtain ⟨-, -, u₀, hu₀, -, hd₀⟩ := step _ _ _ _ _ m₀ m₀'
    refine ⟨_, ⟨u₀⁻¹, rfl⟩, fun h γ k h' γ' m m' => ?_⟩
    obtain ⟨δ, hδ, u, hu, he, hd⟩ := step _ _ _ _ _ m m'
    have n₀ := (finHom_herm_det D V u₀).2.1
    have hq := quot_cong_one D.host.F (cF D) l.M l.Mb _ l.coprime l.prod
      (fun b hb => ⟨H.bar b, Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) hb, H.bar_eq b⟩)
      _ _ _ (det_int_of_gLat V hu) (det_int_of_gLat V hu₀) (finHom_herm_det D V u).2.1 n₀ hd hd₀
    have hinv : (((Matrix.GeneralLinearGroup.det (finHom V u₀))⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        Af D.host.F ⊗[D.host.F] D.host.E) = GlobalTheory.AdLat.sg (Af D.host.F) (cF D) (finHom V u₀).1.det :=
      Units.inv_eq_of_mul_eq_one_right n₀
    have h1 := hK (u * u₀⁻¹) (gLat_mul_inv V hu hu₀) (by
      rw [map_mul, map_inv, map_mul, map_inv, Units.val_mul, hinv]
      exact hq)
    have h2 := congrArg (fun g => xi (Matrix.GeneralLinearGroup.det g)) he
    have h3 := hQ δ hδ
    generalize finHom V (γ' * h') = A at h2 ⊢
    generalize finHom V (γ * h) = B at h2 ⊢
    simp only [map_mul, map_inv] at h1 h2 ⊢
    rw [h3, one_mul] at h2
    rw [← h2, mul_inv_eq_one.1 h1, mul_comm, mul_inv_cancel_right]
  · refine ⟨_, ⟨1, rfl⟩, fun h γ k h' γ' m m' => (hex ⟨h, γ, k, h', γ', m, m'⟩).elim⟩

end GlobalTheory.DetTranslate
