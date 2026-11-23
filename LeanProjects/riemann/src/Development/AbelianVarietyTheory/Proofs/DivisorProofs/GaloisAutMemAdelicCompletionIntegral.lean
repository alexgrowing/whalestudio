import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.SmulBasisMemHatIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf

open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct nonZeroDivisors

noncomputable section

namespace GlobalTheory.UCls.Det

theorem exists_sub_notMem {A B : Type} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra.Unramified A B] (σ : B →ₐ[A] B) (hσ : ∃ s, σ s ≠ s) (P : Ideal B) (hP : P ≠ ⊤) :
    ∃ t, t - σ t ∉ P := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs⟩ := hσ
  let φ : B ⊗[A] B →ₐ[A] B := Algebra.TensorProduct.productMap (AlgHom.id A B) σ
  have h1 : ∀ z, Algebra.TensorProduct.lmul' A (S := B) z - φ z ∈ P := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have := P.mul_mem_left x (hcon y)
      simpa [φ, mul_sub] using this
    | add x y hx hy =>
      have := P.add_mem hx hy
      convert this using 1
      simp only [map_add]; ring
  have h2 : φ (Algebra.FormallyUnramified.elem A B) = 0 := by
    have h := congrArg φ (Algebra.FormallyUnramified.one_tmul_mul_elem (R := A) s)
    simp only [map_mul, φ, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply, map_one,
      one_mul, mul_one] at h
    by_contra h0
    exact hs (mul_right_cancel₀ h0 h)
  have h3 := h1 (Algebra.FormallyUnramified.elem A B)
  rw [h2, Algebra.FormallyUnramified.lmul_elem, sub_zero] at h3
  exact hP ((Ideal.eq_top_iff_one _).2 h3)

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem herm_add_right (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp only [herm, cc, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (t : E) (x y : Fin r → E) :
    herm G (t • x) y = t * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem herm_symm (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a) (x y : Fin r → E) :
    IsCMField.complexConj E (herm G x y) = herm G y x := by
  simp only [cc] at hG
  simp only [herm, cc, map_sum, map_mul, IsCMField.complexConj_apply_apply, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem exists_herm_notMem (hr : 1 ≤ r) {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    (h : SelfDualLat G Λ) (P : Ideal (𝓞 E)) (hP : P ≠ ⊤) :
    ¬ ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ p ∈ P, (p : E) = herm G x y := by
  intro hcon
  obtain ⟨-, -, hfg, hsp, hsd⟩ := h
  have key : ∀ a : E, (∀ p ∈ P, IsIntegral ℤ (a * p)) → IsIntegral ℤ a := by
    intro a ha
    have hne : Λ ≠ ⊥ := by
      rintro rfl
      have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
      simp at hsp
    have h1 : ∀ x ∈ Λ, a • x ∈ Λ := by
      intro x hx
      refine (hsd _).1 fun y hy => ?_
      obtain ⟨p, hp, e⟩ := hcon x hx y hy
      rw [herm_smul_left, ← e]
      exact ha p hp
    have := isIntegral_of_smul_mem_submodule Λ hne hfg a h1
    exact isIntegral_trans (A := 𝓞 E) a this
  by_cases h0 : P = ⊥
  · subst h0
    have := key (2 : E)⁻¹ (fun p hp => by
      rw [Ideal.mem_bot] at hp
      subst hp
      simpa using isIntegral_zero)
    have h2 : IsIntegral ℤ (algebraMap ℚ E (2 : ℚ)⁻¹) := by simpa using this
    rw [isIntegral_algebraMap_iff (algebraMap ℚ E).injective] at h2
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    have h3 : (2 * n : ℤ) = 1 := by
      have : ((2 * n : ℤ) : ℚ) = (1 : ℤ) := by
        simp only [eq_intCast] at hn
        push_cast
        rw [hn]; norm_num
      exact_mod_cast this
    omega
  · obtain ⟨a, ha, ha1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := E) h0 hP
    apply ha1
    have hP0 : (P : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by simpa using h0
    have := key a fun p hp => by
      have hm : a * (p : E) ∈ (P : FractionalIdeal (𝓞 E)⁰ E)⁻¹ * P :=
        FractionalIdeal.mul_mem_mul ha (FractionalIdeal.mem_coeIdeal_of_mem _ hp)
      rw [inv_mul_cancel₀ hP0, FractionalIdeal.mem_one_iff] at hm
      obtain ⟨q, hq⟩ := hm
      rw [← hq]
      exact q.isIntegral_coe
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨a, this⟩, rfl⟩

theorem span_norm_eq_top (hE : Unr E) (hr : 1 ≤ r) {G : Matrix (Fin r) (Fin r) E}
    {Λ : Submodule (𝓞 E) (Fin r → E)} (h : SelfDualLat G Λ) :
    Ideal.span {n : 𝓞 (maximalRealSubfield E) | ∃ x ∈ Λ,
      algebraMap (maximalRealSubfield E) E n = herm G x x} = ⊤ := by
  by_contra hI
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨P, hP, hPm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) m
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1
      (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E))]; exact bot_le)
  have : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := hE
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm G x y) := fun x hx => (h.2.2.2.2 x).2 hx
  obtain ⟨t, ht⟩ := exists_sub_notMem (IsCMField.ringOfIntegersComplexConj E).toAlgHom (by
    by_contra hc
    push Not at hc
    apply IsCMField.complexConj_ne_one E
    ext x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    have hc' : ∀ s : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E s) = algebraMap (𝓞 E) E s :=
      fun s => congrArg (fun z : 𝓞 E => (z : E)) (hc s)
    simp [hc']) P hP.ne_top
  have hn : ∀ x (hx : x ∈ Λ), (⟨herm G x x, hint x hx x hx⟩ : 𝓞 E) ∈ P := by
    intro x hx
    have hfix := (IsCMField.complexConj_eq_self_iff E _).1 (herm_symm G h.1 x x)
    have hi : IsIntegral ℤ (⟨herm G x x, hfix⟩ : maximalRealSubfield E) :=
      (isIntegral_algebraMap_iff (algebraMap (maximalRealSubfield E) E).injective).1 (hint x hx x hx)
    have h1 : (⟨_, hi⟩ : 𝓞 (maximalRealSubfield E)) ∈ m := hIm (Ideal.subset_span ⟨x, hx, rfl⟩)
    rw [← hPm] at h1
    exact h1
  have htr : ∀ x (hx : x ∈ Λ) y (hy : y ∈ Λ),
      (⟨herm G x y, hint x hx y hy⟩ + ⟨herm G y x, hint y hy x hx⟩ : 𝓞 E) ∈ P := by
    intro x hx y hy
    have := P.sub_mem (P.sub_mem (hn _ (Λ.add_mem hx hy)) (hn x hx)) (hn y hy)
    convert this using 1
    apply RingOfIntegers.ext
    change herm G x y + herm G y x = herm G (x + y) (x + y) - herm G x x - herm G y y
    rw [herm_add_left, herm_add_right, herm_add_right]; ring
  refine exists_herm_notMem hr h P hP.ne_top fun x hx y hy => ⟨⟨herm G x y, hint x hx y hy⟩, ?_, rfl⟩
  have h1 := P.sub_mem (htr _ (Λ.smul_mem t hx) y hy)
    (P.mul_mem_left (IsCMField.ringOfIntegersComplexConj E t) (htr x hx y hy))
  refine (hP.isPrime.mem_or_mem ?_).resolve_left ht
  convert h1 using 1
  apply RingOfIntegers.ext
  change ((t : E) - IsCMField.complexConj E t) * herm G x y = herm G ((t : E) • x) y + herm G y ((t : E) • x)
    - IsCMField.complexConj E t * (herm G x y + herm G y x)
  rw [← herm_symm G h.1 ((t : E) • x) y, herm_smul_left, map_mul, herm_symm G h.1]
  ring

end Lattice

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem hermA_add_left (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → RA F E) :
    hermA c G (x + x') y = hermA c G x y + hermA c G x' y := by
  simp only [hermA, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hermA_add_right (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → RA F E) :
    hermA c G x (y + y') = hermA c G x y + hermA c G x y' := by
  simp only [hermA, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hermA_tmul (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (s t : FiniteAdeleRing (𝓞 F) F)
    (x y : Fin n → E) : hermA c G (fun i => s ⊗ₜ x i) (fun i => t ⊗ₜ y i)
      = (s * t) ⊗ₜ ∑ a, ∑ b, x a * G a b * c (y b) := by
  simp [hermA, Model.sg_tmul, TensorProduct.tmul_sum]

theorem mul_mem_adelicCompletionIntegral {a b : RA F E} (ha : a ∈ hat1 F {x : E | IsIntegral ℤ x})
    (hb : b ∈ hat1 F {x : E | IsIntegral ℤ x}) : a * b ∈ hat1 F {x : E | IsIntegral ℤ x} := by
  induction ha, hb using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨a, ha, s, hs, rfl⟩ := hx
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure ⟨a * b, fun v => mul_mem (ha v) (hb v), s * t, IsIntegral.mul hs ht, rfl⟩
  | zero_left x hx => rw [zero_mul]; exact AddSubgroup.zero_mem _
  | zero_right x hx => rw [mul_zero]; exact AddSubgroup.zero_mem _
  | add_left x y z _ _ _ h1 h2 => rw [add_mul]; exact AddSubgroup.add_mem _ h1 h2
  | add_right x y z _ _ _ h1 h2 => rw [mul_add]; exact AddSubgroup.add_mem _ h1 h2
  | neg_left x y _ _ h => rw [neg_mul]; exact AddSubgroup.neg_mem _ h
  | neg_right x y _ _ h => rw [mul_neg]; exact AddSubgroup.neg_mem _ h

theorem galoisAut_mem_adelicCompletionIntegral (c : E ≃ₐ[F] E) {a : RA F E} (ha : a ∈ hat1 F {x : E | IsIntegral ℤ x}) :
    sg _ c a ∈ hat1 F {x : E | IsIntegral ℤ x} := by
  induction ha using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, s, hs, rfl⟩ := hz
    rw [Model.sg_tmul]
    exact AddSubgroup.subset_closure ⟨a, ha, c s, IsIntegral.map (c : E →+* E).toIntAlgHom hs, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem smul_mem_hat (Λ : Submodule (𝓞 E) (Fin n → E)) {a : RA F E} {z : Fin n → RA F E}
    (ha : a ∈ hat1 F {x : E | IsIntegral ℤ x}) (hz : z ∈ hat F (Λ : Set (Fin n → E))) :
    a • z ∈ hat F (Λ : Set (Fin n → E)) := by
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨a, ha, s, hs, rfl⟩ := ha
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨b, hb, x, hx, rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨a * b, fun v => mul_mem (ha v) (hb v), s • x,
        Λ.smul_mem (⟨s, hs⟩ : 𝓞 E) hx, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  | zero => rw [zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_smul]; exact neg_mem hx

theorem adelicHermitianFormGalois_mem_integral (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E))
    (hL : ∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (∑ a, ∑ b, x a * G a b * c (y b))) {x y : Fin n → RA F E}
    (hx : x ∈ hat F L) (hy : y ∈ hat F L) : hermA c G x y ∈ hat1 F {x : E | IsIntegral ℤ x} := by
  induction hx, hy using AddSubgroup.closure_induction₂ with
  | mem x y hx hy =>
    obtain ⟨a, ha, s, hs, rfl⟩ := hx
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    rw [hermA_tmul]
    exact AddSubgroup.subset_closure ⟨a * b, fun v => mul_mem (ha v) (hb v), _, hL s hs t ht, rfl⟩
  | zero_left x hx => simp [hermA]
  | zero_right x hx => simp [hermA]
  | add_left x y z _ _ _ h1 h2 => rw [hermA_add_left]; exact AddSubgroup.add_mem _ h1 h2
  | add_right x y z _ _ _ h1 h2 => rw [hermA_add_right]; exact AddSubgroup.add_mem _ h1 h2
  | neg_left x y _ _ h => simpa [hermA] using h
  | neg_right x y _ _ h => simpa [hermA] using h

theorem exists_isKM_of_unit_norm (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ a b, c (G a b) = G b a) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (∑ a, ∑ b, x a * G a b * c (y b))) (M : ℕ)
    {e : Fin n → RA F E} (he : e ∈ hat F (Λ : Set (Fin n → E))) {b : RA F E}
    (hb : b ∈ hat1 F {x : E | IsIntegral ℤ x}) (hbe : b * hermA c G e e = 1) {k y : RA F E} (hk : IsTA c k)
    (hy : y ∈ hat1 F {x : E | IsIntegral ℤ x}) (hky : k - 1 = M • y) :
    ∃ g, IsKM c G (Λ : Set (Fin n → E)) M g ∧ g.det = k := by
  unfold IsTA at hk
  let w : Fin n → RA F E := fun a => ∑ j, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G a j) * sg _ c (e j)
  have hw : ∀ x, w ⬝ᵥ x = hermA c G x e := by
    intro x
    simp only [w, dotProduct, hermA, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  let g : Matrix (Fin n) (Fin n) (RA F E) := 1 + vecMulVec (((k - 1) * b) • e) w
  have hg : ∀ x, g *ᵥ x = x + ((k - 1) * b * hermA c G x e) • e := by
    intro x
    rw [← hw]
    funext i
    simp only [g, add_mulVec, one_mulVec, vecMulVec_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring
  have hdet : g.det = k := by
    simp only [g]
    rw [vecMulVec_eq (ι := Unit), det_one_add_replicateCol_mul_replicateRow, hw, Model.hermA_smul_left]
    linear_combination (k - 1) * hbe
  have hsb : sg _ c b = b := by
    have := congrArg (sg _ c) hbe
    rw [map_mul, map_one, Model.hermA_symm c hc G hG] at this
    linear_combination b * this - sg _ c b * hbe
  have hsk : sg _ c k - 1 = M • sg _ c y := by
    have := congrArg (sg _ c) hky
    rwa [map_sub, map_one, map_nsmul] at this
  refine ⟨g, ⟨⟨?_, fun x z => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩, hdet⟩
  · rw [hdet]
    exact IsUnit.of_mul_eq_one _ hk
  · rw [hg, hg]
    simp only [hermA_add_left, hermA_add_right, Model.hermA_smul_left, Model.hermA_smul_right, map_mul,
      map_sub, map_one, hsb, Model.hermA_symm c hc G hG]
    linear_combination (b * hermA c G x e * hermA c G e z) * hk
      + ((k - 1) * (sg _ c k - 1) * b * hermA c G x e * hermA c G e z) * hbe
  · refine ⟨(y * b * hermA c G x e) • e,
      smul_mem_hat Λ (mul_mem_adelicCompletionIntegral (mul_mem_adelicCompletionIntegral hy hb) (adelicHermitianFormGalois_mem_integral c G _ hL hx he)) he, ?_⟩
    rw [hg, hky, add_sub_cancel_left, smul_mul_assoc, smul_mul_assoc, smul_assoc]
  · refine ⟨x + ((sg _ c k - 1) * b * hermA c G x e) • e, add_mem hx (smul_mem_hat Λ (mul_mem_adelicCompletionIntegral
      (mul_mem_adelicCompletionIntegral ?_ hb) (adelicHermitianFormGalois_mem_integral c G _ hL hx he)) he), ?_⟩
    · rw [hsk]
      exact nsmul_mem (galoisAut_mem_adelicCompletionIntegral c hy) M
    · rw [hg, add_assoc, ← add_smul, hermA_add_left, Model.hermA_smul_left]
      have : (sg _ c k - 1) * b * hermA c G x e + (k - 1) * b *
          (hermA c G x e + (sg _ c k - 1) * b * hermA c G x e * hermA c G e e) = 0 := by
        linear_combination (b * hermA c G x e) * hk
          + ((k - 1) * (sg _ c k - 1) * b * hermA c G x e) * hbe
      rw [this, zero_smul, add_zero]

def incl : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+* FiniteAdeleRing (𝓞 F) F where
  toFun a := (⟨fun v => (a v : v.adicCompletion F), Filter.Eventually.of_forall fun v => (a v).2⟩ :
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => v.adicCompletionIntegers F) Filter.cofinite)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem incl_algebraMap (a : 𝓞 F) :
    incl (fun v : HeightOneSpectrum (𝓞 F) => algebraMap (𝓞 F) (v.adicCompletionIntegers F) a)
      = algebraMap F (FiniteAdeleRing (𝓞 F) F) a := by
  ext v
  rfl

theorem isUnit_of_notMem (v : HeightOneSpectrum (𝓞 F)) {m : 𝓞 F} (hm : m ∉ v.asIdeal) :
    IsUnit (algebraMap (𝓞 F) (v.adicCompletionIntegers F) m) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (m : F)
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hm] at h
  exact h

theorem exists_idem {ι T : Type} [Fintype T] [DecidableEq T] (O : ι → Type) [∀ v, CommRing (O v)]
    (f : T → ∀ v, O v) (hf : ∀ v, ∃ m, IsUnit (f m v)) :
    ∃ (ε : T → ∀ v, O v) (u : ∀ v, O v), (∀ m m', ε m * ε m' = if m = m' then ε m else 0) ∧
      u * ∑ m, ε m * f m = 1 := by
  choose i hi using hf
  choose u hu using fun v => (hi v).exists_left_inv
  refine ⟨fun m v => if i v = m then 1 else 0, u, fun m m' => ?_, ?_⟩
  · funext v
    by_cases h : m = m'
    · subst h
      by_cases h' : i v = m <;> simp [h']
    · by_cases h' : i v = m
      · subst h'
        simp [h]
      · simp [h, h']
  · funext v
    simpa [Finset.sum_apply] using hu v

theorem exists_idem_adele {T : Type} [Fintype T] [DecidableEq T] (N : T → 𝓞 F)
    (hN : ∀ v : HeightOneSpectrum (𝓞 F), ∃ m, N m ∉ v.asIdeal) :
    ∃ (ε : T → FiniteAdeleRing (𝓞 F) F) (u : FiniteAdeleRing (𝓞 F) F),
      (∀ m v, ε m v ∈ v.adicCompletionIntegers F) ∧ (∀ v, u v ∈ v.adicCompletionIntegers F) ∧
      (∀ m m', ε m * ε m' = if m = m' then ε m else 0) ∧ u * ∑ m, ε m * algebraMap F _ (N m : F) = 1 := by
  obtain ⟨ε, u, hε, hsum⟩ := exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
    (fun m v => algebraMap (𝓞 F) (v.adicCompletionIntegers F) (N m))
    fun v => (hN v).imp fun m hm => isUnit_of_notMem v hm
  refine ⟨fun m => incl (ε m), incl u, fun m v => (ε m v).2, fun v => (u v).2, fun m m' => ?_, ?_⟩
  · rw [← map_mul, hε]
    split_ifs
    · rfl
    · exact map_zero _
  · have hsum' := congrArg incl hsum
    rw [map_mul, map_sum, map_one] at hsum'
    simp only [map_mul, incl_algebraMap] at hsum'
    exact hsum'

theorem hermA_sum_idem (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) {T : Type} [Fintype T] [DecidableEq T]
    (ε : T → FiniteAdeleRing (𝓞 F) F) (hε : ∀ m m', ε m * ε m' = if m = m' then ε m else 0)
    (x : T → Fin n → E) (N : T → F) (hx : ∀ m, algebraMap F E (N m) = ∑ a, ∑ b, x m a * G a b * c (x m b)) :
    hermA c G (∑ m, fun j => ε m ⊗ₜ x m j) (∑ m, fun j => ε m ⊗ₜ x m j)
      = (∑ m, ε m * algebraMap F _ (N m)) ⊗ₜ 1 := by
  have hl : ∀ (f : T → Fin n → RA F E) z, hermA c G (∑ m, f m) z = ∑ m, hermA c G (f m) z := fun f z =>
    map_sum (AddMonoidHom.mk' (fun x => hermA c G x z) fun a b => hermA_add_left c G a b z) _ _
  have hr : ∀ (f : T → Fin n → RA F E) z, hermA c G z (∑ m, f m) = ∑ m, hermA c G z (f m) := fun f z =>
    map_sum (AddMonoidHom.mk' (fun x => hermA c G z x) fun a b => hermA_add_right c G z a b) _ _
  rw [hl, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hr, Finset.sum_eq_single m]
  · rw [hermA_tmul, hε, if_pos rfl, ← hx, mul_comm, ← Algebra.smul_def,
      TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  · intro m' _ hm
    rw [hermA_tmul, hε, if_neg hm.symm, TensorProduct.zero_tmul]
  · simp

theorem exists_unit_norm (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E))
    (hL : Ideal.span {m : 𝓞 F | ∃ x ∈ L, algebraMap F E m = ∑ a, ∑ b, x a * G a b * c (x b)} = ⊤) :
    ∃ e ∈ hat F L, ∃ b ∈ hat1 F {x : E | IsIntegral ℤ x}, b * hermA c G e e = 1 := by
  classical
  obtain ⟨T, hT, h1⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).1 hL)
  have hx : ∀ m : T, ∃ x ∈ L, algebraMap F E (m : 𝓞 F) = ∑ a, ∑ b, x a * G a b * c (x b) := fun m => hT m.2
  choose x hxL hx using hx
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), ∃ m : T, (m : 𝓞 F) ∉ v.asIdeal := by
    intro v
    by_contra hcon
    push Not at hcon
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (Submodule.span_le.2 (fun m hm => hcon ⟨m, hm⟩) h1))
  obtain ⟨ε, u, hε, hu, hεε, hsum⟩ := exists_idem_adele (fun m : T => (m : 𝓞 F)) hv
  refine ⟨∑ m : T, fun j => ε m ⊗ₜ x m j,
    sum_mem fun m _ => AddSubgroup.subset_closure ⟨ε m, hε m, x m, hxL m, rfl⟩, u ⊗ₜ 1,
    AddSubgroup.subset_closure ⟨u, hu, 1, isIntegral_one, rfl⟩, ?_⟩
  rw [hermA_sum_idem c G ε hεε x (fun m => ((m : 𝓞 F) : F)) hx, Algebra.TensorProduct.tmul_mul_tmul, hsum,
    mul_one, Algebra.TensorProduct.one_def]

end Adelic

theorem exists_isKM_det_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ r → 1 ≤ M → SelfDualLat G Λ → ∀ k : RA (maximalRealSubfield E) E, IsTA (IsCMField.complexConj E) k → (∃ y ∈ hat1 (maximalRealSubfield E) {x : E | IsIntegral ℤ x}, k - 1 = M • y) → ∃ g, IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M g ∧ g.det = k := by
  intro E _ _ _ hE r M G Λ hr _ h k hk ⟨y, hy, hky⟩
  obtain ⟨e, he, b, hb, hbe⟩ := exists_unit_norm (IsCMField.complexConj E) G (Λ : Set (Fin r → E))
    (span_norm_eq_top hE hr h)
  exact exists_isKM_of_unit_norm _ (IsCMField.complexConj_apply_apply E) G h.1 Λ
    (fun x hx => (h.2.2.2.2 x).2 hx) M he hb hbe hk hy hky

end GlobalTheory.UCls.Det
