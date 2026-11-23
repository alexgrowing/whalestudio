import Mathlib
import Formalism.PeriodIntegrals.SplitIntLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitPrimeIntegers.EmbMemOfIsIntegral

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct

noncomputable section

namespace PI.SplitIntLoc.Proof

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} (spl : E ⊗[F] (v.adicCompletion F) ≃+* (v.adicCompletion F) × (v.adicCompletion F))

lemma spl_tmul (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (e : E) (a : (v.adicCompletion F)) :
    spl (e ⊗ₜ[F] a) =
      (emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) e * a, emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) e * a) := by
  have h : e ⊗ₜ[F] a = (e ⊗ₜ[F] (1 : (v.adicCompletion F))) * ((1 : E) ⊗ₜ[F] a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, spl_tmul_one, hspl]
  rfl

lemma exists_small : ∃ ϖ : (v.adicCompletion F), ϖ ≠ 0 ∧ Valued.v ϖ < 1 := by
  obtain ⟨π, hπ0, hπ⟩ := exists_unif v
  exact ⟨_, (map_ne_zero_iff _ (algebraMap F (v.adicCompletion F)).injective).2 hπ0, hπ⟩

lemma approx (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (z : E ⊗[F] (v.adicCompletion F)) :
    ∃ y : E, Valued.v ((spl z).1 - emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y) < 1 ∧
      Valued.v ((spl z).2 - emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y) < 1 := by
  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_small (v := v)
  have key : ∀ w : (v.adicCompletion F), w ∈ (v.adicCompletionIntegers F) → Valued.v (ϖ * w) < 1 := fun w hw =>
    have hw' : Valued.v w ≤ 1 := hw
    calc Valued.v (ϖ * w) = Valued.v ϖ * Valued.v w := map_mul _ _ _
      _ ≤ Valued.v ϖ * 1 := by gcongr
      _ = Valued.v ϖ := mul_one _
      _ < 1 := hϖ
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp, by simp⟩
  | tmul e a =>
    let U : Set (v.adicCompletion F) :=
      (fun x => ϖ⁻¹ * emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) e * (a - x)) ⁻¹' ((v.adicCompletionIntegers F) : Set (v.adicCompletion F)) ∩
      (fun x => ϖ⁻¹ * emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) e * (a - x)) ⁻¹' ((v.adicCompletionIntegers F) : Set (v.adicCompletion F))
    have hU : IsOpen U := by
      refine IsOpen.inter ?_ ?_ <;>
      exact (Valued.isOpen_integer (v.adicCompletion F)).preimage
        (continuous_const.mul (continuous_const.sub continuous_id))
    have hU' : U.Nonempty := ⟨a, by
      simp only [U, Set.mem_inter_iff, Set.mem_preimage, sub_self, mul_zero, SetLike.mem_coe]
      exact ⟨zero_mem _, zero_mem _⟩⟩
    obtain ⟨f, hf⟩ := (denseRange_algebraMap F v).exists_mem_open hU hU'
    have hsmall : ∀ c : (v.adicCompletion F), ϖ⁻¹ * c * (a - algebraMap F (v.adicCompletion F) f) ∈ (v.adicCompletionIntegers F) →
        Valued.v (c * a - algebraMap F (v.adicCompletion F) f * c) < 1 := fun c hc => by
      have h : c * a - algebraMap F (v.adicCompletion F) f * c = ϖ * (ϖ⁻¹ * c * (a - algebraMap F (v.adicCompletion F) f)) := by
        rw [show ϖ * (ϖ⁻¹ * c * (a - algebraMap F (v.adicCompletion F) f)) =
          (ϖ * ϖ⁻¹) * (c * (a - algebraMap F (v.adicCompletion F) f)) by ring, mul_inv_cancel₀ hϖ0, one_mul]
        ring
      rw [h]
      exact key _ hc
    refine ⟨algebraMap F E f * e, ?_, ?_⟩
    · rw [spl_tmul spl hspl, map_mul, emb_algebraMap spl hspl _ (fun _ => rfl)]
      exact hsmall _ hf.1
    · rw [spl_tmul spl hspl, map_mul, emb_algebraMap spl hspl _ (fun _ => rfl)]
      exact hsmall _ hf.2
  | add x y hx hy =>
    obtain ⟨y1, h1, h1'⟩ := hx
    obtain ⟨y2, h2, h2'⟩ := hy
    refine ⟨y1 + y2, ?_, ?_⟩
    · rw [map_add, map_add, Prod.fst_add,
        show (spl x).1 + (spl y).1 - (emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y1 + emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y2)
          = ((spl x).1 - emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y1) + ((spl y).1 - emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y2)
          by ring]
      exact Valuation.map_add_lt _ h1 h2
    · rw [map_add, map_add, Prod.snd_add,
        show (spl x).2 + (spl y).2 - (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y1 + emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y2)
          = ((spl x).2 - emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y1) + ((spl y).2 - emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y2)
          by ring]
      exact Valuation.map_add_lt _ h1' h2'

lemma exists_sep (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    ∃ y : E, 1 < Valued.v (emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y) ∧
      Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y) < 1 := by
  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_small (v := v)
  obtain ⟨y, h1, h2⟩ := approx spl hspl (spl.symm (ϖ⁻¹, 0))
  rw [RingEquiv.apply_symm_apply] at h1 h2
  dsimp only at h1 h2
  have hinv : 1 < Valued.v ϖ⁻¹ := by
    by_contra h
    rw [not_lt] at h
    have h3 : Valued.v ϖ * Valued.v ϖ⁻¹ < 1 :=
      calc Valued.v ϖ * Valued.v ϖ⁻¹ ≤ Valued.v ϖ * 1 := by gcongr
        _ = Valued.v ϖ := mul_one _
        _ < 1 := hϖ
    rw [← map_mul, mul_inv_cancel₀ hϖ0, map_one] at h3
    exact lt_irrefl _ h3
  refine ⟨y, ?_, ?_⟩
  · have hlt : Valued.v (emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y - ϖ⁻¹) < Valued.v ϖ⁻¹ := by
      rw [Valuation.map_sub_swap]
      exact h1.trans hinv
    rw [Valuation.map_eq_of_sub_lt _ hlt]
    exact hinv
  · rw [zero_sub, Valuation.map_neg] at h2
    exact h2

lemma emb_mem_of_mul (p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F)) (a s : 𝓞 E) (hs : s ∉ P spl p) (z : E)
    (hz : z * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a) : emb spl p z ∈ (v.adicCompletionIntegers F) := by
  have hu : IsUnit (phi spl p s) := by
    by_contra h
    apply hs
    show phi spl p s ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)
    rw [IsLocalRing.mem_maximalIdeal]
    exact h
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h2 : (phi spl p s : (v.adicCompletion F)) * (w : (v.adicCompletion F)) = 1 := congrArg Subtype.val hw
  have h3 : emb spl p z = (phi spl p a : (v.adicCompletion F)) * (w : (v.adicCompletion F)) := by
    rw [coe_phi, ← hz, map_mul, ← coe_phi, mul_assoc, h2, mul_one]
  rw [h3]
  exact (phi spl p a * w).2

def Dloc (Q : Ideal (𝓞 E)) [Q.IsPrime] : Subalgebra (𝓞 E) E :=
  Localization.subalgebra E Q.primeCompl Q.primeCompl_le_nonZeroDivisors

instance (Q : Ideal (𝓞 E)) [Q.IsPrime] : IsLocalization.AtPrime (Dloc Q) Q :=
  inferInstanceAs (IsLocalization Q.primeCompl
    (Localization.subalgebra E Q.primeCompl Q.primeCompl_le_nonZeroDivisors))

instance (Q : Ideal (𝓞 E)) [Q.IsPrime] : IsFractionRing (Dloc Q) E :=
  inferInstanceAs (IsFractionRing
    (Localization.subalgebra E Q.primeCompl Q.primeCompl_le_nonZeroDivisors) E)

lemma prime_fst_ne_prime_snd (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) ≠ P spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) := by
  intro hPP
  obtain ⟨y, hy1, hy2⟩ := exists_sep spl hspl
  have hQ0 : P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) ≠ ⊥ := prime_ne_bot spl hspl _ (fun _ => rfl)
  have : IsDiscreteValuationRing (Dloc (P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)))) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) hQ0 _
  have hloc : ∀ p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F), P spl p = P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) → ∀ z : E,
      IsLocalization.IsInteger (Dloc (P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)))) z → emb spl p z ∈ (v.adicCompletionIntegers F) := by
    rintro p hp z ⟨d, hd⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F))).primeCompl d
    have hs : (s : 𝓞 E) ∉ P spl p := by rw [hp]; exact s.2
    have hspec := congrArg (algebraMap (Dloc (P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)))) E)
      (IsLocalization.mk'_spec (Dloc (P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)))) a s)
    rw [map_mul, hd, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hspec
    exact emb_mem_of_mul spl p a s hs z hspec
  rcases ValuationRing.isInteger_or_isInteger (Dloc (P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)))) y with h | h
  · have h' : Valued.v (emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y) ≤ 1 := hloc _ rfl y h
    exact absurd h' (not_le.2 hy1)
  · have h' : Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y⁻¹) ≤ 1 := hloc _ hPP.symm y⁻¹ h
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero, Valuation.map_zero] at hy1
      exact absurd hy1 (not_lt.2 zero_le)
    have hu0 : emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y ≠ 0 :=
      (map_ne_zero_iff _ (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F))).injective).2 hy0
    rw [map_inv₀] at h'
    have h3 : Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y) * Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y)⁻¹ < 1 :=
      calc Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y) * Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y)⁻¹ ≤ Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y) * 1 := by gcongr
        _ = Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y) := mul_one _
        _ < 1 := hy2
    rw [← map_mul, mul_inv_cancel₀ hu0, map_one] at h3
    exact lt_irrefl _ h3

lemma exists_unit_diff (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    ∃ b : 𝓞 E, IsUnit (phi spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) b - phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b) := by
  have h1 : (P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F))).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (prime_ne_bot spl hspl _ (fun _ => rfl))
  have h2 : (P spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F))).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (prime_ne_bot spl hspl _ (fun _ => rfl))
  have htop := Ideal.IsMaximal.coprime_of_ne h1 h2 (prime_fst_ne_prime_snd spl hspl)
  have h1mem : (1 : 𝓞 E) ∈ P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) ⊔ P spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1mem
  refine ⟨b, ?_⟩
  have hsum := congrArg (phi spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F))) hab
  rw [map_add, map_one] at hsum
  have heq : phi spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) b - phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b =
      1 - (phi spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) a + phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b) := by
    rw [← hsum]; ring
  rw [heq]
  apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
  rw [← IsLocalRing.mem_maximalIdeal]
  have ha' : phi spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := ha
  have hb' : phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := hb
  exact Ideal.add_mem _ ha' hb'

theorem sup_dir (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (x : E ⊗[F] (v.adicCompletion F))
    (h1 : (spl x).1 ∈ (v.adicCompletionIntegers F)) (h2 : (spl x).2 ∈ (v.adicCompletionIntegers F)) :
    x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) ((v.adicCompletionIntegers F)).toSubring := by
  obtain ⟨b, hb⟩ := exists_unit_diff spl hspl
  obtain ⟨u, hu⟩ := hb.exists_right_inv
  have hu' : ((phi spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) b : (v.adicCompletion F)) - (phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b : (v.adicCompletion F))) *
      (u : (v.adicCompletion F)) = 1 := congrArg Subtype.val hu
  have hE : ∀ e : 𝓞 E, (algebraMap (𝓞 E) E e) ⊗ₜ[F] (1 : (v.adicCompletion F)) ∈
      tensInt (F := F) (v.adicCompletion F) (intOE E) ((v.adicCompletionIntegers F)).toSubring := fun e =>
    Subring.subset_closure (Or.inl ⟨⟨_, RingHom.mem_range.2 ⟨e, rfl⟩⟩, rfl⟩)
  have hK : ∀ c : (v.adicCompletionIntegers F), (1 : E) ⊗ₜ[F] (c : (v.adicCompletion F)) ∈
      tensInt (F := F) (v.adicCompletion F) (intOE E) ((v.adicCompletionIntegers F)).toSubring := fun c =>
    Subring.subset_closure (Or.inr ⟨⟨c, c.2⟩, rfl⟩)
  obtain ⟨w, hw_def⟩ : ∃ w : E ⊗[F] (v.adicCompletion F), w = (algebraMap (𝓞 E) E b ⊗ₜ[F] (1 : (v.adicCompletion F)) -
      (1 : E) ⊗ₜ[F] (phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b : (v.adicCompletion F))) * ((1 : E) ⊗ₜ[F] (u : (v.adicCompletion F))) := ⟨_, rfl⟩
  have hw : w ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) ((v.adicCompletionIntegers F)).toSubring := by
    rw [hw_def]
    exact Subring.mul_mem _ (Subring.sub_mem _ (hE b) (hK _)) (hK u)
  have hsw : spl w = (1, 0) := by
    rw [hw_def, map_mul, map_sub, spl_tmul_one, hspl, hspl]
    refine Prod.ext ?_ ?_
    · exact hu'
    · show ((phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b : (v.adicCompletion F)) - (phi spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) b : (v.adicCompletion F))) *
        (u : (v.adicCompletion F)) = 0
      rw [sub_self, zero_mul]
  have hx' : spl x = spl ((1 : E) ⊗ₜ[F] (((⟨_, h2⟩ : (v.adicCompletionIntegers F))) : (v.adicCompletion F)) +
      w * ((1 : E) ⊗ₜ[F] ((((⟨_, h1⟩ : (v.adicCompletionIntegers F)) - ⟨_, h2⟩ : (v.adicCompletionIntegers F))) : (v.adicCompletion F)))) := by
    rw [map_add, map_mul, hsw, hspl, hspl]
    refine Prod.ext ?_ ?_
    · show (spl x).1 = (spl x).2 + 1 * ((spl x).1 - (spl x).2)
      ring
    · show (spl x).2 = (spl x).2 + 0 * ((spl x).1 - (spl x).2)
      ring
  rw [spl.injective hx']
  exact Subring.add_mem _ (hK _) (Subring.mul_mem _ hw (hK _))

theorem main : PI.SplitIntLoc := by
  intro F E _ _ _ _ _ v spl hspl x
  exact ⟨fun hx => sub_dir spl hspl x hx, fun h => sup_dir spl hspl x h.1 h.2⟩

end PI.SplitIntLoc.Proof
