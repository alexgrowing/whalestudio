import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host

namespace GlobalTheory.HeckeGal.Model

variable (E : Type) [Field E] [NumberField E]

def absPow (s : ℝ) : HChar E :=
  ⟨GlobalTheory.Mem.Chr.CharModel.absHom E s, (GlobalTheory.Mem.Chr.CharModel.absChar E s).2⟩

theorem absPow_isAbsPow (s : ℝ) : (absPow E s).IsAbsPow s :=
  GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow (F := E) s

theorem prod_emb_real (k : E) : ∃ q : ℚ, ∏ φ : E →+* ℂ, φ k = (q : ℂ) := by
  refine ⟨Algebra.norm ℚ k, ?_⟩
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ k
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ k)
    (fun σ : E →ₐ[ℚ] ℂ => σ k) (fun _ => rfl)] at h
  rw [← h]; simp

theorem absPow_two_isAlg : (absPow E 2).IsAlg (fun _ => 2) := by
  intro k
  rw [(absPow_isAbsPow E 2).2.2 k]
  obtain ⟨q, hq⟩ := prod_emb_real E (k : E)
  have h1 : ∏ φ : E →+* ℂ, ((‖φ (k : E)‖ : ℝ) : ℂ) = ((|(q : ℝ)| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod, ← norm_prod, hq]
    congr 1
    exact Complex.norm_ratCast q
  have e2 : ((2 : ℝ) : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
  simp only [e2, Complex.cpow_natCast, zpow_ofNat]
  rw [Finset.prod_pow, Finset.prod_pow, h1, hq, ← Complex.ofReal_pow, sq_abs]
  push_cast; rfl

theorem absPow_two_isAlgPos : IsAlgPos (absPow E 2) (fun _ => 2) := isAlgPos_of_isAlg (absPow_two_isAlg E)

theorem absPow_one_isAlgPos_rat : IsAlgPos (absPow ℚ 1) (fun _ => 1) := by
  intro k hk
  rw [(absPow_isAbsPow ℚ 1).2.2 k]
  refine Finset.prod_congr rfl fun φ _ => ?_
  have h := hk (Rat.castHom ℝ)
  simp only [eq_ratCast] at h
  simp only [eq_ratCast, Complex.ofReal_one, Complex.cpow_one, zpow_one, Complex.norm_ratCast, abs_of_pos h]
  simp

theorem absPow_one_not_isAlg_rat : ¬ (absPow ℚ 1).IsAlg (fun _ => 1) := by
  intro h
  have h1 := h (-1)
  rw [(absPow_isAbsPow ℚ 1).2.2] at h1
  simp at h1
  rw [Embeddings.card, Module.finrank_self] at h1
  norm_num at h1

theorem frob_abs {Ω : Type} [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {art : Ideles E →* Gab E Ω}
    (ha : IsGlobalArtin art) {ι : Qbar l ≃+* ℂ} {m : ℕ} {n : (E →+* ℂ) → ℤ} {r : G E Ω →* (Qbar l)ˣ}
    (h : IsLAdicOf art ι (absPow E m) n r) {v : HeightOneSpectrum (𝓞 E)} (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal)
    {A : ValuationSubring Ω} (hA : IsPlaceOver A v) {σ : G E Ω} (hσ : IsFrob (F := E) A (normV v) σ) :
    ((r σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) ^ m := by
  rw [h.frob_unr ha (Or.inl hv) ((absPow_isAbsPow E m).1 v) hA hσ, (absPow_isAbsPow E m).2.1 v,
    Complex.cpow_neg, Complex.ofReal_natCast, Complex.cpow_natCast, map_inv₀, inv_inv, map_pow, map_natCast]
  rfl

theorem infPow_diag_rat (n : (ℚ →+* ℂ) → ℤ) (k : ℚˣ) :
    infPow n (diagUnits ℚ k) = ((k : ℚ) : ℂ) ^ n (Rat.castHom ℂ) := by
  unfold infPow
  rw [Fintype.prod_unique]
  set w : InfinitePlace ℚ := default
  have hs : Subsingleton {i : w.Completion →+* ℂ // Continuous i} := by
    refine ⟨fun a b => Subtype.ext (DFunLike.coe_injective ?_)⟩
    have hd : DenseRange (algebraMap ℚ w.Completion) := by
      refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
      rintro _ ⟨a, rfl⟩
      exact ⟨WithAbs.equiv w.1 a, rfl⟩
    refine hd.equalizer a.2 b.2 ?_
    funext x
    exact DFunLike.congr_fun (Subsingleton.elim (a.1.comp (algebraMap ℚ _)) (b.1.comp (algebraMap ℚ _))) x
  let i0 : {i : w.Completion →+* ℂ // Continuous i} :=
    ⟨InfinitePlace.Completion.extensionEmbedding w, (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous⟩
  rw [finprod_eq_single _ i0 fun j hj => absurd (Subsingleton.elim j i0) hj,
    Subsingleton.elim (i0.1.comp (algebraMap ℚ w.Completion)) (Rat.castHom ℂ)]
  congr 1
  exact eq_ratCast (i0.1.comp (algebraMap ℚ w.Completion)) (k : ℚ)

theorem lPow_diag_rat {l : ℕ} [hl : Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : (ℚ →+* ℂ) → ℤ) (k : ℚˣ) :
    lPow ι n (diagUnits ℚ k) = ((k : ℚ) : Qbar l) ^ n (Rat.castHom ℂ) := by
  unfold lPow
  let p : Nat.Primes := ⟨l, hl.out⟩
  let v : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p
  rw [finprod_eq_single _ v]
  · have hs : Subsingleton {j : v.adicCompletion ℚ →+* Qbar l // Continuous j} := by
      refine ⟨fun a b => Subtype.ext (DFunLike.coe_injective ?_)⟩
      refine (HeightOneSpectrum.denseRange_algebraMap ℚ v).equalizer a.2 b.2 ?_
      funext x
      exact DFunLike.congr_fun (Subsingleton.elim (a.1.comp (algebraMap ℚ _)) (b.1.comp (algebraMap ℚ _))) x
    let e : ℚ_[l] ≃A[ℚ] v.adicCompletion ℚ := Padic.adicCompletionEquiv (𝓞 ℚ) p
    let j0 : {j : v.adicCompletion ℚ →+* Qbar l // Continuous j} :=
      ⟨(algebraMap ℚ_[l] (Qbar l)).comp e.symm.toAlgEquiv.toRingEquiv.toRingHom,
        (continuous_algebraMap ℚ_[l] (Qbar l)).comp e.symm.continuous⟩
    unfold locPow
    rw [finprod_eq_single _ j0 fun j hj => absurd (Subsingleton.elim j j0) hj,
      Subsingleton.elim ((ι.toRingHom.comp j0.1).comp (algebraMap ℚ (v.adicCompletion ℚ))) (Rat.castHom ℂ)]
    congr 1
    exact eq_ratCast (j0.1.comp (algebraMap ℚ (v.adicCompletion ℚ))) (k : ℚ)
  · intro u hu
    refine locPow_of_notMem ι n (fun hm => hu ?_) _
    have h1 : Rat.HeightOneSpectrum.natGenerator u ∣ l := by
      rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))]
      exact Ideal.mem_map_of_mem _ hm
    have h2 := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator u) hl.out).1 h1
    rw [Equiv.eq_symm_apply]
    exact Subtype.ext h2

theorem formula_diag_rat {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (χ : HChar ℚ) (n : (ℚ →+* ℂ) → ℤ) (k : ℚˣ) :
    ι.symm (((χ.1 (diagUnits ℚ k) : ℂˣ) : ℂ) * (infPow n (diagUnits ℚ k))⁻¹) * lPow ι n (diagUnits ℚ k) = 1 := by
  rw [χ.2.2 k, infPow_diag_rat, lPow_diag_rat, Units.val_one, one_mul, map_inv₀, map_zpow₀, map_ratCast]
  exact inv_mul_cancel₀ (zpow_ne_zero _ (by exact_mod_cast k.ne_zero))

theorem isLAdicOf_one {Ω : Type} [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] (art : Ideles E →* Gab E Ω)
    (ι : Qbar l ≃+* ℂ) : IsLAdicOf art ι (1 : HChar E) 0 1 := by
  intro x σ _
  rw [infPow_zero, lPow_zero]
  simp

end GlobalTheory.HeckeGal.Model

end
