import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ShapeDegreeParity
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TeichmullerFactorisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TauPlBijective
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.InertCompare Classical

namespace GlobalTheory.CompletedBasis

section General

variable {l : ℕ} [Fact l.Prime]

theorem isCompact_closure_range {A V : Type} [AddCommGroup A] [Module.Finite ℤ A] [NormedAddCommGroup V]
    [NormedSpace ℚ_[l] V] (f : A →+ V) : IsCompact (closure (Set.range f)) := by
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := A)
  let g : (Fin n → ℤ_[l]) → V := fun c => ∑ i, ((c i : ℤ_[l]) : ℚ_[l]) • f (b i)
  have hg : Continuous g := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_subtype_val.comp (continuous_apply i)).smul continuous_const
  have hc : IsCompact (Set.range g) := isCompact_range hg
  refine hc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hc.isClosed)
  rintro _ ⟨a, rfl⟩
  have ha : a ∈ Submodule.span ℤ (Set.range b) := hb ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 ha
  refine ⟨fun i => (c i : ℤ_[l]), ?_⟩
  simp only [g, map_sum, map_zsmul, PadicInt.coe_intCast, Int.cast_smul_eq_zsmul]

variable {K : Type} [Field K] [NumberField K] (ρ : K →+* ℂ_[l])

def intClosure : Subring ℂ_[l] := (ρ.comp (algebraMap (𝓞 K) K)).range.topologicalClosure

theorem coe_intClosure : (intClosure ρ : Set ℂ_[l]) = closure (Set.range fun a : 𝓞 K => ρ (a : K)) := rfl

theorem isCompact_intClosure : IsCompact (intClosure ρ : Set ℂ_[l]) :=
  isCompact_closure_range (l := l) (ρ.comp (algebraMap (𝓞 K) K)).toAddMonoidHom

theorem mem_intClosure (a : 𝓞 K) : ρ (a : K) ∈ intClosure ρ := subset_closure ⟨a, rfl⟩

theorem norm_le_one_of_mem {x : ℂ_[l]} (hx : x ∈ intClosure ρ) : ‖x‖ ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨C, hC⟩ := (isCompact_intClosure ρ).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have := hC _ ((intClosure ρ).pow_mem hx n)
  rw [norm_pow] at this
  exact absurd hn (not_lt.2 this)

def primeOf : Ideal (𝓞 K) where
  carrier := {a | ‖ρ (a : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    have : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := rfl
    rw [this, map_add]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    have : ((c * a : 𝓞 K) : K) = (c : K) * (a : K) := rfl
    rw [this, map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem ρ (mem_intClosure ρ c))) ha

theorem mem_primeOf {a : 𝓞 K} : a ∈ primeOf ρ ↔ ‖ρ (a : K)‖ < 1 := Iff.rfl

theorem primeOf_isPrime : (primeOf ρ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_primeOf]; simp
  · intro a b h
    rw [mem_primeOf] at h
    have e : ((a * b : 𝓞 K) : K) = (a : K) * (b : K) := rfl
    rw [e, map_mul, norm_mul] at h
    by_contra hn
    simp only [mem_primeOf, not_or, not_lt] at hn
    nlinarith [hn.1, hn.2]

theorem primeOf_ne_bot : primeOf ρ ≠ ⊥ := by
  intro h
  have h1 : ((l : ℕ) : 𝓞 K) ∈ primeOf ρ := by
    rw [mem_primeOf]
    have e : (((l : ℕ) : 𝓞 K) : K) = (l : K) := rfl
    rw [e, map_natCast]
    have : ((l : ℕ) : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  rw [h, Ideal.mem_bot] at h1
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h1)

theorem inv_mem_of_not_mem {b : 𝓞 K} (hb : b ∉ primeOf ρ) : (ρ (b : K))⁻¹ ∈ intClosure ρ := by
  have hm : (primeOf ρ).IsMaximal := (primeOf_isPrime ρ).isMaximal (primeOf_ne_bot ρ)
  obtain ⟨y, p, hp, h⟩ := hm.exists_inv hb
  have hp' : ‖ρ (p : K)‖ < 1 := hp
  have hs := hasSum_geometric_of_norm_lt_one hp'
  have h1 : (1 - ρ (p : K))⁻¹ ∈ intClosure ρ := by
    refine (isCompact_intClosure ρ).isClosed.mem_of_tendsto hs (Filter.Eventually.of_forall fun s => ?_)
    exact (intClosure ρ).sum_mem fun i _ => (intClosure ρ).pow_mem (mem_intClosure ρ p) i
  have h2 : ρ (y : K) * ρ (b : K) = 1 - ρ (p : K) := by
    have := congrArg (fun a : 𝓞 K => ρ (a : K)) h
    have e : ((y * b + p : 𝓞 K) : K) = (y : K) * (b : K) + (p : K) := rfl
    simp only [e, map_add, map_mul] at this
    have e1 : ((1 : 𝓞 K) : K) = 1 := rfl
    rw [e1, map_one] at this
    linear_combination this
  have h3 : 1 - ρ (p : K) ≠ 0 := by
    intro h0
    have : ρ (p : K) = 1 := by linear_combination -h0
    rw [this] at hp'
    simp at hp'
  have h4 : ρ (b : K) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    exact h3 h2.symm
  have : (ρ (b : K))⁻¹ = ρ (y : K) * (1 - ρ (p : K))⁻¹ := by
    field_simp
    linear_combination -h2
  rw [this]
  exact (intClosure ρ).mul_mem (mem_intClosure ρ y) h1

theorem mem_of_norm_le_one {k : K} (hk : ‖ρ k‖ ≤ 1) : ρ k ∈ intClosure ρ := by
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨primeOf ρ, primeOf_isPrime ρ, primeOf_ne_bot ρ⟩
  have key : ∀ n d : 𝓞 K, d ∉ primeOf ρ → k * (d : K) = (n : K) → ρ k ∈ intClosure ρ := by
    intro n d hd h
    have hd0 : ρ (d : K) ≠ 0 := by
      intro h0
      apply hd
      rw [mem_primeOf, h0]; simp
    have : ρ k = ρ (n : K) * (ρ (d : K))⁻¹ := by
      rw [← h, map_mul]; field_simp
    rw [this]
    exact (intClosure ρ).mul_mem (mem_intClosure ρ n) (inv_mem_of_not_mem ρ hd)
  obtain ⟨n, d, h | h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq k
  · exact key n d d.2 h
  · refine key d n (fun hn => d.2 ?_) h
    change ‖ρ ((d : 𝓞 K) : K)‖ < 1
    have h' : k * (n : K) = ((d : 𝓞 K) : K) := h
    rw [← h', map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hk) hn

theorem div_mem {x y : ℂ_[l]} (hx : x ∈ intClosure ρ) (hy : y ∈ intClosure ρ) (h : ‖x / y‖ ≤ 1) :
    x / y ∈ intClosure ρ := by
  have hle : ∀ z ∈ intClosure ρ, z ∈ ρ.fieldRange.topologicalClosure := by
    intro z hz
    refine closure_mono ?_ hz
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  have h1 : x / y ∈ closure (ρ.fieldRange : Set ℂ_[l]) :=
    ρ.fieldRange.topologicalClosure.div_mem (hle x hx) (hle y hy)
  have ho : IsOpen (Metric.closedBall (0 : ℂ_[l]) 1) := IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have h2 := ho.inter_closure ⟨mem_closedBall_zero_iff.2 h, h1⟩
  refine closure_minimal ?_ (isCompact_intClosure ρ).isClosed h2
  rintro _ ⟨hb, k, rfl⟩
  exact mem_of_norm_le_one ρ (mem_closedBall_zero_iff.1 hb)

instance valuationRing_intClosure : ValuationRing (intClosure ρ) := by
  have aux : ∀ x y : intClosure ρ, ‖(x : ℂ_[l])‖ ≤ ‖(y : ℂ_[l])‖ → ∃ c, y * c = x := by
    intro x y h
    by_cases hy : (y : ℂ_[l]) = 0
    · refine ⟨0, Subtype.ext ?_⟩
      rw [hy, norm_zero, norm_le_zero_iff] at h
      simp [h]
    · refine ⟨⟨x / y, div_mem ρ x.2 y.2 ?_⟩, Subtype.ext ?_⟩
      · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · change (y : ℂ_[l]) * (x / y) = x
        field_simp
  refine { cond' := fun a b => ?_ }
  rcases le_total ‖(a : ℂ_[l])‖ ‖(b : ℂ_[l])‖ with h | h
  · obtain ⟨c, hc⟩ := aux a b h
    exact ⟨c, Or.inr hc⟩
  · obtain ⟨c, hc⟩ := aux b a h
    exact ⟨c, Or.inl hc⟩

variable {E : Type} [Field E] [NumberField E] [Algebra K E] {ι : Type} [Fintype ι] (σ : ι → E →+* ℂ_[l])

def embAll : 𝓞 E →+ (ι → ℂ_[l]) where
  toFun a := fun s => σ s (a : E)
  map_zero' := by funext s; simp
  map_add' a b := by funext s; simp

def closureMod (h : ∀ s x, σ s (algebraMap K E x) = ρ x) : Submodule (intClosure ρ) (ι → ℂ_[l]) where
  carrier := closure (Set.range (embAll σ))
  add_mem' := fun ha hb => (embAll σ).range.topologicalClosure.add_mem ha hb
  zero_mem' := (embAll σ).range.topologicalClosure.zero_mem
  smul_mem' := by
    intro c x hx
    refine map_mem_closure₂ (f := fun (c : ℂ_[l]) (x : ι → ℂ_[l]) => c • x) continuous_smul
      (show (c : ℂ_[l]) ∈ closure (Set.range fun a : 𝓞 K => ρ (a : K)) from c.2) hx ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    refine ⟨algebraMap (𝓞 K) (𝓞 E) a * b, ?_⟩
    funext s
    have e : ((algebraMap (𝓞 K) (𝓞 E) a * b : 𝓞 E) : E) = algebraMap K E (a : K) * (b : E) := rfl
    change σ s ((algebraMap (𝓞 K) (𝓞 E) a * b : 𝓞 E) : E) = ρ (a : K) * σ s (b : E)
    rw [e, map_mul, h]

end General

section Host

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

def rhoBase : D.host.E →+* ℂ_[l] :=
  lam.comp (D.host.φ₀.codRestrict Qbar fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom)

theorem rhoBase_apply (x : D.host.E) : rhoBase D lam x = lamC lam (D.host.φ₀ x) := by
  unfold lamC
  rw [dif_pos]
  rfl

def rhoK : D.host.K →+* ℂ_[l] := (rhoBase D lam).comp (algebraMap D.host.K D.host.E)

theorem fst_image_OKp : Prod.fst '' GL3Theta.OKp D lam = (intClosure (rhoK D lam) : Set ℂ_[l]) := by
  let f : 𝓞 D.host.K →+ ℂ_[l] × ℂ_[l] :=
    (((rhoK D lam).prod (((rhoBase D lam).comp (D.host.conj : D.host.E →+* D.host.E)).comp
      (algebraMap D.host.K D.host.E))).comp (algebraMap (𝓞 D.host.K) D.host.K)).toAddMonoidHom
  have hf : (fun a : 𝓞 D.host.K => (GL3Theta.tauK D lam (a : D.host.K), GL3Theta.tauKc D lam (a : D.host.K))) = f := by
    funext a
    exact Prod.ext (rhoBase_apply D lam _).symm (rhoBase_apply D lam _).symm
  unfold GL3Theta.OKp
  rw [hf, image_closure_of_isCompact (isCompact_closure_range (l := l) f) continuous_fst.continuousOn,
    ← Set.range_comp, coe_intClosure]
  rfl

end Host

end GlobalTheory.CompletedBasis
