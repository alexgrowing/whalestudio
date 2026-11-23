import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToZModPowKummerEqIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobeniusSemisimplification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNilpotentZpowSubOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAevalEqSmulOnEigenspace

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module

namespace GlobalTheory.WeilDeligne

section Exp

open IsNilpotent

theorem semiconj_exp {R : Type*} [Ring R] [Algebra ℚ R] {x a b : R} (ha : IsNilpotent a)
    (hb : IsNilpotent b) (hx : x * a = b * x) : x * exp a = exp b * x := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨k, hk⟩ := hb
  rw [exp_eq_sum (pow_eq_zero_of_le (le_max_left m k) hm),
    exp_eq_sum (pow_eq_zero_of_le (le_max_right m k) hk), Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, (SemiconjBy.pow_right (a := x) hx i).eq]

variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

theorem exp_add_smul {N : Matrix n n K} (hN : IsNilpotent N) (s t : K) :
    exp ((s + t) • N) = exp (s • N) * exp (t • N) := by
  rw [add_smul]
  exact exp_add_of_commute (((Commute.refl N).smul_left s).smul_right t) (hN.smul s) (hN.smul t)

theorem exp_smul_mul {N : Matrix n n K} (hN : IsNilpotent N) (s : K) :
    exp (s • N) * N = N * exp (s • N) :=
  (semiconj_exp (hN.smul s) (hN.smul s) ((Commute.refl N).smul_right s).eq).symm

theorem eq_of_exp_smul_eq {N N' : Matrix n n K} (hN : IsNilpotent N) (hN' : IsNilpotent N')
    {c : K} (hc : c ≠ 0) (H : ∀ k : ℕ, exp (((k : K) * c) • N) = exp (((k : K) * c) • N')) :
    N = N' := by
  obtain ⟨m, hm⟩ := hN
  obtain ⟨m', hm'⟩ := hN'
  ext i j
  let P : Matrix n n K → K[X] := fun M =>
    ∑ d ∈ Finset.range (m + m' + 2), monomial d ((d.factorial : K)⁻¹ * (M ^ d) i j)
  have hP : ∀ M : Matrix n n K, M ^ (m + m' + 2) = 0 → ∀ s : K,
      (P M).eval s = (exp (s • M)) i j := by
    intro M hM s
    rw [exp_eq_sum (k := m + m' + 2) (by rw [_root_.smul_pow, hM, smul_zero]), eval_finsetSum,
      Matrix.sum_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [eval_monomial, _root_.smul_pow, Matrix.smul_apply, Matrix.smul_apply, Rat.smul_def]
    simp only [smul_eq_mul]
    push_cast; ring
  have hPP : P N = P N' := by
    refine eq_of_infinite_eval_eq _ _ (Set.infinite_of_injective_forall_mem
      (f := fun k : ℕ => (k : K) * c) (fun a b hab => by simpa [hc] using hab) fun k => ?_)
    show _ = _
    rw [hP N (pow_eq_zero_of_le (by omega) hm), hP N' (pow_eq_zero_of_le (by omega) hm'), H]
  have := congrArg (fun p => coeff p 1) hPP
  simpa [P, finsetSum_coeff, coeff_monomial] using this

end Exp

theorem charpoly_eq_of_isNilpotent_sub {K V : Type*} [Field K] [Infinite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {f g : End K V} (hc : Commute f g)
    (hn : IsNilpotent (g - f)) : f.charpoly = g.charpoly := by
  refine eq_of_infinite_eval_eq _ _ ((f.charpoly.finite_setOfPred_isRoot
    (LinearMap.charpoly_monic f).ne_zero).infinite_compl.mono fun t ht => ?_)
  have hu : IsUnit (algebraMap K (End K V) t - f) := by
    rw [LinearMap.isUnit_iff_isUnit_det, ← LinearMap.eval_charpoly]
    exact isUnit_iff_ne_zero.mpr ht
  obtain ⟨u, hu⟩ := hu
  have h1 : Commute (u : End K V) (g - f) := by
    rw [hu]
    exact (Algebra.commute_algebraMap_left t _).sub_left (hc.sub_right (Commute.refl f))
  have h2 : IsNilpotent ((↑u⁻¹ : End K V) * (g - f)) :=
    h1.units_inv_left.isNilpotent_mul_left hn
  have h3 : LinearMap.det (1 - (↑u⁻¹ : End K V) * (g - f)) = 1 := by
    have := LinearMap.eval_charpoly ((↑u⁻¹ : End K V) * (g - f)) 1
    rw [h2.charpoly_eq_X_pow_finrank, map_one] at this
    simpa using this.symm
  have h4 : algebraMap K (End K V) t - g = u * (1 - (↑u⁻¹ : End K V) * (g - f)) := by
    rw [mul_sub, Units.mul_inv_cancel_left, mul_one, hu]; abel
  show _ = _
  rw [LinearMap.eval_charpoly, LinearMap.eval_charpoly, h4, map_mul, h3, mul_one, hu]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def IsFrobSS (ρ : Weil h → End ℂ V) (N : End ℂ V) (a : WDRep h V) : Prop :=
  a.N = N ∧ ∀ g, Commute (a.ρ g) (ρ g) ∧ IsNilpotent (ρ g - a.ρ g)

theorem isFrobSS_self (a : WDRep h V) : IsFrobSS a.ρ a.N a :=
  ⟨rfl, fun g => ⟨Commute.refl _, by simp⟩⟩

theorem IsFrobSS.ρ_eq {ρ : Weil h → End ℂ V} {N : End ℂ V} {a : WDRep h V} (ha : IsFrobSS ρ N a)
    {g : Weil h} (hg : (ρ g).IsSemisimple) : a.ρ g = ρ g :=
  (End.isNilpotent_isSemisimple_unique (ha.2 g).2 (a.semisimple g) IsNilpotent.zero hg
    ((ha.2 g).1.symm.sub_left (Commute.refl _)) (Commute.zero_left _) (by simp)).2

theorem IsFrobSS.ρ_unique {ρ : Weil h → End ℂ V} {N N' : End ℂ V} {a b : WDRep h V}
    (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ N' b) : a.ρ = b.ρ :=
  MonoidHom.ext fun g =>
    (End.isNilpotent_isSemisimple_unique (ha.2 g).2 (a.semisimple g) (hb.2 g).2 (b.semisimple g)
      ((ha.2 g).1.symm.sub_left (Commute.refl _)) ((hb.2 g).1.symm.sub_left (Commute.refl _))
      (by simp)).2

theorem IsFrobSS.iso {ρ : Weil h → End ℂ V} {N : End ℂ V} {a : WDRep h V} {ρ' : Weil h → End ℂ V'}
    {N' : End ℂ V'} {b : WDRep h V'} (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ' N' b)
    (e : V ≃ₗ[ℂ] V') (hρ : ∀ g v, e (ρ g v) = ρ' g (e v)) (hN : ∀ v, e (N v) = N' (e v)) :
    a.Iso b := by
  have h1 : ∀ g, ρ' g = e.conjAlgEquiv ℂ (ρ g) := fun g => LinearMap.ext fun v => by
    simp [hρ]
  have h2 : IsFrobSS ρ' (a.transport e).N (a.transport e) := ⟨rfl, fun g => by
    rw [h1]
    refine ⟨(ha.2 g).1.map (e.conjAlgEquiv ℂ), ?_⟩
    have := (ha.2 g).2.map (e.conjAlgEquiv ℂ)
    rwa [map_sub] at this⟩
  refine ⟨e, fun g v => ?_, fun v => by rw [ha.1, hb.1, hN]⟩
  rw [← h2.ρ_unique hb]
  show _ = e.conjAlgEquiv ℂ (a.ρ g) (e v)
  simp

theorem IsFrobSS.iso_of_smul {ρ : Weil h → End ℂ V} {N : End ℂ V} {a b : WDRep h V} {c : ℂ}
    (hc : c ≠ 0) (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ (c • N) b) : a.Iso b :=
  WDRep.iso_of_N_eq_smul E Ω A w h V a b c hc (ha.ρ_unique hb) (by rw [hb.1, ha.1])

theorem isFrobSS_of_unipotent {ρ : Weil h → End ℂ V} {a : WDRep h V} (u : (End ℂ V)ˣ)
    (hu : IsNilpotent ((u : End ℂ V) - 1)) (hc : ∀ g, Commute (u : End ℂ V) (ρ g))
    (hρ : ∀ g, ρ g = a.ρ g * ((u ^ deg g : (End ℂ V)ˣ) : End ℂ V)) : IsFrobSS ρ a.N a := by
  refine ⟨rfl, fun g => ?_⟩
  obtain ⟨h1, h2⟩ := FrobSemisimpleUnique.nilpotent_part (u ^ deg g)
    (FrobSemisimpleUnique.isNilpotent_zpow_sub_one u hu _) ((hc g).units_zpow_left _) (hρ g)
  exact ⟨by simpa using (h2.add_left (Commute.refl _)).symm, h1⟩

theorem exists_isFrobSS (ρ : Representation ℂ (Weil h) V) (N : End ℂ V) (hρ : IsSmooth ρ)
    (hN : IsNilpotent N) (hc : ∀ g, ρ g * N = ((normV w : ℕ) : ℂ) ^ deg g • (N * ρ g)) :
    ∃ a : WDRep h V, IsFrobSS ρ N a := by
  obtain ⟨a, u, h1, h2, -, h3, h4⟩ :=
    exists_frobenius_semisimplification E Ω A w h V ρ N hρ hN hc
  exact ⟨a, h1 ▸ isFrobSS_of_unipotent u h2 h3 h4⟩

theorem IsFrobSS.charpoly_eq {ρ : Weil h → End ℂ V} {N : End ℂ V} {a : WDRep h V}
    (ha : IsFrobSS ρ N a) (g : Weil h) : (a.ρ g).charpoly = (ρ g).charpoly :=
  charpoly_eq_of_isNilpotent_sub (ha.2 g).1 (ha.2 g).2

theorem IsFrobSS.ρ_ineIncl {ρ : Representation ℂ (Weil h) V} {N : End ℂ V} {a : WDRep h V}
    (ha : IsFrobSS ρ N a) (hρ : IsSmooth ρ) (σ : Ine (F := E) A) :
    a.ρ (ineIncl h σ) = ρ (ineIncl h σ) := by
  refine ha.ρ_eq ?_
  have := compactSpace_Ine (E := E) A
  have : Finite (Ine (F := E) A ⧸ (ρ.comp (ineIncl h)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hρ
  obtain ⟨d, hd, -, hσ⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := (ρ.comp (ineIncl h)).ker)) σ
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ d - C 1)
    (separable_X_pow_sub_C 1 (Nat.cast_ne_zero.mpr hd.ne') one_ne_zero).squarefree ?_
  rw [MonoidHom.mem_ker, map_pow] at hσ
  simpa [sub_eq_zero] using hσ

end GlobalTheory.WeilDeligne
