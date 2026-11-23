import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.CvZeroTerm

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

theorem convolution_one {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (g : ℤ → M) (k : ℤ) :
    ConvolutionAlt.cv (1 : PowerSeries R) g k = g k := by
  unfold ConvolutionAlt.cv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [PowerSeries.coeff_one, if_neg hj, zero_smul]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

def phiIt (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (m : ℕ) (x : W.DD T) : ℕ → W.DD T
  | 0 => x
  | i + 1 => W.Q ^ m • W.φD T (phiIt W T m x i)

variable {W : LocWach PD LL O v n}

theorem primitive_root_pow_prime {ζ : LL} (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    ∃ j : ℕ, IsPrimitiveRoot (ζ ^ PD.p) (PD.p ^ j) := by
  obtain ⟨j, hj⟩ := hζ
  rcases j with _ | j
  · refine ⟨0, ?_⟩
    rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hj ⊢
    rw [hj, one_pow]
  · refine ⟨j, hj.pow (pow_pos (Fact.out : PD.p.Prime).pos _) ?_⟩
    rw [pow_succ']

theorem phiIt_levB_gen (Lb : LevB W) (T : LocLat G Qp LL O)
    (levB_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (hp0 : (PD.p : LL) ≠ 0)
    (m : ℕ) (a : ZMod n) (x : W.DD T) :
    ∀ (i : ℕ) (hN : ∀ r ≤ i, phiIt W T m x r ∈ W.N T) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) →
      ∀ k : ℤ, Lb.levB T (a + i) ζ ⟨phiIt W T m x i, hN i le_rfl⟩ k =
        ConvolutionAlt.cv (W.lev (a + i) ζ (∏ r ∈ Finset.range i, W.φA^[r] (W.Q ^ m)))
          (fun k => ((PD.p : LL) ^ ((i : ℤ) * k)) • (φVB PD (LL := LL) (V := T.V))^[i]
            (Lb.levB T a (ζ ^ PD.p ^ i) ⟨x, hN 0 (Nat.zero_le _)⟩ k)) k := by
  intro i
  induction i with
  | zero =>
    intro hN ζ _ k
    rw [Finset.prod_range_zero, map_one, convolution_one]
    simp only [Nat.cast_zero, add_zero, zero_mul, zpow_zero, one_smul, Function.iterate_zero, id, pow_zero,
      pow_one]
    rfl
  | succ i ih =>
    intro hN ζ hζ k
    have hNi : ∀ r ≤ i, phiIt W T m x r ∈ W.N T := fun r hr => hN r (Nat.le_succ_of_le hr)
    have hζp := primitive_root_pow_prime (PD := PD) hζ
    have hstep := levB_φ (a + ((i + 1 : ℕ) : ZMod n)) ζ hζ ⟨phiIt W T m x i, hNi i le_rfl⟩ m (hN (i + 1) le_rfl) k
    have hlet : a + ((i + 1 : ℕ) : ZMod n) - 1 = a + (i : ZMod n) := by push_cast; ring
    rw [hlet] at hstep
    have e0 : (⟨phiIt W T m x (i + 1), hN (i + 1) le_rfl⟩ : ↥(W.N T)) =
        ⟨W.Q ^ m • W.φD T ((⟨phiIt W T m x i, hNi i le_rfl⟩ : ↥(W.N T)) : W.DD T), hN (i + 1) le_rfl⟩ := rfl
    rw [e0, hstep]
    set L := W.lev (a + ((i + 1 : ℕ) : ZMod n)) ζ (W.Q ^ m) with hL
    set F := W.lev (a + (i : ZMod n)) (ζ ^ PD.p) (∏ r ∈ Finset.range i, W.φA^[r] (W.Q ^ m)) with hF
    set φ := φVB PD (LL := LL) (V := T.V) with hφ
    set g0 : ℤ → T.V ⊗[Qp] B := fun k => Lb.levB T a ((ζ ^ PD.p) ^ PD.p ^ i) ⟨x, hN 0 (Nat.zero_le _)⟩ k
      with hg0
    set h : ℤ → T.V ⊗[Qp] B := fun k => ((PD.p : LL) ^ ((i : ℤ) * k)) • φ^[i] (g0 k) with hh
    obtain ⟨m0, hm0⟩ := Lb.supp T a ((ζ ^ PD.p) ^ PD.p ^ i) ⟨x, hN 0 (Nat.zero_le _)⟩
    have hh0 : ∀ k < m0, h k = 0 := fun k hk => by
      simp only [hh, hg0, hm0 k hk, Function.iterate_fixed (map_zero φ) i, smul_zero]
    have hh1 : ∀ k < m0, (fun k => (PD.p : LL) ^ k • φ (h k)) k = 0 := fun k hk => by
      simp only [hh0 k hk, map_zero, smul_zero]
    have hfun : (fun k => (PD.p : LL) ^ k • φ (Lb.levB T (a + (i : ZMod n)) (ζ ^ PD.p)
        ⟨phiIt W T m x i, hNi i le_rfl⟩ k)) = fun k => ConvolutionAlt.cv (PowerSeries.rescale (PD.p : LL) F)
          (fun k => (PD.p : LL) ^ k • φ (h k)) k := by
      funext k'
      rw [ih hNi (ζ ^ PD.p) hζp k']
      exact ConvolutionAlt.cv_twist φ (PD.p : LL) hp0 F h m0 hh0 k'
    show ConvolutionAlt.cv L (fun k => (PD.p : LL) ^ k • φ (Lb.levB T (a + (i : ZMod n)) (ζ ^ PD.p)
        ⟨phiIt W T m x i, hNi i le_rfl⟩ k)) k = _
    rw [hfun, ← ConvolutionAlt.cv_mul L (PowerSeries.rescale (PD.p : LL) F) _ m0 hh1 k]
    have hser : L * PowerSeries.rescale (PD.p : LL) F =
        W.lev (a + ((i + 1 : ℕ) : ZMod n)) ζ (∏ r ∈ Finset.range (i + 1), W.φA^[r] (W.Q ^ m)) := by
      rw [hF, ← hlet, ← lev_φ _ ζ hζ, hL, ← map_mul, Finset.prod_range_succ', map_prod]
      congr 1
      rw [mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [Function.iterate_succ_apply']
    have hfn : (fun k => (PD.p : LL) ^ k • φ (h k)) = fun k => ((PD.p : LL) ^ (((i + 1 : ℕ) : ℤ) * k)) •
        φ^[i + 1] (Lb.levB T a (ζ ^ PD.p ^ (i + 1)) ⟨x, hN 0 (Nat.zero_le _)⟩ k) := by
      funext k'
      simp only [hh, hg0]
      rw [map_smul, smul_smul, ← zpow_add₀ hp0, Function.iterate_succ_apply', ← pow_mul, ← pow_succ']
      congr 2
      push_cast; ring
    rw [hser, hfn]

theorem phiIt_levB (Lb : LevB W) (T : LocLat G Qp LL O)
    (levB_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ (x : ↥(W.N T)) (m : ℕ)
      (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ k =
        ∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
          (((PD.p : LL) ^ (k - (j : ℤ))) •
            φVB PD (LL := LL) (V := T.V) (Lb.levB T (i - 1) (ζ ^ PD.p) x (k - (j : ℤ)))))
    (lev_φ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (hp0 : (PD.p : LL) ≠ 0)
    (m : ℕ) (c : ZMod n) (ell : ℕ) (x : W.DD T) (hN : ∀ i ≤ ell, phiIt W T m x i ∈ W.N T)
    (s : ℕ) (hs : s < ell) (ζ : LL) (hζ : IsPrimitiveRoot ζ (PD.p ^ (s + 1))) (k : ℤ) :
    Lb.levB T c ζ ⟨phiIt W T m x ell, hN ell le_rfl⟩ k =
      ConvolutionAlt.cv (W.lev c ζ (∏ i ∈ Finset.range ell, W.φA^[i] (W.Q ^ m)))
        (fun k => ((PD.p : LL) ^ ((ell : ℤ) * k)) • (φVB PD (LL := LL) (V := T.V))^[ell]
          (Lb.levB T (c - ell) 1 ⟨x, hN 0 (Nat.zero_le _)⟩ k)) k := by
  have h := phiIt_levB_gen Lb T levB_φ lev_φ hp0 m (c - ell) x ell hN ζ ⟨s + 1, hζ⟩ k
  have h1 : ζ ^ PD.p ^ ell = 1 :=
    (hζ.pow_eq_one_iff_dvd _).2 (pow_dvd_pow _ hs)
  rw [h1, sub_add_cancel] at h
  exact h

end Formalism.MainNotions.N.Ln03.Pf
