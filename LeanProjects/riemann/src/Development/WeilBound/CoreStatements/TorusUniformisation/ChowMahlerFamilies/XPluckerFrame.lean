import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XMinorGraded
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XBundleOfFamily
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPullLine

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_plucker_frame
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)
open ReciprocityTheory.ChartRestriction.G.Geo (div_mem_chartRing)

private theorem unit_lemma' {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ R) (hc : ∀ l, c l ∈ R) (hs : ∑ l, c l * f l = 1)
    (n : ℕ) : ∃ d : Fin k → Ω, (∀ l, d l ∈ R) ∧ ∑ l, d l * f l ^ n = 1 := by
  let fR : Fin k → R := fun l => ⟨f l, hf l⟩
  have htop : Ideal.span (Set.range fR) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun l => ⟨c l, hc l⟩, ?_⟩
    apply Subtype.ext
    simp [fR, hs]
  have h2 := Ideal.span_pow_eq_top _ htop n
  rw [← Set.range_comp] at h2
  have h3 : (1 : R) ∈ Ideal.span (Set.range ((fun x : R => x ^ n) ∘ fR)) := by
    rw [h2]
    trivial
  rw [Ideal.mem_span_range_iff_exists_fun] at h3
  obtain ⟨d, hd⟩ := h3
  refine ⟨fun l => (d l : Ω), fun l => (d l).2, ?_⟩
  have := congrArg (fun x : R => (x : Ω)) hd
  simpa [fR] using this

private theorem mem_of_loc_lemma_2 {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ R) (hc : ∀ l, c l ∈ R) (hs : ∑ l, c l * f l = 1)
    (t : Ω) (ht : ∀ l, ∃ n, f l ^ n * t ∈ R) : t ∈ R := by
  choose n hn using ht
  obtain ⟨d, hd, hsum⟩ := unit_lemma' R f c hf hc hs (Finset.univ.sup n)
  have key : t = ∑ l, d l * f l ^ (Finset.univ.sup n - n l) * (f l ^ n l * t) := by
    calc t = (∑ l, d l * f l ^ (Finset.univ.sup n)) * t := by rw [hsum, one_mul]
    _ = _ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← pow_sub_mul_pow (f l) (Finset.le_sup (Finset.mem_univ l))]
      ring
  rw [key]
  exact Subalgebra.sum_mem _ fun l _ =>
    Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hd l) (Subalgebra.pow_mem _ (hf l) _)) (hn l)

private theorem exists_pow_mul_basis_repr_mem {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {E : Type} [AddCommGroup E] [Module Ω E] (N : ℕ) (L : AddSubgroup E)
    {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ R) (hc : ∀ l, c l ∈ R) (hs : ∑ l, c l * f l = 1)
    (b : Fin k → Fin N → E) (hbli : ∀ l, LinearIndependent Ω (b l))
    (hbsp : ∀ l, Submodule.span Ω (Set.range (b l)) = ⊤)
    (hbiff : ∀ l (e : E), (∃ n : ℕ, f l ^ n • e ∈ L) ↔
      ∃ a : Fin N → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ R) ∧ e = ∑ q, a q • b l q) (l : Fin k) :
    ∃ m : ℕ, ∀ e ∈ L, ∀ q, f l ^ m * (Module.Basis.mk (hbli l) (hbsp l).ge).repr e q ∈ R := by
  let B : ∀ l, Module.Basis (Fin N) Ω E := fun l => Module.Basis.mk (hbli l) (hbsp l).ge
  have hB : ∀ l q, B l q = b l q := fun l q => Module.Basis.mk_apply _ _ _
  have hcoord : ∀ l (a : Fin N → Ω) q, (B l).repr (∑ q', a q' • b l q') q = a q := by
    intro l a q
    have h1 : (∑ q', a q' • b l q') = ∑ q', a q' • B l q' := by simp only [hB]
    rw [h1, Module.Basis.repr_sum_self]
  have hloc : ∀ l, ∀ e ∈ L, ∀ q, ∃ n, f l ^ n * (B l).repr e q ∈ R := by
    intro l e he q
    obtain ⟨a, ha, he'⟩ := (hbiff l e).1 ⟨0, by simpa using he⟩
    rw [he', hcoord]
    exact ha q
  have hgen : ∀ l' q', ∃ n, f l' ^ n • b l' q' ∈ L := by
    intro l' q'
    refine (hbiff l' (b l' q')).2 ⟨Pi.single q' 1, fun q => ⟨0, ?_⟩, ?_⟩
    · by_cases h : q = q'
      · subst h
        simpa using R.one_mem
      · simp [Pi.single_apply, h]
    · simp [Pi.single_apply]
  choose n₁ hn₁ using hgen
  have h2 : ∀ l l' q' q, ∃ n, f l ^ n * (B l).repr (f l' ^ n₁ l' q' • b l' q') q ∈ R :=
    fun l l' q' q => hloc l _ (hn₁ l' q') q
  choose n₂ hn₂ using h2
  let m : Fin k → ℕ := fun l => Finset.univ.sup (fun p : Fin k × Fin N × Fin N => n₂ l p.1 p.2.1 p.2.2)
  have hbound : ∀ l l' q' q, f l ^ m l * (B l).repr (f l' ^ n₁ l' q' • b l' q') q ∈ R := by
    intro l l' q' q
    have hle : n₂ l l' q' q ≤ m l :=
      Finset.le_sup (f := fun p : Fin k × Fin N × Fin N => n₂ l p.1 p.2.1 p.2.2) (Finset.mem_univ (l', q', q))
    rw [← pow_sub_mul_pow (f l) hle, mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (hf l) _) (hn₂ l l' q' q)
  refine ⟨m l, fun e he q => ?_⟩
  show f l ^ m l * (B l).repr e q ∈ R
  apply mem_of_loc_lemma_2 R f c hf hc hs
  intro l'
  obtain ⟨a, ha, he'⟩ := (hbiff l' e).1 ⟨0, by simpa using he⟩
  choose n₃ hn₃ using ha
  refine ⟨Finset.univ.sup n₃ + Finset.univ.sup (n₁ l'), ?_⟩
  have hexp : f l' ^ (Finset.univ.sup n₃ + Finset.univ.sup (n₁ l')) * (f l ^ m l * (B l).repr e q) =
      ∑ q', (f l' ^ (Finset.univ.sup n₃ - n₃ q') * (f l' ^ n₃ q' * a q')) *
        (f l' ^ (Finset.univ.sup (n₁ l') - n₁ l' q') *
          (f l ^ m l * (B l).repr (f l' ^ n₁ l' q' • b l' q') q)) := by
    rw [he']
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q' _ => ?_
    have e1 := pow_sub_mul_pow (f l') (Finset.le_sup (f := n₃) (Finset.mem_univ q'))
    have e2 := pow_sub_mul_pow (f l') (Finset.le_sup (f := n₁ l') (Finset.mem_univ q'))
    rw [pow_add, ← e1, ← e2]
    ring
  rw [hexp]
  exact Subalgebra.sum_mem _ fun q' _ => Subalgebra.mul_mem _
    (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (hf l') _) (hn₃ q'))
    (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (hf l') _) (hbound l l' q' q))

theorem genDual_span {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R₀ R : Subalgebra o Ω)
    (hle : ∀ r ∈ R₀, r ∈ R) {V : Type} [AddCommGroup V] [Module Ω V] {N M : ℕ} (L₀ : AddSubgroup V)
    (hL : LocFree R₀ N L₀) (φ : Fin M → Module.Dual Ω V) (hφ : GenDual R₀ L₀ φ) :
    GenDual R (AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ L₀, v = a • e}) φ := by
  obtain ⟨hsm, k, f, c, hf, hc, hs, hch⟩ := hL
  choose b hbli hbsp hbiff using hch
  refine ⟨fun l v hv => ?_, fun ψ hψ => ?_⟩
  · induction hv using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, e, he, rfl⟩ := hx
      rw [map_smul, smul_eq_mul]
      exact R.mul_mem ha (hle _ (hφ.1 l e he))
    | zero =>
      rw [map_zero]
      exact R.zero_mem
    | add x y _ _ hx hy =>
      rw [map_add]
      exact R.add_mem hx hy
    | neg x _ hx =>
      rw [map_neg]
      exact R.neg_mem hx
  · have hψ0 : ∀ e ∈ L₀, ψ e ∈ R := fun e he =>
      hψ e (AddSubgroup.subset_closure ⟨1, R.one_mem, e, he, (one_smul _ _).symm⟩)
    have hchart : ∀ l, ∃ n : ℕ, ∃ u : Fin M → Ω, (∀ m, u m ∈ R) ∧ f l ^ n • ψ = ∑ m, u m • φ m := by
      intro l
      obtain ⟨m, hm⟩ := exists_pow_mul_basis_repr_mem R₀ N L₀ f c hf hc hs b hbli hbsp hbiff l
      set B := Module.Basis.mk (hbli l) (hbsp l).ge with hBdef
      have hB : ∀ q, B q = b l q := fun q => Module.Basis.mk_apply _ _ _
      have hχ : ∀ q, ∃ u : Fin M → Ω, (∀ m', u m' ∈ R₀) ∧ f l ^ m • B.coord q = ∑ m', u m' • φ m' := by
        intro q
        exact hφ.2 _ (fun v hv => by simpa [Module.Basis.coord_apply] using hm v hv q)
      choose u hu hχeq using hχ
      have hgen : ∀ q, ∃ n, f l ^ n • b l q ∈ L₀ := by
        intro q
        refine (hbiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
        · by_cases h : q' = q
          · subst h
            simpa using R₀.one_mem
          · simp [Pi.single_apply, h]
        · simp [Pi.single_apply]
      choose n₁ hn₁ using hgen
      have hψb : ∀ q, f l ^ Finset.univ.sup n₁ * ψ (b l q) ∈ R := by
        intro q
        have h1 := hψ0 _ (hn₁ q)
        rw [map_smul, smul_eq_mul] at h1
        rw [← pow_sub_mul_pow (f l) (Finset.le_sup (f := n₁) (Finset.mem_univ q)), mul_assoc]
        exact R.mul_mem (R.pow_mem (hle _ (hf l)) _) h1
      refine ⟨m + Finset.univ.sup n₁, fun m' => ∑ q, f l ^ Finset.univ.sup n₁ * ψ (b l q) * u q m',
        fun m' => R.sum_mem fun q _ => R.mul_mem (hψb q) (hle _ (hu q m')), ?_⟩
      ext v
      have hχv : ∀ q, f l ^ m * B.repr v q = ∑ m', u q m' * φ m' v := by
        intro q
        have := congrArg (fun χ : Module.Dual Ω V => χ v) (hχeq q)
        simpa [Module.Basis.coord_apply] using this
      have hv := B.sum_repr v
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, Finset.sum_mul]
      conv_lhs => rw [← hv]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, hB]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      calc _ = f l ^ Finset.univ.sup n₁ * ψ (b l q) * (f l ^ m * B.repr v q) := by ring
      _ = _ := by
        rw [hχv q, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m' _ => by ring
    choose n u hu hueq using hchart
    obtain ⟨d, hd, hsum⟩ := unit_lemma' R₀ f c hf hc hs (Finset.univ.sup n)
    refine ⟨fun m' => ∑ l, d l * f l ^ (Finset.univ.sup n - n l) * u l m',
      fun m' => R.sum_mem fun l _ => R.mul_mem (R.mul_mem (hle _ (hd l)) (R.pow_mem (hle _ (hf l)) _)) (hu l m'), ?_⟩
    calc ψ = (∑ l, d l * f l ^ (Finset.univ.sup n)) • ψ := by rw [hsum, one_smul]
    _ = ∑ l, (d l * f l ^ (Finset.univ.sup n - n l)) • (f l ^ n l • ψ) := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, mul_assoc, pow_sub_mul_pow (f l) (Finset.le_sup (Finset.mem_univ l))]
    _ = _ := by
      simp only [hueq, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]

theorem flagMinor_smul {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {N M : ℕ}
    (φ : Fin M → Module.Dual Ω V) (w : Fin N → V) (c : Ω) (n : ℕ) (hn : n ≤ N) (I : Fin n → Fin M) :
    flagMinor (fun l => c • φ l) w n hn I = c ^ n * flagMinor φ w n hn I := by
  unfold flagMinor
  have h : (Matrix.of fun (a b : Fin n) => ((fun l => c • φ l) (I a)) (w (Fin.castLE hn b))) =
      c • Matrix.of fun (a b : Fin n) => φ (I a) (w (Fin.castLE hn b)) := by
    ext a b
    simp
  rw [h, Matrix.det_smul, Fintype.card_fin]

theorem ne_zero_of_mseg {Ω : Type} [Field Ω] {K : Type} [Fintype K] {ι : K → Type}
    (y : (Σ k, ι k) → Ω) (s : ∀ k, ι k) (hs : mseg y s ≠ 0) (k : K) : y ⟨k, s k⟩ ≠ 0 :=
  Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)

theorem ratio_mem {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {K : Type} [Fintype K]
    {ι : K → Type} (y : (Σ k, ι k) → Ω) (s : ∀ k, ι k) (hs : mseg y s ≠ 0) (k : K) (i : ι k) :
    y ⟨k, i⟩ / y ⟨k, s k⟩ ∈ chartRing O (mseg y) s := by
  classical
  have hall : ∀ k', y ⟨k', s k'⟩ ≠ 0 := fun k' => ne_zero_of_mseg y s hs k'
  have key : mseg y (Function.update s k i) / mseg y s = y ⟨k, i⟩ / y ⟨k, s k⟩ := by
    unfold mseg
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase _ (fun k' => y ⟨k', s k'⟩) (Finset.mem_univ k)]
    have hrest : ∏ x ∈ Finset.univ.erase k, y ⟨x, Function.update s k i x⟩ =
        ∏ x ∈ Finset.univ.erase k, y ⟨x, s x⟩ :=
      Finset.prod_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    have hne : ∏ x ∈ Finset.univ.erase k, y ⟨x, s x⟩ ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun x _ => hall x
    rw [hrest, Function.update_self]
    have hk := hall k
    field_simp
  rw [← key]
  exact Algebra.subset_adjoin ⟨_, rfl⟩

theorem prod_zpow_single {Ω : Type} [Field Ω] {K : Type} [Fintype K] [DecidableEq K] (z : K → Ω)
    (p : K) : ∏ k, z k ^ (Pi.single p 1 : K → ℤ) k = z p := by
  rw [Finset.prod_eq_single p]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem prod_zpow_sub {Ω : Type} [Field Ω] {K : Type} [Fintype K] [DecidableEq K] (z : K → Ω)
    (hz : ∀ k, z k ≠ 0) (p q : K) :
    ∏ k, z k ^ ((Pi.single p 1 : K → ℤ) - Pi.single q 1 : K → ℤ) k = z p / z q := by
  simp only [Pi.sub_apply]
  rw [Finset.prod_congr rfl (fun k _ => zpow_sub₀ (hz k) _ _), Finset.prod_div_distrib,
    prod_zpow_single, prod_zpow_single]

end PositivityTheory.Xgn.A_plucker_frame

theorem PositivityTheory.Xgn.t_plucker_frame : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (J : Type) [Fintype J] [DecidableEq J] (E : J → ChartBundle O (mseg x) N V) (M : J → ℕ) (a : J → K → ℤ) (φ : ∀ j, Fin (M j) → Module.Dual Ω V), (∀ j, IsTwistedDualGens x (E j) (a j) (φ j)) → ∀ (w : Module.Basis (Fin N) Ω V) (j : J) (EB : ChartBundle O (mseg (joinCoord x (pluckerCoord φ w))) N V), IsPull O x (pluckerCoord φ w) (E j) EB → IsFlagFrame (joinCoord x (pluckerCoord φ w)) EB w (pluckerDeg (a j) j) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ J _ _ E M a φ hE w j EB hpull
  letI hfin : ∀ k, Fintype (Sum.elim ι (pluckerIdx N M) k) := fun k =>
    match k with
    | Sum.inl k => inferInstanceAs (Fintype (ι k))
    | Sum.inr k => inferInstanceAs (Fintype (Fin (k.2 : ℕ) → Fin (M k.1)))
  refine ⟨fun c hc i => ?_⟩
  have hc' : mseg (joinCoord x (pluckerCoord φ w)) c ≠ 0 := hc
  set c0 : ∀ k, ι k := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.restrictChart c with hc0def
  have hx0 : ∀ k, x ⟨k, c0 k⟩ ≠ 0 := fun k => PositivityTheory.Xgn.A_plucker_frame.ne_zero_of_mseg (joinCoord x (pluckerCoord φ w)) c hc' (Sum.inl k)
  have hz0 : ∀ p : J × Fin (N + 1), (joinCoord x (pluckerCoord φ w)) ⟨Sum.inr p, c (Sum.inr p)⟩ ≠ 0 :=
    fun p => PositivityTheory.Xgn.A_plucker_frame.ne_zero_of_mseg (joinCoord x (pluckerCoord φ w)) c hc' (Sum.inr p)
  have hc0 : mseg x c0 ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hx0 k
  have hle : ∀ r ∈ chartRing O (mseg x) c0, r ∈ chartRing O (mseg (joinCoord x (pluckerCoord φ w))) c := by
    intro r hr
    refine (Algebra.adjoin_le ?_) hr
    rintro _ ⟨t, rfl⟩
    let t' : ∀ k, Sum.elim ι (pluckerIdx N M) k := fun k =>
      Sum.rec (motive := fun k => Sum.elim ι (pluckerIdx N M) k) t (fun p => c (Sum.inr p)) k
    have hZ : ∏ p : J × Fin (N + 1), (joinCoord x (pluckerCoord φ w)) ⟨Sum.inr p, c (Sum.inr p)⟩ ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p _ => hz0 p
    have heq : mseg (joinCoord x (pluckerCoord φ w)) t' / mseg (joinCoord x (pluckerCoord φ w)) c = mseg x t / mseg x c0 := by
      unfold mseg
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      show ((∏ k, x ⟨k, t k⟩) * ∏ p : J × Fin (N + 1), (joinCoord x (pluckerCoord φ w)) ⟨Sum.inr p, c (Sum.inr p)⟩) /
        ((∏ k, x ⟨k, c0 k⟩) * ∏ p : J × Fin (N + 1), (joinCoord x (pluckerCoord φ w)) ⟨Sum.inr p, c (Sum.inr p)⟩) = _
      rw [mul_div_mul_right _ _ hZ]
    show mseg x t / mseg x c0 ∈ _
    rw [← heq]
    exact Algebra.subset_adjoin ⟨t', rfl⟩
  have hL0 : LocFree (chartRing O (mseg x) c0) N ((E j).lat c0) :=
    ((t_bundle_of_family O Ω K ι x N V).2 (E j)).2 c0 hc0
  have hL : LocFree (chartRing O (mseg (joinCoord x (pluckerCoord φ w))) c) N (EB.lat c) :=
    ((t_bundle_of_family O Ω (K ⊕ (J × Fin (N + 1))) (Sum.elim ι (pluckerIdx N M)) (joinCoord x (pluckerCoord φ w)) N V).2 EB).2 c hc'
  set t : Ω := ∏ k, x ⟨k, c0 k⟩ ^ (-(a j k)) with ht
  set P : Ω := ∏ k, x ⟨k, c0 k⟩ ^ (a j k) with hP
  have htP : t * P = 1 := by
    rw [ht, hP, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hx0 k))]
  have ht0 : t ≠ 0 := left_ne_zero_of_mul_eq_one htP
  have hgd0 : GenDual (chartRing O (mseg x) c0) ((E j).lat c0) (fun l => t • φ j l) := by
    refine ⟨fun l v hv => ?_, fun ψ hψ => ?_⟩
    · obtain ⟨r, hr, hrv⟩ := (hE j).sections c0 hc0 l v hv
      rw [LinearMap.smul_apply, hrv, smul_eq_mul]
      show t * (r * P) ∈ _
      rw [mul_left_comm, htP, mul_one]
      exact hr
    · obtain ⟨u, hu, hψeq⟩ := (hE j).generate c0 hc0 ψ hψ
      refine ⟨u, hu, ?_⟩
      rw [hψeq]
      refine Finset.sum_congr rfl fun l _ => ?_
      show _ = u l • t • φ j l
      rw [smul_smul]
  have hgd : GenDual (chartRing O (mseg (joinCoord x (pluckerCoord φ w))) c) (EB.lat c) (fun l => t • φ j l) := by
    rw [hpull c hc']
    exact PositivityTheory.Xgn.A_plucker_frame.genDual_span (chartRing O (mseg x) c0) (chartRing O (mseg (joinCoord x (pluckerCoord φ w))) c) hle ((E j).lat c0) hL0 _ hgd0
  have hsm : ∀ (n : ℕ) (hn : n ≤ N) (I : Fin n → Fin (M j)),
      flagMinor (fun l => t • φ j l) w n hn I = t ^ n * flagMinor (φ j) w n hn I :=
    fun n hn I => PositivityTheory.Xgn.A_plucker_frame.flagMinor_smul (φ j) w t n hn I
  have hI := PositivityTheory.Xgn.A_plucker_frame.ne_zero_of_mseg (joinCoord x (pluckerCoord φ w)) c hc' (Sum.inr (j, i.castSucc))
  have hJ := PositivityTheory.Xgn.A_plucker_frame.ne_zero_of_mseg (joinCoord x (pluckerCoord φ w)) c hc' (Sum.inr (j, i.succ))
  have key := t_minor_graded (chartRing O (mseg (joinCoord x (pluckerCoord φ w))) c) N (M j) (EB.lat c) hL (fun l => t • φ j l) hgd w i
    (c (Sum.inr (j, i.castSucc)) : Fin (i : ℕ) → Fin (M j))
    (c (Sum.inr (j, i.succ)) : Fin ((i : ℕ) + 1) → Fin (M j))
    (by
      rw [hsm (i : ℕ) _ (c (Sum.inr (j, i.castSucc)))]
      exact mul_ne_zero (pow_ne_zero _ ht0) hI)
    (fun I' => by
      rw [hsm _ _ I', hsm (i : ℕ) _ (c (Sum.inr (j, i.castSucc))), mul_div_mul_left _ _ (pow_ne_zero _ ht0)]
      exact PositivityTheory.Xgn.A_plucker_frame.ratio_mem (joinCoord x (pluckerCoord φ w)) c hc' (Sum.inr (j, i.castSucc)) I')
    (by
      rw [hsm ((i : ℕ) + 1) _ (c (Sum.inr (j, i.succ)))]
      exact mul_ne_zero (pow_ne_zero _ ht0) hJ)
    (fun J' => by
      rw [hsm _ _ J', hsm ((i : ℕ) + 1) _ (c (Sum.inr (j, i.succ))), mul_div_mul_left _ _ (pow_ne_zero _ ht0)]
      exact PositivityTheory.Xgn.A_plucker_frame.ratio_mem (joinCoord x (pluckerCoord φ w)) c hc' (Sum.inr (j, i.succ)) J')
  rw [key]
  unfold degLat
  have hQ : ∀ {A B : Ω}, A = B → ({s : Ω | ∃ r ∈ chartRing O (mseg (joinCoord x (pluckerCoord φ w))) c, s = r * A} =
      {s : Ω | ∃ r ∈ chartRing O (mseg (joinCoord x (pluckerCoord φ w))) c, s = r * B}) := fun h => by rw [h]
  apply hQ
  rw [hsm (i : ℕ) _ (c (Sum.inr (j, i.castSucc))), hsm ((i : ℕ) + 1) _ (c (Sum.inr (j, i.succ))), Fintype.prod_sum_type]
  simp only [pluckerDeg, Sum.elim_inl, Sum.elim_inr]
  rw [PositivityTheory.Xgn.A_plucker_frame.prod_zpow_sub (fun p => (joinCoord x (pluckerCoord φ w)) ⟨Sum.inr p, c (Sum.inr p)⟩) hz0]
  have hPt : P = t⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact htP)
  show t ^ (i : ℕ) * (joinCoord x (pluckerCoord φ w)) ⟨Sum.inr (j, i.castSucc), c (Sum.inr (j, i.castSucc))⟩ /
      (t ^ ((i : ℕ) + 1) * (joinCoord x (pluckerCoord φ w)) ⟨Sum.inr (j, i.succ), c (Sum.inr (j, i.succ))⟩) =
    P * ((joinCoord x (pluckerCoord φ w)) ⟨Sum.inr (j, i.castSucc), c (Sum.inr (j, i.castSucc))⟩ /
      (joinCoord x (pluckerCoord φ w)) ⟨Sum.inr (j, i.succ), c (Sum.inr (j, i.succ))⟩)
  rw [hPt, pow_succ]
  field_simp
