import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.DivisorFrames.ExistsNormalVerticalModel
import Development.AutomorphicArithmetic.DivisorFrames.VerticalModelMatchCompat
import Development.AutomorphicArithmetic.DivisorFrames.UnitAtPowDivFnMapOfReadsOfGReads
import Development.AutomorphicArithmetic.DivisorFrames.VerticalDegreeRationalSection
import Development.AutomorphicArithmetic.DivisorFrames.VerticalModelDimensionMatch
import Development.AutomorphicArithmetic.DivisorFrames.NormalModelComplexCompat
import Development.AutomorphicArithmetic.DivisorFrames.PullClassRationalPower
import Development.AutomorphicArithmetic.DivisorFrames.PdegSmulPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapDegreeFinitePullback
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem comb {J Z : Type} [Fintype J] {X : J → Type} (g : ∀ j, X j → Z) (μ w rd : ∀ j, X j → ℤ)
    (hμ : ∀ j, (Function.support (μ j)).Finite) (ν π : Z → ℤ) (hν : (Function.support ν).Finite)
    (A C : Z → Prop) (c K : ℝ) (m d : ℕ)
    (h1 : ∀ j ζ, μ j ζ ≠ 0 → A (g j ζ))
    (h2 : ∀ j ζ, μ j ζ ≠ 0 → (m : ℤ) ^ d * w j ζ = if C (g j ζ) then rd j ζ * π (g j ζ) else 0)
    (h3 : ∀ η, ν η ≠ 0 → C η)
    (h4 : ∀ η, A η → C η →
      c * ∑ j, ((∑ᶠ ζ, if g j ζ = η then ((m : ℤ) * μ j ζ) * rd j ζ else 0 : ℤ) : ℝ) = K * (ν η : ℝ)) :
    (m : ℝ) ^ (d + 1) * c * ∑ j, ((∑ᶠ ζ, μ j ζ * w j ζ : ℤ) : ℝ) =
      K * ∑ᶠ z, if A z then ((ν z * π z : ℤ) : ℝ) else 0 := by
  set S : Finset Z := (hν.toFinset ∪ Finset.univ.biUnion fun j => (hμ j).toFinset.image (g j)).filter
    fun η => A η ∧ C η with hS
  have e1 : (∑ᶠ z, if A z then ((ν z * π z : ℤ) : ℝ) else 0) = ∑ z ∈ S, ((ν z * π z : ℤ) : ℝ) := by
    rw [finsum_eq_sum_of_support_subset (s := S)]
    · refine Finset.sum_congr rfl fun z hz => if_pos (Finset.mem_filter.1 hz).2.1
    · intro z hz
      have hA : A z := by
        by_contra h
        exact hz (if_neg h)
      have hn : ν z ≠ 0 := by
        intro h
        apply hz
        simp [h]
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_union_left _ (by simpa using hn), hA, h3 z hn⟩)
  have e2 : ∀ j, (∑ᶠ ζ, μ j ζ * w j ζ) = ∑ ζ ∈ (hμ j).toFinset, μ j ζ * w j ζ := fun j =>
    finsum_eq_sum_of_support_subset _ fun ζ hζ => by
      simpa using left_ne_zero_of_mul hζ
  have e3 : ∀ j η, (∑ᶠ ζ, if g j ζ = η then ((m : ℤ) * μ j ζ) * rd j ζ else 0) =
      ∑ ζ ∈ (hμ j).toFinset, if g j ζ = η then ((m : ℤ) * μ j ζ) * rd j ζ else 0 := fun j η =>
    finsum_eq_sum_of_support_subset _ fun ζ hζ => by
      have : μ j ζ ≠ 0 := by
        intro h
        apply hζ
        simp [h]
      simpa using this
  have e4 : ∀ j, (m : ℤ) ^ (d + 1) * ∑ ζ ∈ (hμ j).toFinset, μ j ζ * w j ζ =
      ∑ η ∈ S, (∑ ζ ∈ (hμ j).toFinset, if g j ζ = η then ((m : ℤ) * μ j ζ) * rd j ζ else 0) * π η := by
    intro j
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ζ hζ => ?_
    have hζ' : μ j ζ ≠ 0 := by simpa using hζ
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    have hiff : g j ζ ∈ S ↔ C (g j ζ) := by
      refine ⟨fun h => (Finset.mem_filter.1 h).2.2, fun h => Finset.mem_filter.2 ⟨?_, h1 j ζ hζ', h⟩⟩
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _,
        Finset.mem_image_of_mem _ hζ⟩)
    have := h2 j ζ hζ'
    by_cases hC : C (g j ζ)
    · rw [if_pos hC] at this
      rw [if_pos (hiff.2 hC)]
      linear_combination (m : ℤ) * μ j ζ * this
    · rw [if_neg hC] at this
      rw [if_neg (mt hiff.1 hC)]
      linear_combination (m : ℤ) * μ j ζ * this
  rw [e1, Finset.mul_sum S]
  have e5 : ∀ η ∈ S, K * ((ν η * π η : ℤ) : ℝ) = c * ∑ j,
      (((∑ ζ ∈ (hμ j).toFinset, if g j ζ = η then ((m : ℤ) * μ j ζ) * rd j ζ else 0) * π η : ℤ) : ℝ) := by
    intro η hη
    have := h4 η (Finset.mem_filter.1 hη).2.1 (Finset.mem_filter.1 hη).2.2
    simp only [e3] at this
    simp only [Int.cast_mul (_ : ℤ) (π η)]
    rw [← Finset.sum_mul, ← mul_assoc, ← this, mul_assoc]
  rw [Finset.sum_congr rfl e5, ← Finset.mul_sum, Finset.sum_comm, mul_comm _ c, mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e2, ← Int.cast_sum, ← e4]
  push_cast
  rfl

private theorem card_transport {J A O C : Type} [Semiring A] [Semiring O] [Semiring C] {K K' : J → Type}
    [∀ j, Semiring (K j)] [∀ j, Semiring (K' j)] (e : ∀ j, K j →+* K' j) (he : ∀ j, Function.Bijective (e j))
    (φ : ∀ j, A →+* K j) (φ' : ∀ j, A →+* K' j) (c : ∀ j, O →+* K j) (c' : ∀ j, O →+* K' j)
    (hφ : ∀ j, φ' j = (e j).comp (φ j)) (hc : ∀ j, (e j).comp (c j) = c' j) (ι : A →+* C) (τ : O →+* C) :
    Nat.card {q : Σ j, (K' j →+* C) // q.2.comp (φ' q.1) = ι ∧ q.2.comp (c' q.1) = τ} =
      Nat.card {q : Σ j, (K j →+* C) // q.2.comp (φ q.1) = ι ∧ q.2.comp (c q.1) = τ} := by
  let e' := fun j => RingEquiv.ofBijective _ (he j)
  refine Nat.card_congr
    { toFun := fun q => ⟨⟨q.1.1, q.1.2.comp (e q.1.1)⟩, ?_, ?_⟩
      invFun := fun q => ⟨⟨q.1.1, q.1.2.comp (e' q.1.1).symm.toRingHom⟩, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [RingHom.comp_assoc, ← hφ]
    exact q.2.1
  · rw [RingHom.comp_assoc, hc]
    exact q.2.2
  · refine Eq.trans ?_ q.2.1
    rw [hφ]
    ext x
    exact congrArg q.1.2 ((e' q.1.1).symm_apply_apply _)
  · refine Eq.trans ?_ q.2.2
    rw [← hc]
    ext x
    exact congrArg q.1.2 ((e' q.1.1).symm_apply_apply _)
  · rintro ⟨⟨j, a⟩, h⟩
    refine Subtype.ext (Sigma.ext rfl (heq_of_eq ?_))
    ext x
    exact congrArg a ((e' j).apply_symm_apply x)
  · rintro ⟨⟨j, a⟩, h⟩
    refine Subtype.ext (Sigma.ext rfl (heq_of_eq ?_))
    ext x
    exact congrArg a ((e' j).symm_apply_apply x)

private theorem over_of_notMem_gen {F : Type} [Field F] [NumberField F] {Y : Var F} {v : HeightOneSpectrum (𝓞 F)}
    {F' : Type} [Field F'] {ε : F →+* F'} {O : ValuationSubring F'} [IsDiscreteValuationRing O] {b : 𝓞 F →+* O}
    (hb : IsUp v ε O b) {T : Vert.Model O} {Q : TrueGeo.Model Y} {g : T.X ⟶ Q.X}
    (hg : g ≫ Q.p = T.str ≫ spMap b) {ζ : T.X} (hζ : ζ ∉ T.gen) : (Q.p (g ζ)).asIdeal = v.asIdeal := by
  have h1 : T.str ζ = closedPoint O := not_not.1 (mt Vert.Model.mem_gen.2 hζ)
  have h2 : Q.p (g ζ) = spMap b (T.str ζ) := by
    rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]
  rw [h2, h1]
  ext x
  exact (hb.2 x).symm

private theorem notMem_gen_of_mult {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {T : Vert.Model O} (P : VertDiv T) (t : P.M.ι → T.X.functionFieldˣ) (ht : IsRatSec P.M t) (h : IsSecOf P t)
    {ζ : T.X} (hζ : (divOfRatSec P.isLB ht).mult ζ ≠ 0) : ζ ∉ T.gen := by
  intro hg
  obtain ⟨i, hi⟩ := exists_chart P.isLB ζ
  apply hζ
  rw [((presents_divOfRatSec P.isLB ht).isEqn i ζ hi).mult_eq, h i (gen_mem (memInf hg hi))]
  exact (unitAt_fnOf (memInf hg hi) _ (P.isUnit i).unit).ord_eq_zero

private theorem ord_eq_of_unitAt {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {x : X}
    {a c : X.functionField} (ha : a ≠ 0) (hc : c ≠ 0) {m : ℕ} (h : UnitAt x (a ^ m / c)) :
    Scheme.ord c x = (m : ℤ) * Scheme.ord a x := by
  rw [← VertOrd.ord_pow' ha, ← div_mul_cancel₀ (a ^ m) hc, Scheme.ord_mul h.ne_zero hc, h.ord_eq_zero, zero_add]

private theorem onT (F : Type) [Field F] [NumberField F] (Y : Var F) (v : HeightOneSpectrum (𝓞 F)) (p : ℕ)
    [Fact p.Prime] (hp : (p : 𝓞 F) ∈ v.asIdeal) (F' : Type) [Field F'] [NumberField F'] (ε : F →+* F')
    (O : ValuationSubring F') [IsDiscreteValuationRing O] [CharP (ResidueField O) p] [Finite (ResidueField O)]
    (b : 𝓞 F →+* O) (hb : IsUp v ε O b) (σ : F' →+* ℂ) (Q : TrueGeo.Model Y) [IsIntegral Q.X]
    [IsLocallyNoetherian Q.X] (hQ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Q.X) (d : ℕ) (hd : Y.dim = d) (m : ℕ)
    (M : LB Q.X) (hM : M.IsLB) (r : M.ι → Q.X.functionFieldˣ) (hr : IsRatSec M r) (l₀ : Ext v → AlgPt Y → ℝ)
    (hl₀ : GReads Q v M r (fun e y => (m : ℝ) * l₀ e y)) (N : Fin d → LB Q.X) (hN : ∀ k, (N k).IsLB)
    (s : ∀ k, (N k).ι → Q.X.functionFieldˣ) (l : Fin d → Ext v → AlgPt Y → ℝ)
    (hl : ∀ k, GReads Q v (N k) (s k) (fun e y => (m : ℝ) * l k e y)) (J : Type) [Fintype J]
    (B : J → Vert.Model O) (hB : ∀ j, GlobalTheory.IsNormalScheme (B j).X) (hBd : ∀ j, (B j).relDim = d)
    (μ : ∀ j, Match Y b (B j)) (g : ∀ j, (B j).X ⟶ Q.X)
    (hg : ∀ j, g j (genericPoint (B j).X) ⤳ genericPoint Q.X) (hE : ∀ j, Extends (μ j) Q (g j))
    (n : ℕ) (hn : 0 < n) (hc : Count μ ε σ n) (P : ∀ j, VertDiv (B j))
    (t : ∀ j, (P j).M.ι → (B j).X.functionFieldˣ) (hP : ∀ j, IsSecOf (P j) (t j))
    (ht : ∀ j, Reads (μ j) v (P j).M (t j) l₀) (L : ∀ j, Fin d → LB (B j).X) (hL : ∀ j k, (L j k).IsLB)
    (u : ∀ j k, (L j k).ι → (B j).X.functionFieldˣ) (hu : ∀ j k, Reads (μ j) v (L j k) (u j k) (l k)) :
    (m : ℝ) ^ (d + 1) * placeDeg p v * ∑ j, (((B j).capDeg_vp p (Vert.Model.toQ (P j).cls)
      (∏ k, Vert.c1 (L j k) (hL j k)) : ℚ) : ℝ) = (n : ℝ) * ∑ᶠ z : Q.X,
        if (Q.p z).asIdeal = v.asIdeal then (((divOfRatSec hM hr).mult z * pdeg p N z : ℤ) : ℝ) else 0 := by
  have : IsProper Q.p := (isProper_and_exists_isAmpleLB_of_isProjOver Q.ar.isProjOver).1
  have : CompactSpace Q.X := QuasiCompact.compactSpace_of_compactSpace Q.p
  have he : (ramIdx O p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Vert.ramIdx_ne_zero O p)
  have hf : (resDeg O p : ℝ) ≠ 0 := by
    letI := ZMod.algebra (ResidueField O) p
    exact Nat.cast_ne_zero.2 (Module.finrank_pos (R := ZMod p) (M := ResidueField O)).ne'
  have key := comb (fun j => g j) (fun j => (divOfRatSec (P j).isLB (ht j).1).mult) (fun j => pdeg p (L j))
    (fun j ζ => ((g j).residueDegree ζ : ℤ)) (fun j => CartierDiv.finite_support_mult _)
    (divOfRatSec hM hr).mult (pdeg p N) (CartierDiv.finite_support_mult _)
    (fun z => (Q.p z).asIdeal = v.asIdeal) (fun z => Order.coheight z = 1) (placeDeg p v)
    ((n : ℝ) * ((ramIdx O p : ℝ) * (resDeg O p : ℝ))) m d
    (fun j ζ h => over_of_notMem_gen hb (hE j).2 (notMem_gen_of_mult _ _ _ (hP j) h))
    (fun j ζ h => by
      have hζ := notMem_gen_of_mult _ _ _ (hP j) h
      rw [← UpperTheory.pdeg_smul_power O p (B j) d m (L j) (fun k => (N k).pull (g j)) (hL j)
        (fun k => LB.isLB_pull (hN k) (g j)) (fun k => UpperTheory.pull_class_rational_power _ _ (g j) (hg j) (L j k) (hL j k) (u j k)
          (N k) (hN k) (s k) m (hu j k).1 (hl k).1 (UpperTheory.unitAt_pow_div_fnMap_of_reads_of_gReads F Y v p hp F' ε O b hb (B j) (hB j) (μ j) Q
            (g j) (hg j) (hE j) (L j k) (hL j k) (u j k) (N k) (hN k) (s k) (l k) m (hu j k) (hl k))) ζ hζ]
      convert UpperTheory.vertical_model_dimension_match F Y v p hp F' ε O b hb (B j) d hd (hBd j) Q (g j) (hE j).2 N hN ζ hζ
        (CartierDiv.coheight_eq_one_of_mult_ne_zero h))
    (fun η h => CartierDiv.coheight_eq_one_of_mult_ne_zero h)
    (fun η hη hη' => by
      obtain ⟨i', hi'⟩ := exists_chart hM η
      rw [((presents_divOfRatSec hM hr).isEqn i' η hi').mult_eq,
        ← UpperTheory.normal_model_complex_compat F Y v p hp F' ε O b hb σ Q hQ J B hB (fun j => (hBd j).trans hd.symm) μ g hg hE n hn hc η
          hη hη' (r i') (r i').ne_zero]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      refine finsum_congr fun ζ => ?_
      by_cases h : g j ζ = η
      · rw [if_pos h, if_pos h]
        obtain ⟨i, hi⟩ := exists_chart (P j).isLB ζ
        rw [((presents_divOfRatSec (P j).isLB (ht j).1).isEqn i ζ hi).mult_eq,
          ord_eq_of_unitAt (t j i).ne_zero ((map_ne_zero _).2 (r i').ne_zero)
          (UpperTheory.unitAt_pow_div_fnMap_of_reads_of_gReads F Y v p hp F' ε O b hb (B j) (hB j) (μ j) Q
            (g j) (hg j) (hE j) (P j).M (P j).isLB (t j) M hM r l₀ m (ht j) hl₀ ζ i i' hi (h ▸ hi'))]
      · rw [if_neg h, if_neg h])
  have e : ∀ j, ((∑ᶠ ζ, (divOfRatSec (P j).isLB (ht j).1).mult ζ * pdeg p (L j) ζ : ℤ) : ℝ) =
      (((B j).capDeg_vp p (Vert.Model.toQ (P j).cls) (∏ k, Vert.c1 (L j k) (hL j k)) : ℚ) : ℝ) *
        ((ramIdx O p : ℝ) * (resDeg O p : ℝ)) := by
    intro j
    have h := congrArg (Rat.cast : ℚ → ℝ)
      (UpperTheory.vertical_degree_rational_section O p (B j) (hB j) d (hBd j) (P j) (t j) (ht j).1 (hP j) (L j) (hL j))
    rw [Rat.cast_intCast] at h
    rw [← h, Vert.Model.capDeg_vp_toQ]
    push_cast
    field_simp
  simp only [e] at key
  rw [← Finset.sum_mul] at key
  refine mul_right_cancel₀ (mul_ne_zero he hf) ?_
  rw [mul_assoc _ _ (_ * _), key, mul_right_comm]
  congr!

theorem UpperTheory.normal_model_complex_compat_alt :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime], (p : 𝓞 F) ∈ v.asIdeal → ∀ (F' : Type) [Field F'] [NumberField F'] (ε : F →+* F') (O : ValuationSubring F') [IsDiscreteValuationRing O] [CharP (ResidueField O) p] (b : 𝓞 F →+* O), IsUp v ε O b → ∀ (σ : F' →+* ℂ) (Q : TrueGeo.Model Y) [IsIntegral Q.X] [IsLocallyNoetherian Q.X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Q.X → ∀ (d : ℕ), Y.dim = d → ∀ (m : ℕ) (M : LB Q.X) (hM : M.IsLB) (r : M.ι → Q.X.functionFieldˣ) (hr : IsRatSec M r) (l₀ : Ext v → AlgPt Y → ℝ), GReads Q v M r (fun e y => (m : ℝ) * l₀ e y) → ∀ (N : Fin d → LB Q.X), (∀ k, (N k).IsLB) → ∀ (s : ∀ k, (N k).ι → Q.X.functionFieldˣ) (l : Fin d → Ext v → AlgPt Y → ℝ), (∀ k, GReads Q v (N k) (s k) (fun e y => (m : ℝ) * l k e y)) → ∀ (J : Type) [Fintype J] (B : J → Vert.Model O), (∀ j, GlobalTheory.IsNormalScheme (B j).X) → (∀ j, (B j).relDim = d) → ∀ (μ : ∀ j, Match Y b (B j)) (n : ℕ), 0 < n → Count μ ε σ n → ∀ (P : ∀ j, VertDiv (B j)) (t : ∀ j, (P j).M.ι → (B j).X.functionFieldˣ), (∀ j, IsSecOf (P j) (t j)) → (∀ j, Reads (μ j) v (P j).M (t j) l₀) → ∀ (L : ∀ j, Fin d → LB (B j).X) (hL : ∀ j k, (L j k).IsLB) (u : ∀ j k, (L j k).ι → (B j).X.functionFieldˣ), (∀ j k, Reads (μ j) v (L j k) (u j k) (l k)) → (m : ℝ) ^ (d + 1) * placeDeg p v * ∑ j, (((B j).capDeg_vp p (Vert.Model.toQ (P j).cls) (∏ k, Vert.c1 (L j k) (hL j k)) : ℚ) : ℝ) = (n : ℝ) * ∑ᶠ z : Q.X, if (Q.p z).asIdeal = v.asIdeal then (((divOfRatSec hM hr).mult z * pdeg p N z : ℤ) : ℝ) else 0 := by
  intro F _ _ Y v p _ hp F' _ _ ε O _ _ b hb σ Q _ _ hQ d hd m M hM r hr l₀ hl₀ N hN s l hl J _ B hB hBd μ n hn hc
    P t hP ht L hL u hu
  have hfin : Finite (ResidueField O) := by
    refine (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField O (Fact.out : p.Prime).ne_zero ?_).2
    have h : ((p : ℕ) : O) ∈ maximalIdeal O := by
      have := (hb.2 p).1 hp
      rwa [map_natCast] at this
    have := O.coe_mem_nonunits_iff.2 h
    simpa using this
  choose T f μ' g hf f' hT hf0 hf1 hbij hφ h1 h2 hE hg using fun j => UpperTheory.exists_normal_vertical_model F Y O b (B j) (μ j) Q
  have hpb := fun j => UpperTheory.vertical_model_match_compat F Y O b (B j) (T j) (μ j) (μ' j) (f j) (hf j) (f' j) (h1 j) (h2 j)
  have hc' : Count μ' ε σ n := fun ι hι =>
    (card_transport (fun j => SmallSec.fnMap (f j).f (hf j)) hbij (fun j => (μ j).φ) (fun j => (μ' j).φ)
      (fun j => cst (B j)) (fun j => cst (T j)) hφ (fun j => (hpb j).2.2) ι _).trans (hc ι hι)
  have key := onT F Y v p hp F' ε O b hb σ Q hQ d hd m M hM r hr l₀ hl₀ N hN s l hl J T hT
    (fun j => by rw [← (f j).relDim_add, hf0, hBd, add_zero]) μ' g hg hE n hn hc'
    (fun j => (P j).pull (f j).comp_str) _ (fun j => (hpb j).2.1 (P j) (t j) (hP j))
    (fun j => (hpb j).1 v (P j).M (t j) l₀ (ht j)) (fun j k => (L j k).pull (f j).f)
    (fun j k => LB.isLB_pull (hL j k) (f j).f) _ (fun j k => (hpb j).1 v (L j k) (u j k) (l k) (hu j k))
  rw [← key]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h := (GlobalTheory.VertDegProj.capDeg_vp_vPullQ O p (B j) (hB j) (T j) (f j) (hf0 j)).2
    (Vert.Model.toQ (P j).cls) (∏ k, Vert.c1 (L j k) (hL j k))
  rw [hf1, one_mul, Vert.Model.vPullQ_toQ, ← VertDiv.cls_pull, map_prod] at h
  rw [← h]
  simp only [pullback_firstChern (f j).f (hL j _) (LB.isLB_pull (hL j _) (f j).f)]
