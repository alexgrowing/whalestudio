import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory
open IsDedekindDomain GlobalTheory.SelfDualGenus
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.IsomModN

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_approx_int {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (c : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) :
    ∃ s : 𝓞 K, ∀ v : HeightOneSpectrum (𝓞 K), ∃ a : v.adicCompletionIntegers K,
      c v = algebraMap (𝓞 K) _ s + n • a := by
  let y : FiniteAdeleRing (𝓞 K) K :=
    ⟨fun v => (c v : v.adicCompletion K), Filter.Eventually.of_forall fun v => (c v).2⟩
  obtain ⟨s, a, ha, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat K n hn).2 y fun v => (c v).2
  refine ⟨s, fun v => ⟨⟨a v, ha v⟩, Subtype.ext ?_⟩⟩
  exact congrArg (fun t : FiniteAdeleRing (𝓞 K) K => t v) h

def vec (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) : (Fin r → E) →+ (Fin r → LocAlg v) where
  toFun x := fun i => locEmb v (x i)
  map_zero' := funext fun _ => map_zero _
  map_add' _ _ := funext fun _ => map_add _ _ _

theorem vec_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) {L : Submodule (𝓞 E) (Fin r → E)} {x : Fin r → E} (hx : x ∈ L) :
    vec v x ∈ locLattice v L := Submodule.subset_span ⟨x, hx, rfl⟩

theorem vec_smul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (c : 𝓞 E) (x : Fin r → E) :
    vec v (c • x) = locEmb v c • vec v x := funext fun _ => map_mul (locEmb v) _ _

theorem vec_smul_real (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (s : 𝓞 (maximalRealSubfield E)) (x : Fin r → E) :
    vec v (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x) = algebraMap (𝓞 (maximalRealSubfield E)) (v.adicCompletionIntegers (maximalRealSubfield E)) s • vec v x := by
  rw [vec_smul, locEmb_algebraMap, algebraMap_smul]

theorem exists_approx {L : Submodule (𝓞 E) (Fin r → E)} (hL : L.FG) {n : ℕ} (hn : 0 < n)
    (z : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Fin r → LocAlg v) (hz : ∀ v, z v ∈ locLattice v L) :
    ∃ b ∈ L, ∀ v, ∃ u ∈ locLattice v L, z v = vec v b + n • u := by
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨m, t, ht⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  have h1 : ∀ v, z v ∈ Submodule.span (v.adicCompletionIntegers (maximalRealSubfield E)) (Set.range fun i => vec v (t i : Fin r → E)) := by
    intro v
    refine (Submodule.span_le.2 ?_ : locLattice v L ≤ _) (hz v)
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (⟨x, hx⟩ : L) ∈ Submodule.span ℤ (Set.range t) := ht ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx'
    have e : x = ∑ i, c i • (t i : Fin r → E) := by
      have := congrArg Subtype.val hc
      simpa using this.symm
    change vec v x ∈ _
    rw [e, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  choose c hc using fun v => (Submodule.mem_span_range_iff_exists_fun _).1 (h1 v)
  choose s hs using fun i => exists_approx_int hn (fun v => c v i)
  refine ⟨∑ i, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (s i) • (t i : Fin r → E),
    L.sum_mem fun i _ => L.smul_mem _ (t i).2, fun v => ?_⟩
  choose a ha using fun i => hs i v
  refine ⟨∑ i, a i • vec v (t i : Fin r → E),
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (vec_mem v (t i).2), ?_⟩
  rw [← hc v, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ha i, vec_smul_real, add_smul, smul_assoc]

theorem exists_div {L : Submodule (𝓞 E) (Fin r → E)} (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) {n : ℕ} (hn : 0 < n)
    {x : Fin r → E} (hx : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ u ∈ locLattice v L, vec v x = n • u) :
    ∃ y ∈ L, x = n • y := by
  have hn' : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  refine ⟨(n : E)⁻¹ • x, (mem_iff_forall_mem_locLattice hL _).2 fun v => ?_, ?_⟩
  · obtain ⟨u, hu, e⟩ := hx v
    convert hu using 1
    funext i
    have := congrFun e i
    change locEmb v (x i) = n • u i at this
    change locEmb v ((n : E)⁻¹ * x i) = u i
    rw [map_mul, this, nsmul_eq_mul, ← mul_assoc, ← map_natCast (locEmb v), ← map_mul,
      inv_mul_cancel₀ hn', map_one, one_mul]
  · rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hn', one_smul]

def rel (L L' : Submodule (𝓞 E) (Fin r → E)) (γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Matrix (Fin r) (Fin r) (LocAlg v))
    (n : ℕ) : Submodule (𝓞 E) (L × L') where
  carrier := {p | ∀ v, ∃ u ∈ locLattice v L',
    γ v *ᵥ vec v (p.1 : Fin r → E) = vec v (p.2 : Fin r → E) + n • u}
  zero_mem' := fun v => ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    intro p q hp hq v
    obtain ⟨w, hw, hp⟩ := hp v
    obtain ⟨w', hw', hq⟩ := hq v
    refine ⟨w + w', add_mem hw hw', ?_⟩
    simp only [Prod.snd_add, Prod.fst_add, Submodule.coe_add, map_add, Matrix.mulVec_add, hp, hq, smul_add]
    abel
  smul_mem' := by
    intro c p hp v
    obtain ⟨w, hw, hp⟩ := hp v
    refine ⟨_, smul_mem_locLattice v (locEmb_mem_locOrder v c) hw, ?_⟩
    simp only [Prod.smul_snd, Prod.smul_fst, Submodule.coe_smul, vec_smul, Matrix.mulVec_smul, hp, smul_add]
    rw [smul_comm]

theorem exists_linear_approx {L L' : Submodule (𝓞 E) (Fin r → E)} (hL : L.FG) (hL' : L'.FG) {n : ℕ}
    (hn : 0 < n) (γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Matrix (Fin r) (Fin r) (LocAlg v))
    (hγ : ∀ v, ∀ x ∈ locLattice v L, γ v *ᵥ x ∈ locLattice v L') :
    ∃ f : L →ₗ[𝓞 E] L', ∀ a : L, ∀ v, ∃ u ∈ locLattice v L',
      γ v *ᵥ vec v (a : Fin r → E) = vec v (f a : Fin r → E) + n • u := by
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  haveI : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  have hsurj : Function.Surjective ((LinearMap.fst (𝓞 E) L L').comp (rel L L' γ n).subtype) := by
    intro a
    obtain ⟨b, hb, h⟩ := exists_approx hL' hn (fun v => γ v *ᵥ vec v (a : Fin r → E))
      fun v => hγ v _ (vec_mem v a.2)
    exact ⟨⟨(a, ⟨b, hb⟩), h⟩, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hsurj
  refine ⟨(LinearMap.snd (𝓞 E) L L').comp ((rel L L' γ n).subtype.comp s), fun a v => ?_⟩
  obtain ⟨w, hw, e⟩ := (s a).2 v
  have ha : (s a).1.1 = a := LinearMap.congr_fun hs a
  rw [ha] at e
  exact ⟨w, hw, e⟩

def hermLoc (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → LocAlg v) : LocAlg v :=
  x ᵥ* G.map (locEmb v) ⬝ᵥ fun i => locConj v (y i)

section Herm

variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (G : Matrix (Fin r) (Fin r) E)

theorem hermLoc_vec (x y : Fin r → E) : hermLoc v G (vec v x) (vec v y) = locEmb v (herm G x y) := by
  rw [herm_eq_dotProduct, RingHom.map_dotProduct, hermLoc]
  congr 1
  funext i
  exact (RingHom.map_vecMul (locEmb v) G x i).symm

theorem hermLoc_add_left (x x' y : Fin r → LocAlg v) :
    hermLoc v G (x + x') y = hermLoc v G x y + hermLoc v G x' y := by
  simp only [hermLoc, Matrix.add_vecMul, add_dotProduct]

theorem hermLoc_add_right (x y y' : Fin r → LocAlg v) :
    hermLoc v G x (y + y') = hermLoc v G x y + hermLoc v G x y' := by
  simp only [hermLoc, dotProduct, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hermLoc_smul_left (c : v.adicCompletionIntegers (maximalRealSubfield E)) (x y : Fin r → LocAlg v) :
    hermLoc v G (c • x) y = c • hermLoc v G x y := by
  simp only [hermLoc, Matrix.smul_vecMul, smul_dotProduct]

theorem hermLoc_smul_right (c : v.adicCompletionIntegers (maximalRealSubfield E)) (x y : Fin r → LocAlg v) :
    hermLoc v G x (c • y) = c • hermLoc v G x y := by
  simp only [hermLoc, dotProduct, Pi.smul_apply, Algebra.smul_def, map_mul, locConj_algebraMap',
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem hermLoc_nsmul_left (n : ℕ) (x y : Fin r → LocAlg v) :
    hermLoc v G (n • x) y = n • hermLoc v G x y := by
  rw [← Nat.cast_smul_eq_nsmul (v.adicCompletionIntegers (maximalRealSubfield E)), hermLoc_smul_left, Nat.cast_smul_eq_nsmul]

theorem hermLoc_nsmul_right (n : ℕ) (x y : Fin r → LocAlg v) :
    hermLoc v G x (n • y) = n • hermLoc v G x y := by
  rw [← Nat.cast_smul_eq_nsmul (v.adicCompletionIntegers (maximalRealSubfield E)), hermLoc_smul_right, Nat.cast_smul_eq_nsmul]

theorem hermLoc_mulVec {G' : Matrix (Fin r) (Fin r) E} {γ : Matrix (Fin r) (Fin r) (LocAlg v)}
    (h : G'.map (locEmb v) = γᵀ * G.map (locEmb v) * γ.map (locConj v)) (x y : Fin r → LocAlg v) :
    hermLoc v G (γ *ᵥ x) (γ *ᵥ y) = hermLoc v G' x y := by
  have : (fun i => locConj v ((γ *ᵥ y) i)) = γ.map (locConj v) *ᵥ fun i => locConj v (y i) :=
    funext fun i => RingHom.map_mulVec (locConj v) γ y i
  rw [hermLoc, hermLoc, this, h, Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem hermLoc_mem {L : Submodule (𝓞 E) (Fin r → E)} {M : Submodule (𝓞 E) (Fin 1 → E)}
    (h : ∀ x ∈ L, ∀ y ∈ L, (fun _ => herm G x y) ∈ M) {x y : Fin r → LocAlg v}
    (hx : x ∈ locLattice v L) (hy : y ∈ locLattice v L) :
    (fun _ => hermLoc v G x y) ∈ locLattice v M := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      convert vec_mem v (h x hx y hy) using 2
      exact hermLoc_vec v G x y
    | zero =>
      convert zero_mem (locLattice v M) using 2
      simp [hermLoc]
    | add y z _ _ hy hz =>
      convert add_mem hy hz using 2
      exact hermLoc_add_right v G _ y z
    | smul c y _ hy =>
      convert Submodule.smul_mem _ c hy using 2
      exact hermLoc_smul_right v G c _ y
  | zero =>
    convert zero_mem (locLattice v M) using 2
    simp [hermLoc]
  | add x z _ _ hx hz =>
    convert add_mem hx hz using 2
    exact hermLoc_add_left v G x z y
  | smul c x _ hx =>
    convert Submodule.smul_mem _ c hx using 2
    exact hermLoc_smul_left v G c x y

end Herm

theorem exists_isometry_mod {G G' : Matrix (Fin r) (Fin r) E} {L L' : Submodule (𝓞 E) (Fin r → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L') {M : Submodule (𝓞 E) (Fin 1 → E)}
    (hM : ReciprocityTheory.MultiplicativeHeights.IsLattice M) (h : ∀ x ∈ L', ∀ y ∈ L', (fun _ => herm G' x y) ∈ M)
    (hγ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ γ, IsLocalIsometry v G' L' G L γ) {n : ℕ} (hn : 0 < n) :
    ∃ f : L →ₗ[𝓞 E] L', ((∀ a, (∃ e, f a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f a + n • e) ∧
      ∀ a a' : L, ∃ m ∈ M, herm G' (f a) (f a') - herm G a a' = n • m 0 := by
  choose γ hγ using hγ
  obtain ⟨f, hf⟩ := exists_linear_approx hL.1 hL'.1 hn (fun v => (γ v).1) fun v x hx => ((hγ v).2 x).1 hx
  have hinv : ∀ v (x : Fin r → LocAlg v), (γ v).1 *ᵥ (((γ v)⁻¹).1 *ᵥ x) = x := fun v x => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hinv' : ∀ v (x : Fin r → LocAlg v), ((γ v)⁻¹).1 *ᵥ ((γ v).1 *ᵥ x) = x := fun v x => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hback : ∀ v, ∀ x ∈ locLattice v L', ((γ v)⁻¹).1 *ᵥ x ∈ locLattice v L := fun v x hx =>
    ((hγ v).2 _).2 (by rwa [hinv])
  refine ⟨f, ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩, fun a a' => ?_⟩
  · rintro ⟨e, he⟩
    obtain ⟨y, hy, e⟩ := exists_div hL hn (x := a) fun v => by
      obtain ⟨u, hu, eu⟩ := hf a v
      refine ⟨_, hback v _ (add_mem (vec_mem v e.2) hu), ?_⟩
      rw [← Matrix.mulVec_smul, ← hinv' v (vec v a), eu, he, Submodule.coe_smul_of_tower, map_nsmul, smul_add]
    exact ⟨⟨y, hy⟩, Subtype.ext e⟩
  · rintro ⟨e, rfl⟩
    exact ⟨f e, map_nsmul _ _ _⟩
  · obtain ⟨b, hb, h1⟩ := exists_approx hL.1 hn (fun v => ((γ v)⁻¹).1 *ᵥ vec v (a' : Fin r → E))
      fun v => hback v _ (vec_mem v a'.2)
    obtain ⟨y, hy, e⟩ := exists_div hL' hn (x := a' - f ⟨b, hb⟩) fun v => by
      obtain ⟨u, hu, eu⟩ := hf ⟨b, hb⟩ v
      obtain ⟨w, hw, ew⟩ := h1 v
      refine ⟨_, add_mem hu (((hγ v).2 _).1 hw), ?_⟩
      rw [map_sub, ← hinv v (vec v a'), ew, Matrix.mulVec_add, eu, Matrix.mulVec_smul, smul_add]
      abel
    exact ⟨⟨b, hb⟩, ⟨y, hy⟩, Subtype.ext (sub_eq_iff_eq_add'.1 e)⟩
  · obtain ⟨m, hm, e⟩ := exists_div hM hn (x := fun _ => herm G' (f a) (f a') - herm G a a') fun v => by
      obtain ⟨u, hu, eu⟩ := hf a v
      obtain ⟨u', hu', eu'⟩ := hf a' v
      have hγa := ((hγ v).2 _).1 (vec_mem v a'.2)
      refine ⟨_, neg_mem (add_mem (hermLoc_mem v G' h (vec_mem v (f a).2) hu')
        (hermLoc_mem v G' h hu hγa)), funext fun i => ?_⟩
      change locEmb v (herm G' (f a) (f a') - herm G a a') = n • -(hermLoc v G' (vec v (f a)) u' +
        hermLoc v G' u ((γ v).1 *ᵥ vec v a'))
      rw [map_sub, ← hermLoc_vec, ← hermLoc_vec, ← hermLoc_mulVec v G' (hγ v).1, eu, hermLoc_add_left,
        hermLoc_nsmul_left]
      conv_lhs => rw [eu', hermLoc_add_right, hermLoc_nsmul_right, ← eu']
      rw [smul_neg, smul_add]
      abel
    exact ⟨m, hm, congrFun e 0⟩

omit [IsCMField E] in

theorem isLattice_ideal {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (Submodule.pi Set.univ fun _ : Fin 1 => (I : Submodule (𝓞 E) E)) := by
  refine ⟨Submodule.fg_pi fun _ => FractionalIdeal.fg_of_isNoetherianRing le_rfl I, ?_⟩
  obtain ⟨m, hm, hm0⟩ : ∃ m ∈ I, m ≠ 0 := by
    by_contra h
    push Not at h
    exact hI (FractionalIdeal.eq_zero_iff.2 h)
  refine eq_top_iff.2 fun z _ => ?_
  have : z = (z 0 / m) • fun _ : Fin 1 => m := by
    funext i
    rw [Subsingleton.elim i 0]
    simp [hm0]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span fun _ _ => hm)

end GlobalTheory.IsomModN
