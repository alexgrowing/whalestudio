import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.EigenLatDifferent
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjSumSumEmbeddingsEqTrace
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.GeneralBFactThird

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.EigLat

open NumberField GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [NumberField K] {N : ℕ}

open Classical in

theorem sum_dual_mul (σ τ : E →+* K) :
    ∑ k, σ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) = if τ = σ then 1 else 0 := by
  let ρ : 𝓞 E →+* Module.End K K :=
    (Algebra.lmul K K).toRingHom.comp (τ.comp (algebraMap (𝓞 E) E))
  have hρ : ∀ (a : 𝓞 E) (z : K), ρ a z = τ (a : E) * z := fun a z => rfl
  have hmem : (1 : K) ∈ HT.eigSp ρ τ := HT.LatBasic.mem_eigSp.2 fun a => by
    rw [hρ, smul_eq_mul]
  have hP : HT.eigProj ρ σ 1 =
      ∑ k, σ (HT.dualInt E k) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) := by
    simp [HT.eigProj, LinearMap.sum_apply, hρ]
  rw [← hP]
  split_ifs with h
  · subst h
    exact HT.LatBasic.eigProj_of_mem hmem
  · exact HT.LatBasic.eigProj_of_ne (Ne.symm h) hmem

theorem card_embeddings [Fintype (E →+* K)] (ι : K →+* ℂ)
    (h : ∀ σ : E →+* ℂ, ∃ t : E →+* K, ι.comp t = σ) :
    Fintype.card (E →+* K) = Module.finrank ℚ E := by
  classical
  rw [← Embeddings.card E ℂ]
  refine Fintype.card_of_bijective (f := fun t : E →+* K => ι.comp t) ⟨fun a b hab => ?_, h⟩
  ext x
  exact ι.injective (DFunLike.congr_fun hab x)

def diffIm (s : E →+* K) : Submodule (𝓞 K) K :=
  Submodule.span (𝓞 K) ((fun x : 𝓞 E => s (x : E)) '' (differentIdeal ℤ (𝓞 E) : Set (𝓞 E)))

variable (E K) in

def intLat : Submodule (𝓞 K) ((E →+* K) → K) :=
  Submodule.span (𝓞 K) (Set.range fun (b : 𝓞 E) (σ : E →+* K) => σ (b : E))

def pair [Fintype (E →+* K)] (y : E) : ((E →+* K) → K) →ₗ[𝓞 K] K where
  toFun v := ∑ σ, σ y * v σ
  map_add' u v := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, mul_smul_comm]

theorem pair_mem [Fintype (E →+* K)] (hc : Fintype.card (E →+* K) = Module.finrank ℚ E) {y : E}
    (hy : y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) {v : (E →+* K) → K}
    (hv : v ∈ intLat E K) : pair y v ∈ LinearMap.range (Algebra.linearMap (𝓞 K) K) := by
  have hle : (intLat E K).map (pair y) ≤ LinearMap.range (Algebra.linearMap (𝓞 K) K) := by
    rw [intLat, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    have h1 := (FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))).1 hy (b : E)
      ((FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩)
    obtain ⟨n, hn⟩ := h1
    refine ⟨(n : 𝓞 K), ?_⟩
    have h2 : pair (K := K) y (fun σ : E →+* K => σ (b : E)) = ∑ σ : E →+* K, σ (y * b) := by
      simp [pair]
    rw [h2, HT.projSum_sum_embeddings_eq_trace K E hc]
    have h3 : Algebra.trace ℚ E (y * b) = (n : ℚ) := by
      rw [← Algebra.traceForm_apply, ← hn]; simp
    rw [h3]
    simp
  exact hle (Submodule.mem_map_of_mem hv)

theorem mem_diffIm_of_single_mem [Fintype (E →+* K)] [DecidableEq (E →+* K)]
    (hc : Fintype.card (E →+* K) = Module.finrank ℚ E) (s : E →+* K) {w : K}
    (hw : Pi.single s w ∈ intLat E K) : w ∈ diffIm s := by
  have h0 : ∀ y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E),
      s y * w ∈ LinearMap.range (Algebra.linearMap (𝓞 K) K) := by
    intro y hy
    have := pair_mem hc hy hw
    have e : pair y (Pi.single s w : (E →+* K) → K) = s y * w := by
      simp [pair, Pi.single_apply]
    rwa [e] at this
  have h1 : (1 : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [HT.different_mul_dual_one]
    exact FractionalIdeal.one_mem_one _
  have h2 : s 1 * w ∈ diffIm s := by
    refine FractionalIdeal.mul_induction_on (C := fun z => s z * w ∈ diffIm s) h1 ?_ ?_
    · intro x hx y hy
      obtain ⟨x, hx0, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      obtain ⟨a, ha⟩ := h0 y hy
      have e : s ((algebraMap (𝓞 E) E x) * y) * w = a • s (x : E) := by
        have ha' : algebraMap (𝓞 K) K a = s y * w := ha
        rw [Algebra.smul_def, ha', map_mul]
        change s (x : E) * s y * w = _
        ring
      change s ((algebraMap (𝓞 E) E x) * y) * w ∈ diffIm s
      rw [e]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨x, hx0, rfl⟩)
    · intro x y hx hy
      rw [map_add, add_mul]
      exact add_mem hx hy
  simpa using h2

def tmap (φ : Fin N → E) : ((E →+* K) → Fin N → K) →ₗ[𝓞 K] ((E →+* K) → K) where
  toFun v σ := ∑ n, σ (φ n) * v σ n
  map_add' u v := by
    funext σ
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext σ
    simp [Finset.smul_sum, mul_smul_comm]

theorem tmap_gen (φ : Fin N → E) (u : Fin N → E) (σ : E →+* K) :
    tmap φ (fun (τ : E →+* K) a => τ (u a)) σ = σ (∑ n, u n * φ n) := by
  simp [tmap, mul_comm]

theorem tmap_single [DecidableEq (E →+* K)] (φ : Fin N → E) (s : E →+* K) (w : Fin N → K) :
    tmap φ (Pi.single s w : (E →+* K) → Fin N → K) = Pi.single s (∑ n, s (φ n) * w n) := by
  funext σ
  by_cases h : σ = s
  · subst h
    simp [tmap]
  · simp [tmap, Pi.single_apply, h]

theorem exists_smul_mem (I : Submodule (𝓞 E) (Fin N → E)) {v : Fin N → E}
    (hv : v ∈ Submodule.span E (I : Set (Fin N → E))) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ I :=
  by apply _root_.Bl.general_b_fact_third_alt.goal1 <;> assumption

theorem isUnit_end {M : Type} [AddCommGroup M] [Module E M] [Module (𝓞 E) M]
    [IsScalarTower (𝓞 E) E M] (a : (𝓞 E)⁰) :
    IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) M) a) := by
  have ha : algebraMap (𝓞 E) E (a : 𝓞 E) ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero a.2
  rw [Module.End.isUnit_iff]
  refine ⟨fun u v h => ?_, fun u => ⟨(algebraMap (𝓞 E) E (a : 𝓞 E))⁻¹ • u, ?_⟩⟩
  · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← algebraMap_smul E (a : 𝓞 E) u,
      ← algebraMap_smul E (a : 𝓞 E) v] at h
    exact smul_right_injective M ha h
  · rw [Module.algebraMap_end_apply, ← algebraMap_smul E (a : 𝓞 E), smul_smul,
      mul_inv_cancel₀ ha, one_smul]

theorem exists_extend (I : Submodule (𝓞 E) (Fin N → E)) (f : I →ₗ[𝓞 E] 𝓞 E) :
    ∃ φ : Fin N → E, ∀ y : I, ∑ n, (y : Fin N → E) n * φ n = ((f y : 𝓞 E) : E) := by
  let W : Submodule E (Fin N → E) := Submodule.span E (I : Set (Fin N → E))
  let incl : I →ₗ[𝓞 E] W :=
    { toFun := fun y => ⟨y, Submodule.subset_span y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : IsLocalizedModule (𝓞 E)⁰ incl :=
    { map_units := fun a => isUnit_end a
      surj := fun v => by
        obtain ⟨d, hd, hv⟩ := exists_smul_mem I v.2
        exact ⟨(⟨d • (v : Fin N → E), hv⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
      exists_of_eq := fun {x y} h =>
        ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext (congrArg (fun z : W => (z : Fin N → E)) h)⟩ }
  let g : I →ₗ[𝓞 E] E := (Algebra.linearMap (𝓞 E) E) ∘ₗ f
  let G : W →ₗ[𝓞 E] E := IsLocalizedModule.lift (𝓞 E)⁰ incl g (fun a => isUnit_end a)
  have hG : ∀ y : I, G (incl y) = g y := fun y =>
    LinearMap.congr_fun (IsLocalizedModule.lift_comp (𝓞 E)⁰ incl g (fun a => isUnit_end a)) y
  let GE : W →ₗ[E] E := LinearMap.extendScalarsOfIsLocalization (𝓞 E)⁰ E G
  obtain ⟨F, hF⟩ := LinearMap.exists_extend GE
  refine ⟨fun n => F (fun j => if n = j then 1 else 0), fun y => ?_⟩
  have h1 : F (y : Fin N → E) = ((f y : 𝓞 E) : E) := by
    have := LinearMap.congr_fun hF (incl y)
    exact this.trans (hG y)
  rw [← h1, LinearMap.pi_apply_eq_sum_univ F (y : Fin N → E)]
  rfl

theorem exists_dual_system (I : Submodule (𝓞 E) (Fin N → E)) (hI : I.FG) :
    ∃ (m : ℕ) (x : Fin m → I) (f : Fin m → I →ₗ[𝓞 E] 𝓞 E), ∀ y : I, ∑ i, f i y • x i = y := by
  haveI : Module.Finite (𝓞 E) I := Module.Finite.iff_fg.2 hI
  have htors : Submodule.torsion (𝓞 E) I = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨a, ha⟩
    have ha' : (a : 𝓞 E) • (y : I) = 0 := ha
    have h1 : (a : 𝓞 E) • ((y : I) : Fin N → E) = 0 := congrArg Subtype.val ha'
    have h2 : algebraMap (𝓞 E) E (a : 𝓞 E) • ((y : I) : Fin N → E) = 0 := by
      rw [algebraMap_smul]; exact h1
    rcases smul_eq_zero.1 h2 with h | h
    · exact absurd ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).1 h)
        (nonZeroDivisors.ne_zero a.2)
    · exact (Submodule.mem_bot _).2 (Subtype.ext h)
  haveI : Module.Flat (𝓞 E) I := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htors
  haveI := Module.finitePresentation_of_finite (𝓞 E) I
  haveI : Module.Projective (𝓞 E) I := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, p, hp⟩ := Module.Finite.exists_fin' (𝓞 E) I
  obtain ⟨h, hh⟩ := Module.projective_lifting_property p LinearMap.id hp
  refine ⟨m, fun i => p (Pi.single i 1), fun i => LinearMap.proj i ∘ₗ h, fun y => ?_⟩
  have e : p (h y) = y := LinearMap.congr_fun hh y
  conv_rhs => rw [← e, LinearMap.pi_apply_eq_sum_univ p (h y)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e2 : (fun j => if i = j then (1 : 𝓞 E) else 0) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [e2]
  rfl

theorem smul_mem_diffLat {s : E →+* K} {I : Submodule (𝓞 E) (Fin N → E)} {d : K} (hd : d ∈ diffIm s)
    {x : Fin N → E} (hx : x ∈ I) : d • (fun a => s (x a)) ∈ diffLat s I := by
  induction hd using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨e, he, rfl⟩ := hz
    refine Submodule.subset_span ⟨(e : E) • x, ⟨e, he, x, hx, rfl⟩, ?_⟩
    funext a
    simp
  | zero => simp
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | smul c a _ ha =>
    rw [smul_assoc]
    exact Submodule.smul_mem _ c ha

theorem eigenLat_le [Fintype (E →+* K)] (hc : Fintype.card (E →+* K) = Module.finrank ℚ E)
    (I : Submodule (𝓞 E) (Fin N → E)) (hI : I.FG) (s : E →+* K) :
    eigenLat I s ≤ diffLat s I := by
  classical
  intro w hw
  have hw' : (Pi.single s w : (E →+* K) → Fin N → K) ∈ baseChangeLat K I := hw
  obtain ⟨m, x, f, hxf⟩ := exists_dual_system I hI
  choose φ hφ using fun i => exists_extend I (f i)
  have hT : ∀ i, ∀ v ∈ baseChangeLat K I, tmap (φ i) v ∈ intLat E K := by
    intro i v hv
    have hle : (baseChangeLat K I).map (tmap (φ i)) ≤ intLat E K := by
      rw [baseChangeLat, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨f i ⟨u, hu⟩, ?_⟩
      funext σ
      rw [tmap_gen, hφ i ⟨u, hu⟩]
    exact hle (Submodule.mem_map_of_mem hv)
  have hrec : ∀ v ∈ baseChangeLat K I,
      v s = ∑ i, (tmap (φ i) v s) • (fun a => s ((x i : Fin N → E) a)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨u, hu, rfl⟩ := hv
      funext a
      have e := congrArg (fun z : I => s ((z : Fin N → E) a)) (hxf ⟨u, hu⟩)
      simp only [Submodule.coe_sum, Finset.sum_apply, map_sum] at e
      simp only [tmap_gen, hφ _ ⟨u, hu⟩ , Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← e]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← map_mul, Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def]
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib, ← ha, ← hb]
    | smul c a _ ha =>
      simp only [map_smul, Pi.smul_apply, smul_assoc, ← Finset.smul_sum, ← ha]
  have hsum := hrec _ hw'
  simp only [tmap_single, Pi.single_eq_same] at hsum
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ => smul_mem_diffLat ?_ (x i).2
  refine mem_diffIm_of_single_mem hc s ?_
  rw [← tmap_single]
  exact hT i _ hw'

theorem diffLat_le [Fintype (E →+* K)] (I : Submodule (𝓞 E) (Fin N → E)) (s : E →+* K) :
    diffLat s I ≤ eigenLat I s := by
  classical
  rw [diffLat, Submodule.span_le]
  rintro _ ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  choose z hz using HT.exists_different_mul_dualInt E x hx
  change (Pi.single s _ : (E →+* K) → Fin N → K) ∈ baseChangeLat K I
  have e : (Pi.single s (fun i => s (((x : E) • y) i)) : (E →+* K) → Fin N → K) =
      ∑ k, RingOfIntegers.mapRingHom s (z k) •
        (fun (σ : E →+* K) a => σ (((RingOfIntegers.basis E k : 𝓞 E) • y) a)) := by
    funext σ a
    have h1 : ∀ k, ((RingOfIntegers.mapRingHom s (z k) : 𝓞 K) : K) =
        s (x : E) * s (HT.dualInt E k) := fun k => by
      rw [← map_mul, ← hz k]; rfl
    have h2 := sum_dual_mul s σ
    have h3 : ∑ k, (RingOfIntegers.mapRingHom s (z k)) •
        (σ ((RingOfIntegers.basis E k : 𝓞 E) • y a)) =
        s (x : E) * σ (y a) *
          ∑ k, s (HT.dualInt E k) * σ ((RingOfIntegers.basis E k : 𝓞 E) : E) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def]
      change ((RingOfIntegers.mapRingHom s (z k) : 𝓞 K) : K) * _ = _
      rw [h1, Algebra.smul_def, map_mul]
      change _ * (σ ((RingOfIntegers.basis E k : 𝓞 E) : E) * _) = _
      ring
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [h3, h2]
    by_cases h : σ = s
    · subst h
      simp
    · simp [Pi.single_apply, h]
  rw [e]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨_, I.smul_mem _ hy, rfl⟩)

theorem eigenLat_eq_diffLat : EigenLatDifferent.Statement := by
  intro E _ _ K _ _ ι hι N I hI s
  haveI : Finite (E →+* K) := Finite.of_injective (fun t : E →+* K => ι.comp t) (fun a b hab => by
    ext x
    exact ι.injective (DFunLike.congr_fun hab x))
  letI := Fintype.ofFinite (E →+* K)
  exact le_antisymm (eigenLat_le (card_embeddings ι hι) I hI s) (diffLat_le I s)

end GlobalTheory.CompanionTheory.Ar.EigLat
