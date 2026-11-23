import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactIntV
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExtensionEmbeddingEvInfRealAd
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExistsAdelePiInf

noncomputable section

namespace GlobalTheory.ThK.Dbl.Dense

open scoped TensorProduct NNReal Matrix SchwartzMap LineDeriv
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Heis

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_zero : evI F 0 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem evI_sum {ι : Type} (s : Finset ι) (g : ι → AF F) : evI F (∑ i ∈ s, g i) = ∑ i ∈ s, evI F (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evI_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, evI_add, ih]

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ (mixedEmbedding.mixedSpace F) t := by
  simp [evI, realAd]

def linForm (B : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (∑ i, (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) ∘ₗ (LinearMap.mulRight ℝ (B i)) ∘ₗ
      (LinearMap.proj i : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F))

theorem linForm_apply (B y : κ → mixedEmbedding.mixedSpace F) :
    linForm B y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * B i) := by
  simp [linForm, map_sum, LinearMap.sum_apply]

open scoped Classical in

theorem hasDerivAt_line (f : SInf F κ) (y A : κ → mixedEmbedding.mixedSpace F) (l c : ℝ) (ρ : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * l + t ^ 2 * c : ℝ) : ℂ)) * (f (y + t • A) * ρ))
      ((fderiv ℝ f y A + (-(2 * Real.pi * Complex.I) * (l : ℂ)) * f y) * ρ) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t * l + t ^ 2 * c) l 0 := by
    have a1 : HasDerivAt (fun t : ℝ => t * l) l 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const l
    have a2 : HasDerivAt (fun t : ℝ => t ^ 2 * c) 0 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const c
    simpa using a1.fun_add a2
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * l + t ^ 2 * c : ℝ) : ℂ)))
      (-(2 * Real.pi * Complex.I) * (l : ℂ)) 0 := by
    have := ((h1.ofReal_comp).const_mul (-(2 * Real.pi * Complex.I))).cexp
    simpa using this
  have h3 : HasDerivAt (fun t : ℝ => y + t • A) A 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const A).const_add y
  have h4 : HasDerivAt (fun t : ℝ => f (y + t • A)) (fderiv ℝ f y A) 0 := by
    have hf : HasFDerivAt f (fderiv ℝ f y) (y + (0 : ℝ) • A) := by
      simpa using f.hasFDerivAt y
    exact hf.comp_hasDerivAt (0 : ℝ) h3
  exact (h2.fun_mul (h4.mul_const ρ)).congr_deriv (by simp; ring)

open scoped Classical in

theorem phase_line (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (a b x : κ → AF F) (hb : At (evI F) b) (t : ℝ) :
    ψ (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * linForm (fun i => evI F (b i)) (fun i => evI F (x i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) : ℝ) : ℂ)) := by
  have hz : At (evI F) (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) := by
    intro s hs
    have hsb : ∀ i, s * b i = 0 := fun i => by simpa using congrFun (hb s hs) i
    have e1 : ∀ i, s * (x i * (realAd F t * b i)) = x i * realAd F t * (s * b i) := fun i => by ring
    have e2 : ∀ i, s * (⅟(2 : AF F) * (realAd F t * a i * (realAd F t * b i))) =
        ⅟(2 : AF F) * (realAd F t * a i * realAd F t) * (s * b i) := fun i => by ring
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, e1, e2, hsb, mul_zero, Finset.sum_const_zero,
      add_zero]
  rw [hψ.2.2 _ hz]
  congr 3
  have ev : evI F (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      t • (∑ i, evI F (x i) * evI F (b i)) + (t ^ 2) • (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_sum, evI_realAd, Algebra.smul_def, map_pow,
      Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [ev, map_add, map_smul, map_smul, linForm_apply]
  simp [smul_eq_mul]

def pt (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

theorem evI_pt (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    (fun i => evI F (pt x y i)) = x := by
  funext i
  simp [evI, pt]

theorem pureA_pt (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    pureA F f g (pt x y) = f x * g y := by
  simp [pureA, pt]

def rOf (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : (κ → AF F) → ℂ := fun x => g fun i => (x i).2

theorem tens_rOf (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    tens (evI F) f (rOf g) = pureA F f g := rfl

theorem snd_eq_zero {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let u : AF F := (0, 1)
  have h0 : evI F u = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h : u * z i = 0 := congrFun (hz u h0) i
  have h' : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
  simpa using h'

theorem rOf_add (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x z : κ → AF F) (hz : At (evI F) z) :
    rOf g (x + z) = rOf g x := by
  have : (fun i => (x + z) i |>.2) = fun i => (x i).2 := by
    funext i
    show (x i).2 + (z i).2 = _
    rw [snd_eq_zero hz, add_zero]
  simp only [rOf, this]

end Heis

section Real

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lift (v : mixedEmbedding.mixedSpace F) : AF F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm v, 0)

theorem evI_lift (v : mixedEmbedding.mixedSpace F) : evI F (lift v) = v :=
  RingEquiv.apply_symm_apply _ v

theorem lift_add (v v' : mixedEmbedding.mixedSpace F) : lift (v + v') = lift v + lift v' :=
  Prod.ext (map_add _ v v') (add_zero _).symm

theorem lift_zero : lift (0 : mixedEmbedding.mixedSpace F) = 0 :=
  Prod.ext (map_zero _) rfl

theorem mul_lift (c : AF F) (v : mixedEmbedding.mixedSpace F) : c * lift v = lift (evI F c * v) := by
  refine Prod.ext ?_ (mul_zero _)
  show c.1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm v =
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (evI F c * v)
  rw [map_mul]
  exact congrArg (· * _) (RingEquiv.symm_apply_apply _ _).symm

theorem lift_smul (t : ℝ) (v : mixedEmbedding.mixedSpace F) : lift (t • v) = realAd F t * lift v := by
  rw [mul_lift, evI_realAd, Algebra.smul_def]

theorem lift_evI {z : AF F} (hz : At (evI F) z) : lift (evI F z) = z := by
  have h1 : (show AF F from (0, 1)) * z = 0 :=
    hz _ (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  have h2 : z.2 = 0 := by
    have := congrArg Prod.snd h1
    exact (one_mul _).symm.trans this
  exact Prod.ext (RingEquiv.symm_apply_apply _ _) h2.symm

theorem at_lift (v : mixedEmbedding.mixedSpace F) : At (evI F) (lift v) := fun c hc => by
  rw [smul_eq_mul, mul_lift, hc, zero_mul, lift_zero]

theorem at_entry {n d : ℕ} {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (i : Fin n) (j : Fin d) :
    At (evI F) (u i j) := fun c hc => by
  simpa using congrFun (congrFun (hu c hc) i) j

theorem exists_real_structure (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    {n d : ℕ} {κ : Type} [Fintype κ]
    (e : Matrix (Fin n) (Fin d) (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F))
    (C : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin d) ℂ) :
    ∃ (s : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
          Matrix (Fin n) (Fin d) (AE F E))
      (Jm : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      (∀ p, At (evI F) (s p)) ∧
      (∀ p, (fun i => evI F ((e (s p)).1 i)) = p.1 ∧ (fun i => evI F ((e (s p)).2 i)) = p.2) ∧
      ∀ p w, (s (Jm p)).map (piInf (emb w)) = C w ((s p).map (piInf (emb w))) := by
  let s : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
      Matrix (Fin n) (Fin d) (AE F E) :=
    fun p => e.symm (fun i => lift (p.1 i), fun i => lift (p.2 i))
  have es : ∀ p, e (s p) = (fun i => lift (p.1 i), fun i => lift (p.2 i)) := fun p => e.apply_symm_apply _
  have sAdd : ∀ p q, s (p + q) = s p + s q := fun p q => by
    show e.symm _ = e.symm _ + e.symm _
    rw [← map_add]
    congr 1
    refine Prod.ext (funext fun i => lift_add _ _) (funext fun i => lift_add _ _)
  have sSmul : ∀ (t : ℝ) p, s (t • p) = realAd F t • s p := fun t p => by
    show e.symm _ = realAd F t • e.symm _
    rw [← map_smul]
    congr 1
    refine Prod.ext (funext fun i => lift_smul _ _) (funext fun i => lift_smul _ _)
  have sAt : ∀ p, At (evI F) (s p) := fun p c hc => by
    show c • e.symm _ = 0
    rw [← map_smul]
    have : c • ((fun i => lift (p.1 i), fun i => lift (p.2 i)) : (κ → AF F) × (κ → AF F)) = 0 :=
      Prod.ext (funext fun i => at_lift _ c hc) (funext fun i => at_lift _ c hc)
    rw [this, map_zero]
  let Ψ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      (InfinitePlace F → Matrix (Fin n) (Fin d) ℂ) :=
    { toFun := fun p w => (s p).map (piInf (emb w))
      map_add' := fun p q => by
        funext w
        rw [sAdd]
        ext i j
        simp
      map_smul' := fun t p => by
        funext w
        rw [sSmul]
        ext i j
        simp [GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul] }
  have hΨ : ∀ p w, Ψ p w = (s p).map (piInf (emb w)) := fun _ _ => rfl
  have inj : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).2 fun p hp => ?_
    have s0 : s p = 0 := by
      ext i j
      refine GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ h emb _ (at_entry (sAt p) i j) fun w => ?_
      have := congrFun (congrFun (congrFun hp w) i) j
      simpa [hΨ] using this
    have e0 := es p
    rw [s0, map_zero] at e0
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · have := congrFun (congrArg Prod.fst e0) i
      have := congrArg (evI F) this
      rw [evI_lift] at this
      simpa [evI_zero] using this.symm
    · have := congrFun (congrArg Prod.snd e0) i
      have := congrArg (evI F) this
      rw [evI_lift] at this
      simpa [evI_zero] using this.symm
  have surj : Function.Surjective Ψ := fun Z => by
    choose x hxA hxZ using fun (ij : Fin n × Fin d) => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h emb (fun w => Z w ij.1 ij.2)
    let u : Matrix (Fin n) (Fin d) (AE F E) := Matrix.of fun i j => x (i, j)
    have uAt : At (evI F) u := fun c hc => by
      ext i j
      exact hxA (i, j) c hc
    have hAt2 : ∀ c : AF F, evI F c = 0 → c • e u = 0 := fun c hc => by
      rw [← map_smul, uAt c hc, map_zero]
    refine ⟨(fun i => evI F ((e u).1 i), fun i => evI F ((e u).2 i)), ?_⟩
    have su : s (fun i => evI F ((e u).1 i), fun i => evI F ((e u).2 i)) = u := by
      show e.symm _ = u
      rw [LinearEquiv.symm_apply_eq]
      refine Prod.ext (funext fun i => lift_evI fun c hc => ?_) (funext fun i => lift_evI fun c hc => ?_)
      · exact congrFun (congrArg Prod.fst (hAt2 c hc)) i
      · exact congrFun (congrArg Prod.snd (hAt2 c hc)) i
    funext w
    rw [hΨ, su]
    ext i j
    exact hxZ (i, j) w
  let Ψe := LinearEquiv.ofBijective Ψ ⟨inj, surj⟩
  let Cp : (InfinitePlace F → Matrix (Fin n) (Fin d) ℂ) →ₗ[ℝ] (InfinitePlace F → Matrix (Fin n) (Fin d) ℂ) :=
    LinearMap.pi fun w => C w ∘ₗ LinearMap.proj w
  refine ⟨s, Ψe.symm.toLinearMap ∘ₗ Cp ∘ₗ Ψ, sAt, fun p => ?_, fun p w => ?_⟩
  · rw [es]
    exact ⟨funext fun i => evI_lift _, funext fun i => evI_lift _⟩
  · have : Ψ ((Ψe.symm.toLinearMap ∘ₗ Cp ∘ₗ Ψ) p) = Cp (Ψ p) := Ψe.apply_symm_apply _
    exact congrFun this w

open scoped Classical in

def dOp {κ : Type} [Fintype κ] (A B : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) : SInf F κ :=
  ∂_{A} f + (-(2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (linForm B) f

open scoped Classical in
theorem dOp_apply {κ : Type} [Fintype κ] (A B : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) (y) :
    dOp A B f y = fderiv ℝ f y A + (-(2 * Real.pi * Complex.I)) * ((linForm B y : ℝ) : ℂ) * f y := by
  have hT := (linForm B).hasTemperateGrowth
  simp only [dOp, SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hT,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp [mul_assoc]

open scoped Classical in
theorem hasDerivAt_dOp {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (a b : κ → AF F)
    (ha : At (evI F) a) (hb : At (evI F) b) (f : SInf F κ) (r) (hr : Rest (evI F) f r) (x) :
    HasDerivAt (fun t : ℝ => schr ψ (realAd F t • a, realAd F t • b) (tens (evI F) f r) x)
      (tens (evI F) (dOp (fun i => evI F (a i)) (fun i => evI F (b i)) f) r x) 0 := by
  have hat : ∀ t : ℝ, At (evI F) (realAd F t • a) := fun t s hs => by
    rw [smul_comm, ha s hs, smul_zero]
  have key : (fun t : ℝ => schr ψ (realAd F t • a, realAd F t • b) (tens (evI F) f r) x) =
      fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * linForm (fun i => evI F (b i)) (fun i => evI F (x i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) : ℝ) : ℂ)) *
        (f ((fun i => evI F (x i)) + t • fun i => evI F (a i)) * r x) := by
    funext t
    have e : (fun i => evI F ((x + realAd F t • a) i)) = (fun i => evI F (x i)) + t • fun i => evI F (a i) := by
      funext i
      simp [evI_add, evI_mul, evI_realAd, Algebra.smul_def]
    simp only [schr, tens]
    rw [phase_line ψ hψ a b x hb t, e, hr.1 x _ (hat t)]
  rw [key]
  refine (hasDerivAt_line f _ _ _ _ (r x)).congr_deriv ?_
  simp only [tens, dOp_apply]

open mixedEmbedding

theorem trace_mul_eq_zero (b : mixedSpace F) (h : ∀ y, Algebra.trace ℝ (mixedSpace F) (b * y) = 0) : b = 0 := by
  classical
  refine (latticeBasis F).ext_elem fun j => ?_
  have := h (mixedEmbedding F ((integralBasis F).traceDual j))
  rw [← (latticeBasis F).sum_repr b] at this
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, latticeBasis_apply, ← map_mul,
    trace_emb, Module.Basis.trace_mul_traceDual] at this
  simpa [apply_ite] using this

theorem exists_trace_eq (L : mixedSpace F →ₗ[ℝ] ℝ) :
    ∃ b : mixedSpace F, ∀ y, L y = Algebra.trace ℝ (mixedSpace F) (y * b) := by
  have hinj : Function.Injective (Algebra.traceForm ℝ (mixedSpace F)) := by
    refine (injective_iff_map_eq_zero _).mpr fun b hb => trace_mul_eq_zero b fun y => ?_
    simpa using LinearMap.congr_fun hb y
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := mixedSpace F)).symm).mp hinj
  obtain ⟨b, hb⟩ := hsurj L
  exact ⟨b, fun y => by rw [← hb, Algebra.traceForm_apply, mul_comm]⟩

theorem exists_linForm_eq {κ : Type} [Fintype κ] (l : (κ → mixedSpace F) →ₗ[ℝ] ℝ) :
    ∃ B : κ → mixedSpace F, ∀ y, l y = linForm B y := by
  classical
  choose B hB using fun i => exists_trace_eq (F := F) (l ∘ₗ LinearMap.single ℝ (fun _ => mixedSpace F) i)
  refine ⟨B, fun y => ?_⟩
  rw [linForm_apply, map_sum]
  conv_lhs => rw [← Finset.univ_sum_single y, map_sum]
  exact Finset.sum_congr rfl fun i _ => hB i (y i)

def reAd (x : mixedSpace F) : AF F :=
  LinearMap.inl F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x)

theorem evI_reAd (x : mixedSpace F) : evI F (reAd x) = x := RingEquiv.apply_symm_apply _ x

theorem at_reAd {κ : Type} (B : κ → mixedSpace F) : At (evI F) (fun i => reAd (B i)) := by
  intro s hs
  have h1 : s.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 hs
  funext i
  refine Prod.ext ?_ ?_
  · show s.1 * (reAd (B i)).1 = 0
    rw [h1, zero_mul]
  · show s.2 * (reAd (B i)).2 = 0
    simp [reAd]

end Real

theorem fock_mul_linear : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (Y : Spc F E n) (Z : Spc F E d) (Mo : Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), IsStd ψ →
    ∀ (l : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ) (f f₁ : SInf F (Fin n × Fin d)),
      f ∈ Mo.Pol ψ τ → (∀ x, f₁ x = (l x : ℂ) * f x) → f₁ ∈ Mo.Pol ψ τ := by
  intro F E _ _ _ _ _ σ n d Y Z Mo ψ τ hψ l f f₁ hf h₁
  obtain ⟨B, hB⟩ := exists_linForm_eq l
  let b : Fin n × Fin d → AF F := fun i => reAd (B i)
  have hb : At (evI F) b := at_reAd B
  have hBe : (fun i => evI F (b i)) = B := funext fun i => evI_reAd (B i)
  let u := Mo.co.e.symm (0, b)
  have hu : At (evI F) u := by
    intro s hs
    show s • Mo.co.e.symm (0, b) = 0
    rw [← map_smul, Prod.smul_mk, smul_zero, hb s hs]
    exact map_zero _
  let c : ℂ := -(2 * Real.pi * Complex.I)
  have hc : c ≠ 0 := by simp [c, Real.pi_ne_zero]
  have hact : ActsD (evI F) (Mo.heisLine ψ u) f (c • f₁) := by
    intro r hr x
    have key : (fun t : ℝ => Mo.heisLine ψ u t (tens (evI F) f r) x) =
        fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) *
          ((t * linForm (fun i => evI F (b i)) (fun i => evI F (x i)) + t ^ 2 * 0 : ℝ) : ℂ)) *
          (f ((fun i => evI F (x i)) + t • (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F)) * r x) := by
      funext t
      show GlobalTheory.WeilM.schr ψ (Mo.co.e (realAd F t • u)) _ x = _
      rw [map_smul, LinearEquiv.apply_symm_apply]
      show ψ (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • (0 : Fin n × Fin d → AF F)) ⬝ᵥ (realAd F t • b))) *
        tens (evI F) f r (x + realAd F t • (0 : Fin n × Fin d → AF F)) = _
      rw [phase_line ψ hψ 0 b x hb t]
      simp [tens, evI_zero]
    rw [key]
    refine (hasDerivAt_line f _ _ _ _ (r x)).congr_deriv ?_
    show _ = (c • f₁) (fun i => evI F (x i)) * r x
    rw [SchwartzMap.smul_apply, h₁, hBe, ← hB, map_zero, zero_add, smul_eq_mul]
    simp only [c]
    ring
  have hmem : c • f₁ ∈ Mo.Pol ψ τ := by
    refine Submodule.mem_sInf.mpr fun N hN => hN.2 u hu f (Submodule.mem_sInf.mp hf N hN) _ hact
  have := (Mo.Pol ψ τ).smul_mem c⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

section Uniq

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

open scoped Classical in
theorem actsD_unique (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) {f f₁ : SInf F (Fin n × Fin d)}
    (h : ActsD (evI F) (M.heisLine ψ u) f f₁) :
    f₁ = dOp (fun i => evI F ((M.co.e u).1 i)) (fun i => evI F ((M.co.e u).2 i)) f := by
  have hg := pf_mem (good_std (F := F) (κ := Fin n × Fin d))
  have h0 : pf (stdF (F := F) (Fin n × Fin d)) 0 = 1 := by
    rw [pf_eq_prod ∅ 0 fun u _ => ⟨rfl, fun i => by simp⟩, Finset.prod_empty]
  ext x
  have hr : Rest (evI F) f (rOf (pf (stdF (Fin n × Fin d)))) :=
    ⟨fun x z hz => rOf_add _ x z hz, Submodule.subset_span ⟨f, _, hg, rfl⟩⟩
  have hab : ∀ t, evI F t = 0 → t • M.co.e u = 0 := fun t ht => by rw [← map_smul, hu t ht, map_zero]
  have h1 := h _ hr (pt x 0)
  have h2 := hasDerivAt_dOp ψ hψ _ _ (fun t ht => congrArg Prod.fst (hab t ht)) (fun t ht => congrArg Prod.snd (hab t ht))
    f _ hr (pt x 0)
  simp only [Model.heisLine, Darboux.rho, map_smul] at h1
  have := h1.unique h2
  simpa [tens_rOf, pureA_pt, h0] using this

end Uniq

end GlobalTheory.ThK.Dbl.Dense

end
