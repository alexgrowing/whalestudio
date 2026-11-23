import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

noncomputable section

namespace GlobalTheory.LFun.Model

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

def constMap (G : Type) : ℂ →ₗ[ℂ] (G → ℂ) := LinearMap.pi fun _ => LinearMap.id

theorem constMap_injective (G : Type) [Group G] : Function.Injective (constMap G) := fun _ _ h => congrFun h 1

section Linear

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)

def rhoGL (i : Fin n) : ℂˣ := npowU w (((n : ℂ) - 1) / 2 - (i : ℕ))

theorem chiDelta_rhoGL (b : GL (Fin n) (w.adicCompletion E)) : chiDelta E w (fun i => (rhoGL w n i : ℂ)) b = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  have hq : ((qV E w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast qV_ne_zero w
  change (((qV E w : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2 - (i : ℕ))) ^ _ * _ = 1
  rw [← Complex.cpow_mul_int, ← Complex.cpow_add _ _ hq]
  convert Complex.cpow_zero _ using 2
  ring

theorem hasSatGL_trivial : HasSatGL w (Representation.trivial ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (seg w 1 n) := by
  have e : seg w 1 n = Finset.univ.val.map (rhoGL w n) := by
    rw [seg, Finset.range_val, ← Multiset.coe_range, ← List.map_coe_finRange_eq_range, Multiset.map_coe, List.map_map]
    simp only [one_mul]
    rfl
  rw [e]
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl, one_ne_zero⟩, fun x _ h0 => ?_⟩
  refine IsSatVecGL.of_map (constMap _) (fun _ _ => rfl) (constMap_injective _)
    (isSatVecGL_of_isSpherical (fun b g k _ _ => ?_) fun h => h0 (congrFun h 1))
  rw [chiDelta_rhoGL, one_mul]; rfl

theorem not_hasSatGL_trivial_one :
    ¬ HasSatGL w (Representation.trivial ℂ (GL (Fin 2) (w.adicCompletion E)) ℂ) {1, 1} := fun h => by
  have e := (hasSatGL_trivial w 2).unique h
  have h1 : (1 : ℂˣ) * npowU w ((((2 : ℕ) : ℂ) - 1) / 2 - (0 : ℕ)) ∈ seg w 1 2 :=
    Multiset.mem_map.2 ⟨0, by simp, rfl⟩
  rw [e] at h1
  have h2 : npow w ((((2 : ℕ) : ℂ) - 1) / 2 - (0 : ℕ)) = 1 := by
    have : npowU w ((((2 : ℕ) : ℂ) - 1) / 2 - (0 : ℕ)) = 1 := by simpa using h1
    exact congrArg Units.val this
  have h3 := congrArg norm h2
  rw [norm_npow, norm_one] at h3
  refine (Real.one_lt_rpow (by exact_mod_cast one_lt_absNorm w) ?_).ne' h3
  norm_num

theorem psFunGL_one_apply (a : ℂˣ) (t : GL (Fin 1) (w.adicCompletion E)) (ht : IsUnifV E w (t.1 0 0))
    (φ : psSpaceGL w (fun _ : Fin 1 => a)) :
    HasSatGL w (psFunGL w fun _ : Fin 1 => a) {a} ∧ psFunGL w (fun _ : Fin 1 => a) t φ = (a : ℂ) • φ := by
  refine ⟨hasSatGL_psFunGL _, Subtype.ext (funext fun g => ?_)⟩
  change φ.1 (g * t) = a * φ.1 g
  have hc : g * t = t * g := Units.ext (by ext i j; simp [Matrix.mul_apply, mul_comm, Subsingleton.elim i 0, Subsingleton.elim j 0])
  have ho : ordV E w (t.1 0 0) = 1 := by
    have h0 : Valued.v (t.1 0 0) ≠ 0 := by rw [ht]; exact WithZero.coe_ne_zero
    have h1 : WithZero.unzero h0 = Multiplicative.ofAdd (-1 : ℤ) :=
      WithZero.coe_injective ((WithZero.coe_unzero h0).trans ht)
    rw [ordV, dif_neg h0, h1]; rfl
  rw [hc, φ.2 t g fun i j h => absurd h (by simp [Subsingleton.elim i j])]
  simp [chiDelta, ho]

end Linear

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {σ : L →+* L} {ϖ : L} {q : ℕ}

def rhoU {q : ℕ} (hq : q ≠ 0) (n : ℕ) (i : Fin (n / 2)) : ℂˣ :=
  Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))

theorem hasSatU_trivial (hU : IsUnramInv ϖ σ q) (hq : q ≠ 0) (n : ℕ) :
    HasSatU ϖ q (Representation.trivial ℂ (GU σ n) ℂ) (rhoU hq n) := by
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl, one_ne_zero⟩, fun x _ h0 => ?_⟩
  refine IsSatVecU.of_map hU (constMap _) (fun _ _ => rfl) (constMap_injective _)
    (isSatVecU_of_isSphericalU hU (fun b g k _ _ => ?_) fun h => h0 (congrFun h 1))
  have : chiDeltaU q (fun i => (rhoU hq n i : ℂ)) b = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    split_ifs
    · simp only [rhoU, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [← zpow_mul, ← zpow_add₀ hq']
      convert zpow_zero _ using 2
      ring
    · rfl
  rw [this, one_mul]; rfl

end U

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}

theorem paramOf_trivial_split (hv : IsSplit (E := E) v) {e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E)}
    (he : IsSplitChart σ J L h e) : paramOf σ J L h (Representation.trivial ℂ _ ℂ) = seg w 1 n :=
  HasParam.paramOf_eq_of_isSplit hv (Or.inl ⟨hv, e, he, hasSatGL_trivial w n⟩)

theorem hasParam_trivial_inert (hw : IsInertAt F E v w) {c : w.adicCompletion E →+* w.adicCompletion E}
    {ϖ : w.adicCompletion E} (hU : IsUnramInv ϖ c (qV F v)) {e : GLoc σ J v ≃* GU c n}
    (he : IsInertChart σ J L h c e) :
    HasParam σ J L h (Representation.trivial ℂ _ ℂ) (bcParam n (rhoU (qV_ne_zero v) n)) :=
  Or.inr ⟨hw, c, ϖ, e, _, hU, he, hasSatU_trivial hU _ n, rfl⟩

open scoped TensorProduct in

theorem toCompl_surjective (h : w.under (𝓞 F) = v) : Function.Surjective (toCompl h) := fun x => by
  classical
  obtain ⟨y, hy⟩ := (finAdEquiv F E).surjective ⟨Pi.single w x, by
    filter_upwards [(Set.finite_singleton w).compl_mem_cofinite] with u hu
    rw [Pi.single_eq_of_ne (by simpa using hu)]
    exact zero_mem _⟩
  exact ⟨_, (finAdEquiv_apply h y).symm.trans (by rw [hy]; exact Pi.single_eq_same w x)⟩

theorem isConjAt_unique {c c' : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c)
    (hc' : IsConjAt σ h c') : c = c' := RingHom.ext fun x => by
  obtain ⟨y, rfl⟩ := toCompl_surjective h x
  rw [hc, hc']

theorem not_hasParam_id (hw : IsInertAt F E v w) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GLoc (AlgHom.id F E) J v) V) (B : Multiset ℂˣ) :
    ¬ HasParam (AlgHom.id F E) J L h ρ B := by
  rintro (⟨hv, -⟩ | ⟨-, c, ϖ, e, α, hU, he, -⟩)
  · exact not_isSplit_of_isInertAt hw hv
  · have hc : c = RingHom.id _ := isConjAt_unique he.1 fun y => by
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ (AlgHom.id F E) y = y := by simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
      rw [this]; rfl
    obtain ⟨x, -, hx⟩ := hU.2.2.2.2.1
    simp [hc] at hx

theorem not_hasParam_of_subsingleton {V : Type} [AddCommGroup V] [Module ℂ V] [Subsingleton V]
    (ρ : Representation ℂ (GLoc σ J v) V) (B : Multiset ℂˣ) : ¬ HasParam σ J L h ρ B := fun hρ => by
  obtain ⟨x, hx⟩ := hρ.exists_vec
  exact hx.ne_zero (Subsingleton.elim _ _)

theorem not_isFrameAt_bot (a : GL (Fin (n + 1)) (w.adicCompletion E)) : ¬ IsFrameAt w ⊥ a := fun ha => by
  have h1 := (ha (fun _ => 1)).1 fun _ => one_mem _
  have h2 : latAt w (⊥ : Submodule (𝓞 E) (Fin (n + 1) → E)) = ⊥ := by
    rw [latAt, Submodule.span_eq_bot]
    rintro _ ⟨x, hx, rfl⟩
    rw [(Submodule.mem_bot _).1 hx]
    funext i; simp
  rw [h2, Submodule.mem_bot] at h1
  have h3 := congrArg (fun y => (a⁻¹).1.mulVec y) h1
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h3
  exact one_ne_zero (congrFun h3 0)

theorem locL_trivial (s : ℂ) : locL (segFam (fun _ : HeightOneSpectrum (𝓞 E) => 1) n) w s =
    ∏ i ∈ Finset.range n, (1 - npow w (-(s - ((n : ℂ) - 1) / 2 + i)))⁻¹ := by
  rw [locL_segFam]; simp [locL]

end Global

example : ((bcParam 3 (rhoU (q := 3) (by norm_num) 3)).map fun b : ℂˣ => (b : ℂ)) = {9, 9⁻¹, 1} := by
  change ({((rhoU (q := 3) _ 3 0 : ℂˣ) : ℂ), (((rhoU (q := 3) _ 3 0)⁻¹ : ℂˣ) : ℂ), ((1 : ℂˣ) : ℂ)} : Multiset ℂ) = _
  simp [rhoU]; norm_num

end GlobalTheory.LFun.Model

end
