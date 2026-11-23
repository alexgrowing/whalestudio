import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZSt
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic

noncomputable section

open NumberField Matrix IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.LatDictZ.Z5

open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ

section Gl

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {n : Type} [Fintype n] [DecidableEq n]

def gl (s : Finset ι) (e : ι → R) (M : Matrix n n R) (A : ι → Matrix n n R) : Matrix n n R :=
  M + ∑ i ∈ s, e i • (A i - M)

def Orth (s : Finset ι) (e : ι → R) : Prop := ∀ i ∈ s, ∀ j ∈ s, e i * e j = if i = j then e i else 0

theorem gl_const (s : Finset ι) (e : ι → R) (M : Matrix n n R) : gl s e M (fun _ => M) = M := by
  simp [gl]

theorem gl_mul {s : Finset ι} {e : ι → R} (he : Orth s e) (M N : Matrix n n R) (A B : ι → Matrix n n R) :
    gl s e M A * gl s e N B = gl s e (M * N) (fun i => A i * B i) := by
  unfold gl
  have h1 : (∑ i ∈ s, e i • (A i - M)) * (∑ j ∈ s, e j • (B j - N)) =
      ∑ i ∈ s, e i • ((A i - M) * (B i - N)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he i hi i hi, if_pos rfl]
    · intro b hb hbi
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he i hi b hb, if_neg (Ne.symm hbi), zero_smul]
    · intro h
      exact absurd hi h
  rw [add_mul, mul_add, mul_add, h1, Finset.mul_sum, Finset.sum_mul, add_assoc, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add, ← smul_add]
  congr 1
  noncomm_ring

theorem gl_mulVec (s : Finset ι) (e : ι → R) (M : Matrix n n R) (A : ι → Matrix n n R) (y : n → R) :
    gl s e M A *ᵥ y = M *ᵥ y + ∑ i ∈ s, e i • ((A i - M) *ᵥ y) := by
  unfold gl
  rw [Matrix.add_mulVec]
  congr 1
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Matrix.add_mulVec, ih, Matrix.smul_mulVec]

theorem gl_proj {s : Finset ι} {e : ι → R} (he : Orth s e) (M : Matrix n n R) (A : ι → Matrix n n R)
    (y : n → R) {j : ι} (hj : j ∈ s) : e j • (gl s e M A *ᵥ y) = e j • (A j *ᵥ y) := by
  rw [gl_mulVec, smul_add, Finset.smul_sum]
  have h : ∑ i ∈ s, e j • e i • ((A i - M) *ᵥ y) = e j • ((A j - M) *ᵥ y) := by
    rw [Finset.sum_eq_single j]
    · rw [smul_smul, he j hj j hj, if_pos rfl]
    · intro b hb hbj
      rw [smul_smul, he j hj b hb, if_neg (Ne.symm hbj), zero_smul]
    · intro h
      exact absurd hj h
  rw [h, ← smul_add, Matrix.sub_mulVec]
  congr 1
  abel

theorem gl_proj0 {s : Finset ι} {e : ι → R} {f : R} (hf : ∀ i ∈ s, f * e i = 0) (M : Matrix n n R)
    (A : ι → Matrix n n R) (y : n → R) : f • (gl s e M A *ᵥ y) = f • (M *ᵥ y) := by
  rw [gl_mulVec, smul_add, Finset.smul_sum]
  have h : ∑ i ∈ s, f • e i • ((A i - M) *ᵥ y) = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [smul_smul, hf i hi, zero_smul]
  rw [h, add_zero]

theorem cT_gl (σ : R →+* R) {s : Finset ι} {e : ι → R} (hσ : ∀ i ∈ s, σ (e i) = e i) (M : Matrix n n R)
    (A : ι → Matrix n n R) :
    Formalism.UG.cT σ (gl s e M A) = gl s e (Formalism.UG.cT σ M) (fun i => Formalism.UG.cT σ (A i)) := by
  unfold gl Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.sub_apply, map_add, map_sum, map_mul, map_sub, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun k hk => by rw [hσ k hk]

end Gl

section Ad

variable {F : Type} [Field F] [NumberField F]

def mkI (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) : Af F :=
  ⟨c, Filter.Eventually.of_forall hc⟩

theorem mkI_apply (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) : mkI c hc v = c v := rfl

theorem mkI_mem (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) : mkI c hc ∈ Formalism.UG.intAd F := by
  intro v
  exact hc v

def ev (v : HeightOneSpectrum (𝓞 F)) : Af F →+* v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem comp_mul (a b : Af F) (v : HeightOneSpectrum (𝓞 F)) : (a * b) v = a v * b v := rfl
theorem comp_add (a b : Af F) (v : HeightOneSpectrum (𝓞 F)) : (a + b) v = a v + b v := rfl
theorem comp_one (v : HeightOneSpectrum (𝓞 F)) : (1 : Af F) v = 1 := rfl
theorem comp_zero (v : HeightOneSpectrum (𝓞 F)) : (0 : Af F) v = 0 := rfl

open Classical in

def eT (T : Set (HeightOneSpectrum (𝓞 F))) : Af F :=
  mkI (fun v => if v ∈ T then 1 else 0) (fun v => by split_ifs; exacts [one_mem _, zero_mem _])

theorem eT_mem (T : Set (HeightOneSpectrum (𝓞 F))) : eT T ∈ Formalism.UG.intAd F := by
  exact mkI_mem _ _

theorem eT_of_mem {T : Set (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ T) :
    eT T v = 1 := by
  simp [eT, mkI_apply, h]

theorem eT_of_not {T : Set (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ T) :
    eT T v = 0 := by
  simp [eT, mkI_apply, h]

open Classical in
theorem eT_orth (i j : HeightOneSpectrum (𝓞 F)) :
    eT {i} * eT {j} = if i = j then eT {i} else 0 := by
  apply RestrictedProduct.ext
  intro v
  show eT {i} v * eT {j} v = (if i = j then eT {i} else 0) v
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hv : v ∈ ({i} : Set (HeightOneSpectrum (𝓞 F)))
    · rw [eT_of_mem hv, mul_one]
    · rw [eT_of_not hv, mul_zero]
  · rw [if_neg hij]
    show eT {i} v * eT {j} v = 0
    by_cases hv : v ∈ ({i} : Set (HeightOneSpectrum (𝓞 F)))
    · have hv' : v ∉ ({j} : Set (HeightOneSpectrum (𝓞 F))) := by
        rw [Set.mem_singleton_iff] at hv ⊢
        rw [hv]
        exact hij
      rw [eT_of_not hv', mul_zero]
    · rw [eT_of_not hv, zero_mul]

theorem eT_compl_mul {Q : Set (HeightOneSpectrum (𝓞 F))} {i : HeightOneSpectrum (𝓞 F)} (hi : i ∈ Q) :
    eT Qᶜ * eT {i} = 0 := by
  apply RestrictedProduct.ext
  intro v
  show eT Qᶜ v * eT {i} v = 0
  by_cases hv : v ∈ ({i} : Set (HeightOneSpectrum (𝓞 F)))
  · have h2 : v ∉ Qᶜ := by
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact fun h => h hi
    rw [eT_of_not h2, zero_mul]
  · rw [eT_of_not hv, mul_zero]

theorem eT_sum {Q : Set (HeightOneSpectrum (𝓞 F))} (hQ : Q.Finite) :
    eT Qᶜ + ∑ i ∈ hQ.toFinset, eT {i} = 1 := by
  apply RestrictedProduct.ext
  intro v
  have hs : (∑ i ∈ hQ.toFinset, eT {i}) v = ∑ i ∈ hQ.toFinset, eT {i} v := map_sum (ev v) _ _
  show eT Qᶜ v + (∑ i ∈ hQ.toFinset, eT {i}) v = 1
  rw [hs]
  by_cases hv : v ∈ Q
  · rw [eT_of_not (T := Qᶜ) (fun h => h hv), zero_add, Finset.sum_eq_single v]
    · exact eT_of_mem (Set.mem_singleton v)
    · intro b _ hb
      exact eT_of_not (fun h => hb (Set.mem_singleton_iff.mp h).symm)
    · intro h
      exact absurd (hQ.mem_toFinset.mpr hv) h
  · rw [eT_of_mem hv, Finset.sum_eq_zero, add_zero]
    intro b hb
    apply eT_of_not
    rw [Set.mem_singleton_iff]
    rintro rfl
    exact hv (hQ.mem_toFinset.mp hb)

theorem val_one {v : HeightOneSpectrum (𝓞 F)} {r : 𝓞 F} (h : r ∉ v.asIdeal) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = 1 := by
  erw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
  rw [
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  exact h

theorem val_lt {v : HeightOneSpectrum (𝓞 F)} {r : 𝓞 F} (h : r ∈ v.asIdeal) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 := by
  erw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
  rw [
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
  exact h

theorem inv_mem' {v : HeightOneSpectrum (𝓞 F)} {r : 𝓞 F} (h : r ∉ v.asIdeal) :
    (algebraMap (𝓞 F) (v.adicCompletion F) r)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, val_one h, inv_one]

theorem ne0 {v : HeightOneSpectrum (𝓞 F)} {r : 𝓞 F} (h : r ∉ v.asIdeal) :
    algebraMap (𝓞 F) (v.adicCompletion F) r ≠ 0 := by
  intro h0
  have h1 := val_one h
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

end Ad

section Inst

variable (I : AutInst)

abbrev iA : Af I.F →ₐ[I.F] I.E ⊗[I.F] Af I.F := Algebra.TensorProduct.includeRight

theorem iA_mem {a : Af I.F} (ha : a ∈ Formalism.UG.intAd I.F) : iA I a ∈ IntAf I.F I.E := by
  exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

theorem coeOF (a : 𝓞 I.F) :
    algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) a) = algebraMap I.F I.E (algebraMap (𝓞 I.F) I.F a) := rfl

theorem alg_inj : Function.Injective (algebraMap (𝓞 I.F) (𝓞 I.E)) := by
  intro a b hab
  have h := congrArg (algebraMap (𝓞 I.E) I.E) hab
  rw [coeOF, coeOF] at h
  exact RingOfIntegers.coe_injective ((algebraMap I.F I.E).injective h)

theorem incl_OF (a : 𝓞 I.F) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) a)) =
      iA I (algebraMap (𝓞 I.F) (Af I.F) a) := by
  rw [coeOF]
  show (algebraMap I.F I.E (algebraMap (𝓞 I.F) I.F a)) ⊗ₜ[I.F] (1 : Af I.F) =
    (1 : I.E) ⊗ₜ[I.F] (algebraMap (𝓞 I.F) (Af I.F) a)
  rw [Algebra.algebraMap_eq_smul_one (algebraMap (𝓞 I.F) I.F a), TensorProduct.smul_tmul,
    ← Algebra.algebraMap_eq_smul_one]
  congr 1

theorem iv_OF (a : 𝓞 I.F) (w : Fin I.n → I.E) :
    iv I (algebraMap (𝓞 I.F) (𝓞 I.E) a • w) = iA I (algebraMap (𝓞 I.F) (Af I.F) a) • iv I w := by
  funext i
  show Formalism.UG.inclE (F := I.F) (Af I.F) ((algebraMap (𝓞 I.F) (𝓞 I.E) a • w) i) =
    iA I (algebraMap (𝓞 I.F) (Af I.F) a) • Formalism.UG.inclE (F := I.F) (Af I.F) (w i)
  rw [Pi.smul_apply, Algebra.smul_def, map_mul, incl_OF, smul_eq_mul]

theorem denomO (w : Fin I.n → I.E) :
    ∃ m : ℕ, 0 < m ∧ algebraMap (𝓞 I.F) (𝓞 I.E) (m : 𝓞 I.F) • w ∈ I.L := by
  obtain ⟨m, hm, h⟩ := lattice_denominator I (iv I w)
  refine ⟨m, hm, lattice_intersection' I _ ?_⟩
  rw [iv_OF]
  simpa using h

theorem descent (q : HeightOneSpectrum (𝓞 I.F)) {e : Af I.F} (he : e ∈ Formalism.UG.intAd I.F) (he1 : e q = 1)
    (w : Fin I.n → I.E) (hw : iA I e • iv I w ∈ I.Lf) :
    ∃ a : 𝓞 I.F, a ∉ q.asIdeal ∧ algebraMap (𝓞 I.F) (𝓞 I.E) a • w ∈ I.L := by
  obtain ⟨m, hm, hmw⟩ := denomO I w
  have hℓq : ((Ideal.absNorm q.asIdeal : ℕ) : 𝓞 I.F) ∈ q.asIdeal := Ideal.absNorm_mem _
  have hℓ0 : 0 < Ideal.absNorm q.asIdeal :=
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact q.ne_bot)
  set ℓ := Ideal.absNorm q.asIdeal
  obtain ⟨β, y, hy, hβ⟩ := DictRing.af_approx e he (m * ℓ) (Nat.mul_pos hm hℓ0)
  have hy' : ∀ v : HeightOneSpectrum (𝓞 I.F), y v ∈ v.adicCompletionIntegers I.F := hy
  refine ⟨β, fun hβq => ?_, ?_⟩
  · have h1 := congrArg (fun t : Af I.F => t q) hβ
    rw [he1, comp_add, comp_mul, DictRing.comp_algebraMap,
      ← map_natCast (algebraMap (𝓞 I.F) (Af I.F)) (m * ℓ), DictRing.comp_algebraMap] at h1
    have hN : ((m * ℓ : ℕ) : 𝓞 I.F) ∈ q.asIdeal := by
      rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ hℓq
    have hy1 : Valued.v (y q) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 I.F) (K := I.F) (v := q)).1 (hy' q)
    have hlt := Valuation.map_add_lt Valued.v (val_lt hβq)
      (by rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right' hy1) (val_lt hN))
    rw [← h1, map_one] at hlt
    exact lt_irrefl _ hlt
  · apply lattice_intersection' I
    rw [iv_OF]
    have hβ' : algebraMap (𝓞 I.F) (Af I.F) β = e - ((m * ℓ : ℕ) : Af I.F) * y := by rw [hβ]; ring
    have key : iA I (algebraMap (𝓞 I.F) (Af I.F) β) • iv I w =
        iA I e • iv I w - iA I ((ℓ : Af I.F) * y) • iv I (algebraMap (𝓞 I.F) (𝓞 I.E) (m : 𝓞 I.F) • w) := by
      rw [hβ', iv_OF, map_sub, sub_smul, smul_smul]
      congr 2
      simp only [map_mul, map_natCast]
      push_cast
      ring
    rw [key]
    exact sub_mem hw (DictLat.Lf_smul I (iA_mem I (mul_mem (natCast_mem _ ℓ) hy)) (DictLat.iv_mem I hmw))

theorem glue (T : Set (HeightOneSpectrum (𝓞 I.F))) (w : Fin I.n → I.E)
    (h : ∀ q ∈ T, ∃ a : 𝓞 I.F, a ∉ q.asIdeal ∧ algebraMap (𝓞 I.F) (𝓞 I.E) a • w ∈ I.L) :
    iA I (eT T) • iv I w ∈ I.Lf := by
  classical
  obtain ⟨m, hm, hmw⟩ := denomO I w
  set mO : 𝓞 I.F := (m : 𝓞 I.F) with hmO
  have hm0 : mO ≠ 0 := by rw [hmO]; exact_mod_cast hm.ne'
  have hBfin : {v : HeightOneSpectrum (𝓞 I.F) | mO ∈ v.asIdeal}.Finite := by
    have hF : {v : HeightOneSpectrum (𝓞 I.F) | v.valuation I.F (algebraMap (𝓞 I.F) I.F mO) < 1}.Finite := by
      simp_rw [HeightOneSpectrum.valuation_lt_one_iff_dvd]
      apply Ideal.finite_factors
      simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
    simpa only [HeightOneSpectrum.valuation_lt_one_iff_mem] using hF
  let s : Finset (HeightOneSpectrum (𝓞 I.F)) := hBfin.toFinset.filter (· ∈ T)
  let 𝔞 : Ideal (𝓞 I.F) :=
    { carrier := {a | algebraMap (𝓞 I.F) (𝓞 I.E) a • w ∈ I.L}
      add_mem' := fun {a b} ha hb => by
        show algebraMap (𝓞 I.F) (𝓞 I.E) (a + b) • w ∈ I.L
        rw [map_add, add_smul]; exact I.L.add_mem ha hb
      zero_mem' := by
        show algebraMap (𝓞 I.F) (𝓞 I.E) 0 • w ∈ I.L
        rw [map_zero, zero_smul]; exact I.L.zero_mem
      smul_mem' := fun c a ha => by
        show algebraMap (𝓞 I.F) (𝓞 I.E) (c • a) • w ∈ I.L
        rw [smul_eq_mul, map_mul, mul_smul]; exact I.L.smul_mem _ ha }
  have hav : ¬ ((𝔞 : Set (𝓞 I.F)) ⊆ ⋃ i ∈ (↑s : Set (HeightOneSpectrum (𝓞 I.F))), (i.asIdeal : Set (𝓞 I.F))) := by
    have := DictRing.nonempty_places (F := I.F)
    rw [Ideal.subset_union_prime (Classical.arbitrary _) (Classical.arbitrary _) (fun i _ _ _ => i.isPrime)]
    rintro ⟨i, hi, hle⟩
    have hiT : i ∈ T := (Finset.mem_filter.1 hi).2
    obtain ⟨a, ha, haw⟩ := h i hiT
    exact ha (hle (show a ∈ 𝔞 from haw))
  obtain ⟨a, haA, haU⟩ := Set.not_subset.1 hav
  have haw : algebraMap (𝓞 I.F) (𝓞 I.E) a • w ∈ I.L := haA
  have hav' : ∀ v ∈ T, mO ∈ v.asIdeal → a ∉ v.asIdeal := by
    intro v hvT hvm hva
    exact haU (Set.mem_biUnion (x := v) (by simp [s, hvT, hvm]) hva)
  obtain ⟨u0, hu0, hu0v⟩ : ∃ u0 : Af I.F, u0 ∈ Formalism.UG.intAd I.F ∧ ∀ v, u0 v =
      if v ∈ T ∧ mO ∉ v.asIdeal then (algebraMap (𝓞 I.F) (v.adicCompletion I.F) mO)⁻¹ else 0 :=
    ⟨mkI (fun v => if v ∈ T ∧ mO ∉ v.asIdeal then (algebraMap (𝓞 I.F) (v.adicCompletion I.F) mO)⁻¹ else 0)
      (fun v => by split_ifs with hv; exacts [inv_mem' hv.2, zero_mem _]), mkI_mem _ _, fun v => rfl⟩
  obtain ⟨u1, hu1, hu1v⟩ : ∃ u1 : Af I.F, u1 ∈ Formalism.UG.intAd I.F ∧ ∀ v, u1 v =
      if v ∈ T ∧ mO ∈ v.asIdeal then (algebraMap (𝓞 I.F) (v.adicCompletion I.F) a)⁻¹ else 0 :=
    ⟨mkI (fun v => if v ∈ T ∧ mO ∈ v.asIdeal then (algebraMap (𝓞 I.F) (v.adicCompletion I.F) a)⁻¹ else 0)
      (fun v => by split_ifs with hv; exacts [inv_mem' (hav' v hv.1 hv.2), zero_mem _]), mkI_mem _ _,
      fun v => rfl⟩
  have hid : eT T = u0 * algebraMap (𝓞 I.F) (Af I.F) mO + u1 * algebraMap (𝓞 I.F) (Af I.F) a := by
    refine FiniteAdeleRing.ext (K := I.F) fun v => ?_
    rw [comp_add, comp_mul, comp_mul, DictRing.comp_algebraMap, DictRing.comp_algebraMap, hu0v, hu1v]
    by_cases hvT : v ∈ T
    · rw [eT_of_mem hvT]
      by_cases hvm : mO ∈ v.asIdeal
      · rw [if_neg (fun h => h.2 hvm), if_pos ⟨hvT, hvm⟩, zero_mul, zero_add,
          inv_mul_cancel₀ (ne0 (hav' v hvT hvm))]
      · rw [if_pos ⟨hvT, hvm⟩, if_neg (fun h => hvm h.2), zero_mul, add_zero, inv_mul_cancel₀ (ne0 hvm)]
    · rw [eT_of_not hvT, if_neg (fun h => hvT h.1), if_neg (fun h => hvT h.1), zero_mul, zero_mul, add_zero]
  rw [hid, map_add, map_mul, map_mul, add_smul, mul_smul, mul_smul, ← iv_OF, ← iv_OF]
  exact add_mem (DictLat.Lf_smul I (iA_mem I hu0) (DictLat.iv_mem I hmw))
    (DictLat.Lf_smul I (iA_mem I hu1) (DictLat.iv_mem I haw))

theorem norm_hcompl (p : Ideal (𝓞 I.E)) [hp : p.IsPrime] (s : 𝓞 I.E)
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := I.E) p) :
    ∃ a : 𝓞 I.F, algebraMap (𝓞 I.F) (𝓞 I.E) a ∉ p ∧ ∃ t : 𝓞 I.E, algebraMap (𝓞 I.F) (𝓞 I.E) a = t * s := by
  have hinj : Function.Injective (algebraMap (𝓞 I.E) I.E) := IsFractionRing.injective (𝓞 I.E) I.E
  have hP : s ∉ p ∧ ∀ t : 𝓞 I.E, algebraMap (𝓞 I.E) I.E t = star (algebraMap (𝓞 I.E) I.E s) → t ∉ p := by
    unfold Formalism.HermitianLatticesTheory.hcompl at hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one =>
      refine ⟨fun h => hp.ne_top ((Ideal.eq_top_iff_one p).2 h), fun t ht h => hp.ne_top ((Ideal.eq_top_iff_one p).2 ?_)⟩
      have : t = 1 := hinj (by rw [ht, map_one, star_one])
      rwa [this] at h
    | mul x y _ _ hx hy =>
      refine ⟨fun h => (hp.mem_or_mem h).elim hx.1 hy.1, fun t ht h => ?_⟩
      obtain ⟨tx, htx⟩ := DictLat.star_int I x
      obtain ⟨ty, hty⟩ := DictLat.star_int I y
      have : t = tx * ty := hinj (by rw [ht, map_mul, map_mul, star_mul', htx, hty])
      rw [this] at h
      exact (hp.mem_or_mem h).elim (hx.2 tx htx) (hy.2 ty hty)
  obtain ⟨t, ht⟩ := DictLat.star_int I s
  have hfix : star (algebraMap (𝓞 I.E) I.E (t * s)) = algebraMap (𝓞 I.E) I.E (t * s) := by
    rw [map_mul, star_mul', ht, star_star, mul_comm]
  obtain ⟨f, hf⟩ := (I.cm.fixed _).1 hfix
  have hfint : IsIntegral ℤ f := by
    have h1 : IsIntegral ℤ (algebraMap I.F I.E f) := by rw [hf]; exact (t * s).isIntegral_coe
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ I.F I.E) (algebraMap I.F I.E).injective).1 h1
  have hαE : algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) ⟨f, hfint⟩) = algebraMap (𝓞 I.E) I.E (t * s) := by
    exact (coeOF I ⟨f, hfint⟩).trans hf
  have heq := hinj hαE
  refine ⟨⟨f, hfint⟩, ?_, t, heq⟩
  rw [heq]
  exact fun h => (hp.mem_or_mem h).elim (hP.2 t ht) hP.1

theorem loc_iff (p : Ideal (𝓞 I.E)) (hp : p.IsMaximal) (N : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (v : Fin I.n → I.E) :
    v ∈ locE I p N ↔ ∃ a : 𝓞 I.F, a ∉ p.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) ∧
      algebraMap (𝓞 I.F) (𝓞 I.E) a • v ∈ N := by
  have := hp.isPrime
  constructor
  · intro h
    obtain ⟨s, hs, hsv⟩ := (Formalism.HermitianLatticesTheory.locBasic_mem_locS).1 h
    obtain ⟨a, ha, t, hat⟩ := norm_hcompl I p s hs
    refine ⟨a, ha, ?_⟩
    rw [hat, mul_smul]
    exact N.smul_mem t hsv
  · rintro ⟨a, ha, hav⟩
    refine (Formalism.HermitianLatticesTheory.locBasic_mem_locS).2 ⟨algebraMap (𝓞 I.F) (𝓞 I.E) a, ?_, hav⟩
    unfold Formalism.HermitianLatticesTheory.hcompl
    refine Submonoid.subset_closure ⟨ha, fun t ht => ?_⟩
    have hfix : star (algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) a)) =
        algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) a) := by
      rw [coeOF]
      exact (I.cm.fixed _).2 ⟨_, rfl⟩
    rw [hfix] at ht
    rw [IsFractionRing.injective (𝓞 I.E) I.E ht]
    exact ha

theorem loc_congr {p p' : Ideal (𝓞 I.E)} (hp : p.IsMaximal) (hp' : p'.IsMaximal)
    (h : p.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = p'.comap (algebraMap (𝓞 I.F) (𝓞 I.E)))
    (N : Submodule (𝓞 I.E) (Fin I.n → I.E)) : locE I p N = locE I p' N := by
  ext v
  rw [loc_iff I p hp, loc_iff I p' hp', h]

def under (p : Ideal (𝓞 I.E)) (hp : p.IsMaximal) : HeightOneSpectrum (𝓞 I.F) where
  asIdeal := p.comap (algebraMap (𝓞 I.F) (𝓞 I.E))
  isPrime := by have := hp.isPrime; infer_instance
  ne_bot := fun h => Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField I.E)
    (Ideal.eq_bot_of_comap_eq_bot h)

end Inst

end Formalism.L2.SG.Pf.LatDictZ.Z5
