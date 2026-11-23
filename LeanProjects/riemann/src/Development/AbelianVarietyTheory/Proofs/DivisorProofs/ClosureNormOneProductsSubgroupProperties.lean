import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA.Grp
variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a b : R}

theorem cont_coords : Continuous (coords : ℍ[R, a, b] → Fin 4 → R) := continuous_induced_dom
theorem cont_re : Continuous (fun x : ℍ[R, a, b] => x.re) := (continuous_apply 0).comp cont_coords
theorem cont_imI : Continuous (fun x : ℍ[R, a, b] => x.imI) := (continuous_apply 1).comp cont_coords
theorem cont_imJ : Continuous (fun x : ℍ[R, a, b] => x.imJ) := (continuous_apply 2).comp cont_coords
theorem cont_imK : Continuous (fun x : ℍ[R, a, b] => x.imK) := (continuous_apply 3).comp cont_coords

theorem cont_of {X : Type*} [TopologicalSpace X] {f : X → ℍ[R, a, b]}
    (h0 : Continuous fun x => (f x).re) (h1 : Continuous fun x => (f x).imI)
    (h2 : Continuous fun x => (f x).imJ) (h3 : Continuous fun x => (f x).imK) : Continuous f := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem cont_mul : Continuous (fun p : ℍ[R, a, b] × ℍ[R, a, b] => p.1 * p.2) := by
  have r1 := (cont_re (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have i1 := (cont_imI (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have j1 := (cont_imJ (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have k1 := (cont_imK (a := a) (b := b)).comp (continuous_fst : Continuous (Prod.fst : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have r2 := (cont_re (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have i2 := (cont_imI (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have j2 := (cont_imJ (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  have k2 := (cont_imK (a := a) (b := b)).comp (continuous_snd : Continuous (Prod.snd : ℍ[R, a, b] × ℍ[R, a, b] → ℍ[R, a, b]))
  simp only [Function.comp_def] at r1 i1 j1 k1 r2 i2 j2 k2
  apply cont_of <;> simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] <;> fun_prop

theorem cont_star : Continuous (fun x : ℍ[R, a, b] => star x) := by
  have r1 := cont_re (a := a) (b := b)
  have i1 := cont_imI (a := a) (b := b)
  have j1 := cont_imJ (a := a) (b := b)
  have k1 := cont_imK (a := a) (b := b)
  apply cont_of <;> simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star] <;> fun_prop

theorem cont_nrm : Continuous (nrm : ℍ[R, a, b] → R) := by
  have r1 := cont_re (a := a) (b := b)
  have i1 := cont_imI (a := a) (b := b)
  have j1 := cont_imJ (a := a) (b := b)
  have k1 := cont_imK (a := a) (b := b)
  unfold nrm
  fun_prop

theorem cont_conj (c d : ℍ[R, a, b]) : Continuous fun y : ℍ[R, a, b] => c * y * d := by
  have h1 : Continuous fun p : ℍ[R, a, b] × ℍ[R, a, b] => p.1 * p.2 := cont_mul
  have hl : Continuous fun y : ℍ[R, a, b] => c * y :=
    h1.comp (Continuous.prodMk (continuous_const : Continuous fun _ : ℍ[R, a, b] => c) continuous_id)
  exact h1.comp (Continuous.prodMk hl (continuous_const : Continuous fun _ : ℍ[R, a, b] => d))

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem nrm_star (x : ℍ[R, a, b]) : nrm (star x) = nrm x := by
  simp [nrm]

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem star_mul_eq (x : ℍ[R, a, b]) : star x * x = algebraMap R ℍ[R, a, b] (nrm x) := by
  ext <;> simp [nrm, QuaternionAlgebra.algebraMap_eq] <;> ring

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem nrm_one' : nrm (1 : ℍ[R, a, b]) = 1 := by simp [nrm]

end GlobalTheory.QSA.Grp

namespace GlobalTheory.QSA.Grp
variable {F : Type} [Field F] [NumberField F] {a b : F}

theorem rat_mul (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]

theorem rat_one : rat (1 : ℍ[F, a, b]) = 1 := by
  ext <;> simp [rat]

theorem rat_star (x : ℍ[F, a, b]) : rat (star x) = star (rat x) := by
  ext <;> simp [rat]

theorem supp {ε : AF F} (p q u : DA F a b) (hu : ε • u = u) : ε • (p * u * q) = p * u * q := by
  rw [← smul_mul_assoc, ← mul_smul_comm, hu]

theorem rat_inv {γ : ℍ[F, a, b]} (hγ : nrm γ = 1) :
    rat γ * rat (star γ) = 1 ∧ rat (star γ) * rat γ = 1 := by
  constructor
  · rw [← rat_mul, mul_star_eq, hγ, map_one, rat_one]
  · rw [← rat_mul, star_mul_eq, hγ, map_one, rat_one]

theorem nrm_of_mem {ε : AF F} {x : DA F a b} (hx : x ∈ H0 ε) : nrm x = 1 := by
  obtain ⟨γ, hγ, h, hh, -, rfl⟩ := hx
  rw [nrm_mul, nrm_rat, hγ, hh, map_one, one_mul]

theorem mul_mem {ε : AF F} {x y : DA F a b} (hx : x ∈ H0 ε) (hy : y ∈ H0 ε) : x * y ∈ H0 ε := by
  obtain ⟨γ, hγ, h, hh, hs, rfl⟩ := hx
  obtain ⟨γ', hγ', h', hh', hs', rfl⟩ := hy
  obtain ⟨e1, e2⟩ := rat_inv hγ'
  refine ⟨γ * γ', by rw [nrm_mul, hγ, hγ', one_mul], rat (star γ') * h * rat γ' * h', ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, nrm_mul, hh, hh', nrm_rat, nrm_rat, nrm_star, hγ', map_one]; ring
  · have : rat (star γ') * h * rat γ' * h' - 1
        = rat (star γ') * (h - 1) * (rat γ' * h') + (h' - 1) := by
      rw [show rat (star γ') * (h - 1) * (rat γ' * h')
          = rat (star γ') * h * rat γ' * h' - rat (star γ') * rat γ' * h' by noncomm_ring, e2, one_mul]
      abel
    rw [this, smul_add, hs', supp _ _ _ hs]
  · rw [rat_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (rat γ') (rat (star γ')), e1, one_mul]

theorem star_mem {ε : AF F} {x : DA F a b} (hx : x ∈ H0 ε) : star x ∈ H0 ε := by
  obtain ⟨γ, hγ, h, hh, hs, rfl⟩ := hx
  obtain ⟨e1, e2⟩ := rat_inv hγ
  refine ⟨star γ, by rw [nrm_star, hγ], rat γ * star h * rat (star γ), ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, nrm_star, hh, nrm_rat, nrm_rat, nrm_star, hγ, map_one]; ring
  · have hs1 : ε • star (h - 1) = star (h - 1) := by
      rw [← QuaternionAlgebra.star_smul, hs]
    have : rat γ * star h * rat (star γ) - 1 = rat γ * star (h - 1) * rat (star γ) := by
      rw [star_sub, star_one, show rat γ * (star h - 1) * rat (star γ)
          = rat γ * star h * rat (star γ) - rat γ * rat (star γ) by noncomm_ring, e1]
    rw [this, supp _ _ _ hs1]
  · rw [star_mul, ← rat_star]
    simp only [← mul_assoc]
    rw [e2, one_mul]

theorem inv_right {δ δ' : ℍ[F, a, b]} (h : δ * δ' = 1) : δ' * δ = 1 := by
  have hn : nrm δ' * nrm δ = 1 := by rw [mul_comm, ← nrm_mul, h, nrm_one']
  have e : star δ * δ * δ' * δ = star δ * δ := by rw [mul_assoc (star δ), h, mul_one]
  rw [star_mul_eq] at e
  calc δ' * δ = algebraMap F ℍ[F, a, b] (nrm δ' * nrm δ) * (δ' * δ) := by rw [hn, map_one, one_mul]
    _ = algebraMap F ℍ[F, a, b] (nrm δ') * (algebraMap F ℍ[F, a, b] (nrm δ) * δ' * δ) := by
      rw [map_mul]; simp only [mul_assoc]
    _ = 1 := by rw [e, ← map_mul, hn, map_one]

theorem conj_mem {ε : AF F} {δ δ' : ℍ[F, a, b]} (hδ : δ * δ' = 1) {x : DA F a b} (hx : x ∈ H0 ε) :
    rat δ * x * rat δ' ∈ H0 ε := by
  obtain ⟨γ, hγ, h, hh, hs, rfl⟩ := hx
  have hδ2 := inv_right hδ
  have e1 : rat δ * rat δ' = 1 := by rw [← rat_mul, hδ, rat_one]
  have e2 : rat δ' * rat δ = 1 := by rw [← rat_mul, hδ2, rat_one]
  have hn : nrm δ * nrm δ' = 1 := by rw [← nrm_mul, hδ, nrm_one']
  refine ⟨δ * γ * δ', by rw [nrm_mul, nrm_mul, hγ, mul_one, hn], rat δ * h * rat δ', ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, hh, nrm_rat, nrm_rat, mul_one, ← map_mul, hn, map_one]
  · have : rat δ * h * rat δ' - 1 = rat δ * (h - 1) * rat δ' := by
      rw [show rat δ * (h - 1) * rat δ' = rat δ * h * rat δ' - rat δ * rat δ' by noncomm_ring, e1]
    rw [this, supp _ _ _ hs]
  · rw [rat_mul, rat_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (rat δ') (rat δ), e2, one_mul]

end GlobalTheory.QSA.Grp

namespace GlobalTheory.QSA.Grp

theorem t2Space_adeleRing_numberField (F : Type) [Field F] [NumberField F] : T2Space (AF F) :=
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  haveI : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem closure_normOneProducts_subgroup_properties : ∀ (F : Type) [Field F] [NumberField F] (a b : F) (ε : AF F), ε * ε = ε →
    (∀ x ∈ closure (H0 (a := a) (b := b) ε), ∀ y ∈ closure (H0 (a := a) (b := b) ε),
      x * y ∈ closure (H0 (a := a) (b := b) ε)) ∧
    (∀ x ∈ closure (H0 (a := a) (b := b) ε), star x ∈ closure (H0 (a := a) (b := b) ε)) ∧
    (∀ δ δ' : ℍ[F, a, b], δ * δ' = 1 → ∀ x ∈ closure (H0 (a := a) (b := b) ε),
      rat δ * x * rat δ' ∈ closure (H0 (a := a) (b := b) ε)) ∧
    (∀ x ∈ closure (H0 (a := a) (b := b) ε), nrm x = 1) := by
  intro F _ _ a b ε _
  haveI := t2Space_adeleRing_numberField F
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_, fun δ δ' hδ x hx => ?_, fun x hx => ?_⟩
  · exact map_mem_closure₂ cont_mul hx hy fun u hu v hv => mul_mem hu hv
  · exact map_mem_closure cont_star hx fun u hu => star_mem hu
  · have hc : Continuous fun y : DA F a b => rat δ * y * rat δ' := cont_conj (rat δ) (rat δ')
    have hm : Set.MapsTo (fun y : DA F a b => rat δ * y * rat δ') (H0 ε) (H0 ε) :=
      fun u hu => conj_mem hδ hu
    have key := map_mem_closure (x := x) hc hx hm
    exact key
  · have hcl : IsClosed {y : DA F a b | nrm y = 1} := isClosed_eq cont_nrm continuous_const
    exact closure_minimal (fun y hy => nrm_of_mem hy) hcl hx

end GlobalTheory.QSA.Grp
