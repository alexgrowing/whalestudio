import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteNotIsUnitOneAddSmul
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AdaptUnitary

open NumberField IsDedekindDomain
open scoped Matrix

section Genus

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.GenusSelfDual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_coprime_nsmul_mem (m : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
    (h : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (m : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal →
      ∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) :
    ∃ k : ℕ, k.Coprime m ∧ k • x ∈ L := by
  let J : Ideal ℤ := (L.toAddSubgroup.toIntSubmodule).comap (LinearMap.toSpanSingleton ℤ _ x)
  have hJ : ∀ k : ℤ, k ∈ J ↔ k • x ∈ L := fun k => Iff.rfl
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal J).principal
  have hg' : ∀ k : ℤ, k • x ∈ L ↔ g ∣ k := fun k => by
    rw [← hJ, hg]; exact Ideal.mem_span_singleton
  refine ⟨g.natAbs, Nat.Coprime.symm (Nat.coprime_of_dvd fun p hp hpm hpg => ?_), ?_⟩
  · obtain ⟨k, hk, hkx⟩ := exists_nsmul_mem hp L x fun v hv => h v (by
      obtain ⟨c, rfl⟩ := hpm
      rw [Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hv)
    rw [← natCast_zsmul, hg', ← Int.natAbs_dvd_natAbs, Int.natAbs_natCast] at hkx
    exact hk (hpg.trans hkx)
  · rw [← natCast_zsmul, hg']
    exact Int.dvd_natAbs.2 dvd_rfl

omit [NumberField E] [IsCMField E] in

theorem exists_coprime_uniform (m : ℕ) {L₁ L₂ : Submodule (𝓞 E) (Fin n → E)} (hL : L₁.FG)
    (h : ∀ x ∈ L₁, ∃ k : ℕ, k.Coprime m ∧ k • x ∈ L₂) : ∃ k : ℕ, k.Coprime m ∧ ∀ x ∈ L₁, k • x ∈ L₂ := by
  obtain ⟨s, rfl⟩ := hL
  choose k hk hkx using fun x : s => h x (Submodule.subset_span x.2)
  refine ⟨∏ x, k x, Nat.Coprime.prod_left fun x _ => hk x, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem k (Finset.mem_univ (⟨x, hx⟩ : s))
    rw [hc, mul_comm, mul_smul]
    exact nsmul_mem (hkx ⟨x, hx⟩) c
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact L₂.smul_mem a hx

theorem exists_unitary_of_selfDual [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {Λ : Lat E n}
    (hΛ : Λ.SelfDual) {m : ℕ} (hm : m ≠ 0) :
    ∃ γ : Matrix (Fin n) (Fin n) E, (γ.map cc)ᵀ * γ = 1 ∧
      (∀ x ∈ Λ.L, ∃ k : ℕ, k.Coprime m ∧ k • (γ.map cc)ᵀ *ᵥ x ∈ stdMod E n) ∧
      ∀ y ∈ stdMod E n, ∃ k : ℕ, k.Coprime m ∧ k • γ *ᵥ y ∈ Λ.L := by
  have hL : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ.L := ⟨Λ.fg, Λ.span_top⟩
  choose h hh hhL using exists_orthonormal_frame (G := 1) (L := Λ.L)
    (fun a b => by simp [cc, Matrix.one_apply, apply_ite, eq_comm]) (by simp) hL
    (fun x => (hΛ x).trans (forall₂_congr fun y _ => by
      rw [herm_one]
      exact ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨_, h⟩, rfl⟩⟩))
  have hh' : ∀ v, ((h v).1.map (locConj v))ᵀ * (h v).1 = 1 := fun v => by
    have := congrArg Matrix.transpose (hh v)
    rwa [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_one] at this
  have hinv : ∀ v, ((h v)⁻¹).1 = ((h v).1.map (locConj v))ᵀ := fun v =>
    Units.inv_eq_of_mul_eq_one_left (hh' v)
  obtain ⟨γ, hγ, hγ'⟩ := exists_unitary_near hm (fun v => (h v).1) hh'
  have hmap : ∀ v (M : Matrix (Fin n) (Fin n) E) (x : Fin n → E),
      (fun i => locEmb v ((M *ᵥ x) i)) = M.map (locEmb v) *ᵥ fun i => locEmb v (x i) :=
    fun v M x => funext fun i => RingHom.map_mulVec (locEmb v) M x i
  refine ⟨γ, hγ, fun x hx => exists_coprime_nsmul_mem m _ _ fun v hv => ?_,
    fun y hy => exists_coprime_nsmul_mem m _ _ fun v hv => ?_⟩
  · have h1 := (hhL v _).1 (Submodule.subset_span ⟨x, hx, rfl⟩)
    have h2 : ∀ i j, (((γ.map cc)ᵀ).map (locEmb v) * (h v).1) i j ∈ locOrder v := fun i j => by
      convert locConj_mem v (hγ' v hv j i) using 1
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, locConj_locConj,
        locConj_locEmb, mul_comm]
    have h3 := mulVec_mem_locOrder v h2 h1
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← hmap] at h3
    exact exists_smul_mem_stdMod v h3
  · refine (locEmb_mem_locLattice_iff v hL _).1 ((hhL v _).2 ?_)
    change ∀ i, (_ *ᵥ fun i => locEmb v ((γ *ᵥ y) i)) i ∈ _
    rw [hmap, Matrix.mulVec_mulVec, hinv]
    refine mulVec_mem_locOrder v (hγ' v hv) fun i => ?_
    obtain ⟨a, ha⟩ := mem_stdMod.1 hy i
    exact ha ▸ locEmb_mem_locOrder v a

open Formalism.L2.Pj in

theorem exists_lat (Λ : GenLat E n) {N : ℕ} (hU : Λ.Unimod) (hN : 0 < N)
    (hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La) : ∃ Λ' : Lat E n, Λ'.L = Λ.La ∧ Λ'.SelfDual := by
  classical
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hs : ∀ j, (N : E) • (Pi.single j 1 : Fin n → E) ∈ Λ.La := fun j => by
    have := hle (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (single_mem_stdMod (E := E) j))
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at this
  have hin : ∀ x ∈ Λ.La, (N : E) • x ∈ stdMod E n := fun x hx => mem_stdMod.2 fun j => by
    obtain ⟨a, ha⟩ := (hU _).1 (hs j) x hx
    refine ⟨a, ha.trans ?_⟩
    simp [Pi.single_apply, apply_ite]
  have hfg : Λ.La.FG := by
    let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) := (LinearMap.lsmul E (Fin n → E) (N : E)).restrictScalars (𝓞 E)
    have hf : Function.Injective f := fun x y h => smul_right_injective _ hN' h
    refine Submodule.fg_of_fg_map_injective f hf ?_
    have h1 : (stdMod E n).FG := (Lat.std E n).fg
    refine Submodule.FG.of_le h1 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hin x hx
  refine ⟨⟨Λ.La, hfg, ?_⟩, rfl, fun x => (hU x).trans (forall₂_congr fun y _ => ?_)⟩
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have := Submodule.smul_mem _ (N : E)⁻¹ (Submodule.subset_span (R := E) (hs j))
    rw [smul_smul, inv_mul_cancel₀ hN', one_smul] at this
    simpa using this
  · have e : stdForm x y = IsCMField.complexConj E (∑ j, IsCMField.complexConj E (x j) * y j) := by
      simp [stdForm]
    have e' : (∑ j, IsCMField.complexConj E (x j) * y j) = IsCMField.complexConj E (stdForm x y) := by
      simp [stdForm]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨IsCMField.ringOfIntegersComplexConj E a, by rw [e, ← ha]; simp⟩
    · rintro ⟨a, ha⟩
      exact ⟨IsCMField.ringOfIntegersComplexConj E a, by rw [e', ← ha]; simp⟩

end Genus

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj in

theorem exists_unitary_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ)
    (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ m : ℕ, 0 < m →
    ∃ (k : ℕ) (ga : Matrix (Fin n) (Fin n) E), Nat.Coprime k m ∧
      (∀ i j, ∑ b, IsCMField.complexConj E (ga b i) * ga b j = if i = j then 1 else 0) ∧
      (∀ v ∈ Λ.La, (k : E) • ga.mulVec v ∈ stdLat E n) ∧
      ∀ v ∈ stdLat E n, ∃ w ∈ Λ.La, (k : E) • v = ga.mulVec w := by
  intro E _ _ _ H n Λ N hU hN hle m hm
  haveI := H.unram
  obtain ⟨Λ', hΛ', hsd⟩ := exists_lat Λ hU hN hle
  obtain ⟨γ, hγ, h₁, h₂⟩ := exists_unitary_of_selfDual hsd hm.ne'
  have hγ₂ := mul_eq_one_comm.1 hγ
  let f : Matrix (Fin n) (Fin n) E → (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
    fun M => (Matrix.mulVecLin M).restrictScalars (𝓞 E)
  obtain ⟨k₁, hk₁, e₁⟩ := exists_coprime_uniform m (L₂ := GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdMod E n)
    (Λ'.fg.map (f (γ.map ReciprocityTheory.ChartRestriction.G.FD.cc)ᵀ)) (by rintro _ ⟨x, hx, rfl⟩; exact h₁ x hx)
  obtain ⟨k₂, hk₂, e₂⟩ := exists_coprime_uniform m (L₂ := Λ'.L)
    ((GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.Lat.std E n).fg.map (f γ)) (by rintro _ ⟨x, hx, rfl⟩; exact h₂ x hx)
  refine ⟨k₁ * k₂, (γ.map ReciprocityTheory.ChartRestriction.G.FD.cc)ᵀ, Nat.Coprime.mul_left hk₁ hk₂, fun i j => ?_, fun v hv => ?_,
    fun v hv => ⟨(k₁ * k₂) • γ *ᵥ v, ?_, ?_⟩⟩
  · have := congrFun (congrFun hγ₂ i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
  · rw [Nat.cast_smul_eq_nsmul, mul_comm, mul_smul]
    exact nsmul_mem (e₁ _ ⟨v, hΛ' ▸ hv, rfl⟩) k₂
  · rw [mul_smul, ← hΛ']
    exact nsmul_mem (e₂ _ ⟨v, hv, rfl⟩) k₁
  · rw [← Nat.cast_smul_eq_nsmul E, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hγ, Matrix.one_mulVec]

end GlobalTheory.AdaptUnitary
