import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifRiem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianRestrictionOrthonormalCoordsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenusEqCardMulSignatureStatement

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace RootFieldNumerics.PC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem mem_eig {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : 𝓞 E →+* Module.End ℂ V} {s : 𝓞 E →+* ℂ} {x : V} :
    x ∈ eigSp ρ s ↔ ∀ a, ρ a x = s a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem ip_sum (R : RiemLat E g Λ) {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → ℂ) (c : κ → ℂ) (u : ι → Fin g → ℂ)
    (w : κ → Fin g → ℂ) :
    R.ip (∑ k, a k • u k) (∑ l, c l • w l) = ∑ k, ∑ l, star (a k) * c l * R.ip (u k) (w l) := by
  simp only [RiemLat.ip, star_sum, star_smul, mulVec_sum, mulVec_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem ip_conj (R : RiemLat E g Λ) (x y : Fin g → ℂ) : (starRingEnd ℂ) (R.ip x y) = R.ip y x :=
  conj_hermForm R.herm y x

theorem ip_zero_left (R : RiemLat E g Λ) (y : Fin g → ℂ) : R.ip 0 y = 0 := by simp [RiemLat.ip]

theorem ip_zero_right (R : RiemLat E g Λ) (y : Fin g → ℂ) : R.ip y 0 = 0 := by simp [RiemLat.ip]

theorem exists_onb (R : RiemLat E g Λ) (W : Submodule ℂ (Fin g → ℂ)) {m : ℕ} (hm : Module.finrank ℂ W = m) :
    ∃ e : Fin m → Fin g → ℂ, (∀ i, e i ∈ W) ∧ (∀ i j, R.ip (e i) (e j) = if i = j then 1 else 0) ∧
      ∀ z ∈ W, ∃ α : Fin m → ℂ, z = ∑ i, α i • e i := by
  classical
  obtain ⟨c, hc⟩ := GlobalTheory.T.hermitian_restriction_orthonormal_coords g m R.Hm R.herm R.pos W hm
  have hinj : Function.Injective (c.comp W.subtype) := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    by_contra h0
    have h1 := R.pos z fun h => h0 (Subtype.ext h)
    have hz' : c z = 0 := hz
    rw [hc z z.2 z z.2, hz'] at h1
    simp at h1
  have hsur : Function.Surjective (c.comp W.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hm])).1 hinj
  choose e he using fun i => hsur (Pi.single i 1)
  refine ⟨fun i => e i, fun i => (e i).2, fun i j => ?_, fun z hz => ⟨c z, ?_⟩⟩
  · have h1 : c (e i) = Pi.single i 1 := he i
    have h2 : c (e j) = Pi.single j 1 := he j
    rw [RiemLat.ip, hc _ (e i).2 _ (e j).2, h1, h2]
    simp [Pi.single_apply, eq_comm]
  · have h : (⟨z, hz⟩ : W) = ∑ i, c z i • e i := by
      apply hinj
      rw [map_sum]
      simp only [map_smul, he]
      ext k
      simp [Pi.single_apply]
    simpa using congrArg Subtype.val h

section Cx

variable (b : Module.Basis (Fin (2 * g)) ℤ Λ)

def Pc (R : RiemLat E g Λ) : (Fin (2 * g) → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ fun k => R.P (b k)

theorem Pc_apply (R : RiemLat E g Λ) (ξ : Fin (2 * g) → ℂ) : Pc b R ξ = ∑ k, ξ k • R.P (b k) := rfl

def io (a : Λ) : Fin (2 * g) → ℂ := fun k => (b.repr a k : ℂ)

theorem star_io (a : Λ) : star (io b a) = io b a := by
  ext k
  simp [io]

theorem Pc_io (R : RiemLat E g Λ) (a : Λ) : Pc b R (io b a) = R.P a := by
  conv_rhs => rw [← b.sum_repr a]
  rw [Pc_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, io, Int.cast_smul_eq_zsmul]

def act (a : 𝓞 E) (ξ : Fin (2 * g) → ℂ) : Fin (2 * g) → ℂ := ∑ k, ξ k • io b (a • b k)

theorem Pc_act (R : RiemLat E g Λ) (a : 𝓞 E) (ξ : Fin (2 * g) → ℂ) : Pc b R (act b a ξ) = R.B a (Pc b R ξ) := by
  rw [act, map_sum, Pc_apply b R ξ, map_sum]
  simp only [map_smul, Pc_io, R.act]

theorem star_act (a : 𝓞 E) (ξ : Fin (2 * g) → ℂ) : star (act b a ξ) = act b a (star ξ) := by
  simp only [act, star_sum, star_smul, star_io, Pi.star_apply]

theorem exists_real (R : RiemLat E g Λ) (e : Fin g → ℂ) : ∃ ξ, star ξ = ξ ∧ Pc b R ξ = e := by
  have he : e ∈ Submodule.span ℝ (Set.range R.P) := by rw [SheetDecomposition.Riem.span_top]; trivial
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨_, star_io b a, Pc_io b R a⟩
  | zero => exact ⟨0, star_zero _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨ξ, h1, h2⟩ := hx
    obtain ⟨ξ', h1', h2'⟩ := hy
    exact ⟨ξ + ξ', by rw [star_add, h1, h1'], by rw [map_add, h2, h2']⟩
  | smul r x _ hx =>
    obtain ⟨ξ, h1, h2⟩ := hx
    exact ⟨(r : ℂ) • ξ, by rw [star_smul, h1]; simp, by rw [map_smul, h2]; rfl⟩

theorem exists_pair (R : RiemLat E g Λ) (e e' : Fin g → ℂ) : ∃ η, Pc b R η = e ∧ Pc b R (star η) = e' := by
  obtain ⟨ξ, h1, h2⟩ := exists_real b R ((2⁻¹ : ℂ) • (e + e'))
  obtain ⟨ξ', h1', h2'⟩ := exists_real b R ((2⁻¹ * Complex.I : ℂ) • (e' - e))
  refine ⟨ξ + Complex.I • ξ', ?_, ?_⟩
  · rw [map_add, map_smul, h2, h2', smul_smul]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination (2⁻¹ * (e' k - e k)) * Complex.I_mul_I
  · rw [star_add, star_smul, h1, h1', map_add, map_smul, h2, h2', smul_smul]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.star_def, Complex.conj_I]
    linear_combination (-2⁻¹ * (e' k - e k)) * Complex.I_mul_I

theorem ext_pair (R : RiemLat E g Λ) {η η' : Fin (2 * g) → ℂ} (h : Pc b R η = Pc b R η')
    (h' : Pc b R (star η) = Pc b R (star η')) : η = η' := by
  let Θ : (Fin (2 * g) → ℂ) →ₗ[ℂ] (Fin g → ℂ) × (Fin g → ℂ) :=
    (Pc b R).prod (Fintype.linearCombination ℂ fun k => star (R.P (b k)))
  have hΘ : ∀ ξ, Θ ξ = (Pc b R ξ, star (Pc b R (star ξ))) := fun ξ => by
    refine Prod.ext rfl ?_
    show ∑ k, ξ k • star (R.P (b k)) = star (∑ k, star ξ k • R.P (b k))
    simp only [star_sum, star_smul, Pi.star_apply, star_star]
  have hs : Function.Surjective Θ := fun ⟨e, e'⟩ => by
    obtain ⟨η, h1, h2⟩ := exists_pair b R e (star e')
    exact ⟨η, by rw [hΘ, h1, h2, star_star]⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [two_mul])).2 hs ?_
  rw [hΘ, hΘ, h, h']

theorem psi_eq (R : RiemLat E g Λ) (ξ ξ' : Fin (2 * g) → ℂ) :
    R.ip (Pc b R ξ) (Pc b R ξ') - R.ip (Pc b R (star ξ')) (Pc b R (star ξ)) =
      ∑ k, ∑ l, star (ξ k) * ξ' l * (2 * (R.form (b l) (b k) : ℂ) * Complex.I) := by
  simp only [Pc_apply, ip_sum]
  rw [Finset.sum_comm (f := fun k l => star (star ξ' k) * star ξ l * R.ip (R.P (b k)) (R.P (b l))), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h := Complex.sub_conj (R.ip (R.P (b k)) (R.P (b l)))
  have h2 : (R.ip (R.P (b k)) (R.P (b l))).im = R.form (b l) (b k) := R.im _ _
  rw [ip_conj, h2] at h
  push_cast at h
  rw [← h, Pi.star_apply, Pi.star_apply, star_star]
  ring

end Cx

theorem mem_of_eig {Ψ : Type} [Fintype Ψ] (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ)
    (W : Submodule ℂ (Fin g → ℂ)) (h : ∀ τ, eigSp B (σ τ) ≤ W) (h' : ∀ τ, eigSp B ((starRingEnd ℂ).comp (σ τ)) ≤ W) :
    W = ⊤ := by
  refine top_unique fun z _ => ?_
  obtain ⟨y, hy, rfl⟩ := SheetDecomposition.Riem.exists_decomp B z
  refine W.sum_mem fun s _ => ?_
  by_cases e : ∃ τ, σ τ = s.comp (algebraMap (𝓞 E) E)
  · obtain ⟨τ, e⟩ := e
    exact h τ (e ▸ hy s)
  · obtain ⟨τ, e'⟩ := not_not.1 (mt (hσ.2 _).2 e)
    refine h' τ ?_
    have : (starRingEnd ℂ).comp (σ τ) = s.comp (algebraMap (𝓞 E) E) := by
      rw [e']
      ext a
      simp
    exact this ▸ hy s

end RootFieldNumerics.PC
