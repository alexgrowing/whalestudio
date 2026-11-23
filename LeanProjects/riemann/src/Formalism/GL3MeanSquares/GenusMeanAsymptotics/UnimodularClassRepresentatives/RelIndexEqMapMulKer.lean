import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulSpanIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MulMemPrimePower

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace J

theorem relIndex_eq_map_mul_ker {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G')
    {A B : AddSubgroup G} (hBA : B ≤ A) :
    B.relIndex A = (B.map f).relIndex (A.map f) * (B ⊓ f.ker).relIndex (A ⊓ f.ker) := by
  have h1 : (B.map f).relIndex (A.map f) = (B ⊔ (A ⊓ f.ker)).relIndex A := by
    rw [AddSubgroup.relIndex_map_map]
    have e1 : A ⊔ f.ker = A ⊔ (B ⊔ f.ker) := by
      rw [← sup_assoc, sup_eq_left.2 hBA]
    rw [e1, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right]
    congr 1
    rw [inf_comm A, sup_inf_assoc_of_le _ hBA]
  have h2 : (B ⊓ f.ker).relIndex (A ⊓ f.ker) = B.relIndex (B ⊔ (A ⊓ f.ker)) := by
    have e2 : B ⊓ f.ker = B ⊓ (A ⊓ f.ker) := by rw [← inf_assoc, inf_eq_left.2 hBA]
    rw [sup_comm, AddSubgroup.relIndex_sup_right, e2, AddSubgroup.inf_relIndex_right]
  rw [h1, h2, mul_comm]
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hBA inf_le_left)).symm

def adjF (s : V →ₗ⋆[K] V →ₗ[K] K) : V →ₗ⋆[K] V →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star (s y x))
    (fun x x' y => by simp) (fun c x y => by simp [starRingEnd_apply]) (fun x y y' => by simp)
    (fun c x y => by simp [starRingEnd_apply])

theorem adjF_apply (s : V →ₗ⋆[K] V →ₗ[K] K) (x y : V) : adjF s x y = star (s y x) := rfl

def symF : (V →ₗ⋆[K] V →ₗ[K] K) →+ (V →ₗ⋆[K] V →ₗ[K] K) where
  toFun s := s + adjF s
  map_zero' := by
    ext x y
    simp [adjF_apply]
  map_add' s t := by
    ext x y
    simp only [LinearMap.add_apply, adjF_apply, star_add]
    ring

theorem symF_apply (s : V →ₗ⋆[K] V →ₗ[K] K) (x y : V) : symF s x y = s x y + star (s y x) := rfl

theorem exists_skew_unit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    ∃ δ : K, star δ = -δ ∧ δ ≠ 0 ∧ δ ∈ pK K 𝔭 0 ∧ δ⁻¹ ∈ pK K 𝔭 0 := by
  obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
  set d : 𝓞 K := θ - conjO K θ with hd
  have hcd : conjO K d = -d := by
    rw [hd, map_sub, conjO_conjO, neg_sub]
  obtain ⟨n, hn⟩ := (conjO_eq_iff_mem_range hF (d * conjO K d)).1 (by
    rw [map_mul, conjO_conjO, mul_comm])
  have hone : (1 : 𝓞 K) ∉ extP K 𝔭 := by
    intro h1
    have h3 := (idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 1 1).1 (by rwa [map_one, pow_one])
    rw [pow_one] at h3
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hn𝔭 : n ∉ 𝔭 := by
    intro hmem
    have h1 : d * conjO K d ∈ extP K 𝔭 ^ 1 := by
      rw [← hn, pow_one]
      exact Ideal.mem_map_of_mem _ hmem
    have h2 := idealPowerSpanBounds.mem_of_unit_mul_mem hθ h1
    have h3 : d * 1 ∈ extP K 𝔭 ^ 1 := by
      rw [hcd] at h2
      simpa using h2
    have h4 := idealPowerSpanBounds.mem_of_unit_mul_mem hθ h3
    rw [pow_one] at h4
    exact hone h4
  have hd0 : d ≠ 0 := by
    intro h0
    apply hn𝔭
    have : algebraMap (𝓞 F) (𝓞 K) n = algebraMap (𝓞 F) (𝓞 K) 0 := by rw [hn, h0]; simp
    rw [idealPowerSpanBounds.ι_inj this]
    exact 𝔭.zero_mem
  have hdK : ((d : 𝓞 K) : K) ≠ 0 := by
    intro h0
    exact hd0 (RingOfIntegers.ext (h0.trans (map_zero (algebraMap (𝓞 K) K)).symm))
  refine ⟨(d : K), ?_, hdK, algebraMap_mem_pK 𝔭 d, ?_⟩
  · rw [← conjO_coe, hcd]
    exact map_neg (algebraMap (𝓞 K) K) _
  · refine (mem_pK h𝔭).2 ⟨n, hn𝔭, conjO K d, by simp, ?_⟩
    have e : algebraMap F K (n : F) = (d : K) * ((conjO K d : 𝓞 K) : K) := by
      have := congrArg (algebraMap (𝓞 K) K) hn
      rw [map_mul] at this
      rw [← this]
      rfl
    rw [e]
    field_simp

theorem map_symF_sesqL (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (A : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    (sesqL A 𝔭 k).map symF = hermL A 𝔭 k := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨fun x y => ?_, fun x hx y hy => ?_⟩
    · rw [symF_apply, symF_apply, star_add, star_star, add_comm]
    · rw [symF_apply]
      exact (pK K 𝔭 k).add_mem (hs x hx y hy) (star_mem_pK hF h𝔭 (hs y hy x hx))
  · rintro ⟨ht, ht'⟩
    obtain ⟨θ, hθ⟩ := exists_add_conj_eq hK hF (1 : 𝓞 F)
    have hθK : (θ : K) + star (θ : K) = 1 := by
      have := congrArg (algebraMap (𝓞 K) K) hθ
      rw [map_add, map_one, map_one] at this
      exact this
    refine ⟨(θ : K) • t, fun x hx y hy => ?_, ?_⟩
    · have := (pK K 𝔭 k).smul_mem θ (ht' x hx y hy)
      rw [Algebra.smul_def] at this
      exact this
    · ext x y
      rw [symF_apply]
      simp only [LinearMap.smul_apply, smul_eq_mul, star_mul', ht y x]
      rw [← add_mul, hθK, one_mul]

theorem map_smul_hermL (A : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) {δ : K} (hδ : star δ = -δ) (hδ0 : δ ≠ 0)
    (hδ1 : δ ∈ pK K 𝔭 0) (hδ2 : δ⁻¹ ∈ pK K 𝔭 0) :
    (hermL A 𝔭 k).map (DistribSMul.toAddMonoidHom (V →ₗ⋆[K] V →ₗ[K] K) δ) =
      sesqL A 𝔭 k ⊓ (symF (K := K) (V := V)).ker := by
  ext s
  constructor
  · rintro ⟨t, ⟨ht, ht'⟩, rfl⟩
    refine ⟨fun x hx y hy => ?_, ?_⟩
    · have := mul_mem_pK h𝔭 hδ1 (ht' x hx y hy)
      rw [zero_add] at this
      simpa using this
    · show symF _ = 0
      ext x y
      rw [symF_apply]
      simp only [DistribSMul.toAddMonoidHom_apply, LinearMap.smul_apply, smul_eq_mul,
        star_mul', ht y x, hδ, LinearMap.zero_apply]
      ring
  · rintro ⟨hs, hs'⟩
    replace hs' : symF s = 0 := hs'
    have hsk : ∀ x y, star (s x y) = - s y x := fun x y => by
      have := congrArg (fun u => u y x) hs'
      simp only [symF_apply, LinearMap.zero_apply] at this
      exact (neg_eq_of_add_eq_zero_right this).symm
    refine ⟨δ⁻¹ • s, ⟨fun x y => ?_, fun x hx y hy => ?_⟩, ?_⟩
    · simp only [LinearMap.smul_apply, smul_eq_mul, star_mul', star_inv₀, hδ, hsk x y]
      rw [inv_neg]
      ring
    · have := mul_mem_pK h𝔭 hδ2 (hs x hx y hy)
      rw [zero_add] at this
      simpa using this
    · simp only [DistribSMul.toAddMonoidHom_apply]
      rw [smul_smul, mul_inv_cancel₀ hδ0, one_smul]

theorem one_mem_pK (𝔭 : Ideal (𝓞 F)) : (1 : K) ∈ pK K 𝔭 0 := by
  simpa using algebraMap_mem_pK (K := K) 𝔭 1

theorem mul_mem_pK_zero {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {x y : K} (hx : x ∈ pK K 𝔭 0)
    (hy : y ∈ pK K 𝔭 0) : x * y ∈ pK K 𝔭 0 :=
by
  have := mul_mem_pK h𝔭 hx hy
  rwa [add_zero] at this

theorem nO_one {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : nO 𝔭 (1 : K) = 1 :=
  nO_unit h𝔭 (one_mem_pK 𝔭) (by simpa using one_mem_pK (K := K) 𝔭) one_ne_zero

theorem nO_prod {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ι : Type} (s : Finset ι) (z : ι → K)
    (hz : ∀ i, z i ∈ pK K 𝔭 0 ∧ z i ≠ 0) :
    (∏ i ∈ s, z i) ∈ pK K 𝔭 0 ∧ nO 𝔭 (∏ i ∈ s, z i) = ∏ i ∈ s, nO 𝔭 (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ⟨one_mem_pK (K := K) 𝔭, nO_one (K := K) h𝔭⟩
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ⟨mul_mem_pK_zero h𝔭 (hz i).1 ih.1, by rw [nO_mul h𝔭 (hz i).1 (hz i).2 ih.1, ih.2]⟩

theorem nO_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {z : K} (hz : z ∈ pK K 𝔭 0) (hz0 : z ≠ 0)
    (n : ℕ) : z ^ n ∈ pK K 𝔭 0 ∧ nO 𝔭 (z ^ n) = nO 𝔭 z ^ n := by
  simpa using nO_prod h𝔭 (Finset.range n) (fun _ => z) (fun _ => ⟨hz, hz0⟩)

theorem form_rel (s : V →ₗ⋆[K] V →ₗ[K] K) {x y x' y' : V} {γ u v : K} (hx : γ • x' = u • x)
    (hy : γ • y' = v • y) : star γ * γ * s x' y' = star u * v * s x y := by
  have h1 : s (γ • x') (γ • y') = s (u • x) (v • y) := by rw [hx, hy]
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply]
    at h1
  linear_combination h1

theorem gram_rel (h : V →ₗ⋆[K] V →ₗ[K] K) {m : ℕ} (a b : Fin m → V) (e : Fin m → K) (γ : K)
    (hab : ∀ i, γ • b i = e i • a i) :
    (star γ * γ) ^ m * (Matrix.of fun i j => h (b i) (b j)).det =
      ((∏ i, star (e i)) * ∏ i, e i) * (Matrix.of fun i j => h (a i) (a j)).det := by
  have h1 : (star γ * γ) • (Matrix.of fun i j => h (b i) (b j)) =
      Matrix.diagonal (fun i => star (e i)) * (Matrix.of fun i j => h (a i) (a j)) *
        Matrix.diagonal e := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [form_rel h (hab i) (hab j)]
    ring
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    Fintype.card_fin] at h2
  rw [h2]
  ring

end J

theorem relIndex_sesqL_eq_sq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (A₀ B₀ : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k k' : ℕ}
    (hle : sesqL (locF 𝔭 B₀) 𝔭 k' ≤ sesqL (locF 𝔭 A₀) 𝔭 k) :
    (sesqL (locF 𝔭 B₀) 𝔭 k').relIndex (sesqL (locF 𝔭 A₀) 𝔭 k) =
      (hermL (locF 𝔭 B₀) 𝔭 k').relIndex (hermL (locF 𝔭 A₀) 𝔭 k) ^ 2 := by
  obtain ⟨δ, hδ, hδ0, hδ1, hδ2⟩ := J.exists_skew_unit hK hF h𝔭
  rw [J.relIndex_eq_map_mul_ker J.symF hle, J.map_symF_sesqL hK hF _ h𝔭, J.map_symF_sesqL hK hF _ h𝔭,
    ← J.map_smul_hermL _ h𝔭 k' hδ hδ0 hδ1 hδ2, ← J.map_smul_hermL _ h𝔭 k hδ hδ0 hδ1 hδ2,
    AddSubgroup.relIndex_map_map_of_injective, sq]
  intro s t hst
  have := congrArg (fun u => δ⁻¹ • u) hst
  simpa [smul_smul, inv_mul_cancel₀ hδ0] using this

theorem relIndex_sesqL (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsLattice K B₀) (hB₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k c : ℕ}
    (hle : sesqL (locF 𝔭 B₀) 𝔭 (k + c) ≤ sesqL (locF 𝔭 A₀) 𝔭 k) :
    (sesqL (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (sesqL (locF 𝔭 A₀) 𝔭 k) *
        Ideal.absNorm 𝔭 ^ (2 * (finrank K V * vd h (locF 𝔭 B₀) 𝔭)) =
      Ideal.absNorm 𝔭 ^ (2 * (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭)) := by
  classical
  obtain ⟨a, b, e, γ, hγ, he, hA, hB, hab⟩ := exists_smith hA₀ hB₀ h𝔭
  have habK : ∀ i, (γ : K) • b i = (e i : K) • a i := fun i => by
    rw [algebraMap_smul, algebraMap_smul]
    exact hab i
  have hγK : (γ : K) ≠ 0 := fun h0 =>
    hγ (RingOfIntegers.ext (h0.trans (map_zero (algebraMap (𝓞 K) K)).symm))
  have heK : ∀ i, (e i : K) ≠ 0 := fun i h0 =>
    he i (RingOfIntegers.ext (h0.trans (map_zero (algebraMap (𝓞 K) K)).symm))
  have hγm : (γ : K) ∈ pK K 𝔭 0 := algebraMap_mem_pK 𝔭 γ
  have hem : ∀ i, (e i : K) ∈ pK K 𝔭 0 := fun i => algebraMap_mem_pK 𝔭 (e i)
  have hγγ : star (γ : K) * γ ∈ pK K 𝔭 0 ∧ star (γ : K) * γ ≠ 0 :=
    ⟨J.mul_mem_pK_zero h𝔭 (star_mem_pK hF h𝔭 hγm) hγm, mul_ne_zero (star_ne_zero.2 hγK) hγK⟩
  let Φ : (V →ₗ⋆[K] V →ₗ[K] K) →+ Matrix (Fin (finrank K V)) (Fin (finrank K V)) K :=
    (LinearMap.toMatrix₂ a a).toLinearMap.toAddMonoidHom
  have hΦ : ∀ s i j, Φ s i j = s (a i) (a j) := fun s i j => LinearMap.toMatrix₂_apply a a s i j
  have hΦs : Function.Surjective Φ := (LinearMap.toMatrix₂ a a).surjective
  let f : Fin (finrank K V) → Fin (finrank K V) → K := fun i j => star (e i : K) * (e j : K)
  let g : Fin (finrank K V) → Fin (finrank K V) → K := fun _ _ => star (γ : K) * γ
  have hSA : sesqL (locF 𝔭 A₀) 𝔭 k = (matL 𝔭 k (fun _ _ => 1) (fun _ _ => 1)).comap Φ := by
    ext s
    rw [← hA, mem_sesqL_iff hF a h𝔭]
    constructor
    · intro H i j
      exact ⟨_, H i j, by rw [hΦ]⟩
    · intro H i j
      obtain ⟨w, hw, e⟩ := H i j
      rw [one_mul, one_mul, hΦ] at e
      rwa [e]
  have hSB : sesqL (locF 𝔭 B₀) 𝔭 (k + c) = (matL 𝔭 (k + c) f g).comap Φ := by
    ext s
    rw [← hB, mem_sesqL_iff hF b h𝔭]
    constructor
    · intro H i j
      exact ⟨_, H i j, by rw [hΦ]; exact (J.form_rel s (habK i) (habK j)).symm⟩
    · intro H i j
      obtain ⟨w, hw, e⟩ := H i j
      rw [hΦ] at e
      have e2 : star (γ : K) * γ * s (b i) (b j) = star (γ : K) * γ * w :=
        (J.form_rel s (habK i) (habK j)).trans e
      rwa [mul_left_cancel₀ hγγ.2 e2]
  have hle' : matL 𝔭 (k + c) f g ≤ matL 𝔭 k (fun _ _ => 1) (fun _ _ => 1) := by
    rw [hSA, hSB] at hle
    exact (AddSubgroup.comap_le_comap_of_surjective hΦs).1 hle
  have hf : ∀ i j, f i j ∈ pK K 𝔭 0 ∧ f i j ≠ 0 := fun i j =>
    ⟨J.mul_mem_pK_zero h𝔭 (star_mem_pK hF h𝔭 (hem i)) (hem j),
      mul_ne_zero (star_ne_zero.2 (heK i)) (heK j)⟩
  have H1 := relIndex_matL hK hF h𝔭 f g hf (fun _ _ => hγγ) k c hle'
  have hidx : (sesqL (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (sesqL (locF 𝔭 A₀) 𝔭 k) =
      (matL 𝔭 (k + c) f g).relIndex (matL 𝔭 k (fun _ _ => 1) (fun _ _ => 1)) := by
    rw [hSA, hSB, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hΦs]
  rw [← hidx] at H1
  obtain ⟨hDa, hDa0, hDan⟩ := nO_gram hK hF hs hd hA₀ hA₀i h𝔭 a hA
  obtain ⟨hDb, hDb0, hDbn⟩ := nO_gram hK hF hs hd hB₀ hB₀i h𝔭 b hB
  have hnf : ∀ i j, nO 𝔭 (f i j) = nO 𝔭 (e i : K) * nO 𝔭 (e j : K) := fun i j => by
    rw [nO_mul h𝔭 (star_mem_pK hF h𝔭 (hem i)) (star_ne_zero.2 (heK i)) (hem j), nO_star hF h𝔭]
  have hng : nO 𝔭 (star (γ : K) * γ) = nO 𝔭 (γ : K) * nO 𝔭 (γ : K) := by
    rw [nO_mul h𝔭 (star_mem_pK hF h𝔭 hγm) (star_ne_zero.2 hγK) hγm, nO_star hF h𝔭]
  have H2 := congrArg (nO 𝔭) (J.gram_rel h a b (fun i => (e i : K)) γ habK)
  have hp1 := J.nO_prod h𝔭 Finset.univ (fun i => star (e i : K))
    (fun i => ⟨star_mem_pK hF h𝔭 (hem i), star_ne_zero.2 (heK i)⟩)
  have hp2 := J.nO_prod h𝔭 Finset.univ (fun i => (e i : K)) (fun i => ⟨hem i, heK i⟩)
  have hp3 := J.nO_pow h𝔭 hγγ.1 hγγ.2 (finrank K V)
  rw [nO_mul h𝔭 hp3.1 (pow_ne_zero _ hγγ.2) hDb, hp3.2, hng, hDbn,
    nO_mul h𝔭 (J.mul_mem_pK_zero h𝔭 hp1.1 hp2.1)
      (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => star_ne_zero.2 (heK i))
        (Finset.prod_ne_zero_iff.2 fun i _ => heK i)) hDa,
    nO_mul h𝔭 hp1.1 (Finset.prod_ne_zero_iff.2 fun i _ => star_ne_zero.2 (heK i)) hp2.1,
    hp1.2, hp2.2, hDan] at H2
  simp only [nO_star hF h𝔭] at H2
  simp only [hnf, g, hng, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_pow] at H1
  have hE0 : (∏ i, nO 𝔭 (e i : K)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => nO_ne_zero hK hF h𝔭 (hem i) (heK i)
  generalize (∏ i, nO 𝔭 (e i : K)) = E at H1 H2 hE0
  generalize nO 𝔭 (γ : K) = G at H1 H2
  generalize (sesqL (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (sesqL (locF 𝔭 A₀) 𝔭 k) = X at H1 ⊢
  generalize Ideal.absNorm 𝔭 = q at H1 H2 ⊢
  generalize vd h (locF 𝔭 A₀) 𝔭 = vA at H2 ⊢
  generalize vd h (locF 𝔭 B₀) 𝔭 = vB at H2 ⊢
  generalize finrank K V = m at H1 H2 ⊢
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero m hE0) (pow_ne_zero m hE0)))
  calc X * q ^ (2 * (m * vB)) * (E ^ m * E ^ m) = (X * (E ^ m * E ^ m)) * q ^ (2 * (m * vB)) := by ring
    _ = (G ^ m) ^ m * (G ^ m) ^ m * q ^ (2 * m ^ 2 * c) * q ^ (2 * (m * vB)) := by rw [H1]
    _ = ((G * G) ^ m * q ^ (2 * vB)) ^ m * q ^ (2 * m ^ 2 * c) := by ring
    _ = (E * E * q ^ (2 * vA)) ^ m * q ^ (2 * m ^ 2 * c) := by rw [H2]
    _ = q ^ (2 * (m ^ 2 * c + m * vA)) * (E ^ m * E ^ m) := by ring

theorem relIndex_hermL (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsLattice K B₀) (hB₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k c : ℕ}
    (hle : sesqL (locF 𝔭 B₀) 𝔭 (k + c) ≤ sesqL (locF 𝔭 A₀) 𝔭 k) :
    (hermL (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (hermL (locF 𝔭 A₀) 𝔭 k) *
        Ideal.absNorm 𝔭 ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) =
      Ideal.absNorm 𝔭 ^ (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭) := by
  have h1 := relIndex_sesqL hK hF hs hd hA₀ hA₀i hB₀ hB₀i h𝔭 hle
  rw [relIndex_sesqL_eq_sq hK hF A₀ B₀ h𝔭 hle] at h1
  apply Nat.pow_left_injective (n := 2) (by norm_num)
  show _ ^ 2 = _ ^ 2
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm _ 2, mul_comm _ 2]
  exact h1

end Formalism.HermitianLattices.Ext.L3.D2
