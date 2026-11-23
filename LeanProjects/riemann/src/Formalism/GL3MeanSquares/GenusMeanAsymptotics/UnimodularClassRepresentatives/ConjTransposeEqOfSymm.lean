import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ConjTransposeMapMk
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardUnitaryReduction

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem IsE.mono {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e c : ℕ}
    (he : IsE h A 𝔭 e) (hec : e ≤ c) : IsE h A 𝔭 c :=
  fun x hx t ht => he x hx t (Ideal.pow_le_pow_right hec ht)

theorem akCount_basis [hFF : Fact (IsFixF K F)] (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    akCount h (locF 𝔭 (spanO b)) 𝔭 k = Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) //
      Xᴴ * Hq H 𝔭 k * X = Hq H 𝔭 k} := by
  rw [localizedQuotients.akCount_locF hFF.out h _ 𝔭 h𝔭, akCount_free h b hH h𝔭]

theorem map_factor_map_mk (𝔭 : Ideal (𝓞 F)) {j k : ℕ} (hjk : j ≤ k) (Y : Matrix κ κ (𝓞 K)) :
    (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))).map
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right hjk)) = Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ j)) := by
  ext i l
  rfl

theorem redCount_basis [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c j : ℕ}
    (he : IsE h (locF 𝔭 (spanO b)) 𝔭 c) (hj : 1 ≤ j) :
    redCount h (locF 𝔭 (spanO b)) 𝔭 j = Nat.card {X' : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ j) //
      ∃ X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + c)), Xᴴ * Hq H 𝔭 (j + c) * X = Hq H 𝔭 (j + c) ∧
        X.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right j c))) = X'} := by
  have := h𝔭.isPrime
  have hF : IsFixF K F := hFF.out
  unfold redCount
  refine Nat.card_congr ((eL h𝔭 b j).subtypeEquiv fun X => ?_)
  constructor
  · rintro ⟨g, hg, hgX⟩
    obtain ⟨Y, hY1, hY2⟩ := exists_matrix_of_isom hF b hH h𝔭 hg (j + c)
    refine ⟨Y.map (Ideal.Quotient.mk _), (mk_form_iff 𝔭 _ H Y).2 hY1, ?_⟩
    rw [map_factor_map_mk 𝔭 (Nat.le_add_right j c), eq_comm, eL_eq_iff]
    intro i
    obtain ⟨y, hy1, hy2⟩ := hgX (inA 𝔭 b (cmb b (Pi.single i 1)))
    rw [hy2, mk_eq_iff, hy1, coe_inA, coe_cmb_single, coe_inA, coe_cmb]
    exact smul_mono_pow (Nat.le_add_right j c) (hY2 i)
  · rintro ⟨X', hX', hmap⟩
    obtain ⟨Y, rfl⟩ := exists_map_mk 𝔭 _ X'
    rw [map_factor_map_mk 𝔭 (Nat.le_add_right j c), eq_comm, eL_eq_iff] at hmap
    obtain ⟨g, hg, hgY⟩ := exists_isom_matrix hK hF hs hd b hH h𝔭 he (by omega : c + 1 ≤ j + c) Y
      ((mk_form_iff 𝔭 _ H Y).1 hX')
    rw [Nat.add_sub_cancel] at hgY
    refine ⟨g, hg, fun x => ⟨⟨g x, aut_mem hg x.2⟩, rfl, ?_⟩⟩
    obtain ⟨c₀, hc⟩ := exists_cmb h𝔭 b j (Submodule.Quotient.mk x)
    rw [hc, end_apply_cmb b j X Y hmap c₀, mk_eq_iff]
    rw [mk_eq_iff] at hc
    have e1 : (inA 𝔭 b (cmb b (Y *ᵥ c₀)) : V) - g (x : V) =
        -(g ((x : V) - (inA 𝔭 b (cmb b c₀) : V)) + (g (cmb b c₀ : V) - (cmb b (Y *ᵥ c₀) : V))) := by
      rw [map_sub, coe_inA, coe_inA]
      abel
    show (inA 𝔭 b (cmb b (Y *ᵥ c₀)) : V) - g (x : V) ∈ _
    rw [e1]
    exact neg_mem (add_mem (aut_mem_smul hg _ hc) (aut_cmb b hgY c₀))

theorem isUnit_det_of_form [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {e k : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hk : e + 1 ≤ k)
    (X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k)) (hX : Xᴴ * Hq H 𝔭 k * X = Hq H 𝔭 k) : IsUnit X.det := by
  obtain ⟨Y, rfl⟩ := exists_map_mk 𝔭 _ X
  have h1 := isUnit_det_mk hK hFF.out hs hd b hH h𝔭 he hk Y ((mk_form_iff 𝔭 _ H Y).1 hX) k
  have h2 := RingHom.map_det (Ideal.Quotient.mk (extP K 𝔭 ^ k)) Y
  rw [RingHom.mapMatrix_apply] at h2
  rwa [h2] at h1

theorem conjTranspose_eq_of_symm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) : Hᴴ = H := by
  refine Matrix.ext fun i j => ?_
  apply jK_inj
  have : jK (Hᴴ i j) = star (jK (H j i)) := rfl
  rw [this, hH, hH]
  exact hs.eq (b j) (b i)

theorem akCount_eq_mul_basis [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c j : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 c) (hcj : c ≤ j) (hj : 1 ≤ j) :
    akCount h (locF 𝔭 (spanO b)) 𝔭 (j + c) =
      redCount h (locF 𝔭 (spanO b)) 𝔭 j * sigmaCount h (locF 𝔭 (spanO b)) 𝔭 c := by
  rw [akCount_basis h b hH h𝔭, redCount_basis hK hs hd b hH h𝔭 he hj, sigmaCount_basis h b hH h𝔭]
  exact card_cell h𝔭 (conjTranspose_eq_of_symm hs b hH) hcj
    (isUnit_det_of_form hK hs hd b hH h𝔭 he (by omega))

theorem pow_notMem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π₀ : 𝓞 F} (hπ : π₀ ∉ 𝔭 ^ 2) (e : ℕ) :
    π₀ ^ e ∉ 𝔭 ^ (e + 1) := by
  induction e with
  | zero =>
    rw [pow_zero, zero_add, pow_one]
    exact fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h)
  | succ e ih =>
    have := mul_notMem h𝔭.isPrime (ne_bot h𝔭) ih hπ
    rwa [← pow_succ] at this

theorem exists_common_den {𝔭 : Ideal (𝓞 F)} [hp : 𝔭.IsPrime] {α : Type*} [Fintype α] (f : α → K)
    (hf : ∀ a, f a ∈ SP K 𝔭) : ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ a, ∃ z : 𝓞 K, jK z = jK (ι t) * f a := by
  classical
  choose t ht z hz using fun a => mem_SP.1 (hf a)
  refine ⟨∏ a, t a, ?_, fun a => ⟨ι (∏ a' ∈ Finset.univ.erase a, t a') * z a, ?_⟩⟩
  · intro hmem
    obtain ⟨a, -, ha⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    exact ht a ha
  · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), map_mul, hz, map_mul ι, map_mul jK]
    ring

theorem exists_E₀ (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : ∀ x, h x x = 0 → x = 0)
    (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j))
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) :
    ∃ (E₀ : Matrix κ κ (𝓞 K)) (d : 𝓞 F), d ∉ 𝔭 ^ (e + 1) ∧ H * E₀ = ι d • (1 : Matrix κ κ (𝓞 K)) := by
  have := h𝔭.isPrime
  obtain ⟨π₀, s₀, hu⟩ := exists_isUnif0 h𝔭
  obtain ⟨E, hE, hHE⟩ := exists_E hF hd b he hu.mem
  obtain ⟨t, ht, hz⟩ := exists_common_den (fun p : κ × κ => E p.1 p.2) (fun p => hE p.1 p.2)
  choose z hz using hz
  refine ⟨Matrix.of fun i j => z (i, j), t * π₀ ^ e, ?_, ?_⟩
  · have := mul_notMem h𝔭.isPrime (ne_bot h𝔭) (i := 0) (by rwa [zero_add, pow_one]) (pow_notMem h𝔭 hu.notMem e)
    rwa [zero_add] at this
  · have h1 : (Matrix.of fun i j => z (i, j)).map jK = jK (ι t) • E := by
      ext i j
      exact hz (i, j)
    have h2 : (H * Matrix.of fun i j => z (i, j)).map jK = (ι (t * π₀ ^ e) • (1 : Matrix κ κ (𝓞 K))).map jK := by
      rw [Matrix.map_mul, h1, ← gramK_eq_map hH, Matrix.mul_smul, hHE, smul_smul]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    exact Matrix.ext fun i j => jK_inj (congrFun (congrFun h2 i) j)

theorem sigmaCount_succ_basis [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {e j : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hj : e ≤ j) :
    sigmaCount h (locF 𝔭 (spanO b)) 𝔭 (j + 1) =
      Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2) * sigmaCount h (locF 𝔭 (spanO b)) 𝔭 j := by
  obtain ⟨E₀, d, hd1, hHE⟩ := exists_E₀ hFF.out hd b hH h𝔭 he
  rw [sigmaCount_basis h b hH h𝔭, sigmaCount_basis h b hH h𝔭]
  exact card_sigma_succ hK h𝔭 (conjTranspose_eq_of_symm hs b hH) hd1 hHE hj

end Formalism.HermitianLattices.Ext.L3.HU
