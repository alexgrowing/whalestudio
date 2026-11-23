import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximationStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionLatticeSeparatedCompleteStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat

section TowerLimit

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem lim_gen_eq (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) = a • fv F x := by
  funext i
  simp [fv, TensorProduct.smul_tmul']

theorem lim_hat_induction {L : Set (Fin n → E)} (P : (Fin n → RA F E) → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hneg : ∀ x, P x → P (-x))
    (hgen : ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) →
      ∀ x ∈ L, P (a • fv F x)) {z : Fin n → RA F E} (hz : z ∈ hat F L) : P z := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    rw [lim_gen_eq]; exact hgen a ha x hx
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | neg x _ hx => exact hneg x hx

theorem lim_adele_smul_mem {L : Set (Fin n → E)} (a : FiniteAdeleRing (𝓞 F) F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {z : Fin n → RA F E} (hz : z ∈ hat F L) :
    a • z ∈ hat F L := by
  refine lim_hat_induction F (fun z => a • z ∈ hat F L) ?_ ?_ ?_ ?_ hz
  · simp
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx
  · intro b hb x hx
    rw [smul_smul, ← lim_gen_eq]
    exact cap_gen_mem F L _ (fun v => adele_mul_integral F (ha v) (hb v)) x hx

theorem lim_fv_smul (r : E) (x : Fin n → E) :
    fv F (r • x) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] r : RA F E) • fv F x := by
  funext i
  simp [fv]

theorem lim_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (r : 𝓞 E) {z : Fin n → RA F E}
    (hz : z ∈ hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (r : E) : RA F E) • z ∈ hat F (L : Set (Fin n → E)) := by
  refine lim_hat_induction F (fun z => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (r : E) : RA F E) • z ∈
    hat F (L : Set (Fin n → E))) ?_ ?_ ?_ ?_ hz
  · simp
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx
  · intro b hb x hx
    rw [smul_comm, ← lim_fv_smul]
    exact lim_adele_smul_mem F b hb (cap_fv_mem F _ _ (L.smul_mem r hx))

theorem lim_nsmul_cancel {M : Type} [AddCommGroup M] [Module F M] {d : ℕ} (hd : 0 < d) {x y : M}
    (h : d • x = d • y) : x = y := by
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  exact smul_right_injective M (Nat.cast_ne_zero.mpr hd.ne') h

theorem lim_sg_smul (c : E ≃ₐ[F] E) (a : FiniteAdeleRing (𝓞 F) F) (z : RA F E) :
    sg (FiniteAdeleRing (𝓞 F) F) c (a • z) = a • sg (FiniteAdeleRing (𝓞 F) F) c z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => simp [sg, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

noncomputable def hermBil (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) :
    (Fin n → RA F E) →ₗ[FiniteAdeleRing (𝓞 F) F] (Fin n → RA F E) →ₗ[FiniteAdeleRing (𝓞 F) F] RA F E :=
  LinearMap.mk₂ _ (hermA c G)
    (fun x x' y => by simp [hermA, add_mul, Finset.sum_add_distrib])
    (fun a x y => by simp [hermA, Finset.smul_sum])
    (fun x y y' => by simp [hermA, mul_add, Finset.sum_add_distrib])
    (fun a x y => by simp [hermA, Finset.smul_sum, lim_sg_smul])

theorem hermBil_apply (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) :
    hermBil F c G x y = hermA c G x y := rfl

theorem lim_herm_fv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hermBil F c G (fv F x) (fv F y) =
      (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (∑ a, ∑ b, x a * G a b * c (y b)) := by
  simp [hermBil_apply, hermA, fv, sg, TensorProduct.tmul_sum]

theorem lim_herm_mem (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) {Λ : Set (Fin n → E)} {J : Set E}
    (h : ∀ x ∈ Λ, ∀ y ∈ Λ, (∑ a, ∑ b, x a * G a b * c (y b)) ∈ J) {x y : Fin n → RA F E}
    (hx : x ∈ hat F Λ) (hy : y ∈ hat F Λ) : hermBil F c G x y ∈ hat1 F J := by
  refine lim_hat_induction F (fun x => hermBil F c G x y ∈ hat1 F J) ?_ ?_ ?_ ?_ hx
  · simp
  · intro x y hx hy; rw [map_add, LinearMap.add_apply]; exact add_mem hx hy
  · intro x hx; rw [map_neg, LinearMap.neg_apply]; exact neg_mem hx
  intro a ha x hx
  refine lim_hat_induction F (fun y => hermBil F c G (a • fv F x) y ∈ hat1 F J) ?_ ?_ ?_ ?_ hy
  · simp
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro x hx; rw [map_neg]; exact neg_mem hx
  intro b hb y hy
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, lim_herm_fv, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]
  exact tmul_mem_adelicCompletion_of_integral F (fun v => adele_mul_integral F (hb v) (ha v)) (h x hx y hy)

variable [NumberField E]

theorem adelicCompletionFractionalIdeal_divisible_eq_zero (J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E)
    (h : ∀ N : ℕ, 0 < N → ∃ w ∈ hat1 F (J : Set E), z = N • w) : z = 0 := by
  let ι : E →ₗ[𝓞 E] (Fin 1 → E) := LinearMap.pi fun _ => LinearMap.id
  have hfg : ((J : Submodule (𝓞 E) E).map ι).FG :=
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl J).map ι
  have hm : ∀ w ∈ hat1 F (J : Set E), (fun _ => w : Fin 1 → RA F E) ∈
      hat F (((J : Submodule (𝓞 E) E).map ι : Submodule (𝓞 E) (Fin 1 → E)) : Set (Fin 1 → E)) := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact cap_gen_mem F _ a ha (ι x) (Submodule.mem_map_of_mem hx)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  have := (GlobalTheory.T.adelicCompletion_lattice_separated_complete F E 1 _ hfg).1 (fun _ => z) (fun N hN => by
    obtain ⟨w, hw, rfl⟩ := h N hN
    exact ⟨_, hm w hw, rfl⟩)
  exact congrFun this 0

theorem lim_eq_of_congr (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (x y : Fin n → RA F E)
    (h : ∀ N : ℕ, 0 < N → ∃ w ∈ hat F (L : Set (Fin n → E)), x = y + N • w) : x = y := by
  rw [← sub_eq_zero]
  refine (GlobalTheory.T.adelicCompletion_lattice_separated_complete F E n L hL).1 _ fun N hN => ?_
  obtain ⟨w, hw, rfl⟩ := h N hN
  exact ⟨w, hw, by abel⟩

theorem lim_exists_matrix (L : Submodule (𝓞 E) (Fin n → E))
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (φ : L →+ (Fin n → RA F E))
    (hφ : ∀ (r : 𝓞 E) (a : L), φ (r • a) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (r : E) : RA F E) • φ a) :
    ∃ g : Matrix (Fin n) (Fin n) (RA F E), ∀ a : L, g *ᵥ fv F (a : Fin n → E) = φ a := by
  classical
  choose d hd hdL using fun j : Fin n => cap_exists_denom L hsp (Pi.single j (1 : E))
  refine ⟨Matrix.of fun i j => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((d j : E)⁻¹) : RA F E) *
    φ ⟨_, hdL j⟩ i, fun a => ?_⟩
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun j => (d j : E)⁻¹ * (a : Fin n → E) j)
  have hc : ∀ j, IsIntegral ℤ (y.natAbs • ((d j : E)⁻¹ * (a : Fin n → E) j)) := by
    intro j
    have h1 := hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    rcases Int.natAbs_eq y with h | h
    · rw [h, natCast_zsmul] at h1; exact h1
    · rw [h, neg_smul, natCast_zsmul] at h1; simpa using h1.neg
  have hD : 0 < y.natAbs := Int.natAbs_pos.mpr hy0
  let r : Fin n → 𝓞 E := fun j => ⟨_, hc j⟩
  have ha : y.natAbs • a = ∑ j, r j • (⟨_, hdL j⟩ : L) := by
    apply Subtype.ext
    funext i
    have hdi : (d i : E) ≠ 0 := Nat.cast_ne_zero.mpr (hd i).ne'
    simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · change y.natAbs • (a : Fin n → E) i = (y.natAbs • ((d i : E)⁻¹ * (a : Fin n → E) i)) *
        (d i • (Pi.single i (1 : E) : Fin n → E) i)
      simp only [Pi.single_eq_same, nsmul_eq_mul]
      field_simp
    · intro j _ hj
      change (y.natAbs • ((d j : E)⁻¹ * (a : Fin n → E) j)) *
        (d j • (Pi.single j (1 : E) : Fin n → E) i) = 0
      simp [hj.symm]
    · simp
  apply lim_nsmul_cancel F hD
  rw [← map_nsmul, ha, map_sum]
  funext i
  simp only [hφ, Pi.smul_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.smul_sum,
    Matrix.of_apply, fv, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (y.natAbs • ((d j : E)⁻¹ * (a : Fin n → E) j))) * _
  rw [TensorProduct.tmul_smul, smul_mul_assoc, mul_right_comm, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one]

end TowerLimit

theorem exists_adelic_matrix_of_tower : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L Λ : Submodule (𝓞 E) (Fin n → E)) (f : ℕ → (L →ₗ[𝓞 E] Λ)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → Λ.FG → Submodule.span E (Λ : Set (Fin n → E)) = ⊤ → (∀ N m : ℕ, 0 < N → 0 < m → ∀ a, ∃ v, f (N * m) a = f N a + N • v) → (∀ N : ℕ, 0 < N → (∀ a, (∃ v, f N a = N • v) ↔ ∃ v, a = N • v) ∧ ∀ a', ∃ a v, a' = f N a + N • v) → ∃ g : GL (Fin n) (RA F E), (g : Matrix (Fin n) (Fin n) (RA F E)).mulVec '' (hat F (L : Set (Fin n → E))) = (hat F (Λ : Set (Fin n → E))) ∧ (∀ N : ℕ, 0 < N → ∀ a : L, ∃ w ∈ (hat F (Λ : Set (Fin n → E))), (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ fv F (a : Fin n → E) = fv F (f N a : Fin n → E) + N • w) ∧ ∀ (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ Λ, ∀ y ∈ Λ, (∑ a, ∑ b, x a * G a b * c (y b)) ∈ J) → (∀ N : ℕ, 0 < N → ∀ x y : L, ∃ z ∈ J, (∑ a, ∑ b, (f N x : Fin n → E) a * G a b * c ((f N y : Fin n → E) b)) = (∑ a, ∑ b, (x : Fin n → E) a * G a b * c ((y : Fin n → E) b)) + N • z) → ∀ x y, hermA c G ((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ x) ((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ y) = hermA c G x y := by
  intro F E _ _ _ _ _ n L Λ f hL hLsp hΛ hΛsp hcomp hiso
  have hfv : ∀ (M : Submodule (𝓞 E) (Fin n → E)) (x : M), fv F (x : Fin n → E) ∈ hat F (M : Set (Fin n → E)) :=
    fun M x => cap_fv_mem F _ _ x.2

  have hlim : ∀ a : L, ∃ z ∈ hat F (Λ : Set (Fin n → E)), ∀ N : ℕ, 0 < N →
      ∃ w ∈ hat F (Λ : Set (Fin n → E)), z = fv F (f N a : Fin n → E) + N • w := by
    intro a
    refine (GlobalTheory.T.adelicCompletion_lattice_separated_complete F E n Λ hΛ).2 (fun N => fv F (f N a : Fin n → E)) (fun N => hfv Λ _) ?_
    intro N m hN hm
    obtain ⟨v, hv⟩ := hcomp N m hN hm a
    refine ⟨_, hfv Λ v, ?_⟩
    rw [hv, Submodule.coe_add, cap_fv_add, AddSubmonoidClass.coe_nsmul, cap_fv_nsmul]
  choose φ hφm hφ using hlim
  have hφadd : ∀ a b, φ (a + b) = φ a + φ b := by
    intro a b
    refine lim_eq_of_congr F Λ hΛ _ _ fun N hN => ?_
    obtain ⟨w, hw, e⟩ := hφ (a + b) N hN
    obtain ⟨w₁, hw₁, e₁⟩ := hφ a N hN
    obtain ⟨w₂, hw₂, e₂⟩ := hφ b N hN
    refine ⟨w - w₁ - w₂, sub_mem (sub_mem hw hw₁) hw₂, ?_⟩
    rw [e, e₁, e₂, map_add, Submodule.coe_add, cap_fv_add, smul_sub, smul_sub]
    abel
  have hφsmul : ∀ (r : 𝓞 E) (a : L),
      φ (r • a) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (r : E) : RA F E) • φ a := by
    intro r a
    refine lim_eq_of_congr F Λ hΛ _ _ fun N hN => ?_
    obtain ⟨w, hw, e⟩ := hφ (r • a) N hN
    obtain ⟨w₁, hw₁, e₁⟩ := hφ a N hN
    refine ⟨_, sub_mem hw (lim_int_smul_mem F Λ r hw₁), ?_⟩
    have : ((r • f N a : Λ) : Fin n → E) = (r : E) • (f N a : Fin n → E) := rfl
    rw [e, e₁, map_smul, this, lim_fv_smul, smul_sub, smul_add, smul_comm _ N]
    abel
  obtain ⟨g, hg⟩ := lim_exists_matrix F L hLsp (AddMonoidHom.mk' φ hφadd) hφsmul
  simp only [AddMonoidHom.mk'_apply] at hg
  have hgmem : ∀ z ∈ hat F (L : Set (Fin n → E)), g *ᵥ z ∈ hat F (Λ : Set (Fin n → E)) := by
    intro z hz
    refine lim_hat_induction F (fun z => g *ᵥ z ∈ hat F (Λ : Set (Fin n → E))) ?_ ?_ ?_ ?_ hz
    · simp
    · intro x y hx hy; rw [Matrix.mulVec_add]; exact add_mem hx hy
    · intro x hx; rw [Matrix.mulVec_neg]; exact neg_mem hx
    · intro a ha x hx
      rw [Matrix.mulVec_smul, hg ⟨x, hx⟩]
      exact lim_adele_smul_mem F a ha (hφm _)

  have hsurj0 : ∀ b : Λ, ∃ z ∈ hat F (L : Set (Fin n → E)), g *ᵥ z = fv F (b : Fin n → E) := by
    intro b
    have hex : ∀ N : ℕ, ∃ a : L, 0 < N → ∃ v, b = f N a + N • v := by
      intro N
      by_cases hN : 0 < N
      · obtain ⟨a, v, h⟩ := (hiso N hN).2 b
        exact ⟨a, fun _ => ⟨v, h⟩⟩
      · exact ⟨0, fun h => absurd h hN⟩
    choose h hh using hex
    obtain ⟨z, hz, hzN⟩ := (GlobalTheory.T.adelicCompletion_lattice_separated_complete F E n L hL).2 (fun N => fv F (h N : Fin n → E))
      (fun N => hfv L _) (by
        intro N m hN hm
        obtain ⟨v₁, e₁⟩ := hh N hN
        obtain ⟨v₂, e₂⟩ := hh (N * m) (Nat.mul_pos hN hm)
        obtain ⟨v₃, e₃⟩ := hcomp N m hN hm (h (N * m))
        obtain ⟨u, hu⟩ := ((hiso N hN).1 (h (N * m) - h N)).1 ⟨v₁ - m • v₂ - v₃, by
          have e₄ : f N (h (N * m)) = b - (N * m) • v₂ - N • v₃ := by
            rw [e₂, e₃]; abel
          have e₅ : f N (h N) = b - N • v₁ := by rw [e₁]; abel
          rw [map_sub, e₄, e₅, mul_smul, smul_sub, smul_sub]; abel⟩
        refine ⟨_, hfv L u, ?_⟩
        have : h (N * m) = h N + N • u := by rw [← hu]; abel
        rw [this, Submodule.coe_add, cap_fv_add, AddSubmonoidClass.coe_nsmul, cap_fv_nsmul])
    refine ⟨z, hz, lim_eq_of_congr F Λ hΛ _ _ fun N hN => ?_⟩
    obtain ⟨w, hw, e⟩ := hzN N hN
    obtain ⟨v, ev⟩ := hh N hN
    obtain ⟨w', hw', e'⟩ := hφ (h N) N hN
    refine ⟨w' + g *ᵥ w - fv F (v : Fin n → E), sub_mem (add_mem hw' (hgmem w hw)) (hfv Λ v), ?_⟩
    have eb : fv F (b : Fin n → E) = fv F (f N (h N) : Fin n → E) + N • fv F (v : Fin n → E) := by
      conv_lhs => rw [ev]
      rw [Submodule.coe_add, cap_fv_add, AddSubmonoidClass.coe_nsmul, cap_fv_nsmul]
    rw [e, eb, Matrix.mulVec_add, Matrix.mulVec_smul, hg, e', smul_sub, smul_add]
    abel
  have hsurj : ∀ y ∈ hat F (Λ : Set (Fin n → E)), ∃ z ∈ hat F (L : Set (Fin n → E)), g *ᵥ z = y := by
    intro y hy
    refine lim_hat_induction F (fun y => ∃ z ∈ hat F (L : Set (Fin n → E)), g *ᵥ z = y) ?_ ?_ ?_ ?_ hy
    · exact ⟨0, zero_mem _, by simp⟩
    · rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact ⟨x + y, add_mem hx hy, Matrix.mulVec_add _ _ _⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨-x, neg_mem hx, Matrix.mulVec_neg _ _⟩
    · intro a ha x hx
      obtain ⟨z, hz, e⟩ := hsurj0 ⟨x, hx⟩
      exact ⟨a • z, lim_adele_smul_mem F a ha hz, by rw [Matrix.mulVec_smul, e]⟩
  have hunit : IsUnit g := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro y
    obtain ⟨d, hd, hy⟩ := (GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n Λ hΛ hΛsp).2.2.2 y
    obtain ⟨z, -, e⟩ := hsurj _ hy
    refine ⟨(d : F)⁻¹ • z, ?_⟩
    rw [Matrix.mulVec_smul, e, ← Nat.cast_smul_eq_nsmul F, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd.ne'), one_smul]
  obtain ⟨g, rfl⟩ := hunit
  refine ⟨g, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hgmem z hz
    · intro hy
      exact hsurj y hy
  · intro N hN a
    rw [hg]
    exact hφ a N hN
  intro c G J hJ hf
  let T : (Fin n → RA F E) →ₗ[FiniteAdeleRing (𝓞 F) F] (Fin n → RA F E) :=
    { toFun := (g : Matrix (Fin n) (Fin n) (RA F E)).mulVec
      map_add' := Matrix.mulVec_add _
      map_smul' := fun a x => Matrix.mulVec_smul _ a x }
  let B := (hermBil F c G).compl₁₂ T T - hermBil F c G
  have hB0 : ∀ x y : L, B (fv F (x : Fin n → E)) (fv F (y : Fin n → E)) = 0 := by
    intro x y
    refine adelicCompletionFractionalIdeal_divisible_eq_zero F J _ fun N hN => ?_
    obtain ⟨z, hz, e⟩ := hf N hN x y
    obtain ⟨w₁, hw₁, e₁⟩ := hφ x N hN
    obtain ⟨w₂, hw₂, e₂⟩ := hφ y N hN
    refine ⟨(1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] z + hermBil F c G (fv F (f N x : Fin n → E)) w₂ +
      hermBil F c G w₁ (φ y), add_mem (add_mem (one_tmul_mem_adelicCompletionOfElementSet F hz)
        (lim_herm_mem F c G hJ (hfv Λ _) hw₂)) (lim_herm_mem F c G hJ hw₁ (hφm y)), ?_⟩
    have : B (fv F (x : Fin n → E)) (fv F (y : Fin n → E)) = hermBil F c G (φ x) (φ y) -
        hermBil F c G (fv F (x : Fin n → E)) (fv F (y : Fin n → E)) := by
      rw [← hg, ← hg]; rfl
    rw [this, e₁, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply]
    have e₃ : hermBil F c G (fv F (f N x : Fin n → E)) (φ y) =
        hermBil F c G (fv F (x : Fin n → E)) (fv F (y : Fin n → E)) +
          N • (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] z +
          N • hermBil F c G (fv F (f N x : Fin n → E)) w₂ := by
      rw [e₂, map_add, map_nsmul, lim_herm_fv, lim_herm_fv, e, TensorProduct.tmul_add,
        TensorProduct.tmul_smul]
    rw [e₃, smul_add, smul_add]
    abel
  have hB1 : ∀ x ∈ hat F (L : Set (Fin n → E)), ∀ y ∈ hat F (L : Set (Fin n → E)), B x y = 0 := by
    intro x hx y hy
    refine lim_hat_induction F (fun x => B x y = 0) ?_ ?_ ?_ ?_ hx
    · simp only [map_zero, LinearMap.zero_apply]
    · intro x y hx hy; rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    · intro x hx; rw [map_neg, LinearMap.neg_apply, hx, neg_zero]
    intro a ha x hx
    refine lim_hat_induction F (fun y => B (a • fv F x) y = 0) ?_ ?_ ?_ ?_ hy
    · simp only [map_zero]
    · intro x y hx hy; rw [map_add, hx, hy, add_zero]
    · intro x hx; rw [map_neg, hx, neg_zero]
    intro b hb y hy
    rw [map_smul, map_smul, LinearMap.smul_apply, hB0 ⟨x, hx⟩ ⟨y, hy⟩, smul_zero, smul_zero]
  intro x y
  obtain ⟨d, hd, hx⟩ := (GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n L hL hLsp).2.2.2 x
  obtain ⟨e, he, hy⟩ := (GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n L hL hLsp).2.2.2 y
  have h1 := hB1 _ hx _ hy
  rw [map_nsmul, map_nsmul, LinearMap.smul_apply, smul_smul, ← smul_zero (e * d)] at h1
  have h2 := lim_nsmul_cancel F (Nat.mul_pos he hd) h1
  exact sub_eq_zero.mp h2

end GlobalTheory.AdLat
