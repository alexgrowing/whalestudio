import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariantStatement

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Supp

open Lev TensVac

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem row_mul (γ : GL (Fin r) E) (y : Matrix (Fin n) (Fin r) E) (j : Fin n) :
    (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) j = lin γ (y j) := by
  funext i; simp [lin_apply, Matrix.mul_apply, mulVec, dotProduct, mul_comm]

theorem tens_mapL {Λ : Lt E n} {L : Lt E r} {γ : GL (Fin r) E} {y : Matrix (Fin n) (Fin r) E}
    (hy : y ∈ tens Λ (mapL γ L)) :
    ∃ z ∈ tens Λ L, y = z * (γ : Matrix (Fin r) (Fin r) E)ᵀ := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, hv, _, ⟨u, hu, rfl⟩, rfl⟩ := hx
    refine ⟨vecMulVec v u, AddSubgroup.subset_closure ⟨v, hv, u, hu, rfl⟩, ?_⟩
    rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    rfl
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, add_mem ha hb, by rw [Matrix.add_mul]⟩
  | neg x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨-a, neg_mem ha, by rw [Matrix.neg_mul]⟩

theorem epsW_mul {γ : GL (Fin r) E} (h : IsUn X γ) (w : E) (y : Matrix (Fin n) (Fin r) E) :
    epsW X w (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) = epsW X w y := by
  have (k : Fin n) : EF X (lin γ (y k)) (w • lin γ (y k)) = EF X (y k) (w • y k) := by
    have : w • lin γ (y k) = lin γ (w • y k) := by simp [lin_apply, Matrix.mulVec_smul]
    rw [this, EF_lin h, lin_inv]
  simp only [epsW, row_mul, this]

variable {D : Level X}

theorem row_mem {M : ℕ} (hM : (M : 𝓞 E) ∈ D.𝔪) {Λ : Lt E n} (hΛ : Λ ∈ Vset E n M) {L : Lt E r}
    (hL : L ∈ D.lats) {y : Matrix (Fin n) (Fin r) E} (hy : y ∈ tens Λ (D.sh L)) (k : Fin n) :
    y k ∈ loc D.𝔪 (D.𝔪 • X.Λ) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, hv, u, hu, rfl⟩ := hx
    obtain ⟨-, -, s, -, hs, h1, -⟩ := hΛ
    obtain ⟨-, t, ht, h2, -⟩ := hL
    obtain ⟨m, hm, m', hm', e⟩ := Ideal.isCoprime_iff_exists.1 D.cop
    have hs' : IsCoprime (Ideal.span {(s : 𝓞 E)}) D.𝔪 := by
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hs
      refine cop_iff.2 ⟨(a : 𝓞 E), (b : 𝓞 E) * M, Ideal.mul_mem_left _ _ hM, ?_⟩
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab
    have hu' : u ∈ loc D.𝔪 (D.𝔪 • X.Λ) :=
      loc_loc (s := m') (cop_iff.2 ⟨1, m, hm, by linear_combination e⟩)
        ⟨t, ht.of_mul_right_left, smul_map_mem LinearMap.id h2 (hu m' hm')⟩
    have hi : IsIntegral ℤ ((s : E) * v k) := (Base.mem_stdL _).1 (h1 v hv) k
    refine loc_loc hs' ?_
    have : (s : 𝓞 E) • vecMulVec v u k = (⟨_, hi⟩ : 𝓞 E) • u := by
      funext i
      exact (mul_assoc (s : E) (v k) (u i)).symm
    rw [this]
    exact Submodule.smul_mem _ _ hu'
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem red_of_red {γ : GL (Fin r) E} {u : Fin r → Fin r → E} {k l : GL (Fin r) (𝓞 E ⧸ D.𝔪)}
    (h : D.Red u k) (h' : D.Red (fun i => lin γ (u i)) l) :
    D.Red (fun i => lin γ (D.β i)) (l * k⁻¹) := by
  obtain ⟨b, hb⟩ := exists_lift k⁻¹
  have h3 := red_comb h hb
  rw [mul_inv_cancel] at h3
  have h4 := cong_of_red red_one h3
  have h0 (i) : lin γ (u i) ∈ loc D.𝔪 X.Λ := by
    obtain ⟨a, -, h'⟩ := h'
    have := add_mem (loc_mono Submodule.smul_le_right (cong_iff.1 (h' i)))
      (le_loc _ (X.Λ.sum_mem (t := Finset.univ) fun j _ => X.Λ.smul_mem (a j i) (D.β_mem j)))
    rwa [sub_add_cancel] at this
  have h2 : X.Λ ≤ (loc D.𝔪 X.Λ).comap (lin γ) ⊔ D.𝔪 • X.Λ := by
    refine D.β_span.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right)
    rintro _ ⟨i, rfl⟩
    refine mem_of_loc (D.β_mem i) le_sup_right ?_
    have := add_mem (loc_mono (le_sup_right (a := (loc D.𝔪 X.Λ).comap (lin γ)))
      (cong_iff.1 (h4 i)))
      (le_loc _ (Submodule.mem_sup_left (((loc D.𝔪 X.Λ).comap (lin γ)).sum_mem
        (t := Finset.univ) fun j _ => Submodule.smul_mem _ (b j i) (x := u j) (h0 j))))
    rwa [sub_add_cancel] at this
  obtain ⟨t, ht, h2⟩ := nakayama X.Λ_fg h2
  have h1 : mapL γ X.Λ ≤ loc D.𝔪 X.Λ := by
    rintro _ ⟨v, hv, rfl⟩
    refine loc_loc ht ?_
    change t • lin γ v ∈ _
    rw [← map_smul]
    exact h2 v hv
  obtain ⟨s, hs, h1⟩ := exists_mul_of_fg (X.Λ_fg.map _) h1
  refine red_congr (fun i => ?_) (red_comb h' hb)
  simpa only [map_sum, map_smul] using cong_lin hs (fun v hv => h1 _ ⟨v, hv, rfl⟩) (h4 i)

theorem red_of_dat (hn : r ≤ n) {y : Matrix (Fin n) (Fin r) E} (h : ‖D.dat hn y‖ = 1) :
    ∃ k : D.J, D.Red (fun i => y (Fin.castLE hn i)) k := by
  by_contra H
  rw [Level.dat, dif_neg fun H' => H H'.1, norm_zero] at h
  exact zero_ne_one h

variable {w : E} {A A' : AddSubgroup (Matrix (Fin n) (Fin r) E)}
  (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
include idx hs hn

theorem ip_heis_zero (hA : Good X w A) {v : TF n g} (hv : IsVac X bas w A v) {y}
    (hy : y ∉ A) : SW.ip (heisG X bas y v) v = 0 := by
  have h := hA.ip_eq_zero idx hs hn hv hy
  rw [ip_smul_left _ (laws idx hs hn y hv.1).1 hv.1] at h
  exact (mul_eq_zero.1 h).resolve_left (Complex.exp_ne_zero _)

theorem ip_heis_vac (hA : Good X w A) (hA' : Good X w A') {v v' : TF n g}
    (hv : IsVac X bas w A v) (hv' : IsVac X bas w A' v') {t} (ht : ∀ a ∈ A, a + t ∉ A') :
    SW.ip (heisG X bas t v') v = 0 := by
  have hφ := (laws idx hs hn t hv'.1).1
  have hfin := hA.finite idx hs hn hφ
  have hsb : ∀ ψ ∈ hfin.toFinset, IsSB ψ := by
    intro ψ hψ
    obtain ⟨y, -, rfl⟩ := hfin.mem_toFinset.1 hψ
    exact rho_sb idx hs hn y hφ
  obtain ⟨h1, h2⟩ := sum_sb_ip _ hsb hv'.1
  have h3 := congrArg (SW.ip · v') (hA.proj idx hs hn hφ hv).2
  rw [projA, finsum_mem_eq_finite_toFinset_sum _ hfin, ip_smul_left _ h1 hv'.1, h2,
    Finset.sum_eq_zero, mul_zero, ip_smul_left _ hv.1 hv'.1] at h3
  · refine (mul_eq_zero.1 h3.symm).resolve_right fun h => ?_
    have := hA.overlap idx hs hn hA' hv hv'
    simp [h] at this
  · intro ψ hψ
    obtain ⟨a, ha, rfl⟩ := hfin.mem_toFinset.1 hψ
    beta_reduce
    rw [(laws idx hs hn a hv'.1).2.2.1, smul_smul,
      ip_smul_left _ (laws idx hs hn _ hv'.1).1 hv'.1, ip_heis_zero idx hs hn hA' hv' (ht a ha),
      mul_zero]

theorem ip_heis_heis (hA : Good X w A) (hA' : Good X w A') {v v' : TF n g}
    (hv : IsVac X bas w A v) (hv' : IsVac X bas w A' v') {y z}
    (ht : ∀ a ∈ A, a + (-y + z) ∉ A') : SW.ip (heisG X bas z v') (heisG X bas y v) = 0 := by
  rw [← (laws idx hs hn (-y) (laws idx hs hn z hv'.1).1).2.2.2 _ (laws idx hs hn y hv.1).1,
    (laws idx hs hn (-y) hv'.1).2.2.1, (laws idx hs hn (-y) hv.1).2.2.1, neg_add_cancel,
    (laws idx hs hn 0 hv.1).2.1, ip_smul_left _ (laws idx hs hn _ hv'.1).1 (sb_smul _ hv.1),
    ip_smul_right _ (laws idx hs hn _ hv'.1).1 hv.1, ip_heis_vac idx hs hn hA hA' hv hv' ht,
    mul_zero, mul_zero]

theorem isVac_wG {γ : GL (Fin r) E} (hγ : IsUn X γ) {Λ : Lt E n} {L : Lt E r} {v : TF n g}
    (hv : IsVac X bas w (tens Λ L) v) :
    IsVac X bas w (tens Λ (mapL γ L)) (wG X bas idx γ v) := by
  obtain ⟨h1, -, h2, -, -, -, h3⟩ := wG_laws E r X g bas idx n hs hn γ hγ v hv.1
  refine ⟨h1, (h2 v hv.1).1.trans hv.2.1, fun y hy => ?_⟩
  obtain ⟨z, hz, rfl⟩ := tens_mapL hy
  rw [epsW_mul hγ, ← h3, ← (wG_laws E r X g bas idx n hs hn γ hγ _
    (laws idx hs hn z hv.1).1).2.2.2.1, hv.2.2 z hz]

end GlobalTheory.SW.Supp

namespace GlobalTheory.SW

open Lev TensVac Supp

theorem phi_overlap_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ γ, IsUn X γ → γ ∉ D.grp → ∀ L ∈ D.lats, ∀ L' ∈ D.lats, ∀ Λ ∈ Vset E n M, ip (D.phi bas hn v₀ L Λ) (wG X bas idx γ (D.phi bas hn v₀ L' Λ)) = 0 := by
  intro E _ _ _ r X g bas idx n hs he D hn M hM0 hM v₀ hv₀ γ hγ hγ' L hL L' hL' Λ hΛ
  obtain ⟨hsb, hv, H, -⟩ := GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs he D hn M hM0 hM v₀ hv₀ L hL Λ hΛ
  obtain ⟨hsb', hv', -⟩ := GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs he D hn M hM0 hM v₀ hv₀ L' hL' Λ hΛ
  obtain ⟨s, -, hs1, e, e'⟩ := H L' hL'
  generalize unitv (projA X bas D.w (tens Λ (D.sh L)) (v₀ L)) = v at hv e
  generalize unitv (projA X bas D.w (tens Λ (D.sh L')) (v₀ L')) = v' at hv' e'
  have good (L) (hL : SelfD X L) : Good X D.w (tens Λ L) := by
    obtain ⟨h1, h2, h3, -⟩ :=
      GlobalTheory.T.tensorLattice_selfDual_semicharacter_index E r X g bas idx n hs he D.w D.w_int D.w_tr L hL M Λ hΛ
    exact ⟨h1, h2, h3⟩
  have hA := good _ (selfD_idq D.ne_bot D.proper D.cop hL.1)
  have hA' := good _ (selfD_mapL hγ (selfD_idq D.ne_bot D.proper D.cop hL'.1))
  have hw := isVac_wG idx hs he hγ hv'
  have W := wG_laws E r X g bas idx n hs he γ hγ
  have key : ∀ y ∈ s, ∀ y' ∈ s, SW.ip (heisG X bas y v)
      (heisG X bas (y' * (γ : Matrix (Fin r) (Fin r) E)ᵀ) (wG X bas idx γ v')) = 0 := by
    intro y hy y' hy'
    rw [ip_conj (laws idx hs he _ hw.1).1 (laws idx hs he _ hv.1).1,
      ip_heis_heis idx hs he hA hA' hv hw, map_zero]
    intro a ha h
    obtain ⟨a', ha', h⟩ := tens_mapL h
    obtain ⟨k, hk⟩ := red_of_dat hn (hs1 y hy).2.1
    obtain ⟨k', hk'⟩ := red_of_dat hn (hs1 y' hy').2.1
    have h1 : (y' - a') * (γ : Matrix (Fin r) (Fin r) E)ᵀ = y - a := by
      rw [Matrix.sub_mul, ← h]; abel
    have hsub (p q : Matrix (Fin n) (Fin r) E) (j) : (p - q) j - p j = -q j :=
      sub_sub_cancel_left (p j) (q j)
    have h2 : D.Red (fun i => (y' - a') (Fin.castLE hn i)) k' := red_congr (fun i => by
      rw [cong_iff, hsub]
      exact neg_mem (row_mem hM hΛ hL' ha' _)) hk'
    have h3 : D.Red (fun i => lin γ ((y' - a') (Fin.castLE hn i))) k := red_congr (fun i => by
      rw [cong_iff, ← row_mul, h1, hsub]
      exact neg_mem (row_mem hM hΛ hL ha _)) hk
    exact hγ' ((mem_grp γ).2 ⟨hγ, _, mul_mem k.2 (inv_mem k'.2), red_of_red h2 h3⟩)
  have add {φ ψ : TF n g} (h : IsSB φ) (h' : IsSB ψ) : IsSB (φ + ψ) :=
    (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ _ _ _ _ h h').1
  have zero {ψ : TF n g} (h : IsSB ψ) : SW.ip 0 ψ = 0 := by simpa using ip_smul_left 0 h h
  have key2 : ∀ y ∈ s, SW.ip (wG X bas idx γ (D.phi bas hn v₀ L' Λ)) (heisG X bas y v) = 0 := by
    intro y hy
    have hy1 := (laws idx hs he y hv.1).1
    rw [e']
    refine (Finset.sum_induction _ (fun φ => IsSB φ ∧ SW.ip (wG X bas idx γ φ) (heisG X bas y v) = 0)
      (fun φ ψ hφ hψ => ⟨add hφ.1 hψ.1, ?_⟩) ⟨isSB_zero, ?_⟩ fun y' hy' => ?_).2
    · rw [((W φ hφ.1).2.2.1 ψ hψ.1).2.1, ip_add_left (W φ hφ.1).1 (W ψ hψ.1).1 hy1, hφ.2, hψ.2,
        add_zero]
    · have := (W 0 isSB_zero).2.2.2.1 0
      rw [zero_smul, zero_smul] at this
      rw [this, zero hy1]
    · have h1 := (laws idx hs he y' hv'.1).1
      refine ⟨sb_smul _ h1, ?_⟩
      rw [(W _ h1).2.2.2.1, ip_smul_left _ (W _ h1).1 hy1, (W _ hv'.1).2.2.2.2.2.2,
        ip_conj hy1 (laws idx hs he _ hw.1).1, key y hy y' hy', map_zero, mul_zero]
  have hW := (W _ hsb').1
  rw [e]
  refine (Finset.sum_induction _ (fun φ => IsSB φ ∧
      SW.ip φ (wG X bas idx γ (D.phi bas hn v₀ L' Λ)) = 0)
    (fun φ ψ hφ hψ => ⟨add hφ.1 hψ.1, ?_⟩) ⟨isSB_zero, zero hW⟩ fun y hy => ?_).2
  · rw [ip_add_left hφ.1 hψ.1 hW, hφ.2, hψ.2, add_zero]
  · have h1 := (laws idx hs he y hv.1).1
    refine ⟨sb_smul _ h1, ?_⟩
    rw [ip_smul_left _ h1 hW, ip_conj hW h1, key2 y hy, map_zero, mul_zero]

end GlobalTheory.SW
