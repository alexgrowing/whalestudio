import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelCount
import GroundTheory.AutomorphicForms.ReductionSplitting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNcardEntrywiseBoxLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdEntrywiseLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentMemFinset

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum
open scoped NumberField.AdeleRing

namespace PositivityTheory.Rg.Rs

namespace count

def box (K : Type) [Field K] [NumberField K] (n : ℕ) (𝒦 : Set (FiniteAdeleRing (𝓞 K) K))
    (T : Fin n → Fin n → ℝ) : Set (GL (Fin n) K) :=
  {γ | ∀ i j, algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
    ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T i j}

theorem exists_ncard_box_le (K : Type) [Field K] [NumberField K] (n : ℕ)
    {𝒦 : Set (FiniteAdeleRing (𝓞 K) K)} (h𝒦 : IsCompact 𝒦) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ T i j) →
      (box K n 𝒦 T).Finite ∧ ((box K n 𝒦 T).ncard : ℝ) ≤ ∏ i, ∏ j, C * (1 + T i j) ^ Module.finrank ℚ K :=
  GlobalTheory.CompanionTheory.Counting.exists_ncard_entrywiseBox_le K n 𝒦 h𝒦

theorem prod_bound (n r d : ℕ) (hr : r ≤ n) (C β t : ℝ) (hC : 0 ≤ C) (hβ : 0 ≤ β) (ht : 0 ≤ t) :
    ∏ i : Fin n, ∏ j : Fin n, C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d ≤
      C ^ (n * n) * (1 + β) ^ (d * (n * n)) * Real.exp ((d : ℝ) * ((r : ℝ) * ((n : ℝ) - r)) * t) :=
  GlobalTheory.CompanionTheory.EntrywiseCount.prod_entrywise_le n r d hr C β t hC hβ ht

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

abbrev cen (K : Type) [Field K] [NumberField K] (n : ℕ) : AdelicGLn.AdelicGL K n := An.tor K fun _ : Fin n => (1 : ℝ)

theorem cen_comm (g : AdelicGLn.AdelicGL K n) : cen K n * g = g * cen K n :=
  scalarUnits_mul_comm (n := n) (posIdele (K := K) (Real.exp 1) (Real.exp_pos _)) g

theorem cen_zpow_comm (m : ℤ) (g : AdelicGLn.AdelicGL K n) : cen K n ^ m * g = g * cen K n ^ m :=
  Commute.zpow_left (cen_comm g) m

theorem mem_lat {γ : AdelicGLn.AdelicGL K n} (hγ : γ ∈ An.lat K n) :
    ∃ (γ₀ : GL (Fin n) K) (m : ℤ), γ = AdelicGLn.diagonal K n γ₀ * cen K n ^ m := by
  have : (Subgroup.zpowers (cen K n)).Normal := ⟨fun x hx g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← cen_zpow_comm k g, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hγ
  obtain ⟨γ₀, rfl⟩ := MonoidHom.mem_range.1 hy
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact ⟨γ₀, m, rfl⟩

theorem exists_finset_exp (r : ℕ) (hn : 0 < n) {Q : Set (AdelicGLn.AdelicGL K n)} (hQ : IsCompact Q) :
    ∃ M : Finset ℤ, ∀ (t : ℝ) (X Y : UPos n r → 𝔸[K]), ∀ q ∈ Q, ∀ (γ₀ : GL (Fin n) K) (m : ℤ),
      AdelicGLn.diagonal K n γ₀ * cen K n ^ m =
        unipGL X * An.aR K n r t * q * (An.aR K n r t)⁻¹ * (unipGL Y)⁻¹ → m ∈ M :=
  GlobalTheory.CompanionTheory.Latexp.exponent_mem_finset K n r hn Q hQ

theorem exists_fin_bound (r : ℕ) {D : Set (UPos n r → 𝔸[K])} {Q : Set (AdelicGLn.AdelicGL K n)}
    (hD : IsCompact D) (hQ : IsCompact Q) :
    ∃ 𝒦 : Set (FiniteAdeleRing (𝓞 K) K), IsCompact 𝒦 ∧ ∀ t : ℝ, ∀ X ∈ D, ∀ Y ∈ D, ∀ q ∈ Q,
      ∀ γ : GL (Fin n) K,
      AdelicGLn.diagonal K n γ = unipGL X * An.aR K n r t * q * (An.aR K n r t)⁻¹ * (unipGL Y)⁻¹ →
      ∀ i j, algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 := by
  refine ⟨⋃ i : Fin n, ⋃ j : Fin n,
    (fun p : (UPos n r → 𝔸[K]) × (UPos n r → 𝔸[K]) × AdelicGLn.AdelicGL K n =>
      ((AdelicGLn.prodEquiv K n (unipGL p.1 * p.2.2 * (unipGL p.2.1)⁻¹)).2 :
        Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) i j) '' (D ×ˢ D ×ˢ Q), ?_, ?_⟩
  · refine isCompact_iUnion fun i => isCompact_iUnion fun j => (hD.prod (hD.prod hQ)).image ?_
    exact ((continuous_apply j).comp (continuous_apply i)).comp (Units.continuous_val.comp
      (continuous_snd.comp ((AdelicGLn.prodEquiv K n).continuous.comp
        (((continuous_unipGL.comp continuous_fst).mul (continuous_snd.comp continuous_snd)).mul
          (continuous_unipGL.comp (continuous_fst.comp continuous_snd)).inv))))
  · intro t X hX Y hY q hq γ hγ i j
    have hA : (AdelicGLn.prodEquiv K n (An.aR K n r t)).2 = 1 :=
      prodEquiv_diagUnits_posIdele_snd _ _
    have e1 : algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) =
        ((AdelicGLn.prodEquiv K n (unipGL X * An.aR K n r t * q * (An.aR K n r t)⁻¹ * (unipGL Y)⁻¹)).2 :
          Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) i j := by
      rw [← hγ, AdelicGLn.prodEquiv_apply_snd, AdelicGLn.diagonal_apply]
      rfl
    rw [e1]
    refine Set.mem_iUnion₂.2 ⟨i, j, (X, Y, q), ⟨hX, hY, hq⟩, ?_⟩
    simp only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, hA, mul_one, inv_one]

theorem norm_entry_le (w : InfinitePlace K) (U q V : AdelicGLn.AdelicGL K n) (x : Fin n → ℝ)
    {β₁ β₂ β₃ L : ℝ} (i j : Fin n)
    (h1 : ∀ a b, ‖(infAt w U : Matrix (Fin n) (Fin n) w.Completion) a b‖ ≤ β₁)
    (h2 : ∀ a b, ‖(infAt w q : Matrix (Fin n) (Fin n) w.Completion) a b‖ ≤ β₂)
    (h3 : ∀ a b, ‖(infAt w V : Matrix (Fin n) (Fin n) w.Completion) a b‖ ≤ β₃)
    (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hβ₃ : 0 ≤ β₃) (hL0 : 0 ≤ L)
    (hL : ∀ l m, (infAt w U : Matrix (Fin n) (Fin n) w.Completion) i l ≠ 0 →
      (infAt w V : Matrix (Fin n) (Fin n) w.Completion) m j ≠ 0 → Real.exp (x l) / Real.exp (x m) ≤ L) :
    ‖(infAt w (U * An.tor K x * q * (An.tor K x)⁻¹ * V) : Matrix (Fin n) (Fin n) w.Completion) i j‖ ≤
      (n : ℝ) ^ 2 * (β₁ * (L * β₂) * β₃) := by
  have hρ : ∀ l, 0 < Real.exp (x l) := fun l => Real.exp_pos _
  set d : Fin n → w.Completion := fun l =>
    ((posRealToUnits w ⟨Real.exp (x l) ^ w.mult, pow_pos (hρ l) _⟩ : (w.Completion)ˣ) : w.Completion)
  set d' : Fin n → w.Completion := fun l =>
    (((posRealToUnits w ⟨Real.exp (x l) ^ w.mult, pow_pos (hρ l) _⟩)⁻¹ : (w.Completion)ˣ) : w.Completion)
  have hd : ∀ l, ‖d l‖ = Real.exp (x l) := fun l => norm_posRealToUnits w (hρ l)
  have hd' : ∀ l, ‖d' l‖ = (Real.exp (x l))⁻¹ := fun l => by
    simp only [d', Units.val_inv_eq_inv_val, norm_inv]
    rw [norm_posRealToUnits w (hρ l)]
  set B := (infAt w U : Matrix (Fin n) (Fin n) w.Completion)
  set B' := (infAt w V : Matrix (Fin n) (Fin n) w.Completion)
  set Qm := (infAt w q : Matrix (Fin n) (Fin n) w.Completion)
  have hmat : (infAt w (U * An.tor K x * q * (An.tor K x)⁻¹ * V) : Matrix (Fin n) (Fin n) w.Completion) =
      B * (Matrix.diagonal d * Qm * Matrix.diagonal d') * B' := by
    change (infAt w (U * (diagUnits n fun i => posIdele (K := K) (Real.exp (x i)) (hρ i)) * q *
      (diagUnits n fun i => posIdele (K := K) (Real.exp (x i)) (hρ i))⁻¹ * V) :
        Matrix (Fin n) (Fin n) w.Completion) = _
    rw [infAt_mul, infAt_mul, infAt_mul, infAt_mul, infAt_inv w (diagUnits n _),
      infAt_diagUnits_posIdele, ← map_inv (diagUnits n)]
    simp only [Units.val_mul, coe_diagUnits, Pi.inv_apply, mul_assoc]
    rfl
  have hE : ∀ l m, (Matrix.diagonal d * Qm * Matrix.diagonal d') l m = d l * Qm l m * d' m := by
    intro l m
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hterm : ∀ l m, ‖B i l * (Matrix.diagonal d * Qm * Matrix.diagonal d') l m * B' m j‖ ≤
      β₁ * (L * β₂) * β₃ := by
    intro l m
    by_cases hb : B i l = 0
    · rw [hb, zero_mul, zero_mul, norm_zero]; exact mul_nonneg (mul_nonneg hβ₁ (mul_nonneg hL0 hβ₂)) hβ₃
    by_cases hb' : B' m j = 0
    · rw [hb', mul_zero, norm_zero]; exact mul_nonneg (mul_nonneg hβ₁ (mul_nonneg hL0 hβ₂)) hβ₃
    rw [hE, norm_mul, norm_mul, norm_mul, norm_mul, hd, hd']
    have hr := hL l m hb hb'
    have e : Real.exp (x l) * ‖Qm l m‖ * (Real.exp (x m))⁻¹ = Real.exp (x l) / Real.exp (x m) * ‖Qm l m‖ := by
      ring
    rw [e]
    have h4 : Real.exp (x l) / Real.exp (x m) * ‖Qm l m‖ ≤ L * β₂ :=
      mul_le_mul hr (h2 l m) (norm_nonneg _) hL0
    exact mul_le_mul (mul_le_mul (h1 i l) h4 (by positivity) hβ₁) (h3 m j) (norm_nonneg _)
      (mul_nonneg hβ₁ (mul_nonneg hL0 hβ₂))
  rw [hmat, Matrix.mul_apply]
  have hsum : (∑ m, (B * (Matrix.diagonal d * Qm * Matrix.diagonal d')) i m * B' m j) =
      ∑ m, ∑ l, B i l * (Matrix.diagonal d * Qm * Matrix.diagonal d') l m * B' m j := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
  rw [hsum]
  calc ‖∑ m, ∑ l, B i l * (Matrix.diagonal d * Qm * Matrix.diagonal d') l m * B' m j‖
      ≤ ∑ m : Fin n, ∑ l : Fin n, β₁ * (L * β₂) * β₃ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => hterm l m))
    _ = (n : ℝ) ^ 2 * (β₁ * (L * β₂) * β₃) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem infAt_unip_eq_zero (w : InfinitePlace K) (r : ℕ) (X : UPos n r → 𝔸[K]) (a b : Fin n)
    (h : ¬ (a = b ∨ ((a : ℕ) < r ∧ r ≤ (b : ℕ)))) :
    (infAt w (unipGL X) : Matrix (Fin n) (Fin n) w.Completion) a b = 0 := by
  have h1 : a ≠ b := fun e => h (Or.inl e)
  have h2 : ¬ ((a : ℕ) < r ∧ r ≤ (b : ℕ)) := fun e => h (Or.inr e)
  rw [infAt_apply, coe_unipGL, unipMatrix, Matrix.add_apply, Matrix.one_apply_ne h1, blockEntry_apply,
    dif_neg h2, add_zero]
  rfl

theorem infAt_unip_inv_eq_zero (w : InfinitePlace K) (r : ℕ) (X : UPos n r → 𝔸[K]) (a b : Fin n)
    (h : ¬ (a = b ∨ ((a : ℕ) < r ∧ r ≤ (b : ℕ)))) :
    (infAt w (unipGL X)⁻¹ : Matrix (Fin n) (Fin n) w.Completion) a b = 0 := by
  have h1 : a ≠ b := fun e => h (Or.inl e)
  have h2 : ¬ ((a : ℕ) < r ∧ r ≤ (b : ℕ)) := fun e => h (Or.inr e)
  rw [infAt_apply, coe_unipGL_inv, unipMatrix, Matrix.add_apply, Matrix.one_apply_ne h1, blockEntry_apply,
    dif_neg h2, add_zero]
  rfl

theorem exists_inf_bound (r : ℕ) {D : Set (UPos n r → 𝔸[K])} {Q : Set (AdelicGLn.AdelicGL K n)}
    (hD : IsCompact D) (hQ : IsCompact Q) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ t : ℝ, 0 ≤ t → ∀ X ∈ D, ∀ Y ∈ D, ∀ q ∈ Q, ∀ γ : GL (Fin n) K,
      AdelicGLn.diagonal K n γ = unipGL X * An.aR K n r t * q * (An.aR K n r t)⁻¹ * (unipGL Y)⁻¹ →
      ∀ i j, ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤
        β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1) := by
  obtain ⟨β₁, hβ₁0, hβ₁⟩ := exists_norm_infAt_entry_le (hD.image (continuous_unipGL (K := K) (n := n) (r := r)))
  obtain ⟨β₂, hβ₂0, hβ₂⟩ := exists_norm_infAt_entry_le hQ
  obtain ⟨β₃, hβ₃0, hβ₃⟩ :=
    exists_norm_infAt_entry_le (hD.image ((continuous_unipGL (K := K) (n := n) (r := r)).inv))
  refine ⟨(n : ℝ) ^ 2 * (β₁ * β₂ * β₃), by positivity, ?_⟩
  intro t ht X hX Y hY q hq γ hγ i j w
  have e1 : w ((γ : Matrix (Fin n) (Fin n) K) i j) =
      ‖(infAt w (unipGL X * An.aR K n r t * q * (An.aR K n r t)⁻¹ * (unipGL Y)⁻¹) :
        Matrix (Fin n) (Fin n) w.Completion) i j‖ := by
    rw [infAt_apply, ← hγ, AdelicGLn.diagonal_apply, ← GroundTheory.Global.norm_algebraMap_apply]
    rfl
  rw [e1]
  set L : ℝ := if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1 with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; split_ifs <;> positivity
  have key := norm_entry_le w (unipGL X) q (unipGL Y)⁻¹ (fun l : Fin n => if (l : ℕ) < r then t else 0)
    (L := L) i j (hβ₁ _ ⟨X, hX, rfl⟩ w) (hβ₂ q hq w) (hβ₃ _ ⟨Y, hY, rfl⟩ w) hβ₁0 hβ₂0 hβ₃0 hL0 ?_
  · refine le_trans key (le_of_eq ?_)
    ring
  · intro l m hl hm
    have hl' : l = i ∨ ((i : ℕ) < r ∧ r ≤ (l : ℕ)) := by
      by_contra h
      exact hl (infAt_unip_eq_zero w r X i l (fun h' => h (h'.elim (fun e => Or.inl e.symm) Or.inr)))
    have hm' : m = j ∨ ((m : ℕ) < r ∧ r ≤ (j : ℕ)) := by
      by_contra h
      exact hm (infAt_unip_inv_eq_zero w r Y m j h)
    rw [← Real.exp_sub, hLdef]
    by_cases hij : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · rw [if_pos hij]
      refine Real.exp_le_exp.2 ?_
      split_ifs <;> linarith
    · rw [if_neg hij]
      refine Real.exp_le_one_iff.2 ?_
      rcases hl' with rfl | ⟨h1, h2⟩ <;> rcases hm' with rfl | ⟨h3, h4⟩ <;> split_ifs <;>
        first | linarith | (exfalso; omega)

end count

theorem count_holds : An.Count := by
  intro K _ _ n r hr hrn D Q hD hQ
  classical
  set c := count.cen K n with hc
  obtain ⟨M, hM⟩ := count.exists_finset_exp (K := K) r (by omega) hQ
  set Q' : Set (AdelicGLn.AdelicGL K n) := ⋃ m ∈ M, (fun q => c ^ (-m) * q) '' Q with hQ'_def
  have hQ' : IsCompact Q' := M.isCompact_biUnion fun m _ => hQ.image (continuous_const.mul continuous_id)
  obtain ⟨𝒦, h𝒦, hfinb⟩ := count.exists_fin_bound r hD hQ'
  obtain ⟨β, hβ, hinfb⟩ := count.exists_inf_bound r hD hQ'
  obtain ⟨C, hC, hbox⟩ := count.exists_ncard_box_le K n h𝒦
  set d := Module.finrank ℚ K
  refine ⟨M.card * (C ^ (n * n) * (1 + β) ^ (d * (n * n))), fun t ht => ?_⟩
  set T : Fin n → Fin n → ℝ := fun i j => β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1) with hT
  obtain ⟨hfin, hcard⟩ := hbox T (fun i j => by simp only [T]; split_ifs <;> positivity)
  set B := hfin.toFinset
  set g : ℤ × GL (Fin n) K → AdelicGLn.AdelicGL K n := fun p => AdelicGLn.diagonal K n p.2 * c ^ p.1
  set S := {γ : An.lat K n | ∃ X ∈ D, ∃ Y ∈ D, ∃ q ∈ Q,
      (γ : AdelicGLn.AdelicGL K n) = unipGL X * An.aR K n r t * q * (An.aR K n r t)⁻¹ * (unipGL Y)⁻¹}
  have hsub : Subtype.val '' S ⊆ (((M ×ˢ B).image g : Finset _) : Set (AdelicGLn.AdelicGL K n)) := by
    rintro _ ⟨γ, ⟨X, hX, Y, hY, q, hq, hγ⟩, rfl⟩
    obtain ⟨γ₀, m, hγm⟩ := count.mem_lat γ.2
    have hm : m ∈ M := hM t X Y q hq γ₀ m (hγm ▸ hγ)
    have h0 : AdelicGLn.diagonal K n γ₀ =
        unipGL X * An.aR K n r t * (c ^ (-m) * q) * (An.aR K n r t)⁻¹ * (unipGL Y)⁻¹ := by
      have e1 : AdelicGLn.diagonal K n γ₀ = (γ : AdelicGLn.AdelicGL K n) * c ^ (-m) := by
        rw [hγm, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
      rw [e1, hγ]
      have e2 := count.cen_zpow_comm (-m) (q * (An.aR K n r t)⁻¹ * (unipGL Y)⁻¹)
      simp only [mul_assoc] at e2 ⊢
      rw [e2]
    have hq' : c ^ (-m) * q ∈ Q' := Set.mem_biUnion hm ⟨q, hq, rfl⟩
    have hB : γ₀ ∈ B := by
      rw [Set.Finite.mem_toFinset]
      intro i j
      exact ⟨hfinb t X hX Y hY _ hq' γ₀ h0 i j, fun w => hinfb t ht X hX Y hY _ hq' γ₀ h0 i j w⟩
    rw [Finset.coe_image]
    exact ⟨(m, γ₀), Finset.mem_coe.2 (Finset.mem_product.2 ⟨hm, hB⟩), hγm.symm⟩
  have hB : (B.card : ℝ) ≤ C ^ (n * n) * (1 + β) ^ (d * (n * n)) * Real.exp (2 * An.rho K n r * t) := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    refine hcard.trans ((count.prod_bound n r d hrn.le C β t hC hβ ht).trans (le_of_eq ?_))
    congr 2
    simp only [An.rho, d]
    ring
  have hnat : (((M ×ˢ B).image g).card : ℝ) ≤
      M.card * (C ^ (n * n) * (1 + β) ^ (d * (n * n))) * Real.exp (2 * An.rho K n r * t) := by
    calc (((M ×ˢ B).image g).card : ℝ) ≤ ((M ×ˢ B).card : ℝ) := by exact_mod_cast Finset.card_image_le
      _ = M.card * B.card := by rw [Finset.card_product, Nat.cast_mul]
      _ ≤ M.card * (C ^ (n * n) * (1 + β) ^ (d * (n * n)) * Real.exp (2 * An.rho K n r * t)) := by gcongr
      _ = _ := by ring
  calc S.encard = (Subtype.val '' S).encard := (Subtype.val_injective.encard_image S).symm
    _ ≤ ((((M ×ˢ B).image g : Finset _) : Set (AdelicGLn.AdelicGL K n))).encard := Set.encard_le_encard hsub
    _ = (((M ×ˢ B).image g).card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ _ := by
      have := Nat.le_ceil (M.card * (C ^ (n * n) * (1 + β) ^ (d * (n * n))) * Real.exp (2 * An.rho K n r * t))
      have h2 : ((M ×ˢ B).image g).card ≤ ⌈M.card * (C ^ (n * n) * (1 + β) ^ (d * (n * n))) * Real.exp (2 * An.rho K n r * t)⌉₊ := by
        exact_mod_cast hnat.trans this
      exact_mod_cast h2

end PositivityTheory.Rg.Rs
