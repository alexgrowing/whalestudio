import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_dualFamily_of_nsmul_integral {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) {N : ℕ} (hN : 0 < N)
    (hu : ∀ v ∈ L, ∀ b, ∃ u : 𝓞 E, (u : E) = (N : E) * v b) :
    ∃ (m : ℕ) (w : Fin m → L) (lam : Fin m → (L →ₗ[𝓞 E] 𝓞 E)), ∀ v, ∑ i, lam i v • w i = v := by
  classical
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hfg : L.FG := by
    have hle : L ≤ Submodule.span (𝓞 E)
        (Set.range fun b : Fin n => (Pi.single b (N : E)⁻¹ : Fin n → E)) := by
      intro v hv
      choose u hu' using hu v hv
      have : v = ∑ b, u b • (Pi.single b (N : E)⁻¹ : Fin n → E) := by
        funext c
        rw [Finset.sum_apply, Finset.sum_eq_single c]
        · simp only [Pi.smul_apply, Pi.single_eq_same]
          rw [Algebra.smul_def]
          change v c = (u c : E) * _
          rw [hu']; field_simp
        · intro b _ hb
          simp [Pi.single_eq_of_ne hb.symm]
        · simp
      rw [this]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    exact Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) hle
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  have : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) L
  refine ⟨m, fun i => f (Pi.single i 1), fun i => (LinearMap.proj i) ∘ₗ g, fun v => ?_⟩
  have h1 : f (g v) = v := LinearMap.congr_fun hfg v
  conv_rhs => rw [← h1, pi_eq_sum_univ' (g v), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  congr 2

theorem mem_stdLat_iff_integral {E : Type} [Field E] [NumberField E] {n : ℕ} (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∀ b, ∃ u : 𝓞 E, (u : E) = v b := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]

theorem modN_sq_iff_exists_genLat_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ a : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) ↔ ∃ (m : ℕ) (x : Fin m → Dw.La) (v : Fin m → Fin n → 𝓞 E), (∀ i, ∃ w ∈ Λ.La, ∀ b, (v i b : E) = (N : E) * w b) ∧ ∀ b, a b = ∑ i, v i b • x i := by
  classical
  intro E _ _ _ H Dw n Λ N hU hN hle a
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNO : (N : 𝓞 E) ≠ 0 := by exact_mod_cast hN.ne'
  have inj : Function.Injective (fun x : 𝓞 E => (x : E)) := RingOfIntegers.coe_injective
  have he : ∀ b : Fin n, (Pi.single b (N : E) : Fin n → E) ∈ Λ.La := by
    intro b
    apply hle
    have h1 : (Pi.single b (1 : E) : Fin n → E) ∈ stdLat E n := by
      rw [mem_stdLat_iff_integral]
      intro c
      by_cases h : c = b
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_eq_of_ne h]⟩
    have h2 := Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1
    convert h2 using 1
    funext c
    by_cases h : c = b
    · subst h; simp [Algebra.smul_def]
    · simp [Pi.single_eq_of_ne h]
  have hu : ∀ v ∈ Λ.La, ∀ b, ∃ u : 𝓞 E, (u : E) = (N : E) * v b := by
    intro v hv b
    obtain ⟨y, hy⟩ := (hU (Pi.single b (N : E))).1 (he b) v hv
    refine ⟨y, ?_⟩
    change algebraMap (𝓞 E) E y = _
    rw [hy, Finset.sum_eq_single b]
    · simp
    · intro c _ hc
      simp [Pi.single_eq_of_ne hc]
    · simp
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun b => b.elim0⟩
    obtain ⟨m, w, lam, hw⟩ := exists_dualFamily_of_nsmul_integral Λ.La hN hu
    let e : Fin n → Λ.La := fun b => ⟨Pi.single b (N : E), he b⟩
    have hx : ∀ i, ∃ x : Dw.La, ∑ j, lam i (e j) • a j = (N ^ 2) • x := by
      intro i
      refine h (Matrix.of fun _ j => (lam i (e j) : E) / N) ?_ (fun _ j => lam i (e j)) ?_ ⟨0, hn⟩
      · intro v hv
        rw [mem_stdLat_iff_integral]
        intro b
        refine ⟨lam i ⟨v, hv⟩, ?_⟩
        choose u hu' using hu v hv
        have h1 : ((N : 𝓞 E) * N) • (⟨v, hv⟩ : Λ.La) = ∑ j, u j • e j := by
          apply Subtype.ext
          funext c
          simp only [e, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
          rw [Finset.sum_eq_single c]
          · simp only [Pi.single_eq_same, Algebra.smul_def]
            change _ = (u c : E) * _
            rw [hu']; simp; ring
          · intro d _ hd
            simp [Pi.single_eq_of_ne hd.symm]
          · simp
        have h2 := congrArg (fun z => ((lam i z : 𝓞 E) : E)) h1
        simp only [map_smul, map_sum, smul_eq_mul] at h2
        push_cast at h2
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
        apply mul_left_cancel₀ (mul_ne_zero hN' hN')
        rw [Finset.mul_sum]
        refine h2.trans (Finset.sum_congr rfl fun j _ => ?_)
        have := hu' j
        change (u j : E) * (lam i (e j) : E) = _
        rw [this]; field_simp
      · intro _ j
        simp only [Matrix.of_apply]; field_simp
    choose x hx using hx
    choose v hv using fun i => hu (w i) (w i).2
    refine ⟨m, x, v, fun i => ⟨w i, (w i).2, hv i⟩, fun b => ?_⟩
    have := Dw.proj
    have hd : ∀ j, ∑ i, v i b * lam i (e j) = if j = b then (N : 𝓞 E) ^ 2 else 0 := by
      intro j
      apply inj
      have h1 := congrFun (congrArg Subtype.val (hw (e j))) b
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        Algebra.smul_def] at h1
      have h2 : (((∑ i, v i b * lam i (e j) : 𝓞 E)) : E) = (N : E) * (e j : Fin n → E) b := by
        rw [← h1, Finset.mul_sum]
        change algebraMap (𝓞 E) E _ = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        change (v i b : E) * _ = _
        rw [hv]; ring
      change (((∑ i, v i b * lam i (e j) : 𝓞 E)) : E) = _
      rw [h2]
      by_cases hj : j = b
      · subst hj; simp [e, sq]
      · simp [e, hj]
    apply smul_right_injective Dw.La (pow_ne_zero 2 hNO)
    have hx' : ∀ i, ((N : 𝓞 E) ^ 2) • x i = ∑ j, lam i (e j) • a j := by
      intro i
      rw [hx, ← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_pow]
    calc ((N : 𝓞 E) ^ 2) • a b = ∑ j, (∑ i, v i b * lam i (e j)) • a j := by
          simp [hd]
      _ = ∑ i, v i b • ∑ j, lam i (e j) • a j := by
          simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
          exact Finset.sum_comm
      _ = ((N : 𝓞 E) ^ 2) • ∑ i, v i b • x i := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hx', smul_comm]
  · rintro ⟨m, x, v, hv, ha⟩ mu hmu cm hcm i
    choose w hw hvw using hv
    choose y hy using fun k => (mem_stdLat_iff_integral _).1 (hmu (w k) (hw k)) i
    have hd : ∀ k, ∑ j, cm i j * v k j = (N : 𝓞 E) ^ 2 * y k := by
      intro k
      apply inj
      change algebraMap (𝓞 E) E _ = algebraMap (𝓞 E) E _
      rw [map_sum, map_mul]
      change _ = _ * (y k : E)
      rw [hy]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      change (cm i j : E) * (v k j : E) = _
      rw [hcm, hvw]; simp; ring
    refine ⟨∑ k, y k • x k, ?_⟩
    calc ∑ j, cm i j • a j = ∑ k, (∑ j, cm i j * v k j) • x k := by
          simp only [ha, Finset.sum_smul, Finset.smul_sum, mul_smul]
          exact Finset.sum_comm
      _ = _ := by
          rw [← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_pow, Finset.smul_sum]
          simp only [hd, mul_smul]

end GlobalTheory
