import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryEqReflOfCongrModGeThree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportingFormGapOffSmoothConeStatement

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.Poinc.DomTuple

section Squares

variable {X : Type} [AddCommGroup X]

def IsSumSq (F : LinearMap.BilinForm ℤ X → ℤ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (x : ι → X), ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → F β = ∑ i, β (x i) (x i)

theorem IsSumSq.congr {F G : LinearMap.BilinForm ℤ X → ℤ} (h : IsSumSq F)
    (e : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → G β = F β) : IsSumSq G := by
  obtain ⟨ι, _, x, hx⟩ := h
  exact ⟨ι, _, x, fun β hβ => (e β hβ).trans (hx β hβ)⟩

theorem IsSumSq.add {F G : LinearMap.BilinForm ℤ X → ℤ} (h : IsSumSq F) (h' : IsSumSq G) :
    IsSumSq fun β => F β + G β := by
  obtain ⟨ι, _, x, hx⟩ := h
  obtain ⟨κ, _, y, hy⟩ := h'
  exact ⟨ι ⊕ κ, inferInstance, Sum.elim x y, fun β hβ => by
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hx β hβ, hy β hβ]⟩

theorem IsSumSq.nsmul {F : LinearMap.BilinForm ℤ X → ℤ} (h : IsSumSq F) (n : ℕ) : IsSumSq fun β => n * F β := by
  obtain ⟨ι, _, x, hx⟩ := h
  exact ⟨Fin n × ι, inferInstance, fun p => x p.2, fun β hβ => by
    simp [Fintype.sum_prod_type, hx β hβ]⟩

theorem isSumSq_one (v : X) : IsSumSq fun β => β v v :=
  ⟨Unit, inferInstance, fun _ => v, fun β _ => by simp⟩

variable {m : ℕ} (a : Fin m → X)

def Absorbed (F : LinearMap.BilinForm ℤ X → ℤ) : Prop :=
  ∃ C : ℕ, IsSumSq fun β => C * ∑ i, β (a i) (a i) + F β

variable {a}

theorem Absorbed.congr {F G : LinearMap.BilinForm ℤ X → ℤ} (h : Absorbed a F)
    (e : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) → G β = F β) : Absorbed a G := by
  obtain ⟨C, h⟩ := h
  exact ⟨C, h.congr fun β hβ => by rw [e β hβ]⟩

theorem Absorbed.add {F G : LinearMap.BilinForm ℤ X → ℤ} (h : Absorbed a F) (h' : Absorbed a G) :
    Absorbed a fun β => F β + G β := by
  obtain ⟨C, h⟩ := h
  obtain ⟨C', h'⟩ := h'
  exact ⟨C + C', (h.add h').congr fun β _ => by push_cast; ring⟩

theorem Absorbed.nsmul {F : LinearMap.BilinForm ℤ X → ℤ} (h : Absorbed a F) (n : ℕ) : Absorbed a fun β => n * F β := by
  obtain ⟨C, h⟩ := h
  exact ⟨n * C, (h.nsmul n).congr fun β _ => by push_cast; ring⟩

theorem absorbed_sq (v : X) : Absorbed a fun β => β v v :=
  ⟨0, (isSumSq_one v).congr fun β _ => by simp⟩

theorem absorbed_zero : Absorbed a fun _ => 0 :=
  (absorbed_sq 0).congr fun β _ => by simp

theorem absorbed_sum {ι : Type} (S : Finset ι) (F : ι → LinearMap.BilinForm ℤ X → ℤ) (h : ∀ i, Absorbed a (F i)) :
    Absorbed a fun β => ∑ i ∈ S, F i β := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using absorbed_zero
  | insert i S hi ih => exact ((h i).add ih).congr fun β _ => Finset.sum_insert hi

theorem absorbed_neg_sq (ha : Submodule.span ℤ (Set.range a) = ⊤) (v : X) : Absorbed a fun β => - β v v := by
  have hv : v ∈ Submodule.span ℤ (Set.range a) := ha ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨1, {i // i ≠ j}, inferInstance, fun i => a i.1, fun β _ => ?_⟩
    have := Fintype.sum_eq_add_sum_subtype_ne (fun i => β (a i) (a i)) j
    simp only [Nat.cast_one, one_mul]
    rw [this]; ring
  | zero => exact absorbed_zero.congr fun β _ => by simp
  | add x y _ _ hx hy =>
    refine (((hx.nsmul 2).add (hy.nsmul 2)).add (absorbed_sq (x - y))).congr fun β _ => ?_
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    push_cast; ring
  | smul n x _ hx =>
    refine (hx.nsmul (n.natAbs ^ 2)).congr fun β _ => ?_
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    push_cast; rw [sq_abs]; ring

theorem absorbed_two_mul_apply (ha : Submodule.span ℤ (Set.range a) = ⊤) (u v : X) : Absorbed a fun β => 2 * β u v := by
  refine (((absorbed_sq (u + v)).add (absorbed_neg_sq ha u)).add (absorbed_neg_sq ha v)).congr fun β hβ => ?_
  simp only [map_add, LinearMap.add_apply, hβ v u]
  ring

theorem absorbed_two_mul [Module.Free ℤ X] [Module.Finite ℤ X] (ha : Submodule.span ℤ (Set.range a) = ⊤)
    (F : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) : Absorbed a fun β => 2 * F β := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let E : _ → _ → LinearMap.BilinForm ℤ X := fun i j => (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)
  have hE : ∀ β : LinearMap.BilinForm ℤ X, β = ∑ i, ∑ j, β (b i) (b j) • E i j := fun β => by
    refine LinearMap.BilinForm.ext_basis b fun k l => ?_
    simp [E, LinearMap.sum_apply, Finsupp.single_apply]
  refine (absorbed_sum Finset.univ _ fun i => absorbed_sum Finset.univ _ fun j =>
    absorbed_two_mul_apply ha (F (E i j) • b i) (b j)).congr fun β _ => ?_
  conv_lhs => rw [hE β]
  simp only [map_sum, map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Squares

theorem exists_tuple {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : ℕ} {a₀ : Fin m → X}
    (ha : Submodule.span ℤ (Set.range a₀) = ⊤) {s : ℕ} (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ) {w : ℕ} (hw : 1 ≤ w)
    (hW : W 0 0 = w) (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (μ : Fin (s + 1) → X) (D₀ : ℕ) :
    ∃ (D l : ℕ) (a : Fin l × Fin (s + 1) → X) (i₀ : Fin l), D₀ < D ∧ (∀ u, a (i₀, u) = μ u) ∧
      Submodule.span ℤ (Set.range a) = ⊤ ∧ ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) →
        lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + (2 * w : ℕ) * lam β := by
  classical
  have h1 : Absorbed a₀ fun β => 2 * lam β + ∑ u, ∑ v, 2 * β (-W u v • μ u) (μ v) :=
    (absorbed_two_mul ha lam).add (absorbed_sum _ _ fun u => absorbed_sum _ _ fun v => absorbed_two_mul_apply ha _ _)
  obtain ⟨C, ι, _, x, hx⟩ := h1
  let κ := Fin (2 * w) ⊕ (Fin (D₀ + 1) × Fin m) ⊕ ι
  let t : κ → Fin (s + 1) → X :=
    Sum.elim (fun _ => μ) (Sum.elim (fun p => Pi.single 0 (a₀ p.2)) fun i => Pi.single 0 (x i))
  let e := (Fintype.equivFin κ).symm
  refine ⟨w * (C + D₀ + 1), _, fun p => t (e p.1) p.2, e.symm (Sum.inl ⟨0, by omega⟩), by nlinarith, fun u => by simp [t],
    ?_, fun β hβ => ?_⟩
  · rw [eq_top_iff, ← ha]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨(e.symm (Sum.inr (Sum.inl (0, i))), 0), by simp [t]⟩
  · have hs : ∀ v : X, qW W β (Pi.single 0 v) = w * β v v := fun v => by
      simp [qW, Fin.sum_univ_succ, hW]
    have h2 : lin W (fun p : _ × _ => t (e p.1) p.2) β = ∑ k, qW W β (t k) := e.sum_comp fun k => qW W β (t k)
    have h3 := hx β hβ
    have h4 : ∑ u, ∑ v, 2 * β (-W u v • μ u) (μ v) = -2 * qW W β μ := by
      simp only [qW, Finset.mul_sum, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp only [h4] at h3
    rw [h2]
    simp only [κ, t, Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr, hs, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← h3]
    push_cast; ring

theorem exists_dominant (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (hφ : IsPolFanOn bar φ X) (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X)
    (a₀ : Fin m → X) (hγ : IsCone bar φ γ) (hne : NoEquivRays O γ) (hpos : ∀ x, x ≠ 0 → ∃ j, 0 < γ j x x)
    (hs : Supports bar φ d γ a₀) (s : ℕ) (W : Matrix (Fin (s + 1)) (Fin (s + 1)) ℤ) (hW : PosW W) (N₁ : ℕ) (hN : 3 ≤ N₁)
    (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (hlam : ∀ j, 0 ≤ lam (γ j)) (μ : Fin (s + 1) → X) :
    ∃ (D D' l : ℕ) (a : Fin l × Fin (s + 1) → X) (i₀ : Fin l), 1 ≤ D ∧ 1 ≤ D' ∧ (∀ u, a (i₀, u) = μ u) ∧
      Dominant bar φ (D * d) N₁ W γ a ∧
      ∀ β ∈ balForms bar X, lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + D' * lam β := by
  have hW0 : 0 < W 0 0 := by
    have h : (0 : ℝ) < ((W + W.transpose).map (Int.cast : ℤ → ℝ)) 0 0 := Matrix.PosDef.diag_pos hW
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_pos] at h
    omega
  obtain ⟨w, hw⟩ : ∃ w : ℕ, W 0 0 = w := ⟨_, (Int.toNat_of_nonneg hW0.le).symm⟩
  have hw1 : 1 ≤ w := by omega
  let lam' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ((2 * w : ℕ) : ℤ) • lam
  have hlam' : ∀ j, 0 ≤ lam' (γ j) := fun j => mul_nonneg (Int.natCast_nonneg _) (hlam j)
  obtain ⟨D₀, hD₀⟩ := GlobalTheory.T.exists_supportingForm_gap_off_smoothCone O bar φ d X hφ r m γ a₀ hγ hs lam' hlam' (∑ j, lam' (γ j) + 1)
  obtain ⟨D, l, a, i₀, hD, hμ, hsp, hlin⟩ := exists_tuple hs.span W hw1 hw lam μ D₀
  obtain ⟨hle, hgap⟩ := hD₀ D hD.le
  have hlin' : ∀ β ∈ balForms bar X, lin W a β = D * ∑ i, β (a₀ i) (a₀ i) + lam' β := fun β hβ => hlin β hβ.1
  have key : ∀ (e : X ≃ₗ[O] X) j, pull e.toLinearMap (γ j) = γ j ∨
      lin W a (γ j) < lin W (fun i => e (a i)) (γ j) := fun e j => by
    by_cases h : ∃ j', pull e.toLinearMap (γ j) = γ j'
    · obtain ⟨j', h⟩ := h
      exact Or.inl (hne e j j' h ▸ h)
    right
    have hc : IsCone bar φ ![pull e.toLinearMap (γ j)] := by
      have := (hφ.face _ 1 γ ⟨fun _ => j, fun _ _ _ => Subsingleton.elim _ _⟩ hγ).pull_equiv e
      have h0 : ![pull e.toLinearMap (γ j)] = fun _ : Fin 1 => pull e.toLinearMap (γ j) := funext fun i => by simp
      rw [h0]
      exact this
    have h1 := hgap _ hc fun j' hj => h ⟨j', hj⟩
    rw [← hlin' _ (pull_mem _ (hγ.mem j)), evalZ_pull φ (r := e.toLinearMap) e.surjective, mul_assoc, hs.eq j] at h1
    have h2 : D * ∑ i, γ j (a₀ i) (a₀ i) + (∑ j, lam' (γ j) + 1) ≤ lin W a (pull e.toLinearMap (γ j)) := by
      exact_mod_cast h1
    have h3 : lam' (γ j) ≤ ∑ j, lam' (γ j) := Finset.single_le_sum (fun j _ => hlam' j) (Finset.mem_univ j)
    change _ < lin W a (pull e.toLinearMap (γ j))
    rw [hlin' _ (hγ.mem j)]
    omega
  refine ⟨D, 2 * w, l, a, i₀, by omega, by omega, hμ, ⟨hsp, fun β hβ hp => ?_, fun e _ j => ?_, fun e he hx => ?_⟩,
    fun β hβ => hlin β hβ.1⟩
  · rw [hlin' β hβ, Nat.cast_mul]
    exact hle β hβ hp
  · rcases key e j with h | h
    · change _ ≤ lin W a (pull e.toLinearMap (γ j))
      rw [h]
    · exact h.le
  · by_contra hn
    have hfix : ∀ j, pull e.toLinearMap (γ j) = γ j := fun j => (key e j).resolve_right fun h => hn ⟨j, h⟩
    have := GlobalTheory.Poinc.eq_refl_of_isometry_congMod X (∑ j, γ j) (fun x hx => by
      obtain ⟨j, hj⟩ := hpos x hx
      simp only [LinearMap.sum_apply]
      exact Finset.sum_pos' (fun i _ => hγ.nonneg i x) ⟨j, Finset.mem_univ j, hj⟩) e.toAddEquiv.toIntLinearEquiv
      (fun x y => by
        simp only [LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun j _ => LinearMap.congr_fun₂ (hfix j) x y) N₁ hN he
    obtain ⟨x, hx⟩ := hx
    exact hx (LinearEquiv.congr_fun this x)

end GlobalTheory.Poinc.DomTuple
