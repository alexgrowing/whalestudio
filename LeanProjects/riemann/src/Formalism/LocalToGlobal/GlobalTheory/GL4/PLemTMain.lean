import Formalism.LocalToGlobal.GlobalTheory.GL4.PLemTSpan

noncomputable section

open NumberField Matrix Module
open scoped InnerProductSpace

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem psi_mem_U_all (S : HSpace E) (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) (hL : Submodule.IsLattice E L) (v : S.V) : psi M v ∈ UU M L e := by
  have key : ∀ v ∈ Submodule.span E (L : Set S.V), ∀ c : E, psi M (c • v) ∈ UU M L e := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
        intro c
        have halg : IsAlgebraic ℤ c :=
          (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
        obtain ⟨y, hy0, hyi⟩ := halg.exists_integral_multiple
        set w : 𝓞 E := ⟨y • c, hyi⟩ with hw
        have hwx : w • x ∈ L := L.smul_mem w hx
        have h1 := psi_mem_U S M L e _ hwx
        have hwE : (w : E) = (y : E) * c := by
          rw [hw]
          show y • c = (y : E) * c
          rw [zsmul_eq_mul]
        have h2 : c • x = (((1 / (y : ℚ)) : ℚ) : E) • ((w : E) • x) := by
          rw [smul_smul, hwE]
          congr 1
          have : (y : E) ≠ 0 := by exact_mod_cast hy0
          push_cast
          field_simp
        rw [h2, psi_rat, algebraMap_smul]
        exact Submodule.smul_mem _ _ h1
    | zero =>
        intro c
        rw [smul_zero, map_zero]
        exact zero_mem _
    | add x y _ _ hx hy =>
        intro c
        rw [smul_add, map_add]
        exact add_mem (hx c) (hy c)
    | smul a x _ hx =>
        intro c
        rw [smul_smul]
        exact hx (c * a)
  have := key v (by rw [hL.span_eq_top]; exact Submodule.mem_top) 1
  rwa [one_smul] at this

theorem span_E_of_real (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (M : Model S) (L : Submodule (𝓞 E) S.V) {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) (hL : Submodule.IsLattice E L) (R : ℝ)
    (hspan : Submodule.span ℝ {u : UU M L e | u ∈ abelian₂ S hσ hsig hpos M L e ∧ ‖u‖ ≤ R} = ⊤) :
    Submodule.span E {x | x ∈ L ∧ trR (S.hT x x) ≤ R ^ 2} = ⊤ := by
  set P := Submodule.span E {x | x ∈ L ∧ trR (S.hT x x) ≤ R ^ 2} with hPdef
  by_contra hP
  have hlt : finrank E P < finrank E S.V := Submodule.finrank_lt hP
  set p := Module.finBasis E P with hp
  set Φ : S.V →ₗ[E] (Fin (finrank E P) → E) := LinearMap.pi fun j ↦ S.hT (p j : S.V) with hΦ
  have hker : LinearMap.ker Φ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rw [Module.finrank_fin_fun]; exact hlt)
  obtain ⟨z, hzk, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hzj : ∀ j, S.hT (p j : S.V) z = 0 := fun j ↦ congrFun (LinearMap.mem_ker.1 hzk) j
  have hPz : ∀ x ∈ P, S.hT x z = 0 := by
    intro x hx
    have hx' := congrArg (fun t : P ↦ (t : S.V)) (p.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hx'
    calc S.hT x z = S.hT (∑ j, (p.repr ⟨x, hx⟩ j) • (p j : S.V)) z := by rw [hx']
      _ = 0 := by
        rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        rw [hT_smul_left, hzj, mul_zero]
  have hw : psi M z ∈ UU M L e := psi_mem_U_all S M L e hL z
  set w : UU M L e := ⟨psi M z, hw⟩ with hwdef
  have hsub : {u : UU M L e | u ∈ abelian₂ S hσ hsig hpos M L e ∧ ‖u‖ ≤ R} ⊆
      ((Submodule.span ℝ {w})ᗮ : Submodule ℝ (UU M L e)) := by
    rintro u ⟨hu, hnu⟩
    obtain ⟨l, hl, hul⟩ := exists_of_mem_Lam S hσ hsig hpos M L e u hu
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hlP : l ∈ P := by
      refine Submodule.subset_span ⟨hl, ?_⟩
      rw [← norm_psi_sq M l, ← hul]
      have : ‖(u : EuclideanSpace ℝ (Idx S))‖ = ‖u‖ := rfl
      rw [this]
      exact pow_le_pow_left₀ (norm_nonneg _) hnu 2
    change ⟪(u : EuclideanSpace ℝ (Idx S)), psi M z⟫_ℝ = 0
    rw [hul, inner_psi hσ, hPz l hlP]
    simp [trR]
  have htop := Submodule.span_le.2 hsub
  rw [hspan] at htop
  have hww : w ∈ (Submodule.span ℝ {w})ᗮ := htop Submodule.mem_top
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hww
  have hw0 : w = 0 := inner_self_eq_zero.1 hww
  have : psi M z = 0 := by
    have := congrArg (fun t : UU M L e ↦ (t : EuclideanSpace ℝ (Idx S))) hw0
    simpa [hwdef] using this
  exact hz0 (eq_zero_of_psi S hσ hsig hpos M z this)

theorem span_trR_short (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (hsig : S.SigOK)
    (hpos : S.IsPosDef) (q : ℕ) (hq : q ≠ 0) (L : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E L)
    (hLT : LatT S q L) :
    ∃ r : ℕ, r ≤ 2 * finrank ℚ E * S.rank ∧
      Submodule.span E {x | x ∈ L ∧ trR (S.hT x x) ≤ (3 * ((r : ℝ) / 2 /
        Real.sqrt ((finrank ℚ E : ℝ) * ((q : ℝ) * ((discr E).natAbs : ℝ) ^ 2) ^ (-(1 / (finrank ℚ E : ℝ))))
          + 1)) ^ 2} = ⊤ := by
  classical
  obtain ⟨M⟩ := model_exists S hσ hsig hpos
  have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.fg
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have : Module.IsTorsionFree ℤ L := Module.IsTorsionFree.of_smul_eq_zero fun n x h ↦ by
    have h' := congrArg (fun t : L ↦ (t : S.V)) h
    simp only [Submodule.coe_zero] at h'
    have h'' : (n : E) • (x : S.V) = 0 := by rw [Int.cast_smul_eq_zsmul]; simpa using h'
    rcases smul_eq_zero.1 h'' with h1 | h1
    · left; exact_mod_cast h1
    · right; exact Subtype.ext h1
  have : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  set e := Module.Free.chooseBasis ℤ L with he
  set lam := Real.sqrt ((finrank ℚ E : ℝ) * ((q : ℝ) * ((discr E).natAbs : ℝ) ^ 2) ^ (-(1 / (finrank ℚ E : ℝ))))
    with hlamdef
  have hX : (0 : ℝ) < (q : ℝ) * ((discr E).natAbs : ℝ) ^ 2 := by
    have : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
    positivity
  have hdpos : (0 : ℝ) < finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hlam : 0 < lam := Real.sqrt_pos.2 (by positivity)
  have hd : ∀ y : UU M L e, y ≠ 0 → (∀ x ∈ abelian₂ S hσ hsig hpos M L e, ∃ n : ℤ, ⟪x, y⟫_ℝ = (n : ℝ)) →
      lam ≤ ‖y‖ := by
    intro y hy0 hy
    obtain ⟨z, hz, hz0, hyz⟩ := dual_vector_of_integral_pairing S hσ hsig hpos M L e y hy0 hy
    have h1 := trR_dual_ge S hσ hsig hpos q hq L hLT z hz hz0
    have h2 : ‖y‖ ^ 2 = trR (S.hT z z) := by
      rw [← norm_psi_sq M z, ← hyz]; rfl
    rw [← Real.sqrt_sq (norm_nonneg y), h2]
    exact Real.sqrt_le_sqrt h1
  have hsp := span_short_of_dual (abelian₂ S hσ hsig hpos M L e) lam hlam hd
  refine ⟨finrank ℝ (UU M L e), ?_, span_E_of_real S hσ hsig hpos M L e hL _ hsp⟩
  have h1 := Submodule.finrank_le (UU M L e)
  rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Embeddings.card] at h1
  linarith

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
