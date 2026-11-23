import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsSumMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivProdIrrZero

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocGL.ProjLine Matrix

namespace GlobalTheory.Published.LanglandsSumTests

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {χ : kˣ →* ℂˣ}

theorem jhMult_parInd {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    jhMult (detRep (Fin 2) η) (parInd pts (ofChar (detLevi pts η))) = 1 ∧
      ¬ (parInd pts (ofChar (detLevi pts η))).IsIrreducible := by
  classical
  obtain ⟨V, _, _, π, f, ⟨φ⟩, hf, h0, h, h1⟩ := exists_line hη
  have hi : (detRep (Fin 2) η).IsIrreducible := isIrreducible_ofChar _
  refine ⟨?_, fun H => ?_⟩
  · rw [← jhMult_congr_right _ φ, JHMult.jhMult_exact f (quotMk f.range) hi hf
      f.range.toSubmodule.mkQ_surjective (fun u => (Submodule.Quotient.mk_eq_zero _).2 ⟨u, rfl⟩)
      (fun v hv => (Submodule.Quotient.mk_eq_zero _).1 hv), jhMult_self hi]
    have : jhMult (detRep (Fin 2) η) (quot f.range) = 0 := by
      by_contra hne
      obtain ⟨e⟩ := (JHMult.jhMult_ne_zero_iff.1 hne).nonempty_equiv hi (isCosocle_quot h0 h).1
      exact h1.false e.toLinearEquiv
    rw [this, add_zero]
  · have H' : π.IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv φ.symm H
    rcases eq_bot_or_eq_top f.range with e | e
    · exact (isAtom_range hi f hf).1 e
    · exact h0 e

theorem nonempty_equiv_prod (hχ : IsSmoothChar χ) :
    Nonempty ((parInd pts (ofChar (detLevi pts (χ * absPow k (1 / 2))))).Equiv
      (prod₂ (detRep (Fin 1) χ) (detRep (Fin 1) (χ * absPow k 1)))) := by
  have hν := hχ.mul (isSmoothChar_absPow (k := k) 1)
  obtain ⟨a⟩ := nonempty_prod₂_equiv_prodIrr _ (IrrRep.det (Fin 1) χ hχ).smooth (IrrRep.det (Fin 1) χ hχ).irr
    _ (IrrRep.det (Fin 1) _ hν).smooth (IrrRep.det (Fin 1) _ hν).irr rfl
  obtain ⟨hd, ⟨ψ⟩⟩ := exists_equiv_prodIrr (θ := ![χ, χ * absPow k 1])
    (Fin.forall_fin_two.2 ⟨hχ, hν⟩)
    (x := ![IrrGL.of _ (IrrRep.det (Fin 1) χ hχ).smooth (IrrRep.det (Fin 1) χ hχ).irr,
      IrrGL.of _ (IrrRep.det (Fin 1) _ hν).smooth (IrrRep.det (Fin 1) _ hν).irr])
    (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
    (Θ := detLevi pts (χ * absPow k (1 / 2))) fun g => by
      rw [detLevi_pts, Fin.prod_univ_two, mul_assoc χ, mul_assoc χ, ← absPow_add, ← absPow_add]
      norm_num
  exact ⟨Representation.Equiv.trans ψ (Representation.Equiv.symm a)⟩

theorem isL_char {y : IrrGL k} (hy : y.IsCusp) (hχ : IsSmoothChar χ) (e : y = IrrGL.ofChar χ hχ) :
    IsL {Segment.single y hy} (detRep (Fin 1) χ) := by
  subst e
  exact (single_spec hy).2.2.2.of_equiv (equivRep (IrrRep.det (Fin 1) χ hχ)).symm

theorem eq_of_isLSeg_single {ρ x : IrrGL k} (hρ : ρ.IsCusp) (h : IsLSeg (.single ρ hρ) x.rep) : x = ρ := by
  obtain ⟨n, c⟩ := x
  obtain ⟨d, c'⟩ := ρ
  obtain rfl : d = n := (one_mul d).symm.trans h.deg_eq
  exact congrArg _ (irrCl_eq_iff.2 ((single_spec hρ).2.1.unique h))

theorem factors_eq (hχ : IsSmoothChar χ) {h : ℕ} {x : Fin h → IrrGL k}
    (H : LFactors ({Segment.single _ (IrrGL.isCusp_ofChar χ hχ)} +
      {Segment.single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)}) x) :
    h = 2 ∧ HEq x ![(IrrGL.ofChar χ hχ).nu 1, IrrGL.ofChar χ hχ] := by
  obtain ⟨Δ, ⟨hm, ho⟩, hΔ⟩ := H
  obtain rfl : h = 2 := by simpa using congrArg Multiset.card hm
  have hm' : ({Δ 0, Δ 1} : Multiset (Segment k)) =
    {.single _ (IrrGL.isCusp_ofChar χ hχ), .single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)} := hm
  have hp := single_precedes χ hχ
  have h01 : Δ 0 = .single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1) ∧ Δ 1 = .single _ (IrrGL.isCusp_ofChar χ hχ) := by
    rcases Multiset.cons_eq_cons.1 hm' with ⟨a, b⟩ | ⟨-, s, a, b⟩
    · exact absurd hp.1 (by rw [← a, ← Multiset.singleton_inj.1 b]; exact ho 0 1 (by decide))
    · obtain rfl : s = 0 := by simpa using congrArg Multiset.card a
      exact ⟨(Multiset.singleton_inj.1 b).symm, Multiset.singleton_inj.1 a⟩
  refine ⟨rfl, heq_of_eq (funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩))⟩
  · exact eq_of_isLSeg_single _ (h01.1 ▸ hΔ 0)
  · exact eq_of_isLSeg_single _ (h01.2 ▸ hΔ 1)

theorem equiv_of_isL (hχ : IsSmoothChar χ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin 2) k) V} (H : IsL ({Segment.single _ (IrrGL.isCusp_ofChar χ hχ)} +
      {Segment.single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)}) π) :
    Nonempty (π.Equiv (detRep (Fin 2) (χ * absPow k (1 / 2)))) := by
  obtain ⟨_, x, hd, hx, hc⟩ := H
  obtain ⟨_, y, hd', hy, hc'⟩ := isL_detRep_two hχ
  obtain ⟨rfl, h1⟩ := factors_eq hχ hx
  obtain ⟨rfl, h2⟩ := factors_eq hχ hy
  obtain rfl : x = y := eq_of_heq (h1.trans h2.symm)
  exact hc'.unique hc

theorem linked_case (hχ : IsSmoothChar χ) :
    ∃ (𝔪 𝔫 : Multiset (Segment k)) (π₁ π₂ : IrrRep (GL (Fin 1) k)),
      IsL 𝔪 π₁.ρ ∧ IsL 𝔫 π₂.ρ ∧ ¬ (prod₂ π₁.ρ π₂.ρ).IsIrreducible ∧
      (∃ π : IrrRep (GL (Fin (1 + 1)) k), IsL (𝔪 + 𝔫) π.ρ) ∧
        ∀ π : IrrRep (GL (Fin (1 + 1)) k), IsL (𝔪 + 𝔫) π.ρ → jhMult π.ρ (prod₂ π₁.ρ π₂.ρ) = 1 := by
  have hη := hχ.mul (isSmoothChar_absPow (k := k) (1 / 2))
  obtain ⟨φ⟩ := nonempty_equiv_prod hχ
  refine ⟨_, _, IrrRep.det (Fin 1) χ hχ, IrrRep.det (Fin 1) _ (hχ.mul (isSmoothChar_absPow 1)),
    isL_char (IrrGL.isCusp_ofChar χ hχ) hχ rfl,
    isL_char ((IrrGL.isCusp_ofChar χ hχ).nu 1) _ (IrrGL.tw_ofChar _ _ hχ (isSmoothChar_absPow _)),
    fun H => (jhMult_parInd hη).2 (GlobalTheory.Parabolic.isIrreducible_of_equiv φ.symm H),
    ⟨IrrRep.det (Fin 2) _ hη, isL_detRep_two hχ⟩, fun π h => ?_⟩
  obtain ⟨e⟩ := equiv_of_isL hχ h
  have h1 := jhMult_congr_right (detRep (Fin 2) (χ * absPow k (1 / 2))) φ
  rw [(jhMult_parInd hη).1] at h1
  have h2 := jhMult_congr_left e (prod₂ (detRep (Fin 1) χ) (detRep (Fin 1) (χ * absPow k 1)))
  exact h2.trans h1.symm

example : IsNonarchimedeanLocalField ℚ_[2] ∧ CharZero ℚ_[2] ∧ IsSmoothChar (1 : ℚ_[2]ˣ →* ℂˣ) :=
  ⟨inferInstance, inferInstance, isSmoothChar_one⟩

theorem nonempty_equiv_parInd_zero {α V : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [AddCommGroup V] [Module ℂ V] (e : (Σ a, m a) ≃ Fin 0)
    (ρ : Representation ℂ (Levi k m) V) (L : ℂ ≃ₗ[ℂ] V) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (parInd e ρ)) := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  let f : ℂ →ₗ[ℂ] IndSp e ρ :=
    { toFun := fun c => ⟨⟨fun _ => L c, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (hg _)
          simp⟩, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun g => rfl)⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_add L a b))
      map_smul' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_smul L a b)) }
  refine ⟨equivOfBijective ⟨f, fun g => by rw [hg g, map_one, map_one]; rfl⟩ ⟨fun a b h => ?_, fun φ => ?_⟩⟩
  · have h1 : L a = L b := congrArg (fun φ : IndSp e ρ => φ.1.1 1) h
    exact L.injective h1
  · refine ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun g => ?_))⟩
    rw [hg g]
    exact L.apply_symm_apply _

theorem isL_rank_zero {𝔪 : Multiset (Segment k)} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin 0) k) V} (h : IsL 𝔪 π) :
    𝔪 = 0 ∧ Nonempty (π.Equiv (detRep (Fin 0) (1 : kˣ →* ℂˣ))) := by
  have h0 : 𝔪 = 0 := Multiset.eq_zero_of_forall_notMem fun Δ hΔ => by
    have := Multiset.sum_eq_zero_iff.1 (Tests.IsL_deg h) _ (Multiset.mem_map_of_mem _ hΔ)
    exact (Nat.mul_pos Δ.len_pos Δ.d_pos).ne' this
  subst h0
  obtain ⟨s, x, hd, ⟨Δ, ⟨hm, -⟩, -⟩, hc⟩ := h
  obtain rfl : s = 0 := by simpa using congrArg Multiset.card hm
  obtain ⟨φ⟩ := Tests.nonempty_equiv_prodIrr_zero x hd
  exact ⟨rfl, ((isCosocle_self (isIrreducible_ofChar _)).of_equiv (.refl _) φ).unique hc⟩

theorem rank_zero_case (𝔪 𝔫 : Multiset (Segment k)) (π₁ π₂ : IrrRep (GL (Fin 0) k)) (h₁ : IsL 𝔪 π₁.ρ)
    (h₂ : IsL 𝔫 π₂.ρ) : (∃ π : IrrRep (GL (Fin (0 + 0)) k), IsL (𝔪 + 𝔫) π.ρ) ∧
      ∀ π : IrrRep (GL (Fin (0 + 0)) k), IsL (𝔪 + 𝔫) π.ρ → jhMult π.ρ (prod₂ π₁.ρ π₂.ρ) = 1 := by
  obtain ⟨rfl, ⟨a⟩⟩ := isL_rank_zero h₁
  obtain ⟨rfl, ⟨b⟩⟩ := isL_rank_zero h₂
  refine ⟨⟨π₁, h₁⟩, fun π h => ?_⟩
  obtain ⟨-, ⟨c⟩⟩ := isL_rank_zero h
  obtain ⟨φ⟩ := nonempty_equiv_parInd_zero (two (stdSum (rfl : 0 + 0 = 0 + 0)))
    ((extTensor π₁.ρ π₂.ρ).comp (leviTwo k _ _).symm.toMonoidHom)
    ((TensorProduct.lid ℂ ℂ).symm.trans (TensorProduct.congr a.symm.toLinearEquiv b.symm.toLinearEquiv))
  have h1 := jhMult_congr_right (detRep (Fin 0) (1 : kˣ →* ℂˣ)) φ
  rw [jhMult_self (σ := detRep (Fin 0) (1 : kˣ →* ℂˣ)) (isIrreducible_ofChar _)] at h1
  exact (jhMult_congr_left c _).trans h1.symm

end GlobalTheory.Published.LanglandsSumTests

end
