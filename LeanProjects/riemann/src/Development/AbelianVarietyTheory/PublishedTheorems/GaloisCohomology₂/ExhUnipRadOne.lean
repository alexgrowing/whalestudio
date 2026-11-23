import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NonemptyEquivParIndZero

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocGL.ProjLine ValuativeRel

noncomputable section
namespace GlobalTheory.LocGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exh_unipRad_one {s : ℕ} {d : Fin s → ℕ} (e : (Σ a : Fin s, Fin (d a)) ≃ Fin 1) : unipRad k e = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  have h := det_eq_one_of_mem_unipRad k hu
  have h2 : (u : Matrix (Fin 1) (Fin 1) k).det = 1 := by
    simpa using congrArg Units.val h
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simpa using h2

theorem exh_deg_one (c : IrrCl (GL (Fin 1) k)) : ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 (IrrGL.rep ⟨1, c⟩) := by
  have hc : IrrGL.IsCusp (⟨1, c⟩ : IrrGL k) := ⟨one_pos, c.rep.smooth, fun s d e he => absurd (exh_unipRad_one e) he⟩
  exact ⟨_, (single_spec hc).2.2.2⟩

theorem exh_equiv_zero {m : Fin 0 → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin 0)
    {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Levi k m) W)
    (E : W ≃ₗ[ℂ] ℂ) (π : Representation ℂ (GL (Fin 0) k) V) (hirr : π.IsIrreducible) :
    Nonempty ((parInd e ρ).Equiv π) := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  have hnt : ∃ v : V, v ≠ 0 := by
    by_contra h
    push Not at h
    have : (⊥ : Subrepresentation π) = ⊤ := by
      ext v; rw [h v]; exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := hnt
  let S : Subrepresentation π := ⟨Submodule.span ℂ {v}, fun g w hw => by simpa [hg g] using hw⟩
  have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left fun h => hv (by
    have : v ∈ S := Submodule.mem_span_singleton_self v
    rw [h] at this; exact this)
  have hspan : ∀ w : V, ∃ a : ℂ, a • v = w := fun w => by
    have : w ∈ S := by rw [hS]; trivial
    exact Submodule.mem_span_singleton.1 this
  let f : (parInd e ρ).IntertwiningMap π :=
    { toFun := fun φ => E (φ.1.1 1) • v
      map_add' := fun φ ψ => by
        show E (φ.1.1 1 + ψ.1.1 1) • v = _
        rw [map_add, add_smul]
      map_smul' := fun a φ => by
        show E (a • φ.1.1 1) • v = a • (E (φ.1.1 1) • v)
        rw [map_smul, smul_eq_mul, mul_smul]
      isIntertwining' := fun g => by rw [hg g, map_one, map_one]; rfl }
  have hinj : Function.Injective f := fun φ ψ h => by
    have h1 : E (φ.1.1 1) • v = E (ψ.1.1 1) • v := h
    have h2 := E.injective (smul_left_injective ℂ hv h1)
    exact Subtype.ext (Subtype.ext (funext fun g => by rw [hg g]; exact h2))
  have hsurj : Function.Surjective f := fun w => by
    obtain ⟨a, rfl⟩ := hspan w
    refine ⟨⟨⟨fun _ => E.symm a, fun p g => ?_⟩, ?_⟩, ?_⟩
    · have : p = 1 := Subtype.ext (hg _)
      subst this; simp
    · exact mem_smoothPart_of_nhds (Filter.univ_mem' fun g => by rw [hg g]; simp)
    · show E (E.symm a) • v = a • v
      simp
  exact ⟨equivOfBijective f ⟨hinj, hsurj⟩⟩

theorem exh_deg_zero (c : IrrCl (GL (Fin 0) k)) : IsL (0 : Multiset (Segment k)) (IrrGL.rep ⟨0, c⟩) := by
  let x : Fin 0 → IrrGL k := Fin.elim0
  have hd : ∑ a, (x a).1 = 0 := by simp
  refine ⟨0, x, hd, ⟨Fin.elim0, ⟨rfl, fun i => i.elim0⟩, fun i => i.elim0⟩, ?_⟩
  obtain ⟨φ⟩ := exh_equiv_zero (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)
    (PiTensorProduct.isEmptyEquiv (Fin 0)) c.rep.ρ c.rep.irr
  exact (isCosocle_self c.rep.irr).of_equiv (.refl _) φ.symm

theorem exh_not_zero (x : IrrGL k) (hx : 0 < x.1) : ¬ IsL (0 : Multiset (Segment k)) x.rep := by
  rintro ⟨h, y, hd, ⟨Δ, ⟨hΔ, -⟩, -⟩, -⟩
  have : h = 0 := by simpa using congrArg Multiset.card hΔ
  subst this
  simp at hd
  omega

theorem exh_le_one (x : IrrGL k) (hx : x.1 ≤ 1) : ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep := by
  obtain ⟨n, c⟩ := x
  obtain rfl | rfl : n = 0 ∨ n = 1 := by simp at hx; omega
  · exact ⟨0, exh_deg_zero c⟩
  · exact exh_deg_one c

theorem exh_char_two {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 (IrrGL.rep ⟨2, (IrrRep.det (Fin 2) η hη).cl⟩) := by
  have hχ := hη.mul (isSmoothChar_absPow (k := k) (-(1 / 2)))
  have h := isL_detRep_two hχ
  have e : η * absPow k (-(1 / 2)) * absPow k (1 / 2) = η := by
    rw [mul_assoc, ← absPow_add]; simp
  rw [e] at h
  exact ⟨_, h.of_equiv (equivRep (IrrRep.det (Fin 2) η hη))⟩

example : IsNonarchimedeanLocalField ℚ_[2] ∧ CharZero ℚ_[2] := ⟨inferInstance, inferInstance⟩

end GlobalTheory.LocGL
end
