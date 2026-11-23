import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import Formalism.MirabolicMackeyTheory.MirabolicIsMackey

noncomputable section

open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling

namespace PositivityTheory.Mirab.Irr

variable {k : Type} [Field k] [Fintype k] (n : ℕ)

theorem mackey_gap (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) (h : mirabSub k n) (hh : h ∉ uniSub k n) :
    ∃ u c : uniSub k n, (c : mirabSub k n) = h⁻¹ * u * h ∧ genericChar n ψ₀ c ≠ genericChar n ψ₀ u := by
  obtain ⟨u, hu, hc, hne⟩ := (mirabolicIsMackey k ℂ n ψ₀ hψ (mirabSub k n) (uniSub k n)
    (fun _ => Iff.rfl) (fun _ => Iff.rfl)).2.2 h hh
  exact ⟨⟨u, hu⟩, ⟨_, hc⟩, rfl, hne⟩

theorem vanish_off_uni (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) (f : mirabSub k n → ℂ)
    (hl : ∀ (u : uniSub k n) (x : mirabSub k n), f ((u : mirabSub k n) * x) = genericChar n ψ₀ u * f x)
    (hr : ∀ (x : mirabSub k n) (u : uniSub k n), f (x * (u : mirabSub k n)) = f x * genericChar n ψ₀ u)
    (h : mirabSub k n) (hh : h ∉ uniSub k n) : f h = 0 := by
  obtain ⟨u, c, hcu, hne⟩ := mackey_gap n ψ₀ hψ h hh
  have h1 := hl u h
  have h2 := hr h c
  have e : h * (c : mirabSub k n) = u * h := by rw [hcu]; group
  rw [e, h1] at h2
  by_contra hf
  exact hne (mul_left_cancel₀ hf (h2.symm.trans (mul_comm _ _)))

open Classical in

def deltaU (ψ₀ : AddChar k ℂ) (x : mirabSub k n) : ℂ :=
  if h : x ∈ uniSub k n then genericChar n ψ₀ ⟨x, h⟩ else 0

theorem deltaU_one (ψ₀ : AddChar k ℂ) : deltaU n ψ₀ 1 = 1 := by
  unfold deltaU
  rw [dif_pos (one_mem _)]
  exact map_one (genericChar n ψ₀)

theorem deltaU_mem (ψ₀ : AddChar k ℂ) : deltaU n ψ₀ ∈ MirabInducedSpace n ψ₀ := by
  rw [mem_mirabInducedSpace]
  intro u x
  by_cases hx : x ∈ uniSub k n
  · have hux : (u : mirabSub k n) * x ∈ uniSub k n := mul_mem u.2 hx
    unfold deltaU
    rw [dif_pos hx, dif_pos hux, ← map_mul]
    exact congrArg (genericChar n ψ₀) (Subtype.ext rfl)
  · have hux : (u : mirabSub k n) * x ∉ uniSub k n := by
      intro hm
      have := mul_mem (inv_mem u.2) hm
      rw [← mul_assoc, inv_mul_cancel, one_mul] at this
      exact hx this
    unfold deltaU
    rw [dif_neg hx, dif_neg hux, mul_zero]

theorem char_inv_mul (ψ₀ : AddChar k ℂ) (u : uniSub k n) :
    genericChar n ψ₀ (u⁻¹) * genericChar n ψ₀ u = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem avg_apply [Fintype (uniSub k n)] (ψ₀ : AddChar k ℂ) (f : MirabInducedSpace n ψ₀) (x : mirabSub k n) :
    ((∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) • mirabInduced n ψ₀ (u : mirabSub k n) f :
        MirabInducedSpace n ψ₀) : mirabSub k n → ℂ) x =
      ∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * (f : mirabSub k n → ℂ) (x * u) := by
  rw [Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Submodule.coe_smul, Pi.smul_apply, mirabInduced_apply, smul_eq_mul]

theorem avg_right [Fintype (uniSub k n)] (ψ₀ : AddChar k ℂ) (f : mirabSub k n → ℂ) (x : mirabSub k n)
    (v : uniSub k n) :
    ∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * f (x * (v : mirabSub k n) * u) =
      (∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * f (x * u)) * genericChar n ψ₀ v := by
  rw [Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ (fun u => ?_)
  have h3 := char_inv_mul n ψ₀ v
  have e : x * (v : mirabSub k n) * u = x * ((v * u : uniSub k n) : mirabSub k n) := by
    rw [Subgroup.coe_mul, mul_assoc]
  change _ = genericChar n ψ₀ ((v * u)⁻¹) * f (x * ((v * u : uniSub k n) : mirabSub k n)) * genericChar n ψ₀ v
  rw [e, mul_inv_rev, map_mul]
  linear_combination (-(genericChar n ψ₀ (u⁻¹) * f (x * ((v * u : uniSub k n) : mirabSub k n)))) * h3

theorem avg_one [Fintype (uniSub k n)] (ψ₀ : AddChar k ℂ) (f : mirabSub k n → ℂ)
    (hf : f ∈ MirabInducedSpace n ψ₀) :
    ∑ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * f (1 * u) = (Nat.card (uniSub k n) : ℂ) * f 1 := by
  rw [mem_mirabInducedSpace] at hf
  have e : ∀ u : uniSub k n, genericChar n ψ₀ (u⁻¹) * f (1 * u) = f 1 := by
    intro u
    have h2 : f (u : mirabSub k n) = genericChar n ψ₀ u * f 1 := by rw [← hf u 1, mul_one]
    rw [one_mul, h2]
    linear_combination f 1 * char_inv_mul n ψ₀ u
  rw [Finset.sum_congr rfl (fun u _ => e u), Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
    nsmul_eq_mul]

theorem sum_translate (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) [Fintype (mirabSub k n)] [Fintype (uniSub k n)]
    (F g : mirabSub k n → ℂ) (hF : F ∈ MirabInducedSpace n ψ₀)
    (hr : ∀ (x : mirabSub k n) (u : uniSub k n), F (x * (u : mirabSub k n)) = F x * genericChar n ψ₀ u)
    (hg : g ∈ MirabInducedSpace n ψ₀) (x : mirabSub k n) :
    ∑ p : mirabSub k n, g p * F (x * p⁻¹) = (Nat.card (uniSub k n) : ℂ) * F 1 * g x := by
  rw [mem_mirabInducedSpace] at hF hg
  have e1 : ∑ p : mirabSub k n, g p * F (x * p⁻¹) = ∑ y : mirabSub k n, g (y⁻¹ * x) * F y := by
    refine Fintype.sum_equiv ((Equiv.inv _).trans (Equiv.mulLeft x)) _ _ (fun p => ?_)
    change _ = g ((x * p⁻¹)⁻¹ * x) * F (x * p⁻¹)
    rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  have e2 : ∑ u : uniSub k n, g ((u : mirabSub k n)⁻¹ * x) * F u =
      ∑ y ∈ Finset.univ.map (Function.Embedding.subtype (· ∈ uniSub k n)), g (y⁻¹ * x) * F y := by
    rw [Finset.sum_map]; rfl
  have e3 : ∑ y : mirabSub k n, g (y⁻¹ * x) * F y =
      ∑ y ∈ Finset.univ.map (Function.Embedding.subtype (· ∈ uniSub k n)), g (y⁻¹ * x) * F y := by
    refine (Finset.sum_subset (Finset.subset_univ _) (fun y _ hy => ?_)).symm
    have hy' : y ∉ uniSub k n := fun hm => hy (Finset.mem_map.2 ⟨⟨y, hm⟩, Finset.mem_univ _, rfl⟩)
    rw [vanish_off_uni n ψ₀ hψ F hF hr y hy', mul_zero]
  have e4 : ∀ u : uniSub k n, g ((u : mirabSub k n)⁻¹ * x) * F u = F 1 * g x := by
    intro u
    have h1 : g ((u : mirabSub k n)⁻¹ * x) = genericChar n ψ₀ (u⁻¹) * g x := hg (u⁻¹) x
    have h2 : F (u : mirabSub k n) = genericChar n ψ₀ u * F 1 := by rw [← hF u 1, mul_one]
    rw [h1, h2]
    linear_combination (F 1 * g x) * char_inv_mul n ψ₀ u
  rw [e1, e3, ← e2, Finset.sum_congr rfl (fun u _ => e4 u), Finset.sum_const, Finset.card_univ,
    Fintype.card_eq_nat_card, nsmul_eq_mul]
  ring

theorem mirabInduced_isIrreducible (ψ₀ : AddChar k ℂ) (hψ : ψ₀ ≠ 1) : (mirabInduced n ψ₀).IsIrreducible := by
  classical
  let δ : MirabInducedSpace n ψ₀ := ⟨deltaU n ψ₀, deltaU_mem n ψ₀⟩
  have hδ : δ ≠ 0 := by
    intro h
    have h1 : (δ : mirabSub k n → ℂ) 1 = 0 := by rw [h]; rfl
    exact one_ne_zero ((deltaU_one n ψ₀).symm.trans h1)
  have hne : (⊥ : Subrepresentation (mirabInduced n ψ₀)) ≠ ⊤ := by
    intro h
    have hm : δ ∈ (⊤ : Subrepresentation (mirabInduced n ψ₀)).toSubmodule := Submodule.mem_top
    rw [← h] at hm
    exact hδ ((Submodule.mem_bot ℂ).1 hm)
  have : Nontrivial (Subrepresentation (mirabInduced n ψ₀)) := ⟨⟨⊥, ⊤, hne⟩⟩
  refine ⟨fun W => ?_⟩
  rcases eq_or_ne W ⊥ with hW | hW
  · exact Or.inl hW
  right
  obtain ⟨f, hfW, hf0⟩ : ∃ f ∈ W.toSubmodule, f ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hW (Subrepresentation.toSubmodule_injective ((Submodule.eq_bot_iff _).2 hc))
  obtain ⟨q, hq⟩ : ∃ q, (f : mirabSub k n → ℂ) q ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf0 (Subtype.ext (funext hc))
  have hf'W : mirabInduced n ψ₀ q f ∈ W.toSubmodule := W.apply_mem_toSubmodule q hfW
  obtain ⟨F, hFdef⟩ : ∃ F : MirabInducedSpace n ψ₀, F = ∑ u : uniSub k n,
      genericChar n ψ₀ (u⁻¹) • mirabInduced n ψ₀ (u : mirabSub k n) (mirabInduced n ψ₀ q f) := ⟨_, rfl⟩
  have hFW : F ∈ W.toSubmodule := by
    rw [hFdef]
    exact Submodule.sum_mem _ (fun u _ => Submodule.smul_mem _ _ (W.apply_mem_toSubmodule _ hf'W))
  have hFx : ∀ x, (F : mirabSub k n → ℂ) x = ∑ u : uniSub k n,
      genericChar n ψ₀ (u⁻¹) * ((mirabInduced n ψ₀ q f : MirabInducedSpace n ψ₀) : mirabSub k n → ℂ) (x * u) := by
    intro x
    rw [hFdef]
    exact avg_apply n ψ₀ _ x
  have hFr : ∀ (x : mirabSub k n) (v : uniSub k n),
      (F : mirabSub k n → ℂ) (x * v) = (F : mirabSub k n → ℂ) x * genericChar n ψ₀ v := by
    intro x v
    rw [hFx, hFx]
    exact avg_right n ψ₀ _ x v
  have hF1 : (F : mirabSub k n → ℂ) 1 = (Nat.card (uniSub k n) : ℂ) * (f : mirabSub k n → ℂ) q := by
    rw [hFx, avg_one n ψ₀ _ (mirabInduced n ψ₀ q f).2, mirabInduced_apply, one_mul]
  have hcard : (Nat.card (uniSub k n) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hc : (Nat.card (uniSub k n) : ℂ) * (F : mirabSub k n → ℂ) 1 ≠ 0 := by
    rw [hF1]
    exact mul_ne_zero hcard (mul_ne_zero hcard hq)
  refine eq_top_iff.2 ?_
  intro g _
  change g ∈ W.toSubmodule
  have hg : g = ((Nat.card (uniSub k n) : ℂ) * (F : mirabSub k n → ℂ) 1)⁻¹ •
      ∑ p : mirabSub k n, (g : mirabSub k n → ℂ) p • mirabInduced n ψ₀ p⁻¹ F := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_smul, Pi.smul_apply, Submodule.coe_sum, Finset.sum_apply]
    simp only [Submodule.coe_smul, Pi.smul_apply, mirabInduced_apply, smul_eq_mul]
    rw [sum_translate n ψ₀ hψ F g F.2 hFr g.2 x, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [hg]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _ (W.apply_mem_toSubmodule _ hFW)))

end PositivityTheory.Mirab.Irr
