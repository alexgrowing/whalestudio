import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PHeckeFormal

noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

theorem dC_translate {Γ : Type} [Group Γ] {m : ℕ} (F : (Fin (m + 1) → Γ) → ℝ) (g : Γ) (y : Fin (m + 2) → Γ) :
    dC (fun y : Fin (m + 1) → Γ => F fun j => g * y j) y = dC F (fun j => g * y j) := rfl

theorem pTransfer (hC : PCobSub) (hE : PEvDC) : PTransfer := by
  intro Γ X _ _ act h1 hm m Φ hΦ hd hcyc z hz
  classical
  haveI : Fintype X := Fintype.ofFinite X
  have hinv : ∀ x, Inv (stabR act h1 hm x).subtype (Φ x) := by
    intro x g y
    have hg : act x (g : Γ) = x := g.2
    show (Φ x fun j => (g : Γ) * y j) = Φ x y
    rw [← hΦ x g y, hg]
  have hex : ∀ x, ∃ Ψ : (Fin (m + 1) → Γ) → ℝ, Inv (stabR act h1 hm x).subtype Ψ ∧ dC Ψ = Φ x :=
    fun x => hC Γ (stabR act h1 hm x) m (Φ x) (hinv x) (hd x) (hcyc x)
  choose Ψ hΨi hΨd using hex
  obtain ⟨rep, hrep1, hrep2⟩ : ∃ rep : X → X, (∀ x h, rep (act x h) = rep x) ∧
      ∀ x, ∃ g, act (rep x) g = x := by
    letI S : Setoid X := ⟨fun a b => ∃ g, act a g = b, ⟨fun a => ⟨1, h1 a⟩,
      fun ⟨g, hg⟩ => ⟨g⁻¹, by rw [← hg, ← hm, mul_inv_cancel, h1]⟩,
      fun ⟨g, hg⟩ ⟨k, hk⟩ => ⟨g * k, by rw [hm, hg, hk]⟩⟩⟩
    refine ⟨fun x => (Quotient.mk S x).out, fun x h => ?_, fun x => ?_⟩
    · exact congrArg Quotient.out (@Quotient.sound _ S _ _ ⟨h⁻¹, by rw [← hm, mul_inv_cancel, h1]⟩)
    · exact @Quotient.mk_out _ S x
  obtain ⟨gs, hgs⟩ : ∃ gs : X → Γ, ∀ x, act (rep x) (gs x) = x :=
    ⟨fun x => (hrep2 x).choose, fun x => (hrep2 x).choose_spec⟩
  have hshift : ∀ x h (y : Fin (m + 1) → Γ),
      Ψ (rep x) (fun j => gs x * (h * y j)) = Ψ (rep (act x h)) (fun j => gs (act x h) * y j) := by
    intro x h y
    have e2 := hgs (act x h)
    rw [hrep1] at e2 ⊢
    have hk : act (rep x) (gs x * h * (gs (act x h))⁻¹) = rep x := by
      have t : act (act (rep x) (gs (act x h))) (gs (act x h))⁻¹ = rep x := by
        rw [← hm, mul_inv_cancel, h1]
      rw [e2] at t
      rw [hm, hm, hgs x, t]
    have := hΨi (rep x) ⟨gs x * h * (gs (act x h))⁻¹, hk⟩ (fun j => gs (act x h) * y j)
    rw [← this]
    congr 1
    funext j
    show gs x * (h * y j) = (gs x * h * (gs (act x h))⁻¹) * (gs (act x h) * y j)
    group
  have hEinv : Inv (MonoidHom.id Γ) (fun y : Fin (m + 1) → Γ => ∑ x, Ψ (rep x) fun j => gs x * y j) := by
    intro g y
    show ∑ x, Ψ (rep x) (fun j => gs x * (g * y j)) = ∑ x, Ψ (rep x) fun j => gs x * y j
    rw [Finset.sum_congr rfl (fun x _ => hshift x g y)]
    exact Fintype.sum_equiv ⟨fun x => act x g, fun x => act x g⁻¹,
      fun x => by simp only; rw [← hm, mul_inv_cancel, h1],
      fun x => by simp only; rw [← hm, inv_mul_cancel, h1]⟩ _ _
      (fun x => rfl)
  have hdE : dC (fun y : Fin (m + 1) → Γ => ∑ x, Ψ (rep x) fun j => gs x * y j)
      = fun y => ∑ x, Φ x y := by
    funext y
    have hx : ∀ x, Φ x y = dC (fun y' : Fin (m + 1) → Γ => Ψ (rep x) fun j => gs x * y' j) y := by
      intro x
      rw [dC_translate (Ψ (rep x)) (gs x) y, hΨd (rep x), ← hΦ (rep x) (gs x) y, hgs x]
    simp only [hx, dC, Finset.mul_sum]
    exact Finset.sum_comm
  have key := hE Γ Γ Γ (MonoidHom.id Γ) m
    (fun y : Fin (m + 1) → Γ => ∑ x, Ψ (rep x) fun j => gs x * y j) hEinv 1 z
  rw [hdE] at key
  have hz' : bd Γ m z = 0 := hz
  rw [hz'] at key
  simp only [finsum_eq_sum_of_fintype]
  rw [key]
  simp [ev]

end PositivityTheory.KB.AffineStabilizerVanishing

end
