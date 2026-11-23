import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCastRfl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorTorusCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorDeterminantPairEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicInductionColumnEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositionSeriesIntertwiningChainStatement
open scoped TensorProduct
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL

namespace GlobalTheory.IndLineGL.TorusPiece

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem delta_torus (m : ℕ) (t₁ t₂ : kˣ) :
    deltaHalf k (fun i : Fin 3 => Fin (blk3 m i)) (torusPt k m t₁ t₂) =
      absPow k (((m : ℂ) + 1) / 2) t₁ * absPow k (-((m : ℂ) + 1) / 2) t₂ := by
  rw [deltaHalf_apply, Fin.prod_univ_three, torusPt_zero, torusPt_one, torusPt_two,
    Matrix.GeneralLinearGroup.det_scalar, Matrix.GeneralLinearGroup.det_scalar, map_one, map_one, mul_one,
    CellTorus.modExp_three_zero, CellTorus.modExp_three_two, Fintype.card_fin, Fintype.card_fin]
  have h0 : blk3 m 0 = 1 := rfl
  have h1 : blk3 m 1 = m := rfl
  have h2 : blk3 m 2 = 1 := rfl
  rw [h0, h1, h2, pow_one, pow_one]
  congr 3 <;> push_cast <;> ring

private theorem delta_mid (m : ℕ) (h : GL (Fin m) k) :
    deltaHalf k (fun i : Fin 3 => Fin (blk3 m i)) (midIncl k m h) = 1 := by
  have h0 : (midIncl k m h) 0 = 1 := by
    show Pi.mulSingle (M := fun i : Fin 3 => GL (Fin (blk3 m i)) k) 1 h 0 = 1
    exact Pi.mulSingle_eq_of_ne (by decide) _
  have h2 : (midIncl k m h) 2 = 1 := by
    show Pi.mulSingle (M := fun i : Fin 3 => GL (Fin (blk3 m i)) k) 1 h 2 = 1
    exact Pi.mulSingle_eq_of_ne (by decide) _
  rw [deltaHalf_apply, Fin.prod_univ_three, h0, h2]
  have hm : modExp (fun i : Fin 3 => Fin (blk3 m i)) 1 = 0 := by
    simp [modExp, Finset.sum_filter, Fin.sum_univ_three]
  rw [hm, map_one, map_one, map_one, map_one, mul_one]
  simp

private def b₀ (x x' : ℕ) : SizeMatrix (Two (Fin (x + 2)) (Fin x')) fun j : Fin 3 => Fin (blk3 (x + x') j) :=
  ⟨fun r => cond r ![0, x', 0] ![1, x, 1], by
    constructor
    · intro i
      cases i
      · rw [Fin.sum_univ_three]
        refine Eq.trans ?_ (Fintype.card_fin (x + 2)).symm
        show 1 + x + 1 = x + 2
        omega
      · rw [Fin.sum_univ_three]
        refine Eq.trans ?_ (Fintype.card_fin x').symm
        show 0 + x' + 0 = x'
        omega
    · intro j
      rw [Fintype.sum_bool, Fintype.card_fin]
      fin_cases j
      · rfl
      · show x' + x = x + x'
        omega
      · rfl⟩

private theorem delta_cell (x x' : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (t₁ t₂ : kˣ) :
    (χ₁ * absPow k ((x' : ℂ) / 2)) t₁ * (χ₁ * absPow k (-(x' : ℂ) / 2)) t₂ =
      deltaHalf k (fun i : Fin 3 => Fin (blk3 (x + x') i)) (torusPt k (x + x') t₁ t₂) *
        cellChar k (x + 2) x' χ₁ χ₂ (b₀ x x').1 t₁ t₂ := by
  rw [delta_torus, cellChar, Fintype.prod_bool]
  have e1 : (x' : ℂ) / 2 = (((x + x' : ℕ) : ℂ) + 1) / 2 + (1 - ((x + 2 : ℕ) : ℂ)) / 2 := by push_cast; ring
  have e2 : -(x' : ℂ) / 2 = -(((x + x' : ℕ) : ℂ) + 1) / 2 + (((x + 2 : ℕ) : ℂ) - 1) / 2 := by push_cast; ring
  rw [e2, e1, absPow_add, absPow_add]
  have a1 : (b₀ x x').1 true 0 = 0 := rfl
  have a2 : (b₀ x x').1 true 2 = 0 := rfl
  have a3 : (b₀ x x').1 false 0 = 1 := rfl
  have a4 : (b₀ x x').1 false 2 = 1 := rfl
  rw [a1, a2, a3, a4]
  simp only [cond_true, cond_false, pow_zero, pow_one, MonoidHom.mul_apply, one_mul]
  have key : ∀ a b c d e f : ℂˣ, a * (b * c) * (d * (e * f)) = b * e * (a * c * (d * f)) := by
    intros; ac_rfl
  exact key _ _ _ _ _ _

private theorem exists_ne {χ₁ χ₂ : kˣ →* ℂˣ} (h : ∀ t : ℝ, χ₁ * χ₂⁻¹ ≠ absPow k (t : ℂ)) (r s : ℝ) :
    ∃ a, (χ₁ * absPow k (r : ℂ)) a ≠ (χ₂ * absPow k (s : ℂ)) a := by
  by_contra hc
  push Not at hc
  have e : χ₁ * absPow k (r : ℂ) = χ₂ * absPow k (s : ℂ) := MonoidHom.ext hc
  apply h (s - r)
  rw [Complex.ofReal_sub, sub_eq_add_neg, absPow_add, absPow_neg, mul_inv_eq_iff_eq_mul, mul_right_comm,
    eq_mul_inv_iff_mul_eq, e, mul_comm]

private theorem exists_sep (x x' : ℕ) {χ₁ χ₂ : kˣ →* ℂˣ} (h : ∀ t : ℝ, χ₁ * χ₂⁻¹ ≠ absPow k (t : ℂ))
    (b : SizeMatrix (Two (Fin (x + 2)) (Fin x')) fun j : Fin 3 => Fin (blk3 (x + x') j)) (hb : b ≠ b₀ x x') :
    ∃ p : kˣ × kˣ, cellChar k (x + 2) x' χ₁ χ₂ (b₀ x x').1 p.1 p.2 ≠ cellChar k (x + 2) x' χ₁ χ₂ b.1 p.1 p.2 := by
  have hc0 : b.1 true 0 + b.1 false 0 = 1 := by
    have := b.2.2 0
    rw [Fintype.sum_bool, Fintype.card_fin] at this
    exact this
  have hc2 : b.1 true 2 + b.1 false 2 = 1 := by
    have := b.2.2 2
    rw [Fintype.sum_bool, Fintype.card_fin] at this
    exact this
  have hrf : b.1 false 0 + b.1 false 1 + b.1 false 2 = x + 2 := by
    have := b.2.1 false
    rw [Fin.sum_univ_three] at this
    rw [this]; exact Fintype.card_fin _
  have hrt : b.1 true 0 + b.1 true 1 + b.1 true 2 = x' := by
    have := b.2.1 true
    rw [Fin.sum_univ_three] at this
    rw [this]; exact Fintype.card_fin _
  have a1 : (b₀ x x').1 true 0 = 0 := rfl
  have a2 : (b₀ x x').1 true 2 = 0 := rfl
  have a3 : (b₀ x x').1 false 0 = 1 := rfl
  have a4 : (b₀ x x').1 false 2 = 1 := rfl
  by_cases h0 : b.1 true 0 = 1
  · obtain ⟨a, ha⟩ := exists_ne h ((1 - ((x + 2 : ℕ) : ℝ)) / 2) ((1 - (x' : ℝ)) / 2)
    refine ⟨(a, 1), ?_⟩
    have h0' : b.1 false 0 = 0 := by omega
    simp only [cellChar, Fintype.prod_bool, a1, a2, a3, a4, h0, h0', cond_true, cond_false, map_one, one_pow,
      pow_zero, pow_one, mul_one, one_mul]
    push_cast at ha ⊢
    exact ha
  by_cases h2 : b.1 true 2 = 1
  · obtain ⟨a, ha⟩ := exists_ne h ((((x + 2 : ℕ) : ℝ) - 1) / 2) (((x' : ℝ) - 1) / 2)
    refine ⟨(1, a), ?_⟩
    have h0' : b.1 false 2 = 0 := by omega
    simp only [cellChar, Fintype.prod_bool, a1, a2, a3, a4, h2, h0', cond_true, cond_false, map_one, one_pow,
      pow_zero, pow_one, mul_one, one_mul]
    push_cast at ha ⊢
    exact ha
  exfalso
  apply hb
  apply Subtype.ext
  funext i j
  cases i <;> fin_cases j
  · show b.1 false 0 = 1
    omega
  · show b.1 false 1 = x
    omega
  · show b.1 false 2 = 1
    omega
  · show b.1 true 0 = 0
    omega
  · show b.1 true 1 = x'
    omega
  · show b.1 true 2 = 0
    omega

private theorem prod_rescale {ι J : Type} [AddCommGroup J] [Module ℂ J] (U V : ι → Module.End ℂ J) (d : ι → ℂ)
    (h : ∀ t, U t = d t • V t) (l : List ι) : (l.map U).prod = (l.map d).prod • (l.map V).prod := by
  induction l with
  | nil => simp
  | cons t l ih => simp only [List.map_cons, List.prod_cons, ih, h t, smul_mul_smul_comm]

private theorem cellMid_equiv (χ₁ χ₂ : kˣ →* ℂˣ) (b : Bool → Fin 3 → ℕ) (h1 : b false 0 = b false 2)
    (h2 : b true 0 = b true 2) :
    Nonempty ((cellMid k χ₁ χ₂ b).Equiv
      (prod₂ (detRep (Fin (b false 1)) χ₁) (detRep (Fin (b true 1)) χ₂))) := by
  have key : ∀ α β : kˣ →* ℂˣ, α = χ₁ → β = χ₂ →
      Nonempty ((prod₂ (detRep (Fin (b false 1)) α) (detRep (Fin (b true 1)) β)).Equiv
        (prod₂ (detRep (Fin (b false 1)) χ₁) (detRep (Fin (b true 1)) χ₂))) := by
    rintro _ _ rfl rfl
    exact ⟨Representation.Equiv.refl _⟩
  exact key _ _ (by rw [h1, sub_self, zero_div, absPow_zero, mul_one])
    (by rw [h2, sub_self, zero_div, absPow_zero, mul_one])

private theorem equiv_comp {G H V Y : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y]
    [Module ℂ Y] {ρ : Representation ℂ G V} {τ : Representation ℂ G Y} (e : ρ.Equiv τ) (φ : H →* G) :
    Nonempty (Representation.Equiv (ρ.comp φ) (τ.comp φ)) :=
  ⟨.mk e.toLinearEquiv fun x => e.toIntertwiningMap.isIntertwining' (φ x)⟩

private theorem equiv_of_eq {G H V Y : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y]
    [Module ℂ Y] {ρ : Representation ℂ G V} {τ : Representation ℂ H Y} {φ φ' : H →* G} (h : φ = φ')
    (e : Nonempty (Representation.Equiv (ρ.comp φ) τ)) : Nonempty (Representation.Equiv (ρ.comp φ') τ) := by
  subst h; exact e

private theorem mid_equiv' (a a' m : ℕ) {χ₁ χ₂ : kˣ →* ℂˣ} (h1 : IsSmoothChar χ₁) (h2 : IsSmoothChar χ₂)
    (b : SizeMatrix (Two (Fin a) (Fin a')) fun j : Fin 3 => Fin (blk3 m j))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin a) (Fin a') i)
    (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (blk3 m j)) (h3 : b.1 false 0 = b.1 false 2)
    (h4 : b.1 true 0 = b.1 true 2) (x x' : ℕ) (hx : b.1 false 1 = x) (hx' : b.1 true 1 = x') (hm : x + x' = m) :
    Nonempty (Representation.Equiv
      ((cellFunctor f g (detPair k a a' χ₁ χ₂)).comp ((midIncl k m).comp (glCast k hm)))
      (prod₂ (detRep (Fin x) χ₁) (detRep (Fin x') χ₂))) := by
  subst hx hx'
  have e1 := (GlobalTheory.T.cell_functor_determinant_pair_equiv k a a' m χ₁ χ₂ h1 h2 b f g).some
  have e2 := (GlobalTheory.T.parabolic_induction_column_equiv k a a' m χ₁ χ₂ b f g hm).some
  have e : Representation.Equiv ((cellFunctor f g (detPair k a a' χ₁ χ₂)).comp ((midIncl k m).comp (glCast k hm)))
      (cellMid k χ₁ χ₂ b.1) := (equiv_comp e1 (glCast k hm)).some.trans e2
  exact ⟨e.trans (cellMid_equiv χ₁ χ₂ b.1 h3 h4).some⟩

private theorem mid_equiv (x x' : ℕ) {χ₁ χ₂ : kˣ →* ℂˣ} (h1 : IsSmoothChar χ₁) (h2 : IsSmoothChar χ₂)
    (b : SizeMatrix (Two (Fin (x + 2)) (Fin x')) fun j : Fin 3 => Fin (blk3 (x + x') j)) (hb : b = b₀ x x')
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin (x + 2)) (Fin x') i)
    (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (blk3 (x + x') j)) :
    Nonempty (Representation.Equiv ((cellFunctor f g (detPair k (x + 2) x' χ₁ χ₂)).comp (midIncl k (x + x')))
      (prod₂ (detRep (Fin x) χ₁) (detRep (Fin x') χ₂))) := by
  have := mid_equiv' (x + 2) x' (x + x') h1 h2 b f g (by rw [hb]; rfl) (by rw [hb]; rfl) x x'
    (by rw [hb]; rfl) (by rw [hb]; rfl) rfl
  have hg : (midIncl k (x + x')).comp (glCast k (rfl : x + x' = x + x')) = midIncl k (x + x') := by
    rw [glCast_rfl k (x + x'), MonoidHom.comp_id]
  exact equiv_of_eq hg this

private theorem abstract_step {L H J P Q ι : Type} [Group L] [Group H] [AddCommGroup J] [Module ℂ J]
    [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]
    (ρ : Representation ℂ L J) (δ : L →* ℂˣ) (φ : H →* L) (hδ : ∀ h, δ (φ h) = 1)
    (σ : Representation ℂ L Q) (π : Representation ℂ H P) (E : Representation.Equiv (σ.comp φ) π)
    (A : σ.IntertwiningMap (twist ρ δ⁻¹)) (l : List ι) (z : ι → L) (c : ι → ℂ)
    (hl : ∀ w, (l.map fun t => twist ρ δ⁻¹ (z t) - c t • (1 : Module.End ℂ J)).prod w ∈
      LinearMap.range A.toLinearMap) :
    ∃ A' : P →ₗ[ℂ] J, (∀ h w, A' (π h w) = ρ (φ h) (A' w)) ∧
      ∀ w, (l.map fun t => ρ (z t) - ((δ (z t) : ℂ) * c t) • (1 : Module.End ℂ J)).prod w ∈ LinearMap.range A' := by
  refine ⟨A.toLinearMap ∘ₗ E.symm.toIntertwiningMap.toLinearMap, fun h w => ?_, fun w => ?_⟩
  · have h1 := Representation.IntertwiningMap.isIntertwining _ _ E.symm.toIntertwiningMap h w
    have h2 := Representation.IntertwiningMap.isIntertwining _ _ A (φ h) (E.symm.toIntertwiningMap w)
    have h3 : twist ρ δ⁻¹ (φ h) (A (E.symm.toIntertwiningMap w)) = ρ (φ h) (A (E.symm.toIntertwiningMap w)) := by
      rw [twist_apply, MonoidHom.inv_apply, hδ]; simp
    show A (E.symm.toIntertwiningMap (π h w)) = ρ (φ h) (A (E.symm.toIntertwiningMap w))
    rw [h1, ← h3, ← h2]
    rfl
  · rw [prod_rescale _ (fun t => twist ρ δ⁻¹ (z t) - c t • (1 : Module.End ℂ J)) (fun t => (δ (z t) : ℂ))]
    · rw [LinearMap.smul_apply]
      refine Submodule.smul_mem _ _ ?_
      obtain ⟨y, hy⟩ := hl w
      refine ⟨E y, ?_⟩
      rw [← hy]
      exact congrArg A.toLinearMap (E.toLinearEquiv.symm_apply_apply y)
    · intro t
      ext v
      simp [twist_apply, smul_sub, smul_smul]

private theorem abstract_filt {L H J P T : Type} [Group L] [Group H] [AddCommGroup J] [Module ℂ J]
    [AddCommGroup P] [Module ℂ P] [Inhabited T]
    (ρ : Representation ℂ L J) (δ : L →* ℂˣ) (φ : H →* L) (hδ : ∀ h, δ (φ h) = 1)
    (π : Representation ℂ H P) (N : ℕ) (S : Fin (N + 1) → Subrepresentation (twist ρ δ⁻¹))
    (hmono : Monotone S) (h0 : S 0 = ⊥) (htop : S (Fin.last N) = ⊤) (t₀ : Fin N)
    (z : T → L) (hz : ∀ p y, y * z p = z p * y) (ξ : T → ℂˣ) (c : Fin N → T → ℂˣ)
    (hc : ∀ t p y, subQuot (S t.succ) (S t.castSucc) (z p) y = (c t p : ℂ) • y)
    (hsep : ∀ t, t ≠ t₀ → ∃ p, ξ p ≠ δ (z p) * c t p)
    (E : Nonempty (Representation.Equiv ((subQuot (S t₀.succ) (S t₀.castSucc)).comp φ) π)) :
    ∃ (l : List (T × ℂ)) (A : P →ₗ[ℂ] J), (∀ p ∈ l, (ξ p.1 : ℂ) ≠ p.2) ∧ (∀ h w, A (π h w) = ρ (φ h) (A w)) ∧
      ∀ w, (l.map fun p => ρ (z p.1) - p.2 • (1 : Module.End ℂ J)).prod w ∈ LinearMap.range A := by
  have hp : ∀ t : Fin N, ∃ p, t ≠ t₀ → ξ p ≠ δ (z p) * c t p := by
    intro t
    by_cases ht : t = t₀
    · exact ⟨default, fun h => absurd ht h⟩
    · obtain ⟨p, hp⟩ := hsep t ht
      exact ⟨p, fun _ => hp⟩
  choose p hp using hp
  obtain ⟨l, A, hl, hA⟩ := GlobalTheory.T.composition_series_intertwining_chain _ _ _ N S hmono h0 htop t₀ (fun t => z (p t)) (fun t => (c t (p t) : ℂ))
    (fun t y => hz _ y) (fun t _ y => hc t _ y)
  obtain ⟨E⟩ := E
  obtain ⟨A', hA1, hA2⟩ := abstract_step ρ δ φ hδ _ _ E A l _ _ hA
  refine ⟨l.map fun t => (p t, (δ (z (p t)) : ℂ) * (c t (p t) : ℂ)), A', ?_, hA1, ?_⟩
  · intro q hq
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hq
    rw [← Units.val_mul]
    exact fun h => hp t (hl t ht) (Units.val_injective h)
  · intro w
    rw [List.map_map]
    exact hA2 w

end GlobalTheory.IndLineGL.TorusPiece

theorem _root_.GlobalTheory.T.induced_character_composition_series : GlobalTheory.Published.GeometricLemmaFiltration → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x x' : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → (∀ t : ℝ, χ₁ * χ₂⁻¹ ≠ absPow k (t : ℂ)) →
    ∀ e : (Σ i : Fin 3, Fin (blk3 (x + x') i)) ≃ Fin (x + 2 + x'),
    ∃ (l : List ((kˣ × kˣ) × ℂ))
      (A : IndSp (two (stdSum (rfl : x + x' = x + x'))) (detPair k x x' χ₁ χ₂) →ₗ[ℂ]
        Jacquet (prod₂ (detRep (Fin (x + 2)) χ₁) (detRep (Fin x') χ₂)) (unipRad k e)),
      (∀ p ∈ l, (((χ₁ * absPow k ((x' : ℂ) / 2)) p.1.1 * (χ₁ * absPow k (-(x' : ℂ) / 2)) p.1.2 : ℂˣ) : ℂ) ≠ p.2) ∧
      (∀ h w, A (prod₂ (detRep (Fin x) χ₁) (detRep (Fin x') χ₂) h w) =
        jacU e (prod₂ (detRep (Fin (x + 2)) χ₁) (detRep (Fin x') χ₂)) (midIncl k (x + x') h) (A w)) ∧
      ∀ w, (l.map fun p => jacU e (prod₂ (detRep (Fin (x + 2)) χ₁) (detRep (Fin x') χ₂)) (torusPt k (x + x') p.1.1 p.1.2) -
        p.2 • (1 : Module.End ℂ (Jacquet (prod₂ (detRep (Fin (x + 2)) χ₁) (detRep (Fin x') χ₂)) (unipRad k e)))).prod w ∈
          LinearMap.range A := by
  intro hG k _ _ _ _ x x' χ₁ χ₂ h1 h2 hχ e
  refine (hG k Bool (Fin 3) (Fin (x + 2 + x')) (Two (Fin (x + 2)) (Fin x'))
    (fun j : Fin 3 => Fin (blk3 (x + x') j)) (two (stdSum (rfl : x + 2 + x' = x + 2 + x'))) e).elim
    fun N hN => hN.elim fun bb hbb => ?_
  refine (hbb (ℂ ⊗[ℂ] ℂ) (detPair k (x + 2) x' χ₁ χ₂) (isSmooth_detPair _ _ h1 h2)).elim fun S hS => ?_
  have hE : ∀ t : Fin N, Nonempty ((subQuot (S t.succ) (S t.castSucc)).Equiv
      (cellFunctor (bb t).nonempty_rows.some (bb t).nonempty_cols.some (detPair k (x + 2) x' χ₁ χ₂))) :=
    fun t => hS.2.2.2 t _ _
  refine (bb.surjective (TorusPiece.b₀ x x')).elim fun t₀ ht₀ => ?_
  have hsep : ∀ t, t ≠ t₀ → ∃ p : kˣ × kˣ,
      (χ₁ * absPow k ((x' : ℂ) / 2)) p.1 * (χ₁ * absPow k (-(x' : ℂ) / 2)) p.2 ≠
        deltaHalf k (fun i : Fin 3 => Fin (blk3 (x + x') i)) (torusPt k (x + x') p.1 p.2) *
          cellChar k (x + 2) x' χ₁ χ₂ (bb t).1 p.1 p.2 := fun t ht =>
    (TorusPiece.exists_sep x x' hχ (bb t) (fun h => ht (bb.injective (h.trans ht₀.symm)))).imp fun p hp h =>
      hp (mul_left_cancel ((TorusPiece.delta_cell x x' χ₁ χ₂ p.1 p.2).symm.trans h))
  have hc : ∀ (t : Fin N) (p : kˣ × kˣ) y, subQuot (S t.succ) (S t.castSucc) (torusPt k (x + x') p.1 p.2) y =
      (cellChar k (x + 2) x' χ₁ χ₂ (bb t).1 p.1 p.2 : ℂ) • y := fun t p y =>
    smul_of_equiv (hE t).some (CellTorus.cellFunctor_torusPt k (x + 2) x' (x + x') χ₁ χ₂ (bb t)
      (bb t).nonempty_rows.some (bb t).nonempty_cols.some _ _) y
  have E : Nonempty (Representation.Equiv ((subQuot (S t₀.succ) (S t₀.castSucc)).comp (midIncl k (x + x')))
      (prod₂ (detRep (Fin x) χ₁) (detRep (Fin x') χ₂))) :=
    ⟨(TorusPiece.equiv_comp (hE t₀).some (midIncl k (x + x'))).some.trans
      (TorusPiece.mid_equiv x x' h1 h2 (bb t₀) ht₀ (bb t₀).nonempty_rows.some (bb t₀).nonempty_cols.some).some⟩
  have main := TorusPiece.abstract_filt
    (jacU e (parInd (two (stdSum (rfl : x + 2 + x' = x + 2 + x'))) (detPair k (x + 2) x' χ₁ χ₂)))
    (deltaHalf k fun i : Fin 3 => Fin (blk3 (x + x') i)) (midIncl k (x + x')) (TorusPiece.delta_mid (x + x'))
    (prod₂ (detRep (Fin x) χ₁) (detRep (Fin x') χ₂)) N S hS.1 hS.2.1 hS.2.2.1 t₀
    (fun p : kˣ × kˣ => torusPt k (x + x') p.1 p.2) (fun p y => CellTorus.torusPt_central p.1 p.2 y)
    (fun p => (χ₁ * absPow k ((x' : ℂ) / 2)) p.1 * (χ₁ * absPow k (-(x' : ℂ) / 2)) p.2)
    (fun t p => cellChar k (x + 2) x' χ₁ χ₂ (bb t).1 p.1 p.2) hc hsep E
  exact main
