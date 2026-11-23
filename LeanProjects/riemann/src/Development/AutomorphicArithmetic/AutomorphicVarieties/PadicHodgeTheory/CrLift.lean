import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsEps
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

private theorem map_ofGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (h : GL (Fin 3) R) :
    GG.map f (GG.ofGL h) = GG.ofGL (Matrix.GeneralLinearGroup.map f h) := rfl

private theorem map_conjBy {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (h : GL (Fin 3) R)
    (r : G →* GG 3 R) :
    (GG.map f).comp (conjBy h r) = conjBy (Matrix.GeneralLinearGroup.map f h) ((GG.map f).comp r) := by
  refine MonoidHom.ext fun g => ?_
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
    map_ofGL]

private theorem lift_lower {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (n' : GL (Fin 3) S) (hn : ∀ a b, 0 ≤ wt a b → ((n' : Matrix (Fin 3) (Fin 3) S) - 1) a b = 0) :
    ∃ n : GL (Fin 3) R, (∀ a b, 0 ≤ wt a b → ((n : Matrix (Fin 3) (Fin 3) R) - 1) a b = 0) ∧
      Matrix.GeneralLinearGroup.map f n = n' := by
  have hX : ∀ a b, ∃ x : R, (0 ≤ wt a b → x = 0) ∧ f x = ((n' : Matrix (Fin 3) (Fin 3) S) - 1) a b := by
    intro a b
    by_cases h : 0 ≤ wt a b
    · exact ⟨0, fun _ => rfl, by rw [map_zero, hn a b h]⟩
    · obtain ⟨x, hx⟩ := hf (((n' : Matrix (Fin 3) (Fin 3) S) - 1) a b)
      exact ⟨x, fun h' => absurd h' h, hx⟩
  choose X h0 hX using hX
  have hd : (Matrix.of X + 1).det = 1 := by
    have h00 := h0 0 0 (by decide)
    have h01 := h0 0 1 (by decide)
    have h02 := h0 0 2 (by decide)
    have h11 := h0 1 1 (by decide)
    have h12 := h0 1 2 (by decide)
    have h22 := h0 2 2 (by decide)
    simp [Matrix.det_fin_three, h00, h01, h02, h11, h12, h22]
  refine ⟨Matrix.GeneralLinearGroup.mk'' (Matrix.of X + 1) (by rw [hd]; exact isUnit_one), fun a b h => ?_, ?_⟩
  · change (Matrix.of X + 1 - 1) a b = 0
    rw [add_sub_cancel_right]
    exact h0 a b h
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change f ((Matrix.of X + 1) a b) = _
    rw [Matrix.add_apply, map_add, Matrix.of_apply, hX, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem UpperTheory.V.Loc.crLift :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ r' : GQ l →* GG 3 B', D.InDcr (π' : B' →+* E) r' → ∃ r : GQ l →* GG 3 B, D.InDcr (π : B →+* E) r ∧ (GG.map (p : B →+* B')).comp r = r' := by
  intro hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hc r' hr'
  obtain ⟨u', n', hu', hn1, hn2, rfl⟩ := (ordEq hP D E B' π' hπ' r').1 hr'
  obtain ⟨u, hu, rfl⟩ := triLift hP D E B π hπ B' π' hπ' p hp hc u' hu'
  obtain ⟨n, hn, rfl⟩ := lift_lower (p : B →+* B') hp n' hn2
  refine ⟨conjBy n u, (ordEq hP D E B π hπ _).2 ⟨u, n, hu, fun a b => ?_, hn, rfl⟩, map_conjBy _ n u⟩
  have h := hn1 a b
  rw [RingHom.mem_ker] at h ⊢
  rw [← h, ← hc, Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
  change π' (p _) = π' (p _ - _)
  congr 1
  split_ifs <;> simp
