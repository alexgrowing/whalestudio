import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SChain

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

namespace UpperTheory.V.ZK

section

variable {k : Type} [Field k] {A : Type} [CommRing A] {m : ℕ} {θ : Fam k A (m + 1)} {G : Type} [Group G]

private theorem cyc_cm {H : Type} [Group H] (f : G →* H) {z : Ch A G (m + 1)} (hz : Cyc z) :
    Cyc (cm A f (m + 1) z) := by
  unfold Cyc at *
  rw [(sChain A).2.1, hz, map_zero]

private theorem bd_cm {H : Type} [Group H] (f : G →* H) {z : Ch A G (m + 1)} (hz : Bd z) :
    Bd (cm A f (m + 1) z) := by
  obtain ⟨y, rfl⟩ := hz
  exact ⟨cm A f _ y, (sChain A).2.1 _ _ _ _ _⟩

private theorem val_iso (h : IsAdd θ) {V W : Type} [AddCommGroup V] [Module k V] [Finite V] [AddCommGroup W]
    [Module k W] [Finite W] (σ : G →* (W ≃ₗ[k] W)) (ρ : G →* (V ≃ₗ[k] V)) (φ : W ≃ₗ[k] V)
    (hφ : ∀ g w, φ (σ g w) = ρ g (φ w)) {z : Ch A G (m + 1)} (hz : Cyc z) :
    θ W (cm A σ (m + 1) z) = θ V (cm A ρ (m + 1) z) := by
  have e : ρ = (cj φ).comp σ := by
    ext g v
    simp [cj, hφ]
  rw [e, (sChain A).2.2.1, h.iso _ _ φ _ (cyc_cm σ hz)]

private theorem val_one (h : IsAdd θ) {V : Type} [AddCommGroup V] [Module k V] [Finite V]
    {z : Ch A G (m + 1)} (hz : Cyc z) : θ V (cm A (1 : G →* (V ≃ₗ[k] V)) (m + 1) z) = 0 := by
  have h1 : (1 : G →* (V ≃ₗ[k] V)) = (1 : Unit →* (V ≃ₗ[k] V)).comp (1 : G →* Unit) := by
    ext g v
    rfl
  rw [h1, (sChain A).2.2.1 G Unit _ (1 : G →* Unit) (1 : Unit →* (V ≃ₗ[k] V)) (m + 1) z]
  apply h.bdry
  apply bd_cm
  exact (sChain A).2.2.2.2 Unit m _ (cyc_cm _ hz)

private def piRep {V : Type} [AddCommGroup V] [Module k V] (ρ : G →* (V ≃ₗ[k] V)) (d : ℕ) :
    G →* ((Fin d → V) ≃ₗ[k] (Fin d → V)) where
  toFun g := LinearEquiv.piCongrRight fun _ => ρ g
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

private theorem val_pi (h : IsAdd θ) {V : Type} [AddCommGroup V] [Module k V] [Finite V] (ρ : G →* (V ≃ₗ[k] V))
    {z : Ch A G (m + 1)} (hz : Cyc z) (d : ℕ) :
    θ (Fin d → V) (cm A (piRep ρ d) (m + 1) z) = (d : A) • θ V (cm A ρ (m + 1) z) := by
  induction d with
  | zero =>
    have h0 : piRep ρ 0 = 1 := by
      ext g f i
      exact i.elim0
    rw [h0, val_one h hz]
    simp
  | succ d ih =>
    let φ : (Fin (d + 1) → V) ≃ₗ[k] V × (Fin d → V) :=
      { toFun := fun f => (f 0, Fin.tail f)
        invFun := fun p => Fin.cons p.1 p.2
        map_add' := fun f g => rfl
        map_smul' := fun c f => rfl
        left_inv := fun f => Fin.cons_self_tail f
        right_inv := fun p => by simp }
    have hφ : ∀ g w, φ (piRep ρ (d + 1) g w) = sumRep ρ (piRep ρ d) g (φ w) := by
      intro g w
      rfl
    rw [val_iso h (piRep ρ (d + 1)) (sumRep ρ (piRep ρ d)) φ hφ hz,
      h.add G V (Fin d → V) ρ (piRep ρ d) z hz, ih]
    push_cast
    rw [add_smul, one_smul, add_comm]

end

private theorem red_apply {k : Type} [Field k] {R : Type} [CommRing R] (r : R →+* k) (n : ℕ) (g : GL (Fin n) R)
    (v : Fin n → k) (i : Fin n) :
    red r n g v i = ∑ j, r ((g : Matrix (Fin n) (Fin n) R) i j) * v j := by
  simp [red, Matrix.mulVec, dotProduct]

end UpperTheory.V.ZK

theorem UpperTheory.V.ZK.sPhi :
    UpperTheory.V.ZK.SPhi := by
  intro k _ _ A _ m θ hθ R _ r
  have hcomp : ∀ {n n' : ℕ} (f : GL (Fin n) R →* GL (Fin n') R) (z : Ch A (GL (Fin n) R) (m + 1)),
      cm A (red r n') (m + 1) (cm A f (m + 1) z) = cm A ((red r n').comp f) (m + 1) z :=
    fun f z => ((sChain A).2.2.1 _ _ _ f (red r _) (m + 1) z).symm
  refine ⟨fun n z hz => ?_, fun n n' hn z hz => ?_, fun d n z hz => ?_⟩
  · exact hθ.bdry _ _ (bd_cm _ hz)
  · simp only [LinearMap.comp_apply]
    rw [hcomp]
    let φ : (Fin n' → k) ≃ₗ[k] (Fin n → k) × (Fin (n' - n) → k) :=
      { toFun := fun f => (fun i => f (Fin.castLE hn i), fun j => f ⟨n + j, by omega⟩)
        invFun := fun p i => if hi : (i : ℕ) < n then p.1 ⟨i, hi⟩ else p.2 ⟨i - n, by omega⟩
        map_add' := fun f g => rfl
        map_smul' := fun c f => rfl
        left_inv := fun f => by
          funext i
          by_cases hi : (i : ℕ) < n
          · simp [hi]
          · simp only [hi, dite_false]
            congr 1
            ext
            simp
            omega
        right_inv := fun p => by
          refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
          · simp
          · simp }
    have hφ : ∀ g w, φ (((red r n').comp (stab R n n' hn)) g w) =
        sumRep (red r n) (1 : GL (Fin n) R →* ((Fin (n' - n) → k) ≃ₗ[k] (Fin (n' - n) → k))) g (φ w) := by
      intro g w
      refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
      · simp [φ, sumRep, red_apply, stab_apply]
        symm
        refine Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ _ ?_ ?_
        · intro x hx
          have hxn : ¬ (x : ℕ) < n := fun h => hx ⟨⟨x, h⟩, Fin.ext rfl⟩
          have hne : Fin.castLE hn i ≠ x := fun h => hxn (h ▸ i.isLt)
          simp [hxn, hne]
        · intro j
          simp
      · simp [φ, sumRep, red_apply, stab_apply]
    rw [val_iso hθ _ _ φ hφ hz, hθ.add _ _ _ _ _ z hz, val_one hθ hz, add_zero]
  · simp only [LinearMap.comp_apply]
    rw [hcomp, ← val_pi hθ (red r n) hz d]
    have h1 : ∀ x : Fin d × Fin n, (finProdFinEquiv x).divNat = x.1 ∧ (finProdFinEquiv x).modNat = x.2 :=
      fun x => by
        have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) x.2.isLt
        refine ⟨Fin.ext ?_, Fin.ext ?_⟩
        · simp only [finProdFinEquiv, Fin.divNat, Equiv.coe_fn_mk]
          rw [Nat.add_mul_div_left _ _ hn0, Nat.div_eq_of_lt x.2.isLt, zero_add]
        · simp [finProdFinEquiv, Fin.modNat, Nat.mod_eq_of_lt]
    let φ : (Fin d → Fin n → k) ≃ₗ[k] (Fin (d * n) → k) :=
      { toFun := fun f p => f (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
        invFun := fun g i a => g (finProdFinEquiv (i, a))
        map_add' := fun f g => rfl
        map_smul' := fun c f => rfl
        left_inv := fun f => by
          funext i a
          simp
        right_inv := fun g => by
          funext p
          show g (finProdFinEquiv ((finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2)) = g p
          rw [Prod.mk.eta, Equiv.apply_symm_apply] }
    have hφ : ∀ g w, φ (piRep (red r n) d g w) = ((red r (d * n)).comp (psi R d n)) g (φ w) := by
      intro g w
      funext p
      obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective p
      simp [φ, piRep, red_apply, psi, h1]
      rw [← finProdFinEquiv.sum_comp]
      simp [h1, Fintype.sum_prod_type, Matrix.one_apply]
      done
    exact (val_iso hθ _ _ φ hφ hz).symm
