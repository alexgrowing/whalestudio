import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.InV
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CardKerRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdHalf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdKill

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.odCount :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] [Finite X] (D : Dat x.A (plOf G)) (d : ℕ) (dv : L.Vl → ℕ), l ≠ 2 → IsOd h x X D → CohAx G d dv → Finite D.H2LocalConditions ∧ Finite D.Ck2 ∧ Nat.card D.H2LocalConditions ≤ Nat.card D.Sel * (∏ v, Nat.card (H0 (D.Q (inV G v)).ρ)) * Nat.card {f : D.M.X →+ ZMod l // ∀ g m, f (D.M.ρ g m) = PadicInt.toZMod ((G.ε g : ℤ_[l]ˣ) : ℤ_[l]) * f m} := by
  intro l _ L G G0 h n x X _ _ _ D d dv hl hD hC
  obtain ⟨hM, hfixc, hQv⟩ := odHalf l L G G0 h n x X D hl hD
  obtain ⟨ktM, ktQ, ktJ⟩ := odKill l L G G0 h n x X D hD
  set N := Nat.card X ^ (x.a * (n - x.a)) with hN
  have hNpos : 0 < N := pow_pos Nat.card_pos _
  have fM := hC.fin x.A D.M ktM
  have fQ : ∀ w, Finite (H1 (D.Q w).ρ) ∧ Finite (H2 (D.Q w).ρ) := by
    intro w
    cases w with
    | inl v => exact hC.finV v x.A (D.Q (inV G v)) (ktQ _)
    | inr u => exact hC.finU u x.A (D.Q (inU G u)) (ktQ _)
  let dw : (plOf G).ι → ℕ := Sum.elim dv (fun _ => 0)
  let e : (plOf G).ι → ℕ := Sum.elim (fun v => Nat.card (H0 (D.Q (inV G v)).ρ)) (fun _ => 1)
  have hglob : Nat.card (H2 D.M.ρ) * N ^ ∑ w, dw w ≤ Nat.card (H1 D.M.ρ) := by
    obtain ⟨c, hc, hE⟩ := hC.ge
    have E := hE x.A D.M ktM
    have hfix : ∀ i, Nat.card {m // D.M.ρ (c i) m = m} = N := fun i => hfixc (c i) (hc i).1 (hc i).2
    simp only [hfix, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hM] at E
    have hsum : ∑ w, dw w = d := by
      show ∑ w : L.Vl ⊕ L.St, dw w = d
      rw [Fintype.sum_sum_type]
      simp [dw, hC.sum]
    rw [hsum]
    have h0pos : 0 < Nat.card (H0 D.M.ρ) := Nat.card_pos
    have key : Nat.card (H0 D.M.ρ) * Nat.card (H2 D.M.ρ) * N ^ d = Nat.card (H1 D.M.ρ) := by
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hNpos d)
      rw [← E]
      ring
    calc Nat.card (H2 D.M.ρ) * N ^ d ≤ Nat.card (H0 D.M.ρ) * (Nat.card (H2 D.M.ρ) * N ^ d) :=
          Nat.le_mul_of_pos_left _ h0pos
      _ = Nat.card (H1 D.M.ρ) := by rw [← key, mul_assoc]
  have hloc : ∀ w, Nat.card (H1 (D.Q w).ρ) ≤
      Nat.card (H1ur (D.Q w).ρ ((plOf G).J w)) * Nat.card (H2 (D.Q w).ρ) * e w * N ^ dw w := by
    intro w
    cases w with
    | inl v =>
      have E := hC.leV v x.A (D.Q (inV G v)) (ktQ _)
      rw [hQv v] at E
      haveI := (fQ (inV G v)).1
      have hur : 0 < Nat.card (H1ur (D.Q (inV G v)).ρ ((plOf G).J (inV G v))) := Nat.card_pos
      have key : Nat.card (H0 (D.Q (inV G v)).ρ) * Nat.card (H2 (D.Q (inV G v)).ρ) * N ^ dv v
          ≤ Nat.card (H1ur (D.Q (inV G v)).ρ ((plOf G).J (inV G v))) *
            Nat.card (H2 (D.Q (inV G v)).ρ) * Nat.card (H0 (D.Q (inV G v)).ρ) * N ^ dv v := by
        calc _ ≤ Nat.card (H1ur (D.Q (inV G v)).ρ ((plOf G).J (inV G v))) *
              (Nat.card (H0 (D.Q (inV G v)).ρ) * Nat.card (H2 (D.Q (inV G v)).ρ) * N ^ dv v) :=
              Nat.le_mul_of_pos_left _ hur
          _ = _ := by ring
      exact E.le.trans key
    | inr u =>
      have E := hC.leU u x.A (D.Q (inU G u)) (ktQ _)
      have ur := ((hC.ur u) x.A (D.Q (inU G u)) (ktQ _) (ktJ u)).1
      rw [pow_zero, mul_one] at E
      have key : Nat.card (H0 (D.Q (inU G u)).ρ) * Nat.card (H2 (D.Q (inU G u)).ρ)
          ≤ Nat.card (H1ur (D.Q (inU G u)).ρ (L.Ju u)) * Nat.card (H2 (D.Q (inU G u)).ρ) * 1 * N ^ 0 := by
        rw [pow_zero, mul_one, mul_one]
        exact Nat.mul_le_mul_right _ ur
      exact E.le.trans key
  obtain ⟨hfin, hle⟩ := count x.A G.Γ (plOf G) D N dw e hNpos fM.1 fM.2 fQ hglob hloc
  have hfin2 : Finite D.Ck2 := by
    haveI : Fintype (plOf G).ι := (plOf G).fin
    haveI : ∀ w, Finite (H2 (D.Q w).ρ) := fun w => (fQ w).2
    exact Finite.of_surjective _ (Submodule.mkQ_surjective _)
  refine ⟨hfin, hfin2, ?_⟩
  have hck := hC.ck x.A D ktM
  have hprod : ∏ w, e w = ∏ v, Nat.card (H0 (D.Q (inV G v)).ρ) := by
    show ∏ w : L.Vl ⊕ L.St, e w = _
    rw [Fintype.prod_sum_type]
    simp [e]
  calc Nat.card D.H2LocalConditions ≤ (Nat.card D.Sel * ∏ w, e w) * Nat.card D.Ck2 := hle
    _ ≤ _ := by rw [hprod]; exact Nat.mul_le_mul_left _ hck
