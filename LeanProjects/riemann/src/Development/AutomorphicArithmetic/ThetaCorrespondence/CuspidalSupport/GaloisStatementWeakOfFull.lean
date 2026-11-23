import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

noncomputable section

namespace UpperTheory.Lit.Car

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def IneAb {w : PlE H} (y : A.LP w) : Prop :=
  ∀ σ ∈ ⁅Ine (F := H.E) (N.plOm.1 w), Ine (F := H.E) (N.plOm.1 w)⁆, A.inePol y σ = (X - 1) ^ A.lpDim y

structure RelA {w : PlE H} (x y : A.LP w) : Prop where
  dim : A.lpDim x = A.lpDim y
  mono : A.mono0 y → A.mono0 x
  ine : IneAb N A y → ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol x σ = A.inePol y σ

structure Cusp {w : PlE H} (x y : A.LP w) : Prop where
  rel : RelA N A x y
  temp : Odd (A.lpDim y) → ∀ s : ℝ, A.tempered (A.lpTw y s) → A.tempered (A.lpTw x s)
  one : A.lpDim y = 1 → x = y

variable {N A}

theorem RelA.refl {w : PlE H} (x : A.LP w) : RelA N A x x := ⟨rfl, id, fun _ _ _ => rfl⟩

theorem RelA.of_eq {w : PlE H} {x y : A.LP w} (e : x = y) : RelA N A x y := e ▸ RelA.refl x

theorem Cusp.of_eq {w : PlE H} {x y : A.LP w} (e : x = y) : Cusp N A x y :=
  ⟨RelA.of_eq e, fun _ _ h => e ▸ h, fun _ => e⟩

theorem comm_le_ine (w : PlE H) :
    ⁅Ine (F := H.E) (N.plOm.1 w), Ine (F := H.E) (N.plOm.1 w)⁆ ≤ Ine (F := H.E) (N.plOm.1 w) :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem RelA.unr {w : PlE H} {x y : A.LP w} (h : RelA N A x y) (hy : A.unr y) : A.unr x := by
  obtain ⟨h0, h1⟩ := (A.unr_iff_ine y).1 hy
  refine (A.unr_iff_ine x).2 ⟨h.mono h0, fun σ hσ => ?_⟩
  rw [h.ine (fun τ hτ => h1 τ (comm_le_ine w hτ)) σ hσ, h1 σ hσ, h.dim]

theorem RelA.tw {w : PlE H} {x y : A.LP w} (h : RelA N A x y) (s : ℝ) : RelA N A (A.lpTw x s) (A.lpTw y s) := by
  refine ⟨by rw [A.lpDim_tw, A.lpDim_tw, h.dim], by rw [A.monomial_twist_iff, A.monomial_twist_iff]; exact h.mono, fun hy σ hσ => ?_⟩
  rw [A.inePol_tw _ _ σ hσ, A.inePol_tw _ _ σ hσ]
  refine h.ine (fun τ hτ => ?_) σ hσ
  have := hy τ hτ
  rwa [A.inePol_tw _ _ τ (comm_le_ine w hτ), A.lpDim_tw] at this

theorem eq_pow_of_mul {p q : ℂ[X]} (hp : p.Monic) {n : ℕ} (h : p * q = (X - 1) ^ n) : p = (X - 1) ^ p.natDegree := by
  have hirr : Prime (X - C (1 : ℂ)) := prime_X_sub_C 1
  have hd : p ∣ (X - C (1 : ℂ)) ^ n := ⟨q, by simpa using h.symm⟩
  obtain ⟨k, -, hk⟩ := (dvd_prime_pow hirr n).1 hd
  have e : p = (X - C (1 : ℂ)) ^ k := eq_of_monic_of_associated hp ((monic_X_sub_C 1).pow k) hk
  have : p.natDegree = k := by rw [e, natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [this, e]; simp

theorem RelA.sum (hLP : TieLP N A) {w : PlE H} {x y x' y' : A.LP w} (h : RelA N A x y) (h' : RelA N A x' y') :
    RelA N A (A.lpSum x x') (A.lpSum y y') := by
  refine ⟨by rw [A.lpDim_sum, A.lpDim_sum, h.dim, h'.dim], by rw [A.monomial_sum_iff, A.monomial_sum_iff]; exact fun k => ⟨h.mono k.1, h'.mono k.2⟩,
    fun hy σ hσ => ?_⟩
  have d1 : A.lpDim (A.lpUnr w {1}) = 1 := by rw [(A.lpUnr_spec w {1} (by simp)).2.2]; simp
  have mon : ∀ (a : A.LP w), ∀ τ ∈ Ine (F := H.E) (N.plOm.1 w), (A.inePol a τ).Monic ∧ (A.inePol a τ).natDegree = A.lpDim a :=
    fun a τ hτ => ((hLP w a a _ _ 0 d1 d1).2.2.2.2.2 τ hτ).1
  rw [A.inePol_sum, A.inePol_sum, h.ine (fun τ hτ => ?_) σ hσ, h'.ine (fun τ hτ => ?_) σ hσ]
  · have e := hy τ hτ
    rw [A.inePol_sum, mul_comm] at e
    have m := mon y' τ (comm_le_ine w hτ)
    rw [eq_pow_of_mul m.1 e, m.2]
  · have e := hy τ hτ
    rw [A.inePol_sum] at e
    have m := mon y τ (comm_le_ine w hτ)
    rw [eq_pow_of_mul m.1 e, m.2]

theorem inePol_char_unr (hLP : TieLP N A) {w : PlE H} (a c : A.LP w) (hc : A.lpDim c = 1) (hu : A.unr c) :
    ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.lpChar a c) σ = A.inePol a σ := fun σ hσ => by
  have e : A.inePol c σ = X - C 1 := by rw [((A.unr_iff_ine c).1 hu).2 σ hσ, hc]; simp
  rw [((hLP w a a c c 0 hc hc).2.2.2.2.2 σ hσ).2 1 e, scaleRoots_one]

theorem RelA.char (hLP : TieLP N A) {w : PlE H} {x y : A.LP w} (h : RelA N A x y) (c : A.LP w) (hc : A.lpDim c = 1)
    (hu : A.unr c) : RelA N A (A.lpChar x c) (A.lpChar y c) := by
  refine ⟨by rw [A.lpDim_char _ _ hc, A.lpDim_char _ _ hc, h.dim], by rw [A.monomial_char_iff _ _ hc, A.monomial_char_iff _ _ hc]; exact h.mono,
    fun hy σ hσ => ?_⟩
  rw [inePol_char_unr hLP _ _ hc hu σ hσ, inePol_char_unr hLP _ _ hc hu σ hσ]
  refine h.ine (fun τ hτ => ?_) σ hσ
  have := hy τ hτ
  rwa [inePol_char_unr hLP _ _ hc hu τ (comm_le_ine w hτ), A.lpDim_char _ _ hc] at this

variable (N A)

def GaloisRepresentationsWeak : Prop :=
  ∀ i, (∀ a, 1 ≤ a → ∀ π : A.CG a, A.csd π → A.ralg π →
      ∃ ρ : G H.E N.Om →* GL (Fin a) (Qbar (N.l i)),
        Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) ∧
        IsSSRep ρ ∧
        (∀ w, w ∉ placesOver H.E (N.l i) →
          A.wdOf i ρ w = A.lpTw (A.locG π w) ((1 - (a : ℝ)) / 2) ∧ A.tempered (A.locG π w)) ∧
        (∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ w ∧
          (∀ τ, InducesW N i τ w → A.jumpsW i ρ τ = A.jumpsInf i π τ) ∧
          Cusp N A (A.wdOf i ρ w) (A.lpTw (A.locG π w) ((1 - (a : ℝ)) / 2)))) ∧
    (∀ a (π : A.CG a), A.ralg π → ∃ w₀ : ℂ, ∀ τ : H.E →+* ℂ,
      A.infG π (τ.comp (H.conj : H.E ≃ₐ[ℚ] H.E).toRingEquiv.toRingHom) = (A.infG π τ).map (w₀ - ·)) ∧
    (∀ (χ : A.CG 1) (s : ℝ), (∀ τ : H.E →+* ℂ, ∀ z ∈ A.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ)) →
      ∃ ρ : G H.E N.Om →* GL (Fin 1) (Qbar (N.l i)), ContQ N i ρ ∧
        (∀ w, w ∉ placesOver H.E (N.l i) → A.wdOf i ρ w = A.lpTw (A.locG χ w) s) ∧
        ∀ w ∈ placesOver H.E (N.l i), A.IsdRW i ρ w ∧ A.wdOf i ρ w = A.lpTw (A.locG χ w) s ∧
          ∀ τ, InducesW N i τ w → (A.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) =
            (A.infG χ ((A.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (s : ℂ))))

theorem galois_statement_weak_of_full (h : exists_galois_rep_local_global_compatible N A) : GaloisRepresentationsWeak N A := fun i =>
  ⟨fun a ha π hc hr => by
    obtain ⟨ρ, c, s, o, u⟩ := (h i).1 a ha π hc hr
    exact ⟨ρ, c, s, o, fun w hw => ⟨(u w hw).1, (u w hw).2.1, Cusp.of_eq (u w hw).2.2⟩⟩, (h i).2⟩

end UpperTheory.Lit.Car
