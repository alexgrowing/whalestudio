import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.LevelB

noncomputable section

open NumberField Matrix IsDedekindDomain Formalism.UG Formalism.UG.P PI.InHHClassFin
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.InHHClassFin

theorem levelStep : LevelStep := by
  intro I m k B Bi hBB hBB' J' g hg
  classical
  obtain ⟨d1, hd1, h1⟩ := lvB_lat_up (F := I.F) I.L I.L_fg
  obtain ⟨d2, hd2, h2⟩ := lvB_lat_down (F := I.F) I.L I.L_span
  obtain ⟨dc, hdc, hc⟩ := lvB_denom_fam (F := I.F) (E := I.E)
    (fun p : (Fin I.n × (Fin m ⊕ Fin k)) ⊕ ((Fin m ⊕ Fin k) × Fin I.n) => match p with
      | .inl q => inclE (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (B q.1 q.2)
      | .inr q => inclE (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (Bi q.1 q.2))
  have hg0 : ((g : ℕ) : 𝓞 I.F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set D : 𝓞 I.F := (g : 𝓞 I.F) * d2 * dc * dc * d1 with hDdef
  have hD : D ≠ 0 := by
    simp only [hDdef]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hg0 hd2) hdc) hdc) hd1
  set cD : tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) :=
    ⟨levelafC I.E D, levelafC_mem D⟩ with hcD
  set Pr : Subgroup (GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :=
    princ (n := Fin k) (tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F)).subtype
      (Ideal.span {cD}) with hPr
  refine ⟨stdLevel I J' ⊓ Pr.subgroupOf (UPts I.cm.sig J' (FiniteAdeleRing (𝓞 I.F) I.F)),
    inf_le_left, ?_, ?_⟩
  ·
    rw [Subgroup.inf_relIndex_left, stdLevel, Subgroup.relIndex_subgroupOf]
    swap
    · rw [Formalism.UG.Final.LevelAfLStd I.F I.E (Fin k) I.cm.sig J']; exact inf_le_left
    have : Finite (tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) ⧸
        Ideal.span {cD}) := levelaf_finite_quot D hD cD rfl
    have h0 := levelaf_princ_relIndex_ne_zero (n := Fin k)
      (tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F)) (Ideal.span {cD})
    have hle : levelAfL I.cm.sig J' (stdLat (n := Fin k) (A := I.E) (𝓞 I.E)) ≤
        (bc (n := Fin k) (tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E)
          (intAd I.F)).subtype).range := by
      rw [Formalism.UG.Final.LevelAfLStd I.F I.E (Fin k) I.cm.sig J', levelAf, level]
      refine inf_le_right.trans ?_
      rw [Formalism.UG.Final.StabStd _ _ (Fin k) Subtype.val_injective]
      exact le_refl _
    exact fun h => h0 (Subgroup.relIndex_eq_zero_of_le_right hle h)
  · intro y hy h hh
    have hyP : (y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) ∈ Pr :=
      Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hy).2
    set P : Matrix (Fin I.n) (Fin m ⊕ Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) :=
      B.map (inclE (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F)) with hP
    set Q : Matrix (Fin m ⊕ Fin k) (Fin I.n) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) :=
      Bi.map (inclE (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F)) with hQ
    have hPQ : P * Q = 1 := by
      rw [hP, hQ, ← Matrix.map_mul, hBB, Matrix.map_one _ (map_zero _) (map_one _)]
    have hQP : Q * P = 1 := by
      rw [hP, hQ, ← Matrix.map_mul, hBB', Matrix.map_one _ (map_zero _) (map_one _)]
    have hPi : ∀ i j, (levelafC I.E dc • P) i j ∈
        tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) :=
      fun i j => by simpa [P, smul_eq_mul] using hc (.inl (i, j))
    have hQi : ∀ i j, (levelafC I.E dc • Q) i j ∈
        tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) :=
      fun i j => by simpa [Q, smul_eq_mul] using hc (.inr (i, j))
    have hscal : ((cD : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) =
        (g : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) * levelafC I.E d2 * levelafC I.E dc *
          levelafC I.E dc * levelafC I.E d1 := by
      simp only [hcD, hDdef, levelafC_mul, lvB_C_natCast]
    have hgS : (g : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) ∈
        tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F) := natCast_mem _ g
    have hblk : ∀ w : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F), w ∈ Pr →
        ∃ N : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F),
          (∀ i j, N i j ∈ tensInt (F := I.F) (FiniteAdeleRing (𝓞 I.F) I.F) (intOE I.E) (intAd I.F)) ∧
          Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            (w : Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) =
          1 + ((g : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) * levelafC I.E d2 * levelafC I.E dc *
            levelafC I.E dc * levelafC I.E d1) • N := by
      intro w hw
      obtain ⟨N0, hN0, hw0⟩ := lvA_princ_form _ cD w hw
      refine ⟨Matrix.fromBlocks 0 0 0 N0, ?_, ?_⟩
      · intro i j
        rcases i with i | i <;> rcases j with j | j <;> simp [hN0, zero_mem]
      · rw [hw0, ← hscal]
        ext i j
        rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
    have hfm : ((h : GL (Fin I.n) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) =
        P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
          ((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
            Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q := hh
    obtain ⟨N, hN, hu⟩ := hblk _ hyP
    obtain ⟨N', hN', hu'⟩ := hblk _ (Pr.inv_mem hyP)
    have hinv : (P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
          ((((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)))⁻¹ : GL (Fin k) _) :
            Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q) *
        (P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
          ((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
            Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q) = 1 := by
      have e : P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            ((((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)))⁻¹ : GL (Fin k) _) :
              Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q *
          (P * Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            ((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
              Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * Q) =
          P * (Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            ((((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)))⁻¹ : GL (Fin k) _) :
              Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) * (Q * P) *
            Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) 0 0
            ((y : GL (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) :
              Matrix (Fin k) (Fin k) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F))) * Q := by
        simp only [Matrix.mul_assoc]
      rw [e, hQP, Matrix.mul_one, Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
        Units.inv_mul, Matrix.fromBlocks_one, Matrix.mul_one, hPQ]
    refine ⟨?_, ?_⟩
    · show (h : GL (Fin I.n) (I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F)) ∈ stabGL I.Lf
      intro z
      constructor
      · intro hz
        rw [hfm]
        exact lvA_maps _ I.Lf _ _ _ _ hgS h1 h2 P Q hPQ hPi hQi N hN _ hu z hz
      · intro hz
        rw [hfm] at hz
        have := lvA_maps _ I.Lf _ _ _ _ hgS h1 h2 P Q hPQ hPi hQi N' hN' _ hu' _ hz
        rwa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at this
    · intro z hz
      show ∃ w ∈ I.Lf, (I.fmat h - 1) *ᵥ z = (g : I.E ⊗[I.F] FiniteAdeleRing (𝓞 I.F) I.F) • w
      rw [show I.fmat h = _ from hfm]
      exact lvA_key _ I.Lf _ _ _ _ h1 h2 P Q hPQ hPi hQi N hN _ hu z hz

end PI.UnitaryGroupMassFormula.InHHClassFin
