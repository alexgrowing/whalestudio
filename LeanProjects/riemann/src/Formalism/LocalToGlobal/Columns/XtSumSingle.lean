import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Std

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem xt_sum_single {a b : ℕ} (z : HomE E a b) (v : Sp E a) : z v = ∑ j, v j • z (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (Pi.single j (v j) : Sp E a) = v j • Pi.single j 1 := by rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, map_smul]

theorem xt_map_std {a b : ℕ} (z : HomE E a b) (hz : ∀ j l, IntAt P (z (Pi.single j 1) l)) {v : Sp E a} (hv : v ∈ stdAt E a P) :
    z v ∈ stdAt E b P := by
  rw [ciMem_stdAt] at hv ⊢
  intro l
  rw [xt_sum_single z v, Finset.sum_apply]
  exact ciIntAt_sum _ _ fun j _ => by
    rw [Pi.smul_apply, smul_eq_mul]
    exact (hv j).mul (hz j l)

end Std

section Law

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def TopLawG (m2 : ℕ) (Λm : LevFam X.E X.K (R.N (m2 + 1 + 1)) Pr.vGs) (b : L.β (m2 + 1)) : Prop :=
  ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) (h : ↥(L.levG (m2 + 1) b ⟨w.1, hw⟩).H) (h' : ↥(Λm ⟨w.1, hw⟩).H)
    (κ : ↥(GLint X.E (R.N (m2 + 1)) w.1)) (κ' : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1)),
    (∀ x ∈ stdAt X.E (R.N (m2 + 1)) w.1, redV w.1 (κ.1 x) = (h.1⁻¹).1.mulVec (redV w.1 x)) →
    (∀ x ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1, redV w.1 (κ'.1 x) = (h'.1⁻¹).1.mulVec (redV w.1 x)) →
    ∀ y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1)), (∀ j l, IntAt w.1 (y (Pi.single j 1) l)) →
      rhoS Ch sel mu (m2 + 1) w (LinearEquiv.det κ.1 : X.Eˣ) * rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) *
          PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ
            (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) =
        (((Λm ⟨w.1, hw⟩).lam h' : X.Kˣ) : X.K) * ((((L.levG (m2 + 1) b ⟨w.1, hw⟩).lam h)⁻¹ : X.Kˣ) : X.K) *
          PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) w.1 (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ
            LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))

def LastRow {j : ℕ} (Λm : LevFam X.E X.K (R.N j) Pr.vGs) : Prop :=
  ∀ (w : Pr.vGs), ∀ h' ∈ (Λm w).H, ∀ l : Fin (R.N j),
    (h'.1 : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)) ⟨R.N j - 1, xt_last_lt R j⟩ l = if l.1 = R.N j - 1 then 1 else 0

variable {Ch sel mu cst L}

theorem topDat_law (hc : cst.Ok) {m2 : ℕ} (hn : TopNum R (m2 + 1)) {Λm : LevFam X.E X.K (R.N (m2 + 1 + 1)) Pr.vGs} {b : L.β (m2 + 1)}
    (hLaw : TopLawG Ch sel mu cst L m2 Λm b) (hRow : LastRow Λm)
    (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) (h : ↥(L.levG (m2 + 1) b ⟨w.1, hw⟩).H) (h' : ↥(Λm ⟨w.1, hw⟩).H)
    (κ : ↥(GLint X.E (R.N (m2 + 1)) w.1)) (κ' : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1))
    (hκ : ∀ x ∈ stdAt X.E (R.N (m2 + 1)) w.1, redV w.1 (κ.1 x) = (h.1⁻¹).1.mulVec (redV w.1 x))
    (hκ' : ∀ x ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1, redV w.1 (κ'.1 x) = (h'.1⁻¹).1.mulVec (redV w.1 x))
    (hu : ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2)
    (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ y₂ : Sp X.E (R.N (m2 + 1))) (hδ : κ.1 y₁ - y₂ ∈ stdAt X.E (R.N (m2 + 1)) w.1)
    (hq : ((qOf w.1 : ℕ) : X.E) • y₂ ∈ stdAt X.E (R.N (m2 + 1)) w.1) :
    rhoS Ch sel mu (m2 + 1) w (LinearEquiv.det κ.1 : X.Eˣ) * rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) *
        topDat Ch sel mu cst (m2 + 1) w (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) y₁ =
      (((Λm ⟨w.1, hw⟩).lam h' : X.Kˣ) : X.K) * ((((L.levG (m2 + 1) b ⟨w.1, hw⟩).lam h)⁻¹ : X.Kˣ) : X.K) *
        topDat Ch sel mu cst (m2 + 1) w y y₂ := by
  have hk : ∀ v, κ.1 v ∈ stdAt X.E (R.N (m2 + 1)) w.1 ↔ v ∈ stdAt X.E (R.N (m2 + 1)) w.1 := κ.2
  have hk' : ∀ v, κ'.1 v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 ↔ v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 := κ'.2
  by_cases hint : ∀ j l, IntAt w.1 (y (Pi.single j 1) l)
  ·
    have hF : ftY sel mu cst w (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap)) y₁ =
        ftY sel mu cst w (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y₂ := by
      have e1 : atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) =
          (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.1.symm.toLinearMap ∘ₗ y) ∘ₗ κ.1.toLinearMap := rfl
      rw [e1, ftY_move2 sel mu cst hc w hw κ _ y₂ y₁ hδ hq]
      set ζ : Sp X.E (R.N (m2 + 1)) →ₗ[X.E] X.E :=
        atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.1.symm.toLinearMap ∘ₗ y - atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y with hζdef
      have e2 : atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ κ'.1.symm.toLinearMap ∘ₗ y =
          atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y + ζ := by rw [hζdef]; abel

      have hζq : ∀ i, IntAt w.1 (ζ (Pi.single i 1) / (qOf w.1 : X.E)) := by
        intro i
        set v := y (Pi.single i 1) with hv
        have hvs : v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 := (ciMem_stdAt _ _).2 (hint i)
        have hvs' : κ'.1.symm v ∈ stdAt X.E (R.N (m2 + 1 + 1)) w.1 := (hk' _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hvs)
        have h1 := hκ' _ hvs'
        rw [LinearEquiv.apply_symm_apply] at h1
        have h2 : redV w.1 (κ'.1.symm v) = h'.1.1.mulVec (redV w.1 v) := by
          rw [h1, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
        have h3 : redP w.1 (κ'.1.symm v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩) = redP w.1 (v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩) := by
          have h20 := congrFun h2 ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩
          have e : (h'.1.1.mulVec (redV w.1 v)) ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ = redV w.1 v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ := by
            show ∑ l, h'.1.1 ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ l * redV w.1 v l = _
            rw [Finset.sum_eq_single (⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ : Fin (R.N (m2 + 1 + 1)))]
            · rw [hRow ⟨w.1, hw⟩ h'.1 h'.2 ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩, if_pos rfl, one_mul]
            · intro l _ hl
              rw [hRow ⟨w.1, hw⟩ h'.1 h'.2 l, if_neg (fun hh => hl (Fin.ext hh)), zero_mul]
            · intro hh
              exact absurd (Finset.mem_univ _) hh
          exact h20.trans e
        have ha := (ciMem_stdAt _ _).1 hvs' ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩
        have hb := (ciMem_stdAt _ _).1 hvs ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩
        have e3 : ζ (Pi.single i 1) = κ'.1.symm v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ - v ⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ := by
          rw [hζdef, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, xt_atNL, xt_atNL]
          rfl
        rw [e3]
        exact ciIntAt_div (ciQ_mem w.1) hu (ciIntAt_sub ha hb) (by rw [redP_sub ha hb, h3, sub_self])
      have hq0 : (qOf w.1 : X.E) ≠ 0 := ciQ_ne_zero hu
      have hζ : ∀ i, IntAt w.1 (ζ (Pi.single i 1)) := fun i => by
        have := (ciIntAt_q (q := qOf w.1)).mul (hζq i)
        rwa [mul_div_cancel₀ _ hq0] at this
      have hζy : IntAt w.1 (ζ y₂) := by
        have e4 : ζ y₂ = ∑ j, y₂ j * ζ (Pi.single j 1) := by
          conv_lhs => rw [← Finset.univ_sum_single y₂]
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          have : (Pi.single j (y₂ j) : Sp X.E (R.N (m2 + 1))) = y₂ j • Pi.single j 1 := by rw [← Pi.single_smul, smul_eq_mul, mul_one]
          rw [this, map_smul, smul_eq_mul]
        rw [e4]
        refine ciIntAt_sum _ _ fun j _ => ?_
        have h1 := (ciMem_stdAt _ _).1 hq j
        rw [Pi.smul_apply, smul_eq_mul] at h1
        have h2 := h1.mul (hζq j)
        have e5 : ((qOf w.1 : ℕ) : X.E) * y₂ j * (ζ (Pi.single j 1) / (qOf w.1 : X.E)) = y₂ j * ζ (Pi.single j 1) := by
          field_simp
        rwa [e5] at h2
      rw [e2]
      exact fourierTwist_add_integral sel mu cst hc w hw _ ζ y₂ hζ hζy hq
    unfold topDat
    rw [hF, ← mul_assoc, hLaw w hw h h' κ κ' hκ hκ' y hint, mul_assoc]
  ·
    have r0 : topDat Ch sel mu cst (m2 + 1) w y y₂ = 0 := by
      by_contra hne
      exact hint fun j l => topDat_int Ch sel mu cst hn w hw y y₂ hne j l
    have l0 : topDat Ch sel mu cst (m2 + 1) w (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) y₁ = 0 := by
      by_contra hne
      have hz := fun j l => topDat_int Ch sel mu cst hn w hw _ y₁ hne j l
      refine hint fun j l => ?_
      have h1 : κ.1.symm (Pi.single j 1) ∈ stdAt X.E (R.N (m2 + 1)) w.1 :=
        (hk _).1 (by rw [LinearEquiv.apply_symm_apply]; exact ciSingle_mem j)
      have h2 := xt_map_std _ hz h1
      have h3 : (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) (κ.1.symm (Pi.single j 1)) = κ'.1.symm (y (Pi.single j 1)) := by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [h3] at h2
      have h4 := (hk' _).2 h2
      rw [LinearEquiv.apply_symm_apply] at h4
      exact (ciMem_stdAt _ _).1 h4 l
    rw [r0, l0, mul_zero, mul_zero]

end Law

end Formalism.L2.Col
