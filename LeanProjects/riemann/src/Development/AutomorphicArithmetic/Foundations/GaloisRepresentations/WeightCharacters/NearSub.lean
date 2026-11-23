import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem entry_mul_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    {A B : Matrix (Fin a) (Fin a) ℂ} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hA : ∀ i j, ‖ι.symm (A i j)‖ ≤ r) (hB : ∀ i j, ‖ι.symm (B i j)‖ ≤ s) (i j : Fin a) :
    ‖ι.symm ((A * B) i j)‖ ≤ r * s := by
  rw [Matrix.mul_apply, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun k _ => ?_
  rw [map_mul, norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) hr

theorem UpperTheory.Gal.Wt.nearSub_of :
    UpperTheory.Gal.Wt.NearSub := by
  intro l _ ι a Γ _ _ _ φ hc hI ε hε
  refine ⟨{ carrier := {g | NearOne ι ε (φ g)}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, ?_, fun g => Iff.rfl⟩
  · intro g h hg hh
    have hg' : NearOne ι ε (φ g) := hg
    have hh' : NearOne ι ε (φ h) := hh
    show NearOne ι ε (φ (g * h))
    intro i j
    have key : ((φ (g * h) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1
        = (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1) * ((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)
          + (((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1) := by
      rw [map_mul, Units.val_mul]
      noncomm_ring
    have e := congrFun (congrFun key i) j
    rw [Matrix.sub_apply] at e
    rw [e, Matrix.add_apply, map_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · have := entry_mul_le ι hε.le zero_le_one
        (A := ((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)
        (B := ((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))
        (fun i j => by rw [Matrix.sub_apply]; exact hg' i j) (fun i j => (hI h i j).1) i j
      exact this.trans_eq (mul_one ε)
    · rw [Matrix.sub_apply]
      exact hh' i j
  · show NearOne ι ε (φ 1)
    intro i j
    rw [map_one, Units.val_one, sub_self, map_zero, norm_zero]
    exact hε.le
  · intro g hg
    have hg' : NearOne ι ε (φ g) := hg
    show NearOne ι ε (φ g⁻¹)
    intro i j
    have key : ((φ g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1
        = -((((φ g)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)
            * (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)) := by
      rw [map_inv, mul_sub, Units.inv_mul, mul_one, neg_sub]
    have e := congrFun (congrFun key i) j
    rw [Matrix.sub_apply] at e
    rw [e, Matrix.neg_apply, map_neg, norm_neg]
    have := entry_mul_le ι zero_le_one hε.le
      (A := (((φ g)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))
      (B := ((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)
      (fun i j => (hI g i j).2) (fun i j => by rw [Matrix.sub_apply]; exact hg' i j) i j
    exact this.trans_eq (one_mul ε)
  · have hset : ({g | NearOne ι ε (φ g)} : Set Γ)
        = ⋂ i, ⋂ j, (fun g => ι.symm (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)) ⁻¹'
            Metric.closedBall (ι.symm ((1 : Matrix (Fin a) (Fin a) ℂ) i j)) ε := by
      ext g
      simp only [Set.mem_setOf_eq, NearOne, map_sub, Set.mem_iInter, Set.mem_preimage,
        Metric.mem_closedBall, dist_eq_norm]
    show IsOpen ({g | NearOne ι ε (φ g)} : Set Γ)
    rw [hset]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (hc i j).isOpen_preimage _ (IsUltrametricDist.isOpen_closedBall _ hε.ne')
