import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.Nm.conjAll :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P Q P' : GL (Fin n) (Qbar l)), (P' : Matrix (Fin n) (Fin n) (Qbar l)) = (Q : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P * Q → (Continuous ρ → Continuous (cj Q ρ)) ∧ (Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → Submodule.span (Qbar l) (Set.range (mat (cj Q ρ))) = ⊤) ∧ (F.IsForm c.O n ρ P → F.IsForm c.O n (cj Q ρ) P') ∧ GDet.ofRep (mat (cj Q ρ)) = GDet.ofRep (mat ρ) ∧ (∀ g, (mat (cj Q ρ) g).charpoly = (mat ρ g).charpoly) ∧ (∀ S, DetQ F c.O ρ P S → DetQ F c.O (cj Q ρ) P' S) ∧ ∀ I ψ z, IsOrdCoc F ρ P I ψ z → IsOrdCoc F (cj Q ρ) P' I ψ fun g => ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * z g * Q := by
  intro l _ n F c ρ P Q P' hP
  have hm : ∀ g, mat (cj Q ρ) g = ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * mat ρ g * Q := by
    intro g
    change ((cj Q ρ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = _
    rw [cj_apply, Units.val_mul, Units.val_mul]; rfl
  have hch : ∀ g, (mat (cj Q ρ) g).charpoly = (mat ρ g).charpoly := by
    intro g
    have := Matrix.charpoly_units_conj Q⁻¹ (mat ρ g)
    rw [hm, ← this, ← Matrix.coe_units_inv, inv_inv]
  have hinv : ∀ w : GL (Fin n) (Qbar l), (((Q⁻¹ * w)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      ((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * Q := by
    intro w; rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
  have hmul : ∀ w : GL (Fin n) (Qbar l), ((Q⁻¹ * w : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * w := fun w => Units.val_mul _ _
  have hD : GDet.ofRep (mat (cj Q ρ)) = GDet.ofRep (mat ρ) :=
    (UpperTheory.V.AlgebraTools.Det.repApi (mat ρ)).2.2.2.2.2.2.2 _ Q fun g => by
      rw [hm, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  have h1 : (Q : Matrix (Fin n) (Fin n) (Qbar l)) * ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = 1 :=
    Units.mul_inv Q
  have h2 : ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * (Q : Matrix (Fin n) (Fin n) (Qbar l)) = 1 :=
    Units.inv_mul Q
  generalize hqi : ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = qi at *
  generalize hq : (Q : Matrix (Fin n) (Fin n) (Qbar l)) = q at *
  have a1 : ∀ X : Matrix (Fin n) (Fin n) (Qbar l), q * (qi * X) = X := fun X => by rw [← mul_assoc, h1, one_mul]
  have a2 : ∀ X : Matrix (Fin n) (Fin n) (Qbar l), qi * (q * X) = X := fun X => by rw [← mul_assoc, h2, one_mul]
  have t1 : ∀ X : Matrix (Fin n) (Fin n) (Qbar l), qiᵀ * (qᵀ * X) = X := fun X => by
    rw [← mul_assoc, ← transpose_mul, h1, transpose_one, one_mul]
  refine ⟨fun h => ?_, fun h => ?_, fun h g => ?_, hD, hch, fun S h z hz hc hp ht => ?_, fun I ψ z h => ?_⟩
  · have : (cj Q ρ : F.G₀ → _) = fun g => Q⁻¹ * ρ g * Q := funext (cj_apply Q ρ)
    rw [this]
    exact (continuous_const.mul h).mul continuous_const
  · have key : ∀ Z ∈ Submodule.span (Qbar l) (Set.range (mat ρ)),
        qi * Z * q ∈ Submodule.span (Qbar l) (Set.range (mat (cj Q ρ))) := by
      intro Z hZ
      induction hZ using Submodule.span_induction with
      | mem x hx => obtain ⟨g, rfl⟩ := hx; exact Submodule.subset_span ⟨g, hm g⟩
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, add_mul]; exact add_mem hx hy
      | smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
    refine eq_top_iff.2 fun Z _ => ?_
    have := key (q * Z * qi) (h ▸ Submodule.mem_top)
    simpa only [mul_assoc, a2, h2, mul_one] using this
  · have := congrArg (fun X => qᵀ * X * q) (h g)
    simp only [mul_smul_comm, smul_mul_assoc] at this
    rw [hm, hm, hP, ← this]
    simp only [transpose_mul, mul_assoc, a1, t1]
  · obtain ⟨Y, hY⟩ := h (fun g => q * z g * qi) ((continuous_const.mul hz).mul continuous_const)
      (fun g g' => by
        simp only [hc g g', hm, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, a1, h1, mul_one])
      (fun g => by
        have := congrArg (fun X => qiᵀ * X * qi) (hp g)
        simpa only [hP, transpose_mul, mul_assoc, t1, h1, mul_one] using this)
      (fun σ hσ k => by
        have := ht σ hσ k
        rw [← map_pow, hm, map_pow, ← mul_assoc, trace_mul_comm] at this
        simpa only [mul_assoc] using this)
    refine ⟨qi * Y * q, fun g => ?_⟩
    have := congrArg (fun X => qi * X * q) (hY g)
    simpa only [hm, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, a1, a2, h2, mul_one] using this
  · refine ⟨(continuous_const.mul h.cont).mul continuous_const, fun g g' => ?_, fun g => ?_, fun u g hg => ?_, fun v => ?_⟩
    · simp only [h.coc g g', hm, mul_add, add_mul, mul_assoc, a1]
    · have := congrArg (fun X => qᵀ * X * q) (h.pol g)
      simpa only [hP, transpose_mul, mul_assoc, t1, a1, mul_neg, neg_mul] using this
    · simp [h.ine u g hg]
    · obtain ⟨w, Y, hw⟩ := h.ord v
      refine ⟨Q⁻¹ * w, qi * Y * q, fun g => ?_⟩
      have e1 : (Q⁻¹ * w)⁻¹ * cj Q ρ (F.φ v g) * (Q⁻¹ * w) = w⁻¹ * ρ (F.φ v g) * w := by
        rw [cj_apply]; group
      have e2 : (((Q⁻¹ * w)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
          (qi * z (F.φ v g) * q - dY F (mat (cj Q ρ)) (qi * Y * q) (F.φ v g)) *
          ((Q⁻¹ * w : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
          ((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
          (z (F.φ v g) - dY F (mat ρ) Y (F.φ v g)) * (w : Matrix (Fin n) (Fin n) (Qbar l)) := by
        simp only [hinv, hmul, dY, hm, mul_sub, sub_mul, mul_assoc, a1]
      rw [e1, e2]
      exact hw g
