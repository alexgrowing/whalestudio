import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensIdxD

noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing

namespace IdxHW

section Comap

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)

theorem val_mul_lt {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (hy : Valued.v y < 1) :
    Valued.v (x * y) < 1 := by
  rw [map_mul]
  have hx' : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hx
  exact lt_of_le_of_lt (mul_le_of_le_one_left' hx') hy

theorem comap_eq (k0 k1 : Fin 2) (hk : k0 ≠ k1) (ρ : F)
    (hC : ∀ k l, algebraMap F (Fv F v) (Cmat b σ k l) ∈ v.adicCompletionIntegers F)
    (hρ : algebraMap F (Fv F v) ρ ∈ v.adicCompletionIntegers F)
    (hfix : ∀ x : Fin 2 → Fv F v,
      Matrix.mulVec ((Cmat b σ).map (algebraMap F (Fv F v))) x = x →
        x k1 = algebraMap F (Fv F v) ρ * x k0) :
    (hF b v σ a 0).addSubgroupOf (hermO b v σ a) =
      (AddSubgroup.pi Set.univ fun _ : Fin a × Fin a =>
        (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup).comap (psi b v σ a k0) := by
  rw [← ker_redH]
  ext S
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_comap, AddSubgroup.mem_pi]
  have key : redH b v σ a S = 0 ↔ ∀ i j k, Valued.v (crdS b v σ a S i j k) < 1 := by
    constructor
    · intro h i j k
      have h1 : residue _ (⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩ :
          v.adicCompletionIntegers F) = 0 := congrFun (congrFun (congrFun h i) j) k
      have h2 := (ReciprocityTheory.Aut.mem_maxIdeal_iff v _).1 ((residue_eq_zero_iff _).1 h1)
      exact h2
    · intro h
      funext i j k
      have h3 := res_of_val v ⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩ (h i j k)
      exact h3
  rw [key]
  set Sm : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) :=
    ((S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) with hSm
  have hps : ∀ q, psi b v σ a k0 S q ∈ (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup ↔
      Valued.v ((psi b v σ a k0 S q : v.adicCompletionIntegers F) : Fv F v) < 1 :=
    fun q => ReciprocityTheory.Aut.mem_maxIdeal_iff v _
  constructor
  · intro h q _
    rw [hps]
    obtain ⟨i, j⟩ := q
    rcases lt_trichotomy i j with hij | hij | hij
    · simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_pos hij]
      exact h i j 0
    · subst hij
      simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lt_irrefl, if_false]
      exact h i i k0
    · simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_neg (not_lt.2 hij.le), if_pos hij]
      exact h j i 1
  · intro h
    have h' : ∀ q, Valued.v ((psi b v σ a k0 S q : v.adicCompletionIntegers F) : Fv F v) < 1 :=
      fun q => (hps q).1 (h q (Set.mem_univ q))
    have hup : ∀ i j, i < j → ∀ k, Valued.v (crdS b v σ a S i j k) < 1 := by
      intro i j hij k
      fin_cases k
      · have := h' (i, j)
        simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_pos hij] at this
        exact this
      · have := h' (j, i)
        simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_neg (not_lt.2 hij.le),
          if_pos hij] at this
        exact this
    intro i j k
    rcases lt_trichotomy i j with hij | hij | hij
    · exact hup i j hij k
    · subst hij
      have hd : Valued.v (crdS b v σ a S i i k0) < 1 := by
        have := h' (i, i)
        simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lt_irrefl, if_false] at this
        exact this
      have hfx := hfix (fun l => crdS b v σ a S i i l) (by
        funext m
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
        have hs : sigR (Fv F v) σ (Sm i i) = Sm i i := S.1.2 i i
        have := cr_sig b v σ (Sm i i) m
        rw [hs] at this
        simp only [crdS_eq]
        exact this.symm)
      have hkk : k = k0 ∨ k = k1 := by
        fin_cases k <;> fin_cases k0 <;> fin_cases k1 <;> simp_all
      rcases hkk with rfl | rfl
      · exact hd
      · have e : crdS b v σ a S i i k = algebraMap F (Fv F v) ρ * crdS b v σ a S i i k0 := hfx
        rw [e]
        exact val_mul_lt v hρ hd
    · have hs : Sm i j = sigR (Fv F v) σ (Sm j i) := (S.1.2 i j).symm
      rw [crdS_eq, show ((S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = Sm i j
        from rfl, hs, cr_sig, Fin.sum_univ_two]
      refine Valuation.map_add_lt _ (val_mul_lt v (hC _ _) ?_) (val_mul_lt v (hC _ _) ?_)
      · exact hup j i hij 0
      · exact hup j i hij 1

end Comap

theorem index_max {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup.index = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  rw [← ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue v]
  rfl

end IdxHW

end PI.VolStabSW
