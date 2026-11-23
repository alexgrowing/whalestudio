import Formalism.LocalToGlobal.GlobalTheory.GL6.FrobeniusNoKernelOfFrobeniusSimilitude

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open Formalism.GradedWeylDivisibility (blockAct)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem valuation_class_translate_mem (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (lam : ι → DomWeight n) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) {V : Frames (gramC J emb) → ℂ}
    (hV : V ∈ ValC (gramC J emb) lam) :
    (fun y => V (frameTranslate emb hc γ hγ y)) ∈ ValC (gramC J emb) lam := by
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.1 hV
  refine Submodule.mem_map.2 ⟨(∏ τ, (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ).det ^ shiftOf lam τ) •
    blockAct ℂ (atInf emb (γ : Matrix (Fin n) (Fin n) E)) P,
    Submodule.smul_mem _ _ (complex_span_block_action_stable lam _ hP), ?_⟩
  rw [← Formalism.L2.Col.fnOf_mul]
  funext y
  simp only [fnOf, frameTranslate, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.mul_one, Matrix.one_mul]

theorem class_rep_translate_unique (S : StepLevel F E σ J T f bad) {C : Type} (yc : C → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hinj : Function.Injective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (hstab : ∀ c (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ S.U.map (MulAut.conj (yc c).1).toMonoidHom → γ = 1)
    (c1 c2 : C) (γ1 γ2 : GL (Fin n) E) (h1 : γ1 ∈ UJ (σ : E →+* E) J) (h2 : γ2 ∈ UJ (σ : E →+* E) J)
    (κ1 κ2 : S.U)
    (e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * (yc c1).1 * κ1.1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2 * (yc c2).1 * κ2.1) :
    c1 = c2 ∧ γ1 = γ2 ∧ κ1 = κ2 := by
  have hU : ∀ κ : S.U, κ.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := fun κ => ((S.U_eq κ.1).1 κ.2).1
  set k : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨κ1.1 * κ2.1⁻¹, (UPts _ _ _).mul_mem (hU κ1) ((UPts _ _ _).inv_mem (hU κ2))⟩
  set h : UPts σ J (FiniteAdeleRing (𝓞 F) F) := yc c2 * k⁻¹ * (yc c1)⁻¹
  have hh : h.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ2⁻¹ * γ1) := by
    simp only [h, k, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    have e' : (yc c2).1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2)⁻¹ *
        (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * (yc c1).1 * κ1.1) * κ2.1⁻¹ := by
      rw [e]; group
    rw [e']; group
  have hc : c1 = c2 := by
    apply hinj
    show (Quotient.mk'' (yc c1) : Cls S) = Quotient.mk'' (yc c2)
    refine (DoubleCoset.eq _ _ (yc c1) (yc c2)).2 ⟨h, ?_, k, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ2⁻¹ * γ1, (UJ _ _).mul_mem ((UJ _ _).inv_mem h2) h1, hh.symm⟩)
    · exact Subgroup.mem_subgroupOf.2 (S.U.mul_mem κ1.2 (S.U.inv_mem κ2.2))
    · simp only [h]; group
  subst hc
  have hγ : γ2⁻¹ * γ1 = 1 := by
    apply hstab c1 _ ((UJ _ _).mul_mem ((UJ _ _).inv_mem h2) h1)
    refine Subgroup.mem_map.2 ⟨κ2.1 * κ1.1⁻¹, S.U.mul_mem κ2.2 (S.U.inv_mem κ1.2), ?_⟩
    show (yc c1).1 * (κ2.1 * κ1.1⁻¹) * (yc c1).1⁻¹ = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ2⁻¹ * γ1)
    rw [map_mul, map_inv]
    have e' : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2 * (yc c1).1 * κ2.1 * κ1.1⁻¹ * (yc c1).1⁻¹ := by
      rw [← e]; group
    rw [e']; group
  have hγ' : γ1 = γ2 := by
    have := congrArg (γ2 * ·) hγ
    simpa [← mul_assoc] using this
  subst hγ'
  refine ⟨rfl, rfl, Subtype.ext ?_⟩
  have := e
  rw [mul_assoc, mul_assoc] at this
  exact mul_left_cancel (mul_left_cancel this)

theorem adelic_function_ext (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (lam : ι → DomWeight n) {C : Type}
    (yc : C → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hbij : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (hstab : ∀ c (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ S.U.map (MulAut.conj (yc c).1).toMonoidHom → γ = 1)
    (φ : C → Frames (gramC J emb) → ℂ) (hφ : ∀ c, φ c ∈ ValC (gramC J emb) lam) :
    φ ∈ FiC S emb lam yc := by
  have hdec : ∀ x : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ c, ∃ γ : GL (Fin n) E, ∃ _ : γ ∈ UJ (σ : E →+* E) J,
      ∃ κ : S.U, x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1 := by
    intro x
    obtain ⟨c, hcx⟩ := hbij.2 (Quotient.mk'' x)
    obtain ⟨hh, hhH, κ, hκK, e⟩ := (DoubleCoset.eq _ _ (yc c) x).1 hcx
    obtain ⟨g, hgU, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
    refine ⟨c, g, hgU, ⟨κ.1, hκK⟩, ?_⟩
    have := congrArg Subtype.val e
    simp only [Subgroup.coe_mul] at this
    rw [this, hge]
  choose cx γx hγx κx hx using hdec
  have hun := class_rep_translate_unique S yc hbij.1 hstab
  refine Submodule.mem_map.2 ⟨fun x y => (S.chi (κx x) : ℂ) *
    φ (cx x) (frameTranslate emb hc (γx x)⁻¹ ((UJ _ _).inv_mem (hγx x)) y), Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  ·
    intro γ' hγ' x x' κ' hx' y y' hy
    obtain ⟨hc2, hg2, hk2⟩ := hun (cx x') (cx x) (γx x') (γ' * γx x) (hγx x') ((UJ _ _).mul_mem hγ' (hγx x))
      (κx x') (κx x * κ') (by
        rw [← hx x', hx', hx x, map_mul, Subgroup.coe_mul]; group)
    have hfr : frameTranslate emb hc (γx x')⁻¹ ((UJ _ _).inv_mem (hγx x')) y =
        frameTranslate emb hc (γx x)⁻¹ ((UJ _ _).inv_mem (hγx x)) y' := by
      apply Subtype.ext
      funext τ
      show atInf emb (((γx x')⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ =
        atInf emb (((γx x)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y'.1 τ
      rw [hy τ, hg2, _root_.mul_inv_rev]
      simp only [atInf, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    show (S.chi (κx x') : ℂ) * φ (cx x') (frameTranslate emb hc (γx x')⁻¹ ((UJ _ _).inv_mem (hγx x')) y) =
      (S.chi κ' : ℂ) * ((S.chi (κx x) : ℂ) * φ (cx x) (frameTranslate emb hc (γx x)⁻¹ ((UJ _ _).inv_mem (hγx x)) y'))
    rw [hfr, hc2, hk2, map_mul, Units.val_mul]
    ring
  · refine Submodule.mem_pi.2 fun x _ => ?_
    exact Submodule.smul_mem _ _ (valuation_class_translate_mem emb hc lam _ _ (hφ (cx x)))
  · funext c y
    obtain ⟨hc1, hg1, hk1⟩ := hun (cx (yc c)) c (γx (yc c)) 1 (hγx (yc c)) (UJ _ _).one_mem (κx (yc c)) 1 (by
      rw [← hx (yc c), map_one]; simp)
    show (S.chi (κx (yc c)) : ℂ) * φ (cx (yc c)) (frameTranslate emb hc (γx (yc c))⁻¹ ((UJ _ _).inv_mem (hγx (yc c))) y) = φ c y
    have hfr : frameTranslate emb hc (γx (yc c))⁻¹ ((UJ _ _).inv_mem (hγx (yc c))) y = y := by
      apply Subtype.ext
      funext τ
      show atInf emb (((γx (yc c))⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ = y.1 τ
      rw [hg1, inv_one]
      simp [atInf]
    rw [hfr, hc1, hk1, map_one, Units.val_one, one_mul]

end Gen

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
