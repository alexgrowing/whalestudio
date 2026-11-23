import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypInvLe
import Formalism.LocalToGlobal.GlobalTheory.GL6.ValuationClassTranslateMem

noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem isTr_inv_mul (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (γ1 γ2 : GL (Fin n) E)
    (h1 : γ1 ∈ UJ (σ : E →+* E) J) (h2 : γ2 ∈ UJ (σ : E →+* E) J) (z : Formalism.L2.Forms.Frames (gramC J emb)) :
    IsTr (atInf emb ((γ1⁻¹ * γ2 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
      (frameTranslate emb hc γ2⁻¹ ((UJ _ _).inv_mem h2) z) (frameTranslate emb hc γ1⁻¹ ((UJ _ _).inv_mem h1) z) := by
  intro τ
  show atInf emb ((γ1⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * z.1 τ =
    atInf emb ((γ1⁻¹ * γ2 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ *
      (atInf emb ((γ2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * z.1 τ)
  rw [← Matrix.mul_assoc]
  congr 1
  simp only [atInf]
  rw [← Matrix.map_mul, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one]

def LawAt (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ) : Prop :=
  ∀ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 →
    ∀ y y' : Formalism.L2.Forms.Frames (gramC J emb), IsTr (atInf emb γ) y' y → v y = (S.chi κ : ℂ) * v y'

theorem law_wd (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ) (hv : LawAt S emb y0 v)
    (γ1 γ2 : GL (Fin n) E) (h1 : γ1 ∈ UJ (σ : E →+* E) J) (h2 : γ2 ∈ UJ (σ : E →+* E) J) (κ1 κ2 : S.U)
    (e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * y0.1 * κ1.1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2 * y0.1 * κ2.1) (z : Formalism.L2.Forms.Frames (gramC J emb)) :
    (S.chi κ1 : ℂ) * v (frameTranslate emb hc γ1⁻¹ ((UJ _ _).inv_mem h1) z) =
      (S.chi κ2 : ℂ) * v (frameTranslate emb hc γ2⁻¹ ((UJ _ _).inv_mem h2) z) := by
  have e0 : y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ1⁻¹ * γ2) * y0.1 * (κ2 * κ1⁻¹ : S.U).1 := by
    have e' : y0.1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1)⁻¹ *
        (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * y0.1 * κ1.1) * κ1.1⁻¹ := by group
    rw [e] at e'
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    calc y0.1 = _ := e'
      _ = _ := by group
  rw [hv (γ1⁻¹ * γ2) ((UJ _ _).mul_mem ((UJ _ _).inv_mem h1) h2) (κ2 * κ1⁻¹) e0 _ _ (isTr_inv_mul emb hc γ1 γ2 h1 h2 z),
    map_mul, map_inv, Units.val_mul, ← mul_assoc, ← mul_assoc, mul_comm (S.chi κ1 : ℂ), mul_assoc (S.chi κ2 : ℂ), mul_comm ((S.chi κ1 : ℂˣ) : ℂ),
    Units.inv_mul, mul_one]

open Classical in

theorem exists_form_of_law (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (lam : ι → DomWeight n) (y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (v : Formalism.L2.Forms.Frames (gramC J emb) → ℂ)
    (hV : v ∈ ValC (gramC J emb) lam) (hv : LawAt S emb y0 v) : ∃ g ∈ AdForms S emb lam, g y0 = v := by
  let Pd : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Prop := fun x =>
    ∃ q : {γ : GL (Fin n) E // γ ∈ UJ (σ : E →+* E) J} × S.U, x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) q.1.1 * y0.1 * q.2.1
  let g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Formalism.L2.Forms.Frames (gramC J emb) → ℂ := fun x y =>
    if h : Pd x then (S.chi h.choose.2 : ℂ) * v (frameTranslate emb hc h.choose.1.1⁻¹ ((UJ _ _).inv_mem h.choose.1.2) y) else 0
  have gval : ∀ x (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (κ : S.U),
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1 → ∀ y,
      g x y = (S.chi κ : ℂ) * v (frameTranslate emb hc γ⁻¹ ((UJ _ _).inv_mem hγ) y) := by
    intro x γ hγ κ e y
    have h : Pd x := ⟨(⟨γ, hγ⟩, κ), e⟩
    show (if h : Pd x then (S.chi h.choose.2 : ℂ) * v (frameTranslate emb hc h.choose.1.1⁻¹ ((UJ _ _).inv_mem h.choose.1.2) y) else 0) = _
    rw [dif_pos h]
    exact law_wd S emb hc y0 v hv _ _ h.choose.1.2 hγ _ _ (h.choose_spec.symm.trans e) y
  have gzero : ∀ x, ¬ Pd x → ∀ y, g x y = 0 := by
    intro x h y
    show (if h : Pd x then (S.chi h.choose.2 : ℂ) * v (frameTranslate emb hc h.choose.1.1⁻¹ ((UJ _ _).inv_mem h.choose.1.2) y) else 0) = _
    rw [dif_neg h]
  refine ⟨g, Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · intro γ' hγ' x x' κ' hx' y y' hy
    by_cases hP : Pd x
    · obtain ⟨⟨⟨γ, hγ⟩, κ⟩, e⟩ := hP
      have e' : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ' * γ) * y0.1 * (κ * κ' : S.U).1 := by
        rw [hx', e, map_mul, Subgroup.coe_mul]; group
      rw [gval x γ hγ κ e, gval x' (γ' * γ) ((UJ _ _).mul_mem hγ' hγ) (κ * κ') e']
      have hfr : frameTranslate emb hc (γ' * γ)⁻¹ ((UJ _ _).inv_mem ((UJ _ _).mul_mem hγ' hγ)) y =
          frameTranslate emb hc γ⁻¹ ((UJ _ _).inv_mem hγ) y' := by
        apply Subtype.ext
        funext τ
        show atInf emb (((γ' * γ)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ =
          atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y'.1 τ
        rw [hy τ, _root_.mul_inv_rev]
        simp only [atInf, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
        congr 1
        rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
      rw [hfr, map_mul, Units.val_mul]
      ring
    · have hP' : ¬ Pd x' := by
        rintro ⟨⟨⟨γ, hγ⟩, κ⟩, e⟩
        refine hP ⟨(⟨γ'⁻¹ * γ, (UJ _ _).mul_mem ((UJ _ _).inv_mem hγ') hγ⟩, κ * κ'⁻¹), ?_⟩
        show x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ'⁻¹ * γ) * y0.1 * (κ * κ'⁻¹ : S.U).1
        have e1 : x.1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ')⁻¹ * x'.1 * κ'.1⁻¹ := by
          rw [hx']; group
        rw [e1, e, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]; group
      rw [gzero x hP, gzero x' hP', mul_zero]
  · refine Submodule.mem_pi.2 fun x _ => ?_
    by_cases hP : Pd x
    · obtain ⟨⟨⟨γ, hγ⟩, κ⟩, e⟩ := hP
      have : g x = (S.chi κ : ℂ) • fun y => v (frameTranslate emb hc γ⁻¹ ((UJ _ _).inv_mem hγ) y) := by
        funext y
        exact gval x γ hγ κ e y
      rw [this]
      exact Submodule.smul_mem _ _ (valuation_class_translate_mem emb hc lam _ _ hV)
    · have : g x = 0 := by
        funext y
        exact gzero x hP y
      rw [this]
      exact Submodule.zero_mem _
  · funext y
    rw [gval y0 1 (UJ _ _).one_mem 1 (by rw [map_one]; simp)]
    have hfr : frameTranslate emb hc (1 : GL (Fin n) E)⁻¹ ((UJ _ _).inv_mem (UJ (σ : E →+* E) J).one_mem) y = y := by
      apply Subtype.ext
      funext τ
      show atInf emb (((1 : GL (Fin n) E)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ = y.1 τ
      rw [inv_one]
      simp [atInf]
    rw [hfr, map_one, Units.val_one, one_mul]

end Gen

open Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem formsOnClassOf (S : StepIn M i hi G) : FormsOnClassOf S := by
  intro β c v hv
  obtain ⟨g, hg, e⟩ := exists_form_of_law (S.K β).lev (embT D) (embedding_conj_compat D) (lamTG M i) ((S.K β).y c) v hv.1 hv.2
  exact Submodule.mem_map.2 ⟨res (embT D) (S.K β).y g, Submodule.mem_map.2 ⟨g, hg, rfl⟩, e⟩

end Formalism.MainNotions.G.ChF

end
