import Formalism.LocalToGlobal.GlobalTheory.GL6.ValuationClassTranslateMem
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ClassMapEstimateOfPartial
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ExistsOnOfPosDef
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.TilEqLevel
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.DefNOfFact

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases (frameTranslate)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem cls_eq_of_dec (S : StepLevel F E σ J T f bad) {C : Type} (yc : C → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hinj : Function.Injective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (c1 c2 : C) (γ1 γ2 : GL (Fin n) E) (h1 : γ1 ∈ UJ (σ : E →+* E) J) (h2 : γ2 ∈ UJ (σ : E →+* E) J)
    (κ1 κ2 : S.U)
    (e : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * (yc c1).1 * κ1.1 =
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2 * (yc c2).1 * κ2.1) : c1 = c2 := by
  have hU : ∀ κ : S.U, κ.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := fun κ => ((S.U_eq κ.1).1 κ.2).1
  set k : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨κ1.1 * κ2.1⁻¹, (UPts _ _ _).mul_mem (hU κ1) ((UPts _ _ _).inv_mem (hU κ2))⟩
  set h : UPts σ J (FiniteAdeleRing (𝓞 F) F) := yc c2 * k⁻¹ * (yc c1)⁻¹
  have hh : h.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ2⁻¹ * γ1) := by
    simp only [h, k, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    have e' : (yc c2).1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ2)⁻¹ *
        (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ1 * (yc c1).1 * κ1.1) * κ2.1⁻¹ := by
      rw [e]; group
    rw [e']; group
  apply hinj
  show (Quotient.mk'' (yc c1) : Cls S) = Quotient.mk'' (yc c2)
  refine (DoubleCoset.eq _ _ (yc c1) (yc c2)).2 ⟨h, ?_, k, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ2⁻¹ * γ1, (UJ _ _).mul_mem ((UJ _ _).inv_mem h2) h1, hh.symm⟩)
  · exact Subgroup.mem_subgroupOf.2 (S.U.mul_mem κ1.2 (S.U.inv_mem κ2.2))
  · simp only [h]; group

theorem fic_of_stab (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (lam : ι → DomWeight n) {C : Type}
    (yc : C → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hbij : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (φ : C → Frames (gramC J emb) → ℂ)
    (hstab : ∀ c (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (yc c).1 * κ.1 = (yc c).1 →
      ∀ y y' : Frames (gramC J emb), IsTr (atInf emb γ) y' y → φ c y = (S.chi κ : ℂ) * φ c y')
    (hφ : ∀ c, φ c ∈ ValC (gramC J emb) lam) :
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
  have hcl := cls_eq_of_dec S yc hbij.1
  have hmulTr : ∀ (a b : GL (Fin n) E) (y : Frames (gramC J emb)) τ,
      atInf emb ((a * b : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ =
        atInf emb (a : Matrix (Fin n) (Fin n) E) τ * (atInf emb (b : Matrix (Fin n) (Fin n) E) τ * y.1 τ) := by
    intro a b y τ
    simp only [atInf, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
  refine Submodule.mem_map.2 ⟨fun x y => (S.chi (κx x) : ℂ) *
    φ (cx x) (frameTranslate emb hc (γx x)⁻¹ ((UJ _ _).inv_mem (hγx x)) y), Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  ·
    intro γ' hγ' x x' κ' hx' y y' hy
    have e1 : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γx x') * (yc (cx x')).1 * (κx x').1 =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ' * γx x) * (yc (cx x)).1 * (κx x * κ').1 := by
      rw [← hx x', hx', hx x, map_mul, Subgroup.coe_mul]; group
    have hc2 : cx x' = cx x := hcl _ _ _ _ (hγx x') ((UJ _ _).mul_mem hγ' (hγx x)) _ _ e1
    set c := cx x with hcdef
    set δ : GL (Fin n) E := (γx x')⁻¹ * γ' * γx x with hδ
    have hδU : δ ∈ UJ (σ : E →+* E) J := (UJ _ _).mul_mem ((UJ _ _).mul_mem ((UJ _ _).inv_mem (hγx x')) hγ') (hγx x)
    set κ0 : S.U := κx x * κ' * (κx x')⁻¹ with hκ0
    have hst : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) δ * (yc c).1 * κ0.1 = (yc c).1 := by
      have e2 : (yc c).1 = (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γx x'))⁻¹ *
          (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ' * γx x) * (yc c).1 * (κx x * κ').1) * (κx x').1⁻¹ := by
        rw [← e1, hc2]; group
      conv_rhs => rw [e2]
      simp only [hδ, hκ0, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hT : IsTr (atInf emb (δ : Matrix (Fin n) (Fin n) E))
        (frameTranslate emb hc (γx x)⁻¹ ((UJ _ _).inv_mem (hγx x)) y')
        (frameTranslate emb hc (γx x')⁻¹ ((UJ _ _).inv_mem (hγx x')) y) := by
      intro τ
      show atInf emb (((γx x')⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ =
        atInf emb (δ : Matrix (Fin n) (Fin n) E) τ *
          (atInf emb (((γx x)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y'.1 τ)
      rw [hy τ]
      simp only [hδ, atInf, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((γx x : Matrix (Fin n) (Fin n) E).map (emb τ)), ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    have key := hstab c δ hδU κ0 hst _ _ hT
    show (S.chi (κx x') : ℂ) * φ (cx x') (frameTranslate emb hc (γx x')⁻¹ ((UJ _ _).inv_mem (hγx x')) y) =
      (S.chi κ' : ℂ) * ((S.chi (κx x) : ℂ) * φ (cx x) (frameTranslate emb hc (γx x)⁻¹ ((UJ _ _).inv_mem (hγx x)) y'))
    rw [hc2, key]
    have hk : κ0 * κx x' = κx x * κ' := by simp only [hκ0, inv_mul_cancel_right]
    have hch : (S.chi (κx x') : ℂ) * (S.chi κ0 : ℂ) = (S.chi κ' : ℂ) * (S.chi (κx x) : ℂ) := by
      rw [mul_comm (S.chi (κx x') : ℂ), ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hk, map_mul, map_mul, mul_comm]
    rw [← mul_assoc, hch, mul_assoc]
  · refine Submodule.mem_pi.2 fun x _ => ?_
    exact Submodule.smul_mem _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.valuation_class_translate_mem emb hc lam _ _ (hφ (cx x)))
  · funext c y
    have e1 : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γx (yc c)) * (yc (cx (yc c))).1 * (κx (yc c)).1 =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) 1 * (yc c).1 * (1 : S.U).1 := by
      rw [← hx (yc c), map_one]; simp
    have hc1 : cx (yc c) = c := hcl _ _ _ _ (hγx (yc c)) (UJ _ _).one_mem _ _ e1
    have hst : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γx (yc c)) * (yc c).1 * (κx (yc c)).1 = (yc c).1 := by
      have := e1; rw [hc1] at this; rw [this]; simp
    have hT : IsTr (atInf emb ((γx (yc c) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
        (frameTranslate emb hc (γx (yc c))⁻¹ ((UJ _ _).inv_mem (hγx (yc c))) y) y := by
      intro τ
      show y.1 τ = atInf emb ((γx (yc c) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ *
        (atInf emb (((γx (yc c))⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ)
      simp only [atInf]
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    show (S.chi (κx (yc c)) : ℂ) * φ (cx (yc c)) (frameTranslate emb hc (γx (yc c))⁻¹ ((UJ _ _).inv_mem (hγx (yc c))) y) = φ c y
    rw [hc1, hstab c _ (hγx (yc c)) _ hst _ _ hT]

end Gen

section Tied

open Formalism.MainNotions.product_first_zeroth_parts

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem brTen_memS (Tf : FormsTiedSym D u Ch chOf) {P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ}
    (hP : P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam D.R.m)) : Formalism.L2.Ker.brTen D u P ∈ Formalism.L2.Forms.CSpan (D.fm u).sg := by
  induction hP using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f, hf, rfl⟩ := hp
    have e : Formalism.L2.Ker.brTen D u (Formalism.L2.Forms.ten f) =
        Formalism.MainNotions.product_first_zeroth_parts.ten (fun τ => Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) (f τ)) := by
      unfold Formalism.L2.Ker.brTen
      exact Formalism.MainNotions.product_first_zeroth_parts.blk_ten (fun τ => Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) f
    rw [e]
    refine Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩
    have := (Formalism.L2.Ker.brOne_member D u τ (interlaceTr D u (sg_interlace Tf.valP) τ)).1 (f τ)
    rwa [sgTr, delSq_wSh] at this
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem pt_val (Tf : FormsTiedSym D u Ch chOf) (hL : Formalism.L2.Rows.LowerMapTieS Tf) (φ : Fn D u D.R.m)
    (hφ : φ ∈ (D.fm u).Fi D.R.m) (c : (D.fm u).clsP) :
    ∃ Q ∈ Formalism.L2.Forms.CSpan (sgT u), Tf.valP.eW (Pt D u φ) c = fnOf (gramC (gramP D) (embT D)) (shiftOf (sgT u)) 1 Q := by
  obtain ⟨P, hP, hv⟩ := val_repS Tf φ hφ c
  rw [LowerMapTieSym.pt_eq (lowerMapTieSym_of Tf hL) (bZ_isUnitS Tf) φ c P hP hv]
  refine ⟨_, ?_, rfl⟩
  have h := brTen_memS Tf hP
  unfold sgT
  rw [CSpan_shW]
  exact h

def StabCompS (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c (γ : GL (Fin (D.R.N D.R.m - 1)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramP D) →
    ∀ κ : Tf.clsP.lev.U,
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (Tf.clsP.y c).1 * κ.1 = (Tf.clsP.y c).1 →
      ∀ y y' : FrP D, IsTr (atInf (embT D) (γ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) y' y →
        Tf.valP.eW (Pt D u φ) c y = (Tf.clsP.lev.chi κ : ℂ) * Tf.valP.eW (Pt D u φ) c y'

theorem forms_of_stab (Tf : FormsTiedSym D u Ch chOf) (hL : Formalism.L2.Rows.LowerMapTieS Tf) (hS : StabCompS Tf) :
    ∀ φ ∈ (D.fm u).Fi D.R.m, Pt D u φ ∈ (D.fm u).ptC := by
  intro φ hφ
  rw [Tf.valP.ptC]
  exact fic_of_stab Tf.clsP.lev (embT D) (embT_sig (D := D)) (sgT u) Tf.clsP.y Tf.clsP.y_bij _
    (fun c γ hγ κ h y y' hy => hS φ hφ c γ hγ κ h y y' hy)
    (fun c => by obtain ⟨Q, hQ, e⟩ := pt_val Tf hL φ hφ c; exact Submodule.mem_map.2 ⟨Q, hQ, e.symm⟩)

end Tied

section Ext

open Formalism.MainNotions.product_first_zeroth_parts

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def ExtLevS (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  (∀ γ : GL (Fin (D.R.N D.R.m - 1)) D.host.E, γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramP D) →
    ∃ Γ : GL (Fin (D.R.N D.R.m)) D.host.E, Γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) ∧
      IsExt D Tf.til.z0 (RingHom.id D.host.E) (γ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
        (Γ : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E)) ∧
  (∀ κ : Tf.clsP.lev.U, ∃ G : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U,
    IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1.1 ∧
    (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi G : ℂˣ) : ℂ) = ((Tf.clsP.lev.chi κ : ℂˣ) : ℂ))

theorem ext_mul_bZ (Tf : FormsTiedSym D u Ch chOf) (γ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
    (Γ : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) (h : IsExt D Tf.til.z0 (RingHom.id D.host.E) γ Γ) :
    Γ * bZ u Tf.til.z0 = bZ u Tf.til.z0 * dgE γ := by
  rw [← bZg_eq_mul]
  obtain ⟨h1, h2⟩ := h
  have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
  rw [hm] at h1
  have h2' : Γ *ᵥ Tf.til.z0 = Tf.til.z0 := h2
  ext a b
  simp only [Matrix.mul_apply, bZ, bZg]
  by_cases hb : (b : ℕ) < D.R.N D.R.m - 1
  · simp only [dif_pos hb]
    have := congrFun (congrFun h1 a) ⟨b, hb⟩
    simp only [Matrix.mul_apply] at this
    exact_mod_cast this
  · simp only [dif_neg hb]
    have := congrFun h2' a
    simp only [Matrix.mulVec, dotProduct] at this
    rw [← this, Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => (mul_div_assoc _ _ _).symm

end Ext

section ExtU

open Formalism.MainNotions.product_first_zeroth_parts

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

set_option maxHeartbeats 2000000 in

theorem extU (Tf : FormsTiedSym D u Ch chOf) (γ : GL (Fin (D.R.N D.R.m - 1)) D.host.E)
    (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramP D)) :
    ∃ Γ : GL (Fin (D.R.N D.R.m)) D.host.E, Γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) ∧
      IsExt D Tf.til.z0 (RingHom.id D.host.E) (γ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
        (Γ : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) := by
  obtain ⟨g, hg, hu⟩ := til_ext Tf (RingHom.id D.host.E) (γ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
  have hγd : IsUnit (γ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit
  refine ⟨((Matrix.isUnit_iff_isUnit_det g).mpr (hu hγd)).unit, ?_, hg⟩
  show cT (sigD D : D.host.E →+* D.host.E) g * gramN D D.R.m le_rfl * g = gramN D D.R.m le_rfl
  obtain ⟨h1, h2⟩ := hg
  have hm : (iXm D).map (RingHom.id D.host.E) = iXm D := by ext i j; rfl
  rw [hm] at h1
  have hz : g *ᵥ Tf.til.z0 = Tf.til.z0 := h2
  obtain ⟨a, ha⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
    have h := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [ha, zero_smul] at h
    simp [Formalism.UG.hform] at h
    exact hT h.symm
  have hzc : g *ᵥ zc D = zc D := by
    rw [ha, Matrix.mulVec_smul] at hz
    exact smul_right_injective _ ha0 hz
  have hiX : ∀ x, iXc D x = iXm D *ᵥ x := fun x => by simp only [iXm, LinearMap.toMatrix'_mulVec]
  have hX : ∀ x, g *ᵥ iXc D x = iXc D ((γ : Matrix _ _ D.host.E) *ᵥ x) := by
    intro x
    rw [hiX, hiX, Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec]
  have hγ' : cT (sigD D : D.host.E →+* D.host.E) (γ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) *
      gramP D * (γ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) = gramP D := hγ
  have hγf : ∀ x y, hform (sigD D : D.host.E →+* D.host.E) (gramP D) ((γ : Matrix _ _ D.host.E) *ᵥ x)
      ((γ : Matrix _ _ D.host.E) *ᵥ y) = hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y := by
    intro x y
    rw [Formalism.UG.P.hform_mulVec, hγ']
  have hpres : ∀ v w, hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (g *ᵥ v) (g *ᵥ w) =
      hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) v w := by
    intro v w
    obtain ⟨x, s, rfl⟩ := span_iXc_zc D v
    obtain ⟨x', s', rfl⟩ := span_iXc_zc D w
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hX, hzc, hform_add_left, hform_add_right, hform_smul_left,
      hform_smul_right, hform_iXc, hform_iXc_zc, hform_zc_iXc, hγf]
  ext i j
  rw [← Formalism.UG.P.hform_single (sigD D : D.host.E →+* D.host.E) (cT (sigD D : D.host.E →+* D.host.E) g * gramN D D.R.m le_rfl * g) i j,
    ← Formalism.UG.P.hform_mulVec, hpres, Formalism.UG.P.hform_single]

end ExtU

section Inv

open Formalism.MainNotions.product_first_zeroth_parts TensorProduct

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

set_option maxHeartbeats 4000000 in

theorem stab_m (Tf : FormsTiedSym D u Ch chOf) (hE : ExtLevS Tf)
    (c : (D.fm u).clsP) (γ : GL (Fin (D.R.N D.R.m - 1)) D.host.E) (κ : Tf.clsP.lev.U)
    (hst : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (Tf.clsP.y c).1 * κ.1 = (Tf.clsP.y c).1)
    (Γ0 : GL (Fin (D.R.N D.R.m)) D.host.E)
    (hΓ0E : IsExt D Tf.til.z0 (RingHom.id D.host.E) (γ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
        (Γ0 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E)) :
    ∃ κm : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U, ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((Tf.til.ga c).1⁻¹ * Γ0 * (Tf.til.ga c).1) * ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 * κm.1 ∧
      (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi κm : ℂˣ) : ℂ) = ((Tf.clsP.lev.chi κ : ℂˣ) : ℂ) := by
  obtain ⟨G, hGE, hGchi⟩ := hE.2 κ
  have hdet : IsUnit ((Tf.clsP.y c).1.1).det := (Matrix.isUnit_iff_isUnit_det _).mp (Tf.clsP.y c).1.isUnit
  obtain ⟨g1m, hg1E, hg1u⟩ := til_ext Tf (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.clsP.y c).1.1
  obtain ⟨g1, hg1⟩ : ∃ g1 : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), g1.1 = g1m :=
    ⟨((Matrix.isUnit_iff_isUnit_det g1m).mpr (hg1u hdet)).unit, rfl⟩
  rw [← hg1] at hg1E
  have e1 := Tf.tilAd.til_ad c g1 hg1E
  have hE2 : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.clsP.y c).1.1 (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ0 * g1 * G.1).1 := by
    have h := isExt_mul (isExt_mul (isExt_map (φ := (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) hΓ0E) hg1E) hGE
    have e : (γ : Matrix _ _ D.host.E).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (Tf.clsP.y c).1.1 * κ.1.1 = (Tf.clsP.y c).1.1 :=
      congrArg (fun x : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) => x.1) hst
    rw [e] at h
    exact h
  have e2 := Tf.tilAd.til_ad c _ hE2
  refine ⟨(Tf.tilAd.ka c)⁻¹ * G * Tf.tilAd.ka c, ?_, ?_⟩
  · have hg1' : g1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.til.ga c).1 * ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 * ((Tf.tilAd.ka c).1)⁻¹ :=
      eq_mul_inv_of_mul_eq e1.symm
    rw [hg1'] at e2
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    calc ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.til.ga c).1)⁻¹ * (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.til.ga c).1 * ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1) := by group
      _ = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.til.ga c).1)⁻¹ * (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) Γ0 * (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.til.ga c).1 * ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)).1 *
            ((Tf.tilAd.ka c).1)⁻¹) * G.1 * (Tf.tilAd.ka c).1) := by rw [← e2]
      _ = _ := by group
  · rw [← hGchi, map_mul, map_mul, map_inv, mul_comm ((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹, mul_assoc, inv_mul_cancel, mul_one]

set_option maxHeartbeats 4000000 in

theorem val_inv (Tf : FormsTiedSym D u Ch chOf) (hE : ExtLevS Tf) (φ : Fn D u D.R.m) (hφ : φ ∈ (D.fm u).Fi D.R.m)
    (c : (D.fm u).clsP) (γ : GL (Fin (D.R.N D.R.m - 1)) D.host.E) (κ : Tf.clsP.lev.U)
    (hst : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * (Tf.clsP.y c).1 * κ.1 = (Tf.clsP.y c).1)
    (Γ0 : GL (Fin (D.R.N D.R.m)) D.host.E) (hΓ0U : Γ0 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl))
    (hΓ0E : IsExt D Tf.til.z0 (RingHom.id D.host.E) (γ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
        (Γ0 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E))
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)
    (hv : ∀ s, Tf.eWz ((D.mem u).P.evz φ) c s =
      fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY s))
    (Z : Fr D D.R.m le_rfl) :
    fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P (Z.tr (atInf (Formalism.L2.Forms.embT D) (Γ0 : Matrix _ _ D.host.E))
      (isUnit_det_atInf (Formalism.L2.Forms.embT D) Γ0)) =
      ((Tf.clsP.lev.chi κ : ℂˣ) : ℂ) * fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P Z := by
  obtain ⟨κm, hstm, hchi⟩ := stab_m Tf hE c γ κ hst Γ0 hΓ0E
  have hΓmU : (Tf.til.ga c).1⁻¹ * Γ0 * (Tf.til.ga c).1 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) :=
    (UJ _ _).mul_mem ((UJ _ _).mul_mem ((UJ _ _).inv_mem (Tf.til.ga c).2) hΓ0U) (Tf.til.ga c).2
  have hF := ((Tf.val D.R.m le_rfl (Or.inr rfl)).Fi φ).1 hφ
  obtain ⟨gA, hgA, hres⟩ := Submodule.mem_map.1 hF
  have hA := (Submodule.mem_inf.1 hgA).1
  have hval : ∀ Y, gA ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)) Y = φ ((D.fm u).til c) ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm Y) :=
    fun Y => congrFun (congrFun hres ((D.fm u).til c)) Y
  have hPZ : ∀ Y : Fr D D.R.m le_rfl, fnOf _ (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0) P Y =
      ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ) * φ ((D.fm u).til c) ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm
        (Y.tr (atInf (Formalism.L2.Forms.embT D) (((Tf.til.ga c).1⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E))
        (isUnit_det_atInf (Formalism.L2.Forms.embT D) (Tf.til.ga c).1⁻¹))) := by
    intro Y
    have h1 := hv ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY.symm Y)
    rw [Equiv.apply_symm_apply] at h1
    rw [← h1]
    refine Tf.evz φ c _ _ (fun τ => ?_)
    simp only [Equiv.apply_symm_apply]
    show Y.1 τ = atInf (Formalism.L2.Forms.embT D) ((Tf.til.ga c).1 : Matrix _ _ D.host.E) τ *
      (atInf (Formalism.L2.Forms.embT D) (((Tf.til.ga c).1⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ * Y.1 τ)
    rw [← Matrix.mul_assoc, atInf_mul_inv, Matrix.one_mul]
  rw [hPZ, hPZ, ← hval, ← hval, hA _ hΓmU ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)) ((Tf.cls D.R.m le_rfl (Or.inr rfl)).y ((D.fm u).til c)) κm hstm, hchi]
  · ring
  · intro τ
    show atInf (Formalism.L2.Forms.embT D) (((Tf.til.ga c).1⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ *
        (atInf (Formalism.L2.Forms.embT D) (Γ0 : Matrix _ _ D.host.E) τ * Z.1 τ) =
      atInf (Formalism.L2.Forms.embT D) (((Tf.til.ga c).1⁻¹ * Γ0 * (Tf.til.ga c).1 : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ *
        (atInf (Formalism.L2.Forms.embT D) (((Tf.til.ga c).1⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix _ _ D.host.E) τ * Z.1 τ)
    simp only [atInf, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((Tf.til.ga c).1 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E).map (Formalism.L2.Forms.embT D τ)),
      ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

end Inv

section Main

open Formalism.MainNotions.product_first_zeroth_parts

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

set_option maxHeartbeats 4000000 in

theorem stab_of_ext (Tf : FormsTiedSym D u Ch chOf) (hL : Formalism.L2.Rows.LowerMapTieS Tf) (hE : ExtLevS Tf) : StabCompS Tf := by
  intro φ hφ c γ hγ κ hst y y' hy
  obtain ⟨Γ0, hΓ0U, hΓ0E⟩ := hE.1 γ hγ
  obtain ⟨P, hP, hv⟩ := val_repS Tf φ hφ c
  rw [LowerMapTieSym.pt_eq (lowerMapTieSym_of Tf hL) (bZ_isUnitS Tf) φ c P hP hv]
  have hbZ := bZ_isUnitS Tf
  have hγu : IsUnit (γ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit

  have hdg : dgE (γ : Matrix _ _ D.host.E) * (bZ u Tf.til.z0)⁻¹ = (bZ u Tf.til.z0)⁻¹ * (Γ0 : Matrix _ _ D.host.E) := by
    have hx := ext_mul_bZ Tf _ _ hΓ0E
    calc dgE (γ : Matrix _ _ D.host.E) * (bZ u Tf.til.z0)⁻¹
        = (bZ u Tf.til.z0)⁻¹ * (bZ u Tf.til.z0 * dgE (γ : Matrix _ _ D.host.E)) * (bZ u Tf.til.z0)⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hbZ, Matrix.one_mul]
      _ = (bZ u Tf.til.z0)⁻¹ * ((Γ0 : Matrix _ _ D.host.E) * bZ u Tf.til.z0) * (bZ u Tf.til.z0)⁻¹ := by rw [hx]
      _ = (bZ u Tf.til.z0)⁻¹ * (Γ0 : Matrix _ _ D.host.E) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hbZ, Matrix.mul_one]
  have hM : ∀ τ, atInf (Formalism.L2.Forms.embT D) (dgE (γ : Matrix _ _ D.host.E)) τ * mZ u Tf.til.z0 τ =
      mZ u Tf.til.z0 τ * atInf (Formalism.L2.Forms.embT D) (Γ0 : Matrix _ _ D.host.E) τ := by
    intro τ
    simp only [mZ, atInf]
    rw [← Matrix.map_mul, ← Matrix.map_mul, hdg]

  have hF : fnOf (gramC (gramN D D.R.m le_rfl) (Formalism.L2.Forms.embT D)) (shiftOf (lamT u D.R.m))
      (fun τ => atInf (Formalism.L2.Forms.embT D) (dgE (γ : Matrix _ _ D.host.E)) τ * mZ u Tf.til.z0 τ) P =
      ((Tf.clsP.lev.chi κ : ℂˣ) : ℂ) • fnOf (gramC (gramN D D.R.m le_rfl) (Formalism.L2.Forms.embT D)) (shiftOf (lamT u D.R.m))
        (mZ u Tf.til.z0) P := by
    funext Z
    rw [Pi.smul_apply, smul_eq_mul, ← val_inv Tf hE φ hφ c γ κ hst Γ0 hΓ0U hΓ0E P hv Z]
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Frames.tr, hM, Matrix.mul_assoc]
  have hc2 := fnOf_change (gramC (gramN D D.R.m le_rfl) (Formalism.L2.Forms.embT D)) (shiftOf (lamT u D.R.m)) (mZ u Tf.til.z0)
    (fun τ => atInf (Formalism.L2.Forms.embT D) (dgE (γ : Matrix _ _ D.host.E)) τ * mZ u Tf.til.z0 τ) (mZ_isUnit hbZ) P
  simp only [Matrix.mul_nonsing_inv_cancel_right _ _ (mZ_isUnit hbZ _)] at hc2
  rw [hc2] at hF
  have hPe := fnOf_injective _ _ _ (mZ_isUnit hbZ) (hF.trans (map_smul _ _ _).symm)
  have hK : (fun τ => atInf (Formalism.L2.Forms.embT D) (dgE (γ : Matrix _ _ D.host.E)) τ) = fun τ =>
      ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (glT (γ : Matrix _ _ D.host.E) hγu τ) : GL (Fin (D.R.N D.R.m)) ℂ) :
        Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ).transpose :=
    funext fun τ => (embGL_glT _ hγu τ).symm
  have hB := congrArg (Formalism.L2.Ker.brTen D u) hPe
  rw [map_smul, map_smul, hK, brTen_blkRowS Tf] at hB
  have hK2 : (fun τ => ((glT (γ : Matrix _ _ D.host.E) hγu τ : GL (Fin (D.R.N D.R.m - 1)) ℂ) :
      Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ).transpose) =
      fun τ => atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ D.host.E) τ := by
    funext τ; rw [glT_val, Matrix.transpose_transpose]; rfl
  rw [hK2] at hB

  have hy1 : fnOf (gramC (gramP D) (Formalism.L2.Forms.embT D)) (shiftOf (sgT u)) 1 (Formalism.L2.Ker.brTen D u P) y =
      fnOf (gramC (gramP D) (Formalism.L2.Forms.embT D)) (shiftOf (sgT u)) (atInf (Formalism.L2.Forms.embT D) (γ : Matrix _ _ D.host.E))
        (Formalism.L2.Ker.brTen D u P) y' := by
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul, show ∀ τ, y.1 τ = _ from hy]
    rfl
  have hc3 := fnOf_change (gramC (gramP D) (Formalism.L2.Forms.embT D)) (shiftOf (sgT u)) 1
    (atInf (Formalism.L2.Forms.embT D) (γ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) (fun τ => by simp)
    (Formalism.L2.Ker.brTen D u P)
  simp only [Pi.one_apply, inv_one, Matrix.mul_one] at hc3
  have hdet : (∏ τ, (atInf (Formalism.L2.Forms.embT D) (dgE (γ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) τ).det ^
      shiftOf (lamT u D.R.m) τ) =
      ∏ τ, (atInf (Formalism.L2.Forms.embT D) (γ : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) τ).det ^
        shiftOf (sgT u) τ := by
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [shift_lamT_sgTS Tf τ]
    congr 1
    simp only [atInf]
    unfold dgE
    rw [Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.det_submatrix_equiv_self, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  rw [hdet] at hB
  rw [hy1, hc3, hB, map_smul]
  rfl

theorem forms_of_ext (Tf : FormsTiedSym D u Ch chOf) (hL : Formalism.L2.Rows.LowerMapTieS Tf) (hE : ExtLevS Tf) :
    ∀ φ ∈ (D.fm u).Fi D.R.m, Pt D u φ ∈ (D.fm u).ptC :=
  forms_of_stab Tf hL (stab_of_ext Tf hL hE)

theorem forms_of_extension (hE : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i)
    (Tf : FormsTiedSym D u Ch chOf), ExtLevS Tf) : FormsCarriedToComplement :=
  fun D u Ch chOf Tf hL => forms_of_ext Tf hL (hE D u Ch chOf Tf)

end Main

section ExtUA

open Formalism.MainNotions.product_first_zeroth_parts TensorProduct

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

set_option maxHeartbeats 4000000 in

theorem extUA (Tf : FormsTiedSym D u Ch chOf) (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hk : cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k * (gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * k = (gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (G : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k G) :
    cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) G * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * G = (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have hc : (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (sigD D : D.host.E →+* D.host.E) = (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).comp (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    ext e
    simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
  set B' := (bZ u Tf.til.z0).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) with hB'
  set d : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Matrix.fromBlocks k 0 0 (1 : Matrix (Fin 1) (Fin 1) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))) with hd
  obtain ⟨h1, h2⟩ := hE

  have hGB : G * B' = B' * d := by
    ext a b
    obtain ⟨y, rfl⟩ := (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).surjective b
    rw [Matrix.mul_apply, Matrix.mul_apply, ← (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).sum_comp, ← (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
    rcases y with i | i
    · have := congrFun (congrFun h1 a) i
      simp only [Matrix.mul_apply] at this
      simp [hB', hd, bZ, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
      simpa [Fintype.sum_sum_type, ← (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).sum_comp] using this
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      have := congrFun h2 a
      simp only [Matrix.mulVec, dotProduct] at this
      simp [hB', hd, bZ, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
      have key : ∑ x : Fin (D.R.N D.R.m), G a x * (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.til.z0 x / ((D.mem u).A.T : D.host.E)) =
          (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Tf.til.z0 a / ((D.mem u).A.T : D.host.E)) := by
        simp only [div_eq_mul_inv, map_mul, ← mul_assoc, ← Finset.sum_mul, this]
      rw [← (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).sum_comp, Fintype.sum_sum_type] at key
      simpa using key

  have hH : cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) B' * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * B' =
      Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Matrix.fromBlocks ((gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) 0 0
        ((Matrix.of fun _ _ => ((D.mem u).A.T : D.host.E)⁻¹ : Matrix (Fin 1) (Fin 1) D.host.E).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))) := by
    have hg := gram_bZ (u := u) Tf.til.z0 Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [hB', Formalism.UG.P.cT_map _ _ _ hc, ← Matrix.map_mul, ← Matrix.map_mul]
    rw [show cT (sigD D : D.host.E →+* D.host.E) (bZ u Tf.til.z0) = ((bZ u Tf.til.z0).map (sigD D : D.host.E →+* D.host.E))ᵀ from rfl, hg]
    rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
  have hdu : cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) d * Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Matrix.fromBlocks ((gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) 0 0
        ((Matrix.of fun _ _ => ((D.mem u).A.T : D.host.E)⁻¹ : Matrix (Fin 1) (Fin 1) D.host.E).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))) * d =
      Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Matrix.fromBlocks ((gramP D).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) 0 0
        ((Matrix.of fun _ _ => ((D.mem u).A.T : D.host.E)⁻¹ : Matrix (Fin 1) (Fin 1) D.host.E).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))) := by
    have hcd : cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) d = Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Matrix.fromBlocks (cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) k) 0 0 (1 : Matrix (Fin 1) (Fin 1) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))) := by
      unfold cT
      rw [hd, Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.transpose_submatrix, Matrix.fromBlocks_map,
        Matrix.fromBlocks_transpose, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_zero, Matrix.transpose_zero, Matrix.transpose_one]
    rw [hcd, hd, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, hk]
  have hBu : IsUnit B'.det := by
    rw [hB']
    have h := (bZ_isUnitS Tf).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    rwa [RingHom.map_det] at h
  have hcBu : IsUnit (cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) B').det := by
    unfold cT
    rw [Matrix.det_transpose]
    have h := hBu.map (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    rwa [RingHom.map_det] at h
  have key : cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) B' * (cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) G * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * G) * B' = cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) B' * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * B' := by
    calc cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) B' * (cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) G * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * G) * B'
        = cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (G * B') * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (G * B') := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (B' * d) * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (B' * d) := by rw [hGB]
      _ = cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) d * (cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) B' * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * B') * d := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) B' * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * B' := by rw [hH, hdu]
  have e2 : cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) B' * (cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) G * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * G) = cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) B' * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    have := congrArg (· * B'⁻¹) key
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hBu] using this
  have := congrArg ((cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) B')⁻¹ * ·) e2
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hcBu] using this

end ExtUA

section ExtOff

open Formalism.MainNotions.product_first_zeroth_parts TensorProduct

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

set_option maxHeartbeats 4000000 in

theorem extUR {R : Type} [CommRing R] [Algebra D.host.F R] (Tf : FormsTiedSym D u Ch chOf) (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] R))
    (hk : cT (sigR (sigD D) R) k * (gramP D).map (inclE (F := D.host.F) R) * k = (gramP D).map (inclE (F := D.host.F) R))
    (G : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] R)) (hE : IsExt D Tf.til.z0 (inclE (F := D.host.F) R) k G) :
    cT (sigR (sigD D) R) G * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) R) * G = (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) R) := by
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have hc : (inclE (F := D.host.F) R).comp (sigD D : D.host.E →+* D.host.E) = (sigR (sigD D) R).comp (inclE (F := D.host.F) R) := by
    ext e
    simp [sigR, inclE, Algebra.TensorProduct.includeLeftRingHom_apply]
  set B' := (bZ u Tf.til.z0).map (inclE (F := D.host.F) R) with hB'
  set d : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] R) :=
    Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Matrix.fromBlocks k 0 0 (1 : Matrix (Fin 1) (Fin 1) (D.host.E ⊗[D.host.F] R))) with hd
  obtain ⟨h1, h2⟩ := hE

  have hGB : G * B' = B' * d := by
    ext a b
    obtain ⟨y, rfl⟩ := (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).surjective b
    rw [Matrix.mul_apply, Matrix.mul_apply, ← (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).sum_comp, ← (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
    rcases y with i | i
    · have := congrFun (congrFun h1 a) i
      simp only [Matrix.mul_apply] at this
      simp [hB', hd, bZ, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
      simpa [Fintype.sum_sum_type, ← (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).sum_comp] using this
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      have := congrFun h2 a
      simp only [Matrix.mulVec, dotProduct] at this
      simp [hB', hd, bZ, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
      have key : ∑ x : Fin (D.R.N D.R.m), G a x * (inclE (F := D.host.F) R) (Tf.til.z0 x / ((D.mem u).A.T : D.host.E)) =
          (inclE (F := D.host.F) R) (Tf.til.z0 a / ((D.mem u).A.T : D.host.E)) := by
        simp only [div_eq_mul_inv, map_mul, ← mul_assoc, ← Finset.sum_mul, this]
      rw [← (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).sum_comp, Fintype.sum_sum_type] at key
      simpa using key

  have hH : cT (sigR (sigD D) R) B' * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) R) * B' =
      Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Matrix.fromBlocks ((gramP D).map (inclE (F := D.host.F) R)) 0 0
        ((Matrix.of fun _ _ => ((D.mem u).A.T : D.host.E)⁻¹ : Matrix (Fin 1) (Fin 1) D.host.E).map (inclE (F := D.host.F) R))) := by
    have hg := gram_bZ (u := u) Tf.til.z0 Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [hB', Formalism.UG.P.cT_map _ _ _ hc, ← Matrix.map_mul, ← Matrix.map_mul]
    rw [show cT (sigD D : D.host.E →+* D.host.E) (bZ u Tf.til.z0) = ((bZ u Tf.til.z0).map (sigD D : D.host.E →+* D.host.E))ᵀ from rfl, hg]
    rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
  have hdu : cT (sigR (sigD D) R) d * Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Matrix.fromBlocks ((gramP D).map (inclE (F := D.host.F) R)) 0 0
        ((Matrix.of fun _ _ => ((D.mem u).A.T : D.host.E)⁻¹ : Matrix (Fin 1) (Fin 1) D.host.E).map (inclE (F := D.host.F) R))) * d =
      Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Matrix.fromBlocks ((gramP D).map (inclE (F := D.host.F) R)) 0 0
        ((Matrix.of fun _ _ => ((D.mem u).A.T : D.host.E)⁻¹ : Matrix (Fin 1) (Fin 1) D.host.E).map (inclE (F := D.host.F) R))) := by
    have hcd : cT (sigR (sigD D) R) d = Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Matrix.fromBlocks (cT (sigR (sigD D) R) k) 0 0 (1 : Matrix (Fin 1) (Fin 1) (D.host.E ⊗[D.host.F] R))) := by
      unfold cT
      rw [hd, Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.transpose_submatrix, Matrix.fromBlocks_map,
        Matrix.fromBlocks_transpose, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_zero, Matrix.transpose_zero, Matrix.transpose_one]
    rw [hcd, hd, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, hk]
  have hBu : IsUnit B'.det := by
    rw [hB']
    have h := (bZ_isUnitS Tf).map (inclE (F := D.host.F) R)
    rwa [RingHom.map_det] at h
  have hcBu : IsUnit (cT (sigR (sigD D) R) B').det := by
    unfold cT
    rw [Matrix.det_transpose]
    have h := hBu.map (sigR (sigD D) R)
    rwa [RingHom.map_det] at h
  have key : cT (sigR (sigD D) R) B' * (cT (sigR (sigD D) R) G * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) R) * G) * B' = cT (sigR (sigD D) R) B' * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) R) * B' := by
    calc cT (sigR (sigD D) R) B' * (cT (sigR (sigD D) R) G * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) R) * G) * B'
        = cT (sigR (sigD D) R) (G * B') * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) R) * (G * B') := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (sigR (sigD D) R) (B' * d) * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) R) * (B' * d) := by rw [hGB]
      _ = cT (sigR (sigD D) R) d * (cT (sigR (sigD D) R) B' * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) R) * B') * d := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (sigR (sigD D) R) B' * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) R) * B' := by rw [hH, hdu]
  have e2 : cT (sigR (sigD D) R) B' * (cT (sigR (sigD D) R) G * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) R) * G) = cT (sigR (sigD D) R) B' * (gramN D D.R.m le_rfl).map (inclE (F := D.host.F) R) := by
    have := congrArg (· * B'⁻¹) key
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hBu] using this
  have := congrArg ((cT (sigR (sigD D) R) B')⁻¹ * ·) e2
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hcBu] using this

theorem col_M (Tf : FormsTiedSym D u Ch chOf) (P : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E)
    (hP1 : P * iXm D = 1) (hPz : P *ᵥ Tf.til.z0 = 0) :
    ∀ b, ∃ s : D.host.E, ∀ c, ((1 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) - iXm D * P) c b = s * zc D c := by
  obtain ⟨a0, ha0⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have ha : a0 ≠ 0 := by
    rintro rfl
    have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
    have h := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [ha0, zero_smul] at h
    simp [Formalism.UG.hform] at h
    exact hT h.symm
  have hPzc : P *ᵥ zc D = 0 := by
    rw [ha0, Matrix.mulVec_smul] at hPz
    exact (smul_eq_zero.mp hPz).resolve_left ha
  have hiX : ∀ x, iXc D x = iXm D *ᵥ x := fun x => by simp only [iXm, LinearMap.toMatrix'_mulVec]
  intro b
  obtain ⟨x, s, hxs⟩ := span_iXc_zc D (Pi.single b 1)
  refine ⟨s, fun c => ?_⟩
  have e1 : P *ᵥ (iXm D *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, hP1, Matrix.one_mulVec]
  have hcol : ((1 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) - iXm D * P) *ᵥ Pi.single b 1 = s • zc D := by
    rw [hxs, Matrix.mulVec_add, Matrix.mulVec_smul, hiX, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, hPzc, Matrix.mulVec_zero, sub_zero, sub_self, zero_add]
  have := congrFun hcol c
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.transpose_apply] using this

theorem ext_form (Tf : FormsTiedSym D u Ch chOf) {R : Type} [CommRing R] (φ : D.host.E →+* R)
    (P : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m)) D.host.E) (hP1 : P * iXm D = 1) (hPz : P *ᵥ Tf.til.z0 = 0)
    (k : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) R) (G : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) R)
    (hE : IsExt D Tf.til.z0 φ k G) :
    G = (iXm D).map φ * k * P.map φ + (1 - (iXm D * P).map φ) := by
  obtain ⟨h1, h2⟩ := hE
  obtain ⟨a0, ha0⟩ := Tf.til.lastCoordinateUniformizerVector_spans_orthogonal_line
  have ha : a0 ≠ 0 := by
    rintro rfl
    have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
    have h := Tf.til.hermitianForm_lastCoordinateUniformizerVector_self
    rw [ha0, zero_smul] at h
    simp [Formalism.UG.hform] at h
    exact hT h.symm
  have hzc : G *ᵥ (fun c => φ (zc D c)) = fun c => φ (zc D c) := by
    have h2' : G *ᵥ (φ a0 • fun c => φ (zc D c)) = φ a0 • fun c => φ (zc D c) := by
      have e : (fun a => φ (Tf.til.z0 a)) = φ a0 • fun c => φ (zc D c) := by
        funext c; rw [ha0]; simp [Pi.smul_apply, smul_eq_mul, map_mul]
      rw [← e]; exact h2
    rw [Matrix.mulVec_smul] at h2'
    have hu : IsUnit (φ a0) := (Ne.isUnit ha).map φ
    exact hu.smul_left_cancel.mp h2'
  have hGM : G * (1 - (iXm D * P).map φ) = 1 - (iXm D * P).map φ := by
    ext a b
    obtain ⟨s, hs⟩ := col_M Tf P hP1 hPz b
    have hM : ∀ c, (1 - (iXm D * P).map φ) c b = φ s * φ (zc D c) := by
      intro c
      have e : (1 - (iXm D * P).map φ) c b = φ (((1 : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) - iXm D * P) c b) := by
        simp [Matrix.sub_apply, Matrix.one_apply]
        rw [← Matrix.map_mul]; rfl
      rw [e, hs c, map_mul]
    rw [Matrix.mul_apply, hM a]
    simp_rw [hM]
    have := congrFun hzc a
    simp only [Matrix.mulVec, dotProduct] at this
    rw [← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => by ring
  calc G = G * ((iXm D).map φ * P.map φ + (1 - (iXm D * P).map φ)) := by
        rw [← Matrix.map_mul, add_sub_cancel, Matrix.mul_one]
    _ = (iXm D).map φ * k * P.map φ + (1 - (iXm D * P).map φ) := by
        rw [Matrix.mul_add, ← Matrix.mul_assoc, h1, hGM]

end ExtOff

section Close

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def ExtLevK (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ κ : Tf.clsP.lev.U, ∃ G : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U,
    IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1.1 ∧
    (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi G : ℂˣ) : ℂ) = ((Tf.clsP.lev.chi κ : ℂˣ) : ℂ)

theorem extLevS_of (Tf : FormsTiedSym D u Ch chOf) (hK : ExtLevK Tf) : ExtLevS Tf :=
  ⟨fun γ hγ => extU Tf γ hγ, hK⟩

theorem forms_of_kernel_extension (hK : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i)
    (Tf : FormsTiedSym D u Ch chOf), ExtLevK Tf) : FormsCarriedToComplement :=
  forms_of_extension fun D u Ch chOf Tf => extLevS_of Tf (hK D u Ch chOf Tf)

open TensorProduct

def ExtLevL (Tf : FormsTiedSym D u Ch chOf) : Prop :=
  ∀ (κ : Tf.clsP.lev.U) (G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    IsExt D Tf.til.z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1 G.1 →
    G ∈ UPts (sigD D) (gramN D D.R.m le_rfl) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
    (∀ v, bc (prV (E := D.host.E) v) G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.Uloc v) ∧
    ∀ hG : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U,
      (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi ⟨G, hG⟩ : ℂˣ) : ℂ) = ((Tf.clsP.lev.chi κ : ℂˣ) : ℂ)

set_option maxHeartbeats 4000000 in
theorem extLevK_of (Tf : FormsTiedSym D u Ch chOf) (hL : ExtLevL Tf) : ExtLevK Tf := by
  intro κ
  obtain ⟨g, hg, hu⟩ := til_ext Tf (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) κ.1.1
  have hdet : IsUnit (κ.1.1).det := (Matrix.isUnit_iff_isUnit_det _).mp κ.1.isUnit
  obtain ⟨G, hGg⟩ : ∃ G : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), G.1 = g :=
    ⟨((Matrix.isUnit_iff_isUnit_det g).mpr (hu hdet)).unit, rfl⟩
  rw [← hGg] at hg
  have hκU := ((Tf.clsP.lev.U_eq κ.1).1 κ.2).1
  have hUP : G ∈ UPts (sigD D) (gramN D D.R.m le_rfl) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    extUA Tf κ.1.1 hκU G.1 hg
  obtain ⟨hloc, hchi⟩ := hL κ G hg hUP
  have hGU : G ∈ (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U := ((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U_eq G).2 ⟨hUP, hloc⟩
  exact ⟨⟨G, hGU⟩, hg, hchi hGU⟩

theorem forms_of_lattice_extension (hL : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i)
    (Tf : FormsTiedSym D u Ch chOf), ExtLevL Tf) : FormsCarriedToComplement :=
  forms_of_kernel_extension fun D u Ch chOf Tf => extLevK_of Tf (hL D u Ch chOf Tf)

end Close

end Formalism.L2.GlobalTheoryTheory.Br
