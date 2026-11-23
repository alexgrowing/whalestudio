import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivSymmPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixIntegralityFromCompletePointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowNormPosOfUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularMatrixChainPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularReversedChainPointsStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.VB GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Pad.Pull GlobalTheory.FieldPtGlue GlobalTheory.ChainPts
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TriFrame

section General

variable {X Z : Scheme.{0}} (h : X ⟶ Z)

theorem cls_pullLB (L : FinLB Z) : (pullLB h L).cls = CechPic.pull h L.cls :=
  (CechPic.cls_eq_iff _ (LB.isLB_pull L.isLB h)).2 (LBIso.chartPull (h := h) (A := L.lb) (B := L.lb)
    ⟨fun i => i, fun _ => le_rfl, fun y i j hi hj => by
      refine Eq.trans (congrArg _ (Units.ext ?_)) ((gm_pull (𝟙 X) h y (L.U i ⊓ L.U j) ⟨hi, hj⟩ (L.g i j)).trans (by
        rw [Category.id_comp]))
      exact congrArg (fun q => q.hom (L.g i j).val) (Scheme.Hom.appLE_eq_app h)⟩
    ⟨fun J => J PUnit.unit, fun _ _ h => mem_pull.1 h, fun y J J' h₁ h₂ =>
      (gm_pull_g L.lb h (𝟙 _) y J J' h₁ h₂).trans (by rw [Category.id_comp])⟩ ((CechPic.cls_eq_iff L.isLB L.isLB).1 rfl))

def pullFn (U : Z.Opens) (L : FinLB Z) (ρ : ∀ k, Γ(Z, U ⊓ L.U k)ˣ) (k : (pullLB h L).lb.ι) :
    Γ(X, h ⁻¹ᵁ U ⊓ (pullLB h L).lb.U k) :=
  (h.appLE (U ⊓ L.U k) (h ⁻¹ᵁ U ⊓ (pullLB h L).lb.U k) le_rfl).hom (ρ k).val

theorem valF_pullFn {U : Z.Opens} {L : FinLB Z} (ρ : ∀ k, Γ(Z, U ⊓ L.U k)ˣ) (k : (pullLB h L).lb.ι) {T : X.Opens}
    (e : T ≤ h ⁻¹ᵁ U ⊓ (pullLB h L).lb.U k) {F : Type} [Field F] {w : Sp F ⟶ X} (hw : ⊤ ≤ w ⁻¹ᵁ T) :
    valF w T (resG X e (pullFn h U L ρ k)) = valF (w ≫ h) _ (ρ k).val :=
  (valF_restrict e hw _).trans (valF_appLE h _ _ (hw.trans (w.preimage_mono e)) _)

theorem isGenOn_pullFn [IsReduced X] {U : Z.Opens} {L : FinLB Z} {ρ : ∀ k, Γ(Z, U ⊓ L.U k)ˣ}
    (H : ∀ (F : Type) [Field F] (w : Sp F ⟶ Z) k k', ⊤ ≤ w ⁻¹ᵁ (U ⊓ (L.U k ⊓ L.U k')) →
      valF w _ (ρ k').val = valF w _ (L.g k k').val * valF w _ (ρ k).val) :
    IsGenOn (h ⁻¹ᵁ U) (pullLB h L).lb (pullFn h U L ρ) := fun k k' T e e' e'' => section_ext _ _ fun F _ w hw => by
  rw [valF_mul hw, valF_pullFn h ρ k e hw, valF_pullFn h ρ k' e' hw,
    H F (w ≫ h) k k' fun q hq => ⟨(e (hw hq)).1, e'' (hw hq)⟩]
  exact congrArg (· * _) ((valF_restrict e'' hw _).trans (valF_appLE h _ _ (hw.trans (w.preimage_mono e'')) _)).symm

theorem isUnit_coef {F : X.Modules} {r : ℕ} (d : Bool) {V V' : X.Opens} {e : Fin r → Γ(F, V)} {s : Fin r → Γ(F, V')}
    (he : VB.IsFrame e) (hs : VB.IsFrame s) {k : Type} [Field k] {w : Sp k ⟶ X} (hw : ⊤ ≤ w ⁻¹ᵁ (V ⊓ V')) :
    IsUnit ((Matrix.of (coef d he hs)).map (valF w _)) := by
  have h₁ : IsUnit (Matrix.of (coef d he hs)) := by
    cases d
    · have := (he.basis inf_le_left).invertibleToMatrix (hs.basis (inf_le_right : V ⊓ V' ≤ V'))
      convert isUnit_of_invertible ((he.basis inf_le_left).toMatrix (hs.basis (inf_le_right : V ⊓ V' ≤ V'))) using 1
      ext l i
      rw [Module.Basis.toMatrix_apply, hs.basis_apply]
      rfl
    · have := (hs.basis inf_le_right).invertibleToMatrix (he.basis (inf_le_left : V ⊓ V' ≤ V))
      rw [← Matrix.isUnit_transpose]
      convert isUnit_of_invertible ((hs.basis inf_le_right).toMatrix (he.basis (inf_le_left : V ⊓ V' ≤ V))) using 1
      ext l i
      rw [Module.Basis.toMatrix_apply, he.basis_apply]
      rfl
  have h₂ := h₁.map (((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.comp (w.appLE _ ⊤ hw).hom).mapMatrix)
  convert h₂ using 1
  ext l i
  exact dif_pos hw

theorem exists_frame_le {F : X.Modules} {r : ℕ} (hF : IsVB F r) {x : X} {n : ℕ} {U : Fin n → X.Opens} (hU : ∀ i, x ∈ U i) :
    ∃ (V : X.Opens) (e : Fin r → Γ(F, V)), VB.IsFrame e ∧ x ∈ V ∧ ∀ i, V ≤ U i := by
  have ho : IsOpen (⋂ i, (U i : Set X)) := isOpen_iInter_of_finite fun i => (U i).isOpen
  obtain ⟨V, e, -, h₁, h₂, h₃⟩ := hF.exists_affine (V := ⟨_, ho⟩) (Set.mem_iInter.2 hU)
  exact ⟨V, e, h₃, h₁, fun i q hq => Set.mem_iInter.1 (h₂ hq) i⟩

end General

section Base

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B B₁ : Vert.Model O}

theorem exists_special (x : B.X) : ∃ x₀ : B.X, x ⤳ x₀ ∧ x₀ ∉ B.gen := by
  have hc : IsClosed (B.str '' closure {x}) := B.str.isClosedMap _ isClosed_closure
  obtain ⟨x₀, hx, e⟩ : closedPoint O ∈ B.str '' closure {x} :=
    (IsLocalRing.specializes_closedPoint (B.str x)).mem_closed hc ⟨x, subset_closure rfl, rfl⟩
  exact ⟨x₀, specializes_iff_mem_closure.2 hx, fun hq => hq e⟩

theorem eqn_pull {f : B₁.X ⟶ B.X} (hf : f ≫ B.str = B₁.str) (P : VertDiv B) (j : (P.pull hf).M.ι) {W : B₁.X.Opens}
    (h : W ≤ B₁.gen ⊓ (P.pull hf).M.U j) {V : B.X.Opens} (hV : V ≤ B.gen ⊓ P.M.U (j ⟨⟩)) (e : W ≤ f ⁻¹ᵁ V) :
    (P.pull hf).eqn j h = (f.appLE V W e).hom (P.eqn (j ⟨⟩) hV) := by
  rw [VertDiv.eqn, VertDiv.eqn, LB.appLE_resG]
  exact (LB.resG_resG _ _ _).trans (LB.resG_appLE f (LB.pull_inf_le f _ j) _ _)

theorem isRatio_pull {Z : NModel O} (c : Z.Comp) (f : Vert.Model.Hom B (Z.comp c)) {U : Z.X.Opens} {L L' : FinLB Z.X}
    (u : Z.GenIso L.lb L'.lb) (ρ : ∀ k, Γ(Z.X, U ⊓ L.U k)ˣ) (ρ' : ∀ k, Γ(Z.X, U ⊓ L'.U k)ˣ)
    (H : ∀ (F : Type) [Field F] (w : Sp F ⟶ Z.X) k k', ⊤ ≤ w ⁻¹ᵁ Z.gen → ⊤ ≤ w ⁻¹ᵁ (U ⊓ (L.U k ⊓ L'.U k')) →
      valF w _ (u.u k k').val * valF w _ (ρ k).val = valF w _ (ρ' k').val) :
    IsRatio ((f.f ≫ Z.compι c) ⁻¹ᵁ U) (((u.pair L.isLB L'.isLB).pull (Z.compι_str c)).pull f.comp_str)
      (pullLB (f.f ≫ Z.compι c) L).lb (pullLB (f.f ≫ Z.compι c) L').lb (pullFn _ U L ρ) (pullFn _ U L' ρ') := by
  intro x
  obtain ⟨k, hk⟩ := LB.mem_of_cover L.isLB ((f.f ≫ Z.compι c) x)
  obtain ⟨k', hk'⟩ := LB.mem_of_cover L'.isLB ((f.f ≫ Z.compι c) x)
  refine ⟨fun _ _ => (k, k'), k, k', mem_pull.2 (mem_pull.2 ⟨hk, hk'⟩), hk, hk', fun T h₁ h₂ h₃ =>
    section_ext _ _ fun F _ w hw => ?_⟩
  have g₁ : T ≤ f.f ⁻¹ᵁ ((Z.comp c).gen ⊓ ((u.pair L.isLB L'.isLB).pull (Z.compι_str c)).M.U fun _ => (k, k')) :=
    fun q hq => ⟨(Vert.Model.preimage_gen f.comp_str).ge (h₁ hq).1, mem_pull.1 (h₁ hq).2⟩
  have g₂ : (Z.comp c).gen ⊓ ((u.pair L.isLB L'.isLB).pull (Z.compι_str c)).M.U (fun _ => (k, k')) ≤
      Z.compι c ⁻¹ᵁ (Z.gen ⊓ (L.U k ⊓ L'.U k')) :=
    fun q hq => ⟨(NModel.preimage_gen (Z.compι_str c)).ge hq.1, mem_pull.1 hq.2⟩
  rw [valF_mul hw, valF_pullFn (f.f ≫ Z.compι c) ρ k h₂ hw, valF_pullFn (f.f ≫ Z.compι c) ρ' k' h₃ hw,
    eqn_pull f.comp_str _ _ h₁ le_rfl g₁,
    valF_appLE _ _ _ hw, NModel.VPair.eqn_pull (u.pair L.isLB L'.isLB) (Z.compι_str c) (fun _ => (k, k')) le_rfl le_rfl g₂,
    valF_appLE (x := w ≫ f.f) _ _ _ (fun q hq => g₁ (hw hq)), Category.assoc,
    ← H F (w ≫ f.f ≫ Z.compι c) k k' (fun q hq => (g₂ (g₁ (hw hq))).1)
      fun q hq => ⟨(h₂ (hw hq)).1, (h₂ (hw hq)).2, (h₃ (hw hq)).2⟩]
  exact congrArg (fun a => valF _ _ a * _) (LB.resG_self _ _)

end Base

section Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem grNorm_eq_matNorm {X : Scheme.{0}} {t : SAB H X} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    {x : Sp C ⟶ X} {Λ : Set (Sp (DualNumber C) ⟶ t.G.left)} {r : ℕ} {u : Fin r → (Sp (DualNumber C) ⟶ t.G.left)}
    (hu : ∀ i, IsTanAtG t x (u i)) {N : Matrix (Fin r) (Fin r) C}
    (h : ∀ cf v, IsCombAtG t x u cf v → (v ∈ Λ ↔ ∀ l, ‖∑ i, cf i * N l i‖ ≤ 1)) (σ : Fin r ≃ Fin r) (i : Fin r) :
    grNorm t x Λ (fun k => u (σ k)) i = matNorm (N.submatrix id σ) i := by
  obtain ⟨U, rfl⟩ := exists_tan hu
  have key (cf : Fin r → C) : (∃ w ∈ Λ, IsCombAtG t x (fun k => (tv (U (σ k))).left) cf w) ↔
      ∀ l, ‖∑ j, cf j * N.submatrix id σ l j‖ ≤ 1 := by
    have e := h (fun k => cf (σ.symm k)) _ ((comb_iff U _ _).2 rfl)
    rw [← σ.sum_comp] at e
    simp only [comb_iff (fun k => U (σ k)), exists_eq_right]
    simp only [Equiv.symm_apply_apply] at e
    refine e.trans (forall_congr' fun l => ?_)
    rw [← σ.sum_comp]
    simp only [Equiv.symm_apply_apply, Matrix.submatrix_apply, id]
  simp only [grNorm, matNorm, key]

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) {Z : LocM.Mdl Y i₀}

include hp hW

theorem norm_mul_matNorm {X : Scheme.{0}} {h : X ⟶ Z.X} {r : ℕ} {x : Fin r → Letter Dw} {d b : Bool} {F : X.Modules}
    {s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)} (hF : IsLat Z h x d b F s)
    {st : Fin r → ((E →+* ℂ) × ℕ) ⊕ ℕ} (M : ∀ i, LineModel Z b (st i) (x i)) (σ : Fin r ≃ Fin r)
    (hN : StepNorms Dw p (fun i => st (σ i)) fun i => x (σ i)) (a : Fin Z.m) {V : X.Opens} {e : Fin r → Γ(F, V)}
    (he : VB.IsFrame e) (C : SCF p) (w : Sp ↥(intO ↥C.S) ⟶ X) (hV : ⊤ ≤ w ⁻¹ᵁ V)
    (ha : ⊤ ≤ (spMap (intO ↥C.S).subtype ≫ w) ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a).1)) (i : Fin r) (k : Fin (M (σ i)).L.n)
    (hk : V ≤ h ⁻¹ᵁ (M (σ i)).L.U k) :
    ‖valF ((spMap (intO ↥C.S).subtype ≫ w) ≫ h) _ ((M (σ i)).r a k).val‖ *
      matNorm (((Matrix.of (coef d he (hF.frame a))).map (valF (spMap (intO ↥C.S).subtype ≫ w) _)).submatrix id σ) i = 1 := by
  obtain ⟨φ, hφ⟩ := exists_fromSpec (Z.U a).2 (spMap (intO ↥C.S).subtype ≫ w ≫ h) ha
  replace hφ : spMap φ ≫ Z.chart a = spMap (intO ↥C.S).subtype ≫ w ≫ h := hφ
  obtain ⟨Q, hQ⟩ := ModelPt.exists_ptC E H Dw Xo p W Y i₀ hp hW Z C (w ≫ h) (range_opn Z hφ)
  let y : Z.Pt := ⟨C, Q, w ≫ h, hQ⟩
  have hV' : ⊤ ≤ (spMap (intO ↥C.S).subtype ≫ w) ⁻¹ᵁ V := fun q _ => hV (Set.mem_univ (spMap (intO ↥C.S).subtype q))
  have n := (M (σ i)).norm y a k φ hφ fun q hq => hk (hV hq)
  rw [hN _ _ _ _ _ b i, grNorm_eq_matNorm (u := fun i => (Z.fr a).bc φ (x i).1 (x i).2)
    (N := (Matrix.of (coef d he (hF.frame a))).map (valF (spMap (intO ↥C.S).subtype ≫ w) _))
    (fun i => ((chart_frame Z (w := y.gen) hφ).1 _ _).1) (hF.norm y w rfl a φ hφ V e he hV) σ i] at n
  have pos := GlobalTheory.T.matrix_row_norm_pos_of_unit _ r _ ((Matrix.isUnit_submatrix_equiv (Equiv.refl _) σ).2
    (isUnit_coef d he (hF.frame a) (w := spMap (intO ↥C.S).subtype ≫ w) fun q hq => ⟨hV' hq, ha hq⟩)) i
  rw [Equiv.coe_refl] at pos
  have r0 := norm_pos_iff.2 (GenId.val_ne_zero (M (σ i)) (w := y.gen) (a := a) (i := k) ha fun q hq => hk (hV' hq))
  rw [← Real.log_mul r0.ne' pos.ne', Real.log_eq_zero] at n
  rw [Category.assoc]
  exact (n.resolve_left (mul_pos r0 pos).ne').resolve_right (by linarith [mul_pos r0 pos])

variable [IsDiscreteValuationRing (Z.i.c.V W)] {B : Vert.Model (Z.i.c.V W)} (hB : GlobalTheory.IsNormalScheme B.X) {h : B.X ⟶ Z.X}
  {r : ℕ} {x : Fin r → Letter Dw} {b : Bool} {F : B.X.Modules} {s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)}
  {st : Fin r → ((E →+* ℂ) × ℕ) ⊕ ℕ} (M : ∀ i, LineModel Z b (st i) (x i)) {a : Fin Z.m}
  (ha : genericPoint B.X ∈ h ⁻¹ᵁ (Z.U a).1) (hvb : IsVB F r)

include hB ha hvb

theorem exists_triangular {d : Bool} (hF : IsLat Z h x d b F s) (σ : Fin r ≃ Fin r)
    (hN : StepNorms Dw p (fun i => st (σ i)) fun i => x (σ i)) (q : B.X) :
    ∃ (V V' : B.X.Opens) (hV : V' ≤ V) (e : Fin r → Γ(F, V)) (he : VB.IsFrame e) (k : ∀ i, Fin (M i).L.n)
      (hk : ∀ i, V' ≤ h ⁻¹ᵁ (M i).L.U (k i)) (P : GL (Fin r) Γ(B.X, V')), q ∈ V' ∧
      (∀ l j, j < l → ((P : Matrix (Fin r) (Fin r) Γ(B.X, V')).map (resG B.X (inf_le_left : V' ⊓ h ⁻¹ᵁ (Z.U a).1 ≤ V')) *
        (Matrix.of fun l j => coef d he (hF.frame a) l (σ j)).map (resG B.X (inf_le_inf_right _ hV))) l j = 0) ∧
      ∀ j, ((P : Matrix (Fin r) (Fin r) Γ(B.X, V')).map (resG B.X (inf_le_left : V' ⊓ h ⁻¹ᵁ (Z.U a).1 ≤ V')) *
        (Matrix.of fun l j => coef d he (hF.frame a) l (σ j)).map (resG B.X (inf_le_inf_right _ hV))) j j *
          resG B.X (le_inf inf_le_right (inf_le_left.trans (hk (σ j))))
            (pullFn h (Z.U a).1 (M (σ j)).L ((M (σ j)).r a) (k (σ j))) = 1 := by
  refine (exists_special q).elim fun q₀ ⟨hq, hq₀⟩ => ?_
  have hk : ∃ k : ∀ i, Fin (M i).L.n, ∀ i, q₀ ∈ h ⁻¹ᵁ (M i).L.U (k i) :=
    Classical.skolem.1 fun i => LB.mem_of_cover (M i).L.isLB (h q₀)
  refine hk.elim fun k hk => ?_
  refine (exists_frame_le hvb hk).elim fun V ⟨e, he, hqV, hVk⟩ => ?_
  have := Fact.mk hp
  have := charP_residueField_of_mem_nonunits Z.i.c hp hW
  have c₁ : (p : Z.i.c.V W) ∈ maximalIdeal (Z.i.c.V W) := natCast_mem_maximalIdeal _ p
  have c₂ : Cardinal.mk (Z.i.c.V W) ≤ Cardinal.continuum :=
    (Cardinal.mk_subtype_le _).trans ((Cardinal.mk_subtype_le _).trans Cardinal.mk_complex.le)
  have key := GlobalTheory.T.matrix_integrality_from_complete_points p hp (Z.i.c.V W) c₁ c₂ B hB (h ⁻¹ᵁ (Z.U a).1) V q₀ ha hqV hq₀ r
    (Matrix.of fun l j => coef d he (hF.frame a) l (σ j))
    fun j => resG B.X (le_inf inf_le_right (inf_le_left.trans (hVk (σ j))))
      (pullFn h (Z.U a).1 (M (σ j)).L ((M (σ j)).r a) (k (σ j)))
  refine (key fun C w hw hw' i => ?_).elim fun V' ⟨hV, P, h₁, h₂, h₃⟩ =>
    ⟨V, V', hV, e, he, k, fun i => hV.trans (hVk i), P, hq.mem_open V'.isOpen h₁, h₂, fun j => ?_⟩
  · have hw₁ : ⊤ ≤ (spMap (intO ↥C.S).subtype ≫ w) ⁻¹ᵁ (V ⊓ h ⁻¹ᵁ (Z.U a).1) :=
      fun q hq => ⟨hw (Set.mem_univ (spMap (intO ↥C.S).subtype q)), hw' hq⟩
    have e₁ := valF_pullFn h ((M (σ i)).r a) (k (σ i)) (le_inf inf_le_right (inf_le_left.trans (hVk (σ i)))) hw₁
    have e₂ := norm_mul_matNorm hp hW hF M σ hN a he C w hw hw' i _ (hVk _)
    rw [← e₁] at e₂
    exact e₂
  · have h₄ := h₃ j
    rw [LB.resG_resG] at h₄
    exact h₄

theorem tri_lie (hF : IsLat Z h x false b F s) (hN : StepNorms Dw p st x) :
    Tri (hF.frame a) (fun i => (pullLB h (M i).L).lb) fun i => pullFn h (Z.U a).1 (M i).L ((M i).r a) := fun q => by
  obtain ⟨V, V', hV, e, he, k, hk, P, h₁, h₂, h₃⟩ := exists_triangular hp hW hB M ha hvb hF (Equiv.refl _) hN q
  obtain ⟨e', a₁, a₂, a₃⟩ := GlobalTheory.T.triangular_matrix_chain_points B.X _ V V' hV F r _ (hF.frame a) e he P _ h₂ h₃
  exact ⟨V', e', k, hk, h₁, a₁, a₂, a₃⟩

theorem tri_dual (hF : IsLat Z h x true b F s) (hN : StepNorms Dw p (fun i => st i.rev) fun i => x i.rev) :
    Tri (hF.frame a) (fun i => (pullLB h (M i).L.dual).lb) fun i => pullFn h (Z.U a).1 (M i).L.dual fun k => ((M i).r a k)⁻¹ :=
    fun q => by
  obtain ⟨V, V', hV, e, he, k, hk, P, h₁, h₂, h₃⟩ := exists_triangular hp hW hB M ha hvb hF Fin.revPerm hN q
  obtain ⟨e', a₁, a₂, a₃⟩ := GlobalTheory.T.triangular_reversed_chain_points B.X _ V V' hV F r _ (hF.frame a) e he P _ h₂ h₃
  refine ⟨V', e', k, hk, h₁, a₁, a₂, fun i => ?_⟩
  have a₄ := a₃ i
  have a₅ (j : Fin r) (hj : j = i) : resG B.X (le_inf inf_le_right (inf_le_left.trans (hk j)) : V' ⊓ h ⁻¹ᵁ (Z.U a).1 ≤ _)
      (pullFn h (Z.U a).1 (M j).L ((M j).r a) (k j)) * resG B.X (le_inf inf_le_right (inf_le_left.trans (hk i)))
      (pullFn h (Z.U a).1 (M i).L.dual (fun k => ((M i).r a k)⁻¹) (k i)) = 1 := by
    subst hj
    refine (map_mul _ _ _).symm.trans ((congrArg _ ((map_mul _ _ _).symm.trans ?_)).trans (map_one _))
    rw [Units.mul_inv]
    exact map_one _
  exact left_inv_eq_right_inv a₄ (a₅ _ (Fin.rev_rev i))

end Lattices

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p} {Z : LocM.Mdl Y i₀} [IsDiscreteValuationRing (Z.i.c.V W)]

theorem exists_chart (c : (nmodel Z).Comp) {B : Vert.Model (Z.i.c.V W)} (f : Vert.Model.Hom B ((nmodel Z).comp c)) :
    ∃ a, genericPoint B.X ∈ (f.f ≫ (nmodel Z).compι c) ⁻¹ᵁ (Z.U a).1 := by
  obtain ⟨y, hy, hy'⟩ := Z.dense.inter_open_nonempty _ c.opens.isOpen c.2.1.1
  rw [← Z.cover] at hy'
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hy'
  have := f.surjective
  obtain ⟨q, hq⟩ := f.f.surjective (⟨y, hy⟩ : c.opens.toScheme)
  refine ⟨a, VB.genericPoint_mem (x := q) ?_⟩
  change (nmodel Z).compι c (f.f q) ∈ (Z.U a).1
  rw [hq]
  exact ha

theorem firstChernClassTateTwist_pullback (c : (nmodel Z).Comp) {B : Vert.Model (Z.i.c.V W)} (f : Vert.Model.Hom B ((nmodel Z).comp c))
    (L : FinLB Z.X) {N : LB B.X} (hN : N.IsLB)
    (e : CechPic.cls N hN = CechPic.cls _ (pullLB (f.f ≫ (nmodel Z).compι c) L).isLB) :
    picSymPull f.f (picSymPull ((nmodel Z).compι c) L.c1) = c1 N hN := by
  rw [FinLB.c1_eq, picSymPull_c1Pic, picSymPull_c1Pic, ← CechPic.pull_comp, ← firstChernPic_class, e]
  exact congrArg firstChernPic (cls_pullLB _ L).symm

end Main

end GlobalTheory.TriFrame

end
