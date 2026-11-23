import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsChartOfMaximal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMemNonunitsOfInduces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentFamilyOfUniqueLiftPrime
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

namespace admitted

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (z : admitted Y i₀)

def stepLB (b : Bool) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : FinLB z.Z.X :=
  match h : letterOf Dw st with
  | some x => (z.line b st x h).L
  | none => FinLB.triv _

theorem stepLB_of_some (b : Bool) {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (h : letterOf Dw st = some x) :
    z.stepLB b st = (z.line b st x h).L := by
  unfold stepLB
  split
  · next y hy => obtain rfl : y = x := Option.some.inj (hy.symm.trans h); rfl
  · next hy => exact absurd (hy.symm.trans h) (by simp)

def rootLB (b : Bool) (τ : E →+* ℂ) (i : ℕ) : FinLB z.Z.X :=
  if i < Dw.p then z.stepLB b (.inl (τ, i)) else (z.stepLB b (.inl (conjEmb τ, Dw.p + Dw.q - 1 - i))).dual

variable (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)

section Step

variable {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (h : letterOf Dw st = some x)

def genId : GenIso z.Z (z.line false st x h).L (z.line true st x h).L :=
  (exists_isGenId hp hW z.full (GenId.bdd_step hp st) _ _).choose

theorem isGenId_genId : IsGenId (z.line false st x h) (z.line true st x h) (z.genId hp hW h) :=
  (exists_isGenId hp hW z.full (GenId.bdd_step hp st) _ _).choose_spec

theorem log_norm_genId (y : z.Z.Pt) (a : Fin z.Z.m) (φ : Γ(z.Z.X, (z.Z.U a).1) →+* ↥y.C.S)
    (hφ : spMap φ ≫ z.Z.chart a = y.gen) {i j} (hi : ⊤ ≤ y.z ⁻¹ᵁ (z.line false st x h).L.U i)
    (hj : ⊤ ≤ y.z ⁻¹ᵁ (z.line true st x h).L.U j) :
    Real.log ‖valF y.gen _ ((z.genId hp hW h).u i j).val‖ =
      lnStep (Y z.Z.i).t (y.gen ≫ z.Z.π) ((z.Z.fr a).bc φ) p false st -
        lnStep (Y z.Z.i).t (y.gen ≫ z.Z.π) ((z.Z.fr a).bc φ) p true st := by
  have ha := Pull.le_of_fromSpec (z.Z.U a).2 hφ
  have hi' : ⊤ ≤ y.gen ⁻¹ᵁ (z.line false st x h).L.U i := fun q _ => hi (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
  have hj' : ⊤ ≤ y.gen ⁻¹ᵁ (z.line true st x h).L.U j := fun q _ => hj (Set.mem_univ (spMap (intO ↥y.C.S).subtype q))
  have e := z.isGenId_genId hp hW h _ y.gen a i j fun q hq => ⟨ha hq, hi' hq, hj' hq⟩
  have n := GenId.val_ne_zero _ ha hj'
  have e' := congrArg (fun c => Real.log ‖c‖) e
  rw [← e] at n
  simp only [norm_mul] at e'
  rw [Real.log_mul (norm_ne_zero_iff.2 (left_ne_zero_of_mul n)) (norm_ne_zero_iff.2 (right_ne_zero_of_mul n))] at e'
  linarith [(z.line false st x h).norm y a i φ hφ hi, (z.line true st x h).norm y a j φ hφ hj]

end Step

variable (d : ℕ) {r : ℕ} {st : Fin r → ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Fin r → Letter Dw}
  (h : ∀ i, letterOf Dw (st i) = some (x i))

def stepPair : DV.FPair (ithOf hp hW z.Z d) r :=
  fpairOf hp hW d (fun i => (z.line false _ _ (h i)).L) (fun i => (z.line true _ _ (h i)).L) fun i => z.genId hp hW (h i)

def dualPair : DV.FPair (ithOf hp hW z.Z d) r :=
  fpairOf hp hW d (fun i => (z.line false _ _ (h i)).L.dual) (fun i => (z.line true _ _ (h i)).L.dual)
    fun i => NModel.GenIso.dual (z.genId hp hW (h i))

theorem pair_x_eq_LB_false (i : Fin r) : (z.stepPair hp hW d h).x i = z.stepLB false (st i) := (z.stepLB_of_some _ _).symm

theorem pair_x_prime_eq_LB_true (i : Fin r) : (z.stepPair hp hW d h).x' i = z.stepLB true (st i) := (z.stepLB_of_some _ _).symm

theorem dualPair_x_eq_dual_LB_false (i : Fin r) : (z.dualPair hp hW d h).x i = (z.stepLB false (st i)).dual :=
  congrArg FinLB.dual (z.stepLB_of_some _ _).symm

theorem dualPair_x_prime_eq_dual_LB_true (i : Fin r) : (z.dualPair hp hW d h).x' i = (z.stepLB true (st i)).dual :=
  congrArg FinLB.dual (z.stepLB_of_some _ _).symm

theorem dualPair_Dv (i : Fin r) : (z.dualPair hp hW d h).Dv i = -vdiv hp hW d _ _ (z.genId hp hW (h i)) :=
  vdiv_dual hp hW d _ _ _

omit hp

variable [Fact p.Prime]

include hW

end admitted

section Ranks

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) {p : ℕ} [Fact p.Prime] (jc : DV.KW p →+* ℂ)

theorem comp_cEmb (τ : DV.Emb D p) : jc.comp (DV.cEmb D τ) = conjEmb (jc.comp τ) :=
  RingHom.ext fun x => Formalism.MainNotions.WeightFamilies.emb_conj D (jc.comp τ) x

theorem mult_comp (τ : DV.Emb D p) : S.Dw.mult (jc.comp τ) = DV.rkOf (DV.PsiOf D jc) N j τ := by
  have h₁ := S.p_eq
  have h₂ := S.rank_eq
  by_cases h : τ ∈ DV.PsiOf D jc
  · obtain ⟨t, ht⟩ := id h
    rw [DV.rkOf, if_pos h, ht, Datum.mult, if_pos (A.cm t), h₁]
  · obtain ⟨t, ht⟩ : DV.cEmb D τ ∈ DV.PsiOf D jc := by_contra fun h' => h ((cm_type_meets_conjugate_pair p jc τ).2 h')
    have h₃ := GlobalTheory.Proof.LetterConjugation.mult_add S.Dw (jc.comp τ)
    rw [← comp_cEmb, ht, Datum.mult.eq_1 _ (DV.tauEmb D t), if_pos (A.cm t)] at h₃
    rw [DV.rkOf, if_neg h]
    omega

theorem mult_conj_comp (τ : DV.Emb D p) : S.Dw.mult (conjEmb (jc.comp τ)) = N - DV.rkOf (DV.PsiOf D jc) N j τ := by
  have h₁ := GlobalTheory.Proof.LetterConjugation.mult_add S.Dw (jc.comp τ)
  have h₂ := S.rank_eq
  rw [mult_comp] at h₁
  omega

theorem length_letters : (letters S.Dw).length = D.R.f * N := by
  have h := GlobalTheory.Proof.LetterConjugation.two_mul_length S.Dw
  rw [GlobalTheory.Proof.LetterConjugation.finrank_host, S.rank_eq, mul_assoc] at h
  omega

theorem letterOf_lie (τ : DV.Emb D p) (i : Fin (DV.rkOf (DV.PsiOf D jc) N j τ)) :
    letterOf S.Dw (.inl (jc.comp τ, i)) = some ⟨jc.comp τ, i.cast (mult_comp S jc τ).symm⟩ :=
  dif_pos (i.cast (mult_comp S jc τ).symm).2

theorem letterOf_om (τ : DV.Emb D p) (i : Fin (N - DV.rkOf (DV.PsiOf D jc) N j τ)) :
    letterOf S.Dw (.inl (conjEmb (jc.comp τ), i.rev)) =
      some ⟨conjEmb (jc.comp τ), i.rev.cast (mult_conj_comp S jc τ).symm⟩ :=
  dif_pos (i.rev.cast (mult_conj_comp S jc τ).symm).2

theorem letterOf_whole (k : Fin (D.R.f * N)) :
    letterOf S.Dw (.inr k) = some ((letters S.Dw).get (k.cast (length_letters S).symm)) :=
  List.getElem?_eq_getElem (k.cast (length_letters S).symm).2

end Ranks

section Mdl

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
  {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : DV.KW p →+* ℂ)

def mdlOf : DV.Mdl D p N (DV.rkOf (DV.PsiOf D jc) N j) where
  Z := ithOf hp hW z.Z (Formalism.DegreeFormula.dimFl D.what₂.Tau N)
  cov := cov z
  cov_pos := cov_pos z
  lvl := z.n
  lie τ := z.stepPair hp hW _ (letterOf_lie S jc τ)
  om τ := z.dualPair hp hW _ (letterOf_om S jc τ)
  lieW := z.stepPair hp hW _ (letterOf_whole S)
  omW := z.dualPair hp hW _ fun k => letterOf_whole S k.rev
  om_dual τ := ⟨Fin.revPerm.trans (finCongr (by rw [← mult_conj_comp S, ← mult_comp S, comp_cEmb])), fun i => by
    rw [admitted.dualPair_x_eq_dual_LB_false, admitted.pair_x_eq_LB_false]
    exact (FinLB.firstChern_dual _).trans
      (congrArg (fun σ => -(admitted.stepLB z false (.inl (σ, i.rev))).c1) (comp_cEmb jc τ).symm)⟩
  dim_eq := rfl
  omW_dual := ⟨Fin.revPerm, fun _ => FinLB.firstChern_dual _⟩

theorem mdlOf_lie (τ : DV.Emb D p) (i) : ((mdlOf z jc).lie τ).x i = z.stepLB false (.inl (jc.comp τ, i)) ∧
    ((mdlOf z jc).lie τ).x' i = z.stepLB true (.inl (jc.comp τ, i)) :=
  ⟨z.pair_x_eq_LB_false hp hW _ _ i, z.pair_x_prime_eq_LB_true hp hW _ _ i⟩

theorem mdlOf_om (τ : DV.Emb D p) (i) :
    ((mdlOf z jc).om τ).x i = (z.stepLB false (.inl (conjEmb (jc.comp τ), i.rev))).dual ∧
    ((mdlOf z jc).om τ).x' i = (z.stepLB true (.inl (conjEmb (jc.comp τ), i.rev))).dual :=
  ⟨z.dualPair_x_eq_dual_LB_false hp hW _ _ i, z.dualPair_x_prime_eq_dual_LB_true hp hW _ _ i⟩

theorem mdlOf_lieW (k) : (mdlOf z jc).lieW.x k = z.stepLB false (.inr k) ∧
    (mdlOf z jc).lieW.x' k = z.stepLB true (.inr k) :=
  ⟨z.pair_x_eq_LB_false hp hW _ _ k, z.pair_x_prime_eq_LB_true hp hW _ _ k⟩

theorem mdlOf_omW (k) : (mdlOf z jc).omW.x k = (z.stepLB false (.inr k.rev)).dual ∧
    (mdlOf z jc).omW.x' k = (z.stepLB true (.inr k.rev)).dual :=
  ⟨z.dualPair_x_eq_dual_LB_false hp hW _ _ k, z.dualPair_x_prime_eq_dual_LB_true hp hW _ _ k⟩

theorem mdlOf_lie_Dv (τ : DV.Emb D p) (i) :
    ((mdlOf z jc).lie τ).Dv i = vdiv hp hW _ _ _ (z.genId hp hW (letterOf_lie S jc τ i)) := rfl

theorem mdlOf_om_Dv (τ : DV.Emb D p) (i) :
    ((mdlOf z jc).om τ).Dv i = -vdiv hp hW _ _ _ (z.genId hp hW (letterOf_om S jc τ i)) :=
  z.dualPair_Dv hp hW _ _ i

theorem mdlOf_omW_Dv (k) : (mdlOf z jc).omW.Dv k = -(mdlOf z jc).lieW.Dv k.rev := z.dualPair_Dv hp hW _ _ k

def rootOf (x : Bool × DV.Rt D.what₂.Tau N) : (mdlOf z jc).Z.LB := z.rootLB x.1 (DV.tauEmb D x.2.1) x.2.2

variable {jc} {t : D.what₂.Tau} {τ : DV.Emb D p} (ht : jc.comp τ = DV.tauEmb D t)

include ht

theorem rootOf_lie (i : Fin (DV.rkOf (DV.PsiOf D jc) N j τ)) (i' : Fin N) (h : (i' : ℕ) = i) :
    rootOf z jc (false, (t, i')) = ((mdlOf z jc).lie τ).x i ∧ rootOf z jc (true, (t, i')) = ((mdlOf z jc).lie τ).x' i := by
  have hi : (i' : ℕ) < S.Dw.p := by
    have hr : DV.rkOf (DV.PsiOf D jc) N j τ = j := if_pos ⟨t, ht⟩
    have := i.2
    have := S.p_eq
    omega
  rw [(mdlOf_lie z jc τ i).1, (mdlOf_lie z jc τ i).2, ht, ← h]
  exact ⟨if_pos hi, if_pos hi⟩

theorem rootOf_om (i : Fin (N - DV.rkOf (DV.PsiOf D jc) N j τ)) (i' : Fin N) (h : (i' : ℕ) = j + i) :
    rootOf z jc (false, (t, i')) = ((mdlOf z jc).om τ).x i ∧ rootOf z jc (true, (t, i')) = ((mdlOf z jc).om τ).x' i := by
  have hr : DV.rkOf (DV.PsiOf D jc) N j τ = j := if_pos ⟨t, ht⟩
  have h₁ := S.p_eq
  have h₂ := S.rank_eq
  have hi : ¬ (i' : ℕ) < S.Dw.p := by omega
  have e : (i.rev : ℕ) = S.Dw.p + S.Dw.q - 1 - i' := by rw [Fin.val_rev]; omega
  rw [(mdlOf_om z jc τ i).1, (mdlOf_om z jc τ i).2, ht, e]
  exact ⟨if_neg hi, if_neg hi⟩

end Mdl

section PiLocalization₂

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) (κ : Lv A)
  (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ))
  (hj : ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la))

theorem one_add_lt_three {p : ℕ} (hp : p.Prime) : 1 + 1 / ((p : ℝ) - 1) < (3 : ℕ) := by
  have h : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : 1 / ((p : ℝ) - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  push_cast
  linarith

abbrev AdmPl (p : ℕ) [Fact p.Prime] (la : PlL D p) : Type :=
  AdmAt S κ Fact.out (placeW_over D p la (jC p la) (hj p la)).1

def admissible_representation_factorisation (hA : AdmEx S κ) : AdmSt D N j jC where
  admitted p _ la := AdmPl S κ jC hj p la
  mdl p _ la z := mdlOf z (jC p la)
  Crv _ _ _ z := Crv z
  deg _ _ _ z c x := degRoot z c (DV.tauEmb D x.1) x.2
  ht p _ _ := (hA p Fact.out _ _ 3 (one_add_lt_three Fact.out)).choose

variable (hA : AdmEx S κ) (p : ℕ) [Fact p.Prime] (la : PlL D p)

end PiLocalization₂

section Examples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)

example (z : admitted Y i₀) {τ : E →+* ℂ} (hτ : τ (H.rt : E) ≠ H.rt0) (k : Fin (Dw.mult τ))
    (h : letterOf Dw (.inl (τ, k)) = some ⟨τ, k⟩) (y : z.Z.Pt) (a : Fin z.Z.m) (φ : Γ(z.Z.X, (z.Z.U a).1) →+* ↥y.C.S)
    (hφ : spMap φ ≫ z.Z.chart a = y.gen) {i j} (hi : ⊤ ≤ y.z ⁻¹ᵁ (z.line false _ _ h).L.U i)
    (hj : ⊤ ≤ y.z ⁻¹ᵁ (z.line true _ _ h).L.U j) : 0 ≤ Real.log ‖valF y.gen _ ((z.genId hp hW h).u i j).val‖ := by
  have g : y.gen ≫ z.Z.π = spMap (intO ↥y.C.S).subtype ≫ y.z ≫ z.Z.π := Category.assoc _ _ _
  have F := Pull.frame_ind (Pull.chart_frame z.Z hφ) τ
  rw [z.log_norm_genId hp hW h y a φ hφ hi hj]
  simp only [lnStep, dif_pos k.2, hτ, and_false, if_false, sub_zero, sub_nonneg]
  rw [g] at F ⊢
  have pos (b) := GlobalTheory.GrNormPos.grNorm_pos HTBound.htBound E H _ _ p y.C b _ hp (Pull.ext_unique _ _) _ _ F.1 F.2 k
  refine Real.log_le_log (pos true) (csInf_le_csInf ⟨0, ?_⟩ ?_ ?_)
  · rintro r ⟨cf, -, -, -, rfl⟩
    positivity
  · exact Set.nonempty_iff_ne_empty.2 fun e => (pos false).ne' ((congrArg sInf e).trans Real.sInf_empty)
  · rintro r ⟨cf, h₁, h₂, ⟨w, hw, hc⟩, rfl⟩
    exact ⟨cf, h₁, h₂, ⟨w, latDR_subset_latHT E H _ _ _ p _ hw, hc⟩, rfl⟩

example {Z : LocM.Mdl Y i₀} {b st x} (M : LineModel Z b st x) (u : GenIso Z M.L M.L) (h : IsGenId M M u) (d : ℕ) :
    vdiv hp hW d _ _ u = 0 := by
  have := isDiscreteValuationRing_V Z.i.c hp hW
  have e : IsGenId M M (.ofGlobal (idIso _) (idIso_isGen M.L.isLB)) := fun k _ w a i j hw => by
    have hw' : ⊤ ≤ w ⁻¹ᵁ ((nmodel Z).gen ⊓ (M.L.U i ⊓ M.L.U j)) := fun q hq => ⟨chart_le_gen hp hW a (hw hq).1, (hw hq).2⟩
    rw [M.trans k w a i j hw]
    exact congrArg (· * _) (FieldPtGlue.valF_restrict _ hw' _)
  rw [h.unique hp hW e]
  exact (congrArg NModel.toQ (NModel.GenIso.div_ofGlobal _ _ _ _)).trans (map_zero _)

example {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} [Fact p.Prime] (z : AdmAt S κ hp hW)
    (jc : DV.KW p →+* ℂ) (h : 0 < D.R.f * N) : (mdlOf z jc).Z.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1 ∧
      (mdlOf z jc).omW.x ⟨0, h⟩ = (z.stepLB false (.inr (D.R.f * N - 1))).dual :=
  ⟨rfl, (mdlOf_omW z jc _).1⟩

end Examples

end GlobalTheory.ShFam.Pad
