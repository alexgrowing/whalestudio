import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EtDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open CH PAlg

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C] [Category.{0} C']

theorem subMor_cup {A : C ⥤ CommAlgCat.{0} R} {A' : C' ⥤ CommAlgCat.{0} R'} (m : CH.Mor (modF A) (modF A') σ)
    (hm : ∀ (T : C') (x y : A.obj (m.G.obj T)), m.τ T (x * y) = (show A'.obj T from m.τ T x) * (show A'.obj T from m.τ T y))
    {S₁ S₂ S₃ : SubF (modF A)} {S₁' S₂' S₃' : SubF (modF A')} (h₁ h₂ h₃) (hS hS') {p q n : ℕ} (h : p + q = n)
    (x : H S₁.fn p) (y : H S₂.fn q) :
    (subMor m S₃ S₃' h₃).pull n ((subPair S₁ S₂ S₃ hS).cup h x y) =
      (subPair S₁' S₂' S₃' hS').cup h ((subMor m S₁ S₁' h₁).pull p x) ((subMor m S₂ S₂' h₂).pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (subPair S₁ S₂ S₃ hS) (subPair S₁' S₂' S₃' hS') m.G (subMor m S₁ S₁' h₁).τ (subMor m S₂ S₂' h₂).τ
    (subMor m S₃ S₃' h₃).τ (subMor m S₁ S₁' h₁).nat (subMor m S₂ S₂' h₂).nat (subMor m S₃ S₃' h₃).nat
    (fun T x y => Subtype.ext (hm T _ _)) h x y

theorem mulTo_cup {A : C ⥤ CommAlgCat.{0} R} {c₁ c₂ c₃ : R} (hc : c₃ = c₁ * c₂) {S₁ S₂ S₃ : SubF (modF A)} (h₁ h₂ h₃) (hS)
    {p q n : ℕ} (h : p + q = n) (x : H (modF A) p) (y : H (modF A) q) :
    (mulTo c₃ S₃ h₃).pull n ((mulP A).cup h x y) =
      (subPair S₁ S₂ S₃ hS).cup h ((mulTo c₁ S₁ h₁).pull p x) ((mulTo c₂ S₂ h₂).pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (mulP A) (subPair S₁ S₂ S₃ hS) (𝟭 C) (mulTo c₁ S₁ h₁).τ (mulTo c₂ S₂ h₂).τ
    (mulTo c₃ S₃ h₃).τ (mulTo c₁ S₁ h₁).nat (mulTo c₂ S₂ h₂).nat (mulTo c₃ S₃ h₃).nat
    (fun T (x y : A.obj T) => Subtype.ext (show c₃ • (x * y) = (c₁ • x) * (c₂ • y) by rw [hc, smul_mul_smul_comm])) h x y

theorem subMor_one {A : C ⥤ CommAlgCat.{0} R} {A' : C' ⥤ CommAlgCat.{0} R'} (m : CH.Mor (modF A) (modF A') σ)
    (hm : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) {c : R} {c' : R'} (hc : c = 1) (hc' : c' = 1)
    {S : SubF (modF A)} {S' : SubF (modF A')} (h h₁ h₂) :
    (subMor m S S' h).pull 0 ((mulTo c S h₁).pull 0 (CH.oneH A)) = (mulTo c' S' h₂).pull 0 (CH.oneH A') := by
  subst hc hc'
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change m.τ _ ((1 : R) • (1 : A.obj _)) = (1 : R') • (1 : A'.obj _)
  rw [one_smul, one_smul, hm]

end Gen

section Pd
variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R}
  {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ) (σ₀ : Λ →+* Λ') (hσ : ∀ a, σ (c a) = c' (σ₀ a))

theorem pdOm_cup {r r' s : ℕ} (e : r + r' = s) {p q n : ℕ} (h : p + q = n) (x : H (B.pdS L c r).fn p) (y : H (B.pdS L c r').fn q) :
    (pdOm m σ₀ hσ s).pull n ((pdPair L c e).cup h x y) =
      (pdPair L' c' e).cup h ((pdOm m σ₀ hσ r).pull p x) ((pdOm m σ₀ hσ r').pull q y) :=
  subMor_cup (A := B.OA L c) (A' := B.OA L' c') (B.omMor m σ₀ hσ) (fun _ _ _ => rfl) _ _ _ _ _ h x y

theorem pdOm_one : (pdOm m σ₀ hσ 0).pull 0 (pdOne L c) = pdOne L' c' :=
  subMor_one (A := B.OA L c) (A' := B.OA L' c') (B.omMor m σ₀ hσ) (fun _ => rfl) rfl rfl _ _ _

end Pd

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def ttPair (P : PAlg l ⥤ Type) (n : ℕ) {r r' s : ℕ} (h : r + r' = s) : Pairing (TT P r n).fn (TT P r' n).fn (TT P s n).fn :=
  subPair (A := AcrEl P n) (TT P r n) (TT P r' n) (TT P s n) fun T x y hx hy =>
    mem_TT.2 (h ▸ dividedPowerFiltration_mul (B.DD false T.1.obj n) r r' (mem_TT.1 hx) (mem_TT.1 hy))

section F
variable {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l)

theorem βF_cup (n : ℕ) {r r' s : ℕ} (e : r + r' = s) {p q k : ℕ} (h : p + q = k)
    (x : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn p) (y : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r').fn q) :
    (βMorF F κ s n).pull k ((pdPair (B.Lc F κ false n) ((base l).cris n) e).cup h x y) =
      (ttPair (F.pt κ) n e).cup h ((βMorF F κ r n).pull p x) ((βMorF F κ r' n).pull q y) :=
  subMor_cup (A := B.OcA F κ false n) (A' := AcrEl (F.pt κ) n) (B.βMor F κ false n) (fun _ _ _ => rfl) _ _ _ _ _ h x y

theorem βF_one (ht : TFil l) (n : ℕ) : (βMorF F κ 0 n).pull 0 (pdOne (B.Lc F κ false n) ((base l).cris n)) =
    (tMor ht (F.pt κ) 0 n).pull 0 (CH.oneH (AcrEl (F.pt κ) n)) :=
  subMor_one (A := B.OcA F κ false n) (A' := AcrEl (F.pt κ) n) (B.βMor F κ false n) (fun _ => rfl) rfl (pow_zero _) _ _ _

end F

theorem tMor_cup (ht : TFil l) (P : PAlg l ⥤ Type) (n : ℕ) {r r' s : ℕ} (e : r + r' = s) {p q k : ℕ} (h : p + q = k)
    (x : MH P n p) (y : MH P n q) :
    (tMor ht P s n).pull k ((mulP (AcrEl P n)).cup h x y) =
      (ttPair P n e).cup h ((tMor ht P r n).pull p x) ((tMor ht P r' n).pull q y) :=
  mulTo_cup (A := AcrEl P n) (by rw [← e, pow_add]) _ _ _ _ h x y

theorem comp_cup {M : Model l K} {r r' s i j : ℕ} (h : r + r' = s) {x : Fam M r i} {y : Fam M r' j} (hx : Comp x) (hy : Comp y) :
    Comp (cupS h x y) := fun n =>
  (pdOm_cup (CrystallineSemistableComparison.SH.redM (B.schFn M.p) (okToOC l K) false n) (RingHom.id _) (B.red_cris _ n.le_succ) h rfl
    (x (n + 1)) (y (n + 1))).trans
    (congrArg₂ ((pdPair (M.L false n) ((base l).cris n) h).cup rfl) (hx n) (hy n))

theorem comp_one (M : Model l K) : Comp (oneS M) := fun n =>
  pdOm_one (CrystallineSemistableComparison.SH.redM (B.schFn M.p) (okToOC l K) false n) (RingHom.id _) (B.red_cris _ n.le_succ)

theorem cup_gen (ht : TFil l) {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l) (n : ℕ) {r r' s i j : ℕ} (e : r + r' = s)
    (x : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn i) (y : H (B.pdS (B.Lc F κ false n) ((base l).cris n) r').fn j)
    (a : MH (F.pt κ) n i) (b : MH (F.pt κ) n j) (w : MH (F.pt κ) n (i + j))
    (hw : w = (mulP (AcrEl (F.pt κ) n)).cup rfl a b)
    (hx : (βMorF F κ r n).pull i x = (tMor ht (F.pt κ) r n).pull i a)
    (hy : (βMorF F κ r' n).pull j y = (tMor ht (F.pt κ) r' n).pull j b) :
    (βMorF F κ s n).pull (i + j) ((pdPair (B.Lc F κ false n) ((base l).cris n) e).cup rfl x y) =
      (tMor ht (F.pt κ) s n).pull (i + j) w :=
  ((βF_cup F κ n e rfl x y).trans (congrArg₂ ((ttPair (F.pt κ) n e).cup rfl) hx hy)).trans
    ((tMor_cup ht (F.pt κ) n e rfl a b).symm.trans (congrArg ((tMor ht (F.pt κ) s n).pull (i + j)) hw.symm))

variable (ht : TFil l) {e : E.EtFam l K}

theorem isLift_cupS_of_cupT (he : EtP e) : ∀ {M : Model l K} {r r' s i j : ℕ} (h : r + r' = s) {v : M.T i} {v' : M.T j} {w : M.T (i + j)}
    {x : Fam M r i} {x' : Fam M r' j}, M.CupT v v' w → IsLift ht e r v x → IsLift ht e r' v' x' → IsLift ht e s w (cupS h x x') :=
  fun {M _ _ _ i j} h {v v' w x x'} hw hx hx' => ⟨comp_cup h hx.1 hx'.1, fun n =>
    cup_gen ht (B.schFn M.p) (okToOC l K) n h (x n) (x' n) (e M n i (v.lev n)) (e M n j (v'.lev n)) (e M n (i + j) (w.lev n))
      ((congrArg (e M n (i + j)) (hw n)).trans (he.good.cup M n i j (v.lev n) (v'.lev n))) (hx.2 n) (hx'.2 n)⟩

theorem isLift_oneS_of_lev_eq_one (he : EtP e) : ∀ (M : Model l K) (v : M.T 0), (∀ k, v.lev k = GlobalTheory.EtC.one (l ^ k) M.spc) →
    IsLift ht e 0 v (oneS M) := fun M v hv => ⟨comp_one M, fun n =>
  (βF_one (B.schFn M.p) (okToOC l K) ht n).trans
    (congrArg ((tMor ht ((B.schFn M.p).pt (okToOC l K)) 0 n).pull 0) ((congrArg (e M n 0) (hv n)).trans (he.one M n)).symm)⟩

end CrystallineSemistableComparison.HT
