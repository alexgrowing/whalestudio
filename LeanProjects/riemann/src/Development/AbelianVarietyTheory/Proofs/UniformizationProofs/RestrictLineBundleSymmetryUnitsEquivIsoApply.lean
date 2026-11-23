import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.PowerGroupDatum

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.LB
open GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum (PowerDatum IsNormSymm)

section Units

variable {X Y : Scheme.{0}}

lemma res_self {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)ˣ) : res h x = x := by
  ext
  change (X.presheaf.map (𝟙 (Opposite.op U))).hom (x : Γ(X, U)) = _
  rw [X.presheaf.map_id]
  rfl

lemma res_pullU_id {U W : X.Opens} (h : W ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (h' : W ≤ U) (x : Γ(X, U)ˣ) :
    res h (pullU (𝟙 X) U x) = res h' x := by
  ext
  rfl

lemma gen_ext {L : LB X} {s t : LB.Gen L} (h : ∀ i, s.s i = t.s i) : s = t := by
  cases s; cases t
  congr 1
  exact funext h

lemma res_gen_congr {L : LB X} (s : LB.Gen L) {i j : L.ι} (e : i = j) {W : X.Opens}
    (h : W ≤ L.U i) (h' : W ≤ L.U j) : res h (s.s i) = res h' (s.s j) := by
  subst e
  rfl

end Units

section TwoForms

variable {X T : Scheme.{0}} (L : LB X) (f : X ⟶ X)

abbrev SymGen := LB.Gen (LB.LinComb L (K := Fin 2) ![f, 𝟙 X] ![1, -1])

lemma le_two {W : X.Opens} (j : Fin 2 → L.ι) :
    W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] j ↔ W ≤ f ⁻¹ᵁ L.U (j 0) ∧ W ≤ L.U (j 1) := by
  refine ⟨fun h => ⟨h.trans (wchart_le L _ j 0), h.trans (wchart_le L _ j 1)⟩,
    fun h y hy => Set.mem_iInter.2 fun k => ?_⟩
  fin_cases k
  · exact h.1 hy
  · exact h.2 hy

lemma le_one {W : T.Opens} (e : T ⟶ X) (a : PUnit.{1} → L.ι) :
    W ≤ wchart L (fun _ : PUnit.{1} => e) a ↔ W ≤ e ⁻¹ᵁ L.U (a ⟨⟩) :=
  ⟨fun h => h.trans (wchart_le L _ a ⟨⟩), fun h _ hy => Set.mem_iInter.2 fun _ => h hy⟩

lemma toIso_le (p : (PUnit.{1} → L.ι) × L.ι) :
    wchart L (fun _ : PUnit.{1} => f) p.1 ⊓ L.U p.2 ≤
      wchart L (K := Fin 2) ![f, 𝟙 X] ![p.1 ⟨⟩, p.2] :=
  (le_two L f _).2 ⟨(le_one L f _).1 inf_le_left, inf_le_right⟩

lemma ofIso_le (j : Fin 2 → L.ι) :
    wchart L (K := Fin 2) ![f, 𝟙 X] j ≤
      wchart L (fun _ : PUnit.{1} => f) (fun _ => j 0) ⊓ L.U (j 1) :=
  le_inf ((le_one L f _).2 ((le_two L f j).1 le_rfl).1) ((le_two L f j).1 le_rfl).2

def symEquiv : SymGen L f ≃ LB.Iso L (L.pull f) where
  toFun sy := ⟨fun p => res (toIso_le L f p) (ts sy ![p.1 ⟨⟩, p.2])⟩
  invFun w := ⟨fun j => res (ofIso_le L f j) (w.s (fun _ => j 0, j 1))⟩
  left_inv sy := gen_ext fun j => by
    refine (res_res _ _ _).trans ((res_gen_congr sy ?_ _ le_rfl).trans (res_self _ _))
    funext k
    fin_cases k <;> rfl
  right_inv w := gen_ext fun p => (res_res _ _ _).trans (res_self _ _)

lemma restrict_lineBundleSymmetryUnitsEquivIso_apply (sy : SymGen L f) (p : (PUnit.{1} → L.ι) × L.ι) {W : X.Opens}
    (h : W ≤ wchart L (fun _ : PUnit.{1} => f) p.1 ⊓ L.U p.2)
    (h' : W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] ![p.1 ⟨⟩, p.2]) :
    res h ((symEquiv L f sy).s p) = res h' (ts sy ![p.1 ⟨⟩, p.2]) :=
  res_res (toIso_le L f p) h _

lemma res_lcg_two (i j : Fin 2 → L.ι) {W : X.Opens}
    (h : W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] i ⊓ wchart L (K := Fin 2) ![f, 𝟙 X] j)
    (h₁ : W ≤ f ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0))) (h₂ : W ≤ L.U (i 1) ⊓ L.U (j 1)) :
    res h (lcg L (K := Fin 2) ![f, 𝟙 X] ![1, -1] i j) =
      res h₁ (pullU f _ (L.g (i 0) (j 0))) * (res h₂ (L.g (i 1) (j 1)))⁻¹ := by
  rw [res_lcg, Fin.prod_univ_two]
  refine congrArg₂ (· * ·) (zpow_one _) ((zpow_neg_one _).trans (congrArg (·⁻¹) ?_))
  exact res_pullU_id _ _ _

lemma res_dg_pull (p q : (PUnit.{1} → L.ι) × L.ι) {W : X.Opens}
    (h : W ≤ wchart L (fun _ : PUnit.{1} => f) p.1 ⊓ L.U p.2 ⊓
      (wchart L (fun _ : PUnit.{1} => f) q.1 ⊓ L.U q.2))
    (h₁ : W ≤ f ⁻¹ᵁ (L.U (p.1 ⟨⟩) ⊓ L.U (q.1 ⟨⟩))) (h₂ : W ≤ L.U p.2 ⊓ L.U q.2) :
    res h (dg (L.pull f) L p q) =
      res h₁ (pullU f _ (L.g (p.1 ⟨⟩) (q.1 ⟨⟩))) * (res h₂ (L.g p.2 q.2))⁻¹ := by
  refine (res_dg (L.pull f) L p q h).trans (congrArg₂ (· * ·) ?_ rfl)
  exact (congrArg (res _) (lcg_pull L f p.1 q.1)).trans (res_res _ _ _)

def SymCompat (sy : SymGen L f) : Prop :=
  ∀ (a b a' b' : L.ι) (W : X.Opens) (h₁ : W ≤ f ⁻¹ᵁ (L.U a ⊓ L.U a')) (h₂ : W ≤ L.U b ⊓ L.U b')
    (h₃ : W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] ![a, b])
    (h₄ : W ≤ wchart L (K := Fin 2) ![f, 𝟙 X] ![a', b']),
    res h₃ (ts sy ![a, b]) =
      res h₁ (pullU f _ (L.g a a')) * (res h₂ (L.g b b'))⁻¹ * res h₄ (ts sy ![a', b'])

lemma isGen_iff_symCompat (sy : SymGen L f) : sy.IsGen ↔ SymCompat L f sy := by
  rw [isGen_iff]
  refine ⟨fun H a b a' b' W h₁ h₂ h₃ h₄ => ?_, fun H i j => ?_⟩
  · have key := congrArg (res (le_inf h₃ h₄)) (H ![a, b] ![a', b'])
    rw [map_mul, res_res, res_res, res_lcg_two L f _ _ _ h₁ h₂] at key
    exact key
  · obtain ⟨a, b, rfl⟩ : ∃ a b, i = ![a, b] := ⟨i 0, i 1, by funext k; fin_cases k <;> rfl⟩
    obtain ⟨a', b', rfl⟩ : ∃ a b, j = ![a, b] := ⟨j 0, j 1, by funext k; fin_cases k <;> rfl⟩
    have h₁ := wchart_inter_le L (K := Fin 2) ![f, 𝟙 X] ![a, b] ![a', b'] 0
    have h₂ := wchart_inter_le L (K := Fin 2) ![f, 𝟙 X] ![a, b] ![a', b'] 1
    rw [← res_self le_rfl (lcg _ _ _ _ _), res_lcg_two L f _ _ _ h₁ h₂]
    exact H a b a' b' _ h₁ h₂ _ _

lemma isGen_symEquiv_iff_symCompat (sy : SymGen L f) :
    (symEquiv L f sy).IsGen ↔ SymCompat L f sy := by
  refine ⟨fun H a b a' b' W h₁ h₂ h₃ h₄ => ?_, fun H p q => ?_⟩
  · have k₃ := h₃.trans (ofIso_le L f _)
    have k₄ := h₄.trans (ofIso_le L f _)
    have key := congrArg (res (le_inf k₃ k₄)) (H (fun _ => a, b) (fun _ => a', b'))
    refine ((restrict_lineBundleSymmetryUnitsEquivIso_apply L f sy (fun _ => a, b) k₃ h₃).symm.trans ?_)
    refine ((res_res _ _ _).symm.trans key).trans ((map_mul _ _ _).trans ?_)
    refine congrArg₂ (· * ·) (res_dg_pull L f (fun _ => a, b) (fun _ => a', b') _ h₁ h₂) ?_
    exact (res_res _ _ _).trans (restrict_lineBundleSymmetryUnitsEquivIso_apply L f sy (fun _ => a', b') k₄ h₄)
  · have h₃ := (inf_le_left (b := wchart L (fun _ : PUnit.{1} => f) q.1 ⊓ L.U q.2)).trans
      (toIso_le L f p)
    have h₄ := (inf_le_right (a := wchart L (fun _ : PUnit.{1} => f) p.1 ⊓ L.U p.2)).trans
      (toIso_le L f q)
    have h₁ := (le_inf h₃ h₄).trans (wchart_inter_le L (K := Fin 2) ![f, 𝟙 X] _ _ 0)
    have h₂ := (le_inf h₃ h₄).trans (wchart_inter_le L (K := Fin 2) ![f, 𝟙 X] _ _ 1)
    refine (restrict_lineBundleSymmetryUnitsEquivIso_apply L f sy p _ h₃).trans ((H _ _ _ _ _ h₁ h₂ h₃ h₄).trans ?_)
    refine congrArg₂ (· * ·) ?_ (restrict_lineBundleSymmetryUnitsEquivIso_apply L f sy q _ h₄).symm
    exact (res_dg_pull L f p q le_rfl h₁ h₂).symm.trans (res_self _ _)

theorem isGen_symEquiv (sy : SymGen L f) : (symEquiv L f sy).IsGen ↔ sy.IsGen :=
  (isGen_symEquiv_iff_symCompat L f sy).trans (isGen_iff_symCompat L f sy).symm

end TwoForms

section Norm

variable {X T : Scheme.{0}} (L : LB X) (f : X ⟶ X) (e : T ⟶ X)

def DiagOne (sy : SymGen L f) : Prop :=
  ∀ (a : L.ι) (W : T.Opens) (h : W ≤ e ⁻¹ᵁ wchart L (K := Fin 2) ![f, 𝟙 X] ![a, a]),
    res h (pullU e _ (ts sy ![a, a])) = 1

def FixesRig (sy : SymGen L f) (r : LB.Gen (L.pull e)) : Prop :=
  ∀ (a b : L.ι) (W : T.Opens) (ha : W ≤ wchart L (fun _ : PUnit.{1} => e) (fun _ => a))
    (hb : W ≤ wchart L (fun _ : PUnit.{1} => e) (fun _ => b))
    (h : W ≤ e ⁻¹ᵁ wchart L (K := Fin 2) ![f, 𝟙 X] ![a, b]),
    res ha (ts r (fun _ => a)) = res h (pullU e _ (ts sy ![a, b])) * res hb (ts r (fun _ => b))

lemma corr_iff_diagOne (he : e ≫ f = e) (sy : SymGen L f) :
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ sy e) (LB.oneGen L) ↔ DiagOne L f e sy := by
  refine ⟨fun H a W h => ?_, fun H j j' hj _ _ => ?_⟩
  · have key := H ![a, a] PEmpty.elim
      (fun k₁ k₂ _ => by fin_cases k₁ <;> fin_cases k₂ <;> rfl) (fun k => k.elim)
      (fun _ k => k.elim)
    have hW : W ≤ wchart L (fun k => e ≫ (![f, 𝟙 X] : Fin 2 → (X ⟶ X)) k) ![a, a] ⊓
        wchart L (Y := T) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun y hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h hy) k,
        Set.mem_iInter.2 fun k => k.elim⟩
    have key' := congrArg (res hW) key
    refine ((res_res _ _ _).trans (res_res _ _ _)).symm.trans (key'.trans ?_)
    exact (congrArg (res hW) (map_one _)).trans (map_one _)
  · have h01 : j 0 = j 1 := hj 0 1 (he.trans (Category.comp_id e).symm)
    obtain ⟨a, rfl⟩ : ∃ a, j = ![a, a] := ⟨j 0, by
      funext k
      fin_cases k
      · rfl
      · exact h01.symm⟩
    exact ((res_res _ _ _).trans (H a _ _)).trans (map_one _).symm

lemma diagOne_iff_fixesRig (hL : L.IsLB) (sy : SymGen L f) (hsy : sy.IsGen)
    (r : LB.Gen (L.pull e)) (hr : r.IsGen) : DiagOne L f e sy ↔ FixesRig L f e sy r := by
  refine ⟨fun H a b W ha hb h => ?_, fun H a W h => ?_⟩
  · have hc := (isGen_iff_symCompat L f sy).1 hsy
    set V := wchart L (K := Fin 2) ![f, 𝟙 X] ![a, b] ⊓ L.U a with hV
    have v₁ : V ≤ f ⁻¹ᵁ L.U a := ((le_two L f ![a, b]).1 (inf_le_left : V ≤ _)).1
    have v₂ : V ≤ L.U b := ((le_two L f ![a, b]).1 (inf_le_left : V ≤ _)).2
    have v₃ : V ≤ wchart L (K := Fin 2) ![f, 𝟙 X] ![a, a] :=
      (le_two L f ![a, a]).2 ⟨v₁, inf_le_right⟩
    have hWV : W ≤ e ⁻¹ᵁ V := fun y hy => ⟨h hy, (le_one L e _).1 ha hy⟩
    have k := hc a b a a V (fun y hy => ⟨v₁ hy, v₁ hy⟩) (le_inf v₂ inf_le_right) inf_le_left v₃
    rw [pull_g_self hL f a (fun y hy => ⟨v₁ hy, v₁ hy⟩), _root_.one_mul] at k
    have k' := congrArg (fun x => res hWV (pullU e V x)) k
    simp only [map_mul, map_inv, pullU_res, res_res] at k'
    rw [H a W, _root_.mul_one] at k'
    have k₂ := congrArg (res (le_inf hb ha)) ((isGen_iff L r).1 hr (fun _ => b) (fun _ => a))
    rw [map_mul, res_res, res_res, lcg_pull, res_res] at k₂
    rw [k', k₂, inv_mul_cancel_left]
  · have ha : W ≤ wchart L (fun _ : PUnit.{1} => e) (fun _ => a) :=
      (le_one L e _).2 (h.trans (e.preimage_mono ((le_two L f ![a, a]).1 le_rfl).2))
    exact (mul_right_cancel ((_root_.one_mul _).trans (H a a W ha ha h))).symm

end Norm

section GroupNorm

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

omit [GrpObj G] [IsCommMonObj G] in
lemma prod_punit {M : Type} [CommMonoid M] (g : PUnit.{1} → M) : ∏ k, g k = g ⟨⟩ :=
  Fintype.prod_unique g

lemma maps_iff_fixesRig (L : LB G.left) (r : LB.Gen (L.pull (eSec G)))
    (sy : SymGen L (ι[G]).left) :
    LB.Gen.Maps (LB.linCombIso (symEquiv L _ sy) (K := PUnit.{1}) (fun _ => eSec G) (fun _ => 1))
        r (rigPullOf (ι[G]).left (𝟙 _) GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv L r) ↔
      FixesRig L (ι[G]).left (eSec G) sy r := by
  have he : eSec G ≫ (ι[G]).left = eSec G := GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv.trans (Category.id_comp _)

  have main : ∀ (a b : L.ι) (W : (𝟙_ (Over S)).left.Opens)
      (hW : W ≤ wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) (fun _ _ => a) ⊓
        wchart L (fun _ : PUnit.{1} => eSec G) (fun _ => b))
      (h : W ≤ eSec G ⁻¹ᵁ wchart L (K := Fin 2) ![(ι[G]).left, 𝟙 _] ![a, b]),
      res hW ((LB.linCombIso (symEquiv L _ sy) (K := PUnit.{1}) (fun _ => eSec G)
        (fun _ => 1)).s (fun _ _ => a, fun _ => b)) =
        res h (pullU (eSec G) _ (ts sy ![a, b])) := by
    intro a b W hW h
    refine (congrArg (res hW) ((prod_punit _).trans
      (zpow_one _))).trans ?_
    refine (res_res _ _ _).trans ?_
    exact (res_pullU_eq (eSec G) (toIso_le L _ (fun _ => a, b)) h _ _).symm
  have main₂ : ∀ (a : L.ι) (W : (𝟙_ (Over S)).left.Opens)
      (hW : W ≤ wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) (fun _ _ => a))
      (ha : W ≤ wchart L (fun _ : PUnit.{1} => eSec G) (fun _ => a)),
      res hW ((rigPullOf (ι[G]).left (𝟙 _) GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv L r).s (fun _ _ => a)) =
        res ha (ts r (fun _ => a)) := fun a W hW ha =>
    (res_res _ _ _).trans (res_pullU_id _ _ _)
  refine ⟨fun H a b W ha hb h => ?_, fun H p => ?_⟩
  · have hW₁ : W ≤ wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) (fun _ _ => a) :=
      fun y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (h hy) 0
    have key := congrArg (res (le_inf hW₁ hb)) (H (fun _ _ => a, fun _ => b))
    refine (main₂ a W hW₁ ha).symm.trans ((res_res _ _ _).symm.trans (key.trans ?_))
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (main a b W _ h) (res_res _ _ _))
  · obtain ⟨a, b⟩ := p
    have ha : wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) a ⊓
        wchart L (fun _ : PUnit.{1} => eSec G) b ≤
        wchart L (fun _ : PUnit.{1} => eSec G) (fun _ => a ⟨⟩ ⟨⟩) :=
      inf_le_left.trans (rigPull_le (ι[G]).left (𝟙 _) GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv L a)
    have h : wchart (L.pull (ι[G]).left) (fun _ : PUnit.{1} => eSec G) a ⊓
        wchart L (fun _ : PUnit.{1} => eSec G) b ≤
        eSec G ⁻¹ᵁ wchart L (K := Fin 2) ![(ι[G]).left, 𝟙 _] ![a ⟨⟩ ⟨⟩, b ⟨⟩] :=
      fun y hy => toIso_le L _ (a ⟨⟩, b ⟨⟩)
        ⟨Set.mem_iInter.1 hy.1 ⟨⟩, Set.mem_iInter.1 hy.2 ⟨⟩⟩
    refine (main₂ (a ⟨⟩ ⟨⟩) _ inf_le_left ha).trans
      ((H (a ⟨⟩ ⟨⟩) (b ⟨⟩) _ ha inf_le_right h).trans ?_)
    exact congrArg₂ (· * ·) ((main (a ⟨⟩ ⟨⟩) (b ⟨⟩) _ le_rfl h).symm.trans (res_self _ _)) rfl

def IsCanonSym (L : LB G.left) (sy : SymGen L (ι[G]).left) : Prop :=
  sy.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ sy (eSec G)) (LB.oneGen L)

theorem isNormSymm_iff (L : RigLB G) (sy : SymGen L.L (ι[G]).left) :
    IsNormSymm L (symEquiv L.L _ sy) ↔ IsCanonSym L.L sy := by
  have he : eSec G ≫ (ι[G]).left = eSec G := GlobalTheory.IndefiniteRowSideFullHecke.PowerGroupDatum.eSec_inv.trans (Category.id_comp _)
  refine (and_congr (isGen_symEquiv L.L _ sy) (maps_iff_fixesRig L.L L.rig sy)).trans ?_
  exact and_congr_right fun hsy => ((corr_iff_diagOne L.L _ _ he sy).trans
    (diagOne_iff_fixesRig L.L _ _ L.isLB sy hsy L.rig L.rigGen)).symm

end GroupNorm

section Pow

variable {S : Scheme.{0}}

def powEquiv (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) :
    Out.IsPowGrp G' G j ≃ PowerDatum j G' G where
  toFun p := ⟨p.pr, p.hom, fun T => ⟨fun x y h => p.lim.hom_ext fun i => congrFun h i.as,
    fun z => ⟨p.lim.lift (Fan.mk T z), funext fun i => p.lim.fac (Fan.mk T z) ⟨i⟩⟩⟩⟩
  invFun P := ⟨P.pr, P.isMonHom, mkFanLimit _ (fun s => ((P.bij s.pt).2 s.proj).choose)
    (fun s i => congrFun ((P.bij s.pt).2 s.proj).choose_spec i)
    (fun s _ hm => (P.bij s.pt).1
      ((funext hm).trans ((P.bij s.pt).2 s.proj).choose_spec.symm))⟩
  left_inv p := by
    cases p
    dsimp only
    congr 1
    exact Subsingleton.elim _ _
  right_inv _ := rfl

abbrev GrpWithMaps (G : Over S) (n : ℕ) := Σ H : Over S, GrpObj H × (Fin n → (H ⟶ G))

def powStep (G : Over S) [GrpObj G] {n : ℕ} (x : GrpWithMaps G n) : GrpWithMaps G (n + 1) :=
  ⟨G ⊗ x.1, letI := x.2.1; inferInstance,
    fun i => Fin.cases (fst G x.1) (fun k => snd G x.1 ≫ x.2.2 k) i⟩

variable {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}

variable [IsCommMonObj G'] [IsCommMonObj G]

end Pow

section Clauses

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] {j : ℕ}

end Clauses

def WellFormedSt : Prop :=
  ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (j : ℕ) (p : Out.IsPowGrp G' G j) (L : RigLB G),
    (Out.boxLB L.L p.pr).IsLB ∧ (Out.boxRig p L.L L.rig).IsGen

def BoxSymRigSt : Prop :=
  ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (j : ℕ) (p : Out.IsPowGrp G' G j) (L : RigLB G) (sy : SymGen L.L (ι[G]).left),
    IsCanonSym L.L sy → IsCanonSym (Out.boxLB L.L p.pr) (Out.boxSym p L.L sy)

end GlobalTheory.BoxCompare
