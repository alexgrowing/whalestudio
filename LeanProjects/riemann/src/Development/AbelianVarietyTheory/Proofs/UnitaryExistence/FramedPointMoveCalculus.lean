import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MoveCalc

section Stalk

variable {X Y Y' Y'' : Scheme.{0}} {L : LB X} {F : X ⟶ X}

abbrev Fam (L : LB X) (p : Y ⟶ X) : Type :=
  ∀ i : Fin 1 → L.ι, Γ(Y, LB.wchart L (fun _ : Fin 1 => p) i)

theorem mem_chart {p : Y ⟶ X} {i : Fin 1 → L.ι} {y : Y} :
    y ∈ LB.wchart L (fun _ : Fin 1 => p) i ↔ p y ∈ L.U (i 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by rw [Subsingleton.elim k 0]; exact h⟩

def Carry (w : LB.Iso L (L.pull F)) {p : Y ⟶ X} {p' : Y' ⟶ X} (pm : Y ⟶ Y') (a : Fam L p) (a' : Fam L p') : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i j : L.ι), F (p (r z)) ∈ L.U i → p (r z) ∈ L.U j →
    gs (r ≫ pm) z _ (a' fun _ => i) = (gw w (r ≫ p) z i j).val * gs r z _ (a fun _ => j)

theorem carry_iff (w : LB.Iso L (L.pull F)) {p : Y ⟶ X} {p' : Y' ⟶ X} {pm : Y ⟶ Y'} (hpm : pm ≫ p' = p ≫ F)
    (a : Fam L p) (a' : Fam L p') :
    (∀ (i j : L.ι) (W : Y.Opens), W = p ⁻¹ᵁ ((LB.div (L.pull F) L).U ((fun _ => i), j)) →
      ∀ (h₀ : W ≤ p ⁻¹ᵁ ((LB.div (L.pull F) L).U ((fun _ => i), j)))
        (h₁ : W ≤ pm ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p') (fun _ => i))
        (h₂ : W ≤ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j)),
      (pm.appLE (LB.wchart L (fun _ : Fin 1 => p') (fun _ => i)) W h₁).hom (a' (fun _ => i)) =
        (p.appLE ((LB.div (L.pull F) L).U ((fun _ => i), j)) W h₀).hom (Units.val (w.s ((fun _ => i), j))) *
          (Y.presheaf.map (homOfLE h₂).op).hom (a (fun _ => j))) ↔ Carry w pm a a' := by
  have key : ∀ (i j : L.ι) (W : Y.Opens) (h₀ : W ≤ p ⁻¹ᵁ ((LB.div (L.pull F) L).U ((fun _ => i), j)))
      (h₂ : W ≤ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j)) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ W →
      gs r z W ((p.appLE ((LB.div (L.pull F) L).U ((fun _ => i), j)) W h₀).hom (Units.val (w.s ((fun _ => i), j))) *
          (Y.presheaf.map (homOfLE h₂).op).hom (a (fun _ => j))) =
        (gw w (r ≫ p) z i j).val * gs r z _ (a fun _ => j) := fun i j W h₀ h₂ Z r z hz =>
    (gs_mul r z W hz _ _).trans (congrArg₂ (· * ·)
      ((gs_appLE p _ W h₀ r z hz _).trans (gs_unit (r ≫ p) z _ (h₀ hz) _)) (gs_res r z h₂ hz _))
  constructor
  · intro h Z r z i j hi hj
    have hz : r z ∈ p ⁻¹ᵁ ((LB.div (L.pull F) L).U ((fun _ => i), j)) := ⟨mem_pull.2 hi, hj⟩
    have m₁ : p ⁻¹ᵁ ((LB.div (L.pull F) L).U ((fun _ => i), j)) ≤
        pm ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p') (fun _ => i) := fun y hy => mem_chart.2 (by
      have h' : (p ≫ F) y ∈ L.U i := mem_pull.1 hy.1
      rw [← hpm] at h'
      exact h')
    have m₂ : p ⁻¹ᵁ ((LB.div (L.pull F) L).U ((fun _ => i), j)) ≤
        LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) := fun y hy => mem_chart.2 hy.2
    exact (gs_appLE pm _ _ m₁ r z hz _).symm.trans
      ((congrArg (gs r z _) (h i j _ rfl le_rfl m₁ m₂)).trans (key i j _ le_rfl m₂ Z r z hz))
  · intro h i j W _ h₀ h₁ h₂
    refine fn_ext fun y hy => ?_
    exact (gs_appLE pm _ W h₁ (𝟙 Y) y hy _).trans ((h Y (𝟙 Y) y i j (mem_pull.1 (h₀ hy).1) (h₀ hy).2).trans
      (key i j W h₀ h₂ Y (𝟙 Y) y hy).symm)

def Pulls {p : Y ⟶ X} {p' : Y' ⟶ X} (q : Y' ⟶ Y) (a : Fam L p) (b : Fam L p') : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (i : L.ι), p' (r z) ∈ L.U i →
    gs (r ≫ q) z _ (a fun _ => i) = gs r z _ (b fun _ => i)

theorem pulls_iff {p : Y ⟶ X} {p' : Y' ⟶ X} {q : Y' ⟶ Y} (hq : q ≫ p = p') (a : Fam L p) (b : Fam L p') :
    (∀ (i : Fin 1 → L.ι) (h : LB.wchart L (fun _ : Fin 1 => p') i ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) i),
      (q.appLE _ _ h).hom (a i) = b i) ↔ Pulls q a b := by
  constructor
  · intro h Z r z i hi
    have m : LB.wchart L (fun _ : Fin 1 => p') (fun _ => i) ≤
        q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => i) := fun y hy => mem_chart.2 (by
      have h' : p' y ∈ L.U i := mem_chart.1 hy
      rw [← hq] at h'
      exact h')
    exact (gs_appLE q _ _ m r z (mem_chart.2 hi) _).symm.trans (congrArg (gs r z _) (h _ m))
  · intro h i m
    obtain ⟨k, rfl⟩ : ∃ k, i = fun _ => k := ⟨i 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
    exact fn_ext fun y hy => (gs_appLE q _ _ m (𝟙 _) y hy _).trans (h _ (𝟙 _) y k (mem_chart.1 hy))

theorem pulls_of_carry (hL : L.IsLB) {w : LB.Iso L (L.pull F)} {Y₂ Y₂' : Scheme.{0}} {p : Y ⟶ X} {p' : Y' ⟶ X}
    {p₂ : Y₂ ⟶ X} {p₂' : Y₂' ⟶ X} {pm : Y ⟶ Y'} {pm₂ : Y₂ ⟶ Y₂'} {q : Y₂ ⟶ Y} {σ : Y₂' ⟶ Y₂}
    (hσ : σ ≫ pm₂ = 𝟙 _) (h₂ : pm₂ ≫ p₂' = p₂ ≫ F) (hq : q ≫ p = p₂)
    {a : Fam L p} {a' : Fam L p'} {b : Fam L p₂} {b' : Fam L p₂'}
    (ha : Carry w pm a a') (hb : Carry w pm₂ b b') (h : Pulls q a b) : Pulls (σ ≫ q ≫ pm) a' b' := by
  intro Z r z i hi
  obtain ⟨j, hj⟩ := exists_chart hL (p₂ (σ (r z)))
  have e : σ ≫ p₂ ≫ F = p₂' := by rw [← h₂, ← Category.assoc, hσ, Category.id_comp]
  have hi' : F (p₂ (σ (r z))) ∈ L.U i := by
    rw [← e] at hi
    exact hi
  have e' : p (q (σ (r z))) = p₂ (σ (r z)) := congrArg (fun g : Y₂ ⟶ X => g (σ (r z))) hq
  have A := ha Z ((r ≫ σ) ≫ q) z i j (by show F (p (q (σ (r z)))) ∈ _; rw [e']; exact hi')
    (by show p (q (σ (r z))) ∈ _; rw [e']; exact hj)
  have B := hb Z (r ≫ σ) z i j hi' hj
  rw [h Z (r ≫ σ) z j hj, Category.assoc (r ≫ σ) q p, hq, ← B, Category.assoc r σ pm₂, hσ, Category.comp_id] at A
  rw [← A]
  simp only [Category.assoc]

theorem Carry.comp (hL : L.IsLB) {F' : X ⟶ X} {w : LB.Iso L (L.pull F)} {w' : LB.Iso L (L.pull F')}
    {w'' : LB.Iso L (L.pull (F ≫ F'))} (T : Tri w' w w'') {p : Y ⟶ X} {p' : Y' ⟶ X} {p'' : Y'' ⟶ X}
    {pm : Y ⟶ Y'} {pm' : Y' ⟶ Y''} (hpm : pm ≫ p' = p ≫ F) {a : Fam L p} {a' : Fam L p'} {a'' : Fam L p''}
    (h : Carry w pm a a') (h' : Carry w' pm' a' a'') : Carry w'' (pm ≫ pm') a a'' := by
  intro Z r z i j hi hj
  obtain ⟨k, hk⟩ := exists_chart hL (F (p (r z)))
  have e : p' (pm (r z)) = F (p (r z)) := congrArg (fun g : Y ⟶ X => g (r z)) hpm
  have A := h' Z (r ≫ pm) z i k (by show F' (p' (pm (r z))) ∈ _; rw [e]; exact hi)
    (by show p' (pm (r z)) ∈ _; rw [e]; exact hk)
  rw [← Category.assoc, A, h Z r z k j hk hj, T Z (r ≫ p) z i k j hi hk hj, Units.val_mul, _root_.mul_assoc,
    Category.assoc r pm p', hpm, Category.assoc r p F]

theorem Carry.smul {w : LB.Iso L (L.pull F)} {B : Scheme.{0}} {p : Y ⟶ X} {p' : Y' ⟶ X} {pm : Y ⟶ Y'}
    (hpm : pm ≫ p' = p ≫ F) {f : Y ⟶ B} {f' : Y' ⟶ B} (hf : pm ≫ f' = f) (t : Γ(B, ⊤))
    {a : Fam L p} {a' : Fam L p'} (h : Carry w pm a a') :
    Carry w pm (fun i => (Y.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom t) * a i)
      (fun i => (Y'.presheaf.map (homOfLE le_top).op).hom (f'.appTop.hom t) * a' i) := by
  intro Z r z i j hi hj
  have e : p' (pm (r z)) = F (p (r z)) := congrArg (fun g : Y ⟶ X => g (r z)) hpm
  have m' : (r ≫ pm) z ∈ LB.wchart L (fun _ : Fin 1 => p') (fun _ => i) :=
    mem_chart.2 (by show p' (pm (r z)) ∈ _; rw [e]; exact hi)
  have m : r z ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) := mem_chart.2 hj
  have c' := (gs_res (r ≫ pm) z le_top m' (f'.appTop.hom t)).trans (gs_pull (r ≫ pm) f' z ⊤ trivial t)
  have c := (gs_res r z le_top m (f.appTop.hom t)).trans (gs_pull r f z ⊤ trivial t)
  rw [Category.assoc, hf] at c'
  refine (gs_mul _ z _ m' _ _).trans (Eq.trans ?_ (congrArg _ (gs_mul _ z _ m _ _).symm))
  rw [c, c', h Z r z i j hi hj, mul_left_comm]

def idIso (L : LB X) : LB.Iso L (L.pull (𝟙 X)) where
  s p := res (fun _ hy => ⟨mem_pull.1 hy.1, hy.2⟩ :
    (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2)

theorem gw_idIso (f : Y ⟶ X) (y : Y) {j k : L.ι} (hj : f y ∈ L.U j) (hk : f y ∈ L.U k) :
    gw (idIso L) f y j k = gm f y (L.U j ⊓ L.U k) (L.g j k) :=
  gm_res f y _ (show f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k from ⟨mem_pull.2 hj, hk⟩) _

theorem pgen_idIso (hL : L.IsLB) : PGen (idIso L) := by
  intro Z f y j j' k k' hj hj' hk hk'
  rw [gw_idIso f y hj hk, gw_idIso f y hj' hk', Category.comp_id, mul_right_comm, gm_cocycle hL f y hj hj' hk',
    ← gm_cocycle hL f y hj hk hk', mul_inv_cancel_right]

theorem pmaps_idIso {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) : PMaps (idIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have mp : r z ∈ LB.wchart L φ p := Set.mem_iInter.2 hp
  have mq : r z ∈ LB.wchart L φ q := Set.mem_iInter.2 hq
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨mp, mq⟩
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _) (ht p q)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ((gm_linComb L φ ε r z p q mp mq).trans ?_) (gm_res r z _ hm _))))
  exact Finset.prod_congr rfl fun k _ => by rw [gw_idIso (r ≫ φ k) z (hp k) (hq k)]

theorem carry_idIso {p : Y ⟶ X} (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => p) (fun _ => 1))) :
    Carry (idIso L) (𝟙 Y) s.f s.f := by
  intro Z r z i j hi hj
  have mi : r z ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => i) := mem_chart.2 hi
  have mj : r z ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) := mem_chart.2 hj
  rw [Category.comp_id, gw_idIso (r ≫ p) z hi hj]
  refine (gs_compat s r z mi mj).trans (congrArg (fun u : (Z.presheaf.stalk z)ˣ => u.val * _) ?_)
  exact (gm_linComb L _ _ r z _ _ mi mj).trans (by rw [Fin.prod_univ_one, zpow_one])

end Stalk

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem cubIso_iff {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)) :
    Formalism.L2.Pj.CubIso ν w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec Xo.univ.t.G) (fun _ => eSec Xo.univ.t.G) (fun _ => 1) Xo.univ.t.PP.rig
        Xo.univ.t.PP.rig ν.cm.e ∧
      PMaps w (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
        Xo.univ.t.cub.t ν.cm.F3 :=
  and_congr (isGen_iff w) (and_congr
    (maps_iff w _ (fun _ => eSec Xo.univ.t.G) _ _ _ ν.cm.e _ (rigPull_le ν.cm.F ν.cm.e ν.cm.e_comm _) (fun _ => rfl))
    (maps_iff w _ (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) _ _ _ ν.cm.F3 _ (ν.cm.theta_le _) (fun _ => rfl)))

theorem cubIso_unique {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ}
    {w w' : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)} (h : Formalism.L2.Pj.CubIso ν w)
    (h' : Formalism.L2.Pj.CubIso ν w') : w = w' :=
  GlobalTheory.iso_eq_of_maps_along_section (S := Xo.X) (exists_chart Xo.univ.t.PP.isLB)
    (fun y => (exists_chart Xo.univ.t.PP.isLB (ν.φ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
    Xo.univ.t.G.hom (eSec Xo.univ.t.G) (Over.w η[Xo.univ.t.G])
    (GlobalTheory.globalFns_holds _ _
      ⟨Xo.univ.t.semi.comm, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩).2
    h.1 h'.1 h.2.1 h'.2.1

theorem frMove_iff_carry {S : Type} [CommRing S] [Algebra c.F S] {ρ : Xo.X ⟶ Xo.X}
    {ν : SABMap Xo.univ.t Xo.univ.t ρ} {y y' : FrPt Xo c S} :
    FrMove ρ ν y y' ↔ y'.x = y.x ≫ ρ ∧ (∀ τ i, y'.u τ i = y.u τ i ≫ ν.φ) ∧
      ∃ (pm : Gx y.x ⟶ Gx y'.x) (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)),
        pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left ∧
        pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ ν.φ ∧
        Formalism.L2.Pj.CubIso ν w ∧
        Carry w (p := (snd (Over.mk y.x) Xo.univ.t.G).left) (p' := (snd (Over.mk y'.x) Xo.univ.t.G).left)
          pm y.s.f y'.s.f :=
  and_congr_right fun _ => and_congr_right fun _ => exists_congr fun _ => exists_congr fun w =>
    and_congr_right fun _ => and_congr_right fun h => and_congr_right fun _ => carry_iff w h y.s.f y'.s.f

theorem exists_section {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    {x x' : Sp S ⟶ Xo.X} (hx : x' = x ≫ ρ) {pm : Gx x ⟶ Gx x'}
    (hf : pm ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (hs : pm ≫ (snd (Over.mk x') Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ ν.φ) :
    ∃ σ : Gx x' ⟶ Gx x, σ ≫ pm = 𝟙 _ := by
  have cond : (fst (Over.mk x') Xo.univ.t.G).left ≫ x' =
      (snd (Over.mk x') Xo.univ.t.G).left ≫ Xo.univ.t.G.hom := pullback.condition
  have sq : (snd (Over.mk x') Xo.univ.t.G).left ≫ Xo.univ.t.G.hom =
      ((fst (Over.mk x') Xo.univ.t.G).left ≫ x) ≫ ρ :=
    cond.symm.trans ((congrArg _ hx).trans (Category.assoc _ _ _).symm)
  obtain ⟨σ, s₁, s₂⟩ : ∃ σ : Gx x' ⟶ Gx x,
      σ ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ∧
      σ ≫ (snd (Over.mk x) Xo.univ.t.G).left = ν.cart.1.lift _ _ sq :=
    ⟨pullback.lift (f := x) (g := Xo.univ.t.G.hom) _ _ (ν.cart.1.lift_snd _ _ sq).symm,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  refine ⟨σ, ?_⟩
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) hf).trans (s₁.trans (Category.id_comp _).symm))
  · refine (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) hs).trans (Eq.trans ?_ (Category.id_comp _).symm))
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ν.φ) s₂).trans (ν.cart.1.lift_fst _ _ sq))

theorem isCombAt_push {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    {x x' : Sp S ⟶ Xo.X} (hx : x' = x ≫ ρ) {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v cf w) :
    IsCombAt x' (fun i => v i ≫ ν.φ) cf (w ≫ ν.φ) := by
  have key : ∀ (b : Sp (DualNumber S) ⟶ Xo.X), b = (tEps x).hom ≫ ρ →
      ∃ e : (tEps x ⟶ Xo.univ.t.G) →* (Over.mk b ⟶ Xo.univ.t.G), ∀ p, (e p).left = p.left ≫ ν.φ := by
    rintro b rfl
    exact ⟨pushHom ν.cart (tEps x), fun _ => rfl⟩
  obtain ⟨e, he⟩ := key (spMap (algebraMap S (DualNumber S)) ≫ x') (by rw [hx]; exact (Category.assoc _ _ _).symm)
  obtain ⟨u, hu, hw⟩ := h
  refine ⟨fun i => e (u i), fun i => (he _).trans ((congrArg (· ≫ ν.φ) (hu i)).trans (Category.assoc _ _ _)), ?_⟩
  have : (List.ofFn fun i => e (u i)).prod = e (List.ofFn u).prod := by
    rw [map_list_prod, List.map_ofFn]; rfl
  exact (congrArg (fun q => q.left) this).trans ((he _).trans (congrArg (· ≫ ν.φ) hw))

theorem move_id : ∃ ν : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X), ν.φ = 𝟙 _ ∧
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FrMove (𝟙 Xo.X) ν y y := by
  let n : CubeMap Xo.univ.t.G Xo.univ.t.G :=
    { F := 𝟙 _, F3 := 𝟙 _, e := 𝟙 _
      e_comm := by rw [Category.comp_id, Category.id_comp]
      psum_comm := fun I => by rw [Category.comp_id, Category.id_comp] }
  have g := pgen_idIso Xo.univ.t.PP.isLB
  have r := pmaps_idIso _ _ Xo.univ.t.PP.rigGen
  have q := pmaps_idIso _ _ Xo.univ.t.cub.isGen
  have cart : IsGrpPullback Xo.univ.t.G Xo.univ.t.G (𝟙 Xo.X) (𝟙 Xo.univ.t.G.left) :=
    ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy =>
      (mul_left_congr (a := T.hom ≫ 𝟙 _) (b := T.hom) (Category.comp_id _) x₀ y₀ x y
        (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm⟩
  let ν : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X) :=
    ⟨n, cart, rfl, fun a => (Category.comp_id _).trans (Category.id_comp _).symm,
      (isPullCubical_iff n _ _).2 ⟨idIso _, g, r, q⟩⟩
  refine ⟨ν, rfl, fun S _ _ y => frMove_iff_carry.2 ⟨(Category.comp_id _).symm, fun τ i => (Category.comp_id _).symm,
    𝟙 _, idIso _, Category.id_comp _, (Category.id_comp _).trans (Category.comp_id _).symm,
    (cubIso_iff ν _).2 ⟨g, r, q⟩, carry_idIso y.s⟩⟩

theorem move_comp (ρ ρ' : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ν' : SABMap Xo.univ.t Xo.univ.t ρ') :
    ∃ κ : SABMap Xo.univ.t Xo.univ.t (ρ ≫ ρ'), κ.φ = ν.φ ≫ ν'.φ ∧
      ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S),
        FrMove ρ ν y y' → FrMove ρ' ν' y' y'' → FrMove (ρ ≫ ρ') κ y y'' := by
  let n : CubeMap Xo.univ.t.G Xo.univ.t.G :=
    { F := ν.cm.F ≫ ν'.cm.F, F3 := ν.cm.F3 ≫ ν'.cm.F3, e := ν.cm.e ≫ ν'.cm.e
      e_comm := by rw [← Category.assoc, ν.cm.e_comm, Category.assoc, ν'.cm.e_comm, Category.assoc]
      psum_comm := fun I => by
        rw [← Category.assoc, ν.cm.psum_comm, Category.assoc, ν'.cm.psum_comm, Category.assoc] }
  let κ : SABMap Xo.univ.t Xo.univ.t (ρ ≫ ρ') :=
    ⟨n, ν.cart.comp ν'.cart, by
      show ν.cm.e ≫ ν'.cm.e = ρ ≫ ρ'
      rw [ν.base, ν'.base], fun a => by
      show _ ≫ ν.cm.F ≫ ν'.cm.F = (ν.cm.F ≫ ν'.cm.F) ≫ _
      rw [← Category.assoc, ν.act, Category.assoc, ν'.act, Category.assoc],
      pullCubComp _ _ _ _ _ _ ν'.cm ν.cm n _ _ _ _ _ _ rfl rfl rfl ν'.lin ν.lin⟩
  refine ⟨κ, rfl, fun S _ _ y y' y'' h h' => ?_⟩
  obtain ⟨hx, hu, pm, w, hf, hs, hw, hc⟩ := frMove_iff_carry.1 h
  obtain ⟨hx', hu', pm', w', hf', hs', hw', hc'⟩ := frMove_iff_carry.1 h'
  obtain ⟨g, r, q⟩ := (cubIso_iff ν w).1 hw
  obtain ⟨g', r', q'⟩ := (cubIso_iff ν' w').1 hw'
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨w'', T⟩ := exists_comp hL w' w g' g hL hL
  refine frMove_iff_carry.2 ⟨by rw [hx', hx, Category.assoc], fun τ i => ?_, pm ≫ pm', w'', ?_, ?_,
    (cubIso_iff κ w'').2 ⟨T.pgen_comp hL g' g, T.pmaps_comp hL (fun _ => ν.cm.e_comm) r' r,
      T.pmaps_comp hL (fun I => ν.cm.psum_comm I.down) q' q⟩, Carry.comp hL T hs hc hc'⟩
  · rw [hu', hu, Category.assoc]
  · rw [Category.assoc, hf', hf]
  · rw [Category.assoc, hs', ← Category.assoc, hs, Category.assoc]

theorem move_frMap {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {S T : Type} [CommRing S] [Algebra c.F S]
    [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T}
    (h : FrMap φ y z) (hy : FrMove ρ ν y y') (hz : FrMove ρ ν z z') : FrMap φ y' z' := by
  obtain ⟨hx, hu, pm, w, hf, hs, hw, hc⟩ := frMove_iff_carry.1 hy
  obtain ⟨hx', hu', pm', w', hf', hs', hw', hc'⟩ := frMove_iff_carry.1 hz
  obtain rfl := cubIso_unique hw hw'
  obtain ⟨gx, gu, q, qs, qf, qa⟩ := h
  obtain ⟨σ, hσ⟩ := exists_section ν hx' hf' hs'
  have es : (σ ≫ q ≫ pm) ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk z'.x) Xo.univ.t.G).left := by
    rw [Category.assoc, Category.assoc, hs, ← Category.assoc q, qs, ← hs', ← Category.assoc, hσ, Category.id_comp]
  refine ⟨by rw [hx', gx, hx, Category.assoc], fun τ i => by rw [hu', gu, hu, Category.assoc], σ ≫ q ≫ pm, es, ?_,
    (pulls_iff es y'.s.f z'.s.f).2
      (pulls_of_carry Xo.univ.t.PP.isLB hσ hs' qs hc hc' ((pulls_iff qs y.s.f z.s.f).1 qa))⟩
  rw [Category.assoc, Category.assoc, hf, qf, ← hf', Category.assoc, ← Category.assoc σ, hσ, Category.id_comp]

theorem move_frBor {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {S : Type} [CommRing S] [Algebra c.F S]
    {t : Ix Dw → Sˣ} {y y' z z' : FrPt Xo c S}
    (h : FrBor t y z) (hy : FrMove ρ ν y y') (hz : FrMove ρ ν z z') : FrBor t y' z' := by
  obtain ⟨hx, hu, pm, w, hf, hs, hw, hc⟩ := frMove_iff_carry.1 hy
  obtain ⟨hx', hu', pm', w', hf', hs', hw', hc'⟩ := frMove_iff_carry.1 hz
  obtain rfl := cubIso_unique hw hw'
  obtain ⟨gx, gu, q, qs, qf, qa⟩ := h
  obtain ⟨σ, hσ⟩ := exists_section ν hx' hf' hs'
  have es : (σ ≫ q ≫ pm) ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk z'.x) Xo.univ.t.G).left := by
    rw [Category.assoc, Category.assoc, hs, ← Category.assoc q, qs, ← hs', ← Category.assoc, hσ, Category.id_comp]
  refine ⟨by rw [hx', gx, hx], fun τ i => ?_, σ ≫ q ≫ pm, es, ?_,
    (pulls_iff es (fun i => scal y'.x (t none : S) i * y'.s.f i) z'.s.f).2
      (pulls_of_carry Xo.univ.t.PP.isLB hσ hs' qs (hc.smul hs hf (toΓ S (t none : S))) hc'
        ((pulls_iff qs (fun i => scal y.x (t none : S) i * y.s.f i) z.s.f).1 qa))⟩
  · obtain ⟨cf, c₁, c₂, c₃⟩ := gu τ i
    refine ⟨cf, c₁, c₂, ?_⟩
    rw [hu' τ i, show y'.u τ = fun j => y.u τ j ≫ ν.φ from funext (hu τ)]
    exact isCombAt_push ν hx c₃
  · rw [Category.assoc, Category.assoc, hf, qf, ← hf', ← Category.assoc σ, hσ, Category.id_comp]

theorem frMove_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∃ ν : SABMap Xo.univ.t Xo.univ.t (𝟙 Xo.X), ν.φ = 𝟙 _ ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FrMove (𝟙 Xo.X) ν y y) ∧ (∀ (ρ ρ' : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ν' : SABMap Xo.univ.t Xo.univ.t ρ'), ∃ κ : SABMap Xo.univ.t Xo.univ.t (ρ ≫ ρ'), κ.φ = ν.φ ≫ ν'.φ ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S), FrMove ρ ν y y' → FrMove ρ' ν' y' y'' → FrMove (ρ ≫ ρ') κ y y'') ∧ ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), FrMap φ y z → FrMove ρ ν y y' → FrMove ρ ν z z' → FrMap φ y' z') ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' z z' : FrPt Xo c S), FrBor t y z → FrMove ρ ν y y' → FrMove ρ ν z z' → FrBor t y' z' :=
  fun _ _ _ _ _ _ _ _ _ => ⟨move_id, move_comp, fun _ _ =>
    ⟨fun _ _ _ _ _ _ _ _ _ _ _ => move_frMap, fun _ _ _ _ _ _ _ _ => move_frBor⟩⟩

end GlobalTheory.MoveCalc
