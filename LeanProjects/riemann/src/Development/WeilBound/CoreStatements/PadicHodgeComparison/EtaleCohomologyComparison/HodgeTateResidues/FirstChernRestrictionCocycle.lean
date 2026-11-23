import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsLiftOneSOfLevEqOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernJBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullTransport
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleChernClassEqKummerClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ForE

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open CH PAlg

theorem res_id_inj {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (j : ℕ) (a b : H F j)
    (h : (Mor.restrict F (𝟭 C)).pull j a = (Mor.restrict F (𝟭 C)).pull j b) : a = b := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact h

theorem two_cls {R : Type} [CommRing R] {C C' C'' : Type 1} [Category.{0} C] [Category.{0} C'] [Category.{0} C'']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} (m : CH.Mor F F' (RingHom.id R)) (S₀ : SubF F) (S : SubF F') (h₀) (c : R) (h)
    (G : C'' ⥤ C') (x : H S₀.fn 2) (w : Cn ((G ⋙ m.G) ⋙ F) 2)
    (hx : ∃ (z₀ : Cn ((G ⋙ m.G) ⋙ S₀.fn) 2) (hz₀ : d _ 2 z₀ = 0), (∀ s, (show S₀.S _ from z₀ s).1 = w s) ∧
      (cx _).cls z₀ hz₀ = (Mor.restrict S₀.fn (G ⋙ m.G)).pull 2 x)
    (z : Cn (G ⋙ F') 2) (hz : d _ 2 z = 0) (y : H F' 2) (hy : (cx _).cls z hz = (Mor.restrict F' G).pull 2 y)
    (hv : ∀ z' : Cn (G ⋙ F') 2, (∀ s, z' s = m.τ _ (w s)) → ∀ s, z' s = (c • z) s) :
    (Mor.restrict S.fn G).pull 2 ((subMor m S₀ S h₀).pull 2 x) = (Mor.restrict S.fn G).pull 2 ((mulTo c S h).pull 2 y) := by
  obtain ⟨z₀, hz₀, hP, hx⟩ := hx
  obtain ⟨ha, e₂⟩ := GlobalTheory.CompanionTheory.FirstChernComparison.pull_transport S₀.fn S.fn (subMor m S₀ S h₀) G x z₀ hz₀ hx
  obtain ⟨hb, f₂⟩ := GlobalTheory.CompanionTheory.FirstChernComparison.pull_transport F' S.fn (mulTo c S h) G y z hz hy
  refine e₂.symm.trans (Eq.trans ?_ f₂)
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext
    ((congrArg (m.τ _) (hP s)).trans (hv (fun s => m.τ _ (w s)) (fun _ => rfl) s))))

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* OC l}
  {C : Type 1} [Category.{0} C] {G : C ⥤ El (PX q κ)} {D : E.LineData X} (n : ℕ)

theorem log_eq (Λ : E.Lift G D) (w : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2) (hw : Λ.IsCoc n w) (s : ComposableArrows C 2)
    (y : (G.obj (s.obj (Fin.last 2))).1.obj.Acr n)
    (hy : y = B.dlog (B.DD false (G.obj (s.obj (Fin.last 2))).1.obj n) (l * n) ((GlobalTheory.CompanionTheory.FirstChernComparison.lam false n Λ).r s).val) :
    y = E.acrVal G n (s.obj (Fin.last 2)) (w s) :=
  (E.Main.logEx l _ n).2.1 _ _ _ (GlobalTheory.CompanionTheory.FirstChernComparison.st2 false n Λ s y hy) (hw s)

theorem tCo_eq (z : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2) : E.tCo G n 2 z = (tA l ^ 1 : Acris l) • z :=
  congrArg (fun a : Acris l => a • z) (pow_one (tA l : Acris l)).symm

theorem coc_eq (Λ : E.Lift G D) (w : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2) (hw : Λ.IsCoc n w)
    (z' : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2)
    (hz' : ∀ s, z' s = (B.βMor (B.schFn q) κ false n).τ _ ((GlobalTheory.CompanionTheory.FirstChernComparison.lam false n Λ).coc ((base l).cris n) (l * n) s))
    (s : ComposableArrows C 2) : z' s = w s :=
  log_eq n Λ w hw s _ (hz' s)

theorem isFirstChernJ_lift_cocycle (x : H (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1).fn 2)
    (hx : constant_weight_sum_bound.IsFirstChernClassDividedPower (q := q) (b := B.bs l false n) (ht := rfl) (κ := B.κb κ false n) D ((base l).cris n) (l * n) x)
    (Λ : E.Lift G D) :
    ∃ (z₀ : Cn (GlobalTheory.CompanionTheory.FirstChernComparison.gG false n G ⋙ (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1).fn) 2) (hz₀ : d _ 2 z₀ = 0),
      (∀ s, (show (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1).S _ from z₀ s).1 =
        (GlobalTheory.CompanionTheory.FirstChernComparison.lam false n Λ).coc ((base l).cris n) (l * n) s) ∧
      (cx _).cls z₀ hz₀ = (Mor.restrict (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1).fn
        (GlobalTheory.CompanionTheory.FirstChernComparison.gG false n G)).pull 2 x :=
  hx C (GlobalTheory.CompanionTheory.FirstChernComparison.gG false n G) (GlobalTheory.CompanionTheory.FirstChernComparison.lam false n Λ)

theorem firstChern_restriction_cocycle (ht : TFil l) (x : H (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1).fn 2)
    (hx : constant_weight_sum_bound.IsFirstChernClassDividedPower (q := q) (b := B.bs l false n) (ht := rfl) (κ := B.κb κ false n) D ((base l).cris n) (l * n) x)
    (Λ : E.Lift G D) (y : MH (PX q κ) n 2) (z : Cn (G ⋙ modF (AcrEl (PX q κ) n)) 2) (hz : d _ 2 z = 0)
    (hΛ : Λ.IsCoc n ((tA l ^ 1 : Acris l) • z)) (hy : (cx _).cls z hz = (Mor.restrict (modF (AcrEl (PX q κ) n)) G).pull 2 y) :
    (Mor.restrict (TT ((B.schFn q).pt κ) 1 n).fn G).pull 2 ((βMorF (B.schFn q) κ 1 n).pull 2 x) =
      (Mor.restrict (TT ((B.schFn q).pt κ) 1 n).fn G).pull 2 ((tMor ht ((B.schFn q).pt κ) 1 n).pull 2 y) :=
  two_cls (B.βMor (B.schFn q) κ false n) (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1) (TT ((B.schFn q).pt κ) 1 n) _
    (tA l ^ 1) _ G x ((GlobalTheory.CompanionTheory.FirstChernComparison.lam false n Λ).coc ((base l).cris n) (l * n)) (isFirstChernJ_lift_cocycle n x hx Λ) z hz y hy
    (coc_eq n Λ _ hΛ)

end

theorem firstChern_class_general (ht : TFil l) {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l)
    (D : E.LineData X) (n : ℕ) (x : H (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1).fn 2)
    (hx : constant_weight_sum_bound.IsFirstChernClassDividedPower (q := q) (b := B.bs l false n) (ht := rfl) (κ := B.κb κ false n) D ((base l).cris n) (l * n) x)
    (Λ : E.Lift (q := q) (κ := κ) (𝟭 _) D) (y : MH (PX q κ) n 2) (z : Cn (𝟭 _ ⋙ modF (AcrEl (PX q κ) n)) 2) (hz : d _ 2 z = 0)
    (hΛ : Λ.IsCoc n (E.tCo (𝟭 _) n 2 z)) (hy : (cx _).cls z hz = (Mor.restrict (modF (AcrEl (PX q κ) n)) (𝟭 _)).pull 2 y) :
    (βMorF (B.schFn q) κ 1 n).pull 2 x = (tMor ht ((B.schFn q).pt κ) 1 n).pull 2 y :=
  res_id_inj _ 2 _ _ (firstChern_restriction_cocycle n ht x hx Λ y z hz ((congrArg (Λ.IsCoc n) (tCo_eq n z)).mp hΛ) hy)

theorem firstChern_compatible_family {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* OC l)
    (D : E.LineData X) (hD : sSup (Pb.𝒱D D) = ⊤) :
    ∃ x : ∀ n, H (B.pdS (B.Lc (B.schFn q) κ false n) ((base l).cris n) 1).fn 2,
      (∀ n, constant_weight_sum_bound.IsFirstChernClassDividedPower (q := q) (b := B.bs l false n) (ht := rfl) (κ := B.κb κ false n) D ((base l).cris n) (l * n) (x n)) ∧
      ∀ n, (pdOm (CrystallineSemistableComparison.SH.redM (B.schFn q) κ false n) (RingHom.id _) (B.red_cris _ n.le_succ) 1).pull 2 (x (n + 1)) = x n := by
  have ex : ∀ n, ∃! x, constant_weight_sum_bound.IsFirstChernClassDividedPower (q := q) (b := B.bs l false n) (ht := rfl) (κ := B.κb κ false n) D
      ((base l).cris n) (l * n) x := fun n =>
    constant_weight_sum_bound.exu (B.DD false (base l) n) l (Fact.out : l.Prime).ne_zero q (B.κb κ false n) D hD
      ((base l).cris n) (l * n) (GlobalTheory.CompanionTheory.FirstChernClassFactorial.factorial_acr n _ le_rfl)
  choose x hx hu using ex
  exact ⟨x, hx, fun n => hu n _ (constant_weight_sum_bound.isFirstChernJ_base_change (b := B.bs l false (n + 1)) (b' := B.bs l false n) ((base l).red n.le_succ) rfl
    (B.dd_red false _ n.le_succ) (Ideal.quotientMap _ _ (B.red_le false n.le_succ)) (B.red_κb κ false n.le_succ) (fun _ _ _ => rfl)
    _ _ (B.red_cris _ n.le_succ) D (Nat.mul_le_mul_left l n.le_succ) (fun j hj => GlobalTheory.CompanionTheory.FirstChernClassFactorial.factorial_acr n j hj)
    (x (n + 1)) (hx (n + 1)))⟩

theorem firstChern_family_exists (M : Model l K) (D : E.LineData M.X) (hD : sSup (Pb.𝒱D D) = ⊤) : ∃ x : Fam M 1 2, IsFirstChernClassInFamily D x ∧ Comp x :=
  firstChern_compatible_family M.p (okToOC l K) D hD

theorem h1_lift_of_firstChern (ht : TFil l) {e : E.EtFam l K} (he : EtP e) : ∀ (M : Model l K) (D : E.LineData M.X), Etale D.f →
    sSup (Pb.𝒱D D) = ⊤ → ∀ (r : E.Roots l) (v : M.T 2), IsEtaleFirstChernUntwisted r D v → ∃ x, IsFirstChernClassInFamily D x ∧ IsLift ht e 1 v x :=
  fun M D hf hD r v hv => (firstChern_family_exists M D hD).elim fun x hx =>
    ((E.Main.liftEx l (R.forE l) _ M.X M.p (okToOC l K) _ (𝟭 _) D).2 hf).elim fun Λ =>
      ⟨x, hx.1, hx.2, fun n => (he.c1 M D r v hv _ (𝟭 _) Λ n).elim fun z h => h.elim fun hz h' =>
        firstChern_class_general ht M.p (okToOC l K) D n (x n) (hx.1 n) Λ (e M n 2 (v.lev n)) z hz h'.1 h'.2⟩

end CrystallineSemistableComparison.HT
