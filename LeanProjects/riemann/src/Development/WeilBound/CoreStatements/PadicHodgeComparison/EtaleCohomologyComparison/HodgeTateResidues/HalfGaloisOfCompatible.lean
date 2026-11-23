import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ToYIsFirstChernIff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.CompId
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsLiftOneSOfLevEqOne

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.HT

open PAlg H2

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (ht : TFil l) (hs : CrisSurj l)
  {S : ∀ m, Lv (cb K ht hs) (m + 1)} (H : Hyp S)

theorem cY {M : Model l K} {r j : ℕ} {x : Fam M r j} (h : Comp x) : CB.Comp (toY ht hs x) := (toY_comp ht hs x).2 h

theorem toY_pull {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) {r j : ℕ} (x : Fam N r j) (n : ℕ) :
    toY ht hs (pullS u hu x) n = (pdOm (c := (cb K ht hs).c n) (c' := (cb K ht hs).c n) (pullM (cb K ht hs) u hu n)
      (RingHom.id (cb K ht hs).Λ) (fun _ => rfl) r).pull j (toY ht hs x n) := rfl

def galY (M : Model l K) (σ : K.fixingSubgroup) (n : ℕ) : GlobalTheory.LogCris.Mor ((cb K ht hs).L M n) ((cb K ht hs).L M n)
    (galBase (IntermediateField.fixingSubgroupEquiv K σ) n) :=
  CrystallineSemistableComparison.SH.galM (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) false n

theorem galY_pt (M : Model l K) (σ : K.fixingSubgroup) (n : ℕ) (B₀ : CommRingCat.{0}) (y : ((cb K ht hs).L M n).Pt.obj B₀) :
    ((galY ht hs M σ n).pt.app B₀ y).1.2 = y.1.2 :=
  CrystallineSemistableComparison.SH.base_snd (B.schFn M.p) (B.gal_κb (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) false n) B₀ y

theorem toY_gal {M : Model l K} (σ : K.fixingSubgroup) {r j : ℕ} (x : Fam M r j) (n : ℕ) :
    toY ht hs (galS σ x) n = (pdOm (c := (cb K ht hs).c n) (c' := (cb K ht hs).c n) (galY ht hs M σ n)
      (ACris.galCris (IntermediateField.fixingSubgroupEquiv K σ)) (galBase_cris _ n) r).pull j (toY ht hs x n) := rfl

include H in
theorem half_galois_of_compatible (hg : ∀ (m : ℕ) (σ : K.fixingSubgroup), Nonempty (LHom (S m) (S m)
    (ACris.galCris (IntermediateField.fixingSubgroupEquiv K σ)) (galBase (IntermediateField.fixingSubgroupEquiv K σ))
    (period_ring_base.σC σ.1).toRingHom (qC l (period_ring_base.χ σ.1)))) :
    Half2 (K := K) ht fun x => gam S (toY ht hs x) where
  add hM _ _ x y hx hy a := H.add hM (cY ht hs hx) (cY ht hs hy) (cY ht hs (comp_add hx hy)) a
  lin hM _ _ c x hx a φ := H.lin hM c (cY ht hs hx) (cY ht hs (comp_smul c hx)) a φ
  lin' hM _ _ x hx a k φ := H.lin' hM (cY ht hs hx) a k φ
  sh hM _ _ _ k h x hx a := H.sh hM k h (cY ht hs hx) (cY ht hs (comp_sh ht k h hx)) a
  gal {M} hM r _ σ x hx a φ := H.gal hM (hg r σ).some (galY ht hs M σ) (galY_pt ht hs M σ) (cY ht hs hx) _
    (cY ht hs (comp_gal σ hx)) (fun n => galBase_cris _ n) (toY_gal ht hs σ x) a φ
  nat u hu hM hN _ _ x hx a φ := H.nat hM hN u hu (cY ht hs hx) _ (cY ht hs (comp_pull u hu hx)) (toY_pull ht hs u hu x) a φ
  cup hM _ _ _ _ _ h x y hx hy _ _ b b' c φ := H.cup hM h (cY ht hs hx) (cY ht hs hy) (cY ht hs (comp_cup h hx hy)) b b' c φ
  one {M} hM φ := H.one hM (cY ht hs (comp_one M)) φ
  c1 hM D hD x c hx h1 h2 := H.c1' hM D hD _ c (cY ht hs hx) ((toY_isFirstChern_iff ht hs D x).2 h1) h2

variable (l K) in
theorem half2Of : Half2Of l K := fun ht hs hL h1 h2 h3 h4 h5 h6 h7 _ =>
  (hL ht hs).elim fun S => ⟨_, half_galois_of_compatible ht hs (S := S.L) ⟨h1, h2, h3, h4, h5, h6, h7, fun m => ⟨S.dn m⟩⟩ fun m σ => ⟨S.gal m σ⟩⟩

end CrystallineSemistableComparison.HT
