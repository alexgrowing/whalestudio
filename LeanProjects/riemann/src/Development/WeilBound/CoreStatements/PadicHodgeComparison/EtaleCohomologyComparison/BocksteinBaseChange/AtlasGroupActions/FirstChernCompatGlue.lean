import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.AtlasOf

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueB'

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (Amp : ∀ M : Model l K, E.LineData M.X → Prop)

theorem f_act (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (σ : K.fixingSubgroup) (x : ((dat Amp).H a).N j) :
    bβ Amp hC a j (((dat Amp).H a).act j σ x) = ((dat Amp).A a).act j σ (bβ Amp hC a j x) :=
  GlueBL.lim_sq (βS hC (B.schFn M.p) (okToOC l K) false j) (βS hC (B.schFn M.p) (okToOC l K) false j)
    (M.galH false j (IntermediateField.fixingSubgroupEquiv K σ)) (M.galS j (IntermediateField.fixingSubgroupEquiv K σ))
    (fun n y => hC.gal (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) false n j y) x

theorem f_act' (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (σ : K.fixingSubgroup) (x : ((dat Amp).H' a).N j) :
    bβ' Amp hC a j (((dat Amp).H' a).act j σ x) = ((dat Amp).A a).act j σ (bβ' Amp hC a j x) :=
  GlueBL.lim_sq (βS hC (B.schFn M.p) (okToOC l K) true j) (βS hC (B.schFn M.p) (okToOC l K) true j)
    (M.galH true j (IntermediateField.fixingSubgroupEquiv K σ)) (M.galS j (IntermediateField.fixingSubgroupEquiv K σ))
    (fun n y => hC.gal (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K σ) (galOC_okToOC _) true n j y) x

theorem f_phi' (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (x : ((dat Amp).H' a).N j) :
    bβ' Amp hC a j ((dat Amp).phi' a j x) = (dat Amp).phiA a j (bβ' Amp hC a j x) :=
  GlueBL.lim_sq (βS hC (B.schFn M.p) (okToOC l K) true j) (βS hC (B.schFn M.p) (okToOC l K) true j)
    (M.phiH j) (M.phiS j) (fun n y => hC.phi (B.schFn M.p) (okToOC l K) n j y) x

theorem f_nat (hC : B.Compat l) {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : (dat Amp).Ch M}
    {b : (dat Amp).Ch N} (m : (dat Amp).Mo u hu a b) (j : ℕ) (x : ((dat Amp).H b).N j) :
    bβ Amp hC a j ((dat Amp).pullH m j x) = (dat Amp).pullA m j (bβ Amp hC b j x) :=
  GlueBL.lim_sq (βS hC (B.schFn N.p) (okToOC l K) false j) (βS hC (B.schFn M.p) (okToOC l K) false j)
    (Model.pullH u hu false j) (Model.pullS u hu j) (fun n y => hC.pull (okToOC l K) (B.schMap u hu) false n j y) x

theorem f_nat' (hC : B.Compat l) {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : (dat Amp).Ch M}
    {b : (dat Amp).Ch N} (m : (dat Amp).Mo u hu a b) (j : ℕ) (x : ((dat Amp).H' b).N j) :
    bβ' Amp hC a j (datPull Amp m j x) = (dat Amp).pullA m j (bβ' Amp hC b j x) :=
  GlueBL.lim_sq (βS hC (B.schFn N.p) (okToOC l K) true j) (βS hC (B.schFn M.p) (okToOC l K) true j)
    (Model.pullH u hu true j) (Model.pullS u hu j) (fun n y => hC.pull (okToOC l K) (B.schMap u hu) true n j y) x

theorem f_cup (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) {i j : ℕ} (x : ((dat Amp).H a).N i)
    (y : ((dat Amp).H a).N j) (z : ((dat Amp).H a).N (i + j)) (hz : ((dat Amp).H a).cup x y z) :
    ((dat Amp).A a).cup (bβ Amp hC a i x) (bβ Amp hC a j y) (bβ Amp hC a (i + j) z) :=
  GlueBL.lim_cup (fun j => βS hC (B.schFn M.p) (okToOC l K) false j)
    (fun n i j x y => hC.cup (B.schFn M.p) (okToOC l K) false n rfl x y) x y z hz

theorem f_one (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (x : ((dat Amp).H a).N 0) (hx : ((dat Amp).H a).one x) :
    ((dat Amp).A a).one (bβ Amp hC a 0 x) :=
  GlueBL.lim_one (fun j => βS hC (B.schFn M.p) (okToOC l K) false j)
    (fun n => hC.one (B.schFn M.p) (okToOC l K) false n) x hx

theorem first_chern_compat_glue (hC : B.Compat l) (h1 : B.FirstChernCompatible l) {M : Model l K} (a : (dat Amp).Ch M) (x : ((dat Amp).H a).N 2)
    (hx : (dat Amp).c1H a x) : (dat Amp).c1A a (bβ Amp hC a 2 x) :=
  h1 M.p (okToOC l K) false a.1 _ hx

def bmap (hMain : B.Main l) (hC : B.Compat l) (h1 : B.FirstChernCompatible l) : BMap Model.Sm (dat Amp) where
  β a j := bβ Amp hC a j
  β' a j := bβ' Amp hC a j
  act a _ j σ x := f_act Amp hC a j σ x
  nat m _ _ j x := f_nat Amp hC m j x
  cup a _ _ _ x y z hz := f_cup Amp hC a x y z hz
  one a _ x hx := f_one Amp hC a x hx
  c1 a _ x hx := first_chern_compat_glue Amp hC h1 a x hx
  inj a hM j := f_inj Amp hMain hC a hM j
  surj a hM j := f_surj Amp hMain hC a hM j
  act' a _ j σ x := f_act' Amp hC a j σ x
  phi' a _ j x := f_phi' Amp hC a j x
  surj' a hM j := f_surj' Amp hMain hC a hM j

def bphi (hMain : B.Main l) (hC : B.Compat l) (h1 : B.FirstChernCompatible l) : BPhi (bmap Amp hMain hC h1) where
  pull m j := datPull Amp m j
  nat m _ _ j x := f_nat' Amp hC m j x
  inj a hM j := f_inj' Amp hMain hC a hM j

end GlueB'

theorem glueB : GlueB := fun l _ K Amp hMain hC h1 =>
  ⟨GlueB'.bmap Amp hMain hC h1, GlueB'.bphi Amp hMain hC h1, rfl⟩

end CrystallineSemistableComparison
