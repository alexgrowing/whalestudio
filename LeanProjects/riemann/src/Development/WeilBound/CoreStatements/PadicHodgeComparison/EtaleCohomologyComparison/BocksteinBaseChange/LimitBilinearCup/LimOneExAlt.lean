import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtMapP
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimitBilinearCup.PairingFirstChernValue
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimitBilinearCup.LimOneEx
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.FirstChernCompatGlue
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.FirstChernClassUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.EtaleMapFirstChern
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.IsUOfIsUnit

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueP'

theorem lim_one_ex {R : Type} [CommRing R] {Γ : Type} (S : ℕ → Sys.{1} R) {σ : Γ → R →+* R}
    (act : ∀ j g, Sys.Hom (S j) (S j) (σ g)) (one : ∀ n, (S 0).M n)
    (cup : ∀ n i j, (S i).M n → (S j).M n → (S (i + j)).M n) (ho : ∀ n, (S 0).r n (one (n + 1)) = one n) :
    ∃ x, (limAlg S act one cup).one x :=
  ⟨(⟨one, ho⟩ : (S 0).lim), fun _ => rfl⟩

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem one_ex (hC : B.CompatH l) (M : Model l K) : ∃ x, (M.HA true).one x :=
  lim_one_ex (M.HS true) _ _ _ (fun n => hC.one (B.schFn M.p) (okToOC l K) true n.le_succ)

theorem b_one (hC : B.Compat l) (M : Model l K) (x : (M.HA true).N 0) (hx : (M.HA true).one x) :
    M.MA.one ((GlueB'.βS hC (B.schFn M.p) (okToOC l K) true 0).lim x) :=
  GlueBL.lim_one (fun j => GlueB'.βS hC (B.schFn M.p) (okToOC l K) true j) (fun n => hC.one (B.schFn M.p) (okToOC l K) true n) x hx

theorem b_cup (hC : B.Compat l) (M : Model l K) {i j : ℕ} (x : (M.HA true).N i) (y : (M.HA true).N j)
    (z : (M.HA true).N (i + j)) (hz : (M.HA true).cup x y z) :
    M.MA.cup ((GlueB'.βS hC (B.schFn M.p) (okToOC l K) true i).lim x) ((GlueB'.βS hC (B.schFn M.p) (okToOC l K) true j).lim y)
      ((GlueB'.βS hC (B.schFn M.p) (okToOC l K) true (i + j)).lim z) :=
  GlueBL.lim_cup (fun j => GlueB'.βS hC (B.schFn M.p) (okToOC l K) true j)
    (fun n i j x y => hC.cup (B.schFn M.p) (okToOC l K) true n rfl x y) x y z hz

theorem cup_ex (hC : B.CompatH l) (M : Model l K) {i j : ℕ} (x : (M.HA true).N i) (y : (M.HA true).N j) :
    ∃ z, (M.HA true).cup x y z :=
  GlueLim.cup_ex (M.HS true) _ _ (fun n _ _ x y => (CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) true n)).cup rfl x y)
    (GlueL'.red_cup hC M true) x y

variable (Amp : ∀ M : Model l K, E.LineData M.X → Prop)

variable (r : Res l K) (ζ : E.Roots l) (μ : r.Cup)

theorem xlaws (hR : E.RIn l) (hU : E.FirstChernUniqueEtale) (hCH : B.CompatH l) (hMain : B.Main l) (hC : B.Compat l) (h1 : B.FirstChernCompatible l)
    (e : E.EtFam l K) (he : e.Good) (hone : ∀ (M : Model l K) n, e M n 0 (GlobalTheory.EtC.one (l ^ n) _) = CH.oneH _)
    (hc1 : ∀ (M : Model l K) D v, HT.IsEtaleFirstChernUntwisted ζ D v → E.IsFirstChernClassOfLineBundle M.p (okToOC l K) D (e.tMul M v))
    (F : FMap Model.Sm r.perC r.iso (dat Amp) (datPull Amp)) (hF : FPlus (r.xmid ζ μ Amp) F) :
    XLaws (r.xmid ζ μ Amp) (GlueE.emap Amp e he) (GlueB'.bmap Amp hMain hC h1) (GlueB'.bphi Amp hMain hC h1) F where
  e_one := fun {M} _ _ v hv n => (congrArg (e M n 0) (hv n)).trans (hone M n)
  etale_firstChern := fun {M} _ _ L v hv => hc1 M L.1 v hv
  first_chern_class_unique := fun {M} _ _ L x y hx hy => Subtype.ext (hU l hR (OK l K) M.X M.p (okToOC l K) L.1 L.2.1 _ _ hx hy)
  one_ex := fun {M} _ _ => one_ex hCH M
  cup_ex := fun {M} _ _ _ _ x y => cup_ex hCH M x y
  first_chern_class_exists := fun {M} a hM L => (hF.first_chern_class_exists a hM L).1
  β_one := fun {M} _ _ x hx => b_one hC M x hx
  β_cup := fun {M} _ _ _ _ x y z hz => b_cup hC M x y z hz
  beta_firstChern := fun {M} _ _ L x hx => h1 M.p (okToOC l K) true L.1 _ hx
  ψ_one := fun {M} a hM x y hx hy f => hF.one a hM x y hx hy f
  ψ_cup := fun {M} a hM _ _ x y z hz _ _ b b' f => hF.cup a hM x y z hz b b' f
  psi_firstChern := fun {M} a hM L x y hx hy f => hF.c1 a hM L x y hx hy f

end GlueP'

open GlueP' in

theorem glueP : GlueP := fun hCf hI h hE hP l _ K _ r ζ =>
  Exists.elim (cupEx l K r) fun μ hμ =>
  Exists.elim (h.p l K) fun Amp hA =>
  Exists.elim (hE l K ζ) fun e he =>
  Exists.elim (hP l K r ζ μ Amp hμ) fun F hF =>
  Exists.elim (phiPlus l K (per l K) Model.Sm r.perC r.iso (dat Amp) (r.xend ζ μ) (r.xmid ζ μ Amp) (facts l K)
      (hCf l K r).1 (hI l K) (glueL l K Amp (h.compatH l) (h.rin l) h.uniq hA.1 hA.2.1) (GlueE.emap Amp e he.1)
      (GlueB'.bmap Amp (h.main l) (h.compat l) (h.c1 l)) (GlueB'.bphi Amp (h.main l) (h.compat l) (h.c1 l))
      hA.2.2.1.some F (xlaws Amp r ζ μ (h.rin l) h.uniq (h.compatH l) (h.main l) (h.compat l) (h.c1 l) e he.1 he.2.1
        he.2.2.1 F hF)) fun c hc =>
  ⟨μ, F.k, c, hμ, fun M hM => ⟨he.2.2.2.2 M, Exists.elim (limOne_ex r M) fun x hx => ⟨_, x, hx, rfl⟩,
    fun L => ⟨he.2.2.2.1 M L.1, Exists.elim (hA.2.1 M hM) fun D hD => (hF.first_chern_class_exists ⟨D, hD⟩ hM L).2⟩⟩, hc⟩

end CrystallineSemistableComparison
