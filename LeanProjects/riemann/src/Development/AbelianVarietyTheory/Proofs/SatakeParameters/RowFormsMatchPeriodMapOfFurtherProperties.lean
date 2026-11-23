import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
import Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.KerRat GlobalTheory.Mem.Df GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped Matrix

namespace GlobalTheory.AtG.RX

section Fam
variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (R3.Gc X.B px → X.B.LL))
  (tr : R3.TrI X.B px) (a : I.ι)

set_option maxHeartbeats 1000000 in

theorem isFormOf_exists (z : MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) :
    ∃ y, IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y) := by
  have hK := mtildeKOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX
  obtain ⟨hφ, -⟩ := (mem_MtildeV_iff (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) z.1).1 z.2
  let F : (mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a)).EqFun := ⟨z.1, hφ⟩
  have h1 := (mem_lvlPartX_iff (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hK F).2 z.2
  rw [← LiftForms.range_lvlE] at h1
  obtain ⟨y, hy⟩ := h1
  refine ⟨y, F, z.2, ?_, rfl⟩
  apply heq_of_eq
  show _ = (MtildeKCSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hK).basis.equivFun.symm
    ((MtildeKCSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hK).lvlE _ _ _ *ᵥ y)
  rw [Matrix.mulVecLin_apply] at hy
  rw [hy]
  exact ((MtildeKCSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hK).basis.equivFun.symm_apply_apply _).symm

theorem isFormOf_unique {y} {z z' : MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)}
    (h : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y))
    (h' : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z'
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y)) : z = z' := by
  obtain ⟨F, hF, e1, rfl⟩ := h
  obtain ⟨F', hF', e2, rfl⟩ := h'
  have e3 := eq_of_heq (e1.trans e2.symm)
  have e4 := ((mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a)).res _).injective e3
  subst e4
  rfl

set_option maxHeartbeats 1000000 in

theorem isFormOf_mem_iff {y} {z : MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)}
    (h : IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) z
      (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y)) :
    y ∈ rNab X.toD7 (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) ↔
      z ∈ MtildeL (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) := by
  obtain ⟨F, hF, e1, rfl⟩ := h
  have e2 := eq_of_heq e1
  refine (LiftForms.mem_lvlNab _ _ _ _ y).trans ?_
  show R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) y ∈ intForms _ ↔ _
  rw [← e2]
  exact (GSD.mem_intNab_iff _ (mtildeKOk (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX) _ F).symm

end Fam

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0}

theorem lat_of_rx (x : RXs t) (a : w.C.Tup) :
    (∀ v ∈ (Z.W.Mtilde a).gen, ∃ z, x.e a (toCx w.I t.hX a z) = v) ∧
    ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (w.I.tup a) (TC.Ps w.I) ↔ ∃ c : Z.W.Amb a → 𝓞 B.LL,
      x.e a (toCx w.I t.hX a z) = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v := by
  classical
  obtain ⟨hg, hiff⟩ := x.all.latA a
  have hc := x.crd a
  refine ⟨fun v hv => ?_, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := hg v hv
    obtain ⟨z, -, hz⟩ := hc y
    exact ⟨z, hz.symm⟩
  · obtain ⟨y, hy⟩ := isFormOf_exists (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a z
    obtain ⟨z', hz', hj⟩ := hc y
    have e := isFormOf_unique (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a hy hz'
    obtain ⟨c, hc'⟩ := (hiff y).1 ((isFormOf_mem_iff (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a hy).2 hz)
    exact ⟨c, by rw [e, ← hj]; exact hc'⟩
  · rintro ⟨c, hc'⟩
    choose! g hgy using hg
    let n := rDim (w.st Z).toD7 (famAll t) (R3.lev1 w.I) (R3.chr1 w.I) (tAll w.I a)
    let y : Fin n → B.LL := ∑ v ∈ (Z.W.Mtilde a).gen, ((c v : 𝓞 B.LL) : B.LL) • @id (Fin n → B.LL) (g v)
    have hjy : x.all.jA a y = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v := by
      let J : (Fin n → B.LL) →ₛₗ[B.embLL] Z.W.Amb a := x.all.jA a
      refine (map_sum J _ _).trans (Finset.sum_congr rfl fun v hv => ?_)
      exact (J.map_smulₛₗ _ _).trans (congrArg _ (hgy v hv))
    obtain ⟨z', hz', hj⟩ := hc y
    have e : z' = z := by
      apply toMtilde_injective (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (w.I.tup a) (TC.Ps w.I) B.embLL
      apply (x.e a).injective
      exact hj.symm.trans (hjy.trans hc'.symm)
    rw [← e]
    exact (isFormOf_mem_iff (w.st Z) w.I t.hX t.r.z.Xg t.r.z.tr a hz').1 ((hiff y).2 ⟨c, hjy⟩)

section Core

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (hX : B.fields.Ok)

theorem eq_rowForm' (u : B.Word) (a : I.ι) (z : MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps) (G : (I.per l u a).Mt)
    (hG : SameForm I l u a (toCx I hX a z) G) : G = rowForm I l h u a z :=
  Subtype.ext (funext fun _ => funext fun p => hG p)

theorem rowPin_core (Z : TC.Later B (I.cols l)) (e0 : ∀ a : (I.cols l).Tup, MtCx I a ≃ₗ[ℂ] Z.W.Amb a)
    (u : B.Word) (a : (I.cols l).Tup) (e : (I.per l u a).Mt ≃ₗ[ℂ] Z.W.Amb a)
    (he : ∀ F, SameForm I l u a F (e.symm (e0 a F)))
    (hgen : ∀ v ∈ (Z.W.Mtilde a).gen, ∃ z, e0 a (toCx I hX a z) = v)
    (hlat : ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps ↔ ∃ c : Z.W.Amb a → 𝓞 B.LL,
      e0 a (toCx I hX a z) = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v) :
    (∀ v ∈ (Z.W.Mtilde a).gen, ∃ z, e (rowForm I l h u a z) = v) ∧
    ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps ↔ ∃ c : Z.W.Amb a → 𝓞 B.LL,
      e (rowForm I l h u a z) = ∑ v ∈ (Z.W.Mtilde a).gen, B.embLL ((c v : 𝓞 B.LL) : B.LL) • v := by
  have key : ∀ z, e (rowForm I l h u a z) = e0 a (toCx I hX a z) := fun z => by
    rw [← eq_rowForm' I h l hX u a z _ (he _)]
    exact e.apply_symm_apply _
  refine ⟨fun v hv => ?_, fun z => ?_⟩
  · obtain ⟨x, hx⟩ := hgen v hv
    exact ⟨x, (key x).trans hx⟩
  · rw [key]
    exact hlat z

end Core

theorem rowPin_of_rx : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0), RX K B f T w Z Wt p0 t → ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a := by
  intro K B f T w Z Wt p0 t x a u
  obtain ⟨hg, hl⟩ := lat_of_rx (t := t) x a
  by_cases ha : a = (w.D Z).what₂.mu0
  · subst ha
    exact ⟨Z.W.eMt0 u, fun _ => HEq.rfl, fun hn => absurd rfl hn,
      rowPin_core w.I w.ok w.l t.hX Z x.e u _ (Z.W.eMt0 u) (x.eMt0 u) hg hl⟩
  · exact ⟨Z.W.eMtTw u a, fun hn => absurd hn ha, fun _ => rfl,
      rowPin_core w.I w.ok w.l t.hX Z x.e u a (Z.W.eMtTw u a) (x.eMtTw u a) hg hl⟩

end GlobalTheory.AtG.RX

end
