import Formalism.LocalToGlobal.Columns.DetChrOfChi
import Formalism.LocalToGlobal.Columns.Target
import Formalism.LocalToGlobal.Columns.RecLevelCls
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.Col

namespace DetChrChi

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

def ChiReads (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word) : Prop :=
  ∀ j (cl : StCl W Λ u j), ∃ y : D.Dt,
    ((D.chiD y : ℂˣ) : ℂ) = σ₀ ((Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u j cl) : X.Kˣ) : X.K) ∧
      K.idl (QuotientGroup.mk y) = TaylorLogMetric.detId D (StandardLatticesGL3.stdL D (R.N j)) (K.seam.lat (repN W Λ u j cl))

theorem pt_of_reads (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word)
    (h : ChiReads W Λ D K Dc hc u) (j : ℕ) (cl : StCl W Λ u j) :
    σ₀ ((Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u j cl) : X.Kˣ) : X.K) =
      K.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D (R.N j)) (K.seam.lat (repN W Λ u j cl))) := by
  obtain ⟨y, h1, h2⟩ := h j cl
  rw [← h1, K.χ_rec, ← h2, TaylorLogMetric.chiRec_idl D K.idl K.idl_ok.1]
  rfl

theorem chiDetTie_of_reads (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word)
    (h : ChiReads W Λ D K Dc hc u) : ChiDetTie W Λ σ₀ Dc hc K.amb u :=
  DetChrOf.chiDetTie_of_pt W Λ σ₀ Dc hc K.amb u (fun a N => K.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D a) (K.seam.lat N)))
    (fun _ _ _ _ => rfl) (pt_of_reads W Λ D K Dc hc u h)

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem carries_globLat (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    Formalism.L2.Herm.Carries g (stdLat E n) (Formalism.UG.CS.globLat g (stdLat E n)) := fun x =>
  Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.csGlob_intAdApprox F E (Fin n) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top g x

theorem isSDLat_globLat (hc : CMData F E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) :
    IsSDLat E n (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have hlat := Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top x
  have hU := globLat_unimodular hc n hx
  refine ⟨hlat.fg, hlat.span_eq_top, fun y => ?_⟩
  conv_lhs => rw [← hU]
  rw [mem_dual]
  refine forall₂_congr fun z _ => ?_
  rw [Submodule.mem_one, RingHom.mem_range]
  exact Iff.rfl

end Lat

section Rep

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

theorem repN_eq_globLat (hc : CMData X.F X.E) (u : Pr.Word) (j : ℕ) (hS : DecoPtSurj hc (R.N j) (Pr.vT u) Pr.vGs)
    (cl : StCl W Λ u j) :
    repN W Λ u j cl = Formalism.UG.CS.globLat (F := X.F) (repPt W Λ hc u j cl) (stdLat X.E (R.N j)) := by
  have : NeZero (R.N j) := ⟨(R.N_pos j).ne'⟩
  have h1 := decoOf_ptOf hc (R.N j) (Pr.vT u) Pr.vGs hS ((stepGSD W Λ u j).outSec.rep cl)
  have hok := decorated_lattice_exists hc (R.N j) (Pr.vT u) Pr.vGs _ (ptOf hc (R.N j) (Pr.vT u) Pr.vGs ((stepGSD W Λ u j).outSec.rep cl)).2
  show ((stepGSD W Λ u j).outSec.rep cl).1.N = _
  rw [← h1]
  unfold decoOf
  rw [dif_pos hok]
  rfl

theorem carries_rep (hc : CMData X.F X.E) (u : Pr.Word) (j : ℕ) (hS : DecoPtSurj hc (R.N j) (Pr.vT u) Pr.vGs)
    (cl : StCl W Λ u j) :
    Formalism.L2.Herm.Carries (repPt W Λ hc u j cl) (stdLat X.E (R.N j)) (repN W Λ u j cl) := by
  rw [repN_eq_globLat W Λ hc u j hS cl]
  exact carries_globLat (F := X.F) (E := X.E) _

end Rep

section Rel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

def RelReads (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word) : Prop :=
  ∀ j (cl : StCl W Λ u j), ∃ y : D.Dt,
    ((D.chiD y : ℂˣ) : ℂ) = σ₀ ((Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u j cl) : X.Kˣ) : X.K) ∧
      ∃ L L' : SDLat D.host.E (R.N j), L.1 = StandardLatticesGL3.stdL D (R.N j) ∧ L'.1 = K.seam.lat (repN W Λ u j cl) ∧
        (QuotientGroup.mk y : D.Dt ⧸ D.UO) = D.relDet (R.N j) L L'

theorem chiReads_of_rel (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word)
    (h : RelReads W Λ D K Dc hc u) : ChiReads W Λ D K Dc hc u := by
  intro j cl
  obtain ⟨y, h1, L, L', hL, hL', hy⟩ := h j cl
  refine ⟨y, h1, ?_⟩
  rw [hy, K.idl_ok.2.2.2.2 (R.N j) L L', hL, hL']

theorem chiDetTie_of_rel (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word)
    (h : RelReads W Λ D K Dc hc u) : ChiDetTie W Λ σ₀ Dc hc K.amb u :=
  chiDetTie_of_reads W Λ D K Dc hc u (chiReads_of_rel W Λ D K Dc hc u h)

end Rel

end DetChrChi

end Formalism.L2.Col
