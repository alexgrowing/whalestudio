import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulMemComplId
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumInfPartIntegralOneSubMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationOneElementAtGridPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharComb

variable {D : D7}

theorem pairA_zero_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  exact Prod.ext (zero_mul _) rfl

theorem intAf_mul {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F) :
    α * β ∈ intAf D.host.F := fun v => by
  rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem complId_mul {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x y : AE D} (hx : x ∈ complId 𝔞)
    (hy : y ∈ complId 𝔟) : x * y ∈ complId (𝔞 * 𝔟) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, a, ha, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβ, b, hb, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_zero_mul]
      exact tmul_mem_complId (intAf_mul hα hβ) (FractionalIdeal.mul_mem_mul ha hb)
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem infPart_of_mem {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x : AE D} (hx : x ∈ complId 𝔠) :
    infPart D x = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, -, a, -, rfl⟩ := hx
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] a = 0
    exact TensorProduct.zero_tmul _ _
  | zero => exact map_zero _
  | add x z _ _ hx hz => rw [RingHom.map_add, hx, hz, add_zero]
  | neg x _ hx => rw [RingHom.map_neg, hx, neg_zero]

def finId (𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : AddSubgroup (EAf D) :=
  (complId 𝔠).map (toEAf D).toAddMonoidHom

theorem finId_mul {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x y : EAf D} (hx : x ∈ finId 𝔞)
    (hy : y ∈ finId 𝔟) : x * y ∈ finId (𝔞 * 𝔟) := by
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  exact ⟨x₀ * y₀, complId_mul hx₀ hy₀, map_mul (toEAf D) x₀ y₀⟩

theorem tmul_one_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {a : D.host.E} (ha : a ∈ 𝔠) :
    a ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ finId 𝔠 :=
  ⟨_, tmul_mem_complId one_mem_intAf ha, rfl⟩

theorem int_mem_finId_one {z : EAf D} (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    z ∈ finId (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  induction hz using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨b, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨b, hb⟩ := b
      exact tmul_one_mem_finId ((FractionalIdeal.mem_one_iff _).2 hb)
    · exact ⟨_, tmul_mem_complId y.2 (FractionalIdeal.one_mem_one _), rfl⟩
  | zero => exact zero_mem _
  | one => exact tmul_one_mem_finId (FractionalIdeal.one_mem_one _)
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy => simpa using finId_mul hx hy

theorem idS_mem_finId (𝔪 : Ideal (𝓞 D.host.E)) {t : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (ht : t ∈ Formalism.L2.DIV.idS D.host.F 𝔪) :
    (t : EAf D) ∈ finId ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe]
    exact tmul_one_mem_finId ((FractionalIdeal.mem_coeIdeal _).2 ⟨m, hm, rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => rw [Subring.coe_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul]
    simpa using finId_mul (int_mem_finId_one c.2) hx

theorem idem_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {e : AE D} {Q : Formalism.L2.DIV.Pl D.host.E}
    (he : Formalism.L2.NTheta.IsIdemAt e Q) {a : D.host.E} (ha : a ∈ 𝔠)
    (hv : Valued.v (algebraMap D.host.E (Kw Q) a) = 1) : toEAf D e ∈ finId 𝔠 := by
  have ha0 : a ≠ 0 := fun h => by rw [h, map_zero, map_zero] at hv; exact zero_ne_one hv
  obtain ⟨h1, h2⟩ := GlobalTheory.StdFrames.cpt_of_isIdemAt he
  have hu : toEAf D e * (a⁻¹ ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    refine (GlobalTheory.StdFrames.mem_OA_iff _).2 fun Q' => ?_
    rw [map_mul, GlobalTheory.FunObj.Comparison₂.cpt_tmul]
    by_cases hQ : Q' = Q
    · subst hQ
      rw [h1, one_mul, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, hv, inv_one]
    · rw [h2 Q' hQ, zero_mul]
      exact zero_mem _
  have e1 : toEAf D e = (toEAf D e * (a⁻¹ ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F))) *
      (a ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) := by
    rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ ha0, one_mul,
      Algebra.TensorProduct.one_def.symm, mul_one]
  rw [e1]
  simpa using finId_mul (int_mem_finId_one hu) (tmul_one_mem_finId ha)

theorem toEAf_mem_finId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x : AE D} (hx : x ∈ complId 𝔠) :
    toEAf D x ∈ finId 𝔠 := ⟨x, hx, rfl⟩

theorem ring_key {R : Type*} [CommRing R] (e c : R) : c = e * (e * c) + ((1 + e) * (1 - e)) * c := by ring

theorem mem_complId_of_finId {𝔞 𝔟 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {c : AE D} (hc : c ∈ complId 𝔞)
    (h : toEAf D c ∈ finId 𝔟) : c ∈ complId 𝔟 := by
  obtain ⟨z, hz, hze⟩ := h
  have hze' : toEAf D z = toEAf D c := hze
  have hzc : z = c := GlobalTheory.DepthFix.ext_cpt (by rw [infPart_of_mem hz, infPart_of_mem hc])
    fun Q => by rw [hze']
  exact hzc ▸ hz

theorem core {𝔞 𝔟 𝔪 𝔡 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hid : 𝔪 * 𝔡 = 𝔞 * 𝔟) {e c : EAf D}
    (he : e ∈ finId 𝔞) (hec : e * c ∈ finId 𝔟) (hm : (1 + e) * (1 - e) ∈ finId 𝔪) (hc : c ∈ finId 𝔡) :
    c ∈ finId (𝔞 * 𝔟) := by
  have h3 := finId_mul hm hc
  rw [hid] at h3
  have h4 := add_mem (finId_mul he hec) h3
  rwa [← ring_key e c] at h4

theorem ideal_key {M A B : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hM : M ≠ 0) :
    M * (A * (B * M⁻¹)) = A * B := by
  calc _ = A * B * (M * M⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hM, mul_one]

theorem mem_complId_AA_AAbar : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 →
    ∀ {sc : Consts} (G : GridData L sc) (c : AE D), c ∈ complId (D.host.AA * G.pl.stAbar sc) →
    (∀ e, IsIdemSum e G.pl.W0 → e * c ∈ complId D.host.AAbar) → c ∈ complId (D.host.AA * D.host.AAbar) := by
  classical
  intro D hq T L μ0 hL sc G c hc hec
  obtain ⟨e, he⟩ := GlobalTheory.GridIdem.exists_idempotentSum_auxiliaryPlaces D T L G.pl
  have h1 := hec e he
  obtain ⟨-, heO, t, ht, hte⟩ := GlobalTheory.IdemSumIdeal.isIdemSum_props e G.pl.W0
    (fun Q => G.pl.depth sc (Q.under (𝓞 D.host.F))) he
  have hprod : (∏ Q ∈ G.pl.W0, Q.asIdeal ^ G.pl.depth sc (Q.under (𝓞 D.host.F))) = G.pl.modul sc := by
    unfold Places.W0 Places.modul
    rw [Finset.prod_image fun v hv v' hv' h =>
      (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))]
    exact Finset.prod_congr rfl fun v hv => by rw [G.pl.under_w hv]
  rw [hprod] at ht

  have heA : toEAf D e ∈ finId D.host.AA := by
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := id he
    rw [show toEAf D (∑ Q ∈ G.pl.W0, es Q) = ∑ Q ∈ G.pl.W0, toEAf D (es Q) from
      map_sum (toEAf D).toAddMonoidHom (fun Q => es Q) G.pl.W0]
    refine sum_mem fun Q hQ => ?_
    obtain ⟨a, ha, hv⟩ := GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hq hL G Q hQ
    exact idem_mem_finId (hes Q hQ) ha hv

  have ht2 : ((⟨1 + toEAf D e, add_mem (one_mem _) heO⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * t) ∈
      Formalism.L2.DIV.idS D.host.F (G.pl.modul sc) := Ideal.mul_mem_left _ _ ht
  have hM : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hid : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
      (D.host.AA * G.pl.stAbar sc) = D.host.AA * D.host.AAbar := ideal_key hM
  have hm := idS_mem_finId _ ht2
  rw [Subring.coe_mul, hte] at hm
  have h1f := toEAf_mem_finId h1
  rw [RingHom.map_mul] at h1f
  exact mem_complId_of_finId hc (core hid heA h1f hm (toEAf_mem_finId hc))

end GlobalTheory.XCharComb
