import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingPadicComplexInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlCSurjectiveAndLinearIndependentBLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieTieOfFrMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentEvLieOfLieTie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EvLawsGenFrNonemptyComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameLawsOfModuli
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section General

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
  {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  [Algebra c.F C] [StarRing (𝓞 E)]

theorem fg_htLat (P : Point p v O (𝓞 E)) (τ : E →+* ℂ) : (htLat c P τ).FG := by
  classical
  unfold htLat
  split_ifs
  · exact P.fg_latTQuot _ _
  · exact fg_inf P.integers P.fg_latT _

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem exists_isHTFrame (hs : ∀ a : 𝓞 E, star a = H.bar a) (hv : v.Integers O) {T : CDVR} {io : c.F →+* T.Fr}
    (y₀ : IntFr Xo c T io) (hy : y₀.IsAlg) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O)
    (hk : ∀ a, algebraMap O C (kO a) = k (algebraMap T.V T.Fr a)) :
    ∃ y : FrPt Xo c C, IsHTFrame p v O y₀ k y := by
  classical
  letI := io.toAlgebra
  obtain ⟨P, ψ, hP⟩ := GlobalTheory.CompHt.exists_pointOver E H Dw l Xo c p C v O hs hv T io y₀ hy k.toRingHom kO hk
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.allSixLaws.1.secBaseChange E H Dw l Xo c _ C k y₀.1
  obtain ⟨x, hx⟩ := GlobalTheory.CompHt.TieFrame.exists_lieTie_of_frMap E H Dw l Xo c p C v O T io y₀ k kO P ψ z hP hz
  have hli : ∀ τ, LinearIndependent C fun j => P.bLie (x τ j) := fun τ =>
    (GlobalTheory.CompHt.alC_surjective_and_linearIndependent_bLie p C v O (𝓞 E) P (GlobalTheory.T.hodgeTate_inclusion_raynaudExtension_algebraicPoint E H Dw l Xo c p C v O T io y₀ hy k.toRingHom kO P ψ hP)).2 _ (x τ)
      (GlobalTheory.CompHt.linearIndependent_evLie_of_lieTie E H Dw l Xo c p C v O T io y₀ k kO P ψ z hP hz τ (x τ) (hx τ))
  have hmem : ∀ τ j, P.bLie (x τ j) ∈ htLat c P τ := fun τ j =>
    wRec_le_htLat P τ ⟨⟨x τ j, (hx τ j).isEig hP (z.eig τ j)⟩, rfl⟩
  choose g hg0 hg1 hg2 using fun τ => GlobalTheory.CompHt.FlagBasis.exists_adapted_basis O C P.V v hv (Dw.mult τ) (htLat c P τ) (fg_htLat P τ)
    (fun j => P.bLie (x τ j)) (hli τ) fun j => ⟨1, one_ne_zero, by rw [one_smul]; exact hmem τ j⟩
  obtain ⟨y, hy', -⟩ := existsUnique_frChg E H Dw l Xo c C z g 1 fun τ => by
    rw [Matrix.det_of_lowerTriangular _ fun i j hij => hg0 τ i j hij]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hg1 τ i).isUnit
  exact ⟨y, (GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c).1.2.2.2.2.1 C y, kO, P, ψ, z, hP, hz, g, _, x, hy', hg0,
    by simp, hx, hg2⟩

end General

attribute [local instance] algPadicInt algPadicField towerPadic factPadic PadicComplexHost.isAdicComplete

theorem exists_isHTFrameCp {T : CDVR} {io : c.F →+* T.Fr} (y₀ : IntFr Xo c T io) (hy : y₀.IsAlg) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra c.F ℂ_[p]) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p])
      (y : FrPt Xo c ℂ_[p]), IsHTFrameCp p y₀ k y := by
  obtain ⟨p, hp, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hy
  letI := io.toAlgebra
  letI : Algebra c.F ℂ_[p] := (k.comp io).toAlgebra
  letI := H.starRing
  obtain ⟨y, h⟩ := exists_isHTFrame (p := p) (v := (Valued.v : Valuation ℂ_[p] ℝ≥0)) (O := 𝓞_ℂ_[p]) (fun _ => rfl)
    (PadicComplexInt.integers p) y₀ hy { k with commutes' := fun _ => rfl } kO hk
  exact ⟨p, hp, _, _, y, h⟩

theorem exists_isHTFrameCp_and_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg → ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra c.F ℂ_[p]) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p]) (y : FrPt Xo c ℂ_[p]), IsHTFrameCp p y₀ k y) ∧ (1 ≤ Dw.p + Dw.q → (∀ q : ℕ, q.Prime → l.GoodAt q) → ∀ (B : ℝ) (la : HeightOneSpectrum (𝓞 c.F)), ((htVals Xo c).1 la).Nonempty ∧ ((mixVals Xo c B).1 la).Nonempty) := by
  intro E _ _ _ H Dw l Xo c
  refine ⟨fun T io y₀ hy => exists_isHTFrameCp y₀ hy, fun hpq hg B la => ?_⟩
  obtain ⟨Z⟩ := (GlobalTheory.Reg.evLaws_genFr_nonempty_comp E H Dw l Xo c).2.2.2 hpq
  have hv : (valSet Xo c (algCls Xo c) la).Nonempty :=
    (GlobalTheory.FlatLine.valOn_nonempty (((GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c).2 hpq).2.2 hg).1 Z la).mono
      (GlobalTheory.FlatLine.valOn_subset Z la)
  have hh : ((htVals Xo c).1 la).Nonempty := by
    obtain ⟨_, ⟨_, T, io, e, ho, y₀, hy, -⟩, -⟩ := hv
    obtain ⟨p, hp, inst, k, y, h⟩ := exists_isHTFrameCp y₀ hy
    exact ⟨_, p, hp, inst, T, io, e, y₀, k, y, ho, hy, h, rfl⟩
  refine ⟨hh, ?_⟩
  simp only [mixVals, ValFam.patch]
  split_ifs
  exacts [hh, hv]

end GlobalTheory.CompHt
