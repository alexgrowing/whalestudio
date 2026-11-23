import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDVal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsVtOverIsUUOverBaseChange
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InZhGeoInjStable
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsotropicSumIndependentOfChoicesLocal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumSupportCMul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicConnectionValueBaseChangeField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortAtField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_pull [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {n : ℕ} (Λ : GenLat E n) (N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HH c a n)
    {S T : Type} [CommRing S] [Algebra c.F S] [Field T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (w : FrPt Xo c T) (hm : FrMap ψ y w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo y.x z)
    (ht : ∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b))
    (hF : ∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) :
    ∃ (z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (tp' : (Fin n → LevQ Dw l) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (F' : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
        LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo w.x))),
      (∀ i, InZh Xo Λ N (z' i)) ∧ GeoInj Xo w.x z' ∧
      (∀ q b, tp' q b ^ N = levPt Xo w.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp' q b)) ∧
      (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N w.s (z' i b) (tp' q b) (F' q i b)) ∧
      ∀ q, ψ (∑ i, ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ b, nab y ((N : ℤ) ^ 2) (F q i b) (colOf m b)) =
        ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
          ∏ b, nab w ((N : ℤ) ^ 2) (F' q i b) (colOf m b) := by
  let h : ptO Xo w.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hm.1.symm
  choose F' hF' using fun q i b => GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2)
    (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F q i b)
  obtain ⟨p1, -, p3, -⟩ := GlobalTheory.inZh_geoInj_stable E H Dw l Xo n Λ N
  refine ⟨fun i b => h ≫ z i b, fun q b => h ≫ tp q b, F', fun i => p1 _ _ h _ (hz i),
    p3 S T y.x w.x ψ.toRingHom h rfl _ z hg, fun q b => ⟨?_, ?_⟩, fun q i b => ?_, fun q => ?_⟩
  · have e : h ≫ levPt Xo y.x (levRep (q b)) = levPt Xo w.x (levRep (q b)) := by
      unfold levPt
      rw [← Category.assoc, comp_toUnit]
    rw [← e, ← (ht q b).1, MonObj.comp_pow]
  · obtain ⟨j, hj⟩ := (ht q b).2
    exact ⟨j, fun u hu => by rw [Category.assoc, hj u hu, MonObj.comp_one]⟩
  · exact (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo N ⊤ _ _ h y.s w.s
      (GlobalTheory.FramedBaseChange.isPullSec ψ hm h rfl) (F q i b) (F' q i b) (hF' q i b)).2 _ _ (hF q i b)
  · rw [map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      GlobalTheory.harmonicValue_baseChange_field E H Dw l Xo c nab hnab S T ψ y w hm h rfl a n P hP N (F q i) (F' q i)
        (hF' q i)

theorem finite_levQ (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have hp := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at hp
    have := l.three_le
    omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  haveI := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem map_weighted {F S₁ S₂ T Q : Type} [Field F] [CommRing S₁] [CommRing S₂] [CommRing T]
    [Algebra F S₁] [Algebra F S₂] [Algebra F T] [Finite Q] (ψ₁ : S₁ →ₐ[F] T) (ψ₂ : S₂ →ₐ[F] T)
    (k : F) (w : Q → F) (A₁ : Q → S₁) (A₂ : Q → S₂) (h : ∀ q, ψ₁ (A₁ q) = ψ₂ (A₂ q)) :
    ψ₁ (algebraMap F S₁ k * ∑ᶠ q, algebraMap F S₁ (w q) * A₁ q) =
      ψ₂ (algebraMap F S₂ k * ∑ᶠ q, algebraMap F S₂ (w q) * A₂ q) := by
  haveI := Fintype.ofFinite Q
  simp only [finsum_eq_sum_of_fintype, map_mul, map_sum, AlgHom.commutes, h]

theorem exists_algHom_field (F S : Type) [Field F] [CommRing S] [Nontrivial S] [Algebra F S] :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra F Ω), Nonempty (S →ₐ[F] Ω) := by
  obtain ⟨J, hJ⟩ := Ideal.exists_maximal S
  exact ⟨S ⧸ J, Ideal.Quotient.field J, inferInstance, ⟨Ideal.Quotient.mkₐ F J⟩⟩

theorem shortValAt_eq_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → ∀ (cf : (Fin n → LevQ Dw l) → c.F) (β : c.F) (K k : Type) [Field K] [Algebra c.F K] [Field k] [Algebra c.F k] (ψ : K →ₐ[c.F] k) (y : FrPt Xo c K) (yk : FrPt Xo c k), FrMap ψ y yk → ∀ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo y.x z → (∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) → ∀ v : k, ShortValAt Xo c nab cf Λ β N P yk v → v = ψ (algebraMap c.F K (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) * ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F K (cf q) * ∑ i, hv Xo c nab y (N ^ 2) (fun b => sqN Xo N (F q i b)) P) := by
  intro E _ _ _ H Dw l Xo c _ hstar nab hnab n Λ N hU hT hN w P hP cf β K k _ _ _ _ ψ y yk hψ z tp F hz hg ht hF v hv
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  haveI := finite_levQ Dw l
  obtain ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, e1⟩ := hv
  have hinj : Function.Injective φ1 := hf1.injective
  haveI : Nontrivial S1 := hinj.nontrivial
  obtain ⟨Ω, _, _, ⟨κ⟩⟩ := exists_algHom_field c.F S1
  obtain ⟨u, hu⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c S1 Ω κ y1
  have hu' : FrMap (κ.comp (φ1.comp ψ)) y u :=
    GlobalTheory.FramedBaseChange.trans (φ1.comp ψ) κ (GlobalTheory.FramedBaseChange.trans ψ φ1 hψ hm1) hu
  obtain ⟨z1', tp1', G1, a1', b1', c1', d1', f1⟩ :=
    exists_pull nab hnab Λ N w P hP κ y1 u hu z1 tp1 F1 hz1 hg1 ht1 hu1
  obtain ⟨z2', tp2', G2, a2', b2', c2', d2', f2⟩ :=
    exists_pull nab hnab Λ N w P hP (κ.comp (φ1.comp ψ)) y u hu' z tp F hz hg ht hF
  apply (κ.comp φ1).toRingHom.injective
  change κ (φ1 v) = (κ.comp (φ1.comp ψ)) _
  rw [e1]
  refine map_weighted κ (κ.comp (φ1.comp ψ)) _ cf _ _ fun q => ?_
  have hc := (GlobalTheory.PlaceInt.hv_linear E H Dw l Xo c hstar nab hnab K y n P).2.2 N
  rw [← Finset.sum_congr rfl fun i _ => hc (F q i)]
  exact (f1 q).trans ((GlobalTheory.shortSum_indep_local hL E H Dw l Xo c nab hnab n Λ N hU hT hN P Ω u z1' tp1' G1 z2' tp2' G2
    a1' b1' c1' d1' a2' b2' c2' d2' q).trans (f2 q).symm)

end GlobalTheory.ShortAtField
