import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralFourierCoeffClassIndicatorLevelPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCoverComponentExtendsToRankOneCuspData
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfCastDvd
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

section SqLevPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv GlobalTheory.IntCuspLat

namespace GlobalTheory.CovInt.SqLev

open GlobalTheory.TorsFac

theorem factor_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (N ℓ : ℕ) (hodd : Odd N) (hMN : l.M ∣ N) (hp : ℓ.Prime) :
    ∃ (k n' Bn j : ℕ) (β : 𝓞 E), ℓ ^ k ∣ l.M ∧ Nat.Coprime n' ℓ ∧
      (N : 𝓞 E) = β * ((ℓ ^ k : ℕ) : 𝓞 E) * n' ∧ β * H.bar β = (Bn : 𝓞 E) ∧ ℓ ^ (2 * k) * Bn = ℓ ^ j ∧
      ∀ (T : Over Xo.X) (t : T ⟶ Xo.univ.t.G), KilledBy Xo l.Mb (t ^ N) →
        t ^ (N ^ 2) = 1 ∧ (t ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * ℓ ^ (2 * k)) = 1 := by
  have hN : N ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
  have hM : l.M ≠ 0 := by
    intro h
    rw [h] at hMN
    exact hN (zero_dvd_iff.1 hMN)
  obtain ⟨e, n', hn', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN ℓ hp.ne_one
  obtain ⟨k, m, hm', hMe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM ℓ hp.ne_one
  have hcop : Nat.Coprime n' ℓ := ((hp.coprime_iff_not_dvd).2 hn').symm
  have hcm : Nat.Coprime m ℓ := ((hp.coprime_iff_not_dvd).2 hm').symm
  have hMN' : ℓ ^ k * m ∣ ℓ ^ e * n' := hNe ▸ hMe ▸ hMN
  have hke : k ≤ e := by
    have h1 : ℓ ^ k ∣ ℓ ^ e * n' := (Dvd.intro _ rfl).trans hMN'
    have h2 : ℓ ^ k ∣ ℓ ^ e := (Nat.Coprime.pow_left k hcop.symm).dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h2
  obtain ⟨kk, hkk⟩ : m ∣ n' := (hcm.pow_right e).dvd_of_dvd_mul_left ((Dvd.intro_left _ rfl).trans hMN')
  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le hke
  refine ⟨k, n', ℓ ^ (2 * e'), 2 * (k + e'), (ℓ : 𝓞 E) ^ e', ⟨m, hMe⟩, hcop, ?_, ?_, by ring,
    fun T t ht => ⟨?_, ?_⟩⟩
  · rw [hNe]; push_cast; ring
  · rw [map_pow, map_natCast]; push_cast; ring
  · obtain ⟨k2, hk⟩ := hMN
    have := kill Xo t N ht (N : 𝓞 E) (by rw [hk, Nat.cast_mul]; exact l.Mb.mul_mem_right _ (M_mem l))
    rw [← act_nat, ← this]
    congr 2
    push_cast; ring
  · have := kill Xo t N ht ((l.M : 𝓞 E) * kk) (l.Mb.mul_mem_right _ (M_mem l))
    rw [act_pow, ← this]
    congr 2
    rw [hNe, hMe, hkk]; push_cast; ring

section Point
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem class_bound_of_trivAt_pow (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C)
    (nab : NabV Xo c) (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e)
    (hb : ChBound C e ρ w n) (ℓ : ℕ) (hℓ : ℓ.Prime) (hlu : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N : ℕ)
    (hU : Λ.Unimod) (hL : Λ.LevOK N l.M) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y))))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo (xOf y) z) (a : Fin n → Dw.La)
    (htp : ∀ b, tp b ^ N = levPt Xo (xOf y) (a b))
    (hF : ∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) (htr : Λ.TrivAt ℓ) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (((l.M ^ Formalism.L2.Pj.DF Dw w : ℕ) : T.Fr) *
      (io (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P)) := by
  letI := io.toAlgebra
  have hk : ∀ b, KilledBy Xo l.Mb (tp b ^ N) := fun b => by rw [htp b]; exact GlobalTheory.ShortBound.levPt_killed Xo _ _
  obtain ⟨k, n', Bn, j, β₀, hkM, h1, h2, h3, h4, h5⟩ := factor_pow Xo N ℓ hL.1 hL.2.1 hℓ
  have hA : ((ℓ ^ k : ℕ) : 𝓞 E) * H.bar ((ℓ ^ k : ℕ) : 𝓞 E) = ((ℓ ^ (2 * k) : ℕ) : 𝓞 E) := by
    rw [map_natCast]; push_cast; ring
  have key : ∃ u : ℕ, u ∣ l.M ∧ ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w (u : 𝓞 E) *
      (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) :=
    ⟨ℓ ^ k, hkM, sum_bound_of_trivAt Xo c hst T io y C hC nab hnab e ρ w n he hb ℓ hℓ hlu Λ N l.M hU hL P hP z tp F
      hz hg (fun b => (h5 _ _ (hk b)).1) hF htr n' (ℓ ^ (2 * k)) Bn j _ β₀ h1 h2 hA h3 h4
      (fun b => (h5 _ _ (hk b)).2)⟩
  obtain ⟨u, ⟨m, hm⟩, h⟩ := key
  rw [GlobalTheory.ShortBound.nrm_nat, map_mul, map_pow, map_natCast, _root_.mul_assoc] at h
  rw [hm, mul_pow, Nat.cast_mul, _root_.mul_comm ((u ^ _ : ℕ) : T.Fr), _root_.mul_assoc, nval_mul, Nat.cast_pow u]
  calc ((-ρ : ℝ) : EReal) = 0 + ((-ρ : ℝ) : EReal) := (zero_add _).symm
    _ ≤ _ := add_le_add (nval_natCast_nonneg e _) h

end Point

end GlobalTheory.CovInt.SqLev

end SqLevPoint

section SqLevShort
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv GlobalTheory.IntCuspLat

namespace GlobalTheory.CovInt.SqLev

open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions in

theorem smul_nonneg_of_shortRule (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)] (hlev : d.IsLev)
    (hnab : IsNab d.Xo₂ d.c₂ d.nab₂)
    (hroot : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1)
    (hwi : ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) (hM0 : d.l₂.M ≠ 0)
    (Λ : GenLat D.host.E n) (N : ℕ) (hU : Λ.Unimod) (hTM : Λ.TrivAt d.l₂.M) (hN : Λ.LevOK N d.l₂.M)
    (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w) (x0 : Fin n → Dw.La)
    (g : Rul Xo c) (hsec : g ∈ sec Xo c w n) (hR : IsShortRule Xo c d Λ N x0 P g) :
    ∀ (la : HeightOneSpectrum (𝓞 c.F)) (ℓ : ℕ), ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → Λ.TrivAt ℓ →
      ∀ v ∈ valSet Xo c (algCls Xo c) la,
        0 ≤ v ((betaH (Dw := Dw) c Λ * ((GlobalTheory.CovInt.intZ D Dw d.l₂ n w : ℕ) : c.F)) • g) := by
  have hβ : betaH (Dw := Dw) c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  have hc0 : Nat.card (Fin n → LevQ Dw d.l₂) ≠ 0 := by
    rw [GlobalTheory.PlaceInt.card_fun_levQ]; exact pow_ne_zero _ hM0
  haveI := Nat.finite_of_card_ne_zero hc0
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = (NumberField.discr D.host.E).natAbs ^ Formalism.L2.Pj.DF Dw w := ⟨_, rfl⟩
  have hZ : GlobalTheory.CovInt.intZ D Dw d.l₂ n w = Nat.card (Fin n → LevQ Dw d.l₂) * (Q * d.l₂.M ^ Formalism.L2.Pj.DF Dw w) := by
    rw [GlobalTheory.CovInt.intZ, hQ, _root_.mul_assoc]
  rw [hZ]
  rintro la ℓ hℓ hmem htr _ ⟨⟨_, Tc, io, e, ho, yI, hy, eta, heta, rfl⟩, rfl⟩
  show 0 ≤ nval Tc.V e (evI yI _)
  obtain ⟨-, ef2, -⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ Xo c n d Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ Xo c n d hlev hnab 1 hroot Λ N hU hTM hN w P hP x0 g hsec hR Tc io yI hy
  haveI : CharZero T'.Fr := algebraRat.charZero _
  have ho' := ho.bc iT hr hiT
  have he' : 0 < r * e := ho'.1
  have hu : ¬ IsUnit (ℓ : T'.V) := fun hu => by
    have h1 := vV_natCast T' hu
    have h2 := ho'.2 (ℓ : c.F)
    rw [map_natCast, h1] at h2
    have h3 := vLa_pos_of_mem la hℓ.ne_zero hmem
    have h4 : (0 : ℤ) < ((r * e : ℕ) : ℤ) := by exact_mod_cast he'
    exact (mul_pos h4 h3).ne h2
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ Dw _ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C (r * e) he' w n _ le_rfl
  have key := fun q => class_bound_of_trivAt_pow d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ w n he' hch ℓ hℓ
      hu Λ N hU hN _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi (fun b => levRep (q b)) (fun b => (htp q b).1) (hF q) htr
  rw [pow_one] at hζ
  rw [← nval_bc iT hr hiT e, evI_smul, map_mul, hval, ← hio, hζ, _root_.one_mul]
  have := Fintype.ofFinite (Fin n → LevQ Dw d.l₂)
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.mul_sum]
  refine le_nval_sum T' _ _ _ _ fun q _ => ?_
  have hq := key q
  letI := io₂.toAlgebra
  generalize (∑ i, hv d.Xo₂ d.c₂ d.nab₂ y₂.1 (N ^ 2) (fun b => sqN d.Xo₂ N (F q i b))
    (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P)) = Sm at hq ⊢
  have hb0 : io₂ (d.eF (betaH (Dw := Dw) c Λ)) ≠ 0 := (map_ne_zero io₂).2 ((map_ne_zero d.eF).2 hβ)
  have hc1 : ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) ≠ 0 := by exact_mod_cast hc0
  have hQ0 : Q ≠ 0 := hQ ▸ pow_ne_zero _ (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _))
  have hQ1 : (Q : T'.Fr) ≠ 0 := by exact_mod_cast hQ0
  have hQv : 0 ≤ nval T'.V (r * e) ((Q : T'.Fr) * (((d.l₂.M ^ Formalism.L2.Pj.DF Dw w : ℕ) : T'.Fr) *
      (io₂ (((Λ.mIdx N (Dw.p + Dw.q) : d.c₂.F))⁻¹ *
        ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree)⁻¹) * Sm))) := by
    rw [nval_mul, nval_of_ne hQ1]
    refine le_trans ?_ (add_le_add le_rfl hq)
    rw [← EReal.coe_add, EReal.coe_nonneg, ← sub_eq_add_neg, sub_nonneg, hQ]
    exact GlobalTheory.CovInt.ram_sum_le_vV_discr D.host.E T' _ (fun p hp => Nat.prime_of_mem_primeFactors hp) (r * e) _
  refine le_trans (add_nonneg (GlobalTheory.ShortBound.nval_nonneg (V := T'.V) (r * e) (map_isIntegral_int io₂ (hwi x0 q))) hQv)
    (le_of_eq ?_)
  rw [← nval_mul]
  congr 1
  simp only [map_mul, map_inv₀, map_natCast, Nat.cast_mul]
  generalize (io₂ ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree))⁻¹ = a1
  generalize ((Λ.mIdx N (Dw.p + Dw.q) : ℕ) : T'.Fr)⁻¹ = a2
  field_simp

end GlobalTheory.CovInt.SqLev

end SqLevShort

namespace GlobalTheory.CovInt.SqLev

theorem smul_intZ_sq_nonneg_of_sq_dvd : ∀ (D : D7) (H : Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ)
    (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)], d.IsLev → IsNab d.Xo₂ d.c₂ d.nab₂ →
    (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ = 1) →
    (∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) → d.l₂.M ≠ 0 →
    ∀ (Λ : GenLat D.host.E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M →
    ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w →
    ∀ (x0 : Fin n → Dw.La) (g : Rul Xo c), g ∈ sec Xo c w n → IsShortRule Xo c d Λ N x0 P g →
    ∀ (la : HeightOneSpectrum (𝓞 c.F)) (ℓ : ℕ), ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → ℓ ^ 2 ∣ d.l₂.M → Λ.TrivAt ℓ →
    ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v ((betaH (Dw := Dw) c Λ * ((intZ D Dw d.l₂ n w ^ 2 : ℕ) : c.F)) • g) := by
  intro D H Dw l Xo c n d _ hlev hnab hroot hwi hM0 Λ N hU hTM hN w P hP x0 g hsec hR la ℓ hℓ hmem _ htr v hv
  have h := smul_nonneg_of_shortRule D H Dw l Xo c n d hlev hnab (fun k _ _ y => by rw [pow_one]; exact hroot k y)
    hwi hM0 Λ N hU hTM hN w P hP x0 g hsec hR la ℓ hℓ hmem htr v hv
  have hV := isVal_valSet (Xo := Xo) (c := c) (cls := algCls Xo c) la v hv
  have hns : ∀ m : ℕ, 0 ≤ v (m • ((betaH (Dw := Dw) c Λ * ((intZ D Dw d.l₂ n w : ℕ) : c.F)) • g)) := by
    intro m
    induction m with
    | zero => rw [zero_smul, hV.zero]; exact le_top
    | succ m ih => rw [succ_nsmul]; exact (le_min ih h).trans (hV.add _ _)
  have e1 : (betaH (Dw := Dw) c Λ * ((intZ D Dw d.l₂ n w ^ 2 : ℕ) : c.F)) • g =
      (intZ D Dw d.l₂ n w) • ((betaH (Dw := Dw) c Λ * ((intZ D Dw d.l₂ n w : ℕ) : c.F)) • g) := by
    rw [← Nat.cast_smul_eq_nsmul c.F, smul_smul]
    congr 1
    push_cast; ring
  rw [e1]
  exact hns _

end GlobalTheory.CovInt.SqLev
