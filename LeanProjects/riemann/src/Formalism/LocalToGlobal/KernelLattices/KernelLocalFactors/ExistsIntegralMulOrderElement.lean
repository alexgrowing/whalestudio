import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.EmbCInjective
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.LocNormAmbOfOf
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.LocalToGlobal.Columns.RowFormsSel
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.RecLevelHost

open NumberField IsDedekindDomain
open scoped Pointwise

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H

section Per

variable {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ}

def Seam.ptE (a b : ℕ) : VCx X.Tau a b ≃ₗ[ℂ] TaylorLogMetric.VC D a b where
  toFun t := fun τ => t (s.iT.symm τ)
  invFun z := fun τ => z (s.iT τ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv t := by funext τ; simp
  right_inv z := by funext τ; simp

theorem ptE_embH (hok : s.Ok) (δ : ℂ) (x : HomE X.E a b) : s.ptE a b (embH (X.embC s.σ₀) δ x) = KS.phi s δ x := by
  funext τ i j
  show δ * s.σ₀ (X.emb (s.iT.symm τ) (x (Pi.single j 1) i)) = δ * TaylorLogMetric.embT D τ (s.iE (x (Pi.single j 1) i))
  rw [hok.1, Equiv.apply_symm_apply]

theorem lamC_eq (hok : s.Ok) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    LamC (X.embC s.σ₀) δ (KS.aaX s cc) N N' = KS.pb (s.ptE a b) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N')) := by
  ext t
  rw [← KS.phi_per]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (ptE_embH s hok δ x).symm⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, (s.ptE a b).injective ?_⟩
    rw [ptE_embH s hok]
    exact h

theorem HV_ptE (A : ℝ) (x y : VCx X.Tau a b) : HV A⁻¹ x y = formV A D.what₂.Tau a b (s.ptE a b x) (s.ptE a b y) := by
  have h := HV_push s A (s.pt x) (s.pt y)
  rw [pt_iT, pt_iT] at h
  exact h

end Per

section Facts

variable {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ}
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

theorem alV_ptE (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) (x : VCx X.Tau a b)
    (hx : s.ptE a b x ∈ TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) :
    alV D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x = TaylorLogMetric.al D B.tor (s.ptE a b x) := by
  rw [KS.Lat.al_eq_La B hcc hδ hA _ hx]
  unfold alV alphaQ Formalism.L2.Th1.H.qOf
  rw [HV_ptE s]

theorem laFacts_ambOf (hok : s.Ok) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) :
    LaFacts (X.embC (ambOf s B χ cD : Amb X).σ₀) (ambOf s B χ cD : Amb X).δ (ambOf s B χ cD : Amb X).d (ambOf s B χ cD : Amb X).sc
      (ambOf s B χ cD : Amb X).AA N N' := by
  have hL := (B.latAll hcc hδ (KS.Lat.delta_ne hcc hδ)).1 a b _ _ hA
  show IsSelfDual (HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (LamC (X.embC s.σ₀) δ (KS.aaX s cc) N N') ∧
    IsSemiChar (HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (LamC (X.embC s.σ₀) δ (KS.aaX s cc) N N') (alV D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)
  rw [lamC_eq s hok]
  exact ⟨KS.selfDual_pb (s.ptE a b) _ _ (HV_ptE s _) hL.1,
    KS.semi_pb (s.ptE a b) _ _ (HV_ptE s _) (alV_ptE s B N N' hcc hδ hA) hL.2⟩

theorem e_fixed_ambOf (hok : s.Ok) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) :
    (ambOf s B χ cD : Amb X).e a b N N' ∈ fixedBy (HV (ambOf s B χ cD : Amb X).sc) (alV (ambOf s B χ cD : Amb X).d (ambOf s B χ cD : Amb X).sc)
      (LamC (X.embC (ambOf s B χ cD : Amb X).σ₀) (ambOf s B χ cD : Amb X).δ (ambOf s B χ cD : Amb X).AA N N') := by
  have h1 : B.eNat χ a b (s.lat N) (s.lat N') ∈ Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) :=
    Submodule.smul_mem _ (Base.chiFac χ a b (s.lat N) (s.lat N'))
      (B.thMoved_mem (B.latAll hcc hδ (KS.Lat.delta_ne hcc hδ)) (B.thZeroMem (B.stdOK hcc hδ) a b) hA)
  show (fun z => B.eNat χ a b (s.lat N) (s.lat N') (s.ptE a b z)) ∈ fixedBy (HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)
    (alV D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (LamC (X.embC s.σ₀) δ (KS.aaX s cc) N N')
  rw [lamC_eq s hok]
  exact KS.fixed_pb (s.ptE a b) _ _ (HV_ptE s _) (alV_ptE s B N N' hcc hδ hA) h1.2

end Facts

section IdealS

variable {D : D7} {X : Fields} (s : Seam D X)

def Seam.oE : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE

theorem oE_symm_coe (r : 𝓞 D.host.E) : ((s.oE.symm r : 𝓞 X.E) : X.E) = s.iE.symm (r : D.host.E) := rfl

def Seam.PrimeTo (I : Ideal (𝓞 D.host.E)) (P : HeightOneSpectrum (𝓞 X.E)) : Prop := ∃ t ∈ I, s.oE.symm t ∉ P.asIdeal

theorem primeTo_top (P : HeightOneSpectrum (𝓞 X.E)) : s.PrimeTo ⊤ P :=
  ⟨1, Submodule.mem_top, by rw [map_one]; exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)⟩

theorem primeTo_mono {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) {P : HeightOneSpectrum (𝓞 X.E)} (hI : s.PrimeTo I P) : s.PrimeTo J P := by
  obtain ⟨t, ht, hn⟩ := hI
  exact ⟨t, h ht, hn⟩

theorem primeTo_half {P : HeightOneSpectrum (𝓞 X.E)} (h : s.PrimeTo (differentIdeal (𝓞 D.host.K) (𝓞 D.host.E)) P) : s.PrimeTo D.host.𝔟 P := by
  refine primeTo_mono s ?_ h
  have h1 : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) = D.host.𝔟 * (D.host.conj • D.host.𝔟) := D.host.𝔟_spec.1
  rw [h1]
  exact (Ideal.mul_le_left : D.host.𝔟 * (D.host.conj • D.host.𝔟) ≤ D.host.𝔟)

theorem half_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have := D.host.𝔟_spec.2
  rw [h] at this
  simp at this

theorem exists_integral_mul_order_element {t₀ : 𝓞 D.host.E} (h₀ : t₀ ∈ D.host.𝔟) {t : D.host.E} (ht : t ∈ D.host.AA0) :
    ∃ w : 𝓞 D.host.E, (w : D.host.E) = (t₀ : D.host.E) * t := by
  have hb : (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr (half_ne_bot D)
  have h1 : (t₀ : D.host.E) * t ∈ (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0 :=
    FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ h₀) ht
  unfold Host.AA0 at h1
  rw [mul_inv_cancel₀ hb] at h1
  exact (FractionalIdeal.mem_one_iff _).1 h1

variable (cc : Ideal (𝓞 D.host.K))

theorem half_smul_aa {t₀ : 𝓞 D.host.E} (h₀ : t₀ ∈ D.host.𝔟) {r : X.E} (hr : r ∈ KS.aaX s cc) :
    s.oE.symm t₀ • r ∈ (1 : Submodule (𝓞 X.E) X.E) := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨c, -, t, ht, rfl⟩ := hr
    obtain ⟨w, hw⟩ := exists_integral_mul_order_element h₀ ht
    refine Submodule.mem_one.2 ⟨s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩
    rw [Algebra.smul_def]
    show s.iE.symm (((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w : 𝓞 D.host.E)) : D.host.E) = s.iE.symm (t₀ : D.host.E) * _
    rw [← map_mul]
    congr 1
    show (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * (w : D.host.E) = _
    rw [hw]
    ring
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | smul o x _ h => rw [smul_comm]; exact Submodule.smul_mem _ o h

theorem aa_fg : (KS.aaX s cc).FG := by
  obtain ⟨t₀, h₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (half_ne_bot D)
  have hβ : s.oE.symm t₀ ≠ 0 := fun h => hne (by simpa using h)
  let f : X.E →ₗ[𝓞 X.E] X.E := s.oE.symm t₀ • LinearMap.id
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : s.oE.symm t₀ • x = s.oE.symm t₀ • y := hxy
    exact smul_right_injective X.E hβ h1
  have h1 : IsNoetherian (𝓞 X.E) ↥(1 : Submodule (𝓞 X.E) X.E) :=
    isNoetherian_of_fg_of_noetherian _ (by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _)
  have h2 : ((KS.aaX s cc).map f).FG := isNoetherian_submodule.1 h1 _ (by
    rintro _ ⟨r, hr, rfl⟩
    exact half_smul_aa s cc h₀ hr)
  exact Submodule.fg_of_fg_map_injective f hf h2

theorem aa_unit_at (P : HeightOneSpectrum (𝓞 X.E)) (hb : s.PrimeTo D.host.𝔟 P)
    (hc : s.PrimeTo (cc.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) P) :
    localization₂ P.asIdeal (KS.aaX s cc) = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) := by
  obtain ⟨t₀, h₀, hβ⟩ := hb
  obtain ⟨c, hcc, hγ⟩ : ∃ c ∈ cc, s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) ∉ P.asIdeal := by
    obtain ⟨t, ht, hnt⟩ := hc
    by_contra H
    push Not at H
    have h1 : cc.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ P.asIdeal.comap (s.oE.symm : 𝓞 D.host.E →+* 𝓞 X.E) :=
      Ideal.map_le_iff_le_comap.2 fun c hc => H c hc
    exact hnt (h1 ht)
  ext x
  rw [mem_locP, mem_locP]
  constructor
  · rintro ⟨σ, hσ, hx⟩
    refine ⟨s.oE.symm t₀ * σ, fun h => (P.isPrime.mem_or_mem h).elim hβ hσ, ?_⟩
    rw [mul_smul]
    exact half_smul_aa s cc h₀ hx
  · rintro ⟨σ, hσ, hx⟩
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 hx
    refine ⟨s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) * σ, fun h => (P.isPrime.mem_or_mem h).elim hγ hσ, ?_⟩
    have hmem : ((s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) : 𝓞 X.E) : X.E) ∈ KS.aaX s cc :=
      Submodule.subset_span ⟨c, hcc, 1, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.one_mem_inverse_halfDifferent D, by rw [mul_one]; rfl⟩
    have e : s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) • algebraMap (𝓞 X.E) X.E o =
        o • ((s.oE.symm (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) : 𝓞 X.E) : X.E) := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_comm]
    rw [mul_smul, ← ho, e]
    exact Submodule.smul_mem _ o hmem

end IdealS

section NatS

variable {D : D7} {X : Fields} (s : Seam D X)

end NatS

section Main

variable {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

include s in
theorem nonempty_tau : Nonempty X.Tau := by
  have h : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]
    unfold Ranks.f Ranks.n
    positivity)
  exact h.map s.iT.symm

theorem laHyp_ambOf (hok : s.Ok) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) {a b : ℕ} (ha : Even a) (hb : Even b)
    (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (hconj : ∀ P ∈ Sall, conjPrime₂ P ∉ Sall) (hhalf : ∀ P ∈ Sall, s.PrimeTo D.host.𝔟 P)
    (hcur : ∀ P ∈ Sall, s.PrimeTo (cc.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) P) :
    (ambOf s B χ cD : Amb X).LaHyp a b Sall :=
  ⟨KS.Lat.delta_ne hcc hδ, nonempty_tau s, hconj, fun P hP => aa_unit_at s cc P (hhalf P hP) (hcur P hP), aa_fg s cc,
    fun N N' hN hN' => ⟨e_fixed_ambOf s B χ cD N N' hok hcc hδ (s.admissible_of_selfDual_lattices hok ha hb hN hN'),
      laFacts_ambOf s B χ cD N N' hok hcc hδ (s.admissible_of_selfDual_lattices hok ha hb hN hN')⟩⟩

theorem laHyp_ambOf_top {δ : ℂ} (B : Base D (⊤ : Ideal (𝓞 D.host.K)) δ) (hok : s.Ok) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D ⊤ δ) {a b : ℕ} (ha : Even a) (hb : Even b)
    (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) (hconj : ∀ P ∈ Sall, conjPrime₂ P ∉ Sall) (hhalf : ∀ P ∈ Sall, s.PrimeTo D.host.𝔟 P) :
    (ambOf s B χ cD : Amb X).LaHyp a b Sall :=
  laHyp_ambOf s B χ cD hok ⟨top_ne_bot, by simp⟩ hδ ha hb Sall hconj hhalf fun P _ => by
    rw [Ideal.map_top]
    exact primeTo_top s P

end Main

section Bad

open Formalism.EigenvalueLevelCeiling (plc)

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem mem_of_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A} (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact hf.mem_toFinset.mp h
  · simp at h

open Classical in

theorem bad_gen (hPr : Pr.Ok) (u : Pr.Word) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vT u ∪ Pr.vGs) :
    ∃ (π : 𝓞 X.E) (p : ℕ), π ∈ P.asIdeal ∧ IsCoprime π (X.conjO π) ∧ π * X.conjO π = (p : 𝓞 X.E) ∧ p.Prime ∧
      (p = Pr.T u ∧ π = Pr.piT u ∨ ∃ i, p = Pr.g i ∧ π = X.conjO (Pr.piG i)) := by
  have hcc : ∀ r : 𝓞 X.E, X.conjO (X.conjO r) = r := fun r => cO_cO r
  rw [Finset.mem_union] at hP
  rcases hP with h | h
  · exact ⟨Pr.piT u, Pr.T u, mem_of_divs h, hPr.piT_cop u, hPr.piT_norm u, hPr.T_prime u, Or.inl ⟨rfl, rfl⟩⟩
  · unfold Primes.vGs at h
    rw [Finset.mem_union] at h
    have key : ∀ i, P ∈ Pr.vG i → _ := fun i hi =>
      (⟨X.conjO (Pr.piG i), Pr.g i, mem_of_divs hi, by rw [hcc]; exact (hPr.piG_cop i).symm, by rw [hcc, mul_comm]; exact hPr.piG_norm i,
        hPr.g_prime i, Or.inr ⟨i, rfl, rfl⟩⟩ : ∃ (π : 𝓞 X.E) (p : ℕ), π ∈ P.asIdeal ∧ IsCoprime π (X.conjO π) ∧ π * X.conjO π = (p : 𝓞 X.E) ∧ p.Prime ∧
      (p = Pr.T u ∧ π = Pr.piT u ∨ ∃ i, p = Pr.g i ∧ π = X.conjO (Pr.piG i)))
    exact h.elim (key 0) (key 1)

open Classical in

theorem tg_noConj (hPr : Pr.Ok) (u : Pr.Word) : ∀ P ∈ Pr.vT u ∪ Pr.vGs, conjPrime₂ P ∉ Pr.vT u ∪ Pr.vGs := by
  intro P hP hP'
  obtain ⟨π, p, hπ, hcop, hn, hp, hk⟩ := bad_gen hPr u hP
  obtain ⟨π', p', hπ', hcop', hn', hp', hk'⟩ := bad_gen hPr u hP'
  have htop : ∀ {x y : 𝓞 X.E}, IsCoprime x y → x ∈ P.asIdeal → y ∈ P.asIdeal → False := by
    intro x y ⟨a, b, hab⟩ hx hy
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (P.asIdeal.mul_mem_left a hx) (P.asIdeal.mul_mem_left b hy)))
  have h1 : X.conjO π' ∈ P.asIdeal := hπ'
  have hpP : (p : 𝓞 X.E) ∈ P.asIdeal := hn ▸ P.asIdeal.mul_mem_right _ hπ
  have hpP' : (p' : 𝓞 X.E) ∈ P.asIdeal := hn' ▸ P.asIdeal.mul_mem_left _ h1
  by_cases hpp : p = p'
  · have hsame : π = π' := by
      rcases hk with ⟨e1, e2⟩ | ⟨i, e1, e2⟩ <;> rcases hk' with ⟨e1', e2'⟩ | ⟨i', e1', e2'⟩
      · rw [e2, e2']
      · exact absurd (e1.symm.trans (hpp.trans e1')) (hPr.T_ne_g u i')
      · exact absurd (e1'.symm.trans (hpp.symm.trans e1)) (hPr.T_ne_g u i)
      · have hii : i = i' := by
          by_contra hne
          have h2 : Pr.g i = Pr.g i' := e1.symm.trans (hpp.trans e1')
          have h3 : ∀ j j' : Fin 2, j ≠ j' → Pr.g j = Pr.g j' → False := by
            intro j j' hj hg
            fin_cases j <;> fin_cases j'
            · exact hj rfl
            · exact hPr.g_ne hg
            · exact hPr.g_ne hg.symm
            · exact hj rfl
          exact h3 i i' hne h2
        rw [e2, e2', hii]
    exact htop hcop hπ (hsame ▸ h1)
  · have hc : IsCoprime (p : 𝓞 X.E) (p' : 𝓞 X.E) := by
      have := (Nat.coprime_primes hp hp').2 hpp
      have h2 := (Nat.isCoprime_iff_coprime.2 this).map (Int.castRingHom (𝓞 X.E))
      simpa using h2
    exact htop hc hpP hpP'

variable {sel}

theorem qe_nat_notMem (hsel : IsSel X sel) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) : (p : 𝓞 X.E) ∉ P.asIdeal := by
  intro hi
  obtain ⟨v, hv, rfl⟩ := (mem_QE sel mu P).mp hP
  have h1 : ((p : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v]
    show algebraMap (𝓞 X.F) (𝓞 X.E) ((p : ℕ) : 𝓞 X.F) ∈ (sel v).asIdeal
    rw [map_natCast]
    exact hi
  have h2 : plc v ∣ p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at h1
    exact (ringChar.spec _ _).mp h1
  have hpp : (plc v).Prime := by
    have : Finite (𝓞 X.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    have : v.asIdeal.IsPrime := v.isPrime
    exact CharP.char_is_prime (𝓞 X.F ⧸ v.asIdeal) (ringChar (𝓞 X.F ⧸ v.asIdeal))
  have h3 : plc v = p := (Nat.prime_dvd_prime_iff_eq hpp hp).mp h2
  exact (mu.good hv).2.2 (h3 ▸ hS)

theorem qe_noConj (hX : X.AbelianUnramifiedExtensionConditions) (hsel : IsSel X sel) : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), conjPrime₂ P ∉ QE sel (mu : Chr X.F X.E X.K) := by
  intro P hP hP'
  have hc := cmData_of_totallyRealFieldsConditions hX
  obtain ⟨v, hv, rfl⟩ := (mem_QE sel mu P).mp hP
  obtain ⟨v', -, hv'⟩ := (mem_QE sel mu _).mp hP'
  have ho : IsOver v (sel v) := (hsel v).symm
  have ho' : IsOver v' (conjPrime₂ (sel v)) := hv' ▸ (hsel v').symm
  have hvv : v' = v := HeightOneSpectrum.ext (ho'.trans (ho.conj hc).symm)
  have hfix : conjPrime₂ (sel v) = sel v := by rw [← hv', hvv]
  obtain ⟨⟨P1, P2, hne, hsp⟩, -, -⟩ := mu.good hv
  have hover : ∀ Q : HeightOneSpectrum (𝓞 X.E), Ideal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) v.asIdeal ≤ Q.asIdeal → IsOver v Q := by
    intro Q hQ
    have h1 : v.asIdeal ≤ Q.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := Ideal.map_le_iff_le_comap.1 hQ
    exact v.isMaximal.eq_of_le (Ideal.comap_ne_top _ Q.isPrime.ne_top) h1
  have h1 : P1 = sel v := by
    rcases rll_over_cases hc ho (hover P1 (hsp ▸ Ideal.mul_le_left)) with e | e
    · exact e
    · rw [e, hfix]
  have h2 : P2 = sel v := by
    rcases rll_over_cases hc ho (hover P2 (hsp ▸ Ideal.mul_le_right)) with e | e
    · exact e
    · rw [e, hfix]
  exact hne (h1.trans h2.symm)

variable (sel)

theorem conjP_twice (P : HeightOneSpectrum (𝓞 X.E)) : conjPrime₂ (conjPrime₂ P) = P := by
  apply HeightOneSpectrum.ext
  ext r
  rw [mem_conjP, mem_conjP, cO_cO]

open Classical in

theorem sall_noConj (hX : X.AbelianUnramifiedExtensionConditions) (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hT : Pr.T u ∈ S) (hg : ∀ i, Pr.g i ∈ S) :
    ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  have hsplit : ∀ P, P ∈ Sall sel mu u ↔ P ∈ Pr.vT u ∪ Pr.vGs ∨ P ∈ QE sel (mu : Chr X.F X.E X.K) := by
    intro P
    unfold Sall rowSG uSG
    simp only [Finset.mem_union]
    tauto

  have hmix : ∀ P, P ∈ Pr.vT u ∪ Pr.vGs → conjPrime₂ P ∉ QE sel (mu : Chr X.F X.E X.K) := by
    intro P hP hQ
    obtain ⟨π, p, hπ, -, hn, hp, hk⟩ := bad_gen hPr u hP
    have hpS : p ∈ S := by
      rcases hk with ⟨e, -⟩ | ⟨j, e, -⟩
      · rw [e]; exact hT
      · rw [e]; exact hg j
    refine qe_nat_notMem mu hsel hp hpS hQ ?_
    rw [mem_conjP, map_natCast]
    exact hn ▸ P.asIdeal.mul_mem_right _ hπ
  intro P hP hP'
  rcases (hsplit P).1 hP with h | h <;> rcases (hsplit _).1 hP' with h' | h'
  · exact tg_noConj hPr u P h h'
  · exact hmix P h h'
  · exact hmix (conjPrime₂ P) h' (by rw [conjP_twice]; exact h)
  · exact qe_noConj mu hX hsel P h h'

open Classical in

theorem sall_nat (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Sall sel mu u) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 X.E) ∈ P.asIdeal ∧ (p = Pr.T u ∨ (∃ i, p = Pr.g i) ∨ p ∉ S) := by
  have hP' : P ∈ Pr.vT u ∪ Pr.vGs ∨ P ∈ QE sel (mu : Chr X.F X.E X.K) := by
    unfold Sall rowSG uSG at hP
    simp only [Finset.mem_union] at hP ⊢
    tauto
  rcases hP' with h | h
  · obtain ⟨π, p, hπ, -, hn, hp, hk⟩ := bad_gen hPr u h
    refine ⟨p, hp, hn ▸ P.asIdeal.mul_mem_right _ hπ, ?_⟩
    rcases hk with ⟨e, -⟩ | ⟨j, e, -⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl ⟨j, e⟩)
  · obtain ⟨v, hv, rfl⟩ := (mem_QE sel mu P).mp h
    have hpp : (plc v).Prime := by
      have : Finite (𝓞 X.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
      have : v.asIdeal.IsPrime := v.isPrime
      exact CharP.char_is_prime (𝓞 X.F ⧸ v.asIdeal) (ringChar (𝓞 X.F ⧸ v.asIdeal))
    refine ⟨plc v, hpp, ?_, Or.inr (Or.inr (mu.good hv).2.2)⟩
    have h1 : ((plc v : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact CharP.cast_eq_zero _ _
    rw [← hsel v] at h1
    have h2 : algebraMap (𝓞 X.F) (𝓞 X.E) ((plc v : ℕ) : 𝓞 X.F) ∈ (sel v).asIdeal := h1
    rwa [map_natCast] at h2

end Bad

section Chain

variable {D : D7} {X : Fields} {Pr : Primes X} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem rank_even (R : Ranks) (j : ℕ) : Even (R.N j) := by
  unfold Ranks.N
  exact R.k_even.add ((R.t_odd.add_one).mul_left j)

end Chain

end Formalism.L2.Ker
