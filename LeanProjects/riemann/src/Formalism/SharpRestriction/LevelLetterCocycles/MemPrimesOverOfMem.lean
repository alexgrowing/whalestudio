import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ExportFamilies
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.ResidueCharacters.SumLogDivSqModPmOneLe
import Development.AutomorphicArithmetic.CyclotomicBounds.CyclotomicOrders.NuHost

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_E_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  show 4 * D.R.ord = 2 * (2 * D.R.ord)
  ring

theorem two_mem_small (D : D7) : 2 ∈ D.host.small :=
  Nat.mem_primeFactors.2 ⟨Nat.prime_two, (dvd_pow_self 2 (by omega)).trans D.host.tower_dvd, D.host.QS_pos.ne'⟩

end

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7}

theorem logWeight_nonneg (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w := by
  unfold SizeData₂.lwP lw
  apply div_nonneg (Real.log_natCast_nonneg _)
  positivity

open Classical in

theorem etaSum_eq_sum (L : SizeData₂ D) (j : ℕ) :
    etaSum L j = ∑ l ∈ (L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0)).image
      (fun w => D.what₂.places.resChar w), etaAt L j l := by
  unfold etaSum etaAt
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun w => D.what₂.places.resChar w)
      (t := (L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0)).image
        (fun w => D.what₂.places.resChar w)) (fun w hw => Finset.mem_image_of_mem _ hw)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext w
  simp [twAt, Finset.mem_filter, and_assoc]

theorem etaAt_le (L : SizeData₂ D) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {l : ℕ} (hl : l ∉ gset D) {U : ℝ}
    (hU : 0 ≤ U) (h1 : adm1 D) (h2 : adm2 L) (h3 : adm3 L)
    (hloc : ∀ i : D.nd.Loc, TwLoc D i → D.nd.l i = l → ∀ π ∈ D.nd.Zgood i,
      (D.nd.vcc i π : ℝ) + (padicValNat l D.what₂.restRowsFiniteGroupCard : ℝ) ≤ U) :
    etaAt L j l ≤ Real.log l * ((L.dZ0 j : ℝ) * U) := by
  classical
  have hjm : 1 ≤ j ∧ j ≤ D.R.m := Finset.mem_Icc.1 hj
  have hw : ∀ w ∈ twAt L l, (D.what₂.etaJ j w : ℝ) ≤ (L.dZ0 j : ℝ) * U := by
    intro w hw
    obtain ⟨_, htw, hwl⟩ := mem_twAt.1 hw
    rw [D.etaJ_tie j w hjm.1 hjm.2]
    push_cast
    calc ∑ i ∈ D.nd.locs j w, (D.nd.etaLoc i : ℝ)
        ≤ ∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ) * U := by
          apply Finset.sum_le_sum
          intro i hi
          have hiw := (D.nd.locs_mem j w i).1 hi
          have hti : TwLoc D i := TwPl.twLoc htw hi
          have hli : D.nd.l i = l := by rw [← D.nd.w_l i, hiw.2, hwl]
          refine (h1 i hti (hli ▸ hl)).trans ?_
          apply Finset.sum_le_sum
          intro π hπ
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := hloc i hti hli π hπ
          rw [hli]
          exact this
      _ = U * ∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun π _ => ?_)
          ring
      _ ≤ U * (L.zeroSpaceRankAtPlace j w : ℝ) := mul_le_mul_of_nonneg_left (h2 j hj w htw (hwl ▸ hl)) hU
      _ = (L.dZ0 j : ℝ) * U := by rw [h3 j hj w htw]; ring
  have hdU : 0 ≤ (L.dZ0 j : ℝ) * U := mul_nonneg (by positivity) hU
  have hsum : etaAt L j l ≤ (∑ w ∈ twAt L l, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) *
      ((L.dZ0 j : ℝ) * U) := by
    unfold etaAt
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro w hwm
    apply mul_le_mul_of_nonneg_left (hw w hwm)
    exact mul_nonneg (logWeight_nonneg w) (by positivity)
  by_cases he : twAt L l = ∅
  · have : etaAt L j l = 0 := by unfold etaAt; rw [he]; simp
    rw [this]
    exact mul_nonneg (Real.log_natCast_nonneg l) hdU
  · obtain ⟨w, hwm⟩ := Finset.nonempty_iff_ne_empty.2 he
    have hlp : l.Prime := (mem_twAt.1 hwm).2.2 ▸ D.what₂.places.resChar_prime w
    exact hsum.trans (mul_le_mul_of_nonneg_right (admissibleMeanCondition_holds L l hlp) hdU)

theorem etaAt_le_g (L : SizeData₂ D) (tb : Tab L) (C : ℝ) (hH : GeneratorPrimeEtaBound L tb C) (h6 : adm6 L tb)
    {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {l : ℕ} (hl : l ∈ gset D) :
    etaAt L j l ≤ Real.log l * ((L.dZ0 j : ℝ) *
      (C * L.sc.x ^ C * L.etaSz + 2 / (l : ℝ) ^ 2 + VVr D l + vhE D l)) := by
  obtain ⟨hH1, hH2⟩ := hH j hj l hl
  have hs := h6.2 j hj l hl
  refine hH1.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg l)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7}

theorem mem_primesOver_of_mem {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E l) :
    v.asIdeal ∈ (Ideal.span {(l : ℤ)}).primesOver (𝓞 E) := by
  have : Fact l.Prime := ⟨hl⟩
  have hmax := Int.ideal_span_isMaximal_of_prime l
  have := v.isPrime
  refine ⟨v.isPrime, ⟨?_⟩⟩
  apply hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
  have hv' : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal := hv
  simpa using hv'

theorem placesOver_finite (E : Type) [Field E] [NumberField E] {l : ℕ} (hl : l.Prime) :
    (placesOver E l).Finite := by
  classical
  have : Fact l.Prime := ⟨hl⟩
  haveI := Int.ideal_span_isMaximal_of_prime l
  have hfin : ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E)).Finite :=
    Set.toFinite _
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal)
      ((fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) ⁻¹' ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E))) := by
    intro a _ b _ hab
    exact HeightOneSpectrum.ext hab
  exact (hfin.preimage hinj).subset (fun v hv => mem_primesOver_of_mem hl hv)

theorem nLam_pos (D : D7) (lam : HeightOneSpectrum (𝓞 D.host.E)) : 1 ≤ nLam D lam := by
  unfold nLam Formalism.MainNotions.N.locDeg
  have := lam.isPrime
  have h1 := Ideal.ramificationIdx_pos lam.asIdeal ℤ
  have h2 := Ideal.inertiaDeg_pos lam.asIdeal ℤ
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h1.ne' h2.ne')

theorem sum_nLam_le (D : D7) {l : ℕ} (hl : l.Prime) :
    ∑ lam ∈ (placesOver_finite D.host.E hl).toFinset, (nLam D lam : ℝ) ≤ 2 * D.R.f := by
  classical
  have : Fact l.Prime := ⟨hl⟩
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(l : ℤ)}) (𝓞 D.host.E)
  rw [RingOfIntegers.rank, finrank_E_host] at hsum
  have hsum' : ∑ q ∈ ((Ideal.span {(l : ℤ)}).primesOver (𝓞 D.host.E)).toFinset,
      q.ramificationIdx ℤ * q.inertiaDeg ℤ = 2 * D.R.f := by
    rw [← hsum]
    exact (Finset.sum_set_coe (f := fun q : Ideal (𝓞 D.host.E) => q.ramificationIdx ℤ * q.inertiaDeg ℤ) _).symm
  set G : Ideal (𝓞 D.host.E) → ℝ := fun q => ((q.ramificationIdx ℤ * q.inertiaDeg ℤ : ℕ) : ℝ) with hG
  set S := (placesOver_finite D.host.E hl).toFinset with hS
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.asIdeal) (S : Set _) := by
    intro a _ b _ hab
    exact HeightOneSpectrum.ext hab
  calc ∑ lam ∈ S, (nLam D lam : ℝ) = ∑ lam ∈ S, G lam.asIdeal := by
        refine Finset.sum_congr rfl (fun lam _ => ?_)
        simp [hG, nLam, Formalism.MainNotions.N.locDeg]
    _ = ∑ q ∈ S.image (fun v => v.asIdeal), G q := (Finset.sum_image hinj).symm
    _ ≤ ∑ q ∈ ((Ideal.span {(l : ℤ)}).primesOver (𝓞 D.host.E)).toFinset, G q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hq
          rw [Set.mem_toFinset]
          exact mem_primesOver_of_mem hl ((Set.Finite.mem_toFinset _).1 hv)
        · intro q _ _
          simp only [hG]
          positivity
    _ = 2 * D.R.f := by
        simp only [hG]
        rw [← Nat.cast_sum, hsum']
        push_cast
        ring

theorem sum_nLam_succ_le (D : D7) {l : ℕ} (hl : l.Prime) :
    ∑ lam ∈ (placesOver_finite D.host.E hl).toFinset, ((nLam D lam : ℝ) + 1) ≤ 4 * D.R.f := by
  have h := sum_nLam_le D hl
  have h2 : ∑ lam ∈ (placesOver_finite D.host.E hl).toFinset, ((nLam D lam : ℝ) + 1) ≤
      ∑ lam ∈ (placesOver_finite D.host.E hl).toFinset, (2 * (nLam D lam : ℝ)) := by
    apply Finset.sum_le_sum
    intro lam _
    have : (1 : ℝ) ≤ nLam D lam := by exact_mod_cast nLam_pos D lam
    linarith
  rw [← Finset.mul_sum] at h2
  linarith

theorem sumOver_eq (D : D7) {l : ℕ} (hl : l.Prime) (f : HeightOneSpectrum (𝓞 D.host.E) → ℝ) :
    sumOver D l f = ∑ lam ∈ (placesOver_finite D.host.E hl).toFinset, f lam :=
  finsum_mem_eq_finite_toFinset_sum f _

theorem split_or_inert (D : D7) {l : ℕ} (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q) (hd : l ≠ D.host.d) :
    SplitK D l ∨ InertK D l := by
  unfold SplitK InertK Host.cls primeClass
  simp only [h2, hq, hd, if_false]
  split_ifs <;> simp

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7}

section Bound

variable (L : SizeData₂ D) (tb : Tab L) (C : ℝ)

open Classical in

def bandI (l : ℕ) : ℝ :=
  if ∃ s : ℝ, L.sc.w'' D.R.n ≤ s ∧ s ≤ wB L ∧
      |(l : ℝ) * s - L.sc.b| ≤ C * (l * eta₃ L + l * L.Sc + L.sc.b / l + s + l * large₂ L) then 1 else 0

def flatB (l : ℕ) : ℝ := (wP L + eta₃ L) / l + L.Sc + large₂ L + eta₃ L * bandI L C l

def rowBr (l : ℕ) : ℝ :=
  hB L / ((l : ℝ) - 1) ^ (jA L l + 1) + (GP L + 1) * ((jA L l : ℝ) + 1) + large₂ L

open Classical in

def lenB (l : ℕ) : ℝ :=
  if SplitK D l then (2 * (D.R.f : ℝ) * D.R.m + D.R.f) * eP L C l
  else if (l : ℝ) < lA L ∧ 4 * D.host.Lw < ordH D l then 4 * (D.R.f : ℝ) * (C * D.R.r * rowBr L l)
  else 4 * (D.R.f : ℝ) * (C * D.R.r * (hB L / (l : ℝ) ^ 2 + flatB L C l)) +
    2 * (D.R.f : ℝ) * (C * D.R.m * eP L C l)

def bbB : ℝ := C * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (large₂ L) ^ 2

open Classical in

def lamB (l : ℕ) : ℝ :=
  if l ∈ D.host.small ∨ l = 3 then C * D.R.f * D.R.m * L.sc.b * Real.log L.sc.x + C * L.sc.x ^ C * (large₂ L) ^ 2
  else if l = D.host.q ∨ l = D.host.d then 2 * C * D.R.f * D.R.m * L.sc.b
  else if lStar L < l ∧ l ∉ tb.exc then 0
  else bbB L C + lenB L C l

end Bound

section Signs

variable (L : SizeData₂ D)

theorem one_le_b : 1 ≤ L.sc.b := by
  unfold Scale.b
  apply Real.one_le_exp
  unfold Scale.L
  exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _

theorem x_pos : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]

theorem Lg_nonneg : 0 ≤ large₂ L := by
  unfold large₂ Scale.L
  exact Real.rpow_nonneg (x_pos L).le _

theorem b'_pos : 0 < L.sc.b' := by
  unfold Scale.b' Scale.a Scale.X'
  have := x_pos L
  have := one_le_b L
  positivity

theorem w''_nonneg : 0 ≤ L.sc.w'' D.R.n := by
  unfold Scale.w''
  have := b'_pos L
  have := x_pos L
  positivity

theorem one_le_hB : 1 ≤ hB L := by
  unfold hB
  have := one_le_b L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

theorem etaP_nonneg : 0 ≤ eta₃ L := by
  unfold eta₃
  have := L.etaSz_pos
  positivity

theorem wB_nonneg : 0 ≤ wB L := by
  unfold wB
  have := w''_nonneg L
  have := L.etaSz_pos
  exact le_max_of_le_left (by linarith)

theorem placeWeight_nonneg : 0 ≤ wP L := by
  unfold wP
  have := wB_nonneg L
  positivity

theorem GP_nonneg : 0 ≤ GP L := by
  unfold GP
  have := placeWeight_nonneg L
  have := etaP_nonneg L
  have := L.Sc_pos
  linarith

theorem eP_nonneg {C : ℝ} (hC : 0 ≤ C) (l : ℕ) : 0 ≤ eP L C l := by
  unfold eP
  apply mul_nonneg hC
  have h1 : 0 ≤ hB L / l := div_nonneg (by linarith [one_le_hB L]) (by positivity)
  have h2 : 0 ≤ Real.logb l (hB L) := by
    unfold Real.logb
    exact div_nonneg (Real.log_nonneg (one_le_hB L)) (Real.log_natCast_nonneg l)
  linarith

theorem bandI_nonneg (C : ℝ) (l : ℕ) : 0 ≤ bandI L C l := by
  unfold bandI; split_ifs <;> norm_num

theorem flatB_nonneg (C : ℝ) (l : ℕ) : 0 ≤ flatB L C l := by
  unfold flatB
  have := placeWeight_nonneg L
  have := etaP_nonneg L
  have := L.Sc_pos
  have := Lg_nonneg L
  have := bandI_nonneg L C l
  have : 0 ≤ (wP L + eta₃ L) / l := by positivity
  have : 0 ≤ eta₃ L * bandI L C l := by positivity
  linarith

theorem rowBr_nonneg {l : ℕ} (hl : 2 ≤ l) : 0 ≤ rowBr L l := by
  unfold rowBr
  have hl1 : (0 : ℝ) ≤ (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have := one_le_hB L
  have := GP_nonneg L
  have := Lg_nonneg L
  have : 0 ≤ hB L / ((l : ℝ) - 1) ^ (jA L l + 1) := div_nonneg (by linarith) (pow_nonneg hl1 _)
  have : 0 ≤ (GP L + 1) * ((jA L l : ℝ) + 1) := by positivity
  linarith

end Signs

theorem ge_five {l : ℕ} (hp : l.Prime) (h2 : l ≠ 2) (h3 : l ≠ 3) : 5 ≤ l := by
  by_contra h
  push_neg at h
  interval_cases l <;> simp_all (config := {decide := true})

theorem flatCD_le (L : SizeData₂ D) (tb : Tab L) (C : ℝ) (hBand : BandPlaceWeightApproximation L tb C) {i : D.nd.Loc}
    (hti : TwLoc D i) {lam : HeightOneSpectrum (𝓞 D.host.E)} {l : ℕ} (hlam : lam ∈ placesOver D.host.E l)
    (hl : l.Prime) : flatCD L tb i lam l ≤ flatB L C l := by
  classical
  unfold flatCD flatB
  have he := etaP_nonneg L
  by_cases hb : tb.band i lam
  · have hI : bandI L C l = 1 := by
      unfold bandI
      rw [if_pos (hBand i lam hti hb l hlam hl)]
    rw [if_pos hb, hI]
  · rw [if_neg hb]
    have := bandI_nonneg L C l
    have : 0 ≤ eta₃ L * bandI L C l := mul_nonneg he this
    linarith

theorem loc_le_lamB (L : SizeData₂ D) (tb : Tab L) (C : ℝ) (hC : 0 < C)
    (h5 : adm5 L tb C) (hA : admA L tb C) (hRowB : admB L tb C) (hCc : MediumInertPrimeLengthBound L tb C) (hD : SmallInertPrimeSmallOrderLengthBound L tb C)
    (hBand : BandPlaceWeightApproximation L tb C) (hE : LargePrimeLengthVanishing L tb) (hF : SmallPrimeLengthBound L tb C) (hG : RamifiedPrimeLengthBound L tb C)
    (i : D.nd.Loc) (hti : TwLoc D i) (hlg : D.nd.l i ∉ gset D) :
    sumOver D (D.nd.l i) (tb.len i) + tb.BB i ≤
      lamB L tb C (D.nd.l i) := by
  classical
  have hp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  set l := D.nd.l i with hl
  have hS := sumOver_eq D hp (tb.len i)
  set T := (placesOver_finite D.host.E hp).toFinset with hT
  have hmemT : ∀ lam ∈ T, lam ∈ placesOver D.host.E l := fun lam h => (Set.Finite.mem_toFinset _).1 h
  have hn := sum_nLam_le D hp
  have hn1 := sum_nLam_succ_le D hp
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  have hm0 : (0 : ℝ) ≤ D.R.m := by positivity
  have hr0 : (0 : ℝ) ≤ D.R.r := by positivity
  unfold lamB
  by_cases h23 : l ∈ D.host.small ∨ l = 3
  · rw [if_pos h23]
    exact hF i hti h23
  have hsm : l ∉ D.host.small := fun h => h23 (Or.inl h)
  have h2 : l ≠ 2 := fun h => hsm (by rw [h]; exact two_mem_small D)
  have h3 : l ≠ 3 := fun h => h23 (Or.inr h)
  rw [if_neg h23]
  by_cases hqd : l = D.host.q ∨ l = D.host.d
  · rw [if_pos hqd]
    exact (hG.1 i hti hqd).trans (hG.2 l hqd)
  rw [if_neg hqd]
  by_cases he : lStar L < l ∧ l ∉ tb.exc
  · rw [if_pos he]
    obtain ⟨hlen, hBB⟩ := hE.1 i hti ⟨he.1, hlg, he.2⟩
    rw [hBB, hS, Finset.sum_eq_zero (fun lam hlam => hlen lam (hmemT lam hlam))]
    norm_num
  rw [if_neg he]
  · have hq : l ≠ D.host.q := fun h => hqd (Or.inl h)
    have hd : l ≠ D.host.d := fun h => hqd (Or.inr h)
    have h5l := ge_five hp h2 h3
    have hle : (l : ℝ) ≤ lStar L ∨ l ∈ tb.exc := by
      by_contra hc
      push_neg at hc
      exact he ⟨hc.1, hc.2⟩
    have hBB := h5 i hti ⟨hsm, hq, hd, hlg⟩
    have hBB' : tb.BB i ≤ bbB L C := by unfold bbB; exact hBB
    suffices hlen : sumOver D l (tb.len i) ≤ lenB L C l by linarith
    rw [hS]
    have he' := eP_nonneg L hC.le l
    unfold lenB
    by_cases hsp : SplitK D l
    · rw [if_pos hsp]
      have ha : 2 * sumOver D l (tb.len i) ≤
          sumOver D l (fun lam => (2 * (nLam D lam : ℝ) * D.R.m + 1) * eP L C l) :=
        hA i hti ⟨h5l, hsp, hle, hlg⟩
      rw [hS, sumOver_eq D hp] at ha
      have : ∑ lam ∈ T, (2 * (nLam D lam : ℝ) * D.R.m + 1) * eP L C l ≤
          ∑ lam ∈ T, ((2 * D.R.m + 1) * eP L C l) * (nLam D lam : ℝ) := by
        apply Finset.sum_le_sum
        intro lam _
        have : (1 : ℝ) ≤ nLam D lam := by exact_mod_cast nLam_pos D lam
        nlinarith
      rw [← Finset.mul_sum] at this
      have h2f : (2 * (D.R.m : ℝ) + 1) * eP L C l * ∑ lam ∈ T, (nLam D lam : ℝ) ≤
          (2 * (D.R.m : ℝ) + 1) * eP L C l * (2 * D.R.f) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      nlinarith
    rw [if_neg hsp]
    have hin : InertK D l := (split_or_inert D hsm hq hd).resolve_left hsp
    by_cases hb : (l : ℝ) < lA L ∧ 4 * D.host.Lw < ordH D l
    · rw [if_pos hb]
      have hb' := hRowB i hti ⟨hin, hb.1, hb.2, hlg⟩
      have hbr := rowBr_nonneg L (show 2 ≤ l by omega)
      calc ∑ lam ∈ T, tb.len i lam
          ≤ ∑ lam ∈ T, (C * D.R.r * rowBr L l) * ((nLam D lam : ℝ) + 1) := by
            apply Finset.sum_le_sum
            intro lam hlam
            have := hb' lam (hmemT lam hlam)
            unfold rowBr
            nlinarith
        _ = (C * D.R.r * rowBr L l) * ∑ lam ∈ T, ((nLam D lam : ℝ) + 1) := by rw [Finset.mul_sum]
        _ ≤ (C * D.R.r * rowBr L l) * (4 * D.R.f) := mul_le_mul_of_nonneg_left hn1 (by positivity)
        _ = 4 * (D.R.f : ℝ) * (C * D.R.r * rowBr L l) := by ring
    · rw [if_neg hb]
      have hX : ∀ lam ∈ T, tb.len i lam ≤
          (C * D.R.r * (hB L / (l : ℝ) ^ 2 + flatB L C l)) * ((nLam D lam : ℝ) + 1) +
            (C * D.R.m * eP L C l) * (nLam D lam : ℝ) := by
        intro lam hlam
        have hfl := flatCD_le L tb C hBand hti (hmemT lam hlam) hp
        have hCr : 0 ≤ C * ((nLam D lam : ℝ) + 1) * D.R.r := by positivity
        by_cases hc : lA L ≤ l
        · have := hCc i hti ⟨hin, hc, hle, hlg⟩ lam (hmemT lam hlam)
          have : C * ((nLam D lam : ℝ) + 1) * D.R.r * (hB L / (l : ℝ) ^ 2 + flatCD L tb i lam l) ≤
              C * ((nLam D lam : ℝ) + 1) * D.R.r * (hB L / (l : ℝ) ^ 2 + flatB L C l) :=
            mul_le_mul_of_nonneg_left (by linarith) hCr
          nlinarith
        · push_neg at hc
          have hord : ordH D l ≤ 4 * D.host.Lw := by
            by_contra ho
            push_neg at ho
            exact hb ⟨hc, ho⟩
          have := hD i hti ⟨hin, hc, hord, hlg⟩ lam (hmemT lam hlam)
          have : C * ((nLam D lam : ℝ) + 1) * D.R.r * flatCD L tb i lam l ≤
              C * ((nLam D lam : ℝ) + 1) * D.R.r * flatB L C l :=
            mul_le_mul_of_nonneg_left hfl hCr
          nlinarith
      have hfb := flatB_nonneg L C l
      have hh : 0 ≤ hB L / (l : ℝ) ^ 2 := div_nonneg (by linarith [one_le_hB L]) (by positivity)
      calc ∑ lam ∈ T, tb.len i lam
          ≤ ∑ lam ∈ T, ((C * D.R.r * (hB L / (l : ℝ) ^ 2 + flatB L C l)) * ((nLam D lam : ℝ) + 1) +
            (C * D.R.m * eP L C l) * (nLam D lam : ℝ)) := Finset.sum_le_sum hX
        _ = (C * D.R.r * (hB L / (l : ℝ) ^ 2 + flatB L C l)) * ∑ lam ∈ T, ((nLam D lam : ℝ) + 1) +
            (C * D.R.m * eP L C l) * ∑ lam ∈ T, (nLam D lam : ℝ) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ (C * D.R.r * (hB L / (l : ℝ) ^ 2 + flatB L C l)) * (4 * D.R.f) +
            (C * D.R.m * eP L C l) * (2 * D.R.f) := by
            gcongr
        _ = _ := by ring

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7}

theorem VVr_nonneg (D : D7) (l : ℕ) : 0 ≤ VVr D l := by
  unfold VVr Rows.Data.VV
  exact_mod_cast Finset.sum_nonneg fun e _ => D.what₂.shaLen_nonneg l e

theorem vvTerm_nonneg (D : D7) (l : ℕ) : 0 ≤ vvTerm D l := by
  unfold vvTerm
  split_ifs
  · refine mul_nonneg ?_ (Real.log_natCast_nonneg l)
    exact_mod_cast Finset.sum_nonneg fun e _ => D.what₂.shaLen_nonneg l e
  · exact le_rfl

theorem vhE_nonneg (D : D7) (l : ℕ) : 0 ≤ vhE D l := by unfold vhE; positivity

open Classical in

def lamG (L : SizeData₂ D) (tb : Tab L) (C : ℝ) (l : ℕ) : ℝ :=
  if l ∈ gset D then C * L.sc.x ^ C * L.etaSz else lamB L tb C l

theorem lamB_nonneg (L : SizeData₂ D) (tb : Tab L) {C : ℝ} (hC : 0 < C) {l : ℕ} (hl : 2 ≤ l) :
    0 ≤ lamB L tb C l := by
  classical
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  have hm0 : (0 : ℝ) ≤ D.R.m := by positivity
  have hr0 : (0 : ℝ) ≤ D.R.r := by positivity
  have hb := one_le_b L
  have hlx : 0 < Real.log L.sc.x := Real.log_pos L.sc.one_lt_alt
  have hxC : 0 ≤ L.sc.x ^ C := Real.rpow_nonneg (x_pos L).le _
  have hLg := Lg_nonneg L
  have he := eP_nonneg L hC.le l
  unfold lamB
  split_ifs
  · positivity
  · positivity
  · exact le_rfl
  · have hbb : 0 ≤ bbB L C := by unfold bbB; positivity
    have hlen : 0 ≤ lenB L C l := by
      unfold lenB
      have := rowBr_nonneg L hl
      have := flatB_nonneg L C l
      have hh : 0 ≤ hB L / (l : ℝ) ^ 2 := div_nonneg (by linarith [one_le_hB L]) (by positivity)
      split_ifs <;> positivity
    linarith

open Classical in

theorem etaSum_le (L : SizeData₂ D) (tb : Tab L) (C : ℝ) (P : ParameterChoice' D L) (hA : AdmT L tb C P)
    (_hg2 : ∀ l ∈ gset D, l ≠ 2) (hsumm : Summable (vvTerm D)) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) :
    etaSum L j ≤ (L.dZ0 j : ℝ) * (6 + UpperTheory.KStar.nuBudget D + Real.log (Formalism.MainNotions.N.hE D.host : ℝ) + Real.log (D.what₂.restRowsFiniteGroupCard : ℝ) +
      ∑ l ∈ (L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0)).image
        (fun w => D.what₂.places.resChar w), Real.log l * lamG L tb C l) + (L.dZ0 j : ℝ) * ∑' l, vvTerm D l := by
  classical
  obtain ⟨h1, h2, h3, h4, h5, h6, hRa, hRb, hRc, hRd, hBand, hRe, hExc, hRf, hRg, hRh, hPar⟩ := hA
  have hC : 0 < C := lt_of_lt_of_le P.CLw_pos hPar.1
  set S := (L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0)).image
    (fun w => D.what₂.places.resChar w) with hSdef
  have hSp : ∀ l ∈ S, l.Prime := by
    intro l hl
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.1 hl
    exact D.what₂.places.resChar_prime w

  let sig : ℕ → ℝ := fun l => nuL D l + 2 / (l : ℝ) ^ 2
  let VVo : ℕ → ℝ := fun l => VVr D l
  let vG : ℕ → ℝ := fun l => (padicValNat l D.what₂.restRowsFiniteGroupCard : ℝ)
  let U : ℕ → ℝ := fun l => sig l + lamG L tb C l + VVo l + vhE D l + vG l
  have hd0 : (0 : ℝ) ≤ L.dZ0 j := by positivity
  have hper : ∀ l ∈ S, etaAt L j l ≤ Real.log l * ((L.dZ0 j : ℝ) * U l) := by
    intro l hl
    have hp := hSp l hl
    have hsig0 : 0 ≤ sig l := by have := nuL_nonneg D l; simp only [sig]; positivity
    have hVVo0 : 0 ≤ VVo l := VVr_nonneg D l
    have hvG0 : 0 ≤ vG l := by simp only [vG]; positivity
    have hvh := vhE_nonneg D l
    by_cases hlg : l ∈ gset D
    · refine (etaAt_le_g L tb C hRh h6 hj hlg).trans ?_
      apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg l)
      apply mul_le_mul_of_nonneg_left _ hd0
      simp only [U, sig, VVo, lamG, if_pos hlg]
      have : 0 ≤ nuL D l := nuL_nonneg D l
      linarith
    · have hlam0 : 0 ≤ lamG L tb C l := by
        simp only [lamG, if_neg hlg]; exact lamB_nonneg L tb hC hp.two_le
      have hU0 : 0 ≤ U l := by simp only [U]; linarith
      refine etaAt_le L hj hlg hU0 h1 h2 h3 ?_
      intro i hti hli π hπ
      have hl' : D.nd.l i ∉ gset D := hli ▸ hlg
      have hloc := loc_le_lamB L tb C hC h5 hRa hRb hRc hRd hBand hRe hRf hRg i hti hl'
      have h4' := h4 i hti hl' π hπ
      have h6' := h6.1 i hti π hπ
      rw [hli] at hloc h4' h6'
      simp only [U, sig, VVo, vG, lamG, if_neg hlg]
      linarith

  have hsum : etaSum L j ≤ (L.dZ0 j : ℝ) * ∑ l ∈ S, Real.log l * U l := by
    rw [etaSum_eq_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    refine (hper l hl).trans (le_of_eq (by ring))
  refine hsum.trans ?_

  have hsig : ∑ l ∈ S, Real.log l * sig l ≤ 6 + UpperTheory.KStar.nuBudget D := by
    have hA2 : ∑ l ∈ S, Real.log l / (l : ℝ) ^ 2 ≤ 2 := by
      have := Sums.sum_log_div_sq_le S
      have heq : S.filter (fun l : ℕ => 2 ≤ l) = S := Finset.filter_true_of_mem (fun l hl => (hSp l hl).two_le)
      rw [heq] at this
      exact this
    have hν := UpperTheory.KStar.sum_nuL_le D S hSp
    have e : ∑ l ∈ S, Real.log l * sig l = ∑ l ∈ S, nuL D l * Real.log l + 2 * ∑ l ∈ S, Real.log l / (l : ℝ) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by simp only [sig]; ring
    linarith
  have hVV : ∑ l ∈ S, Real.log l * VVo l ≤ ∑' l, vvTerm D l := by
    have heq : ∑ l ∈ S, Real.log l * VVo l = ∑ l ∈ S, vvTerm D l := by
      refine Finset.sum_congr rfl (fun l hl => ?_)
      have hp := hSp l hl
      simp only [VVo]
      unfold vvTerm VVr Rows.Data.VV
      rw [if_pos hp]
      ring
    rw [heq]
    exact Summable.sum_le_tsum S (fun l _ => vvTerm_nonneg D l) hsumm
  have hvh : ∑ l ∈ S, Real.log l * vhE D l ≤ Real.log (Formalism.MainNotions.N.hE D.host : ℝ) := by
    have := Sums.sum_padicVal_log_le S hSp (Formalism.MainNotions.N.hE D.host) (by
      unfold Formalism.MainNotions.N.hE NumberField.classNumber; exact Fintype.card_ne_zero)
    refine le_of_eq_of_le (Finset.sum_congr rfl (fun l _ => ?_)) this
    unfold vhE; ring
  have hvG : ∑ l ∈ S, Real.log l * vG l ≤ Real.log (D.what₂.restRowsFiniteGroupCard : ℝ) := by
    have := Sums.sum_padicVal_log_le S hSp D.what₂.restRowsFiniteGroupCard D.what₂.restRowsFiniteGroupCard_pos.ne'
    refine le_of_eq_of_le (Finset.sum_congr rfl (fun l _ => ?_)) this
    simp only [vG]; ring
  have hsplit : ∑ l ∈ S, Real.log l * U l = ∑ l ∈ S, Real.log l * sig l + ∑ l ∈ S, Real.log l * lamG L tb C l +
      ∑ l ∈ S, Real.log l * VVo l + ∑ l ∈ S, Real.log l * vhE D l + ∑ l ∈ S, Real.log l * vG l := by
    simp only [U, mul_add, Finset.sum_add_distrib]
  rw [hsplit, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ hd0
  linarith

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions

def Mst (D : D7) : ℕ := 2 ^ (D.R.e + 2 - Nat.log 2 (4 * D.host.Lw))

lemma pm_mod_of_dvd (l M N : ℕ) (hM : 0 < M) (hMN : M ∣ N) (hN : 0 < N)
    (h : l % N = 1 ∨ l % N = N - 1) : l % M = 1 ∨ l % M = M - 1 := by
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · have hM1 : M = 1 := by omega
    subst hM1; right; simp [Nat.mod_one]
  have hN2 : 2 ≤ N := le_trans hM2 (Nat.le_of_dvd hN hMN)
  rcases h with h | h
  · left
    rw [← Nat.mod_mod_of_dvd l hMN, h, Nat.mod_eq_of_lt (by omega)]
  · right
    have h0 : (l + 1) % N = 0 := by
      rw [Nat.add_mod, h, Nat.mod_eq_of_lt (show 1 < N by omega), Nat.sub_add_cancel (by omega),
        Nat.mod_self]
    have h1 : M ∣ l + 1 := dvd_trans hMN (Nat.dvd_of_mod_eq_zero h0)
    have hr := Nat.mod_lt l hM
    have h3 : (l % M + 1) % M = 0 := by
      rw [Nat.mod_add_mod]; exact Nat.mod_eq_zero_of_dvd h1
    generalize l % M = r at hr h3 ⊢
    by_contra hne
    have hlt : r + 1 < M := by omega
    rw [Nat.mod_eq_of_lt hlt] at h3
    omega

theorem rowd_cong (D : D7) (l : ℕ) (hl : Odd l) (hord : ordH D l ≤ 4 * D.host.Lw) :
    l % Mst D = 1 ∨ l % Mst D = Mst D - 1 := by
  have hne := Cong.ordPM_nonempty (D.R.e + 2) l hl
  have hmem : ordH D l ∈ {o : ℕ | 0 < o ∧ ((l : ZMod (2 ^ (D.R.e + 2))) ^ o = 1 ∨
      (l : ZMod (2 ^ (D.R.e + 2))) ^ o = -1)} := Nat.sInf_mem hne
  obtain ⟨ho, hpm⟩ := hmem
  have key := Cong.pm_one_of_pow (D.R.e + 2) l (ordH D l) hl ho hpm
  have hv : padicValNat 2 (ordH D l) ≤ Nat.log 2 (4 * D.host.Lw) :=
    Nat.le_log_of_pow_le (by norm_num) ((Cong.two_pow_padicVal_le _ ho).trans hord)
  have hdvd : Mst D ∣ 2 ^ (D.R.e + 2 - padicValNat 2 (ordH D l)) := by
    unfold Mst; exact Nat.pow_dvd_pow 2 (by omega)
  exact pm_mod_of_dvd l (Mst D) _ (by unfold Mst; positivity) hdvd (by positivity) key

theorem Mst_ge (D : D7) (hV : Nat.log 2 (4 * D.host.Lw) ≤ D.R.e + 2) (hLw : 0 < D.host.Lw) :
    ((2 ^ D.R.e : ℕ) : ℝ) / D.host.Lw ≤ Mst D := by
  have hpow : 2 ^ Nat.log 2 (4 * D.host.Lw) ≤ 4 * D.host.Lw := Nat.pow_log_le_self 2 (by omega)
  have h1 : Mst D * 2 ^ Nat.log 2 (4 * D.host.Lw) = 4 * 2 ^ D.R.e := by
    unfold Mst; rw [← pow_add, Nat.sub_add_cancel hV, pow_add]; ring
  have h2 : Mst D * 2 ^ Nat.log 2 (4 * D.host.Lw) ≤ Mst D * (4 * D.host.Lw) :=
    Nat.mul_le_mul_left _ hpow
  have hnat : 2 ^ D.R.e ≤ Mst D * D.host.Lw := by nlinarith
  rw [div_le_iff₀ (by exact_mod_cast hLw)]
  exact_mod_cast hnat

end Formalism.MainNotions.TwistedPlaces

end

noncomputable section

namespace Formalism.MainNotions.ExportFamilies

alias etaSum_le := Formalism.MainNotions.TwistedPlaces.etaSum_le
alias placeWeight_nonneg := Formalism.MainNotions.TwistedPlaces.placeWeight_nonneg
alias flatCD_le := Formalism.MainNotions.TwistedPlaces.flatCD_le
alias one_le_b := Formalism.MainNotions.TwistedPlaces.one_le_b
alias vhE_nonneg := Formalism.MainNotions.TwistedPlaces.vhE_nonneg
alias VVr_nonneg := Formalism.MainNotions.TwistedPlaces.VVr_nonneg
alias Mst := Formalism.MainNotions.TwistedPlaces.Mst
alias one_le_hB := Formalism.MainNotions.TwistedPlaces.one_le_hB
alias sumOver_eq := Formalism.MainNotions.TwistedPlaces.sumOver_eq
alias finrank_E_host := Formalism.MainNotions.TwistedPlaces.finrank_E_host
alias mem_primesOver_of_mem := Formalism.MainNotions.TwistedPlaces.mem_primesOver_of_mem
alias etaSum_eq_sum := Formalism.MainNotions.TwistedPlaces.etaSum_eq_sum
alias bandI := Formalism.MainNotions.TwistedPlaces.bandI
alias nLam_pos := Formalism.MainNotions.TwistedPlaces.nLam_pos
alias flatB := Formalism.MainNotions.TwistedPlaces.flatB
alias flatB_nonneg := Formalism.MainNotions.TwistedPlaces.flatB_nonneg
alias w''_nonneg := Formalism.MainNotions.TwistedPlaces.w''_nonneg
alias ge_five := Formalism.MainNotions.TwistedPlaces.ge_five
alias lamB_nonneg := Formalism.MainNotions.TwistedPlaces.lamB_nonneg
alias rowBr := Formalism.MainNotions.TwistedPlaces.rowBr
alias bbB := Formalism.MainNotions.TwistedPlaces.bbB
alias vvTerm_nonneg := Formalism.MainNotions.TwistedPlaces.vvTerm_nonneg
alias eP_nonneg := Formalism.MainNotions.TwistedPlaces.eP_nonneg
alias bandI_nonneg := Formalism.MainNotions.TwistedPlaces.bandI_nonneg
alias lamB := Formalism.MainNotions.TwistedPlaces.lamB
alias x_pos := Formalism.MainNotions.TwistedPlaces.x_pos
alias wB_nonneg := Formalism.MainNotions.TwistedPlaces.wB_nonneg
alias etaP_nonneg := Formalism.MainNotions.TwistedPlaces.etaP_nonneg
alias GP_nonneg := Formalism.MainNotions.TwistedPlaces.GP_nonneg
alias lenB := Formalism.MainNotions.TwistedPlaces.lenB
alias sum_nLam_succ_le := Formalism.MainNotions.TwistedPlaces.sum_nLam_succ_le
alias rowBr_nonneg := Formalism.MainNotions.TwistedPlaces.rowBr_nonneg
alias placesOver_finite := Formalism.MainNotions.TwistedPlaces.placesOver_finite
alias lamG := Formalism.MainNotions.TwistedPlaces.lamG
alias split_or_inert := Formalism.MainNotions.TwistedPlaces.split_or_inert
alias pm_mod_of_dvd := Formalism.MainNotions.TwistedPlaces.pm_mod_of_dvd
alias logWeight_nonneg := Formalism.MainNotions.TwistedPlaces.logWeight_nonneg
alias sum_nLam_le := Formalism.MainNotions.TwistedPlaces.sum_nLam_le
alias b'_pos := Formalism.MainNotions.TwistedPlaces.b'_pos
alias rowd_cong := Formalism.MainNotions.TwistedPlaces.rowd_cong
alias etaAt_le_g := Formalism.MainNotions.TwistedPlaces.etaAt_le_g
alias loc_le_lamB := Formalism.MainNotions.TwistedPlaces.loc_le_lamB
alias Mst_ge := Formalism.MainNotions.TwistedPlaces.Mst_ge
alias etaAt_le := Formalism.MainNotions.TwistedPlaces.etaAt_le
alias Lg_nonneg := Formalism.MainNotions.TwistedPlaces.Lg_nonneg

end Formalism.MainNotions.ExportFamilies

end
