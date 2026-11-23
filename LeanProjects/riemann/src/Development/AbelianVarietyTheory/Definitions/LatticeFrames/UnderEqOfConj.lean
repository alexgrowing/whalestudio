import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TowerAtPre
import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharTameAtOfFactorsThroughResidue

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

namespace GlobalTheory.ChainTw.RModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem not_two_primes {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊤) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h1 : (p : 𝓞 D.host.E) ∈ I) (h2 : (q : 𝓞 D.host.E) ∈ I) : False := by
  obtain ⟨a, b, h⟩ : IsCoprime (p : 𝓞 D.host.E) q := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  exact hI ((Ideal.eq_top_iff_one _).2 (h ▸ I.add_mem (I.mul_mem_left _ h1) (I.mul_mem_left _ h2)))

theorem char_mem {P : Pl D.host.E} {q : ℕ} (h : Nat.card (kP P) = q) : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
  have h1 : Nat.card (kP P) • (1 : kP P) = 0 := card_nsmul_eq_zero'
  rw [h, nsmul_one] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_natCast _ q).trans h1)

theorem nat_mem_of_conj {P P' : Pl D.host.E} (h : Lev.IsConjPl (D := D) P P') {q : ℕ} (hq : (q : 𝓞 D.host.E) ∈ P.asIdeal) :
    (q : 𝓞 D.host.E) ∈ P'.asIdeal := by
  obtain ⟨c', hc', e⟩ := h _ hq
  have : c' = q := by
    apply RingOfIntegers.ext
    rw [e]; simp
  exact this ▸ hc'

theorem g_mem_of_div (C : Formalism.L2.Host.CharFrame D) {k : Fin 2} {PP : Pl D.host.E} (h : C.P.Div k PP) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  have h0 := C.P.pb_over k
  rw [← h] at h0
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h0
  rw [map_natCast] at h2
  exact h2

theorem disjoint_Pg_Q (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) (t : T) : Disjoint L.Pg (L.Q t) := by
  rw [Finset.disjoint_left]
  intro P hP hPQ
  obtain ⟨i, hi⟩ := (hL.Pg P).1 hP
  obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hL.Q_pl t P hPQ
  exact not_two_primes P.isPrime.ne_top (D.host.g_prime i) hq (fun h => hqg i h.symm) (g_mem_of_div L.C hi) (char_mem hcard)

theorem rangeX_iff : RangeX R ↔ Formalism.IndefR.RecTie.TopMultH R := Iff.rfl

theorem comR_S (t : T) : (comR R t).S = GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
  unfold Com.S GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl comR
  congr

theorem mem_S (hL : R.toLevCh.Is A.μ0) (t : T) (k : Fin 2) (P : Pl D.host.E)
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : P.under (𝓞 D.host.F) ∈ (comR R t).S := by
  classical
  unfold Com.S
  rw [Finset.mem_image]
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D R.C.P k P hk with h1 | ⟨P', h1, hc⟩
  · exact ⟨P, by simp only [comR, Finset.mem_union]; exact Or.inl ((hL.Pg P).2 ⟨k, h1⟩), rfl⟩
  · refine ⟨P', by simp only [comR, Finset.mem_union]; exact Or.inl ((hL.Pg P').2 ⟨k, h1⟩), ?_⟩
    ext x
    show algebraMap _ _ x ∈ P'.asIdeal ↔ algebraMap _ _ x ∈ P.asIdeal
    rw [hc, Formalism.L2.Col.mem_conjIdeal]
    have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap _ _ x := by
      apply RingOfIntegers.ext
      exact (D.sp.cm.fixed _).2 ⟨x, rfl⟩
    rw [this]

theorem stages (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (t : T) :
    (∀ j < D.R.m, IsStage (comR R t) (twR R t) j (stY R t j)) ∧ IsStage (comR R t) (twR R t) D.R.m (stX R t) := by
  refine ⟨fun j hj => ⟨r_le_Y j, rfl, ?_⟩, ⟨r_le_X, rfl, ?_⟩⟩
  · have hm : min j D.R.m = j := min_eq_left hj.le
    obtain ⟨c, hc⟩ := hL.βY j hj
    have hν : (R.νY t j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
      by_cases h1 : j + 1 < D.R.m
      · exact ⟨(hM.νY t j h1).1.1, (hM.νY t j h1).2⟩
      · have : j = D.R.m - 1 := by omega
        subst this
        exact ⟨(hM.νY' t).1.1, (hM.νY' t).2⟩
    refine ⟨?_, D.sp.Y_sig _, fun τ => ?_, ?_, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1,
      ⟨_, hc, fun P hP hN => hP ?_⟩, ⟨r_le_Y j, R.xiR t, rfl⟩, hν.1, hν.2⟩
    · show (D.sp.Y (min j D.R.m)).rank = _
      rw [D.sp.Y_rank _ (min_le_right _ _), hm]
    · show (D.sp.Y (min j D.R.m)).sig τ = _
      rw [D.Y_sigval _ (min_le_right _ _), hm]
    · show parB _ (min j D.R.m) = _
      rw [hm]
    · push_cast at hN
      have := P.isPrime.mem_of_pow_mem _ hN
      rcases P.isPrime.mem_or_mem this with h0 | h0
      · exact mem_S R hL t 0 P h0
      · exact mem_S R hL t 1 P h0
  · obtain ⟨c, hc⟩ := hL.βX
    refine ⟨D.sp.X'_rank, D.sp.X'_sig, fun τ => ?_, rfl, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1,
      ⟨_, hc, fun P _ hN => ?_⟩, ⟨r_le_X, R.xiR t, rfl⟩, (hM.νX t).1.1, (hM.νX t).2⟩
    · show D.sp.X'.sig τ = _
      rw [D.X'_posDef τ, D.sp.X'_rank]; simp [sigYD, Ranks.rankY, Ranks.rankX']
    · rw [one_pow, Nat.cast_one] at hN
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hN)

theorem steps (hC : R.IsChain) (h : RangeX R) (t : T) :
    (∀ k, k + 1 < D.R.m → IsStep (twR R t) (k + 1) (stepY R t k)) ∧ IsStep (twR R t) D.R.m (stepX R h t) := by
  refine ⟨fun k hk => ⟨hC.ωY t k hk, ⟨_, hC.vY t k hk⟩, hC.ptY t k hk, hC.ItY t k hk, hC.ioY t k (by omega)⟩,
    ⟨hC.ωX t, ⟨_, hC.vX t⟩, hC.ptX t, hC.ItX t, ?_, ?_⟩⟩
  · intro F φ v g
    exact (hC.ioX t).integ (LinearEquiv.ofEq _ _ (h t).symm F) φ v g
  · intro F φ v g
    exact (hC.ioX t).eq (LinearEquiv.ofEq _ _ (h t).symm F) φ v g

theorem twist_of (hL : R.toLevCh.Is A.μ0) (t : T) (hc : (comR R t).Is) (hne : ∀ PP ∈ R.Q t, R.xiR t PP ≠ 1) :
    (twR R t).Is (comR R t) := by
  have hd := disjoint_Pg_Q R.toLevCh hL t
  refine ⟨hc, rfl, hd, fun j PP hP => ?_, fun j PP hP => ?_, hne, fun g => Iff.rfl, rfl⟩
  · exact if_neg (Finset.disjoint_left.1 hd hP)
  · exact if_pos hP

theorem stepX_toCC (h : RangeX R) (t : T) (x : (R.HX t).H) :
    PiTensorProduct.lift.symm ((stepX R h t).io (toCC R h t x)).1 = GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.topStep R t x := rfl

theorem toCC_val (h : RangeX R) (t : T) (x : (R.HX t).H) (v) (g) :
    PiLocalization₂.val (toCC R h t x) v g = R.prX (R.cX.ext ((R.HX t).e x) g) v := rfl

theorem toCC_surj (h : RangeX R) (t : T) : Function.Surjective (toCC R h t) :=
  (LinearEquiv.ofEq _ _ (h t)).surjective.comp (LinearMap.surjective_rangeRestrict _)

theorem isInnerProduct_of_isMet (t : T) (k : ℕ) {ipD ip} (hm : IsMet (comR R t) (stY R t k) ipD ip) (x y : (stY R t k).CC (comR R t)) :
    GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsIP R t k (PiTensorProduct.lift.symm x.1) (PiTensorProduct.lift.symm y.1) (ip y x) := by
  intro v v'
  have h1 := hm.integ y x (PiTensorProduct.tprod ℂ v') (PiTensorProduct.tprod ℂ v)
  have h2 := hm.schur y x (PiTensorProduct.tprod ℂ v') (PiTensorProduct.tprod ℂ v)
  rw [hm.pure v' v] at h2
  have e : (fun g => star ((PiTensorProduct.lift.symm x.1) v g) * (PiTensorProduct.lift.symm y.1) v' g) =
      fun g => PiLocalization₂.val y (PiTensorProduct.tprod ℂ v') g * conj (PiLocalization₂.val x (PiTensorProduct.tprod ℂ v) g) := by
    funext g; rw [mul_comm]; rfl
  refine ⟨?_, ?_⟩
  · exact (congrArg (fun F => IntegrableOn F (stY R t k).fd (stY R t k).ν) e).mpr h1
  · exact (congrArg (fun F : GA D (stY R t k).V → ℂ => ∫ g in (stY R t k).fd, F g ∂(stY R t k).ν) e).trans h2

theorem ipDict_of (hv : ∀ k < D.R.m, ∃ v : (R.MY k).Vec, ∏ τ, ⟪(v τ : (R.MY k).H τ), (v τ : (R.MY k).H τ)⟫_ℂ ≠ 0) : IPDict R := by
  intro t k hk ipD ip hm x y a
  obtain ⟨v, hv⟩ := hv k hk
  exact ⟨fun h => hasPeterssonInner_unique _ _ _ _ _ v hv h (isInnerProduct_of_isMet R t k hm x y), fun h => h ▸ isInnerProduct_of_isMet R t k hm x y⟩

theorem stepExactNS_of (h : StepExact D) : StepExactNS D :=
  fun hg c w hw k hk s s' hs hs' p hp ipD ip hm m X hX mR hR φ v hc u₁ u₂ B hB hQ _ =>
    h hg c w hw k hk s s' hs hs' p hp ipD ip hm m X hX mR hR φ v hc u₁ u₂ B hB hQ

theorem Q_base (hL : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  ext PP
  simp only [Finset.notMem_empty, iff_false]
  intro hP
  have := (hL.Q_ram A.μ0 PP).2 (Or.inl hP)
  rw [hL.xi_base] at this
  exact this fun x _ => rfl

theorem isUnitAt_of (P : Pl D.host.E) (a : 𝓞 D.host.E) (k : D.host.Eˣ) (u : (kP P)ˣ) (hk : (k : D.host.E) = a)
    (hu : (u : kP P) = Ideal.Quotient.mk _ a) : Formalism.L2.Host.IsUnitAt P (Formalism.L2.Host.atFin P k) := by
  have ha : a ∉ P.asIdeal := fun h => by
    haveI := P.isMaximal
    haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
    have : (u : kP P) = 0 := hu.trans (Ideal.Quotient.eq_zero_iff_mem.2 h)
    exact u.ne_zero this
  show Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) = 1
  rw [GlobalTheory.ChainOnto.TameRes.val_alg, hk]
  exact GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem P a ha

theorem under_eq_of_conj {P P' : Pl D.host.E} (h : Lev.IsConjPl (D := D) P' P) :
    P'.under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P'.under (𝓞 D.host.F)).isMaximal.eq_of_le (P.under (𝓞 D.host.F)).isPrime.ne_top fun x hx => ?_)
  obtain ⟨c', hc', e⟩ := h _ hx
  have : c' = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    apply RingOfIntegers.ext
    exact e.trans ((D.sp.cm.fixed _).2 ⟨x, rfl⟩)
  show algebraMap _ _ x ∈ P.asIdeal
  rw [← this]; exact hc'

theorem com_is (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hC : R.IsChain) (t : T) : (comR R t).Is := by
  classical
  have hd := disjoint_Pg_Q R.toLevCh hL t
  have hμ : ∀ j : Fin D.R.m, ChrEq (R.toLevCh.mu t ((j : ℕ) + 1)) (R.C.mu0 j * R.xiH t) := fun j =>
    GlobalTheory.Mem.TupChar.chrEq_mul (hL.mu0 j) (hL.xi t)
  refine ⟨hM.inf, (hC.ωX t).std, ⟨hL.eta.1, GlobalTheory.Mem.TupChar.unramEverywhere hL.eta R.C.isEta.unr, GlobalTheory.HeckeCharacterRestriction.resEta_eta hL,
    fun τ => ?_, fun j hj => ?_⟩, fun j τ => ?_, fun j w hw => ?_, fun j => ⟨_, hμ j, fun PP hP a k u hk hu => ?_⟩, ?_⟩
  · exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (GlobalTheory.InnerSteps.hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, R.C.isEta.inf⟩) τ
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact ⟨GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t ⟨i, by omega⟩, GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t ⟨i, by omega⟩⟩
  · have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 j) (GlobalTheory.InnerSteps.hasInfQ_tauE (R.C.isMu0 j).inf) τ
    simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    haveI : IsTotallyComplex D.host.E := by infer_instance
    have h3 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun _ => 0) (hL.xi t)
      ⟨fun _ => 0, fun _ => by norm_num, fun x => by
        rw [GlobalTheory.TypeValues.inf_eq_one _ hn ho x]; simp⟩ τ
    exact GlobalTheory.InnerSteps.hasInfExp_mul_zero h1 h3
  · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ j) w).2 fun x hx => ?_
    have h1 := (R.C.isMu0 j).unr w (fun k hk => hw (mem_S R hL t k w hk)) x hx
    have h2 : (R.xiH t).UnrAt w := by
      by_contra hc
      apply hw
      show w.under (𝓞 D.host.F) ∈ (comR R t).S
      unfold Com.S
      rw [Finset.mem_image]
      rcases (hL.Q_ram t w).1 hc with h | ⟨P', h, hc⟩
      · exact ⟨w, by simp only [comR, Finset.mem_union]; exact Or.inr h, rfl⟩
      · exact ⟨P', by simp only [comR, Finset.mem_union]; exact Or.inr h, under_eq_of_conj hc⟩
    rw [Formalism.L2.Host.HChar.loc_mul, h1, h2 x hx, mul_one]
  · have hun := isUnitAt_of PP a k u hk hu
    show ((comR R t).chi ((j : ℕ) + 1) PP)⁻¹ u = (R.C.mu0 j).locK PP k * (R.xiH t).locK PP k
    have hP' : PP ∈ R.Pg ∨ PP ∈ R.Q t := by simpa only [comR, Finset.mem_union] using hP
    rcases hP' with h | h
    · have e : (comR R t).chi ((j : ℕ) + 1) PP = R.chi ((j : ℕ) + 1) PP := if_neg (Finset.disjoint_left.1 hd h)
      have h2 : (R.xiH t).UnrAt PP := by
        by_contra hc
        rcases (hL.Q_ram t PP).1 hc with h' | ⟨P', h', hc⟩
        · exact Finset.disjoint_left.1 hd h h'
        · obtain ⟨i, hi⟩ := (hL.Pg PP).1 h
          obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hL.Q_pl t P' h'
          exact not_two_primes PP.isPrime.ne_top hq (D.host.g_prime i) (hqg i)
            (nat_mem_of_conj hc (char_mem hcard)) (g_mem_of_div R.C hi)
      have h3 : (R.xiH t).locK PP k = 1 := h2 _ hun
      rw [e, h3, mul_one]
      exact hL.chi j PP h a k u hk hu
    · have e : (comR R t).chi ((j : ℕ) + 1) PP = (R.xiR t PP)⁻¹ := if_pos h
      obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hL.Q_pl t PP h
      have h3 : (R.C.mu0 j).locK PP k = 1 := (R.C.isMu0 j).unr PP (fun i hi =>
        not_two_primes PP.isPrime.ne_top hq (D.host.g_prime i) (hqg i) (char_mem hcard) hi) _ hun
      rw [e, inv_inv, h3, one_mul]
      exact hL.xiR t PP h a k u hk hu
  · obtain ⟨e, he, -⟩ := (hC.vX t).2
    exact ⟨e, he⟩

theorem xiR_ne (hL : R.toLevCh.Is A.μ0) (t : T) : ∀ PP ∈ R.Q t, R.xiR t PP ≠ 1 := by
  intro PP hP h1
  refine (hL.Q_ram t PP).2 (Or.inl hP) fun x hx => ?_
  have hc := hL.xiR t PP hP
  rw [h1] at hc
  have hU : IsOpen {z : PP.adicCompletion D.host.E | Valued.v (z - x) < 1} :=
    (GlobalTheory.ChainOnto.TameRes.isOpen_ltOne PP).preimage (continuous_sub_right _)
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap D.host.E PP).exists_mem_open hU ⟨x, by simp⟩
  have hk' : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) < Valued.v (x : PP.adicCompletion D.host.E) := by
    rw [hx]; exact hk
  have hv : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k) = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ hk']; exact hx
  have hv1 : PP.valuation D.host.E k = 1 := by rw [← GlobalTheory.ChainOnto.TameRes.val_alg]; exact hv
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hv1
  obtain ⟨a, s, h⟩ := PP.exists_primeCompl_mul_eq_of_integer k hv1.le
  have hs : (s : 𝓞 D.host.E) ∉ PP.asIdeal := s.2
  have hsv := GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem PP _ hs
  have hav : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) = 1 := by
    rw [← h, map_mul, hv1, hsv, one_mul]
  have ha : a ∉ PP.asIdeal := fun hm =>
    absurd hav (ne_of_lt ((PP.valuation_lt_one_iff_mem (K := D.host.E) a).mpr hm))
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  have key : ∀ (b : 𝓞 D.host.E), b ∉ PP.asIdeal → ∀ y : D.host.Eˣ, (y : D.host.E) = b → (R.xiH t).locK PP y = 1 := by
    intro b hb y hy
    have hms : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hb
    obtain ⟨b', hb'⟩ := Ideal.Quotient.exists_inv hms
    exact (hc b y (Units.mkOfMulEqOne _ b' hb') hy rfl).symm
  have hs0 : algebraMap (𝓞 D.host.E) D.host.E s ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hsv; exact zero_ne_one hsv
  have ha0 : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hav; exact zero_ne_one hav
  have hkk : Units.mk0 k hk0 * Units.mk0 _ hs0 = Units.mk0 _ ha0 := Units.ext h
  have hk1 : (R.xiH t).locK PP (Units.mk0 k hk0) = 1 := by
    have := congrArg ((R.xiH t).locK PP) hkk
    rwa [map_mul, key _ hs (Units.mk0 _ hs0) rfl, key _ ha (Units.mk0 _ ha0) rfl, mul_one] at this
  set y := Formalism.L2.Host.atFin PP (Units.mk0 k hk0) with hy
  have hyv : (y : PP.adicCompletion D.host.E) = algebraMap D.host.E (PP.adicCompletion D.host.E) k := rfl
  have ht := hL.xi_tame t PP (y * x⁻¹) (by
    unfold Formalism.L2.Host.IsUnitAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hyv, hv, hx, inv_one, mul_one]) (by
    have e : ((y * x⁻¹ : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) - 1 =
        (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) * (x : PP.adicCompletion D.host.E)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hyv, sub_mul, mul_inv_cancel₀ x.ne_zero]
    unfold Formalism.L2.Host.IsUnitAt at hx
    rw [e, map_mul, map_inv₀, hx, inv_one, mul_one]
    have hlt : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) < 1 := hk
    generalize Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) = z at hlt
    rcases eq_or_ne z 0 with rfl | hz
    · exact zero_le'
    · rw [← WithZero.exp_log hz] at hlt ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]
      push_cast
      omega)
  have hk2 : (R.xiH t).loc PP y = 1 := hk1
  rw [map_mul, hk2, one_mul, map_inv, inv_eq_one] at ht
  exact ht

theorem rChain (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hC : R.IsChain) (h : RangeX R) : RChain R h := fun t =>
  ⟨twist_of R hL t (com_is R hL hM hC t) (xiR_ne R hL t), (stages R hL hM t).1, (stages R hL hM t).2, (steps R hC h t).1, (steps R hC h t).2⟩

theorem zinv_pos (PP : Pl D.host.E) (a b : ℕ) : 0 < zinv PP a b := by
  refine Finset.prod_pos fun n hn => sub_pos.2 (inv_lt_one_of_one_lt₀ (one_lt_pow₀ ?_ ?_))
  · exact_mod_cast HeightOneSpectrum.one_lt_absNorm PP
  · have := (Finset.mem_Ioc.1 hn).1; omega

theorem rVol_zero (h : RVol R) (t : T) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D 0) (R.νY t 0) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ (Yc D 0) (R.νY A.μ0 0) := by
  have h2 := D.R.two_le_m
  rw [((h t).1 0 (by omega)).1, Finset.prod_eq_one, mul_one]
  intro PP _
  have := (zinv_pos PP 0 D.R.r).ne'
  simp [idxQ, zinv] at this ⊢
  exact this

end GlobalTheory.ChainTw.RModel

end
