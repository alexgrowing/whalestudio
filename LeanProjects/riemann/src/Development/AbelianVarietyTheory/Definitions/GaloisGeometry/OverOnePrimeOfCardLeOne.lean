import Mathlib
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions

open NumberField IsDedekindDomain IntermediateField

noncomputable section

namespace GlobalTheory.Formalism.L2.Col

open _root_.Formalism.BasicNotions _root_.Formalism.L2.Host _root_.Formalism.L2.DIV _root_.Formalism.FrobeniusOrbits

export _root_.Formalism.L2.Col (
  Chars Chars.FromHecke Chars.Ok Chars.Tied Dat Dat.Ok FQ_le_EQ Fields Fields.Core Fields.IsCond Fields.Kq Fields.Ok
  Fields.Ok.core Fields.Ok.f_pos Fields.AbelianUnramifiedExtensionConditions Fields.AbelianUnramifiedExtensionConditions.eight_le_f Fields.AbelianUnramifiedExtensionConditions.f_even Fields.AbelianUnramifiedExtensionConditions.four_dvd_f
  Fields.AbelianUnramifiedExtensionConditions.two_le_f Fields.conjO Fields.embBar Fields.embC Fields.f Fields.sig IsEtaT IsMu0 Primes Primes.Ok
  Primes.PiGCong Primes.PiGCong.g_cong Primes.natCast_dvd_intCast Primes.vG Primes.vGs Primes.vT Primes.vTbar QDat
  QDat.HasBase QDat.Off QDat.Ok QDat.TiedTo QDat.empty RowPar RowPar.aMinusRev RowPar.aPlus RowPar.bAt RowPar.dV
  RowPar.eAt RowPar.lamV RowPar.lamVQ RowPar.of RowPar.pOf RowPar.qOf RowPar.sg RowPar.sgHC RowPar.sgQ RowPar.sgTrue
  RowPar.vb Sizes Sizes.T_big Sizes.T_spread Sizes.T_spread_true Sizes.a_pos Sizes.spread_le_N Sizes.two_spread_lt Wts
  Wts.Ok Wts.aTop Wts.bTop Wts.deg Wts.degTrue Wts.lamN Wts.lamTrue Wts.lamV Wts.nuW Wts.sgTrue Wts.sgW divs embQ fin_EQ
  fin_F1Q fin_FQ fin_adjoin fin_sqQ finite_pow_eq fintypePsi hostFields hostTops map_le_of_normal normal_EQ normal_F1Q
  normal_adjoin normal_of_map_le normal_sqQ normal_sup' ofQ shiftW spread_shiftW two_le_N)

def quadFields (K : Type) [Field K] [NumberField K] [IsCMField K] : Fields where
  F := ℚ
  E := K
  K := K
  starE := IsCMField.starRing K
  starK := IsCMField.starRing K
  Tau := Unit
  emb := fun _ => RingHom.id K

theorem quadFields_ok (K : Type) [Field K] [NumberField K] [IsCMField K] (hK : Module.finrank ℚ K = 2) :
    (quadFields K).Ok := by
  have hne : RingHom.id K ≠ (quadFields K).embBar () := fun h =>
    IsCMField.complexConj_ne_one K (AlgEquiv.ext fun x => (RingHom.congr_fun h x).symm)
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  refine
    { realF := inferInstanceAs (IsTotallyReal ℚ)
      rankE := hK
      star_F := fun x => ?_
      conjE := fun φ x => IsCMField.complexEmbedding_complexConj K φ x
      cplxE := inferInstanceAs (IsTotallyComplex K)
      emb_star := fun _ _ => rfl
      card_Tau := ?_
      emb_inj := fun _ _ _ => rfl
      emb_ne := fun _ _ => hne
      emb_all := fun φ => ⟨(), ?_⟩
      cplxK := inferInstanceAs (IsTotallyComplex K)
      normalK := inferInstanceAs (Normal ℚ K)
      conjK := ⟨Classical.arbitrary (K →+* ℂ), fun x => IsCMField.complexEmbedding_complexConj K _ x⟩
      quad := ?_ }
  · exact map_ratCast (IsCMField.complexConj K) x
  · show Fintype.card Unit = Module.finrank ℚ ℚ
    simp
  · classical
    by_contra hφ
    push Not at hφ
    have hc : Fintype.card (K →+* K) ≤ 2 := by
      rw [Fintype.card_congr (RingHom.equivRatAlgHom (R := K) (S := K)), ← hK]
      exact AlgHom.card_le
    have h3 : ({φ, RingHom.id K, (quadFields K).embBar ()} : Finset (K →+* K)).card = 3 :=
      Finset.card_eq_three.2 ⟨_, _, _, hφ.1, hφ.2, hne, rfl⟩
    have := Finset.card_le_univ ({φ, RingHom.id K, (quadFields K).embBar ()} : Finset (K →+* K))
    omega
  · let e : (quadFields K).Kq ≃+* K :=
      RingEquiv.ofBijective (quadFields K).Kq.subtype ⟨Subtype.val_injective, fun x => ⟨⟨x, fun _ _ => rfl⟩, rfl⟩⟩
    rw [← hK]
    exact (AlgEquiv.ofRingEquiv (R := ℚ) (f := e) (fun r => map_ratCast e r)).toLinearEquiv.finrank_eq

instance isCyclotomicExtension_gauss : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
  CyclotomicField.isCyclotomicExtension 4 ℚ

theorem isCMField_gauss : IsCMField (CyclotomicField 4 ℚ) :=
  IsCyclotomicExtension.Rat.isCMField (CyclotomicField 4 ℚ) (S := {4}) ⟨4, rfl, by norm_num⟩

theorem exists_fields_ok : ∃ X : Fields, X.Ok ∧ X.f = 1 := by
  haveI := isCMField_gauss
  refine ⟨quadFields (CyclotomicField 4 ℚ), quadFields_ok _ ?_, rfl⟩
  rw [IsCyclotomicExtension.finrank (n := 4) (CyclotomicField 4 ℚ) (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide

def Wts.const {X : Fields} (Word : Type) {R : Ranks} (P : X.Tau → HCParam R) (tops : Finset X.Tau) : Wts X Word R :=
  ⟨fun τ => RowPar.of (P τ), fun _ τ => P τ, tops⟩

theorem Wts.const_ok {X : Fields} (Word : Type) {R : Ranks} (P : X.Tau → HCParam R) (tops : Finset X.Tau) :
    (Wts.const Word P tops).Ok :=
  ⟨fun τ => ⟨P τ, rfl⟩, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem QDat.empty_ok (X : Fields) (Pr : Primes X) : (QDat.empty X).Ok ∧ (QDat.empty X).Off Pr :=
  ⟨⟨fun _ h => absurd h (Finset.notMem_empty _), fun _ h => absurd h (Finset.notMem_empty _),
    fun _ h => absurd h (Finset.notMem_empty _), fun P => absurd P.2 (Finset.notMem_empty _)⟩,
    fun _ h => absurd h (Finset.notMem_empty _)⟩

def QDat.OverOnePrime {X : Fields} (Z : QDat X) (p : ℕ) : Prop :=
  ∀ P ∈ Z.Q, ∀ P' ∈ Z.Q, ((p : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ((p : ℕ) : 𝓞 X.E) ∈ P'.asIdeal →
    P.asIdeal.comap (RingOfIntegers.mapRingHom X.Kq.subtype) = P'.asIdeal.comap (RingOfIntegers.mapRingHom X.Kq.subtype)

theorem QDat.overOnePrime_iff {X : Fields} (Z : QDat X) (p : ℕ) :
    QDat.OverOnePrime Z p ↔ ∀ P ∈ Z.Q, ∀ P' ∈ Z.Q, ((p : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ((p : ℕ) : 𝓞 X.E) ∈ P'.asIdeal →
      ∀ x : 𝓞 X.E, (x : X.E) ∈ X.Kq → x ∈ P.asIdeal → x ∈ P'.asIdeal := by
  constructor
  · intro h P hP P' hP' h1 h2 x hx hxP
    have hint : IsIntegral ℤ (⟨(x : X.E), hx⟩ : X.Kq) :=
      (isIntegral_algHom_iff X.Kq.subtype.toIntAlgHom Subtype.val_injective).1 (RingOfIntegers.isIntegral_coe x)
    obtain ⟨y, hy⟩ : ∃ y : 𝓞 X.Kq, RingOfIntegers.mapRingHom X.Kq.subtype y = x :=
      ⟨⟨⟨(x : X.E), hx⟩, hint⟩, RingOfIntegers.ext rfl⟩
    have h3 : y ∈ P.asIdeal.comap (RingOfIntegers.mapRingHom X.Kq.subtype) := by
      rw [Ideal.mem_comap, hy]
      exact hxP
    rw [h P hP P' hP' h1 h2, Ideal.mem_comap, hy] at h3
    exact h3
  · intro h P hP P' hP' h1 h2
    ext y
    rw [Ideal.mem_comap, Ideal.mem_comap]
    exact ⟨h P hP P' hP' h1 h2 _ (y : X.Kq).2, h P' hP' P hP h2 h1 _ (y : X.Kq).2⟩

theorem QDat.OverOnePrime.conj_notMem {X : Fields} {Z : QDat X} {p : ℕ} (h : QDat.OverOnePrime Z p)
    {P P' : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Z.Q) (hP' : P' ∈ Z.Q) (h1 : ((p : ℕ) : 𝓞 X.E) ∈ P.asIdeal)
    (h2 : ((p : ℕ) : 𝓞 X.E) ∈ P'.asIdeal) {x : 𝓞 X.E} (hx : (x : X.E) ∈ X.Kq) (hc : IsCoprime x (X.conjO x))
    (hxP : x ∈ P.asIdeal) : X.conjO x ∉ P'.asIdeal := by
  intro hb
  have ha := (QDat.overOnePrime_iff Z p).1 h P hP P' hP' h1 h2 x hx hxP
  obtain ⟨u, v, huv⟩ := hc
  exact P'.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ add_mem (Ideal.mul_mem_left _ u ha) (Ideal.mul_mem_left _ v hb)))

theorem QDat.overOnePrime_of_card_le_one {X : Fields} (Z : QDat X) (p : ℕ) (h : Z.Q.card ≤ 1) : QDat.OverOnePrime Z p :=
  fun P hP P' hP' _ _ => by rw [Finset.card_le_one.1 h P hP P' hP']

theorem QDat.overOnePrime_of_hasBase {X : Fields} {Z : QDat X} {p : ℕ} (h : Z.HasBase p) (hf : X.f = 1) :
    QDat.OverOnePrime Z p := by
  classical
  intro P hP P' hP' h1 h2
  have h3 := h.all
  rw [hf] at h3
  rw [Finset.card_le_one.1 h3.le P (by simpa using ⟨hP, h1⟩) P' (by simpa using ⟨hP', h2⟩)]

example : GlobalTheory.Formalism.L2.Col.Dat = _root_.Formalism.L2.Col.Dat := rfl

example {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (u : Word) (j : ℕ) (τ : X.Tau) (i : Fin (R.N j)) :
    (W.lamTrue u j τ).w i + (j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) = (W.lamN u j τ).w i := by
  simp [Wts.lamTrue, shiftW]

example : (ofQ ![(3 : ℚ), 1]).w 0 = 3 := by
  have h : Antitone ![(3 : ℚ), 1] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  simp [ofQ, h]

example : divs (1 : ℤ) = ∅ := by
  ext P
  have h : {P : HeightOneSpectrum ℤ | (1 : ℤ) ∈ P.asIdeal} = ∅ :=
    Set.eq_empty_of_forall_notMem fun P hP => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hP)
  simp [divs, h]

end GlobalTheory.Formalism.L2.Col
