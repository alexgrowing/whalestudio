import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFrameCharacterMulMovedPoint
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.ReadBad

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem int_of_pts {g m : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {h : GLG E n SG} {c : GLQ E n Q}
    (h1 : IsPtOf hc g p) (h2 : IsPtOf hc (g * m) (((1, h, c) : UF E n × GLG E n SG × GLQ E n Q) • p)) (r s : Fin n) :
    (m : Matrix (Fin n) (Fin n) (AfE F E)) r s ∈ Formalism.L2.Herm.intAf F E ∧
      ((m⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s ∈ Formalism.L2.Herm.intAf F E := by
  have L1 := h1.lat
  have L2 := h2.lat
  have hN : (((1, h, c) : UF E n × GLG E n SG × GLQ E n Q) • p).deco.1.N = p.deco.1.N := LevRead.smul_N p h c
  rw [hN] at L2
  have hstd : ∀ z : Fin n → AfE F E, z ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) ↔ ∀ i, z i ∈ Formalism.L2.Herm.intAf F E :=
    fun z => Formalism.L2.Col.mem_latS_std z
  have he : (Pi.single s 1 : Fin n → AfE F E) ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) := (hstd _).2 fun i => by
    rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  constructor
  · have hx : ((g * m : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single s 1 ∈
        Formalism.L2.Herm.hatL (F := F) p.deco.1.N := by
      refine (L2 _).2 ?_
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact he
    have e : ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        (((g * m : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single s 1) =
        (m : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single s 1 := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]
    have := (hstd _).1 (e ▸ (L1 _).1 hx) r
    simpa [Matrix.mulVec_single_one] using this
  · have hx : ((g : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single s 1 ∈
        Formalism.L2.Herm.hatL (F := F) p.deco.1.N := by
      refine (L1 _).2 ?_
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact he
    have e : (((g * m)⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        (((g : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single s 1) =
        ((m⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single s 1 := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_mul_cancel_right]
    have := (hstd _).1 (e ▸ (L2 _).1 hx) r
    simpa [Matrix.mulVec_single_one] using this

end Gen

end GlobalTheory.Mem.Col2.AdT.ReadBad

namespace GlobalTheory.Mem.Col2.AdT.ReadBad

section Gen2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem hasRes_redP {P : HeightOneSpectrum (𝓞 E)} {y : E} (hy : Formalism.L2.Col.IntAt P y) :
    HasRes P (algebraMap E (P.adicCompletion E) y) (Formalism.L2.Col.redP P y) := by
  obtain ⟨r, s, hs, h⟩ := hy
  have hsp := Formalism.L2.Col.reduction_spec P hs h
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  obtain ⟨t, ht⟩ := Ideal.Quotient.exists_inv hs0
  obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
  refine ⟨t' * r, ?_, ?_⟩
  · rw [map_mul, ← hsp, ← mul_assoc, mul_comm (Ideal.Quotient.mk P.asIdeal t'), ht, one_mul]
  · have hvs : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact HeightOneSpectrum.intValuation_eq_one_iff.2 hs
    have hvy : P.valuation E y ≤ 1 := by
      have e := congrArg (P.valuation E) h
      rw [map_mul, hvs, one_mul] at e
      rw [e]
      exact P.valuation_le_one r
    have h1 : 1 - t' * s ∈ P.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, mul_comm, ht, sub_self]
    have e : y - algebraMap (𝓞 E) E (t' * r) = y * algebraMap (𝓞 E) E (1 - t' * s) := by
      simp only [map_mul, map_sub, map_one]
      rw [← h]
      ring
    rw [← map_sub, valued_algebraMap, e, map_mul]
    exact (mul_le_of_le_one_left' hvy).trans_lt ((HeightOneSpectrum.valuation_lt_one_iff_mem P _).2 h1)

theorem val_sub_lt_of_hasRes {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} {t0 : 𝓞 E}
    (h : HasRes P z (Ideal.Quotient.mk P.asIdeal t0)) :
    Valued.v (z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E t0)) < 1 := by
  obtain ⟨t, ht, hv⟩ := h
  have h0 : t - t0 ∈ P.asIdeal := Ideal.Quotient.eq.1 ht
  have e : z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E t0) =
      (z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E t)) + algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (t - t0)) := by
    simp only [map_sub]
    ring
  rw [e]
  refine Valuation.map_add_lt _ hv ?_
  rw [valued_algebraMap]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem P _).2 h0

theorem le_exp_neg_one {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} (h : Valued.v z < 1) :
    Valued.v z ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : Valued.v z = 0
  · rw [h0]; exact zero_le'
  rw [← WithZero.exp_log h0] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem val_sub_one_lt {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} {r s : Fin n}
    (h : HasRes P z ((1 : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) r s)) :
    Valued.v (z - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) < 1 := by
  by_cases hrs : r = s
  · subst hrs
    rw [Matrix.one_apply_eq] at h ⊢
    have := val_sub_lt_of_hasRes (t0 := 1) (by simpa using h)
    simpa using this
  · rw [Matrix.one_apply_ne hrs] at h ⊢
    have := val_sub_lt_of_hasRes (t0 := 0) (by simpa using h)
    simpa using this

theorem isRed_ratA {P : HeightOneSpectrum (𝓞 E)} {G : Sp E n ≃ₗ[E] Sp E n} (hG : G ∈ Formalism.L2.Col.GLint E n P)
    {A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (hA : ∀ x ∈ Formalism.L2.Col.stdAt E n P, Formalism.L2.Col.redV P (G x) = A.mulVec (Formalism.L2.Col.redV P x)) :
    LevRead.IsRed P (GlobalTheory.TwU.ratA F (toGLm E n G)) A := by
  intro i j
  have he : (Pi.single j 1 : Sp E n) ∈ Formalism.L2.Col.stdAt E n P := by
    refine Formalism.L2.Col.le_locP P _ ((mem_stdLat _).2 fun l => ?_)
    rw [Pi.single_apply]
    split_ifs
    exacts [⟨1, map_one _⟩, ⟨0, map_zero _⟩]
  have hGe : G (Pi.single j 1) ∈ Formalism.L2.Col.stdAt E n P := (hG (Pi.single j 1)).2 he
  have hint : Formalism.L2.Col.IntAt P (G (Pi.single j 1) i) := by
    obtain ⟨s, hs, hsx⟩ := (Formalism.L2.Col.mem_locP P _ _).1 hGe
    obtain ⟨r, hr⟩ := (mem_stdLat _).1 hsx i
    refine ⟨r, s, hs, ?_⟩
    rw [hr]
    simp [Algebra.smul_def]
  have hred : Formalism.L2.Col.redV P (Pi.single j 1 : Sp E n) = Pi.single j 1 := by
    funext l
    show Formalism.L2.Col.redP P _ = _
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · simpa using Formalism.L2.Col.reduction_coe P 1
    · simpa using Formalism.L2.Col.reduction_coe P 0
  have e1 := congrFun (hA _ he) i
  rw [hred, Matrix.mulVec_single_one] at e1
  have e2 : (((GlobalTheory.TwU.ratA F (toGLm E n G) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (G (Pi.single j 1) i) := by
    rw [← GlobalTheory.Mem.Col2.TopCh.toGLm_entry]
    rfl
  rw [e2, adAt_inclE]
  have := hasRes_redP hint
  show HasRes P _ (A i j)
  convert this using 1
  exact (e1.trans (Matrix.transpose_apply A j i)).symm

end Gen2

end GlobalTheory.Mem.Col2.AdT.ReadBad

namespace GlobalTheory.Mem.Col2.AdT.ReadBad

section Gen3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem rhoP_ratA (P : HeightOneSpectrum (𝓞 E)) (G : ↥(Formalism.L2.Col.GLint E n P)) :
    TopCh.rhoP F P (GlobalTheory.TwU.ratA F (toGLm E n G.1)) = TopCh.iotaP P G := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show adAt F P (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) _) = _
  rw [adAt_inclE]
  rfl

theorem core {g m : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {h : GLG E n SG} {c : GLQ E n Q}
    (h1 : IsPtOf hc g p) (h2 : IsPtOf hc (g * m) (((1, h, c) : UF E n × GLG E n SG × GLQ E n Q) • p))
    (P : HeightOneSpectrum (𝓞 E)) :
    (∀ r s, IntAtA (F := F) P ((m : Matrix (Fin n) (Fin n) (AfE F E)) r s)) ∧
    (∀ r s, IntAtA (F := F) P (((m⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)) ∧
    (∀ (hP : P ∈ SG) (G : Sp E n ≃ₗ[E] Sp E n), G ∈ Formalism.L2.Col.GLint E n P →
      (∀ x ∈ Formalism.L2.Col.stdAt E n P, Formalism.L2.Col.redV P (G x) = ((h ⟨P, hP⟩)⁻¹ : GL (Fin n) (𝓞 E ⧸ P.asIdeal)).1.mulVec (Formalism.L2.Col.redV P x)) →
      ∀ r s, Valued.v (adAt F P (((m⁻¹ * GlobalTheory.TwU.ratA F (toGLm E n G) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) -
        (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-1 : ℤ)) ∧
    (∀ (hP : P ∈ Q) (N : ℕ) r s, Valued.v (adAt F P (((m⁻¹ * GlobalTheory.TwU.ratA F (toGLm E n ((c ⟨P, hP⟩)⁻¹).1) : GL (Fin n) (AfE F E)) :
        Matrix (Fin n) (Fin n) (AfE F E)) r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ))) := by
  have hI : ∀ a ∈ Formalism.L2.Herm.intAf F E, IntAtA (F := F) P a := fun a ha =>
    ⟨1, Formalism.L2.Col.one_notMem P, by simpa using ha⟩
  have hV : ∀ a ∈ Formalism.L2.Herm.intAf F E, Valued.v (adAt F P a) ≤ 1 := fun a ha =>
    (mem_rInt_iff F E a).1 ha P
  refine ⟨fun r s => hI _ (int_of_pts h1 h2 r s).1, fun r s => hI _ (int_of_pts h1 h2 r s).2, ?_, ?_⟩
  · intro hP G hG hred r s
    obtain ⟨A, hA⟩ := LevRead.exists_isRed (P := P) (x := m⁻¹) (fun i j => hV _ (int_of_pts h1 h2 i j).2)
      (fun i j => by rw [inv_inv]; exact hV _ (int_of_pts h1 h2 i j).1)
    have h2' : IsPtOf hc (g * (m⁻¹)⁻¹) (((1, h, c) : UF E n × GLG E n SG × GLQ E n Q) • p) := by rwa [inv_inv]
    have hAe := LevRead.eq_red h1 h2' ⟨P, hP⟩ hA
    have hB := isRed_ratA (F := F) hG hred
    have hC := hA.mul hB
    rw [hAe, ← Units.val_mul, mul_inv_cancel, Units.val_one] at hC
    exact le_exp_neg_one (val_sub_one_lt (hC r s))
  · intro hP N r s
    have e0 := TopCh.rhoT_eq_iota (k := 1) (t := 1) (y := g) (x := m) h c (fun _ => map_one _) (by simpa using h1)
      (by simpa using h2) ⟨P, hP⟩
    have e1 : TopCh.rhoP F P m = TopCh.iotaP P ((c ⟨P, hP⟩)⁻¹) := by simpa [TopCh.rhoT] using e0
    have e2 : TopCh.rhoP F P (m⁻¹ * GlobalTheory.TwU.ratA F (toGLm E n ((c ⟨P, hP⟩)⁻¹).1)) = 1 := by
      rw [map_mul, map_inv, e1, rhoP_ratA P ((c ⟨P, hP⟩)⁻¹), inv_mul_cancel]
    have e3 : adAt F P (((m⁻¹ * GlobalTheory.TwU.ratA F (toGLm E n ((c ⟨P, hP⟩)⁻¹).1) : GL (Fin n) (AfE F E)) :
        Matrix (Fin n) (Fin n) (AfE F E)) r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
      have := congrArg (fun x : GL (Fin n) (P.adicCompletion E) => (x : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) e2
      exact this.trans (congrArg (fun M : Matrix (Fin n) (Fin n) (P.adicCompletion E) => M r s) Units.val_one)
    rw [e3, sub_self, map_zero]
    exact zero_le'

end Gen3

end GlobalTheory.Mem.Col2.AdT.ReadBad

namespace GlobalTheory.Mem.Col2.AdT.ReadBad

set_option maxHeartbeats 4000000 in

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (x : GA B (B.R.N i)) (κ' : (I.stp u a i).G c.1), (I.stp u a i).gam c.1 κ' = 1 → PtOf ((show GA B (B.R.N i) from ((K (chOf c)).y ⟨c, rfl⟩).1) * x * k (chOf c)) ((I.stp u a i).act c.1 κ' ((I.stp u a i).rep c)).1.1 → ∀ P : SBof I a, (∀ r s, IntAtA (F := B.host.F) (show HeightOneSpectrum (𝓞 B.host.E) from GlobalTheory.TwU.seamP (sm I l Z) P.1) ((((k (chOf c))⁻¹ * x * k (chOf c) : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s)) ∧ (∀ r s, IntAtA (F := B.host.F) (show HeightOneSpectrum (𝓞 B.host.E) from GlobalTheory.TwU.seamP (sm I l Z) P.1) (((((k (chOf c))⁻¹ * x * k (chOf c))⁻¹ : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s)) ∧ ∀ g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i), LiftsInv I κ' P g → GlobalTheory.TwU.NearAt (show HeightOneSpectrum (𝓞 B.host.E) from GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((k (chOf c))⁻¹ * x * k (chOf c)) (GlobalTheory.TwU.seamGL (sm I l Z) g) := by
  intro B X I hOk l Z u a i hi bad Ch chOf K k hR c x κ' hγ hpt P
  have hpt0 := hR.pt c
  have hd : Disjoint (B.primes X).vGs (I.Q a) := Finset.disjoint_right.2 (fun {P} hP => Q_notMem_of_ok hOk a P hP)
  have hp1 := IsPtOf.of_extTo (I.Q_subset_SQ a) hd hpt0
  have hγ' : toGLm B.fields.E (B.R.N i) κ'.1.1 = 1 := hγ
  have hκ1 : κ'.1 = 1 := Subtype.ext ((MulEquiv.map_eq_one_iff _).1 hγ')
  have hinc : FrmG.incl _ _ κ' = ((1, κ'.2.1.1, κ'.2.2.1) : UF B.fields.E (B.R.N i) × GLG B.fields.E (B.R.N i) (B.primes X).vGs ×
      GLQ B.fields.E (B.R.N i) (I.Q a)) := by
    show (κ'.1, κ'.2.1.1, κ'.2.2.1) = _
    rw [hκ1]
  have hp2 : IsPtOf B.sp.cm ((show GA B (B.R.N i) from ((K (chOf c)).y ⟨c, rfl⟩).1) * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)))
      (((1, κ'.2.1.1, κ'.2.2.1) : UF B.fields.E (B.R.N i) × GLG B.fields.E (B.R.N i) (B.primes X).vGs ×
        GLQ B.fields.E (B.R.N i) (I.Q a)) • ((I.stp u a i).rep c).1.1) := by
    rw [← hinc, show ∀ yy : GA B (B.R.N i), yy * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) = yy * x * k (chOf c) from
      fun yy => by group]
    exact hpt
  obtain ⟨c1, c2, c3, c4⟩ := ReadBad.core hp1 hp2 P.1
  refine ⟨c1, c2, fun g hL => ?_⟩
  have eG : GlobalTheory.TwU.seamGL (sm I l Z) g = toGLm B.fields.E (B.R.N i) g := Units.ext (Matrix.ext fun _ _ => rfl)
  unfold GlobalTheory.TwU.NearAt
  rw [eG]
  refine (GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hOk l Z a (B.R.N i) ((I.cst a).D P) P
    (show GL (Fin (B.R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E) from
      ((k (chOf c))⁻¹ * x * k (chOf c))⁻¹ * GlobalTheory.TwU.ratA B.host.F (toGLm B.fields.E (B.R.N i) g))).2.2.2 ?_
  intro r s
  classical
  rcases Finset.mem_union.1 P.2 with hG | hQ
  · rw [(hOk.idx_ok a).depthG P hG]
    have := c3 hG g hL.1 (hL.2.1 hG) r s
    simpa using this
  · have e := hL.2.2 hQ
    subst e
    exact c4 hQ _ r s

end GlobalTheory.Mem.Col2.AdT.ReadBad
