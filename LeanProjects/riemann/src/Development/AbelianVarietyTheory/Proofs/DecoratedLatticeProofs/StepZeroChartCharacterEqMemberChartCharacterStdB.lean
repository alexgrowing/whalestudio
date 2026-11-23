import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElementSameCharacterNearBad
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfMem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn

noncomputable section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.ChiZero

open GlobalTheory.Mem.Col2.MemChart

theorem redAt_eq_one_of_congAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n D : ℕ} (hD : 1 ≤ D)
    (P : Pl E) (w : St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (h : GlobalTheory.TwU.CongAt P D w.1) : redAt 1 P w = 1 := by
  obtain ⟨_, y, rfl⟩ := w
  have e : redAt 1 P ⟨frGL 1 y, ⟨y, rfl⟩⟩ = bc (resS F P) y := by
    show bc (resS F P) (pullFr 1 ⟨frGL 1 y, ⟨y, rfl⟩⟩) = _
    rw [pullFr_frGL]
  rw [e]
  have e1 : frGL 1 y = intGL F E n y := by simp [frGL]
  apply Units.ext
  ext a b
  obtain ⟨s, hs, hm⟩ := h a b
  have hq : ((Formalism.L2.Col.qOf P : ℕ) : E) ≠ 0 := by
    have : Formalism.L2.Col.qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have hqm : Ideal.Quotient.mk P.asIdeal ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.absNorm_mem _)
  have key : oToS F E s * ((y.1 - 1) a b) = oToS F E ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 E) ^ D * ⟨_, hm⟩ := by
    apply Subtype.ext
    have c1 : ∀ r : 𝓞 E, ((oToS F E r : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E (algebraMap (𝓞 E) E r) := fun _ => rfl
    have c2 : (((y.1 - 1) a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = ((frGL 1 y).1 - 1) a b := by
      rw [e1, Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    rw [Subring.coe_mul, Subring.coe_mul, SubmonoidClass.coe_pow, c1, c1, c2, ← map_pow, map_natCast]
    show _ = _ * (_ * (_ * _))
    rw [mul_left_comm, ← mul_assoc (iA F E (_ ^ D)), ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one, one_mul]
  have k2 := congrArg (resS F P) key
  rw [map_mul, map_mul, map_pow, resS_oToS, resS_oToS, hqm, zero_pow (by omega), zero_mul] at k2
  haveI := P.isPrime
  have k3 := (mul_eq_zero.1 k2).resolve_left (fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0))
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at k3
  show resS F P (y.1 a b) = (1 : Matrix (Fin n) (Fin n) (kP P)) a b
  rw [k3, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

theorem dia_of_base (hPr : (B.primes X).Ok) (u : B.Word) {n : ℕ} [NeZero n] {Q : Finset (HeightOneSpectrum (𝓞 B.fields.E))} {g k : GA B n}
    (k1 : ∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n)
    (k2 : ∀ w ∈ (B.primes X).vGs, bc (prV (E := B.host.E) (w.under (𝓞 B.host.F))) k = 1)
    (k3 : ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B n).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0))
    {p : DecoF B.fields.E n ((B.primes X).vT u) (B.primes X).vGs Q} (h : PtOf (g * k) p) :
    g ∈ UAd B.sp.cm n ∧ (decoOf ((B.primes X).vT u) (B.primes X).vGs g).dia (diaT (Pr := B.primes X) u) = p.deco := by
  refine GlobalTheory.T.decoratedLattice_diagonalBasePoint_mul _ _ B.sp.cm n _ _ Q g _ p _ h k1 k2 fun P r j hr => ?_
  have hu : IsUnit (Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u))) := by
    have h0 : Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u)) ≠ 0 := fun h0 =>
      (basePi_of_ok (GlobalTheory.Mem.FieldsLaws.fields_ok B) hPr u).conj_notMem P.2 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    exact @Ne.isUnit (Res P.1) _ _ h0
  have e : ((diaT (Pr := B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) =
      Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) := by
    unfold diaT
    rw [dif_pos hu]
    rfl
  rw [e]
  exact k3 P r j hr

abbrev levelZeroSubgroupOfWord (u : B.Word) : Subgroup (GA B (B.R.N 0)) :=
  levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp

abbrev typ0 (u : B.Word) : levelZeroSubgroupOfWord I u →* ℂˣ :=
  levTyp (F := B.host.F) (hc := B.sp.cm) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr)

set_option maxHeartbeats 1000000 in

theorem stepZeroChartLevel_mem_columnLevel_of_stdBase (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) {Ch : Type} {chOf : (I.stp u a 0).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N 0))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a 0).Cl → GA B (B.R.N 0)} {st : ∀ c, (I.stp u a 0).Stab c → GL (Fin (B.R.N 0)) B.host.E}
    {k : Ch → GA B (B.R.N 0)} (hR : I.Reads u a 0 chOf Lb U chi y st k) (c : (I.stp u a 0).Cl)
    (k2 : ∀ w ∈ (B.primes X).vGs, bc (prV (E := B.host.E) (w.under (𝓞 B.host.F))) (k (chOf c)) = 1)
    (x : U (chOf c)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) (hq : PtOf (y c * x.1 * k (chOf c)) q) :
    ∃ hx : x.1 ∈ levelZeroSubgroupOfWord I u, chi (chOf c) x = typ0 I u ⟨x.1, hx⟩ := by
  have hL := hI.idx_ok a
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  obtain ⟨κ, h1, h2, -⟩ := (hR.lev c x.1 q hq).1 x.2
  subst h2
  have hg := dia_of_base hPr u (hR.k_std _) k2 (hR.k_T _) (hR.pt c)
  have hx := dia_of_base hPr u (hR.k_std _) k2 (hR.k_T _) hq
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  obtain ⟨hJ, hr⟩ := red_of_act B.sp.cm (B.R.N 0) (diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) • _ = _
    rw [e1]
    rfl)
  have hm : κ.2.1.1 ∈ (colLev I.Ch 0).grp := hΛ c.1 ▸ κ.2.1.2
  have hxU : x.1 ∈ levelZeroSubgroupOfWord I u := (mem_levU _ _ _ _ _).2 ⟨hJ, by rw [hr]; exact inv_mem hm⟩
  refine ⟨hxU, Units.ext ((hR.chr c x κ h1 hq).trans (Eq.symm ?_))⟩
  have e2 : Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x.1, hxU⟩ = (⟨κ.2.1.1, hm⟩ : (colLev I.Ch 0).grp)⁻¹ :=
    Subtype.ext hr
  show ((Units.map B.embLL.toMonoidHom ((colLev I.Ch 0).chr (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x.1, hxU⟩)))⁻¹ : ℂˣ).1 =
    B.embLL (((Chart0.lvG I a c.1).chr κ.2.1 * (Chart0.lvQ I a c.1).chr κ.2.2 : B.LLˣ) : B.LL)
  rw [e2, StepZero.chr_eq_one (hΘ c.1), mul_one, StepZero.chr_congr (hΛ c.1), map_inv, map_inv, inv_inv]
  rfl

theorem stepZeroColumnLevelType_eq_of_congruent_typePrimes (u : B.Word) (x x' : levelZeroSubgroupOfWord I u)
    (h : ∀ w ∈ (B.primes X).vGs, ∃ D, 1 ≤ D ∧ GlobalTheory.TwU.CongAt (F := B.host.F) (E := B.host.E) w D (x.1⁻¹ * x'.1)) :
    typ0 I u x = typ0 I u x' := by
  have e : Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ (x⁻¹ * x') = 1 := by
    apply Subtype.ext
    funext w
    obtain ⟨D, hD, hc⟩ := h w.1 w.2
    exact redAt_eq_one_of_congAt hD w.1 ⟨(x⁻¹ * x').1, congruence_subgroup_le_stabilizer _ _ _ (unipotentLevel_le_mirabolicLevel _ _ _ _ _ (x⁻¹ * x').2)⟩ hc
  have e2 : typ0 I u (x⁻¹ * x') = 1 := by
    show (((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr) (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ (x⁻¹ * x')))⁻¹ = 1
    rw [e, map_one, inv_one]
  rw [map_mul, map_inv, inv_mul_eq_one] at e2
  exact e2

end GlobalTheory.Fam.ChiZero
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam
open GlobalTheory.Fam.ChiZero GlobalTheory.Mem.Col2.MemChart

set_option maxHeartbeats 4000000 in

theorem chi_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ (x : (A.K 0 (Nat.zero_le _) β).lev.U) (x' : (C.forms u).to0.cls0.lev.U), x.1 = x'.1 → (A.K 0 (Nat.zero_le _) β).lev.chi x = (C.forms u).to0.cls0.lev.chi x' := by
  intro B X I hI hP l Z C hC u a Ch A hA β hβ x x' hxx
  have hPr := l.pr
  haveI : NeZero (B.R.N 0) := ⟨(B.R.N_pos 0).ne'⟩
  obtain ⟨c, rfl⟩ := hA.chOf_onto 0 (Nat.zero_le _) β
  have hR := hA.reads 0 (Nat.zero_le _)
  obtain ⟨n, hn, hfin⟩ := hA.fin 0 (Nat.zero_le _) (A.chOf 0 c)
  obtain ⟨x₁, e₁, ⟨q, hq⟩, hcg⟩ := GlobalTheory.Mem.Col2.AdT.LevelElt.exists_level_elt I hI hP l Z u a 0 (Nat.zero_le _) (A.bad 0) (Ch 0) (A.chOf 0)
    (A.K 0 (Nat.zero_le _)) (A.kb 0) hR c ⟨n, hn, fun κ _ => hfin κ⟩ x
  obtain ⟨hx₁, f₁⟩ := stepZeroChartLevel_mem_columnLevel_of_stdBase I hI hPr u a hR c (fun w hw => by
    rw [hβ]
    exact (kStd_spec hPr u _).2.1 _ fun hT => Formalism.L2.Col.rls_T_notUnder hPr u _ hT ⟨w, hw, rfl⟩) x₁ q hq
  obtain ⟨k, hR'⟩ := (hC u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  obtain ⟨c', -⟩ := hR'.onto ()
  have hg1 : gramN (I.rec7 l Z) 0 (Nat.zero_le _) = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 (Nat.zero_le _)).1
  have eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := by rw [hg1]; rfl
  let yc : TC.GA B (B.R.N 0) := (((C.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).y c').1
  let xg : TC.GA B (B.R.N 0) := x'.1
  have hxg : xg ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := eU ▸ (((C.forms u).to0.cls0.lev.U_eq x'.1).1 x'.2).1
  have hyc : yc ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := eU ▸ (((C.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).y c').2
  obtain ⟨p0, hp0, -⟩ := hR'.k_std ()
  have hk : k () ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := hp0.uni
  obtain ⟨q', hq'⟩ : ∃ q' : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup I.mu0) u 0, TC.PtOf (yc * xg * k ()) q' :=
    GlobalTheory.Mem.Col2.ChiFinTop.exists_isPtOf_of_mem B.sp.cm I.twistPrimes_reference_tuple_eq_empty (mul_mem (mul_mem hyc hxg) hk)
  obtain ⟨hx', f'⟩ := stepZeroChartLevel_mem_columnLevel_of_stdBase I hI hPr u I.mu0 hR' c' (fun w hw =>
    hR'.k_off () _ (fun hT => Formalism.L2.Col.rls_T_notUnder hPr u _ hT ⟨w, hw, rfl⟩)
      (fun ⟨P, hP, _⟩ => by rw [I.twistPrimes_reference_tuple_eq_empty] at hP; exact Finset.notMem_empty _ hP) (Or.inl rfl)) x' q' hq'
  refine e₁.symm.trans (f₁.trans (Eq.trans (Eq.symm ?_) f'.symm))
  refine stepZeroColumnLevelType_eq_of_congruent_typePrimes I u _ _ fun w hw => ?_
  have hw' : w ∈ GlobalTheory.Mem.Col2.AdT.SBof I a := Finset.mem_union_left _ hw
  refine ⟨(I.cst a).D ⟨w, hw'⟩, (hI.idx_ok a).cst_ok.D_pos _, ?_⟩
  have h1 := hcg ⟨w, hw'⟩
  rw [(GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hI l Z a (B.R.N 0) 0 ⟨w, hw'⟩ x.1).1, hxx] at h1
  exact h1

end GlobalTheory.Fam
end

end
