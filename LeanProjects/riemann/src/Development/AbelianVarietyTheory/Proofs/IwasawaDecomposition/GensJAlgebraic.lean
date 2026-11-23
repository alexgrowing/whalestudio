import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegreeEqTotDeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColInJetsIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmInverseHalfDifferentMulRelativeDifferent

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.L2.Col (qOf rowSG cAof cBof IsSel QE)

namespace GlobalTheory.Mem.Top.ReW

open GlobalTheory.Mem.Col2.JetEx

def stepSetJ (P : Pre) (J : AmbIn P.host) (χ : HChar P.host.E)
    (k : P.Word × ℕ × Finset (HeightOneSpectrum (𝓞 P.host.E)) × Finset (HeightOneSpectrum (𝓞 P.host.E))) : Set ℂ :=
  jetSet (hostAmb J (chiId χ)) (P.R.N k.2.1) (P.R.N (k.2.1 + 1)) k.2.2.1
    ((∏ Q ∈ k.2.2.2, qOf Q) ^ (P.R.m + 1) * (P.T k.1 * (∏ Q ∈ k.2.2.2, qOf Q) ^ (P.R.m + 1))) (totDeg P k.1 k.2.1)

def allSetJ (P : Pre) (J : AmbIn P.host) (χ : HChar P.host.E) (Ξ : Set (HChar P.host.E)) : Set ℂ :=
  ⋃ k ∈ {k : P.Word × ℕ × Finset (HeightOneSpectrum (𝓞 P.host.E)) × Finset (HeightOneSpectrum (𝓞 P.host.E)) |
      (k.2.1 < P.R.m ∧ (∀ Q ∈ k.2.2.1, Q ∈ badP P Ξ) ∧ ∀ Q ∈ k.2.2.2, Q ∈ badP P Ξ) ∧ FinAlg (stepSetJ P J χ k)}, stepSetJ P J χ k

theorem finAlg_allSetJ (P : Pre) (J : AmbIn P.host) (χ : HChar P.host.E) {Ξ : Set (HChar P.host.E)} (h : Ξ.Finite) :
    FinAlg (allSetJ P J χ Ξ) := by
  have hb := badPrimes_finite₂ P h
  have hs : {S : Finset (HeightOneSpectrum (𝓞 P.host.E)) | ∀ Q ∈ S, Q ∈ badP P Ξ}.Finite :=
    hb.toFinset.powerset.finite_toSet.subset fun S hS =>
      Finset.mem_coe.2 (Finset.mem_powerset.2 fun Q hQ => hb.mem_toFinset.2 (hS Q hQ))
  refine finAlg_biUnion ?_ fun k hk => hk.2
  exact (Set.finite_univ.prod ((Set.finite_Iio P.R.m).prod (hs.prod hs))).subset fun k hk => ⟨trivial, hk.1⟩

open Classical in

def gensJ (P : Pre) (J : AmbIn P.host) (χ : HChar P.host.E) (Ξ : Set (HChar P.host.E)) : Finset ℂ :=
  if h : FinAlg (allSetJ P J χ Ξ) then h.choose else ∅

theorem gensJ_algebraic (P : Pre) (J : AmbIn P.host) (χ : HChar P.host.E) (Ξ : Set (HChar P.host.E)) :
    ∀ z ∈ gensJ P J χ Ξ, IsAlgebraic ℚ z := by
  unfold gensJ
  split_ifs with h
  · exact h.choose_spec.1
  · simp

theorem allSetJ_subset (P : Pre) (J : AmbIn P.host) (χ : HChar P.host.E) {Ξ : Set (HChar P.host.E)} (h : Ξ.Finite)
    {K : Subfield ℂ} (hK : ∀ z ∈ gensJ P J χ Ξ, z ∈ K) : allSetJ P J χ Ξ ⊆ K := by
  have h1 := finAlg_allSetJ P J χ h
  rw [gensJ, dif_pos h1] at hK
  exact h1.choose_spec.2.trans (Subfield.closure_le.2 hK)

theorem jetsIn_of_isTw {B : Base} {X : PreX B.toPre} (hL : StagesInhab.HasLetters B.toPre) {I : ColIn B X} (h : I.Ok)
    (ht : TC.IsTw I) (hK : ∀ z ∈ gensJ B.toPre I.J I.C.chiPsi (Set.range I.xi), z ∈ B.embLL.fieldRange) : I.JetsIn := by
  have hall := allSetJ_subset B.toPre I.J I.C.chiPsi (Set.finite_range I.xi) hK
  refine I.jetsIn_iff.2 fun a u i hi N N' c x hx e he => ?_
  have hM : I.modulus a u = (∏ Q ∈ rowSG (B.primes X) I.sel (I.tup a), qOf Q) ^ (B.R.m + 1) *
      (B.T u * (∏ Q ∈ rowSG (B.primes X) I.sel (I.tup a), qOf Q) ^ (B.R.m + 1)) := by
    unfold ColIn.modulus cAof cBof
    rw [ht.cst_eq a, Finset.prod_coe_sort _ qOf]
    rfl
  have hS : stepSetJ B.toPre I.J I.C.chiPsi (u, i, I.Sb a u, rowSG (B.primes X) I.sel (I.tup a)) =
      jetSet I.A (B.R.N i) (B.R.N (i + 1)) (I.Sb a u) (I.modulus a u) (totDeg B.toPre u i) := by
    rw [hM, ColIn.A]
    exact (jetSet_amb B _ _ _ _ _ _ _).symm
  have hpos : 0 < I.modulus a u := by
    rw [hM]
    have := Finset.prod_pos fun Q (_ : Q ∈ rowSG (B.primes X) I.sel (I.tup a)) =>
      Nat.pos_of_ne_zero (by simpa using qPow_ne_zero Q 1 : qOf Q ≠ 0)
    have := (B.T_prime u).pos
    positivity
  refine hall (Set.mem_iUnion₂.2 ⟨(u, i, I.Sb a u, rowSG (B.primes X) I.sel (I.tup a)),
    ⟨⟨hi, Sb_subset h a u, rowSG_subset h a⟩, ?_⟩, ?_⟩)
  · rw [hS]
    exact finAlg_step hL h a u _ _ _ _ hpos
  · rw [hS]
    exact ⟨N, N', c, x, e, hx, degree_eq_totDeg B u i e he, rfl⟩

end GlobalTheory.Mem.Top.ReW

end

noncomputable section

open Formalism.L2.Col (qOf rowSG cAof cBof IsSel QE)

namespace GlobalTheory.Mem.Top.ReW

open GlobalTheory.Mem.Col2.InEx

theorem exists_bound : ∃ S : ∀ P : Pre, AmbIn P.host → Fr P → Set (HChar P.host.E) → Finset ℂ,
    (∀ P J g Ξ, ∀ z ∈ S P J g Ξ, IsAlgebraic ℚ z) ∧
    ∀ (B : Base) (X : PreX B.toPre) (f : Fr B.toPre) (T : TwDat B)
      (sel : HeightOneSpectrum (𝓞 B.fields.F) → HeightOneSpectrum (𝓞 B.fields.E)) (J : AmbIn B.host),
      (letI := B.host.cmStar; DiagSpaces B.sp) → (∀ u, (B.duStar u : ℝ) = duStarOf B.host (B.hcW u)) →
      StagesInhab.HasLetters B.toPre → Oriented X f.P → IsSel B.fields sel → J.Ok →
      (∀ z ∈ S B.toPre J f (T.set f), ∃ x : B.LL, B.embLL x = z) →
      ∃ I : ColIn B X, I.Ok ∧ TC.IsTw I ∧ I.JetsIn ∧ I.C = f ∧ I.S = avoid B.toPre ∧ Set.range I.xi = T.set f ∧
        I.sel = sel ∧ I.J = J ∧
        (∀ a P, ∃ z : B.LL, B.embLL z = (((I.xi a).val P : ℂˣ) : ℂ)) ∧
        (∀ a, ∀ P ∈ I.Q a, ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (𝓞 B.fields.E ⧸ P.asIdeal))) ∧
        GlobalTheory.Mem.Per.FieldOK B.host B.embLL B.embE := by
  classical
  choose M hM _ _ m1 m2 _ _ _ _ using fun (B : Pre) (f : Top.Fr B) =>
    FrameVal.frame_values B.R B.host _ f fun j τ => (B.hc τ).e_int j
  choose α hα gα using fun (B : Pre) (f : Top.Fr B) => @DatHecke.exists_gen (M B f) (hM B f)
  choose M' hM' _ hok using fun B : Pre => PerField.exists_fieldOK B.R B.host ⊥ inferInstance
  choose β hβ gβ using fun B : Pre => @DatHecke.exists_gen (M' B) (hM' B)
  choose r hr using fun q : ℕ => IsAlgClosed.exists_pow_nat_eq (q : ℂ) (n := 2) two_pos
  choose Z hZ gZ using fun (B : Pre) (Ξ : Set (HChar B.host.E)) => exists_holds (2 * B.R.m) Ξ
  refine ⟨fun P J g Ξ => insert (α P g) (insert (β P) (Z P Ξ ∪ (Finset.univ.image fun k => r (P.host.g k)) ∪
    gensJ P J g.chiPsi Ξ)), ?_, ?_⟩
  · intro P J g Ξ z hz
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with rfl | rfl | ((h | ⟨k, rfl⟩) | h)
    · exact hα P g
    · exact hβ P
    · exact hZ P Ξ z h
    · exact IsAlgebraic.of_pow two_pos (by rw [hr]; exact isAlgebraic_natCast _)
    · exact gensJ_algebraic P J _ Ξ z h
  intro B X f T sel J hsp hdu hL hX hsel hJ hS
  have hα' := hS _ (Finset.mem_insert_self _ _)
  have hβ' := hS _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hZ' : ∀ z ∈ Z B.toPre (T.set f), ∃ x, B.embLL x = z := fun z hz => hS z (by simp [hz])
  have hr' : ∀ k, ∃ x, B.embLL x = r (B.host.g k) := fun k => hS _ (by simp)
  have hG' : ∀ z ∈ gensJ B.toPre J f.chiPsi (T.set f), ∃ x, B.embLL x = z := fun z hz => hS z (by simp [hz])
  have i1 := gα B.toPre f B.LL B.embLL hα'
  have hf := (TwFin.tw_fin B f T).1
  have ht := isTwist_of_mem_set B f T
  have hold : ∀ ξ ∈ T.set f, Holds B.embLL (2 * B.R.m) ξ := fun ξ hξ => gZ B.toPre _ hf B.LL B.embLL hZ' ξ hξ (ht ξ hξ).1
  obtain ⟨I0, h0, e1, e2, e3, e4, e5, hc⟩ := exists_colIn B X f hX hsp hdu (avoid B.toPre)
    (fun u => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Exists.intro u rfl))))), B.T_ne_pde u⟩)
    (fun i => ⟨Or.inr (Or.inl (Exists.intro i rfl)), (B.host.pde_ne_g i).1.symm, (B.host.pde_ne_g i).2.symm⟩)
    (fun _ hp h => mem_avoid_of_dvd _ hp h)
    _ hf (.inl (.inl rfl)) (.inl (.inr (.inl rfl))) (.inl (.inr (.inr rfl))) ht hold
    (fun j => valuesIn_of (m1 _ f j) _ i1) (valuesIn_of (m2 _ f) _ i1) (fun i => by
      obtain ⟨s, hs⟩ := hr' i
      exact ⟨s, B.embLL.injective (by rw [map_pow, hs, hr, map_natCast])⟩) sel hsel J hJ
  have hD : TC.Deep I0 := fun a P hP => by rw [(hc a).2.2.2 P hP]
  have hI : (TC.canon I0).Ok := TC.canon_ok h0 hD
  refine ⟨(TC.canon I0), hI, TC.canon_isTw I0, jetsIn_of_isTw hL hI (TC.canon_isTw I0) fun z hz => ?_, e1, e2, e3, e4, e5,
    fun a P => ?_, fun a P hP => ?_, hok B.toPre B.LL B.embLL B.embE B.embE_φ₀ (gβ B.toPre B.LL B.embLL hβ')⟩
  · have hz' : z ∈ gensJ B.toPre J f.chiPsi (T.set f) := by
      rw [show (TC.canon I0).J = J from e5, show (TC.canon I0).C = f from e1,
        show Set.range (TC.canon I0).xi = T.set f from e3] at hz
      exact hz
    exact RingHom.mem_fieldRange.2 (hG' z hz')
  · have hx : I0.xi a ∈ T.set f := e3 ▸ ⟨a, rfl⟩
    exact RingHom.mem_range.1 ((hold _ hx).1 _)
  · have hx : I0.xi a ∈ T.set f := e3 ▸ ⟨a, rfl⟩
    have htw : Chr.IsTwist B.host I0.S (I0.xi a) := e2 ▸ ht _ hx
    obtain ⟨P', hP', hn⟩ := exists_ram_of_mem_QE B h0.sel_ok (I0.tup a) htw (h0.xi_reads a) hP
    obtain ⟨ζ, hζ⟩ := ((hold _ hx).2 P' hP').2
    have hm := B.R.two_le_m
    have hq : 0 < Ideal.absNorm P'.asIdeal := Nat.pos_of_ne_zero fun h => P'.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    refine ⟨ζ ^ (Ideal.absNorm P'.asIdeal ^ (2 * B.R.m - 1)), ?_⟩
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hn]
    exact hζ.pow (pow_pos hq _) (by rw [← pow_succ]; congr 1; omega)

end GlobalTheory.Mem.Top.ReW

end

noncomputable section

namespace GlobalTheory.Mem.Top.ReW

open GlobalTheory.Mem.Col2.InEx

theorem valuesIn_lift {L : Type} [Field L] [NumberField L] {χ : HChar L} {s : ℝ} {C C' : Type} [Field C] [Field C']
    {σ : C →+* ℂ} {σ' : C' →+* ℂ} (h : χ.ValuesIn s σ) (hσ : ∀ y, ∃ x, σ' x = σ y) : χ.ValuesIn s σ' := fun v hv => by
  obtain ⟨y, hy⟩ := h v hv
  obtain ⟨x, hx⟩ := hσ y
  exact ⟨x, hx.trans hy⟩

theorem extend_pinned : EvG fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre →
    Pinned K B f T w → ∃ (A : ℕ → Finset ℕ) (S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ),
    (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) ∧ ∀ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl B B' → HEq f' f →
    T'.Avoids A → (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) → ∃ w' : ColW B' f' T',
    Pinned K B' f' T' w' ∧ HEq w'.px w.px ∧ HEq w'.I.sel w.I.sel ∧ HEq w'.I.J w.I.J ∧ HEq w'.δ w.δ := by
  classical
  obtain ⟨S, hSa, hS⟩ := exists_bound
  refine evG_all fun K B f T w hO ⟨cp⟩ => ?_
  refine ⟨fun _ => ∅, fun P g Ξ => if h : P = B.toPre then S P (h ▸ w.I.J) g Ξ else ∅, fun P g Ξ z hz => ?_, ?_⟩
  · dsimp only at hz
    by_cases h : P = B.toPre
    · rw [dif_pos h] at hz
      exact hSa _ _ _ _ z hz
    · rw [dif_neg h] at hz
      simp at hz
  intro B' f' T' hE hf _ hS₂
  have hK := Enl.KsC_eq hE
  have hrng : ∀ y : B.LL0, ∃ x : B'.LL0, B'.embLL x = B.embLL y := fun y => by
    have : B.embLL y.1 ∈ B'.embLL '' (B'.LL0 : Set B'.LL) := hE.2.2.1 ▸ ⟨y.1, y.2, rfl⟩
    obtain ⟨x, hx, hxy⟩ := this
    exact ⟨⟨x, hx⟩, hxy⟩
  have hL := GlobalTheory.Mem.Col2.JetEx.hasLetters_of_over hO
  have hP := (base_fields_primes_ok B w.px).2.1
  have hX : Oriented w.px f.P := fun k v => by
    have h1 := w.ok.pibar k v
    rw [DatHecke.mem_vG hP, w.C_eq] at h1
    rw [← h1]
    exact (iff_of_eq (congrArg (· ∈ v.asIdeal) (RingOfIntegers.ext (B.fields_conjO_coe _)))).symm
  have hsp := of_over hO
  obtain ⟨⟨B0, C0, W0, V0, S0, N0, G0⟩, hB0, -⟩ := StagesInhab.exists_stages_over B hL 1
  dsimp only at hB0
  subst hB0
  have hv := w.val C0 W0 V0 S0 N0 G0
  have e1 := hE.1
  clear hE
  cases B0
  dsimp only at e1
  subst e1
  have ef := eq_of_heq hf
  subst ef
  dsimp only at hS₂
  rw [dif_pos rfl] at hS₂
  obtain ⟨I, hI, hTw, hJets, hC, hSS, hxi, hsel, hJ, hval, hroot, hfld⟩ :=
    hS B' w.px f' T' w.I.sel w.I.J hsp.1 hsp.2 hL hX w.ok.sel_ok w.ok.amb_ok hS₂
  have hval0 : ∀ C W V S N G, Formalism.L2.Host.ValLL0 (assemble B' C W V S N G) (Fr.at ⟨B', C, W, V, S, N, G⟩ f') :=
    fun C W V S N G => ⟨fun j => valuesIn_lift (hv.mu0 j) hrng, valuesIn_lift hv.eta hrng, valuesIn_lift hv.chiPsi hrng,
      valuesIn_lift hv.del hrng, valuesIn_lift hv.del' hrng⟩
  let w' : ColW B' f' T' :=
    { px := w.px
      I := I
      ok := hI
      C_eq := hC
      S_eq := hSS
      xi_range := hxi
      pins := ⟨w.pins.iX, w.pins.cof⟩
      l := TC.laws_of_ok I hI
      l0 := StepZero.law0 I hI _
      δ := w.δ
      exact := hK.trans w.exact
      fld := hfld
      val := hval0 }
  have cp' : ColPin w' :=
    { isTw := hTw
      jets := hJets
      hX := (base_fields_primes_ok B' w.px).1
      above := fun v => by rw [hsel]; exact cp.above v
      half := by rw [hsel]; exact cp.half
      d3b := cp.d3b
      selectedPlacesAgree := by rw [hsel]; exact cp.selectedPlacesAgree
      vals := fun a P _ => hval a P
      roots := hroot }
  exact ⟨w', ⟨cp'⟩, HEq.rfl, heq_of_eq hsel, heq_of_eq hJ, HEq.rfl⟩

end GlobalTheory.Mem.Top.ReW

end
