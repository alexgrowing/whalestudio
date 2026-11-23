import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfMulJ0Decoration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnsPeriodMapDatumOkAndOverLevelPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TilQ

section ExtM

variable {A : Type} [CommRing A] {N n : ℕ} (hN : N = n + 1) (g : Matrix (Fin n) (Fin n) A)

theorem extM_iC_iC (i j : Fin n) : TilX.extM hN g (Br.iC hN i) (Br.iC hN j) = g i j := by
  simp [TilX.extM, Br.iC]

theorem extM_iC_iL (i : Fin n) : TilX.extM hN g (Br.iC hN i) (Br.iL hN) = 0 := by
  simp [TilX.extM, Br.iC, Br.iL]

theorem extM_iL_iC (j : Fin n) : TilX.extM hN g (Br.iL hN) (Br.iC hN j) = 0 := by
  simp [TilX.extM, Br.iC, Br.iL]

theorem extM_iL_iL : TilX.extM hN g (Br.iL hN) (Br.iL hN) = 1 := by
  simp [TilX.extM, Br.iL]

end ExtM

section Single

variable {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1)

theorem prH_single_iC (j : Fin n) : GlobalTheory.TopStep.prH E hN (Pi.single (Br.iC hN j) 1) = Pi.single j 1 := by
  funext i
  rw [GlobalTheory.TopStep.prH_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [Pi.single_eq_of_ne (fun e => h (Br.iC_inj hN e)), Pi.single_eq_of_ne h]

theorem prH_single_iL : GlobalTheory.TopStep.prH E hN (Pi.single (Br.iL hN) 1) = 0 := by
  funext i
  rw [GlobalTheory.TopStep.prH_apply, Pi.single_eq_of_ne]
  · rfl
  · intro e
    have := congrArg Fin.val e
    simp [Br.iC, Br.iL] at this
    omega

end Single

theorem adAt_of_bc_one {B : Base} {n : ℕ} {k : GA B n} (P : HeightOneSpectrum (𝓞 B.host.E))
    (hk : bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) k = 1) (i j : Fin n) :
    adAt B.host.F P (k.1 i j) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion B.host.E)) i j := by
  have h2 : prV (E := B.host.E) (P.under (𝓞 B.host.F))
      (k.1 i j - (1 : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) i j) = 0 := by
    have h3 := congrArg (fun g : GL (Fin n) _ => g.1 i j) hk
    simp only [Units.val_one] at h3
    have h4 : prV (E := B.host.E) (P.under (𝓞 B.host.F)) (k.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j := h3
    rw [map_sub, h4, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 := TilX.adAt_eq_zero_of_prV P _ h2
  rw [map_sub, sub_eq_zero] at h3
  refine h3.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

set_option maxHeartbeats 1600000 in

theorem pt_tilF_gen : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → Pins B X → ∀ (l : I.Laws) (Z : Later B (I.cols l)) (u : B.Word) (a : I.ι) (k t : GA B (B.R.N B.R.m)), (∃ p : DecoF B.fields.E (B.R.N B.R.m) ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N B.R.m)) → (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) → (∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N B.R.m)), r.1 + 1 = (B.R.N B.R.m) → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)) → t ∈ K1 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs → (∀ (P : I.Q a) (i j : Fin (B.R.N B.R.m)), adAt B.host.F P.1 (t.1 i j) = algebraMap B.host.E _ (if i = j then (if i.1 + 1 = (B.R.N B.R.m) then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0)) → ∀ (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d → IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 → PtOf (g * (k * t)) (tilF I.sel (I.tup a) u d) := by
  intro B X I hI hP l Z u a k t hk1 hk2 hk3 ht htP d g' g hg' hext
  haveI : IsEmpty ↥(∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) := ⟨fun x => Finset.notMem_empty _ x.2⟩
  obtain ⟨p0, hp0, hN0⟩ := hk1
  have hPr := (base_fields_primes_ok B X).2.1
  have hN := N_m_succ B.R
  have hgw : ∀ w : (B.primes X).vGs, ∃ i, ((B.primes X).g i : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
    intro w
    have h1 : ∃ i, w.1 ∈ (B.primes X).vG i := by
      have h0 := w.2
      unfold Primes.vGs at h0
      simp only [Finset.mem_union] at h0
      rcases h0 with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    obtain ⟨i, hi⟩ := h1
    refine ⟨i, ?_⟩
    rw [← hPr.piG_norm i]
    exact w.1.asIdeal.mul_mem_left _ (mem_of_mem_divs hi)
  have hpi1 : ∀ w : (B.primes X).vGs, (B.primes X).piT u - 1 ∈ w.1.asIdeal := by
    intro w
    obtain ⟨i, hi⟩ := hgw w
    obtain ⟨c, hc⟩ := hPr.piT_cong u
    rw [hc]
    refine w.1.asIdeal.mul_mem_right _ ?_
    have hd : (B.primes X).g i ∣ (B.primes X).cond * ((B.primes X).g 0 * (B.primes X).g 1) ^ 2 := by
      refine dvd_mul_of_dvd_right (dvd_pow ?_ two_ne_zero) _
      fin_cases i
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    obtain ⟨c', hc'⟩ := hd
    rw [hc']
    push_cast
    exact w.1.asIdeal.mul_mem_right _ hi
  have hTw : ∀ w : (B.primes X).vGs, (B.T u : 𝓞 B.host.F) ∉ (w.1.under (𝓞 B.host.F)).asIdeal := by
    intro w hT
    obtain ⟨i, hi⟩ := hgw w
    have h1 : ((B.primes X).T u : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
      have h2 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ w.1.asIdeal := hT
      rw [map_natCast] at h2
      exact h2
    have hc : Nat.Coprime ((B.primes X).T u) ((B.primes X).g i) :=
      (Nat.coprime_primes (hPr.T_prime u) (hPr.g_prime i)).2 (hPr.T_ne_g u i)
    have h3 : ((1 : ℕ) : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc)
      have e : ((1 : ℤ) : 𝓞 B.fields.E) = (a : 𝓞 B.fields.E) * ((B.primes X).T u : 𝓞 B.fields.E) +
          (b : 𝓞 B.fields.E) * ((B.primes X).g i : 𝓞 B.fields.E) := by
        rw [← hab]; push_cast; ring
      have e' : ((1 : ℕ) : 𝓞 B.fields.E) = ((1 : ℤ) : 𝓞 B.fields.E) := by simp
      rw [e', e]
      exact add_mem (w.1.asIdeal.mul_mem_left _ h1) (w.1.asIdeal.mul_mem_left _ hi)
    exact w.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h3))
  have hkw : ∀ (w : (B.primes X).vGs) (i j : Fin (B.R.N B.R.m)),
      adAt B.host.F w.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 i j) = (1 : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (w.1.adicCompletion B.host.E)) i j := by
    intro w i j
    refine adAt_of_bc_one w.1 ?_ i j
    rw [map_inv, hk2 _ (hTw w), inv_one]
  have hA := TilX.isPtOf_tilFr (hc := B.sp.cm) (ST := (B.primes X).vT u) hN (conj_piT_notMem hPr u) hpi1
    (hg'.extTo (Finset.empty_subset _) (Finset.disjoint_empty_right _)) hp0.uni
    (by have := hp0.lat; rwa [hN0] at this) hkw hk3
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 ht
  have hB := (isPtOf_mul_J0 B.host.F B.host.E B.sp.cm _ ((B.primes X).vT u) (B.primes X).vGs ∅ _ m.1 _
    (tilFr (ST := (B.primes X).vT u) hN ((B.primes X).piT u) (extTo ∅ d)) 1).2.1 rfl hA m.2 (by rw [inv_one]; exact hm)
  obtain ⟨-, -, hiX, -⟩ := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z
  have hpi0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := by
    intro h0
    have h1 : X.piT u = 0 := RingOfIntegers.ext h0
    have h2 := hPr.piT_norm u
    have h3 : (B.primes X).piT u = 0 := h1
    rw [h3, zero_mul] at h2
    exact (hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)
  have hgext : g = TilX.extGL hN g' := by
    refine Units.ext (TilX.eq_extM_of_ext hN (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) hpi0
      (TilX.iXm_apply hiX hN) hext.1 ?_)
    have h2 := hext.2
    have hz : z0 X u = Pi.single (Br.iL (N_m_succ B.R)) ((X.piT u : 𝓞 B.host.E) : B.host.E) := TilX.lastCoordinateUniformizerVector_eq_single u
    rw [hz] at h2
    exact h2
  have hQ := PerLaw.piT_notMem_Q hI u a
  have hQ0 : ∀ P : (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))), (B.primes X).piT u ∉ P.1.asIdeal := fun P => isEmptyElim P
  have e : (tilF I.sel (I.tup a) u d).deco =
      (tilFr (ST := (B.primes X).vT u) hN ((B.primes X).piT u) (extTo ∅ d)).deco := by
    rw [tilF_deco I.sel (I.tup a) hPr u hQ d, tilFr_deco hN (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) hQ0, extTo_deco]
  rw [show ((1, 1, 1) : UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs ×
    GLQ B.fields.E (B.R.N B.R.m) ∅) = 1 from rfl, one_smul] at hB
  rw [hgext, ← mul_assoc]
  refine ⟨hB.uni, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact hB.lat
  · rw [e]; exact hB.f
  · rw [e]; exact hB.be
  · intro P i j
    have hTq : (B.T u : 𝓞 B.host.F) ∉ (P.1.under (𝓞 B.host.F)).asIdeal := by
      intro hT
      have h2 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ P.1.asIdeal := hT
      rw [map_natCast] at h2
      exact T_notMem_QE I.sel (I.tup a) u hPr hI.sel_ok (hI.T_mem u) P.1 P.2 h2
    have hkP := adAt_of_bc_one P.1 (hk2 _ hTq)
    have e1 : adAt B.host.F P.1 (((TilX.extGL hN g' * k * (J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)).subtype m :
        GA B (B.R.N B.R.m)) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)) i j) =
        adAt B.host.F P.1 (TilX.extM hN g'.1 i j) *
          adAt B.host.F P.1 ((((J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)).subtype m : GA B (B.R.N B.R.m)) :
            Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)) j j) := by
      rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, map_sum, Finset.sum_eq_single j]
      · rw [map_mul, Matrix.mul_apply, map_sum, Finset.sum_eq_single j, map_mul, hkP, Matrix.one_apply_eq, mul_one]
        · rfl
        · intro l _ hl
          rw [map_mul, hkP, Matrix.one_apply_ne hl, mul_zero]
        · simp
      · intro l _ hl
        rw [map_mul, htP P l j, if_neg hl, map_zero, mul_zero]
      · simp
    rw [e1, htP P j j, if_pos rfl, tilF_fr I.sel (I.tup a) hPr u hQ d P]
    rcases GlobalTheory.TopStep.idx_cases hN i with ⟨i', rfl⟩ | rfl <;> rcases GlobalTheory.TopStep.idx_cases hN j with ⟨j', rfl⟩ | rfl
    · have h1 : ¬ ((Br.iC hN j').1 + 1 = B.R.N B.R.m) := by
        show ¬ (j'.1 + 1 = B.R.N B.R.m)
        have := j'.2
        omega
      rw [if_neg h1, map_one, mul_one, extM_iC_iC, hg'.fr P i' j']
      congr 1
      exact ((congrFun (GlobalTheory.TopStep.prH_sumE hN (d.fr P) _ (Pi.single (Br.iC hN j') 1)) i').trans
        (by rw [prH_single_iC])).symm
    · have h0 := (congrFun (GlobalTheory.TopStep.prH_sumE hN (d.fr P) (unitOf ((B.primes X).piT u)) (Pi.single (Br.iL hN) 1)) i').trans
        (by rw [prH_single_iL, map_zero])
      rw [extM_iC_iL, map_zero, zero_mul]
      exact (congrArg (algebraMap B.host.E _) h0).trans (map_zero _) |>.symm
    · rw [extM_iL_iC, map_zero, zero_mul, GlobalTheory.TopStep.sumE_last, Pi.single_eq_of_ne, mul_zero, map_zero]
      intro e
      have := congrArg Fin.val e
      simp [Br.iC, Br.iL] at this
      omega
    · have h1 : (Br.iL hN).1 + 1 = B.R.N B.R.m := by
        show (B.R.N B.R.m - 1) + 1 = B.R.N B.R.m
        omega
      rw [if_pos h1, extM_iL_iL, map_one, one_mul, GlobalTheory.TopStep.sumE_last, Pi.single_eq_same, mul_one,
        unitOf_val (hQ P)]

end GlobalTheory.Mem.Col2.TilQ

end
