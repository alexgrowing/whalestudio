import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Plc

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.CongL GlobalTheory.RoadWGeo Formalism.MainNotions.N Formalism.BasicNotions Formalism.ConjugateSelfDual UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
attribute [local instance] Ideal.Quotient.field
open Neutral.B1 ReciprocityTheory.Gal

namespace UpperTheory.Gal.Int.Geo.Pl

structure All : Prop where
  frame : FrameEx
  vec : VecEx
  spec : SpecTop
  exp : ExpOf
  sides : Sides
  lev : LevBasic
  mem : MemEx
  triv : SiteTriv
  site : SiteEx
  good : GoodOf
  cong : CongOf
  dat : DatEx
  roots : CertificateRingHomMap.RootsAlg
  card : SatCard
  cof : IntCof

section

variable {E : Type} [Field E] [NumberField E]

theorem exists_prime_mem (w : Plc E) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 E) ∈ w.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qe49.exists_prime_mem w

def pr (w : Plc E) : ℕ := (exists_prime_mem w).choose

theorem pr_prime (w : Plc E) : (pr w).Prime := (exists_prime_mem w).choose_spec.1

theorem pr_mem (w : Plc E) : (pr w : 𝓞 E) ∈ w.asIdeal := (exists_prime_mem w).choose_spec.2

theorem pr_eq {w : Plc E} {q : ℕ} (hq : q.Prime) (h : (q : 𝓞 E) ∈ w.asIdeal) : pr w = q := by
  by_contra hne
  have hc : IsCoprime ((pr w : ℕ) : 𝓞 E) (q : 𝓞 E) := ((Nat.coprime_primes (pr_prime w) hq).2 hne).cast
  obtain ⟨a, b, e⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ (pr_mem w)) (Ideal.mul_mem_left _ _ h)))

theorem finite_pr (Y : Finset ℕ) : {w : Plc E | pr w ∈ Y}.Finite := by
  refine (Y.finite_toSet.biUnion (t := fun q => {w : Plc E | pr w = q}) fun q _ => ?_).subset fun w hw => by simpa using hw
  by_cases hq : q = 0
  · exact Set.finite_empty.subset fun w hw => (pr_prime w).ne_zero (hw.trans hq)
  · refine (Ideal.finite_factors (I := Ideal.span {((q : ℕ) : 𝓞 E)}) ?_).subset fun w hw => ?_
    · rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hq
    · exact Ideal.dvd_span_singleton.2 (by have := pr_mem w; rwa [show pr w = q from hw] at this)

variable [IsCMField E]

theorem pr_cj (w : Plc E) : pr (CertificateRingHomMap.cj w) = pr w := by
  refine pr_eq (pr_prime w) ?_
  have e : (CertificateRingHomMap.cj w).asIdeal = _ := (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) w)
  rw [e, Ideal.mem_comap, map_natCast]
  exact pr_mem w

theorem cj_cj (w : Plc E) : CertificateRingHomMap.cj (CertificateRingHomMap.cj w) = w := GlobalTheory.SplitPts.conjSrc_conjSrc_cm w

theorem sameK_symm {x : E} {w w' : Plc E} (h : SameK x w w') : SameK x w' w := fun y hy => (h y hy).symm

theorem sameK_trans {x : E} {w w' w'' : Plc E} (h : SameK x w w') (h' : SameK x w' w'') : SameK x w w'' :=
  fun y hy => (h y hy).trans (h' y hy)

theorem pr_of_sameK {x : E} {w w' : Plc E} (h : SameK x w w') : pr w = pr w' :=
  (pr_eq (pr_prime w) ((h _ (by simp)).1 (pr_mem w))).symm

end

set_option maxHeartbeats 1000000 in
theorem master (h : All) {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (ha : Odd a) {d : ℕ} (hd : FieldOK E l d) {x : E} (hx : x ^ 2 = -(d : E)) {w₀ : Plc E} (h0 : ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal)
    {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) (hTy : GlobalTheory.CongW.TyEll E l a w₀ U) (H C : Finset (Plc E))
    (hHC : ∀ w ∈ C, w ∉ H)
    (hQ : ∀ w ∈ H ∪ C, UsPl d w ∧ Apart w w₀ ∧ (∃ B, SatU U w B) ∧ (pr w = l → SameK x w w₀) ∧ ∀ w' ∈ H ∪ C, pr w = pr w' → SameK x w w') :
    ∃ P : Plan ι d U, (∀ v ∈ H, P.HTFor v) ∧ ∀ w ∈ C, P.CongAll w := by
  have hl : l.Prime := Fact.out
  have hsq : ∀ w : Plc E, UsPl d w → ∃ _ : Fact (pr w).Prime, IsSquare (-(d : ℚ_[pr w])) := fun w hw =>
    ⟨⟨pr_prime w⟩, hw.2 _ (pr_prime w) (pr_mem w)⟩
  obtain ⟨A, hd0, hG, hgood, ⟨e, he0, he⟩, hP⟩ := h.dat E l a d ha hd x hx (insert l ((H ∪ C).image pr)) (by
    intro q hq
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact ⟨inferInstance, hd.2.1⟩
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hq
      exact hsq w (hQ w hw).1)
  have hgQ : ∀ w ∈ H ∪ C, A.Good (pr w) := fun w hw => hgood _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hw))
  have hgl : A.Good l := hgood _ (Finset.mem_insert_self _ _)
  have hS0 := h.sides E A x hG l hl hgl.1 w₀ h0
  have hSQ := fun w hw => h.sides E A x hG (pr w) (pr_prime w) (hgQ w hw).1 w (pr_mem w)
  let Up : Plc E → Prop := fun u => ∀ w ∈ H ∪ C, ¬ SameK x (CertificateRingHomMap.cj u) w
  have hUp : ∀ u, IsSplitAt u → Up u ∨ Up (CertificateRingHomMap.cj u) := by
    intro u _
    by_contra hc
    simp only [Up, not_or, not_forall, not_not, cj_cj] at hc
    obtain ⟨⟨w, hw, h1⟩, w', hw', h2⟩ := hc
    have e1 : pr w = pr w' := by rw [← pr_of_sameK h1, ← pr_of_sameK h2, pr_cj]
    have h3 : SameK x u w := sameK_trans h2 (sameK_symm ((hQ w hw).2.2.2.2 w' hw' e1))
    exact (hSQ w hw).1 (sameK_trans (sameK_symm ((hSQ w hw).2.2.2.2.1 u w h3)) h1)
  have hUp0 : Up w₀ := by
    intro w hw h1
    have e1 : pr w = l := by rw [← pr_of_sameK h1, pr_cj, pr_eq hl h0]
    exact hS0.1 (sameK_trans h1 ((hQ w hw).2.2.2.1 e1))
  obtain ⟨V⟩ := h.vec E a l d ha.pos hd0 x hx U hU w₀ hS0.2.1 hTy Up hUp hUp0
  have hfree : ∀ w ∈ H ∪ C, Free V w := by
    intro w hw
    obtain ⟨h1, h2⟩ := V.sph w (hQ w hw).1.1 (hQ w hw).2.1 (hQ w hw).2.2.1
    refine ⟨(hQ w hw).1.1, h1, h2, fun u hu hs => ?_, (hSQ w hw).1⟩
    have hq : ((pr w : ℕ) : 𝓞 E) ∈ u.asIdeal := by rw [← pr_of_sameK hs, pr_cj]; exact pr_mem u
    exact (V.shape.up u hu (h.sides E A x hG (pr w) (pr_prime w) (hgQ w hw).1 u hq).2.1).1 w hw hs
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, V.Φ g₀ ≠ 0 := Function.ne_iff.1 V.form.ne
  have hfin := Filter.eventually_cofinite.1 (h.cof E a g₀)
  obtain ⟨p, hp, S, hpX, hsc⟩ := hP ((H ∪ C).image pr ∪ (V.S ∪ hfin.toFinset).image pr)
  have hoff : Off V p := ⟨fun u hu hm => hpX (Finset.mem_union_right _ (Finset.mem_image.2 ⟨u, Finset.mem_union_left _ hu, pr_eq hp.out hm⟩)),
    g₀, hg₀, fun u hm => by_contra fun hn => hpX (Finset.mem_union_right _ (Finset.mem_image.2
      ⟨u, Finset.mem_union_right _ (hfin.mem_toFinset.2 hn), pr_eq hp.out hm⟩))⟩
  obtain ⟨F⟩ := h.frame E A a p S ha
  obtain ⟨r₀, hr₀, hrX, hrp, hspec⟩ := h.spec E A a p S F x U w₀ Up V ha hsc hG hoff ⟨l, hl, hgl, h0⟩ ((H ∪ C).image pr)
  obtain ⟨N, σ, hrN, hKN, hσ, hcomp⟩ := h.site E A a p S F x U w₀ Up V hG hoff (H ∪ C) pr (fun w hw =>
    ⟨pr_prime w, fun e => hpX (Finset.mem_union_left _ (Finset.mem_image.2 ⟨w, hw, e⟩)), hgQ w hw, pr_mem w, hfree w hw,
      (hQ w hw).2.2.2.2⟩) r₀ hr₀.pos ((Nat.coprime_primes hr₀ hp.out).2 hrp)
  obtain ⟨hL1, hL2, hL3, -, -, -⟩ := h.lev p S.D S.G S.L
  obtain ⟨hM1, hM2⟩ := h.mem E A a p S F d x hd0 hx hG N
  let J : Type := {z : Mem S.L N × ℂ // Seen F V r₀ z.1 z.2 ∧ (IsDeckM z.1 ∨ ∃ (w : Plc E) (σ' : Site S N w) (i : ℕ), w ∉ H ∧
    (∀ v hv, (σ v hv).Compat σ') ∧ IsTM F x σ' i z.1)}
  let g : J → Mem S.L N := fun j => j.1.1
  let θ : J → Qbar l := fun j => ι.symm j.1.2
  obtain ⟨f, hf, hsp⟩ := hspec N hrN hKN J g (fun j => j.1.2) fun j => j.2.1
  obtain ⟨hanti, hexp⟩ := h.exp E A a p S x U w₀ Up V d hd0 hx hG
  have hdeck : ∀ (w : Plc E) (σ' : Site S N w), σ'.q ≠ r₀ → (∀ k ∈ σ'.K₀, Stab F V k) → Deck g θ σ'.K₀ := by
    intro w σ' hq hst k hk
    have hk1 : k ∈ S.L.KN 1 := ((σ'.isLev k).1 hk).1
    have hkr : k ∈ S.L.KN r₀ := by
      refine hL2 _ _ _ _ σ'.isLev (hL3 r₀) (Ideal.mul_le_left.trans (Ideal.span_singleton_le_span_singleton.2 ?_)) hk
      have hN0 : N.1 ≠ 0 := by have := N.2.1; omega
      exact Nat.cast_dvd_cast (Nat.dvd_ordCompl_of_dvd_not_dvd hrN fun hd' =>
        hq ((Nat.prime_dvd_prime_iff_eq σ'.atp.prime hr₀).1 hd'))
    obtain ⟨m, hm, rfl⟩ := hM1 k hk1
    exact ⟨⟨(m, 1), Or.inl ⟨hm, hst _ hk, hkr, rfl⟩, Or.inl hm⟩, hm.1, hm.2.1, rfl, map_one ι.symm⟩
  have hpl : ∀ w : Plc E, IsPl (D := S.D) (RingEquiv.refl E) w w.asIdeal := fun w c c' e => by
    obtain rfl : c' = c := RingOfIntegers.ext e
    exact Iff.rfl
  have hcong : ∀ (w : Plc E) (σ' : Site S N w), Free V w → σ'.q ≠ r₀ → (∀ k ∈ σ'.K₀, Stab F V k) → w ∉ H →
      (∀ v hv, (σ v hv).Compat σ') → ∀ B, SatU U w B → CongP ι a (D := S.D) (RingEquiv.refl E) g θ V.κ w B := by
    intro w σ' hfr hq hst hw hc B hB
    let c : ℂ := ((V.κ.val w : ℂˣ) : ℂ)⁻¹
    let ϑ : ℕ → Qbar l := fun i => ι.symm (satEig (Ideal.absNorm w.asIdeal) a B i * c ^ i)
    refine ⟨V.kap.unr w hfr.2.2.2.1, w.asIdeal, ϑ, hpl w, h.cong E A a p S F x hG N w σ' J _ g θ ϑ (hdeck w σ' hq hst) fun i hi => ?_, ?_⟩
    · obtain ⟨m, hm⟩ := hM2 w σ' i hi
      exact ⟨⟨(m, (idx m : ℂ) * (satEig (Ideal.absNorm w.asIdeal) a B i * c ^ i)), Or.inr ⟨w, σ', i, B, hfr, hq, hst, hm, hB, rfl⟩, Or.inr ⟨w, σ', i, hw, hc, hm⟩⟩, hm, by
        simp only [θ, g, ϑ, c, map_mul, map_natCast]⟩
    · have hq0 : 0 < normV w := Nat.pos_of_ne_zero (by
        show Ideal.absNorm w.asIdeal ≠ 0
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot)
      obtain ⟨e0, e1⟩ := h.roots (normV w) a hq0 B (h.card E a U w B hB) 1 c (fun i => ι (ϑ i)) fun i _ => by
        simp only [ϑ, RingEquiv.apply_symm_apply, one_mul]; rfl
      refine ⟨fun h0 => ?_, ?_⟩
      · rw [h0, map_zero] at e0; exact zero_ne_one e0
      · rw [e0, ← e1]
        simp [crystallineComparison.heckePol, Polynomial.map_sum]
  refine ⟨{ p := p, D := S.D, G := S.G, L := S.L, sc := hsc, e := RingEquiv.refl E, n_eq := rfl, N := N, J := J, g := g, θ := θ,
            κ := V.κ, m := mOf x V.W V.jz, alg := V.kap.alg, lam := V.lam, anti := hanti, f := f, fn := hf,
            spec := by simpa only [θ, RingEquiv.apply_symm_apply] using hsp, cong := ?_ }, fun v hv => ?_, fun w hw B hB => ?_⟩
  · refine ⟨(finite_pr (E := E) ((N.1 * e * p).primeFactors ∪ V.S.image pr)).toFinset, fun w hw hus _ B hB => ?_⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_union, not_or] at hw
    have hN0 : N.1 ≠ 0 := by have := N.2.1; omega
    have hnd : ¬ pr w ∣ N.1 * e * p := fun hd' =>
      hw.1 (Nat.mem_primeFactors.2 ⟨pr_prime w, hd', mul_ne_zero (mul_ne_zero hN0 he0.ne') hp.out.ne_zero⟩)
    have hN : ¬ pr w ∣ N.1 := fun hd' => hnd ((hd'.mul_right _).mul_right _)
    obtain ⟨_, hs⟩ := hsq w hus
    have hgw : A.Good (pr w) := he (pr w) hs fun hd' => hnd ((hd'.mul_left _).mul_right _)
    obtain ⟨σ', hq, hK⟩ := h.triv E A a p S x hG N (pr w) (pr_prime w) (fun e' => hnd (Dvd.intro_left _ (by rw [e']))) hgw hN w (pr_mem w)
    have hnS : ∀ u ∈ V.S, pr u ≠ pr w := fun u hu e' => hw.2 (Finset.mem_image.2 ⟨u, hu, e'⟩)
    refine hcong w σ' ⟨hus.1, fun hm => hnS w hm rfl, fun hm => hnS _ hm (pr_cj w), fun u hu hs' => hnS u hu ?_,
      (h.sides E A x hG _ (pr_prime w) hgw.1 w (pr_mem w)).1⟩ (fun e' => hN (by rw [← hq, e']; exact hrN)) (by rw [hK]; exact hKN)
      (fun hm => hN (hσ w (Finset.mem_union_left _ hm)).1) (fun v hv e' => absurd ?_ hN) B hB
    · rw [← pr_cj u]; exact pr_of_sameK hs'
    · rw [← hq, ← e', (hσ v hv).2.1]; exact (hσ v hv).1
  · have hv' := Finset.mem_union_left C hv
    have hq : (σ v hv').q ≠ r₀ := fun e' => hrX (Finset.mem_image.2 ⟨v, hv', by rw [← e', (hσ v hv').2.1]⟩)
    refine ⟨V.kap.unr v (hfree v hv').2.2.2.1, ⟨v.asIdeal, hpl v, h.good E A a p S F x hG N v (σ v hv') J _ g θ
      (hdeck v _ hq (hσ v hv').2.2) fun j => j.2.2.imp_right ?_⟩, fun τ _ => ?_⟩
    · rintro ⟨w, σ', i, hw, hc, hm⟩
      exact ⟨w, σ', i, fun e' => hw (e' ▸ hv), hc v hv', hm⟩
    · obtain ⟨s, hs, hj⟩ := hexp τ
      refine ⟨s, fun _ y => hs y, fun lam hlam j hj' => ?_⟩
      obtain ⟨hh, i, h1, h2⟩ := hj lam hlam j hj'
      exact ⟨(0 : Fin 1), hh, i, h1, h2⟩
  · have hw' := Finset.mem_union_right H hw
    have hq : (σ w hw').q ≠ r₀ := fun e' => hrX (Finset.mem_image.2 ⟨w, hw', by rw [← e', (hσ w hw').2.1]⟩)
    exact hcong w (σ w hw') (hfree w hw') hq (hσ w hw').2.2 (hHC w hw) (fun v hv => hcomp v hv w hw') B hB

theorem planEx_of (h : All) : PlanEx := by
  intro E _ _ _ l _ ι a ha d hd x hx T _ w₀ v' h0 hv hap h1 S U hU hTy _ hsph
  have hl : l.Prime := Fact.out
  have hus : ∀ w : Plc E, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → UsPl d w := fun w hw =>
    ⟨by_contra fun hn => (hd.2.2.2 w hn).1 hw, fun q hq hm => by
      obtain rfl : q = l := (pr_eq hq hm).symm.trans (pr_eq hl hw)
      exact hd.2.1⟩
  have hv0 : SameK x v' w₀ := sameK_symm h1
  have M := fun H C => master h ι ha hd hx h0 hU.1 hTy H C
  refine ⟨?_, fun w hw hlw hs => ?_, fun w hlw hk ha0 hav hs => ⟨?_, ?_⟩⟩
  · obtain ⟨P, hP, -⟩ := M {v'} ∅ (by simp) (by
      simp only [Finset.union_empty, Finset.mem_singleton, forall_eq]
      exact ⟨hus _ hv, hap, hsph, fun _ => hv0, fun _ _ _ => Iff.rfl⟩)
    exact ⟨P, hP _ (by simp)⟩
  · have hne : pr w ≠ l := fun e => hlw (e ▸ pr_mem w)
    have hvl : pr v' = l := pr_eq hl hv
    obtain ⟨P, hP, hC⟩ := M {v'} {w} (by simp only [Finset.mem_singleton, forall_eq]; rintro rfl; exact hlw hv) (by
      simp only [Finset.mem_union, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      refine ⟨⟨hus _ hv, hap, hsph, fun _ => hv0, fun _ _ _ => Iff.rfl, fun e => absurd (e.symm.trans hvl) hne⟩,
        hw, ?_, hs, fun e => absurd e hne, fun e => absurd (e.trans hvl) hne, fun _ _ _ => Iff.rfl⟩
      intro e
      refine hlw ?_
      have h2 : ((l : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ (w₀.under (𝓞 (maximalRealSubfield E))).asIdeal := by
        change algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ w₀.asIdeal
        simpa using h0
      rw [← e] at h2
      change algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ w.asIdeal at h2
      simpa using h2)
    exact ⟨P, hP _ (by simp), hC _ (by simp)⟩
  · obtain ⟨P, hP, -⟩ := M {v', w} ∅ (by simp) (by
      simp only [Finset.union_empty, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨⟨hus _ hv, hap, hsph, fun _ => hv0, fun _ _ _ => Iff.rfl, fun _ => sameK_symm hk⟩,
        hus _ hlw, ha0, hs, fun _ => sameK_trans hk hv0, fun _ => hk, fun _ _ _ => Iff.rfl⟩)
    exact ⟨P, hP _ (by simp), hP _ (by simp)⟩
  · obtain ⟨P, hP, hC⟩ := M {v'} {w} (by simp only [Finset.mem_singleton, forall_eq]; rintro rfl; exact hav rfl) (by
      simp only [Finset.mem_union, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨⟨hus _ hv, hap, hsph, fun _ => hv0, fun _ _ _ => Iff.rfl, fun _ => sameK_symm hk⟩,
        hus _ hlw, ha0, hs, fun _ => sameK_trans hk hv0, fun _ => hk, fun _ _ _ => Iff.rfl⟩)
    exact ⟨P, hP _ (by simp), hC _ (by simp)⟩

end UpperTheory.Gal.Int.Geo.Pl
