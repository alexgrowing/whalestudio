import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.GoodPrimeSelection

theorem heq_sigma_app {P P' Tw Tw' Y Y' : Type} (hP : P = P') (hTw : Tw = Tw') (hY : Y = Y')
    {RCG : Tw → Finset Y → Type} {RCG' : Tw' → Finset Y' → Type} {gR : ∀ i Q, CommGroup (RCG i Q)} {gR' : ∀ i Q, CommGroup (RCG' i Q)}
    {Ok : Tw → ℕ → Type} {Ok' : Tw' → ℕ → Type} {cO : ∀ i k, CommRing (Ok i k)} {cO' : ∀ i k, CommRing (Ok' i k)}
    (hRCG : HEq RCG RCG') (hgR : HEq gR gR') (hOk : HEq Ok Ok') (hcO : HEq cO cO')
    {twI : P → Tw} {twI' : P' → Tw'} (h1 : HEq twI twI') {Q : P → Finset Y} {Q' : P' → Finset Y'} (h2 : HEq Q Q')
    {k : P → ℕ} {k' : P' → ℕ} (h3 : HEq k k')
    {psi : ∀ w, RCG (twI w) (Q w) →* (Ok (twI w) (k w))ˣ} {psi' : ∀ w, RCG' (twI' w) (Q' w) →* (Ok' (twI' w) (k' w))ˣ}
    (h4 : HEq psi psi') {w : P} {w' : P'} (hw : HEq w w') :
    HEq (⟨twI w, Q w, k w, psi w⟩ : Σ (i : Tw) (Q : Finset Y) (k : ℕ), RCG i Q →* (Ok i k)ˣ)
      (⟨twI' w', Q' w', k' w', psi' w'⟩ : Σ (i : Tw') (Q : Finset Y') (k : ℕ), RCG' i Q →* (Ok' i k)ˣ) := by
  subst hP hTw hY
  cases hRCG; cases hgR; cases hOk; cases hcO; cases h1; cases h2; cases h3; cases h4; cases hw
  rfl

theorem heq_sigma_pow {Tw Tw' Y Y' : Type} (hTw : Tw = Tw') (hY : Y = Y')
    {RCG : Tw → Finset Y → Type} {RCG' : Tw' → Finset Y' → Type} {gR : ∀ i Q, CommGroup (RCG i Q)} {gR' : ∀ i Q, CommGroup (RCG' i Q)}
    {Ok : Tw → ℕ → Type} {Ok' : Tw' → ℕ → Type} {cO : ∀ i k, CommRing (Ok i k)} {cO' : ∀ i k, CommRing (Ok' i k)}
    (hRCG : HEq RCG RCG') (hgR : HEq gR gR') (hOk : HEq Ok Ok') (hcO : HEq cO cO')
    {p : Σ (i : Tw) (Q : Finset Y) (k : ℕ), RCG i Q →* (Ok i k)ˣ} {p' : Σ (i : Tw') (Q : Finset Y') (k : ℕ), RCG' i Q →* (Ok' i k)ˣ}
    (hp : HEq p p') (b : Bool) (c : ℤ) :
    HEq (⟨p.1, p.2.1, p.2.2.1, BlochKatoReduction.Gen.psiAt b (p.2.2.2 ^ c)⟩ : Σ (i : Tw) (Q : Finset Y) (k : ℕ), RCG i Q →* (Ok i k)ˣ)
      (⟨p'.1, p'.2.1, p'.2.2.1, BlochKatoReduction.Gen.psiAt b (p'.2.2.2 ^ c)⟩ : Σ (i : Tw') (Q : Finset Y') (k : ℕ), RCG' i Q →* (Ok' i k)ˣ) := by
  subst hTw hY
  cases hRCG; cases hgR; cases hOk; cases hcO; cases hp
  rfl

theorem disjoint_of_heq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H')
    {A B : Finset (PlE H)} {A' B' : Finset (PlE H')} (hA : HEq A A') (hB : HEq B B') (h : Disjoint A B) : Disjoint A' B' := by
  subst hR; cases hH; cases hA; cases hB; exact h

theorem plE_eq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') : PlE H = PlE H' := by
  subst hR; cases hH; rfl

theorem auxiliaryPrime_eq_of_same_ranks_host {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) : AbsolutelyIrreducibleSpan.q0 D = AbsolutelyIrreducibleSpan.q0 D' := by
  cases D; cases D'
  dsimp only at hR hH
  subst hR; cases hH
  rfl

theorem discr_eq {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) :
    (NumberField.discr D.host.E).natAbs.primeFactors = (NumberField.discr D'.host.E).natAbs.primeFactors := by
  cases D; cases D'
  dsimp only at hR hH
  subst hR; cases hH
  rfl

theorem mem_avD_iff {D : D7} (i : D.ntw.Tw) (v : PlE D.host) :
    v ∈ avD D (avDesign D) i ↔ ∃ p ∈ avPrimes D ∪ avPrimesDesign D i, v ∈ placesOver D.host.E p := by
  classical
  unfold avD
  rw [Finset.mem_union, mem_avRec, mem_avDesign]
  constructor
  · rintro (⟨p, hp, hv⟩ | ⟨p, hp, hv⟩)
    · exact ⟨p, Finset.mem_union_left _ hp, hv⟩
    · exact ⟨p, Finset.mem_union_right _ hp, hv⟩
  · rintro ⟨p, hp, hv⟩
    rcases Finset.mem_union.1 hp with hp | hp
    · exact Or.inl ⟨p, hp, hv⟩
    · exact Or.inr ⟨p, hp, hv⟩

theorem avD_heq {D D' : D7} (h : SameExport D D') {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') :
    HEq (avD D (avDesign D) i) (avD D' (avDesign D') i') := by
  have hl : D.ntw.l i = D'.ntw.l i' := ((same_basic h.gal h.set h.frm).2.2.2.2 i i' hi).1
  have hd : avPrimesDesign D i = avPrimesDesign D' i' := by
    unfold avPrimesDesign
    rw [hl, auxiliaryPrime_eq_of_same_ranks_host h.gal.R h.gal.host, discr_eq h.gal.R h.gal.host]
  refine heq_places h.gal.R h.gal.host (s := avPrimes D ∪ avPrimesDesign D i) (mem_avD_iff i) ?_
  intro v
  rw [mem_avD_iff i' v, h.av, hd]

def normE {D : D7} (xd : ThData D) (h : XdAll xd) : IntegralHeckeForms.XD D where
  Dat0 i j b := if 1 ≤ j ∧ j ≤ D.R.m then Set.univ else ∅
  theta_base_equivariant i j b a ha u := by
    by_cases hj : 1 ≤ j ∧ j ≤ D.R.m
    · exact xd.thetaBase_invariant_action i j b a (by rw [h i j b hj.1 hj.2]; trivial) u
    · rw [if_neg hj] at ha
      exact ha.elim

theorem normE_eq {D : D7} (xd : ThData D) (h : XdAll xd) :
    ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, (normE xd h).Dat0 i j b = (twEOf xd).Dat0 i j b := by
  intro i j hj b
  rw [Finset.mem_Icc] at hj
  show (if 1 ≤ j ∧ j ≤ D.R.m then Set.univ else ∅) = xd.xd0 i j b
  rw [if_pos hj, h i j b hj.1 hj.2]

theorem heq_ite_univ {T T' : Type} (hT : T = T') {Dat : T → ℕ → Bool → Type} {Dat' : T' → ℕ → Bool → Type}
    (hD : HEq Dat Dat') {m m' : ℕ} (hm : m = m') :
    HEq (fun i j b => (if 1 ≤ j ∧ j ≤ m then Set.univ else ∅ : Set (Dat i j b)))
      (fun i j b => (if 1 ≤ j ∧ j ≤ m' then Set.univ else ∅ : Set (Dat' i j b))) := by
  subst hT hm; cases hD; rfl

theorem normE_heq {D D' : D7} (h : SameExport D D') (xd : ThData D) (hx : XdAll xd) (xd' : ThData D') (hx' : XdAll xd') :
    HEq (normE xd hx).Dat0 (normE xd' hx').Dat0 :=
  heq_ite_univ (eq_of_heq h.set.Tw) h.frm.Dat (by rw [h.gal.R])

theorem goodTw_swap {D : D7} {E E' : IntegralHeckeForms.XD D} (hE : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, E.Dat0 i j b = E'.Dat0 i j b)
    {N0 : D.ntw.Tw → ℕ} {i : D.ntw.Tw} {e : ℝ} {S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)}
    {A Q : Finset (PlE D.host)} {k : ℕ} {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ}
    (h : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E N0 i e S A Q k ψ) : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E' N0 i e S A Q k ψ := by
  unfold IntegralHeckeForms.GoodTw at h ⊢
  obtain ⟨h1, ⟨eB, h0, hs, hI⟩, h3, h4⟩ := h
  refine ⟨h1, ⟨eB, h0, hs, fun j hj b => ?_⟩, fun j hj b => ?_, h4⟩
  · have := hI j hj b
    unfold IntegralHeckeForms.SgJ at this ⊢
    rwa [← hE i j hj b]
  · have := h3 j hj b
    unfold IntegralHeckeForms.SgJ at this ⊢
    rwa [← hE i j hj b]

theorem ok_swap {D : D7} {I I' : TwIn D} (hE : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, I.E.Dat0 i j b = I'.E.Dat0 i j b)
    (hS : I.S = I'.S) {i : D.ntw.Tw} (h : I.Ok i) : I'.Ok i := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun j hj b => ?_, fun j hj b => ?_⟩
  · have := h1 j hj b
    unfold TwIn.Sg IntegralHeckeForms.SgJ IntegralHeckeForms.FullRk at this ⊢
    rw [← hE i j hj b]
    exact this
  · have := h2 j hj b
    unfold TwIn.Sg IntegralHeckeForms.SgJ at this ⊢
    rw [← hE i j hj b, ← hS]
    exact this

theorem good_pack {D D' : D7} (h : SameExport D D') {I : TwIn D} {I' : TwIn D'} (hE : HEq I.E.Dat0 I'.E.Dat0)
    (hN : HEq I.N0 I'.N0) (hS : HEq I.S I'.S) {p : TwPack D} {p' : TwPack D'} (hp : HEq p p')
    {A : Finset (PlE D.host)} {A' : Finset (PlE D'.host)} (hA : HEq A A')
    (hg : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 p.1 (twEps D p.1) (I.S p.1) A p.2.1 p.2.2.1 p.2.2.2) :
    IntegralHeckeForms.GoodTw D'.nexp (BlochKatoReduction.bk0 D') I'.E I'.N0 p'.1 (twEps D' p'.1) (I'.S p'.1) A' p'.2.1 p'.2.2.1 p'.2.2.2 := by
  obtain ⟨-, -, -, h1, h2⟩ := same_basic h.gal h.set h.frm
  obtain ⟨h3, h4, h5, h6⟩ := h1 p p' hp
  obtain ⟨h7, h8, -⟩ := h2 _ _ h3
  obtain ⟨i, Q, k, ψ⟩ := p
  obtain ⟨i', Q', k', ψ'⟩ := p'
  dsimp only at h3 h4 h5 h6 h7 h8 hg ⊢
  subst h5
  have he : twEps D' i' = twEps D i := by rw [twEps, twEps, h7]
  rw [he]
  exact goodTw_transfer h.gal h.set h.frm (B := BlochKatoReduction.bk0 D) (B' := BlochKatoReduction.bk0 D') h.br rfl rfl hE hN h3 _ (h8 _ _ hS).1 hA h4 k h6 hg

theorem psiAt_pow_pow {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) (a c : ℤ) :
    ∃ e : ℤ, e.natAbs = a.natAbs * c.natAbs ∧ BlochKatoReduction.Gen.psiAt b ((ψ ^ a) ^ c) = ψ ^ e := by
  obtain ⟨e, he, h⟩ := Formalism.MainNotions.N.TwAll.psiAt_side_zpow true b ψ (a * c)
  refine ⟨e, by rw [he, Int.natAbs_mul], ?_⟩
  rw [← zpow_mul, h]
  simp [BlochKatoReduction.Gen.psiAt]

theorem goodO_of_seed : ∀ (D₁ D₂ D₃ : D7) (A : D₁.ntw.Tw → Finset (PlE D₁.host)) (σ : Seed D₁ A) (C₂ : NChoice D₂)
    (C₃ : NChoice D₃) (xd : ThData D₃) (u : D₃.what₂.places.Pl → D₁.what₂.places.Pl), SameExport D₁ D₂ → Kept C₂ C₃ →
    avPrimes D₂ = avPrimes D₃ → D₂.what₂.places.Pl = D₃.what₂.places.Pl → XdAll xd → (∀ i, avD D₁ (avDesign D₁) i ⊆ A i) →
    (∀ v₂ v₃, HEq v₂ v₃ → TwistedAt D₃ v₃ → TwistedAt D₁ (u v₃) ∧ ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l (σ.s (u v₃))) ∧
      HEq (rawPack C₂ v₂) (GlobalTheory.HeightCounting.twPackPow D₁ a (σ.pack (u v₃)))) → GoodO D₃ C₃ xd := by
  intro D₁ D₂ D₃ A σ C₂ C₃ xd u h12 hK hav hPl hxd hA hu
  have h23 : SameExport D₂ D₃ := ⟨hK.gal, hK.set, hK.forms, hK.br, hav⟩
  have h13 : SameExport D₁ D₃ := h12.trans h23
  obtain ⟨hTw, -, hSS, hcomp, hsame⟩ := same_basic h13.gal h13.set h13.frm
  have hY : PlE D₁.host = PlE D₃.host := plE_eq h13.gal.R h13.gal.host

  have key : ∀ v, TwistedAt D₃ v → TwistedAt D₁ (u v) ∧ ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l (σ.s (u v))) ∧
      HEq (GlobalTheory.HeightCounting.twPackPow D₁ a (σ.pack (u v))) (rawPack C₃ v) := by
    intro v hv
    obtain ⟨ht, a, ha, hp⟩ := hu (cast hPl.symm v) v (cast_heq _ _) hv
    refine ⟨ht, a, ha, hp.symm.trans ?_⟩
    exact heq_sigma_app (RCG := D₂.ntw.RCG) (RCG' := D₃.ntw.RCG) (gR := D₂.ntw.grpRCG) (gR' := D₃.ntw.grpRCG)
      (Ok := D₂.ntw.Ok) (Ok' := D₃.ntw.Ok) (cO := D₂.ntw.crOk) (cO' := D₃.ntw.crOk)
      hPl (eq_of_heq hK.set.Tw) (plE_eq hK.gal.R hK.gal.host) hK.set.RCG hK.set.grpRCG hK.set.Ok hK.set.crOk
      hK.twI hK.Q hK.k hK.psi (cast_heq _ _)
  have hN0 : (D₁.ntw.Tw → ℕ) = (D₃.ntw.Tw → ℕ) := by rw [hTw]
  let I₁ : TwIn D₁ := ⟨normE σ.xd σ.all, σ.N0, σ.S⟩
  let In : TwIn D₃ := ⟨normE xd hxd, cast hN0 σ.N0, cast hSS σ.S⟩
  let I₃ : TwIn D₃ := ⟨twEOf xd, cast hN0 σ.N0, cast hSS σ.S⟩
  have hE : HEq I₁.E.Dat0 In.E.Dat0 := normE_heq h13 σ.xd σ.all xd hxd
  have hN : HEq I₁.N0 In.N0 := (cast_heq _ _).symm
  have hS : HEq I₁.S In.S := (cast_heq _ _).symm
  have h1n : ∀ i, ∀ j ∈ Finset.Icc 1 D₁.R.m, ∀ b, (twEOf σ.xd).Dat0 i j b = (normE σ.xd σ.all).Dat0 i j b :=
    fun i j hj b => (normE_eq σ.xd σ.all i j hj b).symm
  have h3n : ∀ i, ∀ j ∈ Finset.Icc 1 D₃.R.m, ∀ b, In.E.Dat0 i j b = I₃.E.Dat0 i j b := normE_eq xd hxd

  have pw : ∀ v, TwistedAt D₃ v → ∀ c : ℤ, Nat.Coprime c.natAbs (D₃.ntw.l (C₃.twI v)) →
      ∀ (B₁ : Finset (PlE D₁.host)) (B₃ : Finset (PlE D₃.host)), HEq B₁ B₃ → B₁ ⊆ A (σ.s (u v)) →
      I₃.Ok (C₃.twI v) ∧ IntegralHeckeForms.GoodTw D₃.nexp (BlochKatoReduction.bk0 D₃) I₃.E I₃.N0 (C₃.twI v) (twEps D₃ (C₃.twI v)) (I₃.S (C₃.twI v)) B₃
        (C₃.Q v) (C₃.k' v) (BlochKatoReduction.Gen.psiAt (C₃.sd v) (C₃.psi' v ^ c)) := by
    intro v hv c hc B₁ B₃ hB hBA
    obtain ⟨ht, a, ha, hp⟩ := key v hv
    have hl : D₁.ntw.l (σ.s (u v)) = D₃.ntw.l (C₃.twI v) := (hsame _ _ (hcomp _ _ hp).1).1
    have hq := heq_sigma_pow (RCG := D₁.ntw.RCG) (RCG' := D₃.ntw.RCG) (gR := D₁.ntw.grpRCG) (gR' := D₃.ntw.grpRCG)
      (Ok := D₁.ntw.Ok) (Ok' := D₃.ntw.Ok) (cO := D₁.ntw.crOk) (cO' := D₃.ntw.crOk)
      hTw hY h13.set.RCG h13.set.grpRCG h13.set.Ok h13.set.crOk hp (C₃.sd v) c
    obtain ⟨e, he, hpe⟩ := psiAt_pow_pow (C₃.sd v) (σ.ψ (σ.s (u v))) a c
    have hce : Nat.Coprime e.natAbs (D₁.ntw.l (σ.s (u v))) := by
      rw [he]
      exact Nat.Coprime.mul ha (hl ▸ hc)
    obtain ⟨hok, hg⟩ := σ.good (u v) ht
    have g1 := goodTw_swap h1n (hg e hce)
    rw [← hpe] at g1
    have g2 : IntegralHeckeForms.GoodTw D₁.nexp (BlochKatoReduction.bk0 D₁) I₁.E I₁.N0 (σ.s (u v)) (twEps D₁ (σ.s (u v))) (I₁.S (σ.s (u v))) B₁
        (σ.Q (σ.s (u v))) (σ.k (σ.s (u v))) (BlochKatoReduction.Gen.psiAt (C₃.sd v) ((σ.ψ (σ.s (u v)) ^ a) ^ c)) :=
      expGood_anti (I := I₁) (p := ⟨σ.Q (σ.s (u v)), σ.k (σ.s (u v)), _⟩) hBA g1
    have ok1 : I₁.Ok (σ.s (u v)) := ok_swap (I := ⟨twEOf σ.xd, σ.N0, σ.S⟩) (I' := I₁) h1n rfl hok
    have g3 := good_pack h13 hE hN hS hq hB g2
    have ok3 := (SameExport.good h13 hE hN hS hq
      ⟨ok1, expGood_anti (I := I₁) (p := ⟨σ.Q (σ.s (u v)), σ.k (σ.s (u v)), _⟩)
        ((avRec_subset_avD D₁ (avDesign D₁) _).trans (hA _)) g1⟩).1
    exact ⟨ok_swap h3n rfl ok3, goodTw_swap h3n g3⟩
  refine ⟨⟨I₃, rfl, fun v hv => ?_, fun v hv _ => ?_⟩, fun v v' hv hv' hne => ?_⟩
  · obtain ⟨ht, a, ha, hp⟩ := key v hv
    exact ⟨(pw v hv 1 (by simp) _ _ h13.avRec ((avRec_subset_avD D₁ (avDesign D₁) _).trans (hA _))).1,
      fun c hc => (pw v hv c hc _ _ h13.avRec ((avRec_subset_avD D₁ (avDesign D₁) _).trans (hA _))).2⟩
  · obtain ⟨ht, a, ha, hp⟩ := key v hv
    have h := (pw v hv 1 (by simp) _ _ (avD_heq h13 (hcomp _ _ hp).1) (hA _)).2
    rw [zpow_one] at h
    exact h
  · obtain ⟨ht, a, ha, hp⟩ := key v hv
    obtain ⟨ht', a', ha', hp'⟩ := key v' hv'
    obtain ⟨hi, hQ, -, -⟩ := hcomp _ _ hp
    obtain ⟨hi', hQ', -, -⟩ := hcomp _ _ hp'
    refine disjoint_of_heq h13.gal.R h13.gal.host hQ hQ' (σ.sep (u v) (u v') ht ht' fun he => hne ?_)
    exact eq_of_heq ((hi.symm.trans (heq_of_eq he)).trans hi')

end GlobalTheory.HeightCounting.Up.GoodPrimeSelection
