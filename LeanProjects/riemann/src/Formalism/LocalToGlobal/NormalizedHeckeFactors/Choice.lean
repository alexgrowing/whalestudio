import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
import Formalism.LocalToGlobal.NormalizedHeckeFactors.WittCoreInclusionMulVecMemLatticeCompletionAtPla
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsGoodPlacesEveryConjugate

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace Formalism.L2

abbrev TwPick (D : D7) (i : D.ntw.Tw) : Type :=
  Σ (Q : Finset (PlE D.host)) (k' : ℕ), D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ

def ExpHyp (D : D7) (I : TwIn D) (i : D.ntw.Tw) : Prop :=
  Formalism.MainNotions.IntegralHeckeEveryConjugate D (BlochKatoReduction.bk0 D) I.E I.N0 ∧ D.ntw.NonzeroIndexPlace i ∧ BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i ∧ I.Ok i

open Classical in

def ExpGood (D : D7) (I : TwIn D) (A : Finset (PlE D.host)) (i : D.ntw.Tw) (p : TwPick D i) : Prop :=
  IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 i (twEps D i) (I.S i) A p.1 p.2.1 p.2.2

open Classical in

theorem expGood_anti {D : D7} {I : TwIn D} {A A' : Finset (PlE D.host)} (hA : A ⊆ A') {i : D.ntw.Tw} {p : TwPick D i}
    (h : ExpGood D I A' i p) : ExpGood D I A i p := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  refine And.intro (And.intro h1 (And.intro (h2.mono_right ?_) h3)) h4
  intro x hx
  simp only [Finset.mem_union] at hx ⊢
  rcases hx with hx | hx | hx
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr (hA hx))

theorem exists_expPick (D : D7) (I : TwIn D) (A : Finset (PlE D.host)) (i : D.ntw.Tw) :
    ∃ p : TwPick D i, ExpHyp D I i → ExpGood D I A i p := by
  by_cases h : ExpHyp D I i
  · obtain ⟨h1, h2, h3, h4⟩ := h
    unfold Formalism.MainNotions.IntegralHeckeEveryConjugate at h1
    obtain ⟨Q, k', ψ', hg⟩ := h1 i h2 h3 (twEps D i) (twEps_pos D i) h4.1 (I.S i) h4.2 A
    refine ⟨⟨Q, k', ψ'⟩, fun _ => ?_⟩
    have hg1 := hg 1 (by simp)
    rw [zpow_one] at hg1
    exact hg1
  · exact ⟨⟨∅, 0, 1⟩, fun h' => absurd h' h⟩

def expPick (D : D7) (I : TwIn D) (A : Finset (PlE D.host)) (i : D.ntw.Tw) : TwPick D i :=
  Classical.choose (exists_expPick D I A i)

theorem expPick_good (D : D7) (I : TwIn D) (A : Finset (PlE D.host)) (i : D.ntw.Tw) (h : ExpHyp D I i) :
    ExpGood D I A i (expPick D I A i) := Classical.choose_spec (exists_expPick D I A i) h

abbrev TwAv (D : D7) : Type := D.ntw.Tw → Finset (PlE D.host)

def avD (D : D7) (Av : TwAv D) (i : D.ntw.Tw) : Finset (PlE D.host) :=
  open Classical in AvRec D ∪ Av i

theorem avRec_subset_avD (D : D7) (Av : TwAv D) (i : D.ntw.Tw) : AvRec D ⊆ avD D Av i := by
  classical
  intro v hv
  unfold avD
  exact Finset.mem_union_left _ hv

theorem av_subset_avD (D : D7) (Av : TwAv D) (i : D.ntw.Tw) : Av i ⊆ avD D Av i := by
  classical
  intro v hv
  unfold avD
  exact Finset.mem_union_right _ hv

def placesOverQ0 (D : D7) : Finset (PlE D.host) :=
  (placesOver_finite_av D.host.E (AbsolutelyIrreducibleSpan.q0 D) (Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1.ne_zero).toFinset

theorem mem_places_over_q0 {D : D7} (v : PlE D.host) : v ∈ placesOverQ0 D ↔ v ∈ placesOver D.host.E (AbsolutelyIrreducibleSpan.q0 D) := by
  unfold placesOverQ0
  exact Set.Finite.mem_toFinset _

theorem places_over_q0_nonempty (D : D7) : (placesOverQ0 D).Nonempty := by
  have h1 : (placesOver D.host.E (AbsolutelyIrreducibleSpan.q0 D)).ncard ≠ 0 := by
    rw [Host.split_prime_splits_completely (D := D)]
    exact Module.finrank_pos.ne'
  obtain ⟨v, hv⟩ := Set.nonempty_of_ncard_ne_zero h1
  exact ⟨v, (mem_places_over_q0 v).2 hv⟩

def avOver (D : D7) (s : Finset ℕ) : Finset (PlE D.host) :=
  (Set.Finite.biUnion (s := ((s.filter (· ≠ 0) : Finset ℕ) : Set ℕ)) (t := fun p => placesOver D.host.E p)
    (Finset.finite_toSet _) fun p hp => placesOver_finite_av _ p (Finset.mem_filter.1 hp).2).toFinset

theorem mem_avOver {D : D7} (s : Finset ℕ) (v : PlE D.host) :
    v ∈ avOver D s ↔ ∃ p ∈ s, p ≠ 0 ∧ v ∈ placesOver D.host.E p := by
  simp only [avOver, Set.Finite.mem_toFinset, Set.mem_iUnion, exists_prop, Finset.mem_coe,
    Finset.mem_filter, and_assoc]

def avPrimesDesign (D : D7) (i : D.ntw.Tw) : Finset ℕ :=
  insert 2 (insert (D.ntw.l i) (insert (AbsolutelyIrreducibleSpan.q0 D) (NumberField.discr D.host.E).natAbs.primeFactors))

theorem prime_of_mem_avPrimesDesign {D : D7} {i : D.ntw.Tw} {p : ℕ} (hp : p ∈ avPrimesDesign D i) : p.Prime := by
  unfold avPrimesDesign at hp
  simp only [Finset.mem_insert, Nat.mem_primeFactors] at hp
  rcases hp with rfl | rfl | rfl | ⟨hp, -, -⟩
  · exact Nat.prime_two
  · exact Fact.out
  · exact (Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1
  · exact hp

def avDesign (D : D7) : TwAv D := fun i => avOver D (avPrimesDesign D i)

theorem mem_avDesign {D : D7} (i : D.ntw.Tw) (v : PlE D.host) :
    v ∈ avDesign D i ↔ ∃ p ∈ avPrimesDesign D i, v ∈ placesOver D.host.E p := by
  show v ∈ avOver D (avPrimesDesign D i) ↔ _
  rw [mem_avOver]
  constructor
  · rintro ⟨p, hp, -, hv⟩
    exact ⟨p, hp, hv⟩
  · rintro ⟨p, hp, hv⟩
    exact ⟨p, hp, (prime_of_mem_avPrimesDesign hp).ne_zero, hv⟩

theorem places_over_q0_subset_design (D : D7) (i : D.ntw.Tw) : placesOverQ0 D ⊆ avDesign D i := by
  intro v hv
  rw [mem_places_over_q0] at hv
  rw [mem_avDesign]
  refine ⟨AbsolutelyIrreducibleSpan.q0 D, ?_, hv⟩
  unfold avPrimesDesign
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

theorem places_over_q0_subset_avD (D : D7) (i : D.ntw.Tw) : placesOverQ0 D ⊆ avD D (avDesign D) i := (places_over_q0_subset_design D i).trans (av_subset_avD D (avDesign D) i)

theorem places_over_q0_subset_avRec (D : D7) : placesOverQ0 D ⊆ AvRec D := by
  intro v hv
  rw [mem_places_over_q0] at hv
  rw [mem_avRec]
  refine ⟨AbsolutelyIrreducibleSpan.q0 D, ?_, hv⟩
  have hq : q0Av D = AbsolutelyIrreducibleSpan.q0 D := rfl
  have hne : q0Av D ≠ 0 := hq ▸ (Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1.ne_zero
  rw [← hq]
  unfold avPrimes
  simp [hne]

def SidePl (D : D7) (w : D.what₂.places.Pl) (i : D.ntw.Tw) (s : Bool) : Prop :=
  ∀ x : D.LL0, 0 ≤ D.what₂.places.val w (x : D.what₂.LL) ↔
    (if s then D.ntw.emb0 i x else D.ntw.emb0b i x) ∈ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).range

def fracOk (D : D7) (i : D.ntw.Tw) (k : ℕ) : FractionRing (D.ntw.O0 i) →+* FractionRing (D.ntw.Ok i k) :=
  IsFractionRing.map (j := (algebraMap (D.ntw.O i) (D.ntw.Ok i k)).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)))
    ((D.ntw.Ok_inj i k).comp (D.ntw.O_inj i))

def twPackPow (D : D7) (a : ℤ) (p : TwPack D) : TwPack D :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2 ^ a⟩

def fracOe (D : D7) (C : NChoice D) (w : D.what₂.places.Pl) : FractionRing (D.ntw.O0 (C.twI w)) →+* FractionRing (C.Oe w) :=
  IsFractionRing.map (j := (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)).comp
      ((algebraMap (D.ntw.O (C.twI w)) (D.ntw.Ok (C.twI w) (C.k' w))).comp (algebraMap (D.ntw.O0 (C.twI w)) (D.ntw.O (C.twI w)))))
    ((C.Oe_inj w).comp ((D.ntw.Ok_inj (C.twI w) (C.k' w)).comp (D.ntw.O_inj (C.twI w))))

structure NChoiceTied (D : D7) (C : NChoice D) (I : TwIn D) (Av : TwAv D) : Prop where
  twI_conj : ∀ w, C.twI (D.what₂.places.conj w) = C.twI w
  sd_place : ∀ w, TwistedAt D w → SidePl D w (C.twI w) (C.sd w)
  emb_side : ∀ w, TwistedAt D w → ∀ (x : D.LL0), C.embW w (x : D.what₂.LL) =
    fracOe D C w (if C.sd w then D.ntw.emb0 (C.twI w) x else D.ntw.emb0b (C.twI w) x)
  sd_conj : ∀ w, TwistedAt D w → D.what₂.places.conj w ≠ w → C.sd (D.what₂.places.conj w) = !C.sd w
  one : ∀ w w', TwistedAt D w → TwistedAt D w' → C.twI w' = C.twI w →
    ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l (C.twI w)) ∧ NChoicePack C w' = twPackPow D a (NChoicePack C w)
  good : ∀ w, TwistedAt D w → ExpHyp D I (C.twI w) →
    ExpGood D I (avD D Av (C.twI w)) (C.twI w) ⟨C.Q w, C.k' w, BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w)⟩
  conj : ∀ w, TwistedAt D w → NChoicePack C (D.what₂.places.conj w) = NChoicePack C w

structure NChoicePick (D : D7) (C : NChoice D) (I : TwIn D) (Av : TwAv D) : Prop where
  twI_conj : ∀ w, C.twI (D.what₂.places.conj w) = C.twI w
  sd_place : ∀ w, SidePl D w (C.twI w) (C.sd w)
  emb_side : ∀ w (x : D.LL0), C.embW w (x : D.what₂.LL) =
    fracOe D C w (if C.sd w then D.ntw.emb0 (C.twI w) x else D.ntw.emb0b (C.twI w) x)
  sd_conj : ∀ w, D.what₂.places.conj w ≠ w → C.sd (D.what₂.places.conj w) = !C.sd w
  pick : ∀ w, TwistedAt D w → NChoicePack C w = ⟨C.twI w, expPick D I (avD D Av (C.twI w)) (C.twI w)⟩

def NChoiceOff (D : D7) (C : NChoice D) : Prop :=
  ∀ w, ¬ TwistedAt D w → C.Q w = ∅ ∧ ∀ g, C.psi' w g = 1

variable {D : D7} {C : NChoice D} {I : TwIn D} {Av : TwAv D}

theorem twPackPow_one (p : TwPack D) : twPackPow D 1 p = p := by
  rcases p with ⟨i, Q, k, ψ⟩
  simp only [twPackPow, zpow_one]

theorem one_of_pack_eq {p p' : TwPack D} (n : ℕ) (h : p' = p) : ∃ a : ℤ, Nat.Coprime a.natAbs n ∧ p' = twPackPow D a p := ⟨1, by simp, by rw [h, twPackPow_one]⟩

theorem NChoiceTied.Q_eq (hT : NChoiceTied D C I Av) {w w' : D.what₂.places.Pl} (hw : TwistedAt D w)
    (hw' : TwistedAt D w') (h : C.twI w' = C.twI w) : C.Q w' = C.Q w := by
  obtain ⟨a, -, ha⟩ := hT.one w w' hw hw' h
  exact congrArg (fun p : TwPack D => p.2.1) ha

theorem NChoiceTied.k'_eq (hT : NChoiceTied D C I Av) {w w' : D.what₂.places.Pl} (hw : TwistedAt D w)
    (hw' : TwistedAt D w') (h : C.twI w' = C.twI w) : C.k' w' = C.k' w := by
  obtain ⟨a, -, ha⟩ := hT.one w w' hw hw' h
  exact congrArg (fun p : TwPack D => p.2.2.1) ha

theorem raw_pow_of_pack {i i' : D.ntw.Tw} {Q Q' : Finset (PlE D.host)} {k k' : ℕ}
    {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} {ψ' : D.ntw.RCG i' Q' →* (D.ntw.Ok i' k')ˣ} {s s' : Bool} {a : ℤ}
    (h : (⟨i', Q', k', BlochKatoReduction.Gen.psiAt s' ψ'⟩ : TwPack D) = ⟨i, Q, k, (BlochKatoReduction.Gen.psiAt s ψ) ^ a⟩) :
    (⟨i', Q', k', ψ'⟩ : TwPack D) = ⟨i, Q, k, ψ ^ (if s = s' then a else -a)⟩ := by
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 (eq_of_heq h)
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 (eq_of_heq h)
  have h' := eq_of_heq h
  have key : ψ' = ψ ^ (if s = s' then a else -a) := by
    cases s <;> cases s' <;> simp only [BlochKatoReduction.Gen.psiAt, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at h' ⊢
    · rw [inv_zpow] at h'
      exact inv_injective h'
    · rw [h', inv_zpow']
    · rw [zpow_neg, ← h', inv_inv]
    · exact h'
  rw [key]

theorem NChoiceTied.conjAllAt (hT : NChoiceTied D C I Av) : TwConjAllAt D C := by
  unfold TwConjAllAt
  intro w w' hw hw' h
  obtain ⟨a, ha, hp⟩ := hT.one w w' hw hw' h
  unfold NChoicePack twPack twPackPow at hp
  refine ⟨if C.sd w = C.sd w' then a else -a, ?_, ?_⟩
  · split_ifs
    · exact ha
    · rwa [Int.natAbs_neg]
  · exact raw_pow_of_pack hp

theorem NChoicePick.pick_eq (hT : NChoicePick D C I Av) (w : D.what₂.places.Pl) (hw : TwistedAt D w) :
    (⟨C.Q w, C.k' w, BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w)⟩ : TwPick D (C.twI w)) = expPick D I (avD D Av (C.twI w)) (C.twI w) := by
  have h := hT.pick w hw
  unfold NChoicePack twPack at h
  exact eq_of_heq (Sigma.mk.inj_iff.1 h).2

private theorem psiAt_psiAt' {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) :
    BlochKatoReduction.Gen.psiAt b (BlochKatoReduction.Gen.psiAt b ψ) = ψ := by
  cases b <;> simp [BlochKatoReduction.Gen.psiAt]

private theorem twPack_psiAt_eq (i : D.ntw.Tw) (s : Bool) (e : TwPick D i) :
    twPack D i s e.1 e.2.1 (BlochKatoReduction.Gen.psiAt s e.2.2) = ⟨i, e⟩ := by
  unfold twPack
  rw [psiAt_psiAt']

theorem NChoicePick.psi'_eq (hT : NChoicePick D C I Av) (w : D.what₂.places.Pl) (hw : TwistedAt D w) :
    (⟨C.Q w, C.k' w, C.psi' w⟩ : TwPick D (C.twI w)) =
      ⟨(expPick D I (avD D Av (C.twI w)) (C.twI w)).1, (expPick D I (avD D Av (C.twI w)) (C.twI w)).2.1,
        BlochKatoReduction.Gen.psiAt (C.sd w) (expPick D I (avD D Av (C.twI w)) (C.twI w)).2.2⟩ := by
  rw [← hT.pick_eq w hw]
  rw [psiAt_psiAt']

theorem NChoicePick.tied (hT : NChoicePick D C I Av) : NChoiceTied D C I Av where
  twI_conj := hT.twI_conj
  sd_place w _ := hT.sd_place w
  emb_side w _ := hT.emb_side w
  sd_conj w _ := hT.sd_conj w
  one w w' hw hw' h := one_of_pack_eq _ (by rw [hT.pick w' hw', hT.pick w hw, h])
  good w hw hE := by
    have hG := expPick_good D I (avD D Av (C.twI w)) (C.twI w) hE
    rw [← hT.pick_eq w hw] at hG
    exact hG
  conj w hw := by rw [hT.pick _ ((twistedAt_conj D w).2 hw), hT.pick w hw, hT.twI_conj w]

theorem twGoodAt_of_tied (hT : NChoiceTied D C I Av) (hconds : Formalism.MainNotions.IntegralHeckeEveryConjugate D (BlochKatoReduction.bk0 D) I.E I.N0)
    (hW1 : ∀ w, TwistedAt D w → D.ntw.NonzeroIndexPlace (C.twI w))
    (hset : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (C.twI w))
    (hI : ∀ w, TwistedAt D w → I.Ok (C.twI w)) : TwGoodAt D C I := by
  intro w hw
  exact ⟨hI w hw, expGood_anti (avRec_subset_avD D Av _)
    (hT.good w hw (And.intro hconds (And.intro (hW1 w hw) (And.intro (hset w hw) (hI w hw)))))⟩

open Classical in

theorem disjoint_av_of_tied (hT : NChoiceTied D C I Av) (hconds : Formalism.MainNotions.IntegralHeckeEveryConjugate D (BlochKatoReduction.bk0 D) I.E I.N0)
    (w : D.what₂.places.Pl) (hw : TwistedAt D w) (hW1 : D.ntw.NonzeroIndexPlace (C.twI w))
    (hset : BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (C.twI w)) (hI : I.Ok (C.twI w)) :
    Disjoint (C.Q w) (avD D Av (C.twI w)) := by
  classical
  obtain ⟨⟨-, hd, -⟩, -⟩ := hT.good w hw (And.intro hconds (And.intro hW1 (And.intro hset hI)))
  refine hd.mono_right ?_
  intro x hx
  simp only [Finset.mem_union]
  exact Or.inr (Or.inr hx)

theorem NChoiceTied.mono {Av' : TwAv D} (hT : NChoiceTied D C I Av) (h : ∀ i, Av' i ⊆ Av i) : NChoiceTied D C I Av' where
  twI_conj := hT.twI_conj
  sd_place := hT.sd_place
  emb_side := hT.emb_side
  sd_conj := hT.sd_conj
  one := hT.one
  good w hw hE := by
    classical
    refine expGood_anti ?_ (hT.good w hw hE)
    unfold avD
    exact Finset.union_subset_union (subset_refl _) (h _)
  conj := hT.conj

theorem disjoint_design_of_tied (hT : NChoiceTied D C I (avDesign D)) (hconds : Formalism.MainNotions.IntegralHeckeEveryConjugate D (BlochKatoReduction.bk0 D) I.E I.N0)
    (w : D.what₂.places.Pl) (hw : TwistedAt D w) (hW1 : D.ntw.NonzeroIndexPlace (C.twI w))
    (hset : BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (C.twI w)) (hI : I.Ok (C.twI w)) :
    ∀ v ∈ C.Q w, ∀ p ∈ avPrimesDesign D (C.twI w), v ∉ placesOver D.host.E p := by
  intro v hv p hp hvp
  have hd := disjoint_av_of_tied hT hconds w hw hW1 hset hI
  have hmem : v ∈ avD D (avDesign D) (C.twI w) := av_subset_avD D _ _ ((mem_avDesign _ v).2 ⟨p, hp, hvp⟩)
  exact Finset.disjoint_left.1 hd hv hmem

theorem disjoint_q0_of_agreement (hT : NChoiceTied D C I (avDesign D)) (hconds : Formalism.MainNotions.IntegralHeckeEveryConjugate D (BlochKatoReduction.bk0 D) I.E I.N0)
    (w : D.what₂.places.Pl) (hw : TwistedAt D w) (hW1 : D.ntw.NonzeroIndexPlace (C.twI w))
    (hset : BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (C.twI w)) (hI : I.Ok (C.twI w)) :
    ∀ v ∈ C.Q w, v ∉ placesOver D.host.E (AbsolutelyIrreducibleSpan.q0 D) := by
  intro v hv hvq
  refine disjoint_design_of_tied hT hconds w hw hW1 hset hI v hv (AbsolutelyIrreducibleSpan.q0 D) ?_ hvq
  unfold avPrimesDesign
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

theorem twConjAt_of_tied (hT : NChoiceTied D C I Av) : TwConjAt D C := fun w hw => ⟨hT.conj w hw, hT.sd_conj w hw⟩

theorem exists_tied_choice (D : D7) (I : TwIn D) (Av : TwAv D) (twI : D.what₂.places.Pl → D.ntw.Tw)
    (sd : D.what₂.places.Pl → Bool) :
    ∃ (Q : D.what₂.places.Pl → Finset (PlE D.host)) (k' : D.what₂.places.Pl → ℕ)
      (psi' : ∀ w, D.ntw.RCG (twI w) (Q w) →* (D.ntw.Ok (twI w) (k' w))ˣ),
      (∀ w w', twI w' = twI w →
        twPack D (twI w') (sd w') (Q w') (k' w') (psi' w') = twPack D (twI w) (sd w) (Q w) (k' w) (psi' w)) ∧
      ∀ w, ExpHyp D I (twI w) → ExpGood D I (avD D Av (twI w)) (twI w) ⟨Q w, k' w, BlochKatoReduction.Gen.psiAt (sd w) (psi' w)⟩ := by
  refine ⟨fun w => (expPick D I (avD D Av (twI w)) (twI w)).1, fun w => (expPick D I (avD D Av (twI w)) (twI w)).2.1,
    fun w => BlochKatoReduction.Gen.psiAt (sd w) (expPick D I (avD D Av (twI w)) (twI w)).2.2, fun w w' h => ?_, fun w hE => ?_⟩
  · unfold twPack
    rw [psiAt_psiAt, psiAt_psiAt]
    exact congrArg (fun i => (⟨i, expPick D I (avD D Av i) i⟩ : TwPack D)) h
  · have hG := expPick_good D I (avD D Av (twI w)) (twI w) hE
    rw [psiAt_psiAt]
    exact hG

theorem sidePl_conj (D : D7) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (w : D.what₂.places.Pl)
    (i : D.ntw.Tw) (s : Bool) (h : SidePl D w i s) : SidePl D (D.what₂.places.conj w) i (!s) := by
  intro x
  let y : D.LL0 := ⟨star (x : D.what₂.LL), hstar x⟩
  rw [D.conj_val, show star (x : D.what₂.LL) = (y : D.what₂.LL) from rfl, h y]
  cases s
  · have e : D.ntw.emb0b i y = D.ntw.emb0 i x := D.ntw.restX_coefficientEmbedding_conj i y x (by simp [y])
    simp only [Bool.not_false, Bool.false_eq_true, if_false, if_true, e]
  · have e : D.ntw.emb0b i x = D.ntw.emb0 i y := D.ntw.restX_coefficientEmbedding_conj i x y rfl
    simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true, e]

theorem sdPlace_conj_of (D : D7) (C : NChoice D) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (w : D.what₂.places.Pl) (h1 : C.twI (D.what₂.places.conj w) = C.twI w)
    (h2 : C.sd (D.what₂.places.conj w) = !C.sd w) (h : SidePl D w (C.twI w) (C.sd w)) :
    SidePl D (D.what₂.places.conj w) (C.twI (D.what₂.places.conj w)) (C.sd (D.what₂.places.conj w)) := by
  rw [h1, h2]
  exact sidePl_conj D hstar w _ _ h

theorem emb0_mem_maximalIdeal_iff_val_pos_of_sidePl (D : D7) (w : D.what₂.places.Pl) (i : D.ntw.Tw) (h : SidePl D w i true)
    (x : D.LL0) :
    (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i x) ↔
    0 < D.what₂.places.val w (x : D.what₂.LL) := by
  have key : ∀ z : D.LL0, 0 ≤ D.what₂.places.val w (z : D.what₂.LL) ↔
      D.ntw.emb0 i z ∈ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).range := fun z => by
    simpa using h z
  have hinj := IsFractionRing.injective (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))
  have hmul : ∀ z : D.LL0, z ≠ 0 →
      D.what₂.places.val w (z : D.what₂.LL) + D.what₂.places.val w ((z⁻¹ : D.LL0) : D.what₂.LL) = 0 := by
    intro z hz
    rw [← AddValuation.map_mul, IntermediateField.coe_inv, mul_inv_cancel₀ (by exact_mod_cast hz),
      AddValuation.map_one]
  constructor
  · rintro ⟨y, hy, hyx⟩
    by_cases hx : x = 0
    · subst hx; simp
    by_contra hlt
    have h0 : 0 ≤ D.what₂.places.val w (x : D.what₂.LL) := (key x).2 ⟨y, hyx⟩
    have heq : D.what₂.places.val w (x : D.what₂.LL) = 0 := le_antisymm (not_lt.1 hlt) h0
    have hinv : 0 ≤ D.what₂.places.val w ((x⁻¹ : D.LL0) : D.what₂.LL) := by
      have := hmul x hx
      rw [heq, zero_add] at this
      rw [this]
    obtain ⟨y', hy'⟩ := (key x⁻¹).1 hinv
    have hne : D.ntw.emb0 i x ≠ 0 := (map_ne_zero _).2 hx
    have hone : algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) (y * y') = 1 := by
      rw [map_mul, hyx, hy', map_inv₀, mul_inv_cancel₀ hne]
    have hyy : y * y' = 1 := hinj (by rw [hone, map_one])
    have hu : IsUnit y := ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).1 hy hu
  · intro hpos
    obtain ⟨y, hy⟩ := (key x).1 hpos.le
    refine ⟨y, ?_, hy⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      have : y = 0 := hinj (by rw [hy, map_zero])
      exact not_isUnit_zero (this ▸ hu)
    have hinv : 0 ≤ D.what₂.places.val w ((x⁻¹ : D.LL0) : D.what₂.LL) := by
      refine (key x⁻¹).2 ⟨((hu.unit⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i), ?_⟩
      rw [map_inv₀, ← hy]
      exact (map_units_inv _ hu.unit).trans (by simp)
    have hsum := hmul x hx
    have : 0 < D.what₂.places.val w (x : D.what₂.LL) + D.what₂.places.val w ((x⁻¹ : D.LL0) : D.what₂.LL) :=
      add_pos_of_pos_of_nonneg hpos hinv
    rw [hsum] at this
    exact lt_irrefl _ this

theorem nonzeroIndexPlace_of_sidePl_twistedAt (D : D7) (w : D.what₂.places.Pl) (i : D.ntw.Tw) (h : SidePl D w i true)
    (hw : TwistedAt D w) : D.ntw.NonzeroIndexPlace i := ⟨w, hw, fun x => emb0_mem_maximalIdeal_iff_val_pos_of_sidePl D w i h (x : D.LL0)⟩

theorem nonzero_index_place_of_twisted (hT : NChoiceTied D C I Av) (hc : ConjPreservesLL0 D) (w : D.what₂.places.Pl) (hw : TwistedAt D w) :
    D.ntw.NonzeroIndexPlace (C.twI w) := by
  have hs := hT.sd_place w hw
  cases hsd : C.sd w with
  | true =>
    rw [hsd] at hs
    exact nonzeroIndexPlace_of_sidePl_twistedAt D w _ hs hw
  | false =>
    rw [hsd] at hs
    unfold ConjPreservesLL0 at hc
    have hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0 := by
      intro x
      obtain ⟨y, hy⟩ := hc x
      rw [← hy]
      exact y.2
    exact nonzeroIndexPlace_of_sidePl_twistedAt D (D.what₂.places.conj w) _ (sidePl_conj D hstar w _ _ hs) ((twistedAt_conj D w).2 hw)

theorem twGoodAt_of_tied_conj (hT : NChoiceTied D C I Av) (hc : ConjPreservesLL0 D) (hconds : Formalism.MainNotions.IntegralHeckeEveryConjugate D (BlochKatoReduction.bk0 D) I.E I.N0)
    (hset : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (C.twI w))
    (hI : ∀ w, TwistedAt D w → I.Ok (C.twI w)) : TwGoodAt D C I := twGoodAt_of_tied hT hconds (fun w hw => nonzero_index_place_of_twisted hT hc w hw) hset hI

open Classical in

def twInOf (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : TwIn D where
  E := E
  N0 := N0
  S i j b := if h : ∃ S, IntegralHeckeForms.BasisOf D.nexp i j b (IntegralHeckeForms.SgJ D.nexp E i j b) S then h.choose else ∅

def twInRec (D : D7) (T : ThData D) (N0 : D.ntw.Tw → ℕ) : TwIn D := twInOf D (twEOf T) N0

def twInAll (D : D7) (N0 : D.ntw.Tw → ℕ) : TwIn D := twInOf D (IntegralHeckeForms.ExpDat.all D.nexp) N0

theorem twInAll_max (D : D7) (N0 : D.ntw.Tw → ℕ) : (twInAll D N0).E.Max := IntegralHeckeForms.ExpDat.all_max D.nexp

theorem twInAll_Sg (D : D7) (N0 : D.ntw.Tw → ℕ) (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    (twInAll D N0).Sg i j b = (twInAll D N0).E.Dat0 i j b := rfl

theorem twInRec_E (D : D7) (T : ThData D) (N0 : D.ntw.Tw → ℕ) : (twInRec D T N0).E.Dat0 = T.xd0 := rfl

theorem twInOf_ok_iff (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) (i : D.ntw.Tw) :
    (twInOf D E N0).Ok i ↔ ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
      IntegralHeckeForms.FullRk D.nexp E i j b (IntegralHeckeForms.SgJ D.nexp E i j b) ∧ ∃ S, IntegralHeckeForms.BasisOf D.nexp i j b (IntegralHeckeForms.SgJ D.nexp E i j b) S := by
  classical
  constructor
  · rintro ⟨hF, hB⟩ j hj b
    exact ⟨hF j hj b, _, hB j hj b⟩
  · intro h
    refine ⟨fun j hj b => (h j hj b).1, fun j hj b => ?_⟩
    have hx := (h j hj b).2
    show IntegralHeckeForms.BasisOf D.nexp i j b (IntegralHeckeForms.SgJ D.nexp E i j b)
      (if h : ∃ S, IntegralHeckeForms.BasisOf D.nexp i j b (IntegralHeckeForms.SgJ D.nexp E i j b) S then h.choose else ∅)
    rw [dif_pos hx]
    exact hx.choose_spec

theorem twInAll_ok_iff (D : D7) (N0 : D.ntw.Tw → ℕ) (i : D.ntw.Tw) :
    (twInAll D N0).Ok i ↔ ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
      IntegralHeckeForms.FullRk D.nexp (IntegralHeckeForms.ExpDat.all D.nexp) i j b ((IntegralHeckeForms.ExpDat.all D.nexp).Dat0 i j b) ∧
        ∃ S, IntegralHeckeForms.BasisOf D.nexp i j b ((IntegralHeckeForms.ExpDat.all D.nexp).Dat0 i j b) S := twInOf_ok_iff D _ N0 i

theorem twGood_of_tied {eps : ℝ} (Fm : FamP eps) (N0 : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, (Fm.D x i).ntw.Tw → ℕ)
    (x0 : ℝ) (h : ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      NChoiceTied (Fm.D x i) (Fm.ex x hx i).nch (twInRec (Fm.D x i) (Fm.ex x hx i).xd (N0 x hx i)) (avDesign (Fm.D x i)) ∧
      Formalism.MainNotions.IntegralHeckeEveryConjugate (Fm.D x i) (BlochKatoReduction.bk0 (Fm.D x i)) (twE Fm x hx i) (N0 x hx i) ∧
      ∀ w, TwistedAt (Fm.D x i) w →
        (Fm.D x i).ntw.NonzeroIndexPlace ((Fm.ex x hx i).nch.twI w) ∧
        BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 (Fm.D x i)) ((Fm.ex x hx i).nch.twI w) ∧
          (twInRec (Fm.D x i) (Fm.ex x hx i).xd (N0 x hx i)).Ok ((Fm.ex x hx i).nch.twI w)) :
    TwGood Fm := by
  unfold TwGood TwGoodE
  refine ⟨x0, fun x hx0 hx i => ?_⟩
  obtain ⟨hT, hconds, hw⟩ := h x hx0 hx i
  exact ⟨twConjAt_of_tied hT, N0 x hx i, (twInRec (Fm.D x i) (Fm.ex x hx i).xd (N0 x hx i)).S,
    twGoodAt_of_tied hT hconds (fun w hw' => (hw w hw').1) (fun w hw' => (hw w hw').2.1)
      (fun w hw' => (hw w hw').2.2)⟩

theorem twGood_of_tied_gen {eps : ℝ} (Fm : FamP eps) (I : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TwIn (Fm.D x i))
    (x0 : ℝ) (h : ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      (I x hx i).E = twE Fm x hx i ∧
      NChoiceTied (Fm.D x i) (Fm.ex x hx i).nch (I x hx i) (avDesign (Fm.D x i)) ∧
      Formalism.MainNotions.IntegralHeckeEveryConjugate (Fm.D x i) (BlochKatoReduction.bk0 (Fm.D x i)) (I x hx i).E (I x hx i).N0 ∧
      ∀ w, TwistedAt (Fm.D x i) w →
        (Fm.D x i).ntw.NonzeroIndexPlace ((Fm.ex x hx i).nch.twI w) ∧
        BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 (Fm.D x i)) ((Fm.ex x hx i).nch.twI w) ∧ (I x hx i).Ok ((Fm.ex x hx i).nch.twI w)) :
    TwGood Fm := by
  unfold TwGood TwGoodE
  refine ⟨x0, fun x hx0 hx i => ?_⟩
  obtain ⟨hE, hT, hconds, hw⟩ := h x hx0 hx i
  refine ⟨twConjAt_of_tied hT, (I x hx i).N0, (I x hx i).S, ?_⟩
  have hg := twGoodAt_of_tied hT hconds (fun w hw' => (hw w hw').1) (fun w hw' => (hw w hw').2.1)
    (fun w hw' => (hw w hw').2.2)
  rw [← hE]
  exact hg

section Vac

variable (D : D7)

theorem twOK_triv (i : D.ntw.Tw) (k : ℕ) : IntegralHeckeForms.TwOK (X := D.ntw) i k ∅ 1 := by
  refine ⟨fun P hP => by simp at hP, Finset.disjoint_empty_left _, ?_, ?_,
    fun g => Subgroup.one_mem _, ?_, ?_⟩
  · simp
  · first
      | (simp [IntegralHeckeForms.AntiHom])
      | (simp [AntiHom])
      | simp
  · intro v A _
    simp
  · first
      | (simp [BlochKatoReduction.Gen.TrivAbove])
      | simp

theorem th_mem_thP (i : D.ntw.Tw) (j : ℕ) (b : Bool) (a : D.nexp.Dat i j b)
    (ha : a ∈ (IntegralHeckeForms.ExpDat.all D.nexp).Dat0 i j b) :
    (1 : D.ntw.Ok i 0) ⊗ₜ[D.ntw.O i] D.nexp.th i j b a ∈
      (D.nexp.MtLat i j b 0 ∅ 1).map (D.nexp.thP i j b 0 ∅ 1) := by
  have h := ha.2.2.2 0 ∅ 1 (twOK_triv D i 0)
  rw [D.nexp.thPsi_one] at h
  exact Set.singleton_subset_iff.1 h

theorem fm_torsionFree (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    Module.IsTorsionFree (D.ntw.O i) (D.nexp.Fm i j b) := by
  constructor
  intro r hr x y hxy
  have hne : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hr.ne_zero
  have h2 : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) r • x =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) r • y := by
    rw [algebraMap_smul, algebraMap_smul]
    exact hxy
  exact smul_right_injective _ hne h2

theorem th_all_fg (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    (IntegralHeckeForms.Th D.nexp i j b ((IntegralHeckeForms.ExpDat.all D.nexp).Dat0 i j b)).FG := by
  have := D.ntw.Ok_fin i 0
  have := fm_torsionFree D i j b
  have hN : (((D.nexp.MtLat i j b 0 ∅ 1).map (D.nexp.thP i j b 0 ∅ 1)).restrictScalars (D.ntw.O i)).FG :=
    ((D.nexp.MtLat_fg i j b 0 ∅ 1).map _).restrictScalars
  let ι : D.nexp.Fm i j b →ₗ[D.ntw.O i] D.ntw.Ok i 0 ⊗[D.ntw.O i] D.nexp.Fm i j b :=
    TensorProduct.mk (D.ntw.O i) (D.ntw.Ok i 0) (D.nexp.Fm i j b) 1
  have hιe : ι = ((Algebra.linearMap (D.ntw.O i) (D.ntw.Ok i 0)).rTensor (D.nexp.Fm i j b)) ∘ₗ
      (TensorProduct.lid (D.ntw.O i) (D.nexp.Fm i j b)).symm.toLinearMap := by
    ext x; simp [ι]
  have hι : Function.Injective ι := by
    rw [hιe]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _ (D.ntw.Ok_inj i 0)).comp
      (TensorProduct.lid (D.ntw.O i) (D.nexp.Fm i j b)).symm.injective
  refine Submodule.fg_of_fg_map_injective ι hι (Submodule.FG.of_le hN ?_)
  rw [IntegralHeckeForms.Th, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  exact th_mem_thP D i j b a ha

theorem exists_basisOf_of_fg (i : D.ntw.Tw) (j : ℕ) (b : Bool) (Sg : Set (D.nexp.Dat i j b))
    (hfg : (IntegralHeckeForms.Th D.nexp i j b Sg).FG) : ∃ S, IntegralHeckeForms.BasisOf D.nexp i j b Sg S := by
  classical
  have := fm_torsionFree D i j b
  let g : D.nexp.Dat i j b → D.nexp.Fm i j b := fun a => IntegralHeckeForms.AO D.nexp i j b (D.nexp.th i j b a)
  let M : Submodule (D.ntw.O i) (D.nexp.Fm i j b) := (IntegralHeckeForms.Th D.nexp i j b Sg).map (IntegralHeckeForms.AO D.nexp i j b)
  have hM : M = Submodule.span (D.ntw.O i) (g '' Sg) := by
    simp only [M, IntegralHeckeForms.Th, Submodule.map_span, Set.image_image, g]
  have hMfg : M.FG := hfg.map _
  have : Module.Finite (D.ntw.O i) M := Module.Finite.iff_fg.2 hMfg
  have : Module.FinitePresentation (D.ntw.O i) M := Module.finitePresentation_of_finite _ _
  let v : Sg → M := fun a => ⟨g a, by rw [hM]; exact Submodule.subset_span ⟨a, a.2, rfl⟩⟩
  have hv : Submodule.span (D.ntw.O i) (Set.range v) = ⊤ := by
    apply Submodule.map_injective_of_injective M.injective_subtype
    have hr : Set.range (M.subtype ∘ v) = g '' Sg := by rw [Set.image_eq_range]; rfl
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp, hr]
    exact hM.symm
  obtain ⟨κ, a, bs, hb⟩ := Module.exists_basis_of_span_of_flat v hv
  have : Finite κ := Module.Finite.finite_basis bs
  let _ : Fintype κ := Fintype.ofFinite κ
  let f : κ → D.nexp.Dat i j b := fun k => ((a k : Sg) : D.nexp.Dat i j b)
  have hf : Function.Injective f := by
    intro k k' h
    apply bs.injective
    rw [hb, hb]
    exact congrArg v (Subtype.ext h)
  have hgf : g ∘ f = M.subtype ∘ bs := by
    funext k
    simp [f, hb, v]
  have hS : ((Finset.univ.image f : Finset (D.nexp.Dat i j b)) : Set (D.nexp.Dat i j b)) = Set.range f := by
    simp
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · rw [hS]; rintro _ ⟨k, rfl⟩; exact (a k).2
  · have h1 : LinearIndepOn (D.ntw.O i) g (Set.range f) := by
      rw [linearIndepOn_range_iff hf, hgf]
      exact bs.linearIndependent.map' M.subtype M.ker_subtype
    rw [← hS] at h1
    exact h1
  · change Submodule.span (D.ntw.O i) (g '' _) = M
    rw [hS, ← Set.range_comp, hgf, Set.range_comp, ← Submodule.map_span, bs.span_eq, Submodule.map_top,
      Submodule.range_subtype]

theorem exists_basisOf_all (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    ∃ S, IntegralHeckeForms.BasisOf D.nexp i j b ((IntegralHeckeForms.ExpDat.all D.nexp).Dat0 i j b) S := exists_basisOf_of_fg D i j b _ (th_all_fg D i j b)

theorem theta_mem_image_lattice (E : IntegralHeckeForms.XD D) (h7 : IntegralHeckeForms.adm7 D E) (i : D.ntw.Tw) (hi : D.ntw.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m)
    (b : Bool) (a : D.nexp.Dat i j b) (ha : a ∈ E.Dat0 i j b) :
    (1 : D.ntw.Ok i 0) ⊗ₜ[D.ntw.O i] D.nexp.th i j b a ∈
      (D.nexp.MtLat i j b 0 ∅ 1).map (D.nexp.thP i j b 0 ∅ 1) := by
  refine h7 i hi j hj b 0 ∅ 1 (twOK_triv D i 0) {a} (Set.singleton_subset_iff.2 ha) (Submodule.subset_span ?_)
  refine Set.mem_iUnion₂.2 ⟨a, rfl, ?_⟩
  rw [D.nexp.thPsi_one]
  exact Set.mem_singleton _

theorem theta_span_fg (E : IntegralHeckeForms.XD D) (h7 : IntegralHeckeForms.adm7 D E) (i : D.ntw.Tw) (hi : D.ntw.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m)
    (b : Bool) : (IntegralHeckeForms.Th D.nexp i j b (E.Dat0 i j b)).FG := by
  have := D.ntw.Ok_fin i 0
  have := fm_torsionFree D i j b
  have hN : (((D.nexp.MtLat i j b 0 ∅ 1).map (D.nexp.thP i j b 0 ∅ 1)).restrictScalars (D.ntw.O i)).FG :=
    ((D.nexp.MtLat_fg i j b 0 ∅ 1).map _).restrictScalars
  let ι : D.nexp.Fm i j b →ₗ[D.ntw.O i] D.ntw.Ok i 0 ⊗[D.ntw.O i] D.nexp.Fm i j b :=
    TensorProduct.mk (D.ntw.O i) (D.ntw.Ok i 0) (D.nexp.Fm i j b) 1
  have hιe : ι = ((Algebra.linearMap (D.ntw.O i) (D.ntw.Ok i 0)).rTensor (D.nexp.Fm i j b)) ∘ₗ
      (TensorProduct.lid (D.ntw.O i) (D.nexp.Fm i j b)).symm.toLinearMap := by
    ext x; simp [ι]
  have hι : Function.Injective ι := by
    rw [hιe]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _ (D.ntw.Ok_inj i 0)).comp
      (TensorProduct.lid (D.ntw.O i) (D.nexp.Fm i j b)).symm.injective
  refine Submodule.fg_of_fg_map_injective ι hι (Submodule.FG.of_le hN ?_)
  rw [IntegralHeckeForms.Th, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  exact theta_mem_image_lattice D E h7 i hi j hj b a ha

theorem twInOf_ok_iff_fullRk (E : IntegralHeckeForms.XD D) (h7 : IntegralHeckeForms.adm7 D E) (N0 : D.ntw.Tw → ℕ) (i : D.ntw.Tw)
    (hi : D.ntw.NonzeroIndexPlace i) :
    (twInOf D E N0).Ok i ↔ ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
      IntegralHeckeForms.FullRk D.nexp E i j b (IntegralHeckeForms.SgJ D.nexp E i j b) := by
  rw [twInOf_ok_iff]
  exact ⟨fun h j hj b => (h j hj b).1,
    fun h j hj b => ⟨h j hj b, exists_basisOf_of_fg D i j b _ (theta_span_fg D E h7 i hi j hj b)⟩⟩

theorem twInRec_ok_iff_fullRk (T : ThData D) (h7 : IntegralHeckeForms.adm7 D (twEOf T)) (N0 : D.ntw.Tw → ℕ) (i : D.ntw.Tw)
    (hi : D.ntw.NonzeroIndexPlace i) :
    (twInRec D T N0).Ok i ↔ ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
      IntegralHeckeForms.FullRk D.nexp (twEOf T) i j b (IntegralHeckeForms.SgJ D.nexp (twEOf T) i j b) := twInOf_ok_iff_fullRk D (twEOf T) h7 N0 i hi

theorem twInAll_ok_iff_fullRk (N0 : D.ntw.Tw → ℕ) (i : D.ntw.Tw) :
    (twInAll D N0).Ok i ↔ ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
      IntegralHeckeForms.FullRk D.nexp (IntegralHeckeForms.ExpDat.all D.nexp) i j b ((IntegralHeckeForms.ExpDat.all D.nexp).Dat0 i j b) := by
  rw [twInAll_ok_iff]
  exact ⟨fun h j hj b => (h j hj b).1, fun h j hj b => ⟨h j hj b, exists_basisOf_all D i j b⟩⟩

end Vac

end Formalism.L2

end
