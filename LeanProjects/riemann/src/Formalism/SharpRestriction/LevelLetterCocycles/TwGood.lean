import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataNChTie
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

noncomputable section

namespace Formalism.MainNotions.IntegralHeckeForms

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

def DatOk (i : X.Tw) (j : ℕ) (b : Bool) (a : Y.Dat i j b) : Prop :=
  (∀ u : Y.U, Y.actG i j b u (Y.th i j b a) =
    ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • Y.th i j b a) ∧
  (∃ c : ℕ, ∀ Q M, (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → ClsQ (D := D) Q →
    Disjoint Q (X.S0 i) → Disjoint Q (Y.lev i j b a) →
    ((X.l i : X.O i) ^ c) • Y.thU i j b Q M a ∈ LinearMap.range ((Mall Y i j b).subtype.rTensor _)) ∧
  (∀ k Q (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), TwOK i k Q ψ → UnrG ψ →
    Y.thPsi i j b k Q ψ a ⊆
      ((((Fm0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k) :
        Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)) : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b))) ∧
  (∀ k Q (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), TwOK i k Q ψ →
    Y.thPsi i j b k Q ψ a ⊆
      (((Y.MtLat i j b k Q ψ).map (Y.thP i j b k Q ψ) :
        Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)) : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b)))

variable {Y}

def ExpDat.Max (E : ExpDat Y) : Prop :=
  ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b (a : Y.Dat i j b), DatOk Y i j b a → a ∈ E.Dat0 i j b

variable (Y)

def ExpDat.all : ExpDat Y where
  Dat0 i j b := {a | DatOk Y i j b a}
  theta_base_equivariant _ _ _ _ ha := ha.1

theorem ExpDat.all_max : (ExpDat.all Y).Max :=
  fun _ _ _ _ _ ha => ha

theorem ExpDat.all_data_admT4 : admT4 Y (ExpDat.all Y) := by
  intro i _ j _ b k Q ψ hψ Sg hSg
  unfold ThPsi
  rw [Submodule.span_le]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨a, ha, hxa⟩ := hx
  exact (hSg ha).2.2.2 k Q ψ hψ hxa

variable {Y}

theorem ExpDat.all_data_isotypicPartsInternalDirectSum {E : ExpDat Y} (h : IsotypicPartsInternalDirectSum Y E) : IsotypicPartsInternalDirectSum Y (ExpDat.all Y) := by
  intro i hi j hj b
  obtain ⟨h1, h2, h3, h4, -, -⟩ := h i hi j hj b
  exact ⟨h1, h2, h3, h4, fun a ha => ha.2.1, fun k Q ψ hψ hu a ha => ha.2.2.1 k Q ψ hψ hu⟩

theorem ExpDat.Max.eq_all {E : ExpDat Y} (hM : E.Max) (hI : IsotypicPartsInternalDirectSum Y E) (hT : admT4 Y E) (i : X.Tw) (hi : X.NonzeroIndexPlace i)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) : E.Dat0 i j b = {a | DatOk Y i j b a} := by
  ext a
  constructor
  · intro ha
    show DatOk Y i j b a
    unfold DatOk
    refine ⟨E.theta_base_equivariant i j b a ha, (hI i hi j hj b).2.2.2.2.1 a ha,
      fun k Q ψ hψ hu => (hI i hi j hj b).2.2.2.2.2 k Q ψ hψ hu a ha, ?_⟩
    intro k Q ψ hψ x hx
    have hle := hT i hi j hj b k Q ψ hψ {a} (Set.singleton_subset_iff.mpr ha)
    exact hle (Submodule.subset_span (Set.mem_biUnion (Set.mem_singleton a) hx))
  · intro ha
    exact hM i j hj b a ha

theorem ExpDat.thSub_all (Sg0 : ∀ (i : X.Tw) (j : ℕ) (b : Bool), Set (Y.Dat i j b))
    (h : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∀ a ∈ Sg0 i j b, DatOk Y i j b a) : ThSub Y (ExpDat.all Y) Sg0 := by
  intro i j hj b
  unfold ThJ Th SgJ
  apply Submodule.span_mono
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a, h i j hj b a ha, rfl⟩

end Formalism.MainNotions.IntegralHeckeForms

namespace Formalism.MainNotions

open NumberField Formalism.BasicNotions

def TwistedAt (D : D7) (w : D.what₂.places.Pl) : Prop := D.what₂.muAt w ≠ D.what₂.mu0

theorem twistedAt_conj (D : D7) (w : D.what₂.places.Pl) : TwistedAt D (D.what₂.places.conj w) ↔ TwistedAt D w := by
  unfold TwistedAt
  rw [D.what₂.muAt_conj]

structure TwIn (D : D7) where
  E : IntegralHeckeForms.XD D
  N0 : D.ntw.Tw → ℕ
  S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)

def TwIn.Sg {D : D7} (I : TwIn D) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Set (D.nexp.Dat i j b) :=
  IntegralHeckeForms.SgJ D.nexp I.E i j b

def TwIn.Ok {D : D7} (I : TwIn D) (i : D.ntw.Tw) : Prop :=
  (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk D.nexp I.E i j b (I.Sg i j b)) ∧
  (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.BasisOf D.nexp i j b (I.Sg i j b) (I.S i j b))

def twEps (D : D7) (i : D.ntw.Tw) : ℝ := ((D.ntw.l i : ℝ) ^ 2)⁻¹

theorem twEps_pos (D : D7) (i : D.ntw.Tw) : 0 < twEps D i := by
  unfold twEps
  have hl : (0 : ℝ) < (D.ntw.l i : ℝ) := by exact_mod_cast (D.ntw.lPrime i).out.pos
  positivity

def rPrAv (D : D7) : ℕ :=
  sInf {p : ℕ | p.Prime ∧
    ¬ p ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK}

def q0Av (D : D7) : ℕ := sInf {p : ℕ | p.Prime ∧ p % (rPrAv D * LevelStarExponents.condE D) = 1 ∧ ¬ p ∣ Ideal.absNorm D.host.ccK}

def avPrimes (D : D7) : Finset ℕ :=
  letI := D.wordFin
  ((insert 3 (insert 5 (insert (D.host.g 0) (insert (D.host.g 1) (insert D.host.pde (insert D.host.pde'
    (insert (q0Av D) (Finset.univ.image fun u => (D.mem u).A.T)))))))) ∪
    (Ideal.absNorm D.host.ccK).primeFactors).filter (· ≠ 0)

def AvSet (D : D7) : Set (PlE D.host) := ⋃ p ∈ avPrimes D, placesOver D.host.E p

theorem placesOver_finite_av (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have hI : (Ideal.span {((p : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem avSet_finite (D : D7) : (AvSet D).Finite := by
  unfold AvSet
  exact Set.Finite.biUnion (Finset.finite_toSet _) fun p hp =>
    placesOver_finite_av _ p (Finset.mem_filter.mp hp).2

def AvRec (D : D7) : Finset (PlE D.host) := (avSet_finite D).toFinset

theorem mem_avRec {D : D7} (v : PlE D.host) : v ∈ AvRec D ↔ ∃ p ∈ avPrimes D, v ∈ placesOver D.host.E p := by
  simp only [AvRec, AvSet, Set.Finite.mem_toFinset, Set.mem_iUnion, exists_prop]

theorem prime_of_mem_avPrimes {D : D7} {q : ℕ} (hq : q ∈ avPrimes D) : q.Prime := by
  unfold avPrimes at hq
  rw [Finset.mem_filter] at hq
  obtain ⟨hq, hq0⟩ := hq
  rcases Finset.mem_union.mp hq with hq | hq
  · simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨u, rfl⟩
    · norm_num
    · norm_num
    · exact D.host.g_prime 0
    · exact D.host.g_prime 1
    · exact D.host.pde_prime
    · exact D.host.pde'_prime
    · have hS : {p : ℕ | p.Prime ∧ p % (rPrAv D * LevelStarExponents.condE D) = 1 ∧
          ¬ p ∣ Ideal.absNorm D.host.ccK}.Nonempty := by
        by_contra hS
        rw [Set.not_nonempty_iff_eq_empty] at hS
        exact hq0 (by unfold q0Av; rw [hS, Nat.sInf_empty])
      exact (Nat.sInf_mem hS).1
    · exact (D.mem u).A.T_prime
  · exact Nat.prime_of_mem_primeFactors hq

theorem not_mem_avRec_of_over {D : D7} {v : PlE D.host} {p : ℕ} (hp : p.Prime) (hpav : p ∉ avPrimes D)
    (hv : v ∈ placesOver D.host.E p) : v ∉ AvRec D := by
  intro hv'
  obtain ⟨q, hq, hvq⟩ := (mem_avRec v).mp hv'
  by_cases hqp : q = p
  · exact hpav (hqp ▸ hq)
  have hcop : Nat.Coprime q p := (Nat.coprime_primes (prime_of_mem_avPrimes hq) hp).mpr hqp
  have h1 : ((Nat.gcd q p : ℤ) : 𝓞 D.host.E) =
      (q : 𝓞 D.host.E) * (Nat.gcdA q p : 𝓞 D.host.E) + (p : 𝓞 D.host.E) * (Nat.gcdB q p : 𝓞 D.host.E) := by
    rw [Nat.gcd_eq_gcd_ab]
    push_cast
    ring
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one, Int.cast_one] at h1
  have hq' : ((q : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := hvq
  have hp' : ((p : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := hv
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hq') (Ideal.mul_mem_right _ _ hp')

open Classical in

def TwGoodOne (D : D7) (I : TwIn D) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : Prop :=
  IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 i (twEps D i) (I.S i) (AvRec D) Q k' (BlochKatoReduction.Gen.psiAt b ψ)

def TwGoodAt (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    I.Ok (C.twI w) ∧ TwGoodOne D I (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

abbrev TwPack (D : D7) : Type :=
  Σ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (k' : ℕ), D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ

def twPack (D : D7) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : TwPack D :=
  ⟨i, Q, k', BlochKatoReduction.Gen.psiAt b ψ⟩

def NChoicePack {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) : TwPack D :=
  twPack D (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

def TwConjAt (D : D7) (C : NChoice D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    NChoicePack C (D.what₂.places.conj w) = NChoicePack C w ∧
      (D.what₂.places.conj w ≠ w → C.sd (D.what₂.places.conj w) = !C.sd w)

theorem TwConjAt.twI_conj {D : D7} {C : NChoice D} (h : TwConjAt D C) (w : D.what₂.places.Pl)
    (hw : D.what₂.muAt w ≠ D.what₂.mu0) : C.twI (D.what₂.places.conj w) = C.twI w :=
  congrArg Sigma.fst (h w hw).1

def TwGoodE {eps : ℝ} (Fm : FamP eps) (E : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, IntegralHeckeForms.XD (Fm.D x i)) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    TwConjAt (Fm.D x i) (Fm.ex x hx i).nch ∧
      ∃ (N0 : (Fm.D x i).ntw.Tw → ℕ) (S : ∀ (i' : (Fm.D x i).ntw.Tw) (j : ℕ) (b : Bool), Finset ((Fm.D x i).nexp.Dat i' j b)),
        TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch ⟨E x hx i, N0, S⟩

def twEOf {D : D7} (T : ThData D) : IntegralHeckeForms.XD D := ⟨T.xd0, T.thetaBase_invariant_action⟩

theorem twist_data_zero_eq {D : D7} (T : ThData D) : (twEOf T).Dat0 = T.xd0 := rfl

def twE {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : IntegralHeckeForms.XD (Fm.D x i) := twEOf (Fm.ex x hx i).xd

def TwGood {eps : ℝ} (Fm : FamP eps) : Prop := TwGoodE Fm (twE Fm)

theorem psiAt_psiAt {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) :
    BlochKatoReduction.Gen.psiAt b (BlochKatoReduction.Gen.psiAt b ψ) = ψ := by
  cases b <;> simp [BlochKatoReduction.Gen.psiAt]

open Classical in

theorem exists_good_of_conditions (D : D7) (I : TwIn D) (twI : D.what₂.places.Pl → D.ntw.Tw)
    (sd : D.what₂.places.Pl → Bool) (hconds : IntegralHeckeForms.aux₃ D (BlochKatoReduction.bk0 D) I.E I.N0)
    (hset : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (twI w))
    (hI : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → I.Ok (twI w))
    (hW1 : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → D.ntw.NonzeroIndexPlace (twI w)) :
    ∃ (Q : D.what₂.places.Pl → Finset (PlE D.host)) (k' : D.what₂.places.Pl → ℕ)
      (psi' : ∀ w, D.ntw.RCG (twI w) (Q w) →* (D.ntw.Ok (twI w) (k' w))ˣ),
      (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → TwGoodOne D I (twI w) (sd w) (Q w) (k' w) (psi' w)) ∧
      ∀ w w', twI w' = twI w →
        twPack D (twI w') (sd w') (Q w') (k' w') (psi' w') = twPack D (twI w) (sd w) (Q w) (k' w) (psi' w) := by
  have hne : ∀ i, Nonempty (Σ (Q : Finset (PlE D.host)) (k' : ℕ), D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) :=
    fun i => ⟨⟨∅, 0, 1⟩⟩
  let good : ∀ i, (Σ (Q : Finset (PlE D.host)) (k' : ℕ), D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) → Prop :=
    fun i s => IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 i (twEps D i) (I.S i) (AvRec D) s.1 s.2.1 s.2.2
  let pk : ∀ i, Σ (Q : Finset (PlE D.host)) (k' : ℕ), D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ :=
    fun i => @Classical.epsilon _ (hne i) (good i)
  have hpk : ∀ i, (∃ s, good i s) → good i (pk i) := fun i h => Classical.epsilon_spec h
  refine ⟨fun w => (pk (twI w)).1, fun w => (pk (twI w)).2.1,
    fun w => BlochKatoReduction.Gen.psiAt (sd w) (pk (twI w)).2.2, ?_, ?_⟩
  · intro w hw
    have hP : ∃ s, good (twI w) s := by
      obtain ⟨Q, k', ψ, hg⟩ := hconds (twI w) (hW1 w hw) (hset w hw) (twEps D (twI w)) (twEps_pos D (twI w))
        (hI w hw).1 (I.S (twI w)) (hI w hw).2 (AvRec D)
      exact ⟨⟨Q, k', ψ⟩, hg⟩
    unfold TwGoodOne
    rw [psiAt_psiAt]
    exact hpk _ hP
  · intro w w' h
    unfold twPack
    rw [psiAt_psiAt, psiAt_psiAt]
    show (⟨twI w', pk (twI w')⟩ : TwPack D) = ⟨twI w, pk (twI w)⟩
    rw [h]

end Formalism.MainNotions

end
