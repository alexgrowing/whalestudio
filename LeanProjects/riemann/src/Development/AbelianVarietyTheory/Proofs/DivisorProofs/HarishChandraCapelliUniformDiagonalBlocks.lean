import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMonicOperatorPolynomials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyMapOfSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAdjoinStatement

open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.LeviHC.CapAlg

open GlobalTheory.LeviHC.MidBlock (stab mem_stab comm_qdet qdet_map)

theorem twoBlocks : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (r m : ℕ) (X : Fin (r + m) → Fin (r + m) → Module.End ℂ M), Formalism.REAL.GlRel X → ∀ M' K : Submodule ℂ M, (∀ i j, ∀ x ∈ M', X i j x ∈ M') → (∀ (p : Fin r) (q : Fin m), ∀ x ∈ M', X (Fin.castAdd m p) (Fin.natAdd r q) x ∈ K) → (∀ p q : Fin r, ∀ x ∈ K, X (Fin.castAdd m p) (Fin.castAdd m q) x ∈ K) → (∀ p q : Fin m, ∀ x ∈ K, X (Fin.natAdd r p) (Fin.natAdd r q) x ∈ K) → ∀ v ∈ M', GlobalTheory.LeviHC.FinMod ⊥ (Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet X))) v → GlobalTheory.LeviHC.FinMod K (Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)))) v ∧ GlobalTheory.LeviHC.FinMod K (Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)))) v := by
  intro M _ _ r m X hX M' K hM hup hK1 hK2 v hv hfin
  let X' : Fin (r + m) → Fin (r + m) → stab M' := fun a b => ⟨X a b, mem_stab.2 (hM a b)⟩
  have hX' : Formalism.REAL.GlRel X' := by
    intro a b c d
    apply Subtype.ext
    have := hX a b c d
    split_ifs at this ⊢ <;> simpa [X'] using this
  have inj1 : Function.Injective (Fin.castAdd m : Fin r → Fin (r + m)) :=
    fun a b h => Fin.ext (by simpa using congrArg Fin.val h)
  have inj2 : Function.Injective (Fin.natAdd r : Fin m → Fin (r + m)) :=
    fun a b h => Fin.ext (by simpa using congrArg Fin.val h)
  have hX1 : Formalism.REAL.GlRel fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q) :=
    GlobalTheory.CapHC.glRel_restrict hX _ inj1
  have hX2 : Formalism.REAL.GlRel fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q) :=
    GlobalTheory.CapHC.glRel_restrict hX _ inj2
  set q₁ : ℂ → Module.End ℂ M := fun u => Formalism.REAL.qdet (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)) u
    with hq₁
  set q₂ : ℂ → Module.End ℂ M := fun u => Formalism.REAL.qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u
    with hq₂
  have e : ∀ u, ∀ x ∈ M', Formalism.REAL.qdet X u x - q₂ u (q₁ (u - m) x) ∈ K := by
    intro u x hx
    have h := GlobalTheory.LeviHC.MidBlock.upperSpan_maps (K := K) X' (fun p q x hx => hup p q x hx)
      (GlobalTheory.CapHC.two_block X' hX' u) x hx
    change (stab M').val (_ - _ * _) x ∈ K at h
    rw [map_sub, map_mul, qdet_map, qdet_map, qdet_map] at h
    exact h
  have c12 : ∀ u u', Commute (q₁ u) (q₂ u') := fun u u' => (GlobalTheory.CapHC.qdet_comm hX u' u).symm
  have c11 : ∀ u u', Commute (q₁ u) (q₁ u') := fun u u' =>
    comm_qdet (fun a b => Formalism.REAL.qDetCentral _ r _ hX1 u a b) u'
  have c22 : ∀ u u', Commute (q₂ u) (q₂ u') := fun u u' =>
    comm_qdet (fun a b => Formalism.REAL.qDetCentral _ m _ hX2 u a b) u'
  have constantCoeff_threeGroupsFirstVariables_eq_zero : ∀ u u', Commute (Formalism.REAL.qdet X u) (q₁ u') := fun u u' =>
    comm_qdet (fun a b => Formalism.REAL.qDetCentral _ _ _ hX u _ _) u'
  have constantCoeff_threeGroupsSecondVariables_eq_zero : ∀ u u', Commute (Formalism.REAL.qdet X u) (q₂ u') := fun u u' =>
    comm_qdet (fun a b => Formalism.REAL.qDetCentral _ _ _ hX u _ _) u'
  have mon1 : ∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, q₁ u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i := by
    obtain ⟨c, hc1, hc⟩ := GlobalTheory.qdet_polyMap_monic (Module.End ℂ M) r (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q))
    exact ⟨r, c, hc1, hc⟩
  have mon2 : ∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, q₂ u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i := by
    obtain ⟨c, hc1, hc⟩ := GlobalTheory.qdet_polyMap_monic (Module.End ℂ M) m (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q))
    exact ⟨m, c, hc1, hc⟩
  have mon1' := GlobalTheory.LeviHC.MidThree.monic_shift (m : ℂ) mon1
  have sM : ∀ {n : ℕ} (f : Fin n → Fin (r + m)) (u : ℂ), ∀ x ∈ M',
      Formalism.REAL.qdet (fun p q : Fin n => X (f p) (f q)) u x ∈ M' :=
    fun f u => mem_stab.1 (GlobalTheory.LeviHC.MidBlock.qdet_mem (stab M') (fun a b => mem_stab.2 (hM _ _)) u)
  have sMX : ∀ u, ∀ x ∈ M', Formalism.REAL.qdet X u x ∈ M' :=
    fun u => mem_stab.1 (GlobalTheory.LeviHC.MidBlock.qdet_mem (stab M') (fun a b => mem_stab.2 (hM a b)) u)
  have sK1 : ∀ u, ∀ x ∈ K, q₁ u x ∈ K :=
    fun u => mem_stab.1 (GlobalTheory.LeviHC.MidBlock.qdet_mem (stab K) (fun a b => mem_stab.2 (hK1 a b)) u)
  have sK2 : ∀ u, ∀ x ∈ K, q₂ u x ∈ K :=
    fun u => mem_stab.1 (GlobalTheory.LeviHC.MidBlock.qdet_mem (stab K) (fun a b => mem_stab.2 (hK2 a b)) u)
  have hr1 : Set.range (fun u => q₁ (u - m)) = Set.range q₁ := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩; exact ⟨u + m, by simp⟩
  refine ⟨?_, ?_⟩
  · have h := GlobalTheory.LeviHC.FactorMod.finMod_factor M M' K (Formalism.REAL.qdet X) (fun u => q₁ (u - m)) q₂ mon1' mon2
      (fun u u' => c11 _ _) c22 (fun u u' => c12 _ _) constantCoeff_threeGroupsSecondVariables_eq_zero
      (fun u x hx => ⟨sMX u x hx, sM _ _ x hx, sM _ _ x hx⟩) (fun u x hx => sK1 _ x hx)
      (fun u x hx => by
        have h := e u x hx
        have hc := LinearMap.congr_fun (c12 (u - m) u).eq x
        simp only [Module.End.mul_apply] at hc
        rwa [hc]) v hv hfin
    rwa [hr1] at h
  · exact GlobalTheory.LeviHC.FactorMod.finMod_factor M M' K (Formalism.REAL.qdet X) q₂ (fun u => q₁ (u - m)) mon2 mon1'
      c22 (fun u u' => c11 _ _) (fun u u' => (c12 _ _).symm) (fun u u' => constantCoeff_threeGroupsFirstVariables_eq_zero _ _)
      (fun u x hx => ⟨sMX u x hx, sM _ _ x hx, sM _ _ x hx⟩) (fun u x hx => sK2 _ x hx) e v hv hfin

theorem finDim : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (c : ℕ → Module.End ℂ V) (g : ℂ → Module.End ℂ V), (∀ u, g u = ∑ i ∈ Finset.range (n + 1), u ^ i • c i) → (∀ u u', Commute (g u) (g u')) → ∀ (w : V) (P : ℂ → Polynomial ℂ), (∀ u, P u ≠ 0) → (∀ u, Polynomial.aeval (g u) (P u) w = 0) → FiniteDimensional ℂ (Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range g), y = b w}) := GlobalTheory.T.finiteDimensional_span_adjoin_apply_of_annihilating

theorem exists_poly {V : Type} [AddCommGroup V] [Module ℂ V] (K : Submodule ℂ V) (A : Subalgebra ℂ (Module.End ℂ V))
    {T : Module.End ℂ V} (hT : T ∈ A) (w : V) (hf : FinMod K A w) :
    ∃ p : Polynomial ℂ, p ≠ 0 ∧ Polynomial.aeval T p w ∈ K := by
  unfold FinMod at hf
  set W := Submodule.span ℂ {y : V ⧸ K | ∃ a ∈ A, y = K.mkQ (a w)}
  let f : ℕ → W := fun k => ⟨K.mkQ ((T ^ k) w), Submodule.subset_span ⟨T ^ k, A.pow_mem hT k, rfl⟩⟩
  have hnli : ¬ LinearIndependent ℂ f := Module.Finite.not_linearIndependent_of_infinite f
  obtain ⟨s, c, hs, i, hi, hci⟩ := not_linearIndependent_iff.1 hnli
  refine ⟨∑ k ∈ s, Polynomial.monomial k (c k), fun h0 => hci ?_, ?_⟩
  · have := congrArg (fun p : Polynomial ℂ => p.coeff i) h0
    simpa [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hi] using this
  · have ev : (Polynomial.aeval T (∑ k ∈ s, Polynomial.monomial k (c k))) w = ∑ k ∈ s, c k • (T ^ k) w := by
      simp [map_sum, Polynomial.aeval_monomial, Module.algebraMap_end_apply]
    have := congrArg Subtype.val hs
    simp only [Submodule.coe_sum, Submodule.coe_smul, f, ZeroMemClass.coe_zero] at this
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ev, map_sum]
    simpa using this

def liftHom (I : Type) (M : Type) [AddCommGroup M] [Module ℂ M] : Module.End ℂ M →ₐ[ℂ] Module.End ℂ (I → M) where
  toFun f := f.compLeft I
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := by
    ext g i
    simp [Module.algebraMap_end_apply]

theorem glRel_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) {n : ℕ}
    {X : Fin n → Fin n → A} (hX : Formalism.REAL.GlRel X) : Formalism.REAL.GlRel fun i j => φ (X i j) := by
  intro a b c d
  have := congrArg φ (hX a b c d)
  simp only [map_sub, map_mul] at this
  rw [this]
  split_ifs <;> simp

theorem stab_aeval {M : Type} [AddCommGroup M] [Module ℂ M] {K : Submodule ℂ M} {T : Module.End ℂ M}
    (hT : ∀ x ∈ K, T x ∈ K) (p : Polynomial ℂ) : ∀ x ∈ K, Polynomial.aeval T p x ∈ K := by
  have h : Polynomial.aeval T p ∈ stab K :=
    Algebra.adjoin_le (s := {T}) (by rintro _ rfl; exact mem_stab.2 hT) (Polynomial.aeval_mem_adjoin_singleton ℂ T)
  exact mem_stab.1 h

theorem core (M : Type) [AddCommGroup M] [Module ℂ M] (r m : ℕ) (X : Fin (r + m) → Fin (r + m) → Module.End ℂ M)
    (hX : Formalism.REAL.GlRel X) (M' K : Submodule ℂ M) (hM : ∀ i j, ∀ x ∈ M', X i j x ∈ M')
    (hup : ∀ (p : Fin r) (q : Fin m), ∀ x ∈ M', X (Fin.castAdd m p) (Fin.natAdd r q) x ∈ K)
    (hK1 : ∀ p q : Fin r, ∀ x ∈ K, X (Fin.castAdd m p) (Fin.castAdd m q) x ∈ K)
    (hK2 : ∀ p q : Fin m, ∀ x ∈ K, X (Fin.natAdd r p) (Fin.natAdd r q) x ∈ K)
    (Q : ℂ → Polynomial ℂ) (hQ : ∀ u, Q u ≠ 0) :
    ∃ q : ℂ → Polynomial ℂ, (∀ u, q u ≠ 0) ∧ ∀ v ∈ M', (∀ u, Polynomial.aeval (Formalism.REAL.qdet X u) (Q u) v = 0) →
      ∀ u, Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)) u) (q u) v ∈ K ∧
        Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u) (q u) v ∈ K := by

  let I := {v : M // v ∈ M' ∧ ∀ u, Polynomial.aeval (Formalism.REAL.qdet X u) (Q u) v = 0}
  let φ := liftHom I M
  let Y : Fin (r + m) → Fin (r + m) → Module.End ℂ (I → M) := fun i j => φ (X i j)
  have hY : Formalism.REAL.GlRel Y := glRel_map φ hX
  let M'' : Submodule ℂ (I → M) := Submodule.pi Set.univ fun _ => M'
  let K'' : Submodule ℂ (I → M) := Submodule.pi Set.univ fun _ => K
  have memM : ∀ g : I → M, g ∈ M'' ↔ ∀ i, g i ∈ M' := fun g => by simp [M'', Submodule.mem_pi]
  have memK : ∀ g : I → M, g ∈ K'' ↔ ∀ i, g i ∈ K := fun g => by simp [K'', Submodule.mem_pi]
  let w : I → M := fun i => i.1
  have hw : w ∈ M'' := (memM w).2 fun i => i.2.1
  have hqY : ∀ {n : ℕ} (f : Fin n → Fin (r + m)) (u : ℂ),
      Formalism.REAL.qdet (fun p q => Y (f p) (f q)) u = φ (Formalism.REAL.qdet (fun p q => X (f p) (f q)) u) :=
    fun f u => (qdet_map φ _ u).symm
  have hq0 : ∀ u, Formalism.REAL.qdet Y u = φ (Formalism.REAL.qdet X u) := fun u => (qdet_map φ X u).symm

  have hfin : FinMod ⊥ (Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet Y))) w := by
    obtain ⟨c, -, hc⟩ := GlobalTheory.qdet_polyMap_monic (Module.End ℂ M) (r + m) X
    have hd := finDim (I → M) (r + m) (fun i => φ (c i)) (Formalism.REAL.qdet Y)
      (fun u => by rw [hq0 u]; simp only [hc u, map_sum, map_smul])
      (fun u u' => by
        rw [hq0 u, hq0 u']
        exact (comm_qdet (fun a b => Formalism.REAL.qDetCentral _ _ _ hX u a b) u').map φ)
      w Q hQ (fun u => by
        rw [hq0 u, Polynomial.aeval_algHom_apply]
        funext i
        exact i.2.2 u)
    unfold FinMod
    have e : Submodule.span ℂ {y : (I → M) ⧸ (⊥ : Submodule ℂ (I → M)) |
        ∃ a ∈ Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet Y)), y = (⊥ : Submodule ℂ (I → M)).mkQ (a w)} =
        (Submodule.span ℂ {y | ∃ b ∈ Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet Y)), y = b w}).map
          (⊥ : Submodule ℂ (I → M)).mkQ := by
      rw [Submodule.map_span]
      congr 1
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ⟨a w, ⟨a, ha, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩; exact ⟨a, ha, rfl⟩
    rw [e]
    infer_instance
  obtain ⟨h1, h2⟩ := twoBlocks (I → M) r m Y hY M'' K''
    (fun i j g hg => (memM _).2 fun k => hM i j _ ((memM g).1 hg k))
    (fun p q g hg => (memK _).2 fun k => hup p q _ ((memM g).1 hg k))
    (fun p q g hg => (memK _).2 fun k => hK1 p q _ ((memK g).1 hg k))
    (fun p q g hg => (memK _).2 fun k => hK2 p q _ ((memK g).1 hg k)) w hw hfin
  have P1 : ∀ u, ∃ p : Polynomial ℂ, p ≠ 0 ∧ Polynomial.aeval
      (Formalism.REAL.qdet (fun p q : Fin r => Y (Fin.castAdd m p) (Fin.castAdd m q)) u) p w ∈ K'' :=
    fun u => exists_poly K'' _ (Algebra.subset_adjoin (Set.mem_range_self u)) w h1
  have P2 : ∀ u, ∃ p : Polynomial ℂ, p ≠ 0 ∧ Polynomial.aeval
      (Formalism.REAL.qdet (fun p q : Fin m => Y (Fin.natAdd r p) (Fin.natAdd r q)) u) p w ∈ K'' :=
    fun u => exists_poly K'' _ (Algebra.subset_adjoin (Set.mem_range_self u)) w h2
  choose p₁ hp₁ hk₁ using P1
  choose p₂ hp₂ hk₂ using P2
  refine ⟨fun u => p₁ u * p₂ u, fun u => mul_ne_zero (hp₁ u) (hp₂ u), fun v hv hQv u => ?_⟩
  let i : I := ⟨v, hv, hQv⟩
  have e1 : Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)) u) (p₁ u) v ∈ K := by
    have := (memK _).1 (hk₁ u) i
    rwa [hqY (fun p => Fin.castAdd m p) u, Polynomial.aeval_algHom_apply] at this
  have e2 : Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u) (p₂ u) v ∈ K := by
    have := (memK _).1 (hk₂ u) i
    rwa [hqY (fun p => Fin.natAdd r p) u, Polynomial.aeval_algHom_apply] at this
  have s1 : ∀ x ∈ K, Formalism.REAL.qdet (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)) u x ∈ K :=
    mem_stab.1 (GlobalTheory.LeviHC.MidBlock.qdet_mem (stab K) (fun a b => mem_stab.2 (hK1 a b)) u)
  have s2 : ∀ x ∈ K, Formalism.REAL.qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u x ∈ K :=
    mem_stab.1 (GlobalTheory.LeviHC.MidBlock.qdet_mem (stab K) (fun a b => mem_stab.2 (hK2 a b)) u)
  refine ⟨?_, ?_⟩ <;> dsimp only
  · rw [mul_comm, Polynomial.aeval_mul, Module.End.mul_apply]
    exact stab_aeval s1 _ _ e1
  · rw [Polynomial.aeval_mul, Module.End.mul_apply]
    exact stab_aeval s2 _ _ e2

theorem qdet_cast {A : Type} [Ring A] [Algebra ℂ A] {k m : ℕ} (h : k = m) (Z : Fin m → Fin m → A) (u : ℂ) :
    Formalism.REAL.qdet (fun p q : Fin k => Z (Fin.cast h p) (Fin.cast h q)) u = Formalism.REAL.qdet Z u := by
  subst h; rfl

theorem capalg : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (a r : ℕ) (hr : r ≤ a) (X : Fin a → Fin a → Module.End ℂ M), Formalism.REAL.GlRel X → ∀ M' K : Submodule ℂ M, (∀ i j, ∀ x ∈ M', X i j x ∈ M') → (∀ i j : Fin a, (i : ℕ) < r → r ≤ (j : ℕ) → ∀ x ∈ M', X i j x ∈ K) → (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) → ∀ x ∈ K, X i j x ∈ K) → ∀ Q : ℂ → Polynomial ℂ, (∀ u, Q u ≠ 0) → ∃ q : ℂ → Polynomial ℂ, (∀ u, q u ≠ 0) ∧ ∀ v ∈ M', (∀ u, Polynomial.aeval (Formalism.REAL.qdet X u) (Q u) v = 0) → ∀ u, Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin r => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inl p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inl p'))) u) (q u) v ∈ K ∧ Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin (a - r) => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p'))) u) (q u) v ∈ K := by
  intro M _ _ a r hr X hX M' K hM hup hK Q hQ
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hr
  obtain ⟨q, hq, h⟩ := core M r m X hX M' K hM
    (fun p q x hx => hup _ _ (by simp) (by simp) x hx)
    (fun p q x hx => hK _ _ (by simp) x hx) (fun p q x hx => hK _ _ (by simp) x hx) Q hQ
  refine ⟨q, hq, fun v hv hQv u => ?_⟩
  obtain ⟨h1, h2⟩ := h v hv hQv u
  have e1 : (fun p p' : Fin r => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inl p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inl p'))) =
      fun p q => X (Fin.castAdd m p) (Fin.castAdd m q) := by
    funext p p'
    congr 1 <;> exact Fin.ext (by simp)
  have hm : r + m - r = m := by omega
  have e2 : (fun p p' : Fin (r + m - r) => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p'))) =
      fun p p' => (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) (Fin.cast hm p) (Fin.cast hm p') := by
    funext p p'
    congr 1 <;> exact Fin.ext (by simp)
  have e3 : Formalism.REAL.qdet (fun p p' : Fin (r + m - r) => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p))
      (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p'))) u = Formalism.REAL.qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u := by
    rw [e2]; exact qdet_cast hm (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u
  rw [e1, e3]
  exact ⟨h1, h2⟩

end GlobalTheory.LeviHC.CapAlg
