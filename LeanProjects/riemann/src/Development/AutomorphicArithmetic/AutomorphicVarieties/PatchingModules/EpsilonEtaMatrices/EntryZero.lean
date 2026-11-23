import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.MemW1IffPattern
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.OneCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.HomCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FiltCount

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem filt_ht {Z Y ι : Type} [AddCommGroup Z] [AddCommGroup Y] [Fintype ι] (ht : ι → ℕ) (f : ι → Z →+ Y)
    (P : ι → Set Y) (h0 : ∀ z, (∀ i, f i z = 0) → z = 0) (hP : ∀ i, (P i).Finite)
    (hf : ∀ i z, (∀ j, ht j < ht i → f j z = 0) → f i z ∈ P i) : Finite Z ∧ Nat.card Z ≤ ∏ i, (P i).ncard := by
  classical
  let σ := Fintype.equivFin ι
  let key : ι → Lex (ℕ × Fin (Fintype.card ι)) := fun i => toLex (ht i, σ i)
  have hkey : Function.Injective key := fun a b hab =>
    σ.injective (by simpa [key] using congrArg (fun p => (ofLex p).2) hab)
  letI : LinearOrder ι := LinearOrder.lift' key hkey
  let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  have hmono : ∀ a b : Fin (Fintype.card ι), ht (e a) < ht (e b) → a < b := by
    intro a b hab
    have : e a < e b := by
      show key (e a) < key (e b)
      exact Prod.Lex.lt_iff.mpr (Or.inl hab)
    exact e.lt_iff_lt.mp this
  obtain ⟨hfin, hcard⟩ := filtCount Z Y (Fintype.card ι) (fun a => f (e a)) (fun a => P (e a))
    (fun z hz => h0 z (fun i => by simpa using hz (e.symm i)))
    (fun a => hP _)
    (fun a z hz => hf (e a) z (fun j hj => by
      simpa using hz (e.symm j) (hmono _ _ (by simpa using hj))))
  refine ⟨hfin, hcard.trans_eq ?_⟩
  exact Equiv.prod_comp e.toEquiv (fun i => (P i).ncard)

private theorem conj_entry {R : Type} [CommRing R] {n : ℕ} (T B T' : Matrix (Fin n) (Fin n) R)
    (hT : ∀ i j, j < i → T i j = 0) (hT' : ∀ i j, j < i → T' i j = 0) (i j : Fin n)
    (hB : ∀ p q, i ≤ p → q ≤ j → (p ≠ i ∨ q ≠ j) → B p q = 0) : (T * B * T') i j = T i i * B i j * T' j j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro p _ hp
      by_cases hpi : i ≤ p
      · rw [hB p j hpi le_rfl (Or.inl hp)]
        ring
      · rw [hT i p (not_le.mp hpi)]
        ring
    · simp
  · intro q _ hq
    by_cases hqj : q ≤ j
    · rw [Matrix.mul_apply, Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro p _
      by_cases hpi : i ≤ p
      · rw [hB p q hpi hqj (Or.inr hq)]
        ring
      · rw [hT i p (not_le.mp hpi)]
        ring
    · rw [hT' q j (not_le.mp hqj)]
      ring
  · simp

private def co (X : Type) [CommRing X] {g : ℕ} (o : Option (Fin g)) : DD X g →+ X where
  toFun y := o.elim y.a y.ep
  map_zero' := by cases o <;> rfl
  map_add' y z := by cases o <;> rfl

private theorem co_mul {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g : ℕ} (o : Option (Fin g)) (c c' : A)
    (y : DD X g) : co X o (algebraMap A (DD X g) c * y * algebraMap A (DD X g) c') = (c * c') • co X o y := by
  cases o with
  | none =>
    show algebraMap A X c * y.a * algebraMap A X c' = (c * c') • y.a
    rw [Algebra.smul_def, map_mul]
    ring
  | some j =>
    show (algebraMap A X c * y.a) * 0 + (algebraMap A X c * y.ep j + 0 * y.a) * algebraMap A X c' =
      (c * c') • y.ep j
    rw [Algebra.smul_def, map_mul]
    ring

private theorem adic_mul {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f f' : D → R}
    (h : AdicCont I f) (h' : AdicCont I f') : AdicCont I fun g => f g * f' g := by
  intro N
  have e : (fun g => Ideal.Quotient.mk (I ^ N) (f g * f' g)) =
      fun g => Ideal.Quotient.mk (I ^ N) (f g) * Ideal.Quotient.mk (I ^ N) (f' g) :=
    funext fun g => map_mul _ _ _
  show IsLocallyConstant (fun g => Ideal.Quotient.mk (I ^ N) (f g * f' g))
  rw [e]
  exact (h N).comp₂ (h' N) _

private theorem adic_sum {D R ι : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} (s : Finset ι) {f : ι → D → R}
    (h : ∀ i, AdicCont I (f i)) : AdicCont I fun g => ∑ i ∈ s, f i g := by
  classical
  intro N
  show IsLocallyConstant (fun g => Ideal.Quotient.mk (I ^ N) (∑ i ∈ s, f i g))
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, map_zero]
    exact IsLocallyConstant.const 0
  · intro a s ha ih
    have e : (fun g => Ideal.Quotient.mk (I ^ N) (∑ i ∈ insert a s, f i g)) =
        fun g => Ideal.Quotient.mk (I ^ N) (f a g) + Ideal.Quotient.mk (I ^ N) (∑ i ∈ s, f i g) :=
      funext fun g => by rw [Finset.sum_insert ha, map_add]
    rw [e]
    exact (h a N).comp₂ ih _

private theorem psi_cont {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) (i : Fin n) :
    AdicCont (IsLocalRing.maximalIdeal x.A) fun g => (x.ψ v i g : x.A) := by
  have e : (fun g => (x.ψ v i g : x.A)) = fun g => ∑ q, (∑ p, (((x.w v)⁻¹ : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A) i p *
      mat x.ρ (F.φ v g) p q) * (x.w v : Matrix (Fin n) (Fin n) x.A) q i := funext fun g => ((x.tri v g).2 i).symm
  rw [e]
  exact adic_sum _ fun q => adic_mul (adic_sum _ fun p => adic_mul (fun N => IsLocallyConstant.const _)
    fun N => (x.cont p q N).comp_continuous (F.φ_cont v)) fun N => IsLocallyConstant.const _

private theorem pair_count {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) (d : ℕ)
    (hL : LocCount (F.Gv v) (F.ε.comp (F.η.ker.subtype.comp (F.φ v))) d) (i j : Fin n) (hij : i < j) :
    ∃ C : ℕ, ∀ m, {z : F.Gv v → x.Am m | IsLocallyConstant z ∧ ∀ g h, z (g * h) =
        z g + ((x.ψ v i g : x.A) * (x.ψ v j g⁻¹ : x.A)) • z h}.Finite ∧
      {z : F.Gv v → x.Am m | IsLocallyConstant z ∧ ∀ g h, z (g * h) =
        z g + ((x.ψ v i g : x.A) * (x.ψ v j g⁻¹ : x.A)) • z h}.ncard ≤ Nat.card x.K ^ (m * (1 + d) + C) := by
  let χ : F.Gv v →* x.Aˣ := x.ψ v i * (x.ψ v j)⁻¹
  have hχ : ∀ g, ((χ g : x.Aˣ) : x.A) = (x.ψ v i g : x.A) * (x.ψ v j g⁻¹ : x.A) := by
    intro g
    simp [χ, map_inv]
  have hcont : AdicCont (IsLocalRing.maximalIdeal x.A) fun g => ((χ g : x.Aˣ) : x.A) := by
    have hinv : AdicCont (IsLocalRing.maximalIdeal x.A) fun g : F.Gv v => (x.ψ v j g⁻¹ : x.A) :=
      fun N => (psi_cont x v j N).comp_continuous continuous_inv
    have := adic_mul (psi_cont x v i) hinv
    simp_rw [hχ]
    exact this
  have hne : ∃ g, ((χ g : x.Aˣ) : x.A) ≠
      algebraMap ℤ_[l] x.A ((F.ε.comp (F.η.ker.subtype.comp (F.φ v)) g : ℤ_[l]ˣ) : ℤ_[l]) := by
    by_contra hall
    push_neg at hall
    apply (x.N1 v).2 i j hij
    refine MonoidHom.ext fun g => Units.ext ?_
    have h1 := hall g
    rw [hχ] at h1
    have h2 : ((x.ψ v j g : x.Aˣ) : x.A) * (x.ψ v j g⁻¹ : x.A) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    have h3 : ((F.eps ℤ_[l] x.A ((F.φ v) g) : x.Aˣ) : x.A) =
        algebraMap ℤ_[l] x.A ((F.ε.comp (F.η.ker.subtype.comp (F.φ v)) g : ℤ_[l]ˣ) : ℤ_[l]) := by
      rfl
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
    rw [h3, ← h1]
    linear_combination (-((x.ψ v i g : x.Aˣ) : x.A)) * h2
  obtain ⟨C, hC⟩ := oneCount l F n x (F.Gv v) _ d χ hL hcont hne
  refine ⟨C, fun m => ?_⟩
  simp only [hχ] at hC
  exact hC m

private noncomputable def crd {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X]
    [Algebra x.A X] (v : F.Vl) (o : Option (Fin k.g)) (i j : Fin n) : k.Zb X v →+ (F.Gv v → X) :=
  AddMonoidHom.mk' (fun β g => co X o ((k.wi1 X v * (β.1 g : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) i j))
    fun β β' => funext fun g => by
      simp only [AddSubgroup.coe_add, Pi.add_apply, Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply,
        map_add]

private theorem crd_coc {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X]
    [Algebra x.A X] (v : F.Vl) (o : Option (Fin k.g)) (i j : Fin n) (β : k.Zb X v)
    (hB : ∀ g p q, i ≤ p → q ≤ j → (p ≠ i ∨ q ≠ j) →
      (k.wi1 X v * (β.1 g : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) p q = 0) :
    IsLocallyConstant (crd k X v o i j β) ∧ ∀ g h, crd k X v o i j β (g * h) =
      crd k X v o i j β g + ((x.ψ v i g : x.A) * (x.ψ v j g⁻¹ : x.A)) • crd k X v o i j β h := by
  obtain ⟨hlc, hcoc, -, -⟩ := β.2
  have hρ := UpperTheory.V.Pa.rho1 l F n x k X
  have ht := (UpperTheory.V.Pa.tri l F n x k X v).1
  have hw' : ∀ M : Matrix (Fin n) (Fin n) (DD X k.g), k.w1 X v * (k.wi1 X v * M) = M := by
    intro M
    rw [← mul_assoc, (hρ.2.2.2.1 v).2, one_mul]
  refine ⟨?_, ?_⟩
  · exact hlc.comp fun b : k.M1 X =>
      co X o ((k.wi1 X v * (b : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) i j)
  · intro g h
    show co X o ((k.wi1 X v * (β.1 (g * h) : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) i j) =
      co X o ((k.wi1 X v * (β.1 g : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) i j) +
      ((x.ψ v i g : x.A) * (x.ψ v j g⁻¹ : x.A)) •
        co X o ((k.wi1 X v * (β.1 h : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) i j)
    rw [hcoc g h]
    have hsplit : k.wi1 X v * (k.ρ1 X (F.φ v g) * (β.1 h : Matrix (Fin n) (Fin n) (DD X k.g)) *
        k.ρ1 X (F.φ v g)⁻¹) * k.w1 X v =
        (k.wi1 X v * k.ρ1 X (F.φ v g) * k.w1 X v) *
          (k.wi1 X v * (β.1 h : Matrix (Fin n) (Fin n) (DD X k.g)) * k.w1 X v) *
          (k.wi1 X v * k.ρ1 X (F.φ v g⁻¹) * k.w1 X v) := by
      rw [map_inv]
      simp only [mul_assoc, hw']
    rw [mul_add, add_mul, Matrix.add_apply, map_add, hsplit,
      conj_entry _ _ _ (ht g).1 (ht g⁻¹).1 i j (hB h), (ht g).2.1 i, (ht g⁻¹).2.1 j, co_mul]

private abbrev Idx {n : ℕ} (ty : Fin n → Bool) (g : ℕ) : Type :=
  Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2 ∧ ty p.1 = ty p.2} ⊕ Fin g × {p : Fin n × Fin n // p.1 < p.2 ∧ ty p.1 ≠ ty p.2}

private def pos {n : ℕ} {ty : Fin n → Bool} {g : ℕ} : Idx ty g → Option (Fin g) × Fin n × Fin n
  | .inl i => (none, i, i)
  | .inr (.inl p) => (none, p.1)
  | .inr (.inr p) => (some p.1, p.2.1)

private theorem entry_zero {X : Type} [CommRing X] {n g : ℕ} {ty : Fin n → Bool} (B : Matrix (Fin n) (Fin n) (DD X g))
    (h1 : ∀ i j, j < i → B i j = 0) (h2 : TyPat ty B) (p q : Fin n)
    (h : ∀ t : Idx ty g, (pos t).2 = (p, q) → co X (pos t).1 (B (pos t).2.1 (pos t).2.2) = 0) : B p q = 0 := by
  obtain ⟨a1, a2, a3, a4⟩ := h2 p q
  rcases lt_trichotomy p q with c | rfl | c
  · by_cases s : ty p = ty q
    · exact DD.ext (h (.inr (.inl ⟨(p, q), c, s⟩)) rfl) (a3 s) a1 a2
    · exact DD.ext (a4 s) (funext fun m => h (.inr (.inr (m, ⟨(p, q), c, s⟩))) rfl) a1 a2
  · exact DD.ext (h (.inl p) rfl) (a3 rfl) a1 a2
  · exact h1 p q c

theorem UpperTheory.V.Pa.locV :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (v : F.Vl) (d d' : ℕ), LocCount (F.Gv v) (F.ε.comp (F.η.ker.subtype.comp (F.φ v))) d → LocAb l (F.Gv v) (F.Iv v) d' → ∃ C : ℕ, ∀ m, Finite (k.Zb (x.Am m) v) ∧ Nat.card (k.Zb (x.Am m) v) ≤ Nat.card x.K ^ (m * (n * (d' + 1) + nu n x.a k.g * (1 + d)) + C) := by
  intro l _ F n x k v d d' hL hA
  classical
  have hpc : ∀ p : Fin n × Fin n, p.1 < p.2 → ∃ C : ℕ, ∀ m,
      {z : F.Gv v → x.Am m | IsLocallyConstant z ∧ ∀ g h, z (g * h) =
        z g + ((x.ψ v p.1 g : x.A) * (x.ψ v p.2 g⁻¹ : x.A)) • z h}.Finite ∧
      {z : F.Gv v → x.Am m | IsLocallyConstant z ∧ ∀ g h, z (g * h) =
        z g + ((x.ψ v p.1 g : x.A) * (x.ψ v p.2 g⁻¹ : x.A)) • z h}.ncard ≤
        Nat.card x.K ^ (m * (1 + d) + C) :=
    fun p hp => pair_count x v d hL p.1 p.2 hp
  let Cof : Idx (x.ty v) k.g → ℕ := fun t => match t with
    | .inl _ => 0
    | .inr (.inl p) => Classical.choose (hpc p.1 p.2.1)
    | .inr (.inr p) => Classical.choose (hpc p.2.1 p.2.2.1)
  refine ⟨∑ t, Cof t, fun m => ?_⟩
  let B : k.Zb (x.Am m) v → F.Gv v → Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) := fun z g =>
    k.wi1 (x.Am m) v * ((z.1 g : k.M1 (x.Am m)) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) *
      k.w1 (x.Am m) v
  have hBtri : ∀ z g, ∀ i j, j < i → B z g i j = 0 := fun z g => z.2.2.2.1 g
  have hBty : ∀ z g, TyPat (x.ty v) (B z g) := fun z g =>
    ((UpperTheory.V.Pa.tri l F n x k (x.Am m) v).2 _).mp (z.1 g).2
  let Sh : Set (F.Gv v → x.Am m) := {z | IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + z h) ∧
    ∀ g ∈ muG l (F.Gv v), z g = 0}
  let Sp : Fin n → Fin n → Set (F.Gv v → x.Am m) := fun i j => {z | IsLocallyConstant z ∧ ∀ g h,
    z (g * h) = z g + ((x.ψ v i g : x.A) * (x.ψ v j g⁻¹ : x.A)) • z h}
  let P : Idx (x.ty v) k.g → Set (F.Gv v → x.Am m) := fun t => match t with
    | .inl _ => Sh
    | .inr (.inl p) => Sp p.1.1 p.1.2
    | .inr (.inr p) => Sp p.2.1.1 p.2.1.2
  let ht : Idx (x.ty v) k.g → ℕ := fun t => ((pos t).2.2 : ℕ) - (pos t).2.1
  let f : Idx (x.ty v) k.g → k.Zb (x.Am m) v →+ (F.Gv v → x.Am m) := fun t =>
    crd k (x.Am m) v (pos t).1 (pos t).2.1 (pos t).2.2
  have h0 : ∀ z, (∀ t, f t z = 0) → z = 0 := by
    intro z hz
    have hBz : ∀ g, B z g = 0 := by
      intro g
      exact Matrix.ext fun p q => entry_zero _ (hBtri z g) (hBty z g) p q fun t _ => congrFun (hz t) g
    apply Subtype.ext
    funext g
    apply Subtype.ext
    have hρ := (UpperTheory.V.Pa.rho1 l F n x k (x.Am m)).2.2.2.1 v
    have e : ((z.1 g : k.M1 (x.Am m)) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) =
        k.w1 (x.Am m) v * B z g * k.wi1 (x.Am m) v := by
      simp only [B, ← mul_assoc, hρ.2, one_mul]
      rw [mul_assoc, hρ.2, mul_one]
    rw [e, hBz g, mul_zero, zero_mul]
    rfl
  have hP : ∀ t, (P t).Finite := by
    intro t
    rcases t with i | p | ⟨o, p⟩
    · exact (homCount l F n x _ (F.Iv v) d' m hA).1
    · exact ((Classical.choose_spec (hpc p.1 p.2.1)) m).1
    · exact ((Classical.choose_spec (hpc p.1 p.2.1)) m).1
  have hf : ∀ t z, (∀ t', ht t' < ht t → f t' z = 0) → f t z ∈ P t := by
    intro t z hz
    have hB : ∀ g p q, (pos t).2.1 ≤ p → q ≤ (pos t).2.2 → (p ≠ (pos t).2.1 ∨ q ≠ (pos t).2.2) →
        B z g p q = 0 := by
      intro g p q hp hq hne
      by_cases hqp : q < p
      · exact hBtri z g p q hqp
      · refine entry_zero _ (hBtri z g) (hBty z g) p q fun t' ht' => ?_
        have e1 : (pos t').2.1 = p := congrArg Prod.fst ht'
        have e2 : (pos t').2.2 = q := congrArg Prod.snd ht'
        have a1 : ((pos t).2.1 : ℕ) ≤ (p : ℕ) := hp
        have a2 : (q : ℕ) ≤ ((pos t).2.2 : ℕ) := hq
        have a3 : (p : ℕ) ≤ (q : ℕ) := not_lt.mp hqp
        have a4 : (p : ℕ) ≠ (pos t).2.1 ∨ (q : ℕ) ≠ (pos t).2.2 :=
          hne.imp (fun h e => h (Fin.ext e)) (fun h e => h (Fin.ext e))
        have hlt : ht t' < ht t := by
          show ((pos t').2.2 : ℕ) - (pos t').2.1 < ((pos t).2.2 : ℕ) - (pos t).2.1
          rw [e1, e2]
          omega
        exact congrFun (hz t' hlt) g
    obtain ⟨hlc, hcoc⟩ := crd_coc k (x.Am m) v (pos t).1 (pos t).2.1 (pos t).2.2 z hB
    rcases t with i | p | ⟨o, p⟩
    · refine ⟨hlc, fun g h => ?_, fun g hg => ?_⟩
      · have e := hcoc g h
        have one : (x.ψ v i g : x.A) * (x.ψ v i g⁻¹ : x.A) = 1 := by
          rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
        rw [show ((x.ψ v (pos (Sum.inl i)).2.1 g : x.A) * (x.ψ v (pos (Sum.inl i)).2.2 g⁻¹ : x.A)) = 1
          from one, one_smul] at e
        exact e
      · obtain ⟨-, -, -, hmu⟩ := z.2
        have e : B z g i i = 0 := hmu g hg i
        show (B z g i i).a = 0
        rw [e]
        rfl
    · exact ⟨hlc, hcoc⟩
    · exact ⟨hlc, hcoc⟩
  obtain ⟨hfin, hcard⟩ := filt_ht ht f P h0 hP hf
  refine ⟨hfin, hcard.trans ?_⟩
  have hK : 0 < Nat.card x.K := Nat.card_pos
  let base : Idx (x.ty v) k.g → ℕ := fun t => match t with
    | .inl _ => m * (d' + 1)
    | .inr _ => m * (1 + d)
  calc ∏ t, (P t).ncard ≤ ∏ t, Nat.card x.K ^ (base t + Cof t) := by
        refine Finset.prod_le_prod' fun t _ => ?_
        rcases t with i | p | ⟨o, p⟩
        · simpa [base, Cof] using (homCount l F n x _ (F.Iv v) d' m hA).2
        · exact ((Classical.choose_spec (hpc p.1 p.2.1)) m).2
        · exact ((Classical.choose_spec (hpc p.1 p.2.1)) m).2
    _ = Nat.card x.K ^ (∑ t, (base t + Cof t)) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ Nat.card x.K ^ (m * (n * (d' + 1) + nu n x.a k.g * (1 + d)) + ∑ t, Cof t) := by
        apply Nat.pow_le_pow_right hK
        rw [Finset.sum_add_distrib]
        apply Nat.add_le_add_right
        obtain ⟨-, hnu, -, -⟩ := UpperTheory.V.Pa.tyCard l F n x v k.g
        have s1 : ∑ t : Idx (x.ty v) k.g, base t = n * (m * (d' + 1)) +
            (Fintype.card {p : Fin n × Fin n // p.1 < p.2 ∧ x.ty v p.1 = x.ty v p.2} +
              k.g * Fintype.card {p : Fin n × Fin n // p.1 < p.2 ∧ x.ty v p.1 ≠ x.ty v p.2}) *
              (m * (1 + d)) := by
          rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
          simp only [base, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            smul_eq_mul]
          ring
        rw [s1, Fintype.card_subtype, Fintype.card_subtype, hnu]
        apply le_of_eq
        ring
