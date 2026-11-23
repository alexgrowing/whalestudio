import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestMemLatticeStabilizerOfLocalMatrices
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFinitePointsOfHasLocalLatticeMatrices
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMemProjEqOnFinset
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiMeasureUnitriangularCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.MeasureEqRelIndexMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SymmetricJacobianSignature

open GlobalTheory.RootEx GlobalTheory.RowRep GlobalTheory.LocGrp GlobalTheory.SplitWeil GlobalTheory.SplitFlip

section Unip
variable {k : Type} [Field k] {Y : Type} [Fintype Y] [DecidableEq Y]

def uni (k : Type) [Field k] {Y : Type} [Fintype Y] [DecidableEq Y] (l : Y → ℕ) : Subgroup (GL Y k) where
  carrier := {x | ∀ r s, l s ≤ l r → x.val r s = (1 : Matrix Y Y k) r s}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := by
    intro x y hx hy r s hrs
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single s]
    · rw [hx r s hrs, hy s s le_rfl, one_apply_eq, mul_one]
    · intro q _ hq
      by_cases h : l s ≤ l q
      · rw [hy q s h, one_apply_ne hq, mul_zero]
      · rw [hx r q (by omega), one_apply_ne (by rintro rfl; omega), zero_mul]
    · simp
  inv_mem' := by
    intro x hx
    have key : ∀ n, ∀ s, l s = n → ∀ r, l s ≤ l r → (x⁻¹).val r s = (1 : Matrix Y Y k) r s := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro s hs r hrs
        have h := congrFun (congrFun x.inv_mul r) s
        rw [Matrix.mul_apply, Finset.sum_eq_single s] at h
        · rw [hx s s le_rfl, one_apply_eq, mul_one] at h
          exact h
        · intro q _ hq
          by_cases h' : l s ≤ l q
          · rw [hx q s h', one_apply_ne hq, mul_zero]
          · rw [ih (l q) (by omega) q rfl r (by omega), one_apply_ne (by rintro rfl; omega), zero_mul]
        · simp
    exact fun r s hrs => key _ s rfl r hrs

def midLev (n : Type) (c : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => c + 1) fun i => 2 * (i.val + 1)

theorem symN_eq_uni (n : Type) [Fintype n] [DecidableEq n] {c : ℕ} (hc : 1 ≤ c) : symN k n c = uni k (midLev n c) := by
  have hle : symN k n c ≤ uni k (midLev n c) := by
    refine sup_le ?_ ?_ <;>
    · refine (Subgroup.closure_le _).2 fun x hx r s hrs => ?_
      refine hx r s ?_
      rcases r with r | r <;> rcases s with s | s <;>
        simp only [midLev, RootEx.lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega
  refine le_antisymm hle fun x hx => ?_
  · obtain ⟨σ, rfl | rfl⟩ := Nat.even_or_odd' c
    · have h1 := ((ParabolicEntries.mem_R_iff_and_mem_RFJ_iff k n (2 * σ) σ).2 (by omega) (by omega) x).2
        fun r s _ hrs => hx r s hrs
      have h2 : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.RFJ k n (2 * σ) σ ≤ symR k n (2 * σ) := by
        rw [symR, symN_even]
        exact sup_le (sup_le_sup_left le_sup_left _) (sup_le_sup_left le_sup_right _)
      let Q : Subgroup (GL (n ⊕ Fin (2 * σ)) k) :=
        { carrier := {y | ∃ g, ∃ u ∈ symN k n (2 * σ), y = embX (2 * σ) g * u}
          one_mem' := ⟨1, 1, one_mem _, by simp⟩
          mul_mem' := by
            rintro _ _ ⟨g, u, hu, rfl⟩ ⟨g', u', hu', rfl⟩
            exact ⟨g * g', _, mul_mem (symN_conj hu g') hu', by simp [mul_assoc]⟩
          inv_mem' := by
            rintro _ ⟨g, u, hu, rfl⟩
            exact ⟨g⁻¹, _, symN_conj (inv_mem hu) g⁻¹, by simp [mul_assoc]⟩ }
      have h3 : symR k n (2 * σ) ≤ Q :=
        sup_le (by rintro _ ⟨g, rfl⟩; exact ⟨g, 1, one_mem _, (mul_one _).symm⟩) fun u hu => ⟨1, u, hu, by simp⟩
      obtain ⟨g, u, hu, rfl⟩ := h3 (h2 h1)
      have h4 : embX (2 * σ) g ∈ uni k (midLev n (2 * σ)) := (mul_mem_cancel_right (hle hu)).1 hx
      obtain rfl : g = 1 := Units.ext (Matrix.ext fun r s => by
        have := h4 (.inl r) (.inl s) le_rfl
        change g.val r s = _ at this
        rw [this]
        simp [one_apply])
      simpa using hu
    · rw [symN_odd]
      refine Subgroup.subset_closure fun r s hrs => hx r s ?_
      rcases r with r | r <;> rcases s with s | s <;> simp only [midLev, RootEx.lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega

end Unip

section Adapt
variable {D : D7} {K : Type} [Field K] (π : AE D →+* K)

def Adapted {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {Y : Type} (F : Matrix (Fin S.rank) Y K) (l : Y → ℕ) : Prop :=
  ∃ (Y₀ : Type) (_ : Fintype Y₀) (_ : DecidableEq Y₀) (b : Matrix (Fin S₀.rank) Y₀ K) (b' : Matrix Y₀ (Fin S₀.rank) K),
    b' * b = 1 ∧ b * b' = 1 ∧ ∃ (τ : Y₀ ⊕ (Fin ρ ⊕ Fin ρ) → Y) (t : Y₀ ⊕ (Fin ρ ⊕ Fin ρ) → K), Function.Surjective τ ∧
      (∀ r z, F r (τ z) = t z * wCols π d b r z) ∧ ∀ z z', l (τ z') ≤ l (τ z) ↔ wlev Y₀ ρ z' ≤ wlev Y₀ ρ z

theorem adapted_jac {A B : HSp D} {σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B (2 * σ) ε)
    {b b' : Matrix (Fin A.rank) (Fin A.rank) K} (hb : b * b' = 1) (u : Fin (2 * σ) → K) :
    Adapted π (jacDec d rfl) (sumCols d π b u) (midLev _ (2 * σ)) := by
  have hσ : σ ≤ 2 * σ := by omega
  refine ⟨Fin A.rank, inferInstance, inferInstance, b, b', mul_eq_one_comm.1 hb, hb,
    Sum.map id (Sum.elim (fun i : Fin σ => Fin.castLE hσ i) fun i : Fin σ => (Fin.castLE hσ i).rev),
    Sum.elim (fun _ => 1) (Sum.elim (fun i => u (Fin.castLE hσ i)) fun i => u (Fin.castLE hσ i).rev), ?_, ?_, ?_⟩
  · rintro (a | j)
    · exact ⟨Sum.inl a, rfl⟩
    · by_cases h : j.val < σ
      · exact ⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩
      · exact ⟨Sum.inr (Sum.inr ⟨2 * σ - 1 - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by
          simp only [Sum.elim_inr, Fin.val_rev, Fin.val_castLE]; omega))⟩
  · rintro r (a | i | i)
    · exact (one_mul _).symm
    · exact (mul_diagonal u _ _ _).trans (mul_comm _ _)
    · exact (mul_diagonal u _ _ _).trans (mul_comm _ _)
  · rintro (a | i | i) (a' | j | j) <;>
      simp only [wlev, midLev, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Fin.val_rev, Fin.val_castLE] <;> omega

theorem adapted_bes {A B : HSp D} {σ : ℕ} (d : HermitianOrthogonalExtensionData A B (2 * σ + 1) (-1)) (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0)
    {b b' : Matrix (Fin A.rank) (Fin A.rank) K} (hb : b * b' = 1) (u : Fin (2 * σ + 1) → K) :
    Adapted π (diagDec (besDec d rfl) l hl) (sumCols d π b u) (midLev _ (2 * σ + 1)) := by
  have hσ : σ ≤ 2 * σ + 1 := by omega
  let E : Fin A.rank ⊕ Fin 1 ≃ Fin (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).rank := finSumFinEquiv
  let φ : D.host.E →+* K := π.comp (incA D)
  have vX : ∀ r (i : Fin σ), φ (d.a r (Fin.castLE hσ i)) = φ (l i)⁻¹ * ((diagDec (besDec d rfl) l hl).jX.map π) r i :=
    fun r i => by
      change _ = _ * φ (((besDec d rfl).e * diagonal l) r i)
      rw [mul_diagonal, ← map_mul, mul_left_comm, inv_mul_cancel₀ (hl i), mul_one]; rfl
  have vY : ∀ r (i : Fin σ), φ (d.a r (Fin.castLE hσ i).rev) =
      φ (star (l i)) * ((diagDec (besDec d rfl) l hl).jY.map π) r i := fun r i => by
    change _ = _ * φ (((besDec d rfl).e' * diagonal fun a => (star (l a))⁻¹) r i)
    rw [mul_diagonal, ← map_mul, mul_left_comm, mul_inv_cancel₀ (star_ne_zero.2 (hl i)), mul_one]; rfl
  have core : ∀ {Z : Type} (X : Matrix (Fin A.rank ⊕ Fin 1) Z K), (diagDec (besDec d rfl) l hl).j0.map π *
      X.submatrix E.symm id = fromCols ((frameMat B A d.ι).map φ) ((midCol d rfl).map φ) * X := fun X => by
    have e : (diagDec (besDec d rfl) l hl).j0.map π =
        (fromCols ((frameMat B A d.ι).map φ) ((midCol d rfl).map φ)).submatrix id E.symm := by
      rw [← fromCols_map]; rfl
    exact (congrArg (· * X.submatrix E.symm id) e).trans (submatrix_mul_equiv _ _ _ E.symm _)
  refine ⟨Fin A.rank ⊕ Fin 1, inferInstance, inferInstance,
    (fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) K)).submatrix E.symm id,
    (fromBlocks b' 0 0 (1 : Matrix (Fin 1) (Fin 1) K)).submatrix id E.symm, ?_, ?_,
    Sum.elim (Sum.map id fun _ => ⟨σ, by omega⟩)
      (Sum.elim (fun i : Fin σ => Sum.inr (Fin.castLE hσ i)) fun i : Fin σ => Sum.inr (Fin.castLE hσ i).rev),
    Sum.elim (Sum.elim (fun _ => 1) fun _ => u ⟨σ, by omega⟩)
      (Sum.elim (fun i => u (Fin.castLE hσ i) * φ (l i)⁻¹) fun i => u (Fin.castLE hσ i).rev * φ (star (l i))), ?_, ?_, ?_⟩
  · refine (submatrix_mul_equiv _ _ _ E.symm _).trans ?_
    rw [fromBlocks_multiply]
    simp [mul_eq_one_comm.1 hb]
  · refine (submatrix_mul_equiv _ _ _ (Equiv.refl _) _).trans ?_
    rw [fromBlocks_multiply]
    simp [hb]
  · rintro (a | j)
    · exact ⟨Sum.inl (Sum.inl a), rfl⟩
    · rcases lt_trichotomy j.val σ with h | h | h
      · exact ⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩
      · exact ⟨Sum.inl (Sum.inr 0), congrArg Sum.inr (Fin.ext h.symm)⟩
      · exact ⟨Sum.inr (Sum.inr ⟨2 * σ - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by
          simp only [Fin.val_rev, Fin.val_castLE]; omega))⟩
  · have e := core (fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) K))
    rw [fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one] at e
    rintro r ((a | a) | i | i)
    · exact (congrFun (congrFun e r) (Sum.inl a)).symm.trans (one_mul _).symm
    · exact (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans (congrArg (u _ * ·) (congrFun (congrFun e r) (Sum.inr a)).symm))
    · exact (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans ((congrArg (u _ * ·) (vX r i)).trans (mul_assoc _ _ _).symm))
    · exact (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans ((congrArg (u _ * ·) (vY r i)).trans (mul_assoc _ _ _).symm))
  · rintro ((a | a) | i | i) ((a' | a') | j | j) <;>
      simp only [wlev, midLev, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr, Fin.val_rev, Fin.val_castLE] <;> omega

abbrev blk {p n q : ℕ} (P : Mx D p n) (M : Mx D n n) (J : Mx D n q) : Mx D p q := HMul.hMul P (HMul.hMul M J)

structure TriBlocks {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (M : Mx D S.rank S.rank) : Prop where
  yx : ∀ i j, π ((blk d.pY M d.jX) i j) = 0
  y0 : ∀ i j, π ((blk d.pY M d.j0) i j) = 0
  ox : ∀ i j, π ((blk d.p0 M d.jX) i j) = 0
  oo : ∀ i j, π ((blk d.p0 M d.j0) i j) = 0
  xx : ∀ i j, j ≤ i → π ((blk d.pX M d.jX) i j) = 0
  yy : ∀ i j, i ≤ j → π ((blk d.pY M d.jY) i j) = 0

theorem tri_of_uni {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {Y : Type} [Fintype Y] [DecidableEq Y]
    {F : Matrix (Fin S.rank) Y K} {Γ : Matrix Y (Fin S.rank) K} {l : Y → ℕ} (hF : Adapted π d F l) (h1 : Γ * F = 1)
    (h2 : F * Γ = 1) (g : GA D S)
    (hg : ∀ r s, l s ≤ l r → (Γ * ((mt S g).map π * F)) r s = (1 : Matrix Y Y K) r s) : TriBlocks π d (mt S g - 1) := by
  obtain ⟨Y₀, _, _, b, b', hb, hb', τ, t, hτ, ht, hl⟩ := hF
  set M : Matrix (Fin S.rank) (Fin S.rank) K := (mt S g - 1).map π with hM
  have m1 : M = (mt S g).map π - 1 := by
    rw [hM, Matrix.map_sub _ (map_sub π), Matrix.map_one _ (map_zero _) (map_one _)]
  have hw := wRows_wCols π d b b' hb
  have col : ∀ {Z : Type} (X : Matrix Z (Fin S.rank) K) x z, (X * F) x (τ z) = t z * (X * wCols π d b) x z := by
    intro Z X x z
    simp only [Matrix.mul_apply, ht, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have key : ∀ z z', wlev Y₀ ρ z' ≤ wlev Y₀ ρ z → (wRows π d b' * M * wCols π d b) z z' = 0 := by
    intro z z' hz
    have t0 : t z' ≠ 0 := fun h => by
      have := col Γ (τ z') z'
      rw [h1, h, zero_mul, one_apply_eq] at this
      exact one_ne_zero this
    refine (mul_eq_zero.1 ?_).resolve_left t0
    have e : wRows π d b' * M * F = wRows π d b' * F * (Γ * ((mt S g).map π * F) - 1) := by
      rw [m1, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc F, h2,
        Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
    rw [← col, e, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun y _ => ?_
    obtain ⟨z'', rfl⟩ := hτ y
    rw [col, hw]
    by_cases h : z = z''
    · subst h
      rw [Matrix.sub_apply, hg _ _ ((hl _ _).2 hz), sub_self, mul_zero]
    · rw [one_apply_ne h, mul_zero, zero_mul]
  simp only [Matrix.mul_assoc] at key
  have mp : ∀ {p q : ℕ} (P : Mx D p S.rank) (J : Mx D S.rank q) i j,
      π (blk P (mt S g - 1) J i j) = (P.map π * (M * J.map π)) i j := fun P J i j => by
    rw [hM, ← Matrix.map_mul, ← Matrix.map_mul]; rfl
  have k1 : d.pY.map π * (M * (d.j0.map π * b)) = 0 := Matrix.ext fun i c =>
    key (.inr (.inr i)) (.inl c) (by simp only [wlev, Sum.elim_inl, Sum.elim_inr]; omega)
  have k2 : b' * d.p0.map π * (M * d.jX.map π) = 0 := Matrix.ext fun i c =>
    key (.inl i) (.inr (.inl c)) (by simp only [wlev, Sum.elim_inl, Sum.elim_inr]; omega)
  have k3 : b' * d.p0.map π * (M * (d.j0.map π * b)) = 0 := Matrix.ext fun i c => key (.inl i) (.inl c) le_rfl
  have k1' := congrArg (· * b') k1
  have k2' := congrArg (b * ·) k2
  have k3' := congrArg (fun X => b * X * b') k3
  simp only [Matrix.mul_assoc, hb', Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero] at k1' k2' k3'
  rw [← Matrix.mul_assoc b, hb', Matrix.one_mul] at k2' k3'
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j h => ?_, fun i j h => ?_⟩ <;> rw [mp]
  · exact key (.inr (.inr i)) (.inr (.inl j)) (by simp only [wlev, Sum.elim_inl, Sum.elim_inr]; omega)
  · rw [k1']; rfl
  · rw [k2']; rfl
  · rw [k3']; rfl
  · exact key (.inr (.inl i)) (.inr (.inl j)) (by simp only [wlev, Sum.elim_inl, Sum.elim_inr]; omega)
  · exact key (.inr (.inr i)) (.inr (.inr j)) (by simp only [wlev, Sum.elim_inl, Sum.elim_inr]; omega)

theorem uni_of_flag {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {Y : Type} [Fintype Y] [DecidableEq Y]
    {F : Matrix (Fin S.rank) Y K} {Γ : Matrix Y (Fin S.rank) K} {l : Y → ℕ} (hF : Adapted π d F l) (h1 : Γ * F = 1)
    (h2 : F * Γ = 1) {g : GA D S} (hg : g ∈ flagN d) (r s : Y) (hrs : l s ≤ l r) :
    (Γ * ((mt S g).map π * F)) r s = (1 : Matrix Y Y K) r s := by
  obtain ⟨Y₀, _, _, b, b', hb, -, τ, t, hτ, ht, hl⟩ := hF
  exact uni_flag π d b b' hb h1 h2 τ hτ t ht l (fun z z' => (hl z z').1) hg r s hrs

end Adapt

section Glue

theorem eq_of_sum_eq_one {R : Type} [CommRing R] {n a b q : Type} [Fintype n] [DecidableEq n] [Fintype a] [Fintype b]
    {jX jY : Matrix n a R} {j0 : Matrix n b R} {pX pY : Matrix a n R} {p0 : Matrix b n R}
    (h : jX * pX + j0 * p0 + jY * pY = 1) {Z : Matrix n q R} (h0 : p0 * Z = 0) (hY : pY * Z = 0) : Z = jX * (pX * Z) := by
  have := congrArg (· * Z) h
  simp only [Matrix.add_mul, Matrix.mul_assoc, Matrix.one_mul, h0, hY, Matrix.mul_zero, add_zero] at this
  exact this.symm

theorem mulVec_of_cols {R : Type} [CommRing R] {n a b : Type} [Fintype n] [Fintype a] [Fintype b]
    {M : Matrix n n R} {jX : Matrix n a R} {j0 : Matrix n b R} {T : Matrix a a R} {B : Matrix a b R}
    (hX : M * jX = jX * T) (h0 : M * j0 = jX * B) {x : n → R} {y : a → R} {z : b → R} (h : x = jX *ᵥ y + j0 *ᵥ z) :
    M *ᵥ x = jX *ᵥ (T *ᵥ y + B *ᵥ z) := by
  rw [h]
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, hX, h0]

variable {D : D7}

theorem eq_zero_of_places {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {a : AE D}
    (ha : (e + cA D e) * a = a) (h1 : ∀ w ∈ P, piAt w a = 0) (h2 : ∀ w ∈ P, piAt w (cA D a) = 0) : a = 0 := by
  obtain ⟨e0, -, e2⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  replace e2 : ∀ w ∉ P, piAt w e = 0 := e2
  have key : ∀ x : AE D, (∀ w ∈ P, piAt w x = 0) → e * x = 0 := fun x hx =>
    ae_ext (by rw [map_mul, e0, zero_mul, map_zero]) fun w => by
      change piAt w (e * x) = piAt w 0
      rw [map_mul, map_zero]
      by_cases h : w ∈ P
      · rw [hx w h, mul_zero]
      · rw [e2 w h, zero_mul]
  have h3 := congrArg (cA D) (key _ h2)
  rw [map_mul, cA_cA, map_zero] at h3
  rw [← ha, add_mul, key a h1, h3, add_zero]

theorem adj_blk (S : HSp D) (g : GA D S) {p q : ℕ} (J : Mx D S.rank p) (J' : Mx D S.rank q) :
    adj (blk (HMul.hMul (adj J) (gA S)) (mt S g - 1) J') = blk (HMul.hMul (adj J') (gA S)) (mt S g⁻¹ - 1) J := by
  have h : HMul.hMul (adj (mt S g)) (gA S) = HMul.hMul (gA S) (mt S g⁻¹) := by
    have := congrArg (fun X => HMul.hMul X (mt S g⁻¹)) (mt_unitary S g)
    simp only [Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one] at this
    exact this
  have h' : HMul.hMul (adj (mt S g - 1)) (gA S) = HMul.hMul (gA S) (mt S g⁻¹ - 1) := by
    rw [adj_sub, adj_one, Matrix.sub_mul, Matrix.mul_sub, h, Matrix.one_mul, Matrix.mul_one]
  rw [blk, blk, adj_mul, adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, ← Matrix.mul_assoc (adj (mt S g - 1)), h']
  simp only [Matrix.mul_assoc]

theorem blk_eq_zero {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {S : HSp D} {g : GA D S} (hg : SuppAt e S g)
    {p q : ℕ} (J : Mx D S.rank p) (J' : Mx D S.rank q) (i : Fin p) (j : Fin q)
    (h1 : ∀ w ∈ P, piAt w (blk (HMul.hMul (adj J) (gA S)) (mt S g - 1) J' i j) = 0)
    (h2 : ∀ w ∈ P, piAt w (blk (HMul.hMul (adj J') (gA S)) (mt S g⁻¹ - 1) J j i) = 0) :
    blk (HMul.hMul (adj J) (gA S)) (mt S g - 1) J' i j = 0 := by
  refine eq_zero_of_places he ?_ h1 fun w hw => ?_
  · have h : (e + cA D e) • (mt S g - 1) = mt S g - 1 := Matrix.ext fun i j => hg i j
    have h' : (e + cA D e) • blk (HMul.hMul (adj J) (gA S)) (mt S g - 1) J' =
        blk (HMul.hMul (adj J) (gA S)) (mt S g - 1) J' := by
      rw [blk, ← Matrix.mul_smul, ← Matrix.smul_mul, h]
    exact congrFun (congrFun h' i) j
  · have := h2 w hw
    rw [← adj_blk] at this
    exact this

theorem mem_flagN {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    {g : GA D S} (hg : SuppAt e S g) (h1 : ∀ w ∈ P, TriBlocks (piAt w) d (mt S g - 1))
    (h2 : ∀ w ∈ P, TriBlocks (piAt w) d (mt S g⁻¹ - 1)) : g ∈ flagN d := by
  have hX := d.pX_eq
  have hY := d.pY_eq
  have h0 := d.p0_eq
  have q0 : ∀ {q : ℕ} (M : Mx D S.rank S.rank) (J : Mx D S.rank q),
      blk (HMul.hMul (adj d.j0) (gA S)) M J = HMul.hMul (gA S₀) (blk d.p0 M J) := fun M J => by
    rw [blk, blk, h0]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (gA S₀), gA_mul_giA, Matrix.one_mul]
  have q1 : ∀ {q : ℕ} (M : Mx D S.rank S.rank) (J : Mx D S.rank q) (w : Pl D.host.E),
      (∀ i j, piAt w (blk d.p0 M J i j) = 0) → ∀ i j, piAt w (blk (HMul.hMul (adj d.j0) (gA S)) M J i j) = 0 :=
    fun M J w h i j => by
      rw [q0, Matrix.mul_apply, map_sum]
      exact Finset.sum_eq_zero fun l _ => by rw [map_mul, h, mul_zero]
  have q2 : ∀ {q : ℕ} (M : Mx D S.rank S.rank) (J : Mx D S.rank q),
      blk (HMul.hMul (adj d.j0) (gA S)) M J = 0 → blk d.p0 M J = 0 := fun M J h => by
    rw [blk] at h
    rw [blk, h0, Matrix.mul_assoc, h, Matrix.mul_zero]
  have yx : blk d.pY (mt S g - 1) d.jX = 0 := Matrix.ext fun i j => by
    rw [hY]
    exact blk_eq_zero he hg _ _ i j (fun w hw => hY ▸ (h1 w hw).yx i j) fun w hw => hY ▸ (h2 w hw).yx j i
  have y0 : blk d.pY (mt S g - 1) d.j0 = 0 := Matrix.ext fun i j => by
    rw [hY]
    exact blk_eq_zero he hg _ _ i j (fun w hw => hY ▸ (h1 w hw).y0 i j) fun w hw => q1 _ _ w (h2 w hw).ox j i
  have ox : blk d.p0 (mt S g - 1) d.jX = 0 := q2 _ _ (Matrix.ext fun i j =>
    blk_eq_zero he hg _ _ i j (fun w hw => q1 _ _ w (h1 w hw).ox i j) fun w hw => hY ▸ (h2 w hw).y0 j i)
  have oo : blk d.p0 (mt S g - 1) d.j0 = 0 := q2 _ _ (Matrix.ext fun i j =>
    blk_eq_zero he hg _ _ i j (fun w hw => q1 _ _ w (h1 w hw).oo i j) fun w hw => q1 _ _ w (h2 w hw).oo j i)
  have xx : ∀ i j, j ≤ i → blk d.pX (mt S g - 1) d.jX i j = 0 := fun i j h => by
    rw [hX]
    exact blk_eq_zero he hg _ _ i j (fun w hw => hX ▸ (h1 w hw).xx i j h) fun w hw => hY ▸ (h2 w hw).yy j i h
  have dec : ∀ {q : ℕ} (J : Mx D S.rank q), blk d.p0 (mt S g - 1) J = 0 → blk d.pY (mt S g - 1) J = 0 →
      HMul.hMul (mt S g - 1) J = HMul.hMul d.jX (blk d.pX (mt S g - 1) J) := fun J a b => by
    exact eq_of_sum_eq_one d.sum_eq_one a b
  have cX := dec _ ox yx
  have c0 := dec _ oo y0
  refine Subgroup.subset_closure ⟨fun i => ⟨fun j => blk d.pX (mt S g - 1) d.jX j i, fun j h => xx j i h, ?_⟩, fun x hx => ?_⟩
  · funext r
    exact congrFun (congrFun cX r) i
  · have hx' : d.pY *ᵥ ratV x = 0 := by
      funext i
      have := congrArg (incA D) (congrFun hx i)
      rw [Pi.zero_apply, map_zero, RingHom.map_mulVec] at this
      exact this
    have hd : ratV x = d.jX *ᵥ (d.pX *ᵥ ratV x) + d.j0 *ᵥ (d.p0 *ᵥ ratV x) := by
      have := congrArg (· *ᵥ ratV x) d.sum_eq_one
      simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hx', Matrix.mulVec_zero, add_zero, Matrix.one_mulVec] at this
      exact this.symm
    refine ⟨blk d.pX (mt S g - 1) d.jX *ᵥ (d.pX *ᵥ ratV x) + blk d.pX (mt S g - 1) d.j0 *ᵥ (d.p0 *ᵥ ratV x), ?_⟩
    change (mt S g - 1) *ᵥ ratV x = d.jX *ᵥ _
    exact mulVec_of_cols cX c0 hd

end Glue

section Row
variable {D : D7}

theorem adapted_jac' {A B : HSp D} {c σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ) {K : Type} [Field K]
    (π : AE D →+* K) {b b' : Matrix (Fin A.rank) (Fin A.rank) K} (hb : b * b' = 1) (u : Fin c → K) :
    Adapted π (jacDec d h) (sumCols d π b u) (midLev _ c) := by
  subst h
  exact adapted_jac π d hb u

theorem adapted_bes' {A B : HSp D} {c σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (l : Fin σ → D.host.E)
    (hl : ∀ a, l a ≠ 0) {K : Type} [Field K] (π : AE D →+* K) {b b' : Matrix (Fin A.rank) (Fin A.rank) K} (hb : b * b' = 1)
    (u : Fin c → K) : Adapted π (diagDec (besDec d h) l hl) (sumCols d π b u) (midLev _ c) := by
  subst h
  exact adapted_bes π d l hl hb u

theorem frame_symN {A B S₀ : HSp D} {c ρ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (hc : 1 ≤ c) (h : HypDec B S₀ ρ)
    (w : Pl D.host.E) {β : GL (Fin A.rank) (Lev.EAf D)} {β' : GL (Fin B.rank) (Lev.EAf D)} {u : Fin c → Kw w}
    (hF : IsSumFrame d w β β' u)
    (hA : Adapted (piAt w) h (sumCols d (piAt w) (GlobalTheory.StdFrames.loc w β).val u) (midLev _ c))
    {a b : ℕ} (ha : a = A.rank) (hb : b = B.rank) (hab : a + c = b) (g : GA D B) :
    (g ∈ flagN h → frameGL hab (inBasis hb β' w (Lev.finE B g)) ∈ symN (Kw w) (Fin a) c) ∧
      (frameGL hab (inBasis hb β' w (Lev.finE B g)) ∈ symN (Kw w) (Fin a) c → TriBlocks (piAt w) h (mt B g - 1)) := by
  subst ha hb
  obtain ⟨Γ, h1, h2, e⟩ := frame_val d w hF
  rw [symN_eq_uni _ hc]
  refine ⟨fun hg r s hrs => ?_, fun hg => tri_of_uni _ h hA h1 h2 g fun r s hrs => ?_⟩
  · exact (congrFun (congrFun (e g) r) s).trans (uni_of_flag _ h hA h1 h2 hg r s hrs)
  · exact (congrFun (congrFun (e g) r) s).symm.trans (hg r s hrs)

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem exists_flag (G : GridData L sc) {j : ℕ} (hi : j ∈ idx D) (hj : j < D.R.m) :
    ∃ (S₀ : HSp D) (ρ : ℕ) (h : HypDec (G.V (.grid D.R.m j)) S₀ ρ), GlobalTheory.CellMass.rowN G j = flagN h ∧
      ∀ {K : Type} [Field K] (π : AE D →+* K) (b b' : Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) K),
        b * b' = 1 → ∀ u, Adapted π h (sumCols (G.rowDec j hj) π b u) (midLev _ (D.R.m - 1 - j)) := by
  have hm := idx_le hi
  obtain ⟨n, hn⟩ := D.R.m_even
  unfold GlobalTheory.CellMass.rowN
  split_ifs with h h'
  · exact ⟨_, _, _, rfl, fun π b b' hb u => adapted_jac' (G.rowDec j hj) _ π hb u⟩
  · exact ⟨_, _, _, rfl, fun π b b' hb u => adapted_bes' (G.rowDec j hj) _ _ _ π hb u⟩
  · omega

def frHom (B : Frames G) (t : T) (w : Pl D.host.E) {j : ℕ} (hj : j ≤ D.R.m) (hj' : j < D.R.m) :
    GA D (G.V (.grid D.R.m j)) →* GL (Fin (topRank (locGrid G t w) j) ⊕ Fin ((locGrid G t w).m - 1 - j)) (Kw w) :=
  (toFrame (G := locGrid G t w) one_le_sLen hj').toMonoidHom.comp (locAt B t w j hj)

theorem rowN_local (S : GridChoice W U) {t : T} (ht : t ∈ U) {j : ℕ} (hi : j ∈ idx D) (hj : j ≤ D.R.m) (hj' : j < D.R.m) :
    (∀ x ∈ GlobalTheory.CellMass.rowN G j, ∀ w ∈ locPl G t,
      frHom S.B t w hj hj' x ∈ symN (Kw w) _ _) ∧
    ∀ e, IsIdemSum e (locPl G t) → ∀ x, SuppAt e _ x →
      (∀ w ∈ locPl G t, frHom S.B t w hj hj' x ∈ symN (Kw w) _ _) →
      x ∈ GlobalTheory.CellMass.rowN G j := by
  have hm := idx_le hi
  obtain ⟨S₀, ρ, h, e, hA⟩ := exists_flag G hi hj'
  have key := fun w (hw : w ∈ locPl G t) x => frame_symN (G.rowDec j hj') (by omega) h w (S.row t ht w hw j hj')
    (hA (piAt w) _ _ (GlobalTheory.StdFrames.loc w (S.βp j)).mul_inv _) (topRank_eq G t w hj)
    (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩)
    (by have := topRank_add (G := locGrid G t w) one_le_sLen j; change _ + D.R.m = (locGrid G t w).rank (D.R.m, j) + _ + _ at this; omega) x
  rw [e]
  refine ⟨fun x hx w hw => (key w hw x).1 hx, fun e he x hx hl => mem_flagN he h hx (fun w hw => (key w hw x).2 (hl w hw))
    fun w hw => (key w hw x⁻¹).2 ?_⟩
  have := inv_mem (hl w hw)
  rw [← map_inv] at this
  exact this

theorem isClosed_rowN (G : GridData L sc) {j : ℕ} (hi : j ∈ idx D) :
    IsClosed (GlobalTheory.CellMass.rowN G j : Set (GA D (G.V (.grid D.R.m j)))) := by
  have hm := idx_le hi
  obtain ⟨S₀, ρ, h, e, -⟩ := exists_flag G hi (by omega)
  rw [e]
  exact GlobalTheory.JacMeas.isClosed_flagN h

theorem smul_mul_sub_one {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {f : R} {x y : Matrix n n R}
    (hx : f • (x - 1) = x - 1) (hy : f • (y - 1) = y - 1) : f • (x * y - 1) = x * y - 1 := by
  have h : x * y - 1 = x * (y - 1) + (x - 1) := by noncomm_ring
  rw [h, smul_add, ← Matrix.mul_smul, hx, hy]

theorem smul_inv_sub_one {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {f : R} {x y : Matrix n n R}
    (hx : f • (x - 1) = x - 1) (hy : y * x = 1) : f • (y - 1) = y - 1 := by
  have h : y - 1 = -(y * (x - 1)) := by rw [Matrix.mul_sub, Matrix.mul_one, hy, neg_sub]
  rw [h, smul_neg, ← Matrix.mul_smul, hx]

theorem smul_conj_sub_one {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {f : R} {x y z : Matrix n n R}
    (hx : f • (x - 1) = x - 1) (hy : y * z = 1) : f • (y * x * z - 1) = y * x * z - 1 := by
  have h : y * x * z - 1 = y * ((x - 1) * z) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, hy, Matrix.mul_assoc]
  rw [h, ← Matrix.mul_smul, ← Matrix.smul_mul, hx]

def suppGrp (e : AE D) (V : HSp D) : Subgroup (GA D V) where
  carrier := {g | (e + cA D e) • (mt V g - 1) = mt V g - 1}
  one_mem' := by
    change (e + cA D e) • (mt V 1 - 1) = mt V 1 - 1
    rw [GlobalTheory.MixModel.mt_one, sub_self, smul_zero]
  mul_mem' := by
    intro x y hx hy
    change (e + cA D e) • (mt V (x * y) - 1) = mt V (x * y) - 1
    rw [mt_mul]
    exact smul_mul_sub_one hx hy
  inv_mem' := fun {x} hx => smul_inv_sub_one hx (mt_inv_mul V x)

theorem mem_suppGrp {e : AE D} {V : HSp D} {g : GA D V} : g ∈ suppGrp e V ↔ SuppAt e V g :=
  ⟨fun h i j => congrFun (congrFun h i) j, fun h => Matrix.ext h⟩

instance suppGrp_normal (e : AE D) (V : HSp D) : (suppGrp e V).Normal := ⟨fun x hx g => by
  change (e + cA D e) • (mt V (g * x * g⁻¹) - 1) = mt V (g * x * g⁻¹) - 1
  rw [mt_mul, mt_mul]
  exact smul_conj_sub_one hx (mt_mul_inv V g)⟩

theorem idem_unique {e e' : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) (h' : IsIdemSum e' P) : e = e' := by
  obtain ⟨a, b, c⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum h
  obtain ⟨a', b', c'⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum h'
  refine ae_ext (a.trans a'.symm) fun w => ?_
  by_cases hw : w ∈ P
  · rw [b w hw, b' w hw]
  · rw [c w hw, c' w hw]

end Row

section Abstract

def cj {H : Type} [Group H] (K : Subgroup H) (c : H) : Subgroup H := K.comap (MulAut.conj c⁻¹).toMonoidHom

theorem mem_cj {H : Type} [Group H] {K : Subgroup H} {c x : H} : x ∈ cj K c ↔ c⁻¹ * x * c ∈ K := by
  simp [cj]

theorem mem_map_conj {H : Type} [Group H] {K : Subgroup H} {c x : H} :
    x ∈ K.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ K := by
  refine ⟨?_, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩
  rintro ⟨y, hy, rfl⟩
  simpa [mul_assoc] using hy

theorem real_mul_idxRatio {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {A B : Subgroup G} (hAo : IsOpen (A : Set G)) (hAc : IsCompact (A : Set G))
    (hBo : IsOpen (B : Set G)) (hBc : IsCompact (B : Set G)) : μ.real B * (idxRatio A B : ℝ) = μ.real A := by
  have h1 : B.relIndex A ≠ 0 := relIndex_ne_zero_of_isOpen hBo hAc le_rfl
  have h2 : A.relIndex B ≠ 0 := relIndex_ne_zero_of_isOpen hAo hBc le_rfl
  have e1 : (A ⊓ B).relIndex A = B.relIndex A := by rw [inf_comm]; exact Subgroup.inf_relIndex_right B A
  have e2 : (A ⊓ B).relIndex B = A.relIndex B := Subgroup.inf_relIndex_right A B
  have ho : IsOpen ((A ⊓ B : Subgroup G) : Set G) := hAo.inter hBo
  have a := PI.IwaMeasEx.MF.measure_eq_relIndex_mul μ (inf_le_left : A ⊓ B ≤ A) hAo.measurableSet ho.measurableSet
    (e1 ▸ h1)
  have b := PI.IwaMeasEx.MF.measure_eq_relIndex_mul μ (inf_le_right : A ⊓ B ≤ B) hBo.measurableSet ho.measurableSet
    (e2 ▸ h2)
  have h2' : (A.relIndex B : ℝ) ≠ 0 := by exact_mod_cast h2
  rw [Measure.real, Measure.real, a, b, e1, e2, idxRatio]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  push_cast
  field_simp

theorem idxRatio_eq_prod {G H ι : Type} [Group G] [Group H] [Fintype ι] {L : ι → Type} [∀ w, Group (L w)] (f : G →* H)
    (φ : ∀ w, H →* L w) (K P : Subgroup H) [P.Normal] (N O : ∀ w, Subgroup (L w))
    (hK : ∀ k ∈ K, ∀ w, φ w k ∈ O w) (hK' : ∀ y ∈ P, (∀ w, φ w y ∈ O w) → y ∈ K)
    (hN : ∀ x w, φ w (f x) ∈ N w) (hN' : ∀ y ∈ P, (∀ w, φ w y ∈ N w) → y ∈ f.range)
    (hP : ∀ g : ∀ w, L w, ∃ y ∈ P, ∀ w, φ w y = g w) (b r : H) (hr : r ∈ P) (s h : ∀ w, L w) (hs : ∀ w, s w ∈ O w)
    (hrs : ∀ w, φ w r = s w * h w) (hn : ∀ w y, y ∈ N w ↔ (φ w b * s w)⁻¹ * y * (φ w b * s w) ∈ N w) :
    idxRatio ((cj K b).comap f) ((cj K (b * r)).comap f) =
      ∏ w, idxRatio (N w ⊓ O w) (N w ⊓ (O w).map (MulAut.conj (h w)).toMonoidHom) := by
  classical
  have key : ∀ p ∈ P, ∀ z, p⁻¹ * z * p ∈ K ↔ z ∈ P ⊔ K ∧ ∀ w, φ w (p⁻¹ * z * p) ∈ O w := by
    intro p hp z
    have hp' : p ∈ P ⊔ K := Subgroup.mem_sup_left hp
    refine ⟨fun hz => ⟨?_, hK _ hz⟩, fun ⟨h1, h2⟩ => ?_⟩
    · have := mul_mem (mul_mem hp' (Subgroup.mem_sup_right hz)) (inv_mem hp')
      simpa [mul_assoc] using this
    · have h3 : p⁻¹ * z * p ∈ P ⊔ K := mul_mem (mul_mem (inv_mem hp') h1) hp'
      obtain ⟨y, hy, k, hk, e⟩ := Subgroup.mem_sup_of_normal_left.1 h3
      rw [← e] at h2 ⊢
      refine mul_mem (hK' y hy fun w => ?_) hk
      have := h2 w
      rw [map_mul] at this
      exact (mul_mem_cancel_right (hK k hk w)).1 this
  let π : ∀ w, G →* L w := fun w => (MulAut.conj (φ w b * s w)⁻¹).toMonoidHom.comp ((φ w).comp f)
  have hπ : ∀ w x, π w x = (φ w b * s w)⁻¹ * φ w (f x) * (φ w b * s w) := fun w x => by simp [π, mul_assoc]
  have hH : ∀ v, ∀ y ∈ N v, ∃ g ∈ (cj (P ⊔ K) b).comap f, π v g = y ∧ ∀ w, w ≠ v → π w g = 1 := by
    intro v y hy
    obtain ⟨z, hz, e⟩ := hP (Pi.mulSingle v ((φ v b * s v) * y * (φ v b * s v)⁻¹))
    obtain ⟨g, rfl⟩ := hN' z hz fun w => by
      rw [e]
      by_cases hw : w = v
      · subst hw
        rw [Pi.mulSingle_eq_same, hn]
        simpa [mul_assoc] using hy
      · rw [Pi.mulSingle_eq_of_ne hw]
        exact one_mem _
    refine ⟨g, mem_cj.2 (Subgroup.mem_sup_left (Subgroup.Normal.conj_mem' inferInstance _ hz b)), ?_, fun w hw => ?_⟩
    · rw [hπ, e, Pi.mulSingle_eq_same]
      group
    · rw [hπ, e, Pi.mulSingle_eq_of_ne hw]
      group
  have h0 : ∀ g, g ∈ (cj K b).comap f ↔ g ∈ (cj (P ⊔ K) b).comap f ∧ ∀ v, π v g ∈ N v ⊓ O v := by
    intro g
    have := key 1 (one_mem _) (b⁻¹ * f g * b)
    rw [inv_one, one_mul, mul_one] at this
    rw [Subgroup.mem_comap, Subgroup.mem_comap, mem_cj, mem_cj, this]
    refine and_congr_right fun _ => forall_congr' fun v => ?_
    have e : π v g = (s v)⁻¹ * φ v (b⁻¹ * f g * b) * s v := by
      rw [hπ, map_mul, map_mul, map_inv]
      group
    rw [Subgroup.mem_inf, and_iff_right (hπ v g ▸ (hn v _).1 (hN g v)), e, mul_mem_cancel_right (hs v),
      mul_mem_cancel_left (inv_mem (hs v))]
  have h1 : ∀ g, g ∈ (cj K (b * r)).comap f ↔ g ∈ (cj (P ⊔ K) b).comap f ∧
      ∀ v, π v g ∈ N v ⊓ (O v).map (MulAut.conj (h v)).toMonoidHom := by
    intro g
    have e0 : (b * r)⁻¹ * f g * (b * r) = r⁻¹ * (b⁻¹ * f g * b) * r := by group
    rw [Subgroup.mem_comap, Subgroup.mem_comap, mem_cj, mem_cj, e0, key r hr]
    refine and_congr_right fun _ => forall_congr' fun v => ?_
    have e : (h v)⁻¹ * π v g * h v = φ v (r⁻¹ * (b⁻¹ * f g * b) * r) := by
      simp only [hπ, map_mul, map_inv, hrs]
      group
    rw [Subgroup.mem_inf, and_iff_right (hπ v g ▸ (hn v _).1 (hN g v)), mem_map_conj, e]
  have a := GlobalTheory.relIndex_eq_prod_local G ι L π _ _ _ _ _ Finset.univ (fun v y hy => hH v y (Subgroup.mem_inf.1 hy).1) h0 h1 (by simp)
  have c := GlobalTheory.relIndex_eq_prod_local G ι L π _ _ _ _ _ Finset.univ (fun v y hy => hH v y (Subgroup.mem_inf.1 hy).1) h1 h0 (by simp)
  simp only [idxRatio, a, c]
  push_cast
  rw [Finset.prod_div_distrib]

end Abstract

section Local
variable {k : Type} [Field k] [ValuativeRel k]

theorem frameGL_mem_KO {a c b : ℕ} (h : a + c = b) (x : GL (Fin b) k) : frameGL h x ∈ KO k (Fin a ⊕ Fin c) ↔ x ∈ KO k (Fin b) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Units.mapEquiv (Matrix.reindexAlgEquiv ℤ _ (frame h)).toMulEquiv y, (frameGL h).injective ?_⟩
    rw [← hy]
    refine Units.ext (Matrix.ext fun i j => ?_)
    change algebraMap _ k (y.val ((frame h).symm (frame h i)) ((frame h).symm (frame h j))) = algebraMap _ k (y.val i j)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · rintro ⟨y, rfl⟩
    exact ⟨Units.mapEquiv (Matrix.reindexAlgEquiv ℤ _ (frame h).symm).toMulEquiv y, Units.ext (Matrix.ext fun i j => rfl)⟩

omit [ValuativeRel k] in
theorem frameGL_diagGL {a c b : ℕ} (h : a + c = b) (g : Fin b → kˣ) : ∃ f, (frameGL h (diagGL g)).val = diagonal f :=
  ⟨_, submatrix_diagonal_equiv (fun i => (g i : k)) (frame h)⟩

theorem map_conj_map {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') {J : Subgroup G} {O : Subgroup G'}
    (h : ∀ x, φ x ∈ O ↔ x ∈ J) (g : G) :
    (J.map (MulAut.conj g).toMonoidHom).map φ.toMonoidHom = O.map (MulAut.conj (φ g)).toMonoidHom := by
  ext x
  obtain ⟨y, rfl⟩ := φ.surjective x
  rw [mem_map_conj, ← map_inv, ← map_mul, ← map_mul, h]
  exact (Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective).trans mem_map_conj

theorem diagGL_sign_mem_KO {n : Type} [Fintype n] [DecidableEq n] (p : n → Prop) [DecidablePred p] (s : ℤˣ) :
    diagGL (fun a => if p a then Units.map (Int.castRingHom k).toMonoidHom s else 1) ∈ KO k n := by
  refine ⟨Units.map (diagonalRingHom n _).toMonoidHom (MulEquiv.piUnits.symm
    fun a => if p a then Units.map (Int.castRingHom (ValuativeRel.valuation k).integer).toMonoidHom s else 1), ?_⟩
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap _ k (diagonal (fun a => ((if p a then Units.map (Int.castRingHom (ValuativeRel.valuation k).integer).toMonoidHom s
    else 1 : _ˣ) : (ValuativeRel.valuation k).integer)) i j) = diagonal (fun a => ((if p a then
      Units.map (Int.castRingHom k).toMonoidHom s else 1 : kˣ) : k)) i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, diagonal_apply_eq]
    split_ifs <;> simp
  · rw [diagonal_apply_ne _ hij, diagonal_apply_ne _ hij, map_zero]

omit [ValuativeRel k] in

theorem diag_normalises {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {y : GL (n ⊕ Fin c) k} {f : n ⊕ Fin c → k}
    (hy : y.val = diagonal f) (x : GL (n ⊕ Fin c) k) : x ∈ symN k n c ↔ y⁻¹ * x * y ∈ symN k n c := by
  have hf : ∀ r, f r ≠ 0 := fun r h => by
    have := congrFun (congrFun y.mul_inv r) r
    rw [hy, diagonal_mul, h, zero_mul, one_apply_eq] at this
    exact zero_ne_one this
  obtain rfl : y = diagGL fun r => Units.mk0 (f r) (hf r) := Units.ext hy
  rw [← mem_map_conj, map_conj_diagGL_symN]

end Local

section Main
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem givenLevel_eq (G : GridData L sc) (t : T) (w : Pl D.host.E) {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ D.R.m) :
    givenLevel G t w (D.R.m, j) = KO (Kw w) _ := by
  have hl : ∀ X : ℕ × ℕ, 1 ≤ X.1 → 1 ≤ X.2 → givenLevel G t w X = KO (Kw w) _ := by
    rintro ⟨_ | a, _ | b⟩ h h'
    · omega
    · simp at h
    · simp at h'
    · rfl
  exact hl _ (by change 1 ≤ D.R.m; omega) h1

theorem conjLevel_eq (G : GridData L sc) (t : T) (w : Pl D.host.E) {j : ℕ} (h1 : 1 ≤ j) (hj : j < D.R.m)
    (g : (locGrid G t w).VertexGroup) :
    conjLevel one_le_sLen (givenLevel G t w) g (j := j) hj = (KO (Kw w) _).map
      (MulAut.conj (toFrame (G := locGrid G t w) one_le_sLen hj (g (D.R.m, j)))).toMonoidHom := by
  refine map_conj_map (toFrame (G := locGrid G t w) one_le_sLen hj) (fun x => (frameGL_mem_KO _ x).trans ?_) _
  exact (givenLevel_eq G t w h1 hj.le) ▸ Iff.rfl

set_option maxHeartbeats 1600000 in

theorem idxRatio_row {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) {t : T} (ht : t ∈ U) {j : ℕ} (hi : j ∈ idx D)
    (hj : j ≤ D.R.m) (hj' : j < D.R.m)
    (hlat : ∀ x g, HasLoc t S.B hj x g → (∀ w, g w ∈ givenLevel G t w.1 (D.R.m, j)) → x ∈ latGrp G j)
    (s : ℤˣ) (β : CosFam G t) {δ b r : GA D (G.V (.grid D.R.m j))} (hδ : IsTilt G j δ) (hb : IsFinOf δ b)
    (hr : HasLoc t S.B hj r fun w => sgnAt G t s w.1 j * (repsAt G t w.1).elt (β w) (D.R.m, j)) :
    idxRatio ((cj (latGrp G j) b).comap ((GfC _).subtype.comp ((GlobalTheory.CellMass.rowN G j).subgroupOf (GfC _)).subtype))
      ((cj (latGrp G j) (b * r)).comap ((GfC _).subtype.comp ((GlobalTheory.CellMass.rowN G j).subgroupOf (GfC _)).subtype)) =
      ∏ w : locPl G t, invVol (conjLevel one_le_sLen (givenLevel G t w) ((repsAt G t w).elt (β w)) (j := j) hj') := by
  have hm := idx_le hi
  obtain ⟨e, he, hre, hr⟩ := hr
  obtain ⟨n1, n2⟩ := rowN_local S ht hi hj hj'
  have hloc : ∀ y ∈ suppGrp e (G.V (.grid D.R.m j)), HasLoc t S.B hj y fun w => locAt S.B t w.1 j hj y :=
    fun y hy => ⟨e, he, mem_suppGrp.1 hy, fun _ => rfl⟩
  have hO : ∀ (w : Pl D.host.E) y, frHom S.B t w hj hj' y ∈ KO (Kw w) _ ↔
      locAt S.B t w j hj y ∈ givenLevel G t w (D.R.m, j) := fun w y => by
    rw [givenLevel_eq G t w hm.1 hj]
    exact frameGL_mem_KO _ _
  refine (idxRatio_eq_prod (ι := locPl G t) _ (fun w => frHom S.B t w.1 hj hj') (latGrp G j) (suppGrp e _)
    (fun w => symN (Kw w.1) _ _) (fun w => KO (Kw w.1) _) (fun k hk w => (hO _ _).2 (locAt_lat S.B t w.1 hm.1 hj hk))
    (fun y hy h => hlat y _ (hloc y hy) fun w => (hO _ _).1 (h w)) (fun x w => n1 _ x.2 _ w.2)
    (fun y hy h => ⟨⟨⟨y, GlobalTheory.RowCover.mem_GfC_of_hasLoc t S.B hj y _ (hloc y hy)⟩,
      n2 e he y (mem_suppGrp.1 hy) fun w hw => h ⟨w, hw⟩⟩, rfl⟩) (fun g => ?_) b r (mem_suppGrp.2 hre)
    (fun w => toFrame (G := locGrid G t w.1) one_le_sLen hj' (sgnAt G t s w.1 j))
    (fun w => toFrame (G := locGrid G t w.1) one_le_sLen hj' ((repsAt G t w.1).elt (β w) (D.R.m, j)))
    (fun w => (frameGL_mem_KO _ _).2 (diagGL_sign_mem_KO _ s)) (fun w => ?_) (fun w y => ?_)).trans ?_
  · obtain ⟨y, e', he', hy, h⟩ := exists_hasLoc hL S.B t hj fun w =>
      (toFrame (G := locGrid G t w.1) one_le_sLen hj').symm (g w)
    obtain rfl := idem_unique he he'
    exact ⟨y, mem_suppGrp.2 hy, fun w => (congrArg (toFrame (G := locGrid G t w.1) one_le_sLen hj') (h w)).trans
      (MulEquiv.apply_symm_apply _ _)⟩
  · exact (congrArg (toFrame (G := locGrid G t w.1) one_le_sLen hj') (hr w)).trans (map_mul _ _ _)
  · obtain ⟨-, a, ha, e⟩ := hb
    obtain ⟨f, hf⟩ := locAt_tilt S ht w.2 hj hj' hδ
    have e1 : locAt S.B t w.1 j hj δ = locAt S.B t w.1 j hj b := by
      rw [← e, map_mul, locAt_inf S.B t w.1 j hj ha, one_mul]
    rw [e1] at hf
    obtain ⟨f', hf'⟩ : ∃ f', (toFrame (G := locGrid G t w.1) one_le_sLen hj' (sgnAt G t s w.1 j)).val = diagonal f' :=
      frameGL_diagGL _ _
    refine diag_normalises (f := fun i => f i * f' i) ?_ y
    rw [Units.val_mul, hf', ← diagonal_mul_diagonal, ← hf]
    rfl
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [invVol_eq_idxRatio, conjLevel_eq G t w.1 hm.1 hj']

end Main

set_option maxHeartbeats 1600000 in

theorem cell_volume_mul_coef : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D,
    ∀ la : Measure ((GlobalTheory.CellMass.rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))), la.IsHaarMeasure →
      ∃ V₀ : ℝ, 0 < V₀ ∧ ∀ t (β : CosFam ch.G t) (b : Pts ch.G), IsRep t ch.S.B s β b →
        ∀ hb : b j ∈ GfC (ch.G.V (.grid D.R.m j)),
          la.real {n | (⟨b j, hb⟩ : GfC (ch.G.V (.grid D.R.m j)))⁻¹ * n.1 * ⟨b j, hb⟩ ∈ (latGrp ch.G j).subgroupOf _} *
            (GlobalTheory.RowWt.colCoef ch t β j : ℝ) = V₀ := by
  obtain ⟨CF0, hC⟩ := GlobalTheory.LatOfHasLoc.mem_latGrp_of_hasLoc
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hC ε CF hCF
  refine ⟨x₀, fun D large₂ he hx' Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  have hlat := hx D large₂ he hx' Γ Pl0 T A Ks R F hS ch hch hsc
  intro s j hi la hla
  have hm := idx_le hi
  have hj : j ≤ D.R.m := by omega
  have hj' : j < D.R.m := by omega
  have sp := GlobalTheory.RowGrpSplit.grpAt_all ch j hi
  obtain ⟨δ, hδ⟩ := exists_isTilt ch.G j
  obtain ⟨b₀, hb₀⟩ := exists_isFinOf _ δ
  let f : (GlobalTheory.CellMass.rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) →* GA D (ch.G.V (.grid D.R.m j)) :=
    (GfC (ch.G.V (.grid D.R.m j))).subtype.comp ((GlobalTheory.CellMass.rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))).subtype
  have hf : Topology.IsClosedEmbedding f := sp.clB.isClosedEmbedding_subtypeVal.comp
    (((isClosed_rowN ch.G hi).preimage continuous_subtype_val).isClosedEmbedding_subtypeVal)
  have hset : ∀ c (hc : c ∈ GfC (ch.G.V (.grid D.R.m j))), (((cj (latGrp ch.G j) c).comap f : Subgroup _) : Set _) =
      {n : (GlobalTheory.CellMass.rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) |
        (⟨c, hc⟩ : GfC (ch.G.V (.grid D.R.m j)))⁻¹ * n.1 * ⟨c, hc⟩ ∈ (latGrp ch.G j).subgroupOf _} := fun c hc => Set.ext fun n =>
      mem_cj (K := latGrp ch.G j) (c := c) (x := f n)
  have hop : ∀ c ∈ GfC (ch.G.V (.grid D.R.m j)), IsOpen (((cj (latGrp ch.G j) c).comap f : Subgroup _) :
      Set ((GlobalTheory.CellMass.rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))))) := fun c hc => by
    rw [hset c hc]
    exact sp.opn.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  have hcp : ∀ c, IsCompact (((cj (latGrp ch.G j) c).comap f : Subgroup _) :
      Set ((GlobalTheory.CellMass.rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))))) := fun c => by
    refine hf.isCompact_preimage (K := (cj (latGrp ch.G j) c : Set (GA D (ch.G.V (.grid D.R.m j))))) ?_
    have e : cj (latGrp ch.G j) c = (latGrp ch.G j).map (MulAut.conj c).toMonoidHom :=
      Subgroup.ext fun x => mem_cj.trans mem_map_conj.symm
    rw [e]
    exact sp.cpt.image ((continuous_const.mul continuous_id).mul continuous_const)
  refine ⟨la.real ((cj (latGrp ch.G j) b₀).comap f), ENNReal.toReal_pos
    ((hop _ hb₀.1).measure_pos la ⟨1, one_mem _⟩).ne' (hcp _).measure_lt_top.ne, fun t β b hb hbj => ?_⟩
  obtain ⟨δ', r, hδ', hr, -, a, ha, e⟩ := hb.2 j hi hj
  obtain rfl := isTilt_unique hj' hδ hδ'
  have hrf := GlobalTheory.RowCover.mem_GfC_of_hasLoc t ch.S.B hj r _ hr
  have eb : b j = b₀ * r := by
    obtain ⟨h₀, a₀, ha₀, e₀⟩ := hb₀
    obtain ⟨E, hE⟩ := sp.prod
    have : E (⟨a, ha⟩, ⟨b j, hbj⟩) = E (⟨a₀, ha₀⟩, ⟨b₀ * r, mul_mem h₀ hrf⟩) := by
      rw [hE, hE]
      change a * b j = a₀ * (b₀ * r)
      rw [e, ← mul_assoc, e₀]
    exact congrArg (fun p => p.2.1) (E.injective this)
  have key := idxRatio_row hS.core.lev ch.S.toGridChoice (Set.mem_univ t) hi hj hj' (hlat t j hm.1 hj) s β hδ hb₀ hr
  rw [← eb] at key
  rw [← hset, ← real_mul_idxRatio la (hop _ hb₀.1) (hcp _) (hop _ hbj) (hcp _), key, GlobalTheory.RowWt.colCoef]
  simp only [dif_pos hj']

end GlobalTheory.SymmetricJacobianSignature
