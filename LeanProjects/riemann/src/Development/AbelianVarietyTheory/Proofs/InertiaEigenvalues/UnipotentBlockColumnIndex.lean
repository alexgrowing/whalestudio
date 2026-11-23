import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep

namespace GlobalTheory.CuspGeneric

section Avg

variable {G : Type} [AddCommGroup G] [TopologicalSpace G]

def IsCoLat (Γ : AddSubgroup G) : Prop :=
  DiscreteTopology Γ ∧ ∃ K : Set G, IsCompact K ∧ ∀ x, ∃ γ ∈ Γ, γ + x ∈ K

def Per (Γ : AddSubgroup G) (Φ : G → ℂ) : Prop := Continuous Φ ∧ ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x

open Classical in

def avg (Γ : AddSubgroup G) (Φ : G → ℂ) : ℂ :=
  letI : MeasurableSpace G := borel G
  if h : ∃ p : Measure G × Set G, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ p.2 p.1 ∧ p.1 p.2 = 1
  then ∫ x in h.choose.2, Φ x ∂h.choose.1 else 0

theorem avg_const_mul (Γ : AddSubgroup G) (c : ℂ) (Φ : G → ℂ) : avg Γ (fun x => c * Φ x) = c * avg Γ Φ := by
  letI : MeasurableSpace G := borel G
  simp only [avg]
  split_ifs
  · exact integral_const_mul _ _
  · simp

end Avg

section Adelic

variable (E : Type) [Field E] [NumberField E]

scoped instance instLC : LocallyCompactSpace (Ad E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
scoped instance instSC : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
scoped instance t2Space_cuspAdeles : T2Space (Ad E) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E

def ratV (ι : Type) : AddSubgroup (ι → Ad E) :=
  (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom ι).range

theorem isCoLat_ratV (ι : Type) [Finite ι] : IsCoLat (ratV E ι) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨U, hU, h0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero E
    obtain ⟨V, hVU, hVo, hV0⟩ := mem_nhds_iff.1 hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have hW : IsOpen (Set.pi Set.univ fun _ : ι => V) :=
      isOpen_set_pi Set.finite_univ fun _ _ => hVo
    convert hW.preimage (continuous_subtype_val (p := fun x => x ∈ ratV E ι)) using 1
    ext ⟨_, x, rfl⟩
    constructor
    · intro h p _
      have h1 := congrFun (congrArg Subtype.val (Set.mem_singleton_iff.1 h)) p
      exact h1.symm ▸ hV0
    · intro h
      have hx : x = 0 := funext fun p => h0 (x p) (hVU (h p trivial))
      subst hx
      exact Subtype.ext (map_zero _)
  · obtain ⟨K, hK, h⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele E
    refine ⟨Set.pi Set.univ fun _ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
    choose y hy using fun p => h (x p)
    refine ⟨_, ⟨fun p => -y p, rfl⟩, fun p _ => ?_⟩
    change algebraMap E (Ad E) (-y p) + x p ∈ K
    rw [map_neg, neg_add_eq_sub]
    exact hy p

end Adelic

section Pos

variable {R : Type} [CommRing R] {a : ℕ} {ι : Type} [Fintype ι]

def IsNil (p : ι → Fin a × Fin a) : Prop := ∀ s t, (p s).2 ≠ (p t).1

def posM (p : ι → Fin a × Fin a) (x : ι → R) : Matrix (Fin a) (Fin a) R :=
  ∑ t, Matrix.single (p t).1 (p t).2 (x t)

theorem posM_mul {p : ι → Fin a × Fin a} (hp : IsNil p) (x y : ι → R) : posM p x * posM p y = 0 := by
  simp only [posM, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
  exact Matrix.single_mul_single_of_ne _ _ _ _ (hp _ _) _

theorem posM_add (p : ι → Fin a × Fin a) (x y : ι → R) : posM p (x + y) = posM p x + posM p y := by
  simp only [posM, Pi.add_apply, Matrix.single_add, Finset.sum_add_distrib]

def posU {p : ι → Fin a × Fin a} (hp : IsNil p) (x : ι → R) : GL (Fin a) R :=
  ⟨1 + posM p x, 1 - posM p x, by simp [mul_sub, add_mul, posM_mul hp], by simp [sub_mul, mul_add, posM_mul hp]⟩

theorem posU_val {p : ι → Fin a × Fin a} (hp : IsNil p) (x : ι → R) : (posU hp x).val = 1 + posM p x := rfl

theorem posU_add {p : ι → Fin a × Fin a} (hp : IsNil p) (x y : ι → R) : posU hp (x + y) = posU hp x * posU hp y := by
  apply Units.ext
  change 1 + posM p (x + y) = (1 + posM p x) * (1 + posM p y)
  rw [posM_add]; simp only [mul_add, add_mul, one_mul, mul_one, posM_mul hp]; abel

theorem posU_zero {p : ι → Fin a × Fin a} (hp : IsNil p) : posU hp (0 : ι → R) = 1 := by
  apply Units.ext
  change 1 + posM p 0 = 1
  simp [posM]

theorem continuous_posU [TopologicalSpace R] [IsTopologicalRing R] {p : ι → Fin a × Fin a} (hp : IsNil p) :
    Continuous (posU hp : (ι → R) → GL (Fin a) R) := by
  have h : Continuous fun x : ι → R => posM p x := by
    refine continuous_finset_sum _ fun t _ => ?_
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.single_apply]
    split_ifs
    · exact continuous_apply t
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨continuous_const.add h, continuous_const.sub h⟩

abbrev UnipotentBlockColumnIndex (a r m : ℕ) : Type := {p : Fin a × Fin a // (p.1 : ℕ) < r ∧ r ≤ (p.2 : ℕ) ∧ (p.2 : ℕ) ≤ m}

theorem isNil_blk (a r m : ℕ) : IsNil (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) := fun s t e => by
  have h1 := s.2.2.1
  have h2 := t.2.1
  rw [e] at h1
  omega

def blkU {r m : ℕ} (x : UnipotentBlockColumnIndex a r m → R) : GL (Fin a) R := posU (isNil_blk a r m) x

end Pos

section Fn

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

omit [NumberField E] in

theorem map_posU {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} [Fintype ι]
    {p : ι → Fin a × Fin a} (hp : IsNil p) (x : ι → R) :
    GeneralLinearGroup.map φ (posU hp x) = posU hp (fun t => φ (x t)) := by
  apply Units.ext
  ext i j
  change φ ((1 + posM p x) i j) = (1 + posM p fun t => φ (x t)) i j
  simp only [posM, Matrix.add_apply, Matrix.sum_apply, map_add, map_sum, Matrix.one_apply, Matrix.single_apply]
  congr 1
  · split_ifs <;> simp
  · refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp

def dot {ι : Type} [Fintype ι] (ξ : ι → E) (x : ι → Ad E) : Ad E := ∑ t, algebraMap E (Ad E) (ξ t) * x t

def eLast (a k : ℕ) : UnipotentBlockColumnIndex a k k → E := fun t => if (t.1.1 : ℕ) + 1 = k then 1 else 0

structure StdPsi (ψ : AddChar (Ad E) ℂ) : Prop where
  cont : Continuous ψ
  norm : ∀ x, ‖ψ x‖ = 1
  rat : ∀ c : E, ψ (algebraMap E (Ad E) c) = 1
  ann : ∀ x, (∀ c : E, ψ (x * algebraMap E (Ad E) c) = 1) → ∃ d : E, x = algebraMap E (Ad E) d
  loc : ∀ w : HeightOneSpectrum (𝓞 E), ∃ y : w.adicCompletion E, ψ (sFin E (sLoc E w y)) ≠ 1

def coefF (ψ : AddChar (Ad E) ℂ) (k : ℕ) (ξ : UnipotentBlockColumnIndex a k k → E) (f : GA E a → ℂ) (g : GA E a) : ℂ :=
  avg (ratV E (UnipotentBlockColumnIndex a k k)) fun x => ψ (-dot ξ x) * f (blkU x * g)

def colT (ψ : AddChar (Ad E) ℂ) (k : ℕ) (f : GA E a → ℂ) : GA E a → ℂ := coefF ψ k (eLast a k) f

def whit (ψ : AddChar (Ad E) ℂ) (m : ℕ) : (GA E a → ℂ) → GA E a → ℂ :=
  Nat.rec (fun f => f) (fun m ih f => ih (colT ψ (m + 1) f)) m

theorem whit_zero (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ) : whit ψ 0 f = f := rfl

theorem whit_succ (ψ : AddChar (Ad E) ℂ) (m : ℕ) (f : GA E a → ℂ) : whit ψ (m + 1) f = whit ψ m (colT ψ (m + 1) f) := rfl

def IsMir (m : ℕ) (γ : GL (Fin a) E) : Prop :=
  ∀ i k : Fin a, (m ≤ (i : ℕ) ∨ m < (k : ℕ)) → γ.val i k = (1 : Matrix (Fin a) (Fin a) E) i k

structure Good (ψ : AddChar (Ad E) ℂ) (m : ℕ) (f : GA E a → ℂ) : Prop where
  cont : Continuous f
  left : ∀ γ : GL (Fin a) E, IsMir m γ → ∀ g, f (ratGL E a γ * g) = f g
  law : ∀ k, m < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g
  van : ∀ r, 0 < r → r ≤ m → ∀ g : GA E a, avg (ratV E (UnipotentBlockColumnIndex a r m)) (fun x => f (blkU x * g)) = 0

theorem ratGL_blkU {r m : ℕ} (c : UnipotentBlockColumnIndex a r m → E) :
    ratGL E a (blkU c) = blkU (fun t => algebraMap E (Ad E) (c t)) := map_posU _ _ _

theorem isMir_blkU {r m : ℕ} (c : UnipotentBlockColumnIndex a r m → E) : IsMir m (blkU c) := by
  intro i k h
  change (1 + posM Subtype.val c : Matrix (Fin a) (Fin a) E) i k = _
  rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero]
  intro t _
  have h1 := t.2
  rw [Matrix.single_apply_of_ne]
  rintro ⟨e1, e2⟩
  rw [← e1, ← e2] at h
  omega

variable {ψ : AddChar (Ad E) ℂ}

theorem StdPsi.map_dot (hψ : StdPsi ψ) {ι : Type} [Fintype ι] (ξ c : ι → E) (x : ι → Ad E) :
    ψ (dot ξ ((fun t => algebraMap E (Ad E) (c t)) + x)) = ψ (dot ξ x) := by
  have : dot ξ ((fun t => algebraMap E (Ad E) (c t)) + x) =
      algebraMap E (Ad E) (∑ t, ξ t * c t) + dot ξ x := by
    simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_sum, map_mul]
  rw [this, AddChar.map_add_eq_mul, hψ.rat, one_mul]

theorem continuous_dot {ι : Type} [Fintype ι] (ξ : ι → E) : Continuous (dot ξ : (ι → Ad E) → Ad E) :=
  continuous_finset_sum _ fun t _ => continuous_const.mul (continuous_apply t)

theorem per_blk {r m : ℕ} {f : GA E a → ℂ} (hc : Continuous f)
    (hl : ∀ (c : UnipotentBlockColumnIndex a r m → E) g, f (ratGL E a (blkU c) * g) = f g) (g : GA E a) :
    Per (ratV E (UnipotentBlockColumnIndex a r m)) (fun x => f (blkU x * g)) := by
  refine ⟨hc.comp ((continuous_posU _).mul continuous_const), ?_⟩
  rintro _ ⟨c, rfl⟩ x
  have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (UnipotentBlockColumnIndex a r m)) c =
      fun t => algebraMap E (Ad E) (c t) := rfl
  rw [e]
  change f (posU _ _ * g) = _
  rw [posU_add, mul_assoc]
  change f (blkU _ * _) = _
  rw [← ratGL_blkU, hl]
  rfl

theorem per_coef (hψ : StdPsi ψ) {k : ℕ} (ξ : UnipotentBlockColumnIndex a k k → E) {f : GA E a → ℂ} (hc : Continuous f)
    (hl : ∀ (c : UnipotentBlockColumnIndex a k k → E) g, f (ratGL E a (blkU c) * g) = f g) (g : GA E a) :
    Per (ratV E (UnipotentBlockColumnIndex a k k)) (fun x => ψ (-dot ξ x) * f (blkU x * g)) := by
  obtain ⟨h1, h2⟩ := per_blk hc hl g
  refine ⟨((hψ.cont.comp (continuous_dot ξ).neg).mul h1), ?_⟩
  rintro _ ⟨c, rfl⟩ x
  have e := h2 _ ⟨c, rfl⟩ x
  simp only at e ⊢
  rw [e, AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv]
  congr 2
  exact hψ.map_dot ξ c x

end Fn

end GlobalTheory.CuspGeneric
