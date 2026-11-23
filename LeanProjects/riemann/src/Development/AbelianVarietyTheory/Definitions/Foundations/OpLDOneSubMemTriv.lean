import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Letter

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ

def slP {R : Type} [CommRing R] (m : Matrix (Fin 2) (Fin 2) ℤ) : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  MvPolynomial.aeval fun i => (m i 0 : R) • MvPolynomial.X 0 + (m i 1 : R) • MvPolynomial.X 1

def Pot (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) : Set (ℂ → MvPolynomial (Fin 2) R) :=
  {F | (∀ z, (F z).IsHomogeneous w) ∧ ∀ γ ∈ Γ, ∃ p, ∀ z ∈ Hs,
    slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) z)) - F z = p}

def Triv (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) : Set (ℂ → MvPolynomial (Fin 2) R) :=
  {F | ∃ (ψ : ℂ → MvPolynomial (Fin 2) R) (p : MvPolynomial (Fin 2) R),
    (∀ γ ∈ Γ, ∀ z ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (ψ (mob (ofSL γ) z)) = ψ z) ∧ ∀ z ∈ Hs, F z = ψ z + p}

def opP (R : Type) [CommRing R] (m : Matrix (Fin 2) (Fin 2) ℤ) :
    (ℂ → MvPolynomial (Fin 2) R) →ₗ[R] (ℂ → MvPolynomial (Fin 2) R) where
  toFun F z := slP m (F (mob (toGQ m) z))
  map_add' F G := by funext z; simp
  map_smul' c F := by funext z; simp

def opL (R : Type) [CommRing R] (N l : ℕ) :
    Letter → ((ℂ → MvPolynomial (Fin 2) R) →ₗ[R] (ℂ → MvPolynomial (Fin 2) R))
  | Letter.T q => (∑ j ∈ Finset.range q, opP R !![1, (j : ℤ); 0, (q : ℤ)]) +
      opP R ((sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])
  | Letter.U => ∑ j ∈ Finset.range l, opP R !![1, (j : ℤ); 0, (l : ℤ)]
  | Letter.D d => opP R (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ)

def admitted (N l : ℕ) : Letter → Prop
  | Letter.T q => q.Prime ∧ ¬ q ∣ N * l
  | Letter.U => True
  | Letter.D d => Nat.Coprime d N

def LetAlg (R : Type) [CommRing R] (S : Letter → Prop) : Subalgebra R (FreeAlgebra R Letter) :=
  Algebra.adjoin R (FreeAlgebra.ι R '' {T | S T})

def SSPot (N l w : ℕ) (lam : Letter → ℂ) : Prop :=
  ∃ P ∈ LetAlg ℂ (admitted N l), FreeAlgebra.lift ℂ lam P = 1 ∧ ∀ F ∈ Pot ℂ w (Gam N l), ∀ T : Letter, admitted N l T →
    (opL ℂ N l T - lam T • (1 : Module.End ℂ (ℂ → MvPolynomial (Fin 2) ℂ)))
      (FreeAlgebra.lift ℂ (opL ℂ N l) P F) ∈ Triv ℂ w (Gam N l)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def FrobAt (q : ℕ) (s : Ω ≃ₐ[ℚ] Ω) : Prop :=
  ∃ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits ∧ ∀ x ∈ V, s x ∈ V ∧ V.valuation (s x - x ^ q) < 1

def Tower.VB (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] :
    Submodule E (E ⊗[ℤ_[l]] X.Fn l) :=
  LinearMap.range (LinearMap.baseChange E (X.B N l w).subtype)

def Tower.opV (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (T : Letter) :
    Module.End E (E ⊗[ℤ_[l]] X.Fn l) :=
  LinearMap.baseChange E (X.op N l T)

def Tower.galV (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (s : Ω ≃ₐ[ℚ] Ω) :
    Module.End E (E ⊗[ℤ_[l]] X.Fn l) :=
  LinearMap.baseChange E (X.galB l s)

def Tower.SSB (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℤ_[l] E] (lam : Letter → E) : Prop :=
  ∃ P ∈ LetAlg E (admitted N l), FreeAlgebra.lift E lam P = 1 ∧ ∀ x ∈ X.VB N l w E, ∀ T : Letter, admitted N l T →
    (X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l))) (FreeAlgebra.lift E (X.opV N l E) P x) = 0

namespace Betti

section Letters

variable {R : Type} [CommRing R] {S : Letter → Prop}

theorem lift_congr {A : Type} [Semiring A] [Algebra R A] {f g : Letter → A} (h : ∀ T, S T → f T = g T)
    {P : FreeAlgebra R Letter} (hP : P ∈ LetAlg R S) : FreeAlgebra.lift R f P = FreeAlgebra.lift R g P := by
  unfold LetAlg at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    simp [h T hT]
  | algebraMap r => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | mul x y _ _ hx hy => simp [hx, hy]

end Letters

theorem exists_isDiam {N l d : ℕ} (hN : N ≠ 0) (hl : l ≠ 0) (hd : Nat.Coprime d N) : ∃ γ, IsDiam N l d γ := by
  have : NeZero (N * l) := ⟨Nat.mul_ne_zero hN hl⟩
  have hNl : N ∣ N * l := Dvd.intro l rfl
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hNl (ZMod.unitOfCoprime d hd)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime u)
  have hdet : (!![a, -b; ((N * l : ℕ) : ℤ), ((u : ZMod (N * l)).val : ℤ)]).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hab
  obtain ⟨γ, hγ⟩ : ∃ γ : SL(2, ℤ),
      (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, -b; ((N * l : ℕ) : ℤ), ((u : ZMod (N * l)).val : ℤ)] :=
    ⟨⟨_, hdet⟩, rfl⟩
  refine ⟨γ, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem, hγ]
    simp
  · rw [CongruenceSubgroup.Gamma0_mem, hγ]
    simp
  · have hcast : (((u : ZMod (N * l)).val : ℕ) : ZMod N) = d := by
      rw [ZMod.natCast_val, ← ZMod.unitsMap_val hNl, hu, ZMod.coe_unitOfCoprime]
    simpa [en, hγ] using hcast

theorem isDiam_sgD {N l d : ℕ} (hN : N ≠ 0) (hl : l ≠ 0) (hd : Nat.Coprime d N) : IsDiam N l d (sgD N l d) := by
  exact Classical.epsilon_spec (exists_isDiam hN hl hd)

theorem isDiam_sgD_of_adm {N l q : ℕ} (h : admitted N l (Letter.T q)) : IsDiam N l q (sgD N l q) := by
  have h' : q.Prime ∧ ¬ q ∣ N * l := h
  obtain ⟨hq, hqN⟩ := h'
  have hN : N ≠ 0 := by
    rintro rfl
    exact hqN (by simp)
  have hl : l ≠ 0 := by
    rintro rfl
    exact hqN (by simp)
  exact isDiam_sgD hN hl ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h'' => hqN (h''.mul_right l))

section Slash

variable {R : Type} [CommRing R]

theorem slP_X (m : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    slP (R := R) m (MvPolynomial.X i) = (m i 0 : R) • MvPolynomial.X 0 + (m i 1 : R) • MvPolynomial.X 1 := by
  simp only [slP, MvPolynomial.aeval_X]

theorem polySlash_one (p : MvPolynomial (Fin 2) R) : slP 1 p = p := by
  have h1 : slP (R := R) 1 = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [slP_X]
    fin_cases i <;> simp [Matrix.one_apply]
  rw [h1, AlgHom.id_apply]

theorem polySlash_polySlash (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    slP m' (slP m p) = slP (m * m') p := by
  have h1 : (slP m').comp (slP m) = slP (R := R) (m * m') := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, slP_X, map_add, map_smul, Matrix.mul_apply, Fin.sum_univ_two,
      Int.cast_add, Int.cast_mul]
    module
  exact DFunLike.congr_fun h1 p

theorem polySlash_isHomogeneous (m : Matrix (Fin 2) (Fin 2) ℤ) {p : MvPolynomial (Fin 2) R} {w : ℕ} (hp : p.IsHomogeneous w) :
    (slP m p).IsHomogeneous w := by
  have h1 := hp.aeval (fun i => (m i 0 : R) • MvPolynomial.X 0 + (m i 1 : R) • MvPolynomial.X 1)
    (n := 1) fun i => (MvPolynomial.homogeneousSubmodule (Fin 2) R 1).add_mem
      ((MvPolynomial.homogeneousSubmodule (Fin 2) R 1).smul_mem _ (MvPolynomial.isHomogeneous_X R 0))
      ((MvPolynomial.homogeneousSubmodule (Fin 2) R 1).smul_mem _ (MvPolynomial.isHomogeneous_X R 1))
  rw [one_mul] at h1
  exact h1

theorem eval_slP (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.eval u (slP m p) = MvPolynomial.eval (m.map (Int.castRingHom R) *ᵥ u) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, slP_X, MvPolynomial.eval_X, map_add, MvPolynomial.smul_eval]
    congr 1
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem toGQ_sl (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact one_pos
  unfold toGQ
  rw [dif_pos h]
  apply Subtype.ext
  apply Units.ext
  rfl

variable {w : ℕ} {Γ : Subgroup SL(2, ℤ)}

def potSub (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) : Submodule R (ℂ → MvPolynomial (Fin 2) R) where
  carrier := Pot R w Γ
  zero_mem' := ⟨fun _ => MvPolynomial.isHomogeneous_zero _ _ _, fun _ _ => ⟨0, fun _ _ => by simp⟩⟩
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    refine ⟨fun z => (hF z).add (hG z), fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    obtain ⟨q, hq⟩ := hG' γ hγ
    refine ⟨p + q, fun z hz => ?_⟩
    rw [← hp z hz, ← hq z hz]; simp only [Pi.add_apply, map_add]; ring
  smul_mem' := by
    rintro c F ⟨hF, hF'⟩
    refine ⟨fun z => (MvPolynomial.homogeneousSubmodule (Fin 2) R w).smul_mem c (hF z), fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    refine ⟨c • p, fun z hz => ?_⟩
    rw [← hp z hz]; simp only [Pi.smul_apply, map_smul, smul_sub]

def trivSub (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)) : Submodule R (ℂ → MvPolynomial (Fin 2) R) where
  carrier := Triv R w Γ
  zero_mem' := ⟨0, 0, fun _ _ _ _ => by simp, fun _ _ => by simp⟩
  add_mem' := by
    rintro F G ⟨ψ, p, h1, h2⟩ ⟨ψ', p', h1', h2'⟩
    refine ⟨ψ + ψ', p + p', fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp [h1 γ hγ z hz, h1' γ hγ z hz]
    · simp only [Pi.add_apply, h2 z hz, h2' z hz]; ring
  smul_mem' := by
    rintro c F ⟨ψ, p, h1, h2⟩
    refine ⟨c • ψ, c • p, fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp [h1 γ hγ z hz]
    · simp [h2 z hz]

@[simp] theorem mem_potSub {F : ℂ → MvPolynomial (Fin 2) R} : F ∈ potSub R w Γ ↔ F ∈ Pot R w Γ := by exact Iff.rfl

@[simp] theorem mem_trivSub {F : ℂ → MvPolynomial (Fin 2) R} : F ∈ trivSub R w Γ ↔ F ∈ Triv R w Γ := by exact Iff.rfl

end Slash

example : slP (R := ℤ) !![1, 2; 0, 3] (MvPolynomial.X 0) = MvPolynomial.X 0 + 2 * MvPolynomial.X 1 := by
  simp [slP_X, MvPolynomial.smul_eq_C_mul]

example : admitted 5 3 (Letter.T 2) ∧ ¬ admitted 5 3 (Letter.T 0) ∧ ¬ admitted 5 3 (Letter.T 1) ∧ ¬ admitted 5 3 (Letter.T 3) ∧
    ¬ admitted 5 3 (Letter.T 4) ∧ admitted 5 3 (Letter.D 3) ∧ ¬ admitted 5 3 (Letter.D 0) := by
  simp only [admitted]; decide

example : FreeAlgebra.ι ℂ (Letter.T 0) ∉ LetAlg ℂ (admitted 5 3) := by
  intro h
  have := lift_congr (f := fun _ => (0 : ℂ)) (g := fun T => match T with | Letter.T 0 => 1 | _ => 0) (fun T hT => by
    rcases T with (_ | q) | _ | d
    · exact absurd hT.1 Nat.not_prime_zero
    all_goals rfl) h
  simp at this

example (s : Ω ≃ₐ[ℚ] Ω) : ¬ FrobAt 1 s := by
  rintro ⟨V, h, -⟩
  simp [ValuationSubring.mem_nonunits_iff] at h

end Betti

end GlobalTheory.KZ
