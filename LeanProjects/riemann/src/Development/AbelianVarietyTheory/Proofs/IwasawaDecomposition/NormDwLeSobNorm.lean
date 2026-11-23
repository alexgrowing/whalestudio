import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexificationHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsKStableOnKFiniteVectors

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace ContDiff Topology

namespace GlobalTheory.TypeSum

abbrev Mx (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def lieOf (G : Mx n) : Set (Mx n) := {X | Xᴴ * G + G * X = 0}

def Words (Lie : Set (Mx n)) (S : List (List (Mx n))) : Prop := ∀ l ∈ S, ∀ X ∈ l, X ∈ Lie

abbrev Dw (σ : Mx n → (H →L[ℂ] H)) (l : List (Mx n)) (w : H) : H := l.foldr (dRep σ) w

abbrev Sm (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) (w : H) : Prop := SmoothVec (lieSet ε) σ w

def Ctrl (Lie Gs : Set (Mx n)) (σ : Mx n → (H →L[ℂ] H)) (S : List (List (Mx n))) : Prop :=
  ∃ B : Mx n → ℝ, Continuous B ∧ ∀ g ∈ Gs, ∀ w, SmoothVec Lie σ w → sobNorm σ S (σ g w) ≤ B g * sobNorm σ S w

def IsExpn (Lie Gs : Set (Mx n)) (σ : Mx n → (H →L[ℂ] H)) (S : List (List (Mx n))) (v : ℕ → H)
    (ℓ : ℕ → (H →ₗ[ℂ] ℂ)) (C : ℕ → ℝ) (f : Mx n → ℂ) : Prop :=
  (∀ i, SmoothVec Lie σ (v i)) ∧ (∀ i, 0 ≤ C i) ∧ (∀ i w, SmoothVec Lie σ w → ‖ℓ i w‖ ≤ C i * sobNorm σ S w) ∧
    Summable (fun i => C i * sobNorm σ S (v i)) ∧ ∀ g ∈ Gs, HasSum (fun i => ℓ i (σ g (v i))) (f g)

def HasType (Lie Gs : Set (Mx n)) (σ : Mx n → (H →L[ℂ] H)) (f : Mx n → ℂ) : Prop :=
  ∃ S, Words Lie S ∧ Ctrl Lie Gs σ S ∧ ∃ v ℓ C, IsExpn Lie Gs σ S v ℓ C f

def IsDerFam (ε : Fin n → Bool) (F : List (Mx n) → Mx n → ℂ) : Prop :=
  ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ X ∈ lieSet ε, ∀ g ∈ UJset ε,
    HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp (t • X))) (F (X :: l) g) 0

def FamGrowth (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ) : Prop :=
  ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖F l g‖ ≤ C * (1 + hs g) ^ N

def UMG (ε : Fin n → Bool) (f : Mx n → ℂ) : Prop :=
  ∃ (N : ℕ) (F : List (Mx n) → Mx n → ℂ), (∀ g ∈ UJset ε, F [] g = f g) ∧ IsDerFam ε F ∧ FamGrowth ε N F

def Std (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) : Prop :=
  IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ ∧ (∀ v, IsKFin ε σ v → Sm ε σ v) ∧ (∃ d, IsFdeg (muG ε) σ d) ∧
    ∃ v, IsKFin ε σ v ∧ v ≠ 0

def SobFun (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) (ξ : H → ℂ) : Prop :=
  (∀ x y, Sm ε σ x → Sm ε σ y → ξ (x + y) = ξ x + ξ y) ∧ (∀ (c : ℂ) x, Sm ε σ x → ξ (c • x) = c * ξ x) ∧
    ∃ S C, Words (lieSet ε) S ∧ ∀ w, Sm ε σ w → ‖ξ w‖ ≤ C * sobNorm σ S w

def AvgBd (σ : Mx n → (H →L[ℂ] H)) (T : H → H) (Z : Set (Mx n)) (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (x w : ι → H) (M : ℝ), 0 ≤ M → (∀ y ∈ Z, ‖∑ j, ⟪x j, σ y (w j)⟫_ℂ‖ ≤ M) →
    ‖∑ j, ⟪x j, T (w j)⟫_ℂ‖ ≤ C * M

def IsAvg (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) (T : H → H) : Prop :=
  ∃ (Z : Set (Mx n)) (C : ℝ), IsCompact Z ∧ Z ⊆ UJset ε ∧ 0 ≤ C ∧ AvgBd σ T Z C

def DomBy (ε : Fin n → Bool) (Z : Set (Mx n)) (C : ℝ) (g : Mx n) (F Φ : Mx n → ℂ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (a : ι → ℂ) (g' : ι → Mx n), (∀ j, g' j ∈ UJset ε) → ∀ M : ℝ, 0 ≤ M →
    (∀ y ∈ Z, ‖∑ j, a j * F (g * y * g' j)‖ ≤ M) → ‖∑ j, a j * Φ (g' j)‖ ≤ C * M

def kAvg (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) (e : KG ε → ℂ) (w : H) : H :=
  ∫ k, e k • σ (toMK k) w ∂(muK ε)

def KFinFun (ε : Fin n → Bool) (e : KG ε → ℂ) : Prop :=
  ∃ F : Submodule ℂ (KG ε → ℂ), FiniteDimensional ℂ F ∧ e ∈ F ∧ (∀ φ ∈ F, Continuous φ) ∧
    ∀ φ ∈ F, ∀ k₀ : KG ε, (fun k => φ (k₀ * k)) ∈ F ∧ (fun k => φ (k * k₀)) ∈ F

def CoefBound (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) : Prop :=
  ∀ a, Sm ε σ a → a ≠ 0 → ∀ N : ℕ, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
    ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieSet ε) σ ℓ → ∀ M : ℝ, 0 ≤ M →
      (∀ g ∈ UJset ε, ‖ℓ (σ g a)‖ ≤ M * (1 + hs g) ^ N) → ∀ w, Sm ε σ w → ‖ℓ w‖ ≤ C * M * sobNorm σ S w

section Banach

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def ModRep (ε : Fin n → Bool) (ρ : Mx n → (E →L[ℂ] E)) : Prop :=
  ρ 1 = 1 ∧ (∀ a ∈ UJset ε, ∀ b ∈ UJset ε, ρ (a * b) = (ρ a).comp (ρ b)) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ g ∈ UJset ε, ‖ρ g‖ ≤ C * (1 + hs g) ^ N

def Fam (ε : Fin n → Bool) (ρ : Mx n → (E →L[ℂ] E)) : Submodule ℂ (List (lie (Jm ε)) → E) where
  carrier := {v | (∀ (l : List (lie (Jm ε))) (X : lie (Jm ε)),
      HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • (X : Mx n))) (v l)) (v (X :: l)) 0) ∧
    (∀ (l₁ l₂ : List (lie (Jm ε))) (a : ℝ) (X Y : lie (Jm ε)),
      v (l₁ ++ (a • X + Y) :: l₂) = (a : ℂ) • v (l₁ ++ X :: l₂) + v (l₁ ++ Y :: l₂)) ∧
    ∀ (l₁ l₂ : List (lie (Jm ε))) (X Y Z : lie (Jm ε)), (Z : Mx n) = X * Y - Y * X →
      v (l₁ ++ X :: Y :: l₂) - v (l₁ ++ Y :: X :: l₂) = v (l₁ ++ Z :: l₂)}
  add_mem' := fun {v w} hv hw => ⟨fun l X => by simpa only [Pi.add_apply, map_add] using (hv.1 l X).fun_add (hw.1 l X),
    fun l₁ l₂ a X Y => by simp only [Pi.add_apply, hv.2.1, hw.2.1, smul_add]; abel,
    fun l₁ l₂ X Y Z h => by
      simp only [Pi.add_apply, ← hv.2.2 l₁ l₂ X Y Z h, ← hw.2.2 l₁ l₂ X Y Z h]; abel⟩
  zero_mem' := ⟨fun l X => by simpa using hasDerivAt_const (0 : ℝ) (0 : E), by simp, by simp⟩
  smul_mem' := fun c v hv => ⟨fun l X => by simpa only [Pi.smul_apply, map_smul] using (hv.1 l X).fun_const_smul c,
    fun l₁ l₂ a X Y => by simp only [Pi.smul_apply, hv.2.1, smul_add, smul_comm c (a : ℂ)],
    fun l₁ l₂ X Y Z h => by simp only [Pi.smul_apply, ← hv.2.2 l₁ l₂ X Y Z h, smul_sub]⟩

end Banach

variable {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}

theorem isUnit_Jm (ε : Fin n → Bool) : IsUnit (Jm ε) := IsUnit.of_mul_eq_one _ (Jm_mul_self ε)

theorem lieSet_eq (ε : Fin n → Bool) : lieSet ε = lieOf (Jm ε) := rfl

theorem lieSet_eq_lie (ε : Fin n → Bool) : lieSet ε = (lie (Jm ε) : Set (Mx n)) := rfl

theorem UJset_eq (ε : Fin n → Bool) : UJset ε = Formalism.QuantumDeterminants.UH (Jm ε) := rfl

theorem sm_iff {w : H} : Sm ε σ w ↔ w ∈ smooth (Jm ε) σ := Iff.rfl

theorem one_mem_UJ (ε : Fin n → Bool) : (1 : Mx n) ∈ UJset ε := (1 : UJ ε).2

theorem mul_mem_UJ {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  have := GlobalTheory.GardingVec.list_prod_mem (G := Jm ε) [a, b] (by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    exacts [ha, hb])
  rwa [List.prod_cons, List.prod_singleton] at this

theorem isUnit_of_UJ {g : Mx n} (hg : g ∈ UJset ε) : IsUnit g := isUnit_of_mem (isUnit_Jm ε) hg

theorem mul_inv_UJ {g : Mx n} (hg : g ∈ UJset ε) : g * g⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hg))

theorem inv_mul_UJ {g : Mx n} (hg : g ∈ UJset ε) : g⁻¹ * g = 1 :=
  Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hg))

theorem inv_eq_UJ {g : Mx n} (hg : g ∈ UJset ε) : g⁻¹ = Jm ε * gᴴ * Jm ε :=
  Matrix.inv_eq_right_inv (indefinite_unitary_inv_closed n ε g hg).1

theorem inv_mem_UJ {g : Mx n} (hg : g ∈ UJset ε) : g⁻¹ ∈ UJset ε := by
  have := conj_inv_mem (ε := ε) (P := g) (G := Jm ε) (isUnit_of_UJ hg) hg (one_mem_UJ ε)
  have e : gᴴ * Jm ε * g = Jm ε := hg
  show (g⁻¹)ᴴ * Jm ε * g⁻¹ = Jm ε
  conv_lhs => rw [← e]
  calc (g⁻¹)ᴴ * (gᴴ * Jm ε * g) * g⁻¹ = (g * g⁻¹)ᴴ * Jm ε * (g * g⁻¹) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [mul_inv_UJ hg]; simp

theorem exp_mem_UJ {X : Mx n} (hX : X ∈ lieSet ε) (t : ℝ) : NormedSpace.exp (t • X) ∈ UJset ε :=
  GlobalTheory.GardingVec.exp_mem (isUnit_Jm ε) hX t

theorem toMK_mem_K (k : KG ε) : toMK k ∈ Kset ε := k.2

theorem K_le_UJ {k : Mx n} (hk : k ∈ Kset ε) : k ∈ UJset ε := (maximal_compact_facts n ε).1 k hk

theorem continuous_toMK (ε : Fin n → Bool) : Continuous fun k : KG ε => toMK k :=
  (isClosedEmbeddingMatrix n ε).1.continuous.comp continuous_subtype_val

def adInv {g : Mx n} (hg : g ∈ UJset ε) (X : lie (Jm ε)) : lie (Jm ε) :=
  ⟨g⁻¹ * X * g, conj_mem_lie (isUnit_Jm ε) hg X.2⟩

theorem hs_nonneg (g : Mx n) : 0 ≤ hs g := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem continuous_hs : Continuous (hs : Mx n → ℝ) := by
  unfold hs; fun_prop

theorem hs_mul_le (a b : Mx n) : hs (a * b) ≤ hs a * hs b := by
  unfold hs
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  calc ‖(a * b) i j‖ ^ 2 ≤ (∑ k, ‖a i k‖ * ‖b k j‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        rw [Matrix.mul_apply]
        exact (norm_sum_le _ _).trans (le_of_eq (by simp))
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem one_add_hs_mul_le (a b : Mx n) : 1 + hs (a * b) ≤ (1 + hs a) * (1 + hs b) := by
  nlinarith [hs_mul_le a b, hs_nonneg a, hs_nonneg b]

theorem hs_inv {g : Mx n} (hg : g ∈ UJset ε) : hs g⁻¹ = hs g := by
  have hJ := (maximal_compact_facts n ε).2.2.1
  rw [inv_eq_UJ hg, ((hermitian_small_ball n ε).2 _ _ hJ).1, ((hermitian_small_ball n ε).2 _ _ hJ).2]
  unfold hs
  rw [Finset.sum_comm]
  simp

theorem sobNorm_nonneg (σ : Mx n → (H →L[ℂ] H)) (S : List (List (Mx n))) (w : H) : 0 ≤ sobNorm σ S w :=
  List.sum_nonneg fun x hx => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _

theorem sobNorm_append (σ : Mx n → (H →L[ℂ] H)) (S S' : List (List (Mx n))) (w : H) :
    sobNorm σ (S ++ S') w = sobNorm σ S w + sobNorm σ S' w := by
  simp [sobNorm]

theorem norm_Dw_le_sobNorm (σ : Mx n → (H →L[ℂ] H)) {S : List (List (Mx n))} {l : List (Mx n)} (hl : l ∈ S) (w : H) :
    ‖Dw σ l w‖ ≤ sobNorm σ S w :=
  List.single_le_sum (fun x hx => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _) _ (List.mem_map.2 ⟨l, hl, rfl⟩)

theorem Dw_append (σ : Mx n → (H →L[ℂ] H)) (l l' : List (Mx n)) (w : H) : Dw σ (l ++ l') w = Dw σ l (Dw σ l' w) :=
  List.foldr_append

theorem words_append {Lie : Set (Mx n)} {S S' : List (List (Mx n))} (h : Words Lie S) (h' : Words Lie S') :
    Words Lie (S ++ S') := fun l hl => (List.mem_append.1 hl).elim (h l) (h' l)

theorem sigma_mul (hσ : IsURepOn (UJset ε) σ) {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (w : H) :
    σ (a * b) w = σ a (σ b w) := by rw [hσ.1.2 a ha b hb]; rfl

theorem sigma_one (hσ : IsURepOn (UJset ε) σ) (w : H) : σ 1 w = w := by rw [hσ.1.1]; rfl

theorem inner_sigma (hσ : IsURepOn (UJset ε) σ) {g : Mx n} (hg : g ∈ UJset ε) (x w : H) :
    ⟪x, σ g w⟫_ℂ = ⟪σ g⁻¹ x, w⟫_ℂ := by
  have h := LinearIsometry.inner_map_map ⟨(σ g : H →ₗ[ℂ] H), hσ.2.1 _ hg⟩ (σ g⁻¹ x) w
  have e : σ g (σ g⁻¹ x) = x := by rw [← sigma_mul hσ hg (inv_mem_UJ hg), mul_inv_UJ hg, sigma_one hσ]
  rw [← h]
  exact congrArg (fun z => ⟪z, σ g w⟫_ℂ) e.symm

theorem Sm.translate (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : Sm ε σ w) {g : Mx n} (hg : g ∈ UJset ε) :
    Sm ε σ (σ g w) := translate_mem (isUnit_Jm ε) hσ hg hw

theorem Sm.word (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : Sm ε σ w) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) :
    Sm ε σ (Dw σ l w) := word_mem (isUnit_Jm ε) hσ l hl hw

theorem Dw_add (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {x y : H} (hx : Sm ε σ x)
    (hy : Sm ε σ y) : Dw σ l (x + y) = Dw σ l x + Dw σ l y := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) hσ l hl
  have := congrArg Subtype.val (L.map_add ⟨x, hx⟩ ⟨y, hy⟩)
  rw [Submodule.coe_add, hL, hL, hL] at this
  exact this

theorem Dw_smul (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) (c : ℂ) {x : H}
    (hx : Sm ε σ x) : Dw σ l (c • x) = c • Dw σ l x := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) hσ l hl
  have := congrArg Subtype.val (L.map_smul c ⟨x, hx⟩)
  rw [Submodule.coe_smul, hL, hL] at this
  exact this

theorem Dw_translate (hσ : IsURepOn (UJset ε) σ) {g : Mx n} (hg : g ∈ UJset ε) {w : H} (hw : Sm ε σ w)
    {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) :
    Dw σ l (σ g w) = σ g (Dw σ (l.map fun X => g⁻¹ * X * g) w) := by
  rw [Dw, word_translate (isUnit_Jm ε) hσ hg hw l hl, Dw, List.foldr_map]

theorem inner_Dw (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {y w : H}
    (hy : Sm ε σ y) (hw : Sm ε σ w) : ⟪y, Dw σ l w⟫_ℂ = (-1) ^ l.length * ⟪Dw σ l.reverse y, w⟫_ℂ := by
  induction l generalizing y with
  | nil => simp
  | cons X l ih =>
    have hX := hl X List.mem_cons_self
    have hl' := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have h1 := inner_dRep (isUnit_Jm ε) hσ hy (hw.word hσ hl') hX
    rw [List.reverse_cons, Dw_append, List.length_cons, pow_succ]
    have h2 := ih hl' (dRep_mem (isUnit_Jm ε) hσ hy hX)
    show ⟪y, dRep σ X (Dw σ l w)⟫_ℂ = _ * ⟪Dw σ l.reverse (dRep σ X y), w⟫_ℂ
    rw [h1, h2]; ring

theorem sobNorm_translate (hσ : IsURepOn (UJset ε) σ) {g : Mx n} (hg : g ∈ UJset ε) {w : H} (hw : Sm ε σ w)
    {S : List (List (Mx n))} (hS : Words (lieSet ε) S) :
    sobNorm σ S (σ g w) = sobNorm σ (S.map fun l => l.map fun X => g⁻¹ * X * g) w := by
  unfold sobNorm
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun l hl => ?_
  show ‖Dw σ l (σ g w)‖ = _
  rw [Dw_translate hσ hg hw (hS l hl), hσ.2.1 g hg]; rfl

theorem SobFun.exists_ext {ξ : H → ℂ} (h : SobFun ε σ ξ) :
    ∃ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieSet ε) σ ℓ ∧ ∀ w, Sm ε σ w → ℓ w = ξ w := by
  let f : smooth (Jm ε) σ →ₗ[ℂ] ℂ :=
    { toFun := fun w => ξ w
      map_add' := fun x y => h.1 _ _ x.2 y.2
      map_smul' := fun c x => h.2.1 c _ x.2 }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  have e : ∀ w, Sm ε σ w → g w = ξ w := fun w hw => LinearMap.congr_fun hg ⟨w, hw⟩
  obtain ⟨S, C, hS, hC⟩ := h.2.2
  exact ⟨g, ⟨S, C, hS, fun w hw => by rw [e w hw]; exact hC w hw⟩, e⟩

theorem sobFun_of_sobCont {ℓ : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) : SobFun ε σ ℓ :=
  ⟨fun _ _ _ _ => map_add _ _ _, fun _ _ _ => map_smul _ _ _, h⟩

theorem SobFun.translate (hσ : IsURepOn (UJset ε) σ) {ξ : H → ℂ} (h : SobFun ε σ ξ) {g : Mx n} (hg : g ∈ UJset ε) :
    SobFun ε σ fun w => ξ (σ g w) := by
  obtain ⟨h1, h2, S, C, hS, hC⟩ := h
  refine ⟨fun x y hx hy => by beta_reduce; rw [map_add, h1 _ _ (hx.translate hσ hg) (hy.translate hσ hg)],
    fun c x hx => by beta_reduce; rw [map_smul, h2 _ _ (hx.translate hσ hg)], S.map fun l => l.map fun X => g⁻¹ * X * g, C, ?_,
    fun w hw => by rw [← sobNorm_translate hσ hg hw hS]; exact hC _ (hw.translate hσ hg)⟩
  intro l hl X hX
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
  obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
  exact conj_mem_lie (isUnit_Jm ε) hg (hS l' hl' Y hY)

theorem SobFun.word (hσ : IsURepOn (UJset ε) σ) {ξ : H → ℂ} (h : SobFun ε σ ξ) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) : SobFun ε σ fun w => ξ (Dw σ l w) := by
  obtain ⟨h1, h2, S, C, hS, hC⟩ := h
  refine ⟨fun x y hx hy => by beta_reduce; rw [Dw_add hσ hl hx hy, h1 _ _ (hx.word hσ hl) (hy.word hσ hl)],
    fun c x hx => by beta_reduce; rw [Dw_smul hσ hl c hx, h2 _ _ (hx.word hσ hl)], S.map (· ++ l), C, ?_, fun w hw => ?_⟩
  · intro l₁ hl₁ X hX
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl₁
    exact (List.mem_append.1 hX).elim (hS l' hl' X) (hl X)
  · have := hC _ (hw.word hσ hl)
    simpa [sobNorm, List.map_map, Function.comp_def, List.foldr_append] using this

theorem sobCont_translate (hσ : IsURepOn (UJset ε) σ) {ℓ : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) {g : Mx n}
    (hg : g ∈ UJset ε) : Sobolev₂ (lieSet ε) σ (ℓ ∘ₗ (σ g : H →ₗ[ℂ] H)) :=
  ((sobFun_of_sobCont h).translate hσ hg).2.2

theorem sobCont_inner (x : H) : Sobolev₂ (lieSet ε) σ (innerSL ℂ x : H →ₗ[ℂ] ℂ) :=
  ⟨[[]], ‖x‖, by simp, fun w _ => by simpa using norm_inner_le_norm x w⟩

theorem IsExpn.sobCont {Lie Gs : Set (Mx n)} {S : List (List (Mx n))} {v : ℕ → H} {ℓ : ℕ → (H →ₗ[ℂ] ℂ)} {C : ℕ → ℝ}
    {f : Mx n → ℂ} (h : IsExpn Lie Gs σ S v ℓ C f) (hS : Words Lie S) (i : ℕ) : Sobolev₂ Lie σ (ℓ i) :=
  ⟨S, C i, hS, h.2.2.1 i⟩

def kfin (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) : Submodule ℂ H :=
  GlobalTheory.KFiniteVectors.kFiniteVectors ε σ

theorem mem_kfin {v : H} : v ∈ kfin ε σ ↔ IsKFin ε σ v := Iff.rfl

theorem isKFin_translate {v : H} (hv : IsKFin ε σ v) {k : Mx n} (hk : k ∈ Kset ε) : IsKFin ε σ (σ k v) := by
  obtain ⟨S, h1, h2, h3⟩ := hv
  exact ⟨S, h1, h3 k hk v h2, h3⟩

theorem conj_one_eq (σ : Mx n → (H →L[ℂ] H)) : (fun g => σ (1 * g * (1 : Mx n)⁻¹)) = σ := by simp

theorem std_of_isDS (h : GlobalTheory.Published.HarishChandraModules) {lam : Fin n → ℝ} (hD : IsDS ε lam σ) : Std ε σ := by
  obtain ⟨_, _, hU, hI, hQ, ⟨S, h1, h2, -, ⟨v, hv, hv0, -⟩, -⟩, -⟩ := hD
  refine ⟨hU, hI, fun w hw => ?_, GlobalTheory.schur_orthogonality_unitary n ε H σ hU hI hQ, v, ⟨S, h1, hv, h2⟩, hv0⟩
  have := h.smoothVec hU hI hw (P := 1) (G := Jm ε) isUnit_one (by simp)
  rwa [conj_one_eq] at this

variable [CompleteSpace H]

theorem Std.dense_smoothAll (h : Std ε σ) : Dense (smoothAll (Jm ε) σ : Set H) := by
  obtain ⟨hσ, hi, -, -, u, -, hu0⟩ := h
  haveI : Nontrivial H := ⟨u, 0, hu0⟩
  refine dense_of_irred hi (fun g hg v hv k x hx hxG => ?_) ?_
  · letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
    letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
    have h1 := hv k (fun t => x t * g) (hx.mul contDiff_const) fun t => mul_mem_UJ (hxG t) hg
    convert h1 using 2 with t
    exact (sigma_mul hσ (hxG t) hg v).symm
  · obtain ⟨v, hv, hs⟩ := GlobalTheory.GardingVec.exists_garding hσ
    exact (Submodule.ne_bot_iff _).2 ⟨v, hs, hv⟩

theorem Std.dense_smooth (h : Std ε σ) : Dense (smooth (Jm ε) σ : Set H) :=
  h.dense_smoothAll.mono (smoothAll_le (isUnit_Jm ε))

theorem Std.continuousOn_Dw (h : Std ε σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    ContinuousOn (fun g => Dw σ l (σ g w)) (UJset ε) :=
  continuousOn_iff_continuous_restrict.2
    (continuous_word_orbit (isUnit_Jm ε) h.1 h.dense_smoothAll continuous_subtype_val (fun t => t.2) l hl hw)

theorem Std.continuousOn_coef (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {w : H} (hw : Sm ε σ w) :
    ContinuousOn (fun g => ℓ (σ g w)) (UJset ε) := by
  obtain ⟨m, S, Λ, hS, hΛ⟩ := exists_factor (isUnit_Jm ε) h.1 hℓ
  refine ContinuousOn.congr (f := fun g => ∑ i, Λ i (Dw σ (S i) (σ g w))) ?_ fun g hg => hΛ _ (hw.translate h.1 hg)
  exact continuousOn_finset_sum _ fun i _ => (Λ i).continuous.comp_continuousOn (h.continuousOn_Dw (hS i) hw)

theorem Std.eq_zero_of_orbit (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {u : H} (hu : Sm ε σ u)
    (hu0 : u ≠ 0) (h0 : ∀ g ∈ UJset ε, ℓ (σ g u) = 0) {w : H} (hw : Sm ε σ w) : ℓ w = 0 := by
  refine eq_zero_of_translates (P := 1) (G := Jm ε) h.1 h.2.1 isUnit_one (by simp) ?_ ?_ hu0 h0 ?_ <;>
    rw [conj_one_eq]
  exacts [hℓ, hu, hw]

theorem Std.dRep_sum (h : Std ε σ) {k : ℕ} {B : Fin k → Mx n} (hB : ∀ i, B i ∈ lieSet ε) {w : H} (hw : Sm ε σ w)
    (c : Fin k → ℝ) : dRep σ (∑ i, c i • B i) w = ∑ i, (c i : ℂ) • dRep σ (B i) w :=
  GlobalTheory.LowTypeDetermined.dRep_sum (isUnit_Jm ε) h.1 h.dense_smoothAll hB hw c

theorem exp_add_smul (X : Mx n) (s t : ℝ) :
    NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)

theorem continuous_exp_smul (X : Mx n) : Continuous fun t : ℝ => NormedSpace.exp (t • X) := by
  simpa only [Complex.coe_smul] using continuous_exp_real_smul X

omit [CompleteSpace H] in
theorem hasDerivAt_orbit (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : Sm ε σ w) {X : Mx n} (hX : X ∈ lieSet ε) (s : ℝ) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) (σ (NormedSpace.exp (s • X)) (dRep σ X w)) s := by
  have h1 := ((σ (NormedSpace.exp (s • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_dRep (G := Jm ε) hw hX)
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = σ _ (σ _ w)
  rw [← sigma_mul hσ (exp_mem_UJ hX _) (exp_mem_UJ hX _), ← exp_add_smul, add_sub_cancel]

theorem Std.hasDerivAt_Dw (h : Std ε σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w)
    {X : Mx n} (hX : X ∈ lieSet ε) :
    HasDerivAt (fun t : ℝ => Dw σ l (σ (NormedSpace.exp (t • X)) w)) (Dw σ l (dRep σ X w)) 0 := by
  have hw' : Sm ε σ (dRep σ X w) := dRep_mem (isUnit_Jm ε) h.1 hw hX
  have hc : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) →
      Continuous fun t : ℝ => Dw σ l (σ (NormedSpace.exp (t • X)) (dRep σ X w)) := fun l hl =>
    (h.continuousOn_Dw hl hw').comp_continuous (continuous_exp_smul X) (exp_mem_UJ hX)
  have e0 : ∀ z, σ (NormedSpace.exp ((0 : ℝ) • X)) z = z := fun z => by
    rw [zero_smul, NormedSpace.exp_zero, sigma_one h.1]
  have key : ∀ t : ℝ, Dw σ l (σ (NormedSpace.exp (t • X)) w) =
      Dw σ l w + ∫ s in (0 : ℝ)..t, Dw σ l (σ (NormedSpace.exp (s • X)) (dRep σ X w)) := by
    intro t
    have h0 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
      (fun s _ => hasDerivAt_orbit h.1 hw hX s) ((hc [] (by simp)).intervalIntegrable 0 t)
    rw [e0] at h0
    refine h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_
    have i1 := fun (z : H) (l : List (Mx n)) (hl : ∀ X ∈ l, X ∈ lieSet ε) =>
      (innerSL ℂ z).intervalIntegral_comp_comm ((hc l hl).intervalIntegrable (μ := volume) 0 t)
    simp only [innerSL_apply_apply] at i1
    have i2 := i1 (Dw σ l.reverse y) [] (by simp)
    simp only [Dw, List.foldr_nil] at i2
    rw [inner_add_right, ← i1 y l hl, inner_Dw h.1 hl hy (hw.translate h.1 (exp_mem_UJ hX t)), inner_Dw h.1 hl hy hw]
    simp only [fun s => inner_Dw h.1 hl hy (hw'.translate h.1 (exp_mem_UJ hX s))]
    rw [intervalIntegral.integral_const_mul, i2, h0, inner_sub_right]
    ring
  simp only [key]
  have := ((hc l hl).integral_hasStrictDerivAt 0 0).hasDerivAt.const_add (Dw σ l w)
  rwa [e0] at this

theorem Std.hasDerivAt_sobFun (h : Std ε σ) {ξ : H → ℂ} (hξ : SobFun ε σ ξ) {w : H} (hw : Sm ε σ w)
    {X : Mx n} (hX : X ∈ lieSet ε) :
    HasDerivAt (fun t : ℝ => ξ (σ (NormedSpace.exp (t • X)) w)) (ξ (dRep σ X w)) 0 := by
  obtain ⟨ℓ, hℓ, e⟩ := hξ.exists_ext
  have hw' : Sm ε σ (dRep σ X w) := dRep_mem (isUnit_Jm ε) h.1 hw hX
  obtain ⟨m, S, Λ, hS, hΛ⟩ := exists_factor (isUnit_Jm ε) h.1 hℓ
  simp only [fun t => (e _ (hw.translate h.1 (exp_mem_UJ hX t))).symm.trans
    (hΛ _ (hw.translate h.1 (exp_mem_UJ hX t))), (e _ hw').symm.trans (hΛ _ hw')]
  exact HasDerivAt.fun_sum fun i _ =>
    ((Λ i).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (h.hasDerivAt_Dw (hS i) hw hX)

end GlobalTheory.TypeSum

end
