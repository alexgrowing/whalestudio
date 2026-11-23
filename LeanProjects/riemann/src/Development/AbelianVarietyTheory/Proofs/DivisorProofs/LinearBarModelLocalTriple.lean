import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapNegApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisSliceT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentCharacterValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceTransformSchwartzBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestExtra
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
noncomputable section

namespace GlobalTheory.SwapSchur

open GlobalTheory.SwapSlice

def splitC {R : Type} {m n : ℕ} (Y : Matrix (Fin m) (Fin (n + n)) R) :
    Matrix (Fin m) (Fin n) R × Matrix (Fin m) (Fin n) R :=
  (fun i j => Y i (Fin.castAdd n j), fun i j => Y i (Fin.natAdd n j))

def joinC {R : Type} {m n : ℕ} (Z : Matrix (Fin m) (Fin n) R × Matrix (Fin m) (Fin n) R) :
    Matrix (Fin m) (Fin (n + n)) R :=
  fun i => Fin.append (Z.1 i) (Z.2 i)

theorem splitC_joinC {R : Type} {m n : ℕ} (Z : Matrix (Fin m) (Fin n) R × Matrix (Fin m) (Fin n) R) :
    splitC (joinC Z) = Z := by
  rcases Z with ⟨Z₁, Z₂⟩
  simp only [splitC, joinC, Fin.append_left, Fin.append_right]

theorem joinC_splitC {R : Type} {m n : ℕ} (Y : Matrix (Fin m) (Fin (n + n)) R) : joinC (splitC Y) = Y := by
  funext i
  exact Fin.append_castAdd_natAdd

theorem splitC_add {R : Type} [Add R] {m n : ℕ} (Y C : Matrix (Fin m) (Fin (n + n)) R) :
    splitC (Y + C) = splitC Y + splitC C := rfl

theorem swapNeg_swapNeg {Y : Type} [InvolutiveNeg Y] (Z : Y × Y) : swapNeg (swapNeg Z) = Z := by
  simp [swapNeg]

def swapH {k : Type} [TopologicalSpace k] [AddGroup k] [IsTopologicalAddGroup k] {m n : ℕ} :
    Matrix (Fin m) (Fin (n + n)) k ≃ₜ (Matrix (Fin m) (Fin n) k × Matrix (Fin m) (Fin n) k) where
  toFun Y := swapNeg (splitC Y)
  invFun Z := joinC (swapNeg Z)
  left_inv Y := by
    show joinC (swapNeg (swapNeg (splitC Y))) = Y
    rw [swapNeg_swapNeg, joinC_splitC]
  right_inv Z := by
    show swapNeg (splitC (joinC (swapNeg Z))) = Z
    rw [splitC_joinC, swapNeg_swapNeg]
  continuous_toFun := by
    have h1 : Continuous fun Y : Matrix (Fin m) (Fin (n + n)) k => (splitC Y).1 :=
      continuous_matrix fun i j => continuous_id.matrix_elem i (Fin.castAdd n j)
    have h2 : Continuous fun Y : Matrix (Fin m) (Fin (n + n)) k => (splitC Y).2 :=
      continuous_matrix fun i j => continuous_id.matrix_elem i (Fin.natAdd n j)
    exact h2.neg.prodMk h1.neg
  continuous_invFun := by
    refine continuous_matrix fun i j => ?_
    cases j using Fin.addCases with
    | left j =>
      simp only [joinC, swapNeg, Fin.append_left, Matrix.neg_apply]
      exact (continuous_snd.matrix_elem i j).neg
    | right j =>
      simp only [joinC, swapNeg, Fin.append_right, Matrix.neg_apply]
      exact (continuous_fst.matrix_elem i j).neg

theorem comp_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {g : Y → ℂ}
    (hg : g ∈ SB Y) : g ∘ e ∈ SB X :=
  ⟨hg.1.comp_continuous e.continuous, hg.2.comp_homeomorph e⟩

theorem bijOn_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    Set.BijOn (fun g : Y → ℂ => g ∘ e) (SB Y : Set (Y → ℂ)) (SB X : Set (X → ℂ)) := by
  refine ⟨fun g hg => comp_mem_SB e hg, fun g _ g' _ h => funext fun y => ?_, fun f hf => ?_⟩
  · have := congrFun h (e.symm y)
    simpa using this
  · refine ⟨f ∘ e.symm, comp_mem_SB e.symm hf, ?_⟩
    funext x
    simp

theorem pairM_neg_left {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X Y : Matrix A C k) :
    GlobalTheory.FlipMatch.pairM (-X) Y = -GlobalTheory.FlipMatch.pairM X Y := by
  simp [GlobalTheory.FlipMatch.pairM, Finset.sum_neg_distrib]

theorem pairM_zero_right {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X : Matrix A C k) :
    GlobalTheory.FlipMatch.pairM X 0 = 0 := by
  simp [GlobalTheory.FlipMatch.pairM]

theorem pairM_zero_left {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (Y : Matrix A C k) :
    GlobalTheory.FlipMatch.pairM 0 Y = 0 := by
  simp [GlobalTheory.FlipMatch.pairM]

def formR {k : Type} [CommRing k] {m n : ℕ} (l : Matrix (Fin m) (Fin (n + n)) k →ₗ[k] k) : Matrix (Fin m) (Fin n) k :=
  fun i j => l (Matrix.single i (Fin.natAdd n j) 1)

def formL {k : Type} [CommRing k] {m n : ℕ} (l : Matrix (Fin m) (Fin (n + n)) k →ₗ[k] k) : Matrix (Fin m) (Fin n) k :=
  fun i j => -l (Matrix.single i (Fin.castAdd n j) 1)

theorem linForm_eq {k : Type} [CommRing k] {m n : ℕ} (l : Matrix (Fin m) (Fin (n + n)) k →ₗ[k] k)
    (Y : Matrix (Fin m) (Fin (n + n)) k) :
    l Y = GlobalTheory.FlipMatch.pairM (splitC Y).2 (formR l) -
      GlobalTheory.FlipMatch.pairM (splitC Y).1 (formL l) := by
  have e : ∀ i j, l (Matrix.single i j (Y i j)) = Y i j * l (Matrix.single i j 1) := fun i j => by
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y, map_sum]
  simp only [map_sum, e]
  simp only [GlobalTheory.FlipMatch.pairM, splitC, formR, formL, Fin.sum_univ_add, mul_neg, Finset.sum_neg_distrib,
    sub_neg_eq_add, Finset.sum_add_distrib]
  ring

end GlobalTheory.SwapSchur

open GlobalTheory.SwapSchur in

theorem GlobalTheory.SwapSchur.sliceT_swap_eq_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (f : AE F E), GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl (incM F G.V'.J)),
      ((w : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    ∀ S : (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ) →
        ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) → ℂ,
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v)) →
    (∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      ∀ Φ' ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), ∀ c : ℂ, S (c • Φ + Φ') = c • S Φ + S Φ') →
    (∀ u, At (evFin F v) u → ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (actB (cA σ) w u)) (S Φ)) →
    ∃ c : ℂ, ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (S Φ) = c • (GlobalTheory.SwapSlice.sliceT ι Φ ∘ GlobalTheory.SwapSlice.swapNeg) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v t ι hι d' hd' dd hdd f hf1 hf2 hf3 hf4 hf5 w hw S hSB hSlin hS
  classical
  obtain ⟨hdV', hdW⟩ := GlobalTheory.GramDet.gram_det_ne_zero F E σ B a a' G X om om' hT
  have hcm : IsCMExt F E σ := hT.base.cm
  have hstd : IsStd B.ψ := hT.base.std
  have hψc : Continuous B.ψ := hstd.1
  have hcont : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hψc v
  have hne : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v
  have hι' : G.M'.IsLin B.ψ (piW (t.comp σ)) (piW t)
      (fun u => -((1 : GL (Fin a') (Fv F v)).1ᵀ * G.V'.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ *
        (1 : GL (Fin (a + a')) (Fv F v)).1)) ι := hι
  have hbij := GlobalTheory.SwapSliceBij.sliceT_bijOn ι hι'.bij
  obtain ⟨-, hw2⟩ := GlobalTheory.SwapAtPlace.swap_at_acts σ hcm (d := a + a') (incM F G.V'.J) v t f hf1 hf2 hf3 hf4 hf5 w hw
  have hheis := GlobalTheory.SwapHeis.heis_sliceT F E σ B a a' G X om om' hT hdV' hdW v t ι hι d' hd' dd hdd
  choose xY hxYat hxY0 hxY using fun Z => (GlobalTheory.SplitCoord.exists_at_coord σ hcm G.V' G.W hdV' hdW v t Z).1
  choose xX hxXat hxX0 hxX using fun Z => (GlobalTheory.SplitCoord.exists_at_coord σ hcm G.V' G.W hdV' hdW v t Z).2

  have atT : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x → At (evFin F v) xᵀ :=
    fun x hx r hr => by rw [← Matrix.transpose_smul, hx r hr, Matrix.transpose_zero]
  have atNeg : ∀ x : Matrix (Fin (a + a')) (Fin a') (AE F E), At (evFin F v) x → At (evFin F v) (-x) :=
    fun x hx r hr => by rw [smul_neg, hx r hr, neg_zero]
  have atCols : ∀ u₁ u₂ : Matrix (Fin (a + a')) (Fin a') (AE F E), At (evFin F v) u₁ → At (evFin F v) u₂ →
      At (evFin F v) (Matrix.fromCols u₁ u₂) := by
    intro u₁ u₂ h1 h2 r hr
    ext i j
    cases j with
    | inl j => simpa using congrFun (congrFun (h1 r hr) i) j
    | inr j => simpa using congrFun (congrFun (h2 r hr) i) j

  have coX0 : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), x.map (piW t) = 0 → GlobalTheory.FlipMatch.coX t 1 1 x = 0 := by
    intro x hx; simp [GlobalTheory.FlipMatch.coX, hx]
  have coY0 : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), x.map (piW (t.comp σ)) = 0 →
      GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x = 0 := by
    intro x hx; simp [GlobalTheory.FlipMatch.coY, hx]
  have mapNeg : ∀ (π : AE F E →+* Fv F v) (x : Matrix (Fin a') (Fin (a + a')) (AE F E)), (-x).map π = -x.map π := by
    intro π x; ext i j; simp
  have coXneg : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E),
      GlobalTheory.FlipMatch.coX t 1 1 (-x) = -GlobalTheory.FlipMatch.coX t 1 1 x := by
    intro x; simp only [GlobalTheory.FlipMatch.coX, mapNeg]; simp [Matrix.mul_neg, Matrix.neg_mul]
  have coYneg : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E),
      GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 (-x) = -GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x := by
    intro x; simp only [GlobalTheory.FlipMatch.coY, mapNeg]; simp [Matrix.mul_neg, Matrix.neg_mul]

  let hH : Matrix (Fin a') (Fin ((a + a') + (a + a'))) (Fv F v) ≃ₜ
      (Matrix (Fin a') (Fin (a + a')) (Fv F v) × Matrix (Fin a') (Fin (a + a')) (Fv F v)) := swapH
  let ι₁ := (LinearMap.funLeft ℂ ℂ hH) ∘ₗ GlobalTheory.SwapSlice.sliceT ι
  have hι₁ : ∀ Φ Y, ι₁ Φ Y = GlobalTheory.SwapSlice.sliceT ι Φ (GlobalTheory.SwapSlice.swapNeg (splitC Y)) := fun _ _ => rfl
  let ι₂ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) →
      Matrix (Fin a') (Fin ((a + a') + (a + a'))) (Fv F v) → ℂ :=
    fun Φ Y => GlobalTheory.SwapSlice.sliceT ι (S Φ) (splitC Y)
  have hbij₁ : Set.BijOn ι₁ (SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) : Set _)
      (SB (Matrix (Fin a') (Fin ((a + a') + (a + a'))) (Fv F v)) : Set _) :=
    (bijOn_comp hH).comp hbij
  have hlin₂ : ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v),
      ∀ y ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y := by
    intro x hx y hy c
    funext Y
    simp only [ι₂, hSlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]

  have tMap : ∀ (π : AE F E →+* Fv F v) (x : Matrix (Fin a') (Fin (a + a')) (AE F E)), x.map π = 0 → xᵀ.map π = 0 := by
    intro π x hx; rw [Matrix.transpose_map, hx, Matrix.transpose_zero]
  have tNeg : ∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), (-xᵀ)ᵀ = -x := by
    intro x; rw [Matrix.transpose_neg, Matrix.transpose_transpose]
  have tr1 : ∀ x₁ x₂ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x₁ → At (evFin F v) x₂ →
      x₁.map (piW t) = 0 → x₂.map (piW t) = 0 →
      ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ Z,
      GlobalTheory.SwapSlice.sliceT ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols x₁ᵀ x₂ᵀ)) x) Z =
        GlobalTheory.SwapSlice.sliceT ι x (Z.1 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₁, Z.2 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₂) := by
    intro x₁ x₂ a1 a2 m1 m2 x hx Z
    have c1 : GlobalTheory.FlipMatch.coX t 1 1 x₁ᵀᵀ = 0 := by rw [Matrix.transpose_transpose]; exact coX0 _ m1
    have c2 : GlobalTheory.FlipMatch.coX t 1 1 x₂ᵀᵀ = 0 := by rw [Matrix.transpose_transpose]; exact coX0 _ m2
    rw [hheis x₁ᵀ x₂ᵀ (atT _ a1) (atT _ a2) (by rw [c1, pairM_zero_left]) (by rw [c2, pairM_zero_left]) x hx, c1, c2,
      Matrix.transpose_transpose, Matrix.transpose_transpose]
    simp only [pairM_zero_right, neg_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
  have tr2 : ∀ x₁ x₂ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x₁ → At (evFin F v) x₂ →
      x₁.map (piW t) = 0 → x₂.map (piW t) = 0 →
      ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ Z,
      GlobalTheory.SwapSlice.sliceT ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols x₁ᵀ x₂ᵀ)) x)) Z =
        GlobalTheory.SwapSlice.sliceT ι (S x) (Z.1 - GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₂, Z.2 - GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₁) := by
    intro x₁ x₂ a1 a2 m1 m2 x hx Z
    have c1 : GlobalTheory.FlipMatch.coX t 1 1 (-x₁ᵀ)ᵀ = 0 := by rw [tNeg, coXneg, coX0 _ m1, neg_zero]
    have c2 : GlobalTheory.FlipMatch.coX t 1 1 (-x₂ᵀ)ᵀ = 0 := by rw [tNeg, coXneg, coX0 _ m2, neg_zero]
    rw [hS _ (atCols _ _ (atT _ a1) (atT _ a2)) x hx, (hw2 _ _ (atT _ a1) (atT _ a2)).1 (tMap _ _ m1) (tMap _ _ m2),
      hheis (-x₂ᵀ) (-x₁ᵀ) (atNeg _ (atT _ a2)) (atNeg _ (atT _ a1)) (by rw [c2, pairM_zero_left])
        (by rw [c1, pairM_zero_left]) (S x) (hSB x hx), c1, c2, tNeg, tNeg, coYneg, coYneg]
    simp only [pairM_zero_right, neg_zero, add_zero, AddChar.map_zero_eq_one, one_mul, sub_eq_add_neg]
  have mu1 : ∀ x₁ x₂ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x₁ → At (evFin F v) x₂ →
      x₁.map (piW (t.comp σ)) = 0 → x₂.map (piW (t.comp σ)) = 0 →
      ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ Z,
      GlobalTheory.SwapSlice.sliceT ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols x₁ᵀ x₂ᵀ)) x) Z =
        GlobalTheory.LatVac.psiAt B.ψ v (-GlobalTheory.FlipMatch.pairM Z.1 (GlobalTheory.FlipMatch.coX t 1 1 x₁) +
          GlobalTheory.FlipMatch.pairM Z.2 (GlobalTheory.FlipMatch.coX t 1 1 x₂)) * GlobalTheory.SwapSlice.sliceT ι x Z := by
    intro x₁ x₂ a1 a2 m1 m2 x hx Z
    have c1 : GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₁ᵀᵀ = 0 := by rw [Matrix.transpose_transpose]; exact coY0 _ m1
    have c2 : GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 x₂ᵀᵀ = 0 := by rw [Matrix.transpose_transpose]; exact coY0 _ m2
    rw [hheis x₁ᵀ x₂ᵀ (atT _ a1) (atT _ a2) (by rw [c1, pairM_zero_right]) (by rw [c2, pairM_zero_right]) x hx, c1, c2,
      Matrix.transpose_transpose, Matrix.transpose_transpose, add_zero, add_zero]
  have mu2 : ∀ x₁ x₂ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) x₁ → At (evFin F v) x₂ →
      x₁.map (piW (t.comp σ)) = 0 → x₂.map (piW (t.comp σ)) = 0 →
      ∀ x ∈ SB (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v), ∀ Z,
      GlobalTheory.SwapSlice.sliceT ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols x₁ᵀ x₂ᵀ)) x)) Z =
        GlobalTheory.LatVac.psiAt B.ψ v (-GlobalTheory.FlipMatch.pairM Z.1 (GlobalTheory.FlipMatch.coX t 1 1 x₂) +
          GlobalTheory.FlipMatch.pairM Z.2 (GlobalTheory.FlipMatch.coX t 1 1 x₁)) * GlobalTheory.SwapSlice.sliceT ι (S x) Z := by
    intro x₁ x₂ a1 a2 m1 m2 x hx Z
    rw [hS _ (atCols _ _ (atT _ a1) (atT _ a2)) x hx, (hw2 _ _ (atT _ a1) (atT _ a2)).2 (tMap _ _ m1) (tMap _ _ m2)]
    exact mu1 x₂ x₁ a2 a1 m2 m1 (S x) (hSB x hx) Z
  obtain ⟨c, hc⟩ := GlobalTheory.LinSchur.eq_smul_of_commute (SB _) (GlobalTheory.LatVac.psiAt B.ψ v) hcont hne ι₁ ι₂ hbij₁ hlin₂
    (fun C x => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v
      (Matrix.fromCols (xY (-(splitC C).2))ᵀ (xY (-(splitC C).1))ᵀ)) x)
    (fun l x => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v
      (Matrix.fromCols (xX (formR l))ᵀ (xX (formL l))ᵀ)) x)
    (fun C x hx => ⟨GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ x hx, funext fun Y => by
        beta_reduce
        rw [hι₁, tr1 _ _ (hxYat _) (hxYat _) (hxY0 _) (hxY0 _) x hx, hxY, hxY, hι₁]
        simp only [GlobalTheory.SwapSlice.swapNeg, splitC_add, Prod.fst_add, Prod.snd_add, neg_add],
      funext fun Y => by
        beta_reduce
        show GlobalTheory.SwapSlice.sliceT ι (S _) (splitC Y) = GlobalTheory.SwapSlice.sliceT ι (S x) (splitC (Y + C))
        rw [tr2 _ _ (hxYat _) (hxYat _) (hxY0 _) (hxY0 _) x hx, hxY, hxY]
        simp only [splitC_add, sub_neg_eq_add]
        rfl⟩)
    (fun l x hx => ⟨GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ x hx, funext fun Y => by
        beta_reduce
        rw [hι₁, mu1 _ _ (hxXat _) (hxXat _) (hxX0 _) (hxX0 _) x hx, hxX, hxX, hι₁, linForm_eq l Y]
        congr 2
        simp only [GlobalTheory.SwapSlice.swapNeg, pairM_neg_left]
        ring,
      funext fun Y => by
        beta_reduce
        show GlobalTheory.SwapSlice.sliceT ι (S _) (splitC Y) = _ * GlobalTheory.SwapSlice.sliceT ι (S x) (splitC Y)
        rw [mu2 _ _ (hxXat _) (hxXat _) (hxX0 _) (hxX0 _) x hx, hxX, hxX, linForm_eq l Y]
        congr 2
        ring⟩)
  refine ⟨c, fun Φ hΦ => funext fun Z => ?_⟩
  have e : GlobalTheory.SwapSlice.sliceT ι (S Φ) (splitC (joinC Z)) =
      c * GlobalTheory.SwapSlice.sliceT ι Φ (GlobalTheory.SwapSlice.swapNeg (splitC (joinC Z))) := congrFun (hc Φ hΦ) (joinC Z)
  rw [splitC_joinC] at e
  exact e
