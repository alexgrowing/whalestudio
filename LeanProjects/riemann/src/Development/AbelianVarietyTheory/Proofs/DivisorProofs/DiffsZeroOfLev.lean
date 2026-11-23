import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.ThK.DescB

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (σ) in

def finK {n : ℕ} (W : Spc F E n) (τ : ∀ w : InfinitePlace F, EmbOver E w) : Set (UA σ W.J) :=
  {x | ∃ k ∈ KInf σ W τ, ∃ g ∈ UAt σ W (fun u : AF F => u.2), x = k * g}

def SplitZ {n n₁ : ℕ} {W : Spc F E n} (W₁ : Spc F E n₁) (H : Plane E n n₁) (χa χb : Chr F E) (za zb : ℝ)
    (f fa fb : UA σ W.J → ℂ) : Prop :=
  IsCT H f (fa + fb) ∧ HasLaw W₁ H χa za fa ∧ HasLaw W₁ H χb zb fb

def BetaZero {n n₁ : ℕ} {W : Spc F E n} (W₁ : Spc F E n₁) (H : Plane E n n₁) (χa χb : Chr F E) (za zb : ℝ)
    (S : Submodule ℂ (UA σ W.J → ℂ)) : Prop :=
  ∀ f ∈ S, ∀ fa fb, SplitZ W₁ H χa χb za zb f fa fb → fb = 0

def alphaSpan {n n₁ : ℕ} {W : Spc F E n} (W₁ : Spc F E n₁) (H : Plane E n n₁) (χa χb : Chr F E) (za zb : ℝ)
    (Kh : Set (UA σ W.J)) (S : Submodule ℂ (UA σ W.J → ℂ)) : Submodule ℂ (UA σ W₁.J → ℂ) :=
  Submodule.span ℂ {g | ∃ f ∈ S, ∃ fa fb, SplitZ W₁ H χa χb za zb f fa fb ∧ ∃ h ∈ Kh,
    (∀ h₁ : UA σ W₁.J, ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H 1 h₁ m) ∧ ∀ h₁ m, IsLevi (W₁ := W₁) H 1 h₁ m → g h₁ = fa (m * h)}

variable {a a' : ℕ}

def Diffs (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a') (c : ℂ) : Submodule ℂ (UA σ G.W.J → ℂ) :=
  Submodule.span ℂ {f | ∃ Φ, ∃ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' ∧
    f = fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h}

def zb (a i : ℕ) : ℝ := ((a : ℝ) - 2 * ((i : ℝ) + 1)) / 2

def Lev (B : Base F E) (X : Chars F E) (a a' : ℕ) {d d₁ : ℕ} {W : Spc F E d} (H : Plane E d d₁)
    (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j)) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1)))
    (S : Submodule ℂ (UA σ W.J → ℂ)) (i : ℕ) : Submodule ℂ (UA σ (sp i).J → ℂ) :=
  Nat.rec (motive := fun i => Submodule ℂ (UA σ (sp i).J → ℂ))
    (alphaSpan (sp 0) H X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (finK σ W B.emb) S)
    (fun i L => alphaSpan (sp (i + 1)) (pl i) X.α X.β ((a' : ℝ) / 2) (zb a i) (finK σ (sp i) B.emb) L) i

theorem lev_zero (B : Base F E) (X : Chars F E) (a a' : ℕ) {d d₁ : ℕ} {W : Spc F E d} (H : Plane E d d₁)
    (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j)) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1)))
    (S : Submodule ℂ (UA σ W.J → ℂ)) :
    Lev B X a a' H sp pl S 0 = alphaSpan (sp 0) H X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (finK σ W B.emb) S := rfl

theorem lev_succ (B : Base F E) (X : Chars F E) (a a' : ℕ) {d d₁ : ℕ} {W : Spc F E d} (H : Plane E d d₁)
    (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j)) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1)))
    (S : Submodule ℂ (UA σ W.J → ℂ)) (i : ℕ) :
    Lev B X a a' H sp pl S (i + 1) = alphaSpan (sp (i + 1)) (pl i) X.α X.β ((a' : ℝ) / 2) (zb a i) (finK σ (sp i) B.emb)
      (Lev B X a a' H sp pl S i) := rfl

structure InducedMaj (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) : Prop where
  cartan : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w)
  tie : ∀ w, ∃ a : Fin n₁ → ℂ, Y.θ w * (H.ι.map (B.emb w).1 + Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) a) =
    (H.ι.map (B.emb w).1 + Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) a) * Y₁.θ w

instance {B : Base F E} {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁} :
    CoeFun (InducedMaj B H Y Y₁) fun _ => ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w) :=
  ⟨fun h => h.cartan⟩

instance {B : Base F E} {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁} :
    CoeOut (InducedMaj B H Y Y₁) (∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w)) :=
  ⟨fun h => h.cartan⟩

theorem InducedMaj.of_comm {B : Base F E} {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    (h₁ : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w))
    (h₂ : ∀ w, Y.θ w * H.ι.map (B.emb w).1 = H.ι.map (B.emb w).1 * Y₁.θ w) : InducedMaj B H Y Y₁ :=
  ⟨h₁, fun w => ⟨0, by
    have e : Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) (0 : Fin n₁ → ℂ) = 0 := by ext; simp [Matrix.vecMulVec_apply]
    rw [e, add_zero]; exact h₂ w⟩⟩

variable (σ) in

def IsIsoPlane (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) : Prop :=
  n = n₁ + 2 ∧ form σ Y.J H.x H.x = 0 ∧ form σ Y.J H.y H.y = 0 ∧ form σ Y.J H.x H.y = 1 ∧
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) ∧ H.ιᵀ * Y.J * H.ι.map σ = Y₁.J ∧
    (∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) ∧ InducedMaj B H Y Y₁

theorem IsIsoPlane.of_adapted {B : Base F E} {n n₁ i₀ i₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (h : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w))
    (h₁ : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w)) : IsIsoPlane σ B H Y Y₁ :=
  ⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, h, .of_comm h₁ fun w => (hH.cartan w).1⟩

def BetaZeroOfLevi : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      (∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ fa fb fa' fb', Split2 W₁ H' X (G.M.I om Φ) fa fb →
        Split2 W₁ H' X (G.M'.I om' Φ') fa' fb' → ∀ h₁ m, IsLevi (W₁ := W₁) H' 1 h₁ m → fb m = c * fb' m) →
      BetaZero W₁ H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c)

def FlagExists : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ →
      ∃ (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j)) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))),
        sp 0 = W₁ ∧ ∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))

def BetaZeroFirst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      0 < G.p → BetaZero (sp (0 + 1)) (pl 0) X.α X.β ((a' : ℝ) / 2) (zb a 0) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) 0)

def BetaZeroNext : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      ∀ i, i + 1 < G.p → (∀ j ≤ i, BetaZero (sp (j + 1)) (pl j) X.α X.β ((a' : ℝ) / 2) (zb a j) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j)) →
        BetaZero (sp (i + 1 + 1)) (pl (i + 1)) X.α X.β ((a' : ℝ) / 2) (zb a (i + 1)) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) (i + 1))

def LevTop : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      (∀ i < G.p, BetaZero (sp (i + 1)) (pl i) X.α X.β ((a' : ℝ) / 2) (zb a i) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) i)) → (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) G.p) = ⊥

def DiffsZeroOfLev : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) 0) = ⊥ → Diffs B G X om om' R Rf c = ⊥

def LevZeroOfNext : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
      (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))), H'.IsAdapted σ B G.W (sp 0) i₀ i₁ →
      (∀ i < G.p, IsIsoPlane σ B (pl i) (sp i) (sp (i + 1))) → ∀ c : ℂ,
      BetaZero (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) (Diffs B G X om om' R Rf c) →
      (∀ j < G.p, BetaZero (sp (j + 1)) (pl j) X.α X.β ((a' : ℝ) / 2) (zb a j) (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) j)) → ∀ i < G.p, (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) (i + 1)) = ⊥ → (Lev B X a a' H' sp pl (Diffs B G X om om' R Rf c) i) = ⊥

end GlobalTheory.ThK.DescB

end
