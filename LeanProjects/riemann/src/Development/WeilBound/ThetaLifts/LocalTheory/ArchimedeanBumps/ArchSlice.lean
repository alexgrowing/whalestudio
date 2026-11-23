import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ArchCone

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

structure IsLift (σ : E →ₐ[F] E) (B : Base F E) (lift : (InfinitePlace F → ℂ) → AE F E) : Prop where
  supp : ∀ c, At (evI F) (lift c)
  pi : ∀ c w, piInf (B.emb w) (lift c) = c w
  inv : ∀ a : AE F E, At (evI F) a → lift (fun w => piInf (B.emb w) a) = a
  part : ∀ a : AE F E, At (evI F) (realAd F 1 • a) ∧ ∀ w, piInf (B.emb w) (realAd F 1 • a) = piInf (B.emb w) a
  conj : ∀ (a : AE F E) w, piInf (B.emb w) (cA σ a) = starRingEnd ℂ (piInf (B.emb w) a)
  incl : ∀ (x : E) w, piInf (B.emb w) (inclR (F := F) (AF F) x) = (B.emb w).1 x
  cont : ∀ w, Continuous (piInf (F := F) (E := E) (B.emb w))
  psi : ∀ a : AE F E, At (evI F) a → B.ψ (Algebra.trace (AF F) (AE F E) a) =
    Complex.exp (-(2 * Real.pi * Complex.I) * ((∑ w, 2 * (piInf (B.emb w) a).re : ℝ) : ℂ))
  abs : ∀ l : (AE F E)ˣ, At (evI F) ((l : AE F E) - 1) → (absE F E l : ℝ) = ∏ w, ‖piInf (B.emb w) (l : AE F E)‖ ^ 2
  idAt : ∀ l : (AE F E)ˣ, l ∈ idAt E (evI F) ↔ At (evI F) ((l : AE F E) - 1)
  unit : ∀ c : InfinitePlace F → ℂ, (∀ w, c w ≠ 0) → ∃ l : (AE F E)ˣ, At (evI F) ((l : AE F E) - 1) ∧
    ∀ w, piInf (B.emb w) (l : AE F E) = c w
  haar : ∀ x : @Measure (Loc.idAt E (evI F)) (borel _), @Measure.IsHaarMeasure _ _ _ (borel _) x → ∃ κ : ℝ, 0 < κ ∧
    ∀ g : (InfinitePlace F → ℂ) → ℂ, @integral _ _ _ _ (borel _) x (fun l => g fun w => piInf (B.emb w) (l.1 : AE F E)) =
      κ * ∫ c, g c * ((∏ w, ‖c w‖ ^ 2 : ℝ) : ℂ)⁻¹

def ArchDict : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∃ lift, IsLift σ B lift

def ArchHeis : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), B.IsGood σ →
    (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ u Φ ∈ schA F (Fin n × Fin d)) ∧
    ∀ u, At (evI F) u → ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (M.co.rho B.ψ u) f f₁

def EiDense : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) e u ei ev, Cfg B M M₁ H H' e u → IsEvLoc M M₁ e ei ev →
    ∀ l : SInf F (Fin n₁ × Fin d₁) →L[ℂ] ℂ, l ≠ 0 → ∃ f, l (ei f) ≠ 0

def ArchSlice : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) e u ei ev, Cfg B M M₁ H H' e u → IsEvLoc M M₁ e ei ev →
    ∀ lift, IsLift σ B lift → ∀ (K : Subgroup (UA σ X.J)) (m : LocMeas K), IsStab B K → m.Is →
    ∀ χX χW om r s r' s', IsPair B M χX χW om r s r' s' →
    IsCompact (kAt K (evI F) : Set (UA σ X.J)) ∧ (∀ k ∈ kAt K (evI F), k ∈ KInf σ X B.emb) ∧
    ∀ (f : SInf F (Fin n × Fin d)) (l : SInf F (Fin n₁ × Fin d₁) →L[ℂ] ℂ),
      (Continuous fun x : kAt K (evI F) × (InfinitePlace F → ℂ) =>
        l (ei (opI (fun Φ => M.co.rho B.ψ (lift x.2 • u 1) (om (x.1.1, 1) Φ)) f))) ∧
      (∀ N : ℕ, ∃ C : ℝ, ∀ (k : kAt K (evI F)) (c : InfinitePlace F → ℂ),
        ‖l (ei (opI (fun Φ => M.co.rho B.ψ (lift c • u 1) (om (k.1, 1) Φ)) f))‖ * (1 + ‖c‖) ^ N ≤ C) ∧
      ∀ (ν : Chr F E) (z : ℕ), Continuous ν → 1 ≤ z → ∀ L, IsConeI B M om m ei u ν z L →
        l (L f) = ∫ k, @integral _ _ _ _ (borel _) m.xi (fun t =>
          l (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • u t.1) (om (k.1, 1) Φ)) f)) * (ν t.1 : ℂ) * ((absE F E t.1 : ℝ) : ℂ) ^ z) ∂m.ki

end PositivityTheory.ThKG.Loc.Bump

end
