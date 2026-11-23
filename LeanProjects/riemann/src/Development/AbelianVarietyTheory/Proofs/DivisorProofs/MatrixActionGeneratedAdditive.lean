import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

namespace GlobalTheory.ChainDesc.MapAdd

variable {p h o : ℕ} {A : Type} [CommRing A] {π : A} {γ : ℕ → A} {Lie Om : Type} [AddCommGroup Lie] [Module A Lie]
  [AddCommGroup Om] [Module A Om]

theorem mv_add_matrix (N N' : Matrix (Fin h) (Fin h) ℤ) (x : Fin h → A) :
    mv (RingHom.id A) (N + N') x = mv (RingHom.id A) N x + mv (RingHom.id A) N' x := by
  unfold mv
  rw [Matrix.map_add _ Int.cast_add, Matrix.add_mulVec]

theorem mv_zero_matrix (x : Fin h → A) : mv (RingHom.id A) (0 : Matrix (Fin h) (Fin h) ℤ) x = 0 := by
  unfold mv
  rw [Matrix.map_zero _ Int.cast_zero, Matrix.zero_mulVec]

theorem mv_neg_matrix (N : Matrix (Fin h) (Fin h) ℤ) (x : Fin h → A) :
    mv (RingHom.id A) (-N) x = -mv (RingHom.id A) N x := by
  rw [eq_neg_iff_add_eq_zero, ← mv_add_matrix, neg_add_cancel, mv_zero_matrix]

variable (D : RChain p A h o π γ Lie Om)

theorem map_zero' : D.Map D (RingHom.id A) 0 (fun _ => 0) (fun _ => 0) where
  mem n x _ := by rw [mv_zero_matrix]; exact zero_mem _
  j y x x' e _ := by
    rw [mv_zero_matrix] at e
    obtain rfl : x' = 0 := Subtype.ext e
    simp
  ρ y x x' e _ := by
    rw [mv_zero_matrix] at e
    obtain rfl : x' = 0 := Subtype.ext e
    simp
  ψ n _ x x' y y' e e' _ := by
    rw [mv_zero_matrix] at e e'
    obtain rfl : x' = 0 := Subtype.ext e
    obtain rfl : y' = 0 := Subtype.ext e'
    simp
  κ n _ x x' y e _ := by
    rw [mv_zero_matrix] at e
    obtain rfl : x' = 0 := Subtype.ext e
    simp

variable {D}

theorem map_sub' {N N' : Matrix (Fin h) (Fin h) ℤ} {l l' : Lie → Lie} {m m' : Om → Om}
    (H : D.Map D (RingHom.id A) N l m) (H' : D.Map D (RingHom.id A) N' l' m') :
    D.Map D (RingHom.id A) (N - N') (fun y => l y - l' y) (fun w => m w - m' w) := by
  have hs : ∀ x : Fin h → A, mv (RingHom.id A) (N - N') x = mv (RingHom.id A) N x - mv (RingHom.id A) N' x := fun x => by
    rw [sub_eq_add_neg, mv_add_matrix, mv_neg_matrix, sub_eq_add_neg]
  have sp : ∀ n (x x' : D.L n), x'.1 = mv (RingHom.id A) (N - N') x.1 →
      x' = ⟨_, H.mem n _ x.2⟩ - ⟨_, H'.mem n _ x.2⟩ := fun n x x' e => Subtype.ext (e.trans (hs _))
  refine ⟨fun n x hx => ?_, fun y x x' e k => ?_, fun y x x' e k => ?_, fun n hn x x' y y' e e' k => ?_,
    fun n hn x x' y e k => ?_⟩
  · rw [hs]; exact sub_mem (H.mem n x hx) (H'.mem n x hx)
  · rw [sp _ _ _ e, map_sub, Submodule.Quotient.mk_sub, H.j y x ⟨_, H.mem _ _ x.2⟩ rfl k,
      H'.j y x ⟨_, H'.mem _ _ x.2⟩ rfl k]
  · rw [sp _ _ _ e, map_sub, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, H.ρ y x ⟨_, H.mem _ _ x.2⟩ rfl k,
      H'.ρ y x ⟨_, H'.mem _ _ x.2⟩ rfl k]
  · rw [sp _ _ _ e, sp _ _ _ e', Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, map_sub,
      H.ψ n hn x ⟨_, H.mem _ _ x.2⟩ y ⟨_, H.mem _ _ y.2⟩ rfl rfl k,
      H'.ψ n hn x ⟨_, H'.mem _ _ x.2⟩ y ⟨_, H'.mem _ _ y.2⟩ rfl rfl k]
  · rw [sp _ _ _ e, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, map_sub,
      H.κ n hn x ⟨_, H.mem _ _ x.2⟩ y rfl k, H'.κ n hn x ⟨_, H'.mem _ _ x.2⟩ y rfl k]

theorem map_of_span : ∀ (p h o : ℕ) (A Λ : Type) [CommRing A] [CommRing Λ] (π : A) (γ : ℕ → A) (Lie Om : Type) [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] (D : RChain p A h o π γ Lie Om) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (α : Λ → Lie → Lie) (β : Λ → Om → Om) (G : Set Λ), (∀ a b y, α (a + b) y = α a y + α b y) → (∀ a b y, β (a + b) y = β a y + β b y) → Submodule.span ℤ G = ⊤ → (∀ a ∈ G, D.Map D (RingHom.id A) (M a) (α a) (β a)) → ∀ a, D.Map D (RingHom.id A) (M a) (α a) (β a) := by
  intro p h o A Λ _ _ π γ Lie Om _ _ _ _ D M α β G hα hβ hG hg
  have a0 : ∀ y, α 0 y = 0 := fun y => by simpa using hα 0 0 y
  have b0 : ∀ y, β 0 y = 0 := fun y => by simpa using hβ 0 0 y
  have as : ∀ a b, α (a - b) = fun y => α a y - α b y := fun a b => funext fun y => by
    rw [eq_sub_iff_add_eq, ← hα, sub_add_cancel]
  have bs : ∀ a b, β (a - b) = fun y => β a y - β b y := fun a b => funext fun y => by
    rw [eq_sub_iff_add_eq, ← hβ, sub_add_cancel]
  have z : D.Map D (RingHom.id A) (M 0) (α 0) (β 0) := by
    rw [map_zero, funext a0, funext b0]; exact map_zero' D
  have s : ∀ a b, D.Map D (RingHom.id A) (M a) (α a) (β a) → D.Map D (RingHom.id A) (M b) (α b) (β b) →
      D.Map D (RingHom.id A) (M (a - b)) (α (a - b)) (β (a - b)) := fun a b ha hb => by
    rw [map_sub, as, bs]; exact map_sub' ha hb
  let S : AddSubgroup Λ :=
    { carrier := {a | D.Map D (RingHom.id A) (M a) (α a) (β a)}
      zero_mem' := z
      neg_mem' := fun {a} ha => by
        have := s 0 a z ha
        rwa [zero_sub] at this
      add_mem' := fun {a b} ha hb => by
        have := s a (0 - b) ha (s 0 b z hb)
        rwa [zero_sub, sub_neg_eq_add] at this }
  have hle : Submodule.span ℤ G ≤ AddSubgroup.toIntSubmodule S := Submodule.span_le.2 hg
  intro a
  exact hle (hG ▸ Submodule.mem_top : a ∈ Submodule.span ℤ G)

end GlobalTheory.ChainDesc.MapAdd
