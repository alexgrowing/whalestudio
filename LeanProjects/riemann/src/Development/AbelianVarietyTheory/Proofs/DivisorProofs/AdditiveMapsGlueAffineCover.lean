import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrob
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobLinSig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfBasis

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

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

namespace GlobalTheory.ChainPts.FrobGlue

theorem ext_span {A A' M N P : Type} [CommRing A] [CommRing A'] [AddCommGroup M] [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A' P] (τ : M →+ N) (hτ : Submodule.span A (Set.range τ) = ⊤) (r : A → A') (f g : N → P)
    (f0 : ∀ x y, f (x + y) = f x + f y) (g0 : ∀ x y, g (x + y) = g x + g y)
    (f1 : ∀ (a : A) x, f (a • x) = r a • f x) (g1 : ∀ (a : A) x, g (a • x) = r a • g x)
    (h : ∀ x, f (τ x) = g (τ x)) (y : N) : f y = g y := by
  have hy : y ∈ Submodule.span A (Set.range τ) := hτ ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨x, rfl⟩ := hy; exact h x
  | zero => rw [← map_zero τ]; exact h 0
  | add y z _ _ hy hz => rw [f0, g0, hy, hz]
  | smul a y _ hy => rw [f1, g1, hy]

section Glue

variable {X : Scheme.{0}} {Λ : Type} [CommRing Λ] (p : ℕ) [Fact p.Prime]

def IsSig (q : ℕ) (F H : Action X.Modules Λ) (τ : ∀ W : X.Opens, Γ(F.V, W) →+ Γ(H.V, W)) : Prop :=
  (∀ (a : Λ) (W : X.Opens) (s : Γ(F.V, W)), (H.ρ a : H.V ⟶ H.V).app W (τ W s) = τ W ((F.ρ a : F.V ⟶ F.V).app W s)) ∧
  (∀ (W W' : X.Opens) (hle : W' ≤ W) (s : Γ(F.V, W)), resM H.V hle (τ W s) = τ W' (resM F.V hle s)) ∧
  ∀ W : X.Opens, IsAffineOpen W → IsFrobLin Γ(X, W) p q (τ W)

theorem IsSig.comp {k k' : ℕ} {F H K : Action X.Modules Λ} {τ : ∀ W : X.Opens, Γ(F.V, W) →+ Γ(H.V, W)}
    {σ : ∀ W : X.Opens, Γ(H.V, W) →+ Γ(K.V, W)} (h : IsSig p (p ^ k) F H τ) (h' : IsSig p (p ^ k') H K σ) :
    IsSig p (p ^ (k + k')) F K fun W => (σ W).comp (τ W) := by
  refine ⟨fun a W s => ?_, fun W W' hle s => ?_, fun W hW => ?_⟩
  · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, h'.1, h.1]
  · rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, h'.2.1, h.2.1]
  · exact (GlobalTheory.RingChain.FrobLin.main _ p _ _ _).2.2.1 k k' _ _ (h.2.2 W hW) (h'.2.2 W hW)

theorem glue (F H G : Action X.Modules Λ) [H.V.IsQuasicoherent] [G.V.IsQuasicoherent] (k : ℕ)
    (τ : ∀ W : X.Opens, Γ(F.V, W) →+ Γ(H.V, W)) (hτ : IsSig p (p ^ k) F H τ) (I : Type) (V : I → X.Opens)
    (ψ : ∀ i, Γ(F.V, V i) →+ Γ(G.V, V i)) (hV : ∀ i, IsAffineOpen (V i)) (hc : ∀ x : X, ∃ i, x ∈ V i)
    (hVV : ∀ i i', IsAffineOpen (V i ⊓ V i')) (hψ : ∀ i, IsFrobLin Γ(X, V i) p (p ^ k) (ψ i))
    (hχ : ∀ i i', ∃ χ : Γ(F.V, V i ⊓ V i') →+ Γ(G.V, V i ⊓ V i'), IsFrobLin Γ(X, V i ⊓ V i') p (p ^ k) χ ∧
      (∀ s, χ (resM F.V inf_le_left s) = resM G.V inf_le_left (ψ i s)) ∧
        ∀ s, χ (resM F.V inf_le_right s) = resM G.V inf_le_right (ψ i' s))
    (hρ : ∀ (i : I) (a : Λ) (s : Γ(F.V, V i)),
      ψ i ((F.ρ a : F.V ⟶ F.V).app _ s) = (G.ρ a : G.V ⟶ G.V).app _ (ψ i s)) : Nonempty (H ≅ G) := by
  have hc' : iSup V = ⊤ := eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (hc x)
  have hsp : ∀ i, Submodule.span Γ(X, V i) (Set.range (τ (V i))) = ⊤ := fun i =>
    ((GlobalTheory.RingChain.FrobLin.main _ p _ _ Γ(G.V, V i)).1 k _ (hτ.2.2 _ (hV i))).1
  have he : ∀ i, ∃ e : Γ(H.V, V i) ≃ₗ[Γ(X, V i)] Γ(G.V, V i), ∀ x, e (τ (V i) x) = ψ i x := fun i =>
    (GlobalTheory.RingChain.FrobLin.main _ p _ _ _).2.1 k _ _ (hτ.2.2 _ (hV i)) (hψ i)
  choose e he using he
  have key : ∀ (i : I) (W : X.Opens) (hW : W ≤ V i) (e' : Γ(H.V, W) →ₗ[Γ(X, W)] Γ(G.V, W)) (χ : Γ(F.V, W) →+ Γ(G.V, W)),
      (∀ x, e' (τ W x) = χ x) → (∀ s, χ (resM F.V hW s) = resM G.V hW (ψ i s)) →
        ∀ s, e' (resM H.V hW s) = resM G.V hW (e i s) := by
    intro i W hW e' χ h₁ h₂
    refine ext_span (τ (V i)) (hsp i) (fun a => X.presheaf.map (homOfLE hW).op a) _ _ (fun x y => ?_) (fun x y => ?_)
      (fun a x => ?_) (fun a x => ?_) fun x => ?_
    · rw [map_add, map_add]
    · rw [map_add, map_add]
    · rw [GlobalTheory.Twist.resM_smul, map_smul]
    · rw [map_smul, GlobalTheory.Twist.resM_smul]
    · rw [hτ.2.1, h₁, h₂, he]
  obtain ⟨u, hu⟩ := (GlobalTheory.CoverHom.hom_on_affineCover X H.V G.V I V hV hc').1 hVV (fun i => (e i).toLinearMap)
    fun i i' => by
      obtain ⟨χ, h₀, h₁, h₂⟩ := hχ i i'
      obtain ⟨e', he'⟩ := (GlobalTheory.RingChain.FrobLin.main _ p _ _ _).2.1 k _ _ (hτ.2.2 _ (hVV i i')) h₀
      exact ⟨e'.toLinearMap, key i _ _ _ χ he' h₁, key i' _ _ _ χ he' h₂⟩
  haveI : IsIso u := (GlobalTheory.CoverHom.hom_on_affineCover X H.V G.V I V hV hc').2.2.2.2.1 u fun i => by
    have : (u.app (V i) : Γ(H.V, V i) → Γ(G.V, V i)) = e i := funext (hu i)
    rw [this]
    exact (e i).bijective
  refine ⟨Action.mkIso (asIso u) fun a => ?_⟩
  change (H.ρ a : H.V ⟶ H.V) ≫ u = u ≫ (G.ρ a : G.V ⟶ G.V)
  refine (GlobalTheory.CoverHom.hom_on_affineCover X H.V G.V I V hV hc').2.1 _ _ fun i s => ?_
  change appLinear ((H.ρ a : H.V ⟶ H.V) ≫ u) (V i) s = appLinear (u ≫ (G.ρ a : G.V ⟶ G.V)) (V i) s
  refine LinearMap.congr_fun (LinearMap.ext_on_range (hsp i) fun x => ?_) s
  change u.app (V i) ((H.ρ a : H.V ⟶ H.V).app (V i) (τ (V i) x)) = (G.ρ a : G.V ⟶ G.V).app (V i) (u.app (V i) (τ (V i) x))
  rw [hτ.1, hu, hu]
  exact (he i _).trans ((hρ i a x).trans (congrArg _ (he i x).symm))

end Glue

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] {B : GlobalTheory.Vert.Model O}
  {Λ : Type} [CommRing Λ] (hp : (p : Γ((fibI p B).subscheme, ⊤)) = 0)

theorem exists_one (F : AM B Λ) (hF : F.V.IsQuasicoherent) :
    (frobA p hp F).V.IsQuasicoherent ∧ ∃ τ, IsSig p (p ^ 1) F (frobA p hp F) τ := by
  obtain ⟨σ, h₁, h₂, h₃⟩ := FrobSec.main O p B hp
  refine ⟨(h₃ F.V).1, σ F.V, fun a W s => h₁ _ _ _ W s, h₂ F.V, fun W hW => ?_⟩
  rw [pow_one]
  exact (h₃ F.V).2 W hW

theorem exists_iter (F : AM B Λ) (hF : F.V.IsQuasicoherent) (k : ℕ) :
    ((frobA p hp)^[k + 1] F).V.IsQuasicoherent ∧ ∃ τ, IsSig p (p ^ (k + 1)) F ((frobA p hp)^[k + 1] F) τ := by
  induction k with
  | zero => exact exists_one p hp F hF
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h₁, τ, hτ⟩ := ih
    obtain ⟨h₂, σ, hσ⟩ := exists_one p hp _ h₁
    exact ⟨h₂, _, hτ.comp p hσ⟩

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (hp : (p : Γ((fibI p B).subscheme, ⊤)) = 0) (F G : AM B Λ) [F.V.IsQuasicoherent] [G.V.IsQuasicoherent] (I : Type) (V : I → B.X.Opens) (k : ℕ) (ψ : ∀ i, Γ(F.V, V i) →+ Γ(G.V, V i)), (∀ i, IsAffineOpen (V i)) → (∀ x : B.X, ∃ i, x ∈ V i) → (∀ i i', IsAffineOpen (V i ⊓ V i')) → (∀ i, IsFrobLin Γ(B.X, V i) p (p ^ (k + 1)) (ψ i)) → (∀ i i', ∃ χ : Γ(F.V, V i ⊓ V i') →+ Γ(G.V, V i ⊓ V i'), IsFrobLin Γ(B.X, V i ⊓ V i') p (p ^ (k + 1)) χ ∧ (∀ s, χ (resM F.V inf_le_left s) = resM G.V inf_le_left (ψ i s)) ∧ ∀ s, χ (resM F.V inf_le_right s) = resM G.V inf_le_right (ψ i' s)) → (∀ (i : I) (a : Λ) (s : Γ(F.V, V i)), ψ i ((F.ρ a : F.V ⟶ F.V).app _ s) = (G.ρ a : G.V ⟶ G.V).app _ (ψ i s)) → Nonempty ((frobA p hp)^[k + 1] F ≅ G) := by
  intro O _ _ _ p _ B Λ _ hp F G hF _ I V k ψ hV hc hVV hψ hχ hρ
  obtain ⟨h₁, τ, hτ⟩ := exists_iter p hp F hF k
  exact glue p F _ G (k + 1) τ hτ I V ψ hV hc hVV hψ hχ hρ

end GlobalTheory.ChainPts.FrobGlue

end
