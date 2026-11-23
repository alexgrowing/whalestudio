import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnivBasisMove

open GlobalTheory.ThetaReal GlobalTheory.ThetaPtMove GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)} {a : ℤ}

def Rel (w : LB.Iso L₁ (L₀.pull φ)) (s : SecM A L₁ a T) (s₀ : SecM G L₀ a T₀) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
    ThetaAct.sv s₀ (r ≫ psi hp τ hτ) z J =
      (wVal w z J J' (r ≫ (snd T A).left) ^ a).val * ThetaAct.sv s r z J'

theorem exists_rel (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (s₀ : SecM G L₀ a T₀) :
    ∃ s, Rel hp τ hτ w s s₀ := by
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ (SecM.toSec G s₀)
  exact ⟨SecM.ofSec A s, hs⟩

theorem exists_rel_up [IsIso τ] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (s : SecM A L₁ a T) :
    ∃ s₀, Rel hp τ hτ w s s₀ := by
  obtain ⟨s₀, hs⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ (SecM.toSec A s)
  exact ⟨SecM.ofSec G s₀, hs⟩

variable {hp τ hτ}

theorem Rel.unique_down (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {s s' : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w s' s₀) : s = s' :=
  ThetaAct.sv_ext hL₁ fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    exact (Units.mul_right_inj _).1 ((h _ _ _ _ _ hJ hJ').symm.trans (h' _ _ _ _ _ hJ hJ'))

theorem Rel.unique_up [IsIso τ] (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {s : SecM A L₁ a T} {s₀ s₀' : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w s s₀') : s₀ = s₀' :=
  ThetaAct.sv_ext hL₀ fun y J hJ => by
    obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    obtain ⟨χ, -, h₂⟩ := WeilPull.exists_psi_inv hp τ hτ
    have h₂' : χ ≫ psi hp τ hτ = 𝟙 _ := h₂
    have q := (h _ χ y _ _ hJ hJ').trans (h' _ χ y _ _ hJ hJ').symm
    rwa [h₂'] at q

theorem Rel.add {s t : SecM A L₁ a T} {s₀ t₀ : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w t t₀) : Rel hp τ hτ w (s + t) (s₀ + t₀) :=
  fun Z r z J J' hJ hJ' => by
    rw [ThetaAct.sv_add _ _ _ _ hJ, ThetaAct.sv_add _ _ _ _ hJ', h _ _ _ _ _ hJ hJ', h' _ _ _ _ _ hJ hJ', mul_add]

theorem Rel.smul {s : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀} (c : Γ(T₀.left, ⊤))
    (h : Rel hp τ hτ w s s₀) : Rel hp τ hτ w (τ.appTop.hom c • s) (c • s₀) :=
  fun Z r z J J' hJ hJ' => by
    rw [ThetaAct.sv_smul _ _ _ _ hJ, ThetaAct.sv_smul _ _ _ _ hJ', h _ _ _ _ _ hJ hJ', mul_left_comm,
      Category.assoc, psi_fst', ← Category.assoc]
    exact congrArg (fun x => _ * (x * _)) (gs_pull _ τ z ⊤ trivial c).symm

theorem Rel.pull {s : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀} (h : Rel hp τ hτ w s s₀)
    {T' : Over S'} {T₀' : Over S} (σ : T'.left ⟶ T₀'.left) (hσ : σ ≫ T₀'.hom = T'.hom ≫ f)
    (u : T' ⟶ T) (u₀ : T₀' ⟶ T₀) (hu : σ ≫ u₀.left = u.left ≫ τ) :
    Rel hp σ hσ w (VVRank.pullM A L₁ a u s) (VVRank.pullM G L₀ a u₀ s₀) :=
  fun Z r z J J' hJ hJ' => by
    have e : psi hp σ hσ ≫ (u₀ ▷ G).left = (u ▷ A).left ≫ psi hp τ hτ := by
      refine psi_ext ?_ ?_
      · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst',
          Category.assoc, Category.assoc, psi_fst', hu, ← Category.assoc (u ▷ A).left, ← Over.comp_left,
          whiskerRight_fst, Over.comp_left, Category.assoc]
      · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', Category.assoc, psi_snd', ← Category.assoc,
          VVRank.whisker_snd_left]
    have q := h _ (r ≫ (u ▷ A).left) z _ _ hJ hJ'
    rw [Category.assoc, Category.assoc, ← e, VVRank.whisker_snd_left, ← Category.assoc] at q
    exact (VVRank.sv_pullS G a u₀ (SecM.toSec G s₀) _ z hJ).trans
      (q.trans (congrArg _ (VVRank.sv_pullS A a u (SecM.toSec A s) _ z hJ').symm))

theorem exists_linearEquiv (hp : IsGrpPullback A G f φ) (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB)
    (a : ℤ) (T : Over S') :
    ∃ E : SecM G L₀ a (Over.mk (T.hom ≫ f)) ≃ₗ[Γ(T.left, ⊤)] SecM A L₁ a T,
      ∀ x, Rel hp (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _) w (E x) x := by
  have : IsIso (C := Scheme.{0}) (X := T.left) (Y := (Over.mk (T.hom ≫ f)).left) (𝟙 T.left) := IsIso.id _
  choose D hD using exists_rel hp (T := T) (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _) (a := a)
    hw hL₀ hL₁
  let l : SecM G L₀ a (Over.mk (T.hom ≫ f)) →ₗ[Γ(T.left, ⊤)] SecM A L₁ a T :=
    { toFun := D
      map_add' := fun x y => (hD _).unique_down hL₀ hL₁ ((hD x).add (hD y))
      map_smul' := fun c x => (hD _).unique_down hL₀ hL₁ (Rel.smul (T₀ := Over.mk (T.hom ≫ f)) (τ := 𝟙 T.left) c (hD x)) }
  refine ⟨LinearEquiv.ofBijective l ⟨fun x y e => ?_, fun s => ?_⟩, hD⟩
  · have e' : D x = D y := e
    exact (hD x).unique_up hL₀ hL₁ (e' ▸ hD y)
  · obtain ⟨s₀, hs⟩ := exists_rel_up hp (T := T) (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _)
      hw hL₀ hL₁ s
    exact ⟨s₀, (hD s₀).unique_down hL₀ hL₁ hs⟩

theorem univBasis_move : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∀ (n : ℤ) (κ : Type) [Fintype κ] (T₀ : Over S) (τ : S' ⟶ T₀.left), τ ≫ T₀.hom = f → ∀ b₀ : κ → SecM P.A P.L n T₀, UnivBasis P n b₀ → ∃ b : κ → SecM P'.A P'.L n (baseOver S'), UnivBasis P' n b := by
  intro S S' f P P' φ hp hw n κ _ T₀ τ hτ b₀ hb₀
  obtain ⟨w, hw⟩ := hw
  have hτ' : τ ≫ T₀.hom = (baseOver S').hom ≫ f := hτ.trans (Category.id_comp _).symm
  choose b hb using fun i => exists_rel hp (T := baseOver S') τ hτ' hw P.isLB P'.isLB (b₀ i)
  refine ⟨b, fun T hT h => ?_⟩
  have hh : h.left = T.hom := (Category.comp_id _).symm.trans (Over.w h)
  let h₀ : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk (T.hom ≫ τ) (by
    change (T.hom ≫ τ) ≫ T₀.hom = T.hom ≫ f
    rw [Category.assoc, hτ])
  have : IsAffine (Over.mk (T.hom ≫ f)).left := hT
  obtain ⟨c, hc⟩ := hb₀ _ h₀
  obtain ⟨E, hE⟩ := exists_linearEquiv hp hw P.isLB P'.isLB n T
  refine ⟨Module.Basis.map (R := Γ(T.left, ⊤)) c E, fun i => ?_⟩
  refine (hE (c i)).unique_down P.isLB P'.isLB ?_
  rw [hc]
  exact (hb i).pull _ _ h h₀ ((Category.id_comp _).trans (congrArg (· ≫ τ) hh.symm))

end GlobalTheory.UnivBasisMove
