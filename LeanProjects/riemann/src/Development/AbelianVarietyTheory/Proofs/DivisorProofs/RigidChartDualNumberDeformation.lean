import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfRefinementStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitExtendOfGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSUniq

variable {K : Type} [Field K]

theorem theta_eq_fibre (P₀ : Out.PolAV (Sp K)) {n : ℕ} (u : Fin n → (epsR K ⟶ P₀.A)) (hu : IsLieBasis u)
    (dd : Fin n → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)) (hdd : ∀ a, IsInvDer (u a) (dd a))
    {X Z : Scheme.{0}} (π : Z ⟶ X) (x0 : Sp K ⟶ X) (m : P₀.A.left ⟶ Z) (hm : IsPullback m P₀.A.hom π x0)
    {U : X.Opens} (hU : IsAffineOpen U) (L : LB Z) (hL : L.IsLB) (hiso : LBIso P₀.L (L.pull m))
    (D : Γ(X, U) → Γ(X, U)) (θ θ' : Matrix (Fin n) (Fin n) K)
    {J J' : Type} (W : J → Z.Opens) (W' : J' → Z.Opens) (j : J → L.ι) (j' : J' → L.ι)
    (d : J → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) (d' : J' → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O))
    (hWU : ∀ i, W i ≤ π ⁻¹ᵁ U) (hWU' : ∀ k, W' k ≤ π ⁻¹ᵁ U)
    (hWj : ∀ i, W i ≤ L.U (j i)) (hWj' : ∀ k, W' k ≤ L.U (j' k))
    (hcov : ∀ z : P₀.A.left, ∃ i, m z ∈ W i) (hcov' : ∀ z : P₀.A.left, ∃ k, m z ∈ W' k)
    (hf : ∀ i, GlobalTheory.LogKS.IsField (W i) (d i)) (hf' : ∀ k, GlobalTheory.LogKS.IsField (W' k) (d' k))
    (hl : ∀ i (h : W i ≤ π ⁻¹ᵁ U) (r : Γ(X, U)),
      d i (W i) ((π.appLE U (W i) h).hom r) = (π.appLE U (W i) h).hom (D r))
    (hl' : ∀ k (h : W' k ≤ π ⁻¹ᵁ U) (r : Γ(X, U)),
      d' k (W' k) ((π.appLE U (W' k) h).hom r) = (π.appLE U (W' k) h).hom (D r))
    (φ : Fin n → C1 (fun i => m ⁻¹ᵁ L.U i)) (hφ : IsDlog m L dd φ)
    (hP : ∀ i i' (O : Z.Opens), O ≤ W i ⊓ W i' → ∀ f, (m.app O).hom (d i O f - d i' O f) =
      ∑ a, (∑ b, constFn P₀.A.hom _ (θ a b) * rsT (φ b (j i) (j i')) (m ⁻¹ᵁ O)) * dd a _ ((m.app O).hom f))
    (hP' : ∀ k k' (O : Z.Opens), O ≤ W' k ⊓ W' k' → ∀ f, (m.app O).hom (d' k O f - d' k' O f) =
      ∑ a, (∑ b, constFn P₀.A.hom _ (θ' a b) * rsT (φ b (j' k) (j' k')) (m ⁻¹ᵁ O)) * dd a _ ((m.app O).hom f)) :
    θ = θ' := by
  have hs : Smooth P₀.A.hom := P₀.isAb.smooth
  obtain ⟨-, hind⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hu hdd Z m L hL hiso
  obtain ⟨hcoc, hcob⟩ := hind φ hφ
  let Wp : J × J' → Z.Opens := fun p => W p.1 ⊓ W' p.2
  have hWpU : ∀ p, Wp p ≤ π ⁻¹ᵁ U := fun p => inf_le_left.trans (hWU p.1)
  have bse := fun i => field_base π (W i) (hWU i) (d i) (hf i) D (hl i)
  have bse' := fun k => field_base π (W' k) (hWU' k) (d' k) (hf' k) D (hl' k)
  have ex : ∀ p : J × J', ∃ h : Fin n → Γ(P₀.A.left, m ⁻¹ᵁ Wp p), ∀ W₁, W₁ ≤ Wp p → ∀ f,
      (m.app W₁).hom (d p.1 W₁ f - d' p.2 W₁ f) = ∑ a, rsT (h a) _ * dd a (m ⁻¹ᵁ W₁) ((m.app W₁).hom f) := by
    intro p
    refine (coeff_id hs hu hdd x0 π m hm hU (Wp p) (hWpU p)
      (fun W₁ f => (m.app W₁).hom (d p.1 W₁ f - d' p.2 W₁ f))
      (fun W₁ h f f' => ?_) (fun W₁ h f f' => ?_) (fun W₁ W₂ h h₀ f => ?_) (fun W₁ h r => ?_)).exists
    · rw [(hf p.1).1 W₁ (h.trans inf_le_left), (hf' p.2).1 W₁ (h.trans inf_le_right)]
      simp only [map_sub, map_add]; ring
    · rw [(hf p.1).2.1 W₁ (h.trans inf_le_left), (hf' p.2).2.1 W₁ (h.trans inf_le_right)]
      simp only [map_sub, map_add, map_mul]; ring
    · rw [(hf p.1).2.2 W₁ W₂ h (h₀.trans inf_le_left), (hf' p.2).2.2 W₁ W₂ h (h₀.trans inf_le_right), ← map_sub,
        app_resG]
    · rw [bse p.1 W₁ (h.trans inf_le_left), bse' p.2 W₁ (h.trans inf_le_right), sub_self, map_zero]
  choose h hh using ex
  have cmp : ∀ (p p' : J × J') (a : Fin n),
      rsT (h p a) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') - rsT (h p' a) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') =
      ∑ b, (constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ a b) *
          rsT (φ b (j p.1) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') -
        constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ' a b) *
          rsT (φ b (j' p.2) (j' p'.2)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) := by
    intro p p'
    let W₁ := Wp p ⊓ Wp p'
    have l1 : W₁ ≤ Wp p := inf_le_left
    have l2 : W₁ ≤ Wp p' := inf_le_right
    have k2 : m ⁻¹ᵁ W₁ ≤ m ⁻¹ᵁ Wp p := m.preimage_mono l1
    have k3 : m ⁻¹ᵁ W₁ ≤ m ⁻¹ᵁ Wp p' := m.preimage_mono l2
    have k4 : m ⁻¹ᵁ W₁ ≤ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨hWj p.1 (hz.1.1), hWj p'.1 (hz.2.1)⟩
    have k5 : m ⁻¹ᵁ W₁ ≤ m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) :=
      fun z hz => ⟨hWj' p.2 (hz.1.2), hWj' p'.2 (hz.2.2)⟩
    let y₁ : Fin n → Γ(P₀.A.left, m ⁻¹ᵁ W₁) := fun a =>
      rsT (h p a) _ - rsT (h p' a) _ - ∑ b, (constFn P₀.A.hom _ (θ a b) * rsT (φ b (j p.1) (j p'.1)) _ -
        constFn P₀.A.hom _ (θ' a b) * rsT (φ b (j' p.2) (j' p'.2)) _)
    have z := (coeff_id hs hu hdd x0 π m hm hU W₁ (l1.trans (hWpU p)) (fun _ _ => 0) (fun _ _ _ _ => by simp)
      (fun _ _ _ _ => by simp) (fun _ _ _ _ _ => by simp [rsT_zero]) (fun _ _ _ => rfl)).unique
      (y₁ := y₁) (y₂ := fun _ => 0) (fun W₂ hW₂ f => ?_) (fun W₂ hW₂ f => by simp [rsT_zero])
    · intro a
      have := congrFun z a
      simp only [y₁] at this
      rw [sub_eq_zero] at this
      exact this
    · have k1 : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ W₁ := m.preimage_mono hW₂
      have E1 := hh p W₂ (hW₂.trans l1) f
      have E2 := hh p' W₂ (hW₂.trans l2) f
      have E3 := hP p.1 p'.1 W₂ (fun z hz => ⟨(l1 (hW₂ hz)).1, (l2 (hW₂ hz)).1⟩) f
      have E4 := hP' p.2 p'.2 W₂ (fun z hz => ⟨(l1 (hW₂ hz)).2, (l2 (hW₂ hz)).2⟩) f
      have k1' : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ Wp p := k1.trans k2
      have k1'' : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ Wp p' := k1.trans k3
      have k4' : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) := k1.trans k4
      have k5' : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) := k1.trans k5
      simp (disch := assumption) only [y₁, rsT_sub, rsT_sum, rsT_mul, rsT_rsT, rsT_constFn, sub_mul,
        Finset.sum_sub_distrib, Finset.sum_mul] at E1 E2 E3 E4 ⊢
      simp only [map_sub] at E1 E2 E3 E4
      linear_combination E1 - E2 - E3 + E4
  funext a
  refine sub_eq_zero.1 (hcob (θ a - θ' a) ?_)
  refine GlobalTheory.T.isCechOneCoboundary_of_refinement (fun i => m ⁻¹ᵁ L.U i) (lc P₀.A.hom (θ a - θ' a) φ) (isCoc_lc _ _ _ hcoc)
    (fun p => m ⁻¹ᵁ Wp p) (fun p => j p.1) (fun p => m.preimage_mono (inf_le_left.trans (hWj p.1))) ?_
    (fun p => -(h p a) - ∑ b, constFn P₀.A.hom _ (θ' a b) * rsT (φ b (j' p.2) (j p.1)) (m ⁻¹ᵁ Wp p)) ?_
  · refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨i, hi⟩ := hcov z
    obtain ⟨k, hk⟩ := hcov' z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, k), hi, hk⟩
  · intro p p'
    have k2 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ Wp p := inf_le_left
    have k3 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ Wp p' := inf_le_right
    have k4 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨hWj p.1 hz.1.1, hWj p'.1 hz.2.1⟩
    have k6 : m ⁻¹ᵁ Wp p ≤ m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) :=
      fun z hz => ⟨hWj' p.2 hz.2, hWj p.1 hz.1⟩
    have k7 : m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨hWj' p'.2 hz.2, hWj p'.1 hz.1⟩
    have T1 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤
        m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨⟨hWj' p.2 hz.1.2, hWj' p'.2 hz.2.2⟩, hWj p'.1 hz.2.1⟩
    have T2 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤
        m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨⟨hWj' p.2 hz.1.2, hWj p.1 hz.1.1⟩, hWj p'.1 hz.2.1⟩
    have C1 : ∀ b, rsT (φ b (j' p.2) (j' p'.2)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') +
        rsT (φ b (j' p'.2) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') =
        rsT (φ b (j' p.2) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') := fun b => by
      have := congrArg (fun s => rsT s (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) (hcoc b (j' p.2) (j' p'.2) (j p'.1))
      have a1 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) := inf_le_left
      have a2 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) := fun _ h => ⟨h.1.2, h.2⟩
      have a3 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) := fun _ h => ⟨h.1.1, h.2⟩
      simpa (disch := assumption) only [rsT_add, rsT_rsT] using this
    have C2 : ∀ b, rsT (φ b (j' p.2) (j p.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') +
        rsT (φ b (j p.1) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') =
        rsT (φ b (j' p.2) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') := fun b => by
      have := congrArg (fun s => rsT s (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) (hcoc b (j' p.2) (j p.1) (j p'.1))
      have a1 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) := inf_le_left
      have a2 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) := fun _ h => ⟨h.1.2, h.2⟩
      have a3 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) := fun _ h => ⟨h.1.1, h.2⟩
      simpa (disch := assumption) only [rsT_add, rsT_rsT] using this
    have E := cmp p p' a
    have k8 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) := k2.trans k6
    have k9 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) := k3.trans k7
    have k10 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) := k4
    simp (disch := assumption) only [lc, rsT_sub, rsT_neg, rsT_sum, rsT_mul, rsT_rsT, rsT_constFn, constFn_sub,
      sub_mul, Finset.sum_sub_distrib]
    have E' : ∑ b, (constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ a b) *
          rsT (φ b (j p.1) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') -
        constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ' a b) *
          rsT (φ b (j p.1) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) =
        rsT (h p a) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') - rsT (h p' a) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') +
        ∑ b, constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ' a b) *
          (rsT (φ b (j' p.2) (j p.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') -
            rsT (φ b (j' p'.2) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) := by
      rw [E, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      linear_combination (constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ' a b)) * (C1 b - C2 b)
    simp only [Pi.sub_apply, constFn_sub, sub_mul, mul_sub, Finset.sum_sub_distrib] at E' ⊢
    linear_combination E'

theorem eq_of_resG_eq_of_dense {Y : Scheme.{0}} [IsReduced Y] {U V : Y.Opens} (hV : Dense (V : Set Y))
    (f g : Γ(Y, U)) (h : resG Y (inf_le_left : U ⊓ V ≤ U) f = resG Y inf_le_left g) : f = g := by
  rw [← sub_eq_zero, ← AlgebraicGeometry.basicOpen_eq_bot_iff]
  have h0 : Y.basicOpen (resG Y (inf_le_left : U ⊓ V ≤ U) (f - g)) = ⊥ := by
    rw [map_sub, h, sub_self, Scheme.basicOpen_zero]
  rw [resG, Scheme.basicOpen_res] at h0
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨y, hy1, hy2⟩ := hV.inter_open_nonempty _ (Y.basicOpen (f - g)).isOpen ⟨x, hx⟩
  have : y ∈ (U ⊓ V) ⊓ Y.basicOpen (f - g) := ⟨⟨Y.basicOpen_le _ hy1, hy2⟩, hy1⟩
  rw [h0] at this
  exact this.elim

theorem isKS_unique_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), IsKS Y.t (interior Y) U v D.1 Θ → IsKS Y.t (interior Y) U v D.1 Θ' → Θ = Θ' := by
  intro E _ _ _ H Dw l Xo c Y _ _ _ _ U n v A hv hb hA D Θ Θ' hK hK'
  haveI : IsReduced Y.X := GlobalTheory.Coisotropic.isReduced_of_isNormalScheme Y.normal
  have key : ∀ {K : Type} [Field K] (x0 : Sp K ⟶ Y.X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1), ⊤ ≤ x0 ⁻¹ᵁ interior Y →
      ∀ a b, GlobalTheory.FlagMod.ev x0 U.1 hU (Θ a b) = GlobalTheory.FlagMod.ev x0 U.1 hU (Θ' a b) := by
    intro K _ x0 hU hV a b
    obtain ⟨P₀, θm, hpb, hiso⟩ := exists_polAV_interior Y x0 hV
    haveI : IsCommMonObj P₀.A := P₀.isAb.comm
    have hx : spMap (GlobalTheory.FlagMod.ev x0 U.1 hU) ≫ chart U = x0 := GlobalTheory.FlagMod.spMap_ev x0 U.2 hU
    have hv' := fun i => GlobalTheory.LieMet.isTan_map (GlobalTheory.FlagMod.ev x0 U.1 hU) hx (hv i)
    have hb' := GlobalTheory.GradedPieces.basis_map (GlobalTheory.FlagMod.ev x0 U.1 hU) hx hv hb
    obtain ⟨u, hu, hu'⟩ := GlobalTheory.LiePull.lieBasis_of_tanBasis Y.t x0 P₀.A θm hpb _ hv' hb'
    choose dd hdd using fun a => (GlobalTheory.KS.InvField.main K P₀.A (u a) (hu.1 a)).1
    obtain ⟨⟨φ, hφ⟩, -⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hu hdd _ θm Y.t.PP.L Y.t.PP.isLB hiso
    obtain ⟨J, W, j, d, hcov, hWj, hf, hl, hdiff⟩ := hK
    obtain ⟨J', W', j', d', hcov', hWj', hf', hl', hdiff'⟩ := hK'
    have hP := pull_diff Y.t (interior Y) U v hv Θ W j d hWj hdiff x0 hU P₀.A θm hpb u hu' dd hdd φ hφ
    have hP' := pull_diff Y.t (interior Y) U v hv Θ' W' j' d' hWj' hdiff' x0 hU P₀.A θm hpb u hu' dd hdd φ hφ
    have hWU : ∀ i, W i ≤ Y.t.G.hom ⁻¹ᵁ U.1 := fun i p hp => by
      have : p ∈ Y.t.G.hom ⁻¹ᵁ (U.1 ⊓ interior Y) := hcov ▸ (le_iSup W i) hp
      exact this.1
    have hWU' : ∀ i, W' i ≤ Y.t.G.hom ⁻¹ᵁ U.1 := fun i p hp => by
      have : p ∈ Y.t.G.hom ⁻¹ᵁ (U.1 ⊓ interior Y) := hcov' ▸ (le_iSup W' i) hp
      exact this.1
    have hfib : ∀ z, Y.t.G.hom (θm z) ∈ U.1 ⊓ interior Y := fun z => by
      rw [← Scheme.Hom.comp_apply, hpb.1.w, Scheme.Hom.comp_apply]
      exact ⟨hU (Set.mem_univ _), hV (Set.mem_univ _)⟩
    have hcv : ∀ z, ∃ i, θm z ∈ W i := fun z => by
      have h2 : θm z ∈ ⨆ i, W i := by rw [hcov]; exact hfib z
      exact TopologicalSpace.Opens.mem_iSup.1 h2
    have hcv' : ∀ z, ∃ i, θm z ∈ W' i := fun z => by
      have h2 : θm z ∈ ⨆ i, W' i := by rw [hcov']; exact hfib z
      exact TopologicalSpace.Opens.mem_iSup.1 h2
    have := theta_eq_fibre P₀ u hu dd hdd Y.t.G.hom x0 θm hpb.1 U.2 Y.t.PP.L Y.t.PP.isLB hiso _
      (Matrix.of fun a b => GlobalTheory.FlagMod.ev x0 U.1 hU (Θ a b)) (Matrix.of fun a b => GlobalTheory.FlagMod.ev x0 U.1 hU (Θ' a b))
      W W' j j' d d' hWU hWU' hWj hWj' hcv hcv' hf hf' hl hl' φ hφ hP hP'
    exact congrFun (congrFun this a) b
  refine Matrix.ext fun a b => eq_of_resG_eq_of_dense (V := interior Y) (dense_interior Y) _ _ ?_
  refine GlobalTheory.GenericExtend.eq_of_valR_eq fun x hx => ⟨Y.X.residueField x, inferInstance,
    Y.X.fromSpecResidueField x, fun o => Scheme.fromSpecResidueField_apply x o, ?_⟩
  have ho : ∀ o, (Y.X.fromSpecResidueField x : Sp (Y.X.residueField x) ⟶ Y.X) o = x :=
    fun o => Scheme.fromSpecResidueField_apply x o
  generalize (Y.X.fromSpecResidueField x : Sp (Y.X.residueField x) ⟶ Y.X) = h at ho
  have hU : ⊤ ≤ h ⁻¹ᵁ U.1 := fun o _ => show h o ∈ U.1 by rw [ho]; exact hx.1
  have hV : ⊤ ≤ h ⁻¹ᵁ interior Y := fun o _ => show h o ∈ interior Y by rw [ho]; exact hx.2
  have hUV : ⊤ ≤ h ⁻¹ᵁ (U.1 ⊓ interior Y) := fun o _ => show h o ∈ U.1 ⊓ interior Y by rw [ho]; exact hx
  exact (GlobalTheory.CechKS.valR_resG h _ hUV _).trans ((GlobalTheory.CechKS.valR_eq_ev _ _ hU _).trans ((key h hU hV a b).trans
    ((GlobalTheory.CechKS.valR_eq_ev _ _ hU _).symm.trans (GlobalTheory.CechKS.valR_resG h _ hUV _).symm)))

end GlobalTheory.KSUniq
