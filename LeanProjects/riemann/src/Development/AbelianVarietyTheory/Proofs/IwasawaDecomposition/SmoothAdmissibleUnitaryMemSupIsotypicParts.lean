import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.SpanIsot

section Abs

variable {G : Type} [Group G] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def Stab (ρ : G →* Module.End ℂ V) (W : Submodule ℂ V) : Prop := ∀ g, ∀ v ∈ W, ρ g v ∈ W

def IrrSub (ρ : G →* Module.End ℂ V) (W : Submodule ℂ V) : Prop :=
  W ≠ ⊥ ∧ Stab ρ W ∧ ∀ W' ≤ W, Stab ρ W' → W' = ⊥ ∨ W' = W

variable (ρ : G →* Module.End ℂ V) (hunit : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)

theorem rho_inv_apply (g : G) (y : V) : ρ g (ρ g⁻¹ y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

include hunit in
theorem inner_rho_left (g : G) (x y : V) : inner ℂ (ρ g x) y = inner ℂ x (ρ g⁻¹ y) := by
  conv_lhs => rw [← rho_inv_apply ρ g y]
  rw [hunit]

include hunit in
theorem stab_orth {W : Submodule ℂ V} (hW : Stab ρ W) : Stab ρ Wᗮ := by
  intro g v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  rw [← rho_inv_apply ρ g u, hunit]
  exact hv _ (hW _ _ hu)

theorem stab_inf {W W' : Submodule ℂ V} (h : Stab ρ W) (h' : Stab ρ W') : Stab ρ (W ⊓ W') :=
  fun g v hv => ⟨h g v hv.1, h' g v hv.2⟩

theorem stab_span (S : Set V) : Stab ρ (Submodule.span ℂ {v | ∃ g, ∃ s ∈ S, v = ρ g s}) := by
  intro g v hv
  have : Submodule.span ℂ {v | ∃ g, ∃ s ∈ S, v = ρ g s} ≤
      (Submodule.span ℂ {v | ∃ g, ∃ s ∈ S, v = ρ g s}).comap (ρ g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g', s, hs, rfl⟩
    exact Submodule.subset_span ⟨g * g', s, hs, by rw [map_mul, Module.End.mul_apply]⟩
  exact this hv

variable (K : Subgroup G) (F : Submodule ℂ V) [FiniteDimensional ℂ F]
  (hF : ∀ v, v ∈ F ↔ ∀ k ∈ K, ρ k v = v)
  (horb : ∀ y, ((fun k : G => ρ k y) '' (K : Set G)).Finite)

include hunit hF horb in

theorem proj {U : Submodule ℂ V} (hU : Stab ρ U) {x : V} (hx : x ∈ F) :
    ∃ u ∈ U ⊓ F, ∀ y ∈ U, inner ℂ (x - u) y = 0 := by
  haveI : FiniteDimensional ℂ ↥(U ⊓ F) := Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨u, huU, hu⟩ := GlobalTheory.IsotOrth.exists_proj ρ hunit K U (U ⊓ F) hU inf_le_left
    (fun w hw k hk => (hF w).1 hw.2 k hk) (fun w hw hfix => ⟨hw, (hF w).2 hfix⟩)
    (fun y _ => horb y) x ((hF x).1 hx)
  refine ⟨u, ⟨huU, (hF u).2 fun k hk => ?_⟩, hu⟩
  have h1 : ∀ y ∈ U, inner ℂ (x - ρ k u) y = 0 := by
    intro y hy
    have : x - ρ k u = ρ k (x - u) := by rw [map_sub, (hF x).1 hx k hk]
    rw [this, inner_rho_left ρ hunit]
    exact hu _ (hU _ _ hy)
  have h2 : ∀ y ∈ U, inner ℂ (u - ρ k u) y = 0 := by
    intro y hy
    have : u - ρ k u = (x - ρ k u) - (x - u) := by abel
    rw [this, inner_sub_left, h1 y hy, hu y hy, sub_zero]
  have h3 := inner_self_eq_zero.1 (h2 _ (U.sub_mem huU (hU k u huU)))
  exact (sub_eq_zero.1 h3).symm

include hunit hF horb in

theorem mem_sSup_irr : ∀ x ∈ F, x ∈ sSup {W | IrrSub ρ W} := by
  haveI hfd : ∀ U : Submodule ℂ V, FiniteDimensional ℂ ↥(U ⊓ F) :=
    fun U => Submodule.finiteDimensional_of_le inf_le_right
  suffices key : ∀ d : ℕ, ∀ U : Submodule ℂ V, Stab ρ U → Module.finrank ℂ ↥(U ⊓ F) ≤ d →
      ∀ x ∈ U ⊓ F, x ∈ sSup {W | IrrSub ρ W} by
    intro x hx
    exact key _ ⊤ (fun _ _ _ => Submodule.mem_top) le_rfl x ⟨Submodule.mem_top, hx⟩
  intro d
  induction d with
  | zero =>
    intro U _ hd x hx
    have : U ⊓ F = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hd)
    rw [this, Submodule.mem_bot] at hx
    rw [hx]; exact zero_mem _
  | succ d ih =>
    intro U hU hd x hx
    by_cases hb : U ⊓ F = ⊥
    · rw [hb, Submodule.mem_bot] at hx; rw [hx]; exact zero_mem _
    classical
    have hex : ∃ m, ∃ W : Submodule ℂ V, W ≤ U ∧ Stab ρ W ∧ W ⊓ F ≠ ⊥ ∧
        Module.finrank ℂ ↥(W ⊓ F) = m := ⟨_, U, le_rfl, hU, hb, rfl⟩
    obtain ⟨W, hWU, hWs, hWb, hWm⟩ := Nat.find_spec hex
    set E := W ⊓ F with hE
    set V' := Submodule.span ℂ {v | ∃ g, ∃ s ∈ (E : Set V), v = ρ g s} with hV'
    have hV's : Stab ρ V' := stab_span ρ _
    have hEV' : E ≤ V' := fun e he => Submodule.subset_span ⟨1, e, he, by simp⟩
    have hV'W : V' ≤ W := Submodule.span_le.2 (by rintro _ ⟨g, s, hs, rfl⟩; exact hWs g s hs.1)
    have hirr : IrrSub ρ V' := by
      refine ⟨fun h => hWb (eq_bot_iff.2 (h ▸ hEV')), hV's, fun W' hW'V hW's => ?_⟩
      by_cases hb' : W' ⊓ F = ⊥
      · left
        have hEo : E ≤ W'ᗮ := by
          intro e he
          obtain ⟨u, hu, hu'⟩ := proj ρ hunit K F hF horb hW's he.2
          have hu0 : u = 0 := by rw [hb', Submodule.mem_bot] at hu; exact hu
          rw [Submodule.mem_orthogonal]
          intro w hw
          have := hu' w hw
          rw [hu0, sub_zero] at this
          exact inner_eq_zero_symm.1 this
        have hV'o : V' ≤ W'ᗮ := Submodule.span_le.2 (by
          rintro _ ⟨g, s, hs, rfl⟩; exact stab_orth ρ hunit hW's g s (hEo hs))
        rw [eq_bot_iff]
        intro w hw
        have := hV'o (hW'V hw)
        rw [Submodule.mem_orthogonal] at this
        rw [Submodule.mem_bot]
        exact inner_self_eq_zero.1 (this w hw)
      · right
        have hle : W' ⊓ F ≤ E := inf_le_inf_right F (hW'V.trans hV'W)
        have hmin := Nat.find_min' hex ⟨W', hW'V.trans (hV'W.trans hWU), hW's, hb', rfl⟩
        have heq : W' ⊓ F = E := Submodule.eq_of_le_of_finrank_le hle ((le_of_eq hWm).trans hmin)
        refine le_antisymm hW'V (Submodule.span_le.2 ?_)
        rintro _ ⟨g, s, hs, rfl⟩
        have hs' : s ∈ W' ⊓ F := by rw [heq]; exact hs
        exact hW's g s hs'.1
    obtain ⟨u, hu, hu'⟩ := proj ρ hunit K F hF horb hV's hx.2
    have huS : u ∈ sSup {W | IrrSub ρ W} := (le_sSup (show V' ∈ {W | IrrSub ρ W} from hirr)) hu.1
    have hU2 : Stab ρ (U ⊓ V'ᗮ) := stab_inf ρ hU (stab_orth ρ hunit hV's)
    have hxu : x - u ∈ (U ⊓ V'ᗮ) ⊓ F :=
      ⟨⟨U.sub_mem hx.1 (hWU (hV'W hu.1)), (Submodule.mem_orthogonal' _ _).2 hu'⟩, F.sub_mem hx.2 hu.2⟩
    have hlt : (U ⊓ V'ᗮ) ⊓ F < U ⊓ F := by
      refine lt_of_le_of_ne (inf_le_inf_right F inf_le_left) fun h => hWb ?_
      rw [eq_bot_iff]
      intro e he
      have he2 : e ∈ (U ⊓ V'ᗮ) ⊓ F := by rw [h]; exact ⟨hWU he.1, he.2⟩
      have : e ∈ V'ᗮ := he2.1.2
      rw [Submodule.mem_orthogonal] at this
      exact (Submodule.mem_bot ℂ).2 (inner_self_eq_zero.1 (this e (hEV' he)))
    have hd2 : Module.finrank ℂ ↥((U ⊓ V'ᗮ) ⊓ F) ≤ d := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    have h5 := ih _ hU2 hd2 (x - u) hxu
    have : x = (x - u) + u := by abel
    rw [this]; exact add_mem h5 huS

end Abs

end GlobalTheory.SpanIsot

namespace GlobalTheory.SpanIsot

open Formalism.L2.NG Formalism.AUTREP Formalism.IndefR.principalLevelFrame

theorem irr_le_isotIn {D : D7} {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]
    (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A)
    (h7 : ∀ x ∈ C, ∃ N : ℕ, 0 < N ∧ ∀ κ, Cong D.host.E n N κ → ρ κ x = x)
    (W : Submodule ℂ A) (hWC : W ≤ C) (hW0 : W ≠ ⊥) (hWs : ∀ h, ∀ x ∈ W, ρ h x ∈ W)
    (hWi : ∀ W' ≤ W, (∀ h, ∀ x ∈ W', ρ h x ∈ W') → W' = ⊥ ∨ W' = W) :
    ∃ π : FinTyp D.host.E n, W ≤ isotIn (D := D) ρ C π := by
  classical
  obtain ⟨s₀, hs₀, hs₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual ℂ A, l s₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hs₀0 ((Module.forall_dual_apply_eq_zero_iff ℂ s₀).1 hcon)
  let m : A →ₗ[ℂ] (GAf D.host.E n → ℂ) :=
    { toFun := fun a g => l (ρ g a)
      map_add' := fun a b => by funext g; simp
      map_smul' := fun c a => by funext g; simp }
  have hm : ∀ h a, m (ρ h a) = rt D.host.E n h (m a) := by
    intro h a
    funext g
    show l (ρ g (ρ h a)) = l (ρ (g * h) a)
    rw [map_mul, Module.End.mul_apply]
  let mW : W →ₗ[ℂ] (GAf D.host.E n → ℂ) := m ∘ₗ W.subtype
  have hmW : ∀ w : W, mW w = m w := fun w => rfl
  have hinj : Function.Injective mW := by
    rw [← LinearMap.ker_eq_bot]
    have hK's : ∀ h, ∀ x ∈ (LinearMap.ker mW).map W.subtype, ρ h x ∈ (LinearMap.ker mW).map W.subtype := by
      rintro h _ ⟨w, hw, rfl⟩
      refine ⟨⟨ρ h w, hWs h w w.2⟩, ?_, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker] at hw ⊢
      rw [hmW] at hw
      show m (ρ h w) = 0
      rw [hm, hw, map_zero]
    rcases hWi _ (Submodule.map_subtype_le _ _) hK's with h | h
    · rw [eq_bot_iff]
      intro w hw
      have : (w : A) ∈ (LinearMap.ker mW).map W.subtype := ⟨w, hw, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
    · exfalso
      have : s₀ ∈ (LinearMap.ker mW).map W.subtype := by rw [h]; exact hs₀
      obtain ⟨w, hw, hw'⟩ := this
      have h1 : mW w 1 = 0 := by rw [LinearMap.mem_ker.1 hw]; rfl
      apply hl
      rw [← hw']
      have : mW w 1 = l (ρ 1 w) := rfl
      rw [this, map_one, Module.End.one_apply] at h1
      exact h1
  let e := LinearEquiv.ofInjective mW hinj
  have he : ∀ w : W, ((e w : LinearMap.range mW) : GAf D.host.E n → ℂ) = m w := fun w => rfl
  let π : FinTyp D.host.E n :=
    { S := LinearMap.range mW
      stable := by
        rintro h _ ⟨w, rfl⟩
        exact ⟨⟨ρ h w, hWs h w w.2⟩, (hm h w)⟩
      smooth := by
        rintro _ ⟨w, rfl⟩
        obtain ⟨N, hN, hfix⟩ := h7 w (hWC w.2)
        exact ⟨N, hN, fun κ hκ => by rw [hmW, ← hm, hfix κ hκ]⟩
      ne := by
        intro h
        have : mW ⟨s₀, hs₀⟩ ∈ LinearMap.range mW := ⟨_, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact hs₀0 (congrArg Subtype.val (hinj (this.trans (map_zero mW).symm)))
      irr := by
        intro S' hS' hst
        have hW's : ∀ h, ∀ x ∈ (S'.comap mW).map W.subtype, ρ h x ∈ (S'.comap mW).map W.subtype := by
          rintro h _ ⟨w, hw, rfl⟩
          refine ⟨⟨ρ h w, hWs h w w.2⟩, ?_, rfl⟩
          show m (ρ h w) ∈ S'
          rw [hm]
          exact hst h _ hw
        rcases hWi _ (Submodule.map_subtype_le _ _) hW's with h | h
        · left
          rw [eq_bot_iff]
          intro f hf
          obtain ⟨w, rfl⟩ := hS' hf
          have : (w : A) ∈ (S'.comap mW).map W.subtype := ⟨w, hf, rfl⟩
          rw [h, Submodule.mem_bot] at this
          have : w = 0 := Subtype.ext this
          rw [this, map_zero]
          exact Submodule.zero_mem _
        · right
          refine le_antisymm hS' ?_
          rintro _ ⟨w, rfl⟩
          have : (w : A) ∈ (S'.comap mW).map W.subtype := by rw [h]; exact w.2
          obtain ⟨w', hw', he'⟩ := this
          have : w' = w := Subtype.ext he'
          rw [← this]
          exact hw' }
  let Φ : π.S →ₗ[ℂ] A := W.subtype ∘ₗ (e.symm : LinearMap.range mW →ₗ[ℂ] W)
  have hΦe : ∀ w : W, Φ (e w) = w := fun w => by simp [Φ]
  have hΦeq : IsEqvA ρ π Φ := by
    intro h f
    obtain ⟨w, rfl⟩ := e.surjective f
    have : (⟨rt D.host.E n h ((e w : LinearMap.range mW) : GAf D.host.E n → ℂ), π.stable h _ (e w).2⟩ : π.S) =
        e ⟨ρ h w, hWs h w w.2⟩ := by
      apply Subtype.ext
      show rt D.host.E n h (m w) = m (ρ h w)
      exact (hm h w).symm
    rw [this, hΦe, hΦe]
  have hrange : LinearMap.range Φ ≤ C := by
    rintro _ ⟨f, rfl⟩
    exact hWC (e.symm f).2
  refine ⟨π, fun x hx => ?_⟩
  have hle : LinearMap.range Φ ≤ isotIn (D := D) ρ C π :=
    le_iSup₂ (f := fun (Φ : π.S →ₗ[ℂ] A) (_ : IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) => LinearMap.range Φ)
      Φ ⟨hΦeq, hrange⟩
  exact hle ⟨e ⟨x, hx⟩, hΦe _⟩

end GlobalTheory.SpanIsot

namespace GlobalTheory.SpanIsot

open Formalism.L2.NG Formalism.AUTREP Formalism.IndefR.principalLevelFrame

theorem span_isotIn : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ h, ∀ x ∈ C, ρ h x ∈ C) → (∀ h, ∀ x ∈ C, ∀ y ∈ C, B (ρ h x) (ρ h y) = B x y) → (∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N κ → ρ κ x = x})) → (∀ x ∈ C, ∃ N : ℕ, 0 < N ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N κ → ρ κ x = x) → ∀ x ∈ C, x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, principalLevelFrame.isotIn (D := D) ρ C π := by
  intro D n A _ _ ρ C B h1 h2 h3 h4 h5 h6 h7 x hx
  obtain ⟨N, hN, hxN⟩ := h7 x hx
  let core := GlobalTheory.IsotOrth.coreOf C B h1 h2 h3
  letI : NormedAddCommGroup C := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ C := InnerProductSpace.ofCore core.toCore
  let ρC := GlobalTheory.IsotOrth.rhoC ρ C h4
  have hρC : ∀ g (c : C), ((ρC g c : C) : A) = ρ g c := fun g c => rfl
  have hunit : ∀ g (x y : C), inner ℂ (ρC g x) (ρC g y) = inner ℂ x y := fun g x y => h5 g x x.2 y y.2
  let F : Submodule ℂ C := fixN ρC N
  haveI := h6 N hN
  let ι : F →ₗ[ℂ] ↥(Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, Cong D.host.E n N κ → ρ κ x = x}) :=
    (C.subtype.comp F.subtype).codRestrict _ (fun w => Submodule.subset_span ⟨w.1.2, fun κ hκ => by
      have := congrArg Subtype.val (w.2 κ hκ)
      exact this⟩)
  have hι : Function.Injective ι := fun a b h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  haveI : FiniteDimensional ℂ F := FiniteDimensional.of_injective ι hι
  have hF : ∀ v, v ∈ F ↔ ∀ k ∈ GlobalTheory.IsotOrth.congSub D.host.E n N, ρC k v = v := fun v => Iff.rfl
  have horb : ∀ y : C, ((fun k => ρC k y) '' (GlobalTheory.IsotOrth.congSub D.host.E n N : Set (GAf D.host.E n))).Finite := by
    intro y
    obtain ⟨N', hN', hy⟩ := h7 y y.2
    refine (GlobalTheory.IsotOrth.orbit_finite ρC hN' y (fun κ hκ => Subtype.ext (hy κ hκ))).subset ?_
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hk.1, rfl⟩
  have hmem := mem_sSup_irr ρC hunit _ F hF horb ⟨x, hx⟩ (fun κ hκ => Subtype.ext (hxN κ hκ))
  have hle : sSup {W | IrrSub ρC W} ≤
      (⨆ π : FinTyp D.host.E n, isotIn (D := D) ρ C π).comap C.subtype := by
    refine sSup_le fun W hW => ?_
    rw [← Submodule.map_le_iff_le_comap]
    obtain ⟨hW0, hWs, hWi⟩ := hW
    obtain ⟨π, hπ⟩ := irr_le_isotIn ρ C h7 (W.map C.subtype) (Submodule.map_subtype_le _ _)
      (by
        intro h
        obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
        have : ((w : C) : A) ∈ W.map C.subtype := ⟨w, hw, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact hw0 (Subtype.ext this))
      (by
        rintro h _ ⟨w, hw, rfl⟩
        exact ⟨ρC h w, hWs h w hw, rfl⟩)
      (by
        intro W' hW'W hW's
        have hs : Stab ρC (W'.comap C.subtype) := fun g c hc => by
          show ((ρC g c : C) : A) ∈ W'
          rw [hρC]
          exact hW's g _ hc
        have hle' : W'.comap C.subtype ≤ W := by
          intro c hc
          obtain ⟨w, hw, e⟩ := hW'W hc
          have : w = c := Subtype.ext e
          rw [← this]
          exact hw
        rcases hWi _ hle' hs with h | h
        · left
          rw [eq_bot_iff]
          intro a ha
          obtain ⟨w, _, rfl⟩ := hW'W ha
          have : w ∈ W'.comap C.subtype := ha
          rw [h, Submodule.mem_bot] at this
          rw [Submodule.mem_bot, this]
          rfl
        · right
          refine le_antisymm hW'W ?_
          rintro _ ⟨w, hw, rfl⟩
          have : w ∈ W'.comap C.subtype := by rw [h]; exact hw
          exact this)
    exact hπ.trans (le_iSup (fun π : FinTyp D.host.E n => isotIn (D := D) ρ C π) π)
  exact hle hmem

end GlobalTheory.SpanIsot
