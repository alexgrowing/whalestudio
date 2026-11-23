import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLeMaximalIdealPowSmulOfDirected
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.Izumi

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem norm_val_add_le {U : Set M.Z} {x : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hy : M.Cen U x y)
    (F G : M.O x) :
    ‖M.val (gPt p ≫ y) ((F + G : M.O x) : Ω)‖ ≤ max ‖M.val (gPt p ≫ y) (F : Ω)‖ ‖M.val (gPt p ≫ y) (G : Ω)‖ := by
  rw [Subalgebra.coe_add, RatModel.val_add (RatModel.gPt_specializes hy.1) F.2 G.2]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem norm_val_mul_le {U : Set M.Z} {x : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hy : M.Cen U x y)
    (c F : M.O x) : ‖M.val (gPt p ≫ y) ((c * F : M.O x) : Ω)‖ ≤ ‖M.val (gPt p ≫ y) (F : Ω)‖ := by
  rw [Subalgebra.coe_mul, RatModel.val_mul (RatModel.gPt_specializes hy.1) c.2 F.2, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hy.norm_val_le_one c.2)

def smallIdeal (U : M.Z.Opens) (x : M.Z) (f : Ω) (N : ℕ) : Ideal (M.O x) where
  carrier := {F | ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y →
      ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨
        ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ N}
  zero_mem' := by
    intro p _ y _
    left
    have h0 : ((0 : M.O x) : Ω) = 0 := rfl
    rw [h0, RatModel.val_zero, norm_zero]
    exact norm_nonneg _
  add_mem' := by
    intro F G hF hG p _ y hy
    have h := norm_val_add_le M hy F G
    rcases le_total ‖M.val (gPt p ≫ y) (F : Ω)‖ ‖M.val (gPt p ≫ y) (G : Ω)‖ with hle | hle
    · rw [max_eq_right hle] at h
      rcases hG p y hy with h' | ⟨k, hk, h'⟩
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨k, hk, h.trans h'⟩
    · rw [max_eq_left hle] at h
      rcases hF p y hy with h' | ⟨k, hk, h'⟩
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨k, hk, h.trans h'⟩
  smul_mem' := by
    intro c F hF p _ y hy
    have h := norm_val_mul_le M hy c F
    rcases hF p y hy with h' | ⟨k, hk, h'⟩
    · exact Or.inl (h.trans h')
    · exact Or.inr ⟨k, hk, h.trans h'⟩

variable {M}

theorem mem_smallIdeal {U : M.Z.Opens} {x : M.Z} {f : Ω} {N : ℕ} {F : M.O x} :
    F ∈ smallIdeal M U x f N ↔ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y →
      ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨
        ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ N := Iff.rfl

theorem smallIdeal_antitone (U : M.Z.Opens) (x : M.Z) (f : Ω) : Antitone (smallIdeal M U x f) := by
  intro N N' hN F hF p _ y hy
  rcases hF p y hy with h' | ⟨k, hk, h'⟩
  · exact Or.inl h'
  · refine Or.inr ⟨k, hk, h'.trans (pow_le_pow_of_le_one (norm_nonneg _) (hy.norm_val_le_one hk.1) hN)⟩

theorem self_mem_smallIdeal (U : M.Z.Opens) {x : M.Z} {f : Ω} (hf : f ∈ M.O x) (N : ℕ) :
    (⟨f, hf⟩ : M.O x) ∈ smallIdeal M U x f N :=
  fun _ _ _ _ => Or.inl le_rfl

end GlobalTheory.Izumi

namespace GlobalTheory.Izumi

open IsLocalRing

theorem exists_le_span_sup_pow (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : ℕ → Ideal A)
    (f : A) (hK : Antitone K) (hf : ∀ N, f ∈ K N)
    (h : ⨅ N, (K N).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) ≤
      Ideal.span {algebraMap A (AdicCompletion (maximalIdeal A) A) f}) (e : ℕ) :
    ∃ N, K N ≤ Ideal.span {f} ⊔ maximalIdeal A ^ e := by
  set B := AdicCompletion (maximalIdeal A) A
  set φ := algebraMap A B
  haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  set I : Ideal B := Ideal.span {φ f}
  let L : ℕ → Submodule B (B ⧸ I) := fun N => Submodule.map I.mkQ ((K N).map φ)
  have hL : Directed (· ≥ ·) L := by
    refine Antitone.directed_ge fun N N' hN => ?_
    exact Submodule.map_mono (Ideal.map_mono (hK hN))
  have hIK : ∀ N, I ≤ (K N).map φ := fun N =>
    (Ideal.span_le).2 (Set.singleton_subset_iff.2 (Ideal.mem_map_of_mem φ (hf N)))
  have h0 : (⨅ N, L N) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨b, rfl⟩ := I.mkQ_surjective x
    have hb : b ∈ ⨅ N, (K N).map φ := by
      refine Submodule.mem_iInf _ |>.2 fun N => ?_
      obtain ⟨b', hb', hbb'⟩ := (Submodule.mem_iInf _).1 hx N
      have hd : b' - b ∈ I := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
        simp only [Submodule.mkQ_apply] at hbb'
        rw [hbb', sub_self]
      have := Submodule.sub_mem _ hb' (hIK N hd)
      simpa using this
    have := h hb
    simp only [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact this
  obtain ⟨N, hN⟩ := GlobalTheory.Chevalley.exists_le_maximalIdeal_pow_smul_of_directed B (B ⧸ I) ℕ L
    inferInstance hL h0 e
  refine ⟨N, fun a ha => ?_⟩
  have h1 : I.mkQ (φ a) ∈ maximalIdeal B ^ e • (⊤ : Submodule B (B ⧸ I)) :=
    hN (Submodule.mem_map_of_mem (Ideal.mem_map_of_mem φ ha))
  have h2 : maximalIdeal B ^ e • (⊤ : Submodule B (B ⧸ I)) = Submodule.map I.mkQ (maximalIdeal B ^ e) := by
    have h4 : maximalIdeal B ^ e • (⊤ : Submodule B B) = maximalIdeal B ^ e := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    rw [← Submodule.range_mkQ I, ← Submodule.map_top, ← Submodule.map_smul'', h4]
  rw [h2, ← Submodule.mem_comap, Submodule.comap_map_mkQ] at h1
  obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  set ψ := AdicCompletion.evalₐ (maximalIdeal A) (R := A) e
  have hψ : ∀ r : A, ψ (φ r) = Ideal.Quotient.mk _ r := fun r => ψ.commutes r
  have ht0 : ψ t = 0 := by
    have hle : maximalIdeal B ^ e ≤ RingHom.ker ψ.toRingHom := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      rw [hψ, Ideal.Quotient.eq_zero_iff_mem]
      exact hr
    exact hle ht
  obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective (ψ c)
  have h3 := congrArg ψ hut
  rw [map_add, map_mul, ht0, add_zero, hψ, hψ, ← hc', ← map_mul, Ideal.Quotient.eq] at h3
  have : a = c' * f + (a - c' * f) := by ring
  rw [this]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)) (by rw [← neg_sub]; exact neg_mem h3)

end GlobalTheory.Izumi
