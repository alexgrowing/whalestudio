import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieFrameIndep

theorem linearIndependent_values {Ω C E EC : Type} [Field Ω] [Field C] [AddCommGroup E] [Module Ω E]
    [AddCommGroup EC] [Module C EC] (A : Subring Ω) (ρ : A →+* C) (P : Submodule A E) (ev : P →+ EC)
    (hsm : ∀ (a : A) (e : P), ev (a • e) = ρ a • ev e) (hspan : Submodule.span C (Set.range ev) = ⊤)
    {g n : ℕ} (b : Fin g → E) (hP : P = Submodule.span A (Set.range b))
    (hfin : Module.finrank C EC = g) (S : Finset (Fin g)) (c : Fin n → E) (hc : LinearIndependent Ω c)
    (hL : Submodule.span A (b '' S) = Submodule.span A (Set.range c))
    (w : Fin n → EC) (hw : ∀ i, ∃ he : c i ∈ P, ev ⟨c i, he⟩ = w i) : LinearIndependent C w := by
  subst hP
  have hbm : ∀ k, b k ∈ Submodule.span A (Set.range b) := fun k => Submodule.subset_span ⟨k, rfl⟩
  let v : Fin g → EC := fun k => ev ⟨b k, hbm k⟩
  have hcomb : ∀ {J : Type} [Fintype J] (f : J → Fin g) (t : J → A)
      (he : ∑ i, t i • b (f i) ∈ Submodule.span A (Set.range b)),
      ev ⟨∑ i, t i • b (f i), he⟩ = ∑ i, ρ (t i) • v (f i) := by
    intro J _ f t he
    have : (⟨∑ i, t i • b (f i), he⟩ : Submodule.span A (Set.range b)) =
        ∑ i, t i • (⟨b (f i), hbm _⟩ : Submodule.span A (Set.range b)) := by
      apply Subtype.ext
      simp
    rw [this, map_sum]
    exact Finset.sum_congr rfl fun i _ => hsm _ _
  have hvspan : ⊤ ≤ Submodule.span C (Set.range v) := by
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨e, he⟩, rfl⟩
    obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 he
    have := hcomb (fun i => i) t he
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hv : LinearIndependent C v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hvspan (by simp [hfin])
  have hvS : LinearIndependent C (fun k : S => v k) := hv.comp _ Subtype.val_injective
  have himg : b '' S = Set.range (fun k : S => b k) := by
    ext y
    simp
  rw [himg] at hL
  have hcm : ∀ i, c i ∈ Submodule.span A (Set.range fun k : S => b k) := fun i => by
    rw [hL]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hbS : ∀ k : S, b k ∈ Submodule.span A (Set.range c) := fun k => by
    rw [← hL]
    exact Submodule.subset_span ⟨k, rfl⟩
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun A).1 (hcm i)
  choose d hd using fun k => (Submodule.mem_span_range_iff_exists_fun A).1 (hbS k)
  have hdelta : ∀ i j, ∑ k, a i k * d k j = if i = j then 1 else 0 := by
    intro i j
    have hexp : ∑ j, (∑ k, a i k * d k j) • c j = c i := by
      conv_rhs => rw [← ha i]
      simp only [← hd, Finset.smul_sum, Finset.sum_smul, mul_smul]
      exact Finset.sum_comm
    have hz : ∑ j, (((∑ k, a i k * d k j : A) : Ω) - if i = j then 1 else 0) • c j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [sub_eq_zero]
      exact hexp
    have := Fintype.linearIndependent_iff.1 hc _ hz j
    apply Subtype.ext
    rw [sub_eq_zero] at this
    rw [this]
    split_ifs <;> simp
  have hwexp : ∀ i, w i = ∑ k : S, ρ (a i k) • v k := by
    intro i
    obtain ⟨he, hev⟩ := hw i
    rw [← hev]
    have hmem : ∑ k : S, a i k • b k ∈ Submodule.span A (Set.range b) := by
      rw [ha i]
      exact he
    rw [← hcomb (fun k : S => (k : Fin g)) (a i) hmem]
    congr 2
    exact (ha i).symm
  rw [Fintype.linearIndependent_iff]
  intro l hl j
  have hk : ∀ k : S, ∑ i, l i * ρ (a i k) = 0 := by
    refine Fintype.linearIndependent_iff.1 hvS _ ?_
    rw [← hl]
    simp only [hwexp, Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  calc l j = ∑ i, l i * ρ (∑ k, a i k * d k j) := by
        simp only [hdelta]
        simp [apply_ite ρ]
    _ = ∑ k : S, (∑ i, l i * ρ (a i k)) * ρ (d k j) := by
        simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
        exact Finset.sum_comm
    _ = 0 := by simp [hk]

open GlobalTheory.CompanionTheory.Ar.LieVB in

theorem finrank_eq_of_isFrameAt {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {Ω : Type}
    [Field Ω] {ξ : Sp Ω ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {C : Type} [Field C]
    {z : Sp C ⟶ X} (h : genPt ξ ⤳ centre z) {EC : Type} [AddCommGroup EC] [Module C EC] (N : LieModel G z EC)
    {g : ℕ} (b : Fin g → E) (hξ : IsCptGen ξ) (hb : M.lat.IsFrameAt b ⟨centre z, h⟩) :
    Module.finrank C EC = g := by
  obtain ⟨R, _, x, hx, F, _, _, MR, n', b', hp⟩ := exists_chart G (centre z)
  have hgen : genPt ξ ∈ x.opensRange := h.mem_open x.opensRange.isOpen hp
  obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
  obtain ⟨a, ha⟩ := exists_lift x z hp
  obtain ⟨_, B, -, -⟩ := basis_tr φ x ξ hφ MR M b'
  obtain ⟨_, BC, -, -⟩ := basis_tr a x z ha MR N b'
  have hC : Module.finrank C EC = n' := by
    rw [Module.finrank_eq_card_basis BC, Fintype.card_fin]
  have hΩ : Module.finrank Ω E = n' := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  haveI : Module.Finite Ω E := Module.Finite.of_basis B
  obtain ⟨U, hU, b₂, hsp, hfr⟩ := (lieLat_isVB_of_smooth X Ω ξ G E M hξ inferInstance).1 ⟨centre z, h⟩ (Set.mem_univ _)
  have h₂ := (hfr ⟨centre z, h⟩ (Set.mem_univ _) hU).2
  have hspan : ⊤ ≤ Submodule.span Ω (Set.range b) := by
    rw [← hsp]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    have hk : b₂ k ∈ Submodule.span (regAt ξ ⟨centre z, h⟩) (Set.range b) := by
      rw [← hb.2, h₂]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact (Submodule.span_le_restrictScalars (regAt ξ ⟨centre z, h⟩) Ω (Set.range b)) hk
  have hg : Module.finrank Ω E = g := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hb.1 hspan), Fintype.card_fin]
  rw [hC, ← hΩ, hg]

end GlobalTheory.CompanionTheory.Ar.LieFrameIndep

namespace GlobalTheory.CompanionTheory.Ar

open GlobalTheory.CompanionTheory.Ar.LieFrameIndep in

theorem values_frame_sublattice_linearIndependent : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (C : Type) [Field C] (z : Sp C ⟶ X) (h : genPt ξ ⤳ centre z) (EC : Type) [AddCommGroup EC] [Module C EC] (N : LieModel G z EC) (g n : ℕ) (b : Fin g → E) (S : Finset (Fin g)) (c : Fin n → E) (L : Lat ξ E) (w : Fin n → EC), IsCptGen ξ → M.lat.IsFrameAt b ⟨centre z, h⟩ → L ⟨centre z, h⟩ = Submodule.span (regAt ξ ⟨centre z, h⟩) (b '' S) → L.IsFrameAt c ⟨centre z, h⟩ → (∀ i, M.ValAt z (c i) (N.pt (w i))) → LinearIndependent C w := by
  intro X G _ _ _ Ω _ ξ E _ _ M C _ z h EC _ _ N g n b S c L w hξ hb hLb hLc hw
  obtain ⟨ev, h1, h2, h3⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ E M C z h EC N hξ inferInstance
  let e : X.presheaf.stalk (centre z) ≃+* regAt ξ ⟨centre z, h⟩ :=
    RingEquiv.ofBijective (genMap ξ ⟨centre z, h⟩).rangeRestrict
      ⟨fun s t est => hξ.inj ⟨centre z, h⟩ (congrArg Subtype.val est), RingHom.rangeRestrict_surjective _⟩
  let ρ : regAt ξ ⟨centre z, h⟩ →+* C :=
    (Scheme.stalkClosedPointTo z).hom.comp (e.symm : regAt ξ ⟨centre z, h⟩ →+* X.presheaf.stalk (centre z))
  have hρ : ∀ a : regAt ξ ⟨centre z, h⟩, ValAt ξ z (a : Ω) (ρ a) := fun a =>
    ⟨h, e.symm a, congrArg Subtype.val (e.apply_symm_apply a), rfl⟩
  refine linearIndependent_values (regAt ξ ⟨centre z, h⟩) ρ (M.lat ⟨centre z, h⟩) ev
    (fun a x => h2 a _ x (hρ a)) h3 b hb.2 (finrank_eq_of_isFrameAt M h N b hξ hb) S c hLc.1 ?_ w
    fun i => (h1 _ _).1 (hw i)
  rw [← hLb, hLc.2]

end GlobalTheory.CompanionTheory.Ar
