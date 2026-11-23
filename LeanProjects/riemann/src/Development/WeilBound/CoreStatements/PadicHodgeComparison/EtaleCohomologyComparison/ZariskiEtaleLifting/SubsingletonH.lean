import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDpOfCompOnGens
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsE
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FGlue
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FGlob
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FLineUniv
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FReesUp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FReesDown
import BuildAid.D2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris

namespace CrystallineSemistableComparison.B

open PAlg CH

theorem exists_dp {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) (h : i.Flat) (I : Ideal Λ) (γ : DividedPowers I) :
    ∃ δ : DividedPowers (I.map i), IsDPMorphism γ δ i := by
  let _ := i.toAlgebra
  have : Module.Flat Λ D := h
  exact GlobalTheory.CompanionTheory.JLiftDP.dpFlat Λ D I γ

variable {l : ℕ} [Fact l.Prime]

theorem local_of (hD : D.Out l) : Local l := by
  intro d j
  obtain ⟨N, hN⟩ := P.glue.{0, 0, 1, 0, 1, 0, 1} d j
  refine ⟨N, fun {O} _ F κ ε k n ρ hρ hn hk s => ?_⟩
  obtain ⟨𝓛⟩ := P.elift s.a (fun k => (s.T k : s.R)) (bs l k n).I (κb κ k n) s.et
  obtain ⟨δ, hδ⟩ := exists_dp 𝓛.i (P.lift_flat 𝓛.i 𝓛.t 𝓛.et).1 (bs l k n).I (bs l k n).γ
  have hp : (bs l k n).p ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hnil : IsNilpotent ((bs l k n).p : (bs l k n).R) := ⟨n, (base l).pow_l_acr n⟩
  obtain ⟨𝒯⟩ := P.tower_ex κ s
  obtain ⟨A, hA⟩ := P.thick_act s (b := bs l k n) rfl 𝓛 δ hδ hp hnil (ε.qU n) (ε.qU_mem k n)
  obtain ⟨A', hA'⟩ := P.tower_act 𝒯 ε
  obtain ⟨θ, hθ, hθγ⟩ := P.theta_ex 𝒯 k n 𝓛 δ hδ hp hnil ε A A' hA hA'
  have hε := P.eps_facts ε
  have hq : (ε.qU n : (bs l k n).R) = (base l).cris n (ε.qk 1) ^ (bs l k n).p :=
    (ε.qU_val n).trans ((congrArg ((base l).cris n) (hε.2.1 0).symm).trans (map_pow _ _ _))
  have hμ : (base l).cris n ε.μ = (ε.qU n : (bs l k n).R) - 1 := by
    rw [Eps.μ, map_sub, map_one, ε.qU_val]
  have hξ : (∑ i ∈ Finset.range (bs l k n).p, (base l).cris n (ε.qk 1) ^ i) ∈ (bs l k n).I := by
    have := fil_le k (base l) n (hε.2.2.1 (base l) n)
    simpa only [map_sum, map_pow] using this
  obtain ⟨L, hL⟩ := P.line_univ (thU (Lc F κ k n) (ε.qU n) (ε.qU_mem k n)) (fun _ _ i g => (flt F κ ε k n ρ hρ).FAcyc i g)
    (P.thick_line F (bs l k n) rfl (κb κ k n) ((base l).cris n) ρ hρ ε.μ (ε.μ_mem k (base l) n) (ε.qU n) (ε.qU_mem k n)
      ((base l).cris n (ε.qk 1)) Fact.out hq hμ hξ)
  obtain ⟨L', hL'⟩ := P.cont_line F κ ε k n ρ hρ
  obtain ⟨ni⟩ := P.local_ni 𝒯 k n 𝓛 δ hδ hp hnil ε ρ hρ A.γ A'.γ ⟨fun _ => θ, fun _ _ a => hθγ a⟩ hn hθ
    (fun a j => (hA _ _ (𝟙 _) j).trans (congrArg (· * 𝓛.t j) (Units.val_pow_eq_pow_val _ _)))
    (fun a j => (hA' _ _ (𝟙 _) j).trans (congrArg (· * (𝒯.c j 0).val) (Units.val_pow_eq_pow_val _ _)))
  exact hN (flt F κ ε k n ρ hρ).rees (gE F κ k n) (jE _) _ _ A L _ _ A' L' θ hθγ _
    (fun T => (P.rees_up (flt F κ ε k n ρ hρ) (𝟭 _) 0).2.2 _ _ (hL T)) (P.desc hD F κ ε k n ρ hρ hk)
    (fun T => (P.rees_up ((flt F κ ε k n ρ hρ).comap (gE F κ k n)) (𝟭 _) 0).2.2 _ _ (hL' T)) ni

theorem ri_pow {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R} {G : C' ⥤ C}
    {s : R} {a b n : ℕ} (h : a ≤ b) (H : RI (s ^ a) n F G) : RI (s ^ b) n F G := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  exact (P.ri_calc F G (𝟭 _) _ _ n).2.2.2.1 H

theorem global_of (h : Local l) (d j : ℕ) : ∃ N : ℕ, ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l)
    (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), n ≠ 0 → (k = false ∨ ρ = 0) → F.Atlas d →
    RI ((Polynomial.X : Polynomial ℤ) ^ N) j (flt F κ ε k n ρ hρ).rees (gT F κ k n) := by
  choose N hN using fun d' => h d' (j + 1)
  refine ⟨((Finset.range (d + 1)).sup N) * (2 * j + 3), fun {O} _ F κ ε k n ρ hρ hn hk 𝒜 => ?_⟩
  rw [pow_mul]
  have hp : (bs l k n).p ≠ 0 := (Fact.out : l.Prime).ne_zero
  have z₁ := fun r => P.thick_zar F (bs l k n) rfl (κb κ k n) ((base l).cris n) 𝒜 hp r
  have z₂ := fun r => P.el_zar F κ 𝒜 k n r
  have onto : ∀ {C : Type 1} [Category.{0} C] (Q : C → Prop), Onto (ObjectProperty.ι Q) Q := fun Q =>
    ⟨inferInstance, inferInstance, fun T => T.property, fun T hT => ⟨⟨T, hT⟩, ⟨Iso.refl _⟩⟩⟩
  refine P.glob _ (gT F κ k n) (fun α T => (𝒜.V α).In T.y.1.2) _ j ?_ ?_ ?_ fun S hS => ?_
  · intro α T T' φ hT
    have e : F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) T.y.1.2 = T'.y.1.2 :=
      congrArg (fun z => z.1.2) φ.pt
    exact e ▸ (𝒜.V α).in_map _ hT
  · exact (P.rees_up (flt F κ ε k n ρ hρ) _ j).1 fun r => P.zar _ _ _ (onto _) (z₁ (ρ r)) j
  · exact (P.rees_up ((flt F κ ε k n ρ hρ).comap (gT F κ k n)) _ j).1 fun r => P.zar _ _ _ (onto _) (z₂ (ρ r)) j
  · obtain ⟨d', hd', ⟨s⟩⟩ := 𝒜.small S hS
    refine ⟨_, _, _, _, subThick (Fn.Sub.inter 𝒜.V S) (bs l k n) rfl (κb κ k n), subEl κ (Fn.Sub.inter 𝒜.V S),
      gT (Fn.Sub.inter 𝒜.V S).fn κ k n, P.thick_onto _ _ _ _, P.el_onto F κ 𝒜 S k n hn, ⟨eqToIso (subEl_gT κ _ k n)⟩, ?_⟩
    rw [subThick_rees]
    exact ri_pow (Finset.le_sup (f := N) (Finset.mem_range.2 (Nat.lt_succ_of_le hd'))) (hN d' _ κ ε k n ρ hρ hn hk s)

theorem pull_factor {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R}
    {F' : C' ⥤ ModuleCat.{0} R} (m : Mor F F' (RingHom.id R)) (h : ∀ T, Function.Bijective (m.τ T)) (j : ℕ) :
    ∃ e : H (m.G ⋙ F) j →ₗ[R] H F' j, Function.Bijective e ∧ ∀ x, m.pull j x = e ((Mor.restrict F m.G).pull j x) := by
  let m' : Mor (m.G ⋙ F) F' (RingHom.id R) := ⟨𝟭 _, m.τ, m.nat⟩
  have : m'.G.IsLeftAdjoint := inferInstanceAs (𝟭 C').IsLeftAdjoint
  exact ⟨m'.pull j, CrystallineSemistableComparison.P.adj_mor m' h j, fun x => (CrystallineSemistableComparison.P.pull_comp (Mor.restrict F m.G) m' j x).1⟩

theorem transfer {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R}
    {F' : C' ⥤ ModuleCat.{0} R} (m : Mor F F' (RingHom.id R)) (h : ∀ T, Function.Bijective (m.τ T)) (j : ℕ) (s : R)
    (S : Submodule R (H F j)) (H₁ : InjUpTo s ((Mor.restrict F m.G).pull j))
    (H₂ : ∀ y, ∃ x ∈ S, (Mor.restrict F m.G).pull j x = s • y) :
    UpTo s (m.pull j) ∧ ∀ y, ∃ x ∈ S, m.pull j x = s • y := by
  obtain ⟨e, he, hm⟩ := pull_factor m h j
  have h2 : ∀ y, ∃ x ∈ S, m.pull j x = s • y := fun y => by
    obtain ⟨y', rfl⟩ := he.2 y
    obtain ⟨x, hx, e'⟩ := H₂ y'
    exact ⟨x, hx, by rw [hm, e', map_smul]⟩
  refine ⟨⟨fun x hx => H₁ x (he.1 ?_), fun y => (h2 y).imp fun _ hx => hx.2⟩, h2⟩
  rw [← hm, hx, map_zero]

theorem subsingleton_H {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    (h : ∀ T, Subsingleton (F.obj T)) (j : ℕ) : Subsingleton (H F j) := by
  have : Subsingleton (Cn F j) := ⟨fun _ _ => funext fun _ => (h _).elim _ _⟩
  exact Submodule.Quotient.mk_surjective _ |>.subsingleton

theorem acr_zero (A : PAlg l) : Subsingleton (A.Acr 0) := subsingleton_of_zero_eq_one (by simpa using (A.pow_l_acr 0).symm)

theorem upTo_zero {R M N : Type _} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (h₁ : Subsingleton M)
    (h₂ : Subsingleton N) (f : M →ₗ[R] N) (s : R) (S : Submodule R M) : UpTo s f ∧ ∀ y, ∃ x ∈ S, f x = s • y :=
  ⟨⟨fun _ _ => h₁.elim _ _, fun _ => ⟨0, h₂.elim _ _⟩⟩, fun _ => ⟨0, zero_mem _, h₂.elim _ _⟩⟩

theorem om_zero {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (h : Subsingleton b.R) (j : ℕ) :
    Subsingleton (H (OM L c) j) :=
  subsingleton_H _ (fun T => (show Subsingleton T.B from T.i.codomain_trivial)) j

theorem pdFlt_zero {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (ρ : ℕ → ℕ) (hρ : Slow ρ) (μ : Λ)
    (hμ : c μ ∈ b.I) (T : Thick L) : ((pdFlt L c ρ hρ μ hμ).S 0).S T = ⊤ := eq_top_iff.2 fun x _ => by
  change (show T.B from x) ∈ T.pdPow (ρ 0)
  rw [hρ.1, T.pdPow_zero]; trivial

theorem level_zero {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (j : ℕ) (s : Acris l)
    (S : Submodule (Acris l) (Hc F κ k 0 j)) : UpTo s (β F κ k 0 j) ∧ ∀ y, ∃ x ∈ S, β F κ k 0 j x = s • y :=
  upTo_zero (om_zero (Lc F κ k 0) ((base l).cris 0) (acr_zero (base l)) j)
    (subsingleton_H (modF (AcrEl (F.pt κ) 0)) (fun T => acr_zero T.1.obj) j) (β F κ k 0 j) s S

theorem level_pos {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n j N : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)
    (h : RI ((Polynomial.X : Polynomial ℤ) ^ N) j (flt F κ ε k n ρ hρ).rees (gT F κ k n)) :
    UpTo (ε.μ ^ N) (β F κ k n j) ∧ ∀ y, ∃ x ∈ HcFil F κ k n (ρ N) j, β F κ k n j x = ε.μ ^ N • y :=
  have H := P.rees_down (flt F κ ε k n ρ hρ) (gT F κ k n) j N (pdFlt_zero _ _ ρ hρ _ _) h j le_rfl
  transfer (βMor F κ k n) (fun _ => Function.bijective_id) j (ε.μ ^ N) (HcFil F κ k n (ρ N) j) H.1 H.2

theorem slow_zero : Slow 0 := ⟨rfl, fun _ => Nat.zero_le _⟩

theorem slow_id : Slow id := ⟨rfl, fun _ => le_rfl⟩

theorem level_all {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n j N : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)
    (h : n ≠ 0 → RI ((Polynomial.X : Polynomial ℤ) ^ N) j (flt F κ ε k n ρ hρ).rees (gT F κ k n)) :
    UpTo (ε.μ ^ N) (β F κ k n j) ∧ ∀ y, ∃ x ∈ HcFil F κ k n (ρ N) j, β F κ k n j x = ε.μ ^ N • y :=
  match n, h with
  | 0, _ => level_zero F κ k j _ _
  | n + 1, h => level_pos F κ ε k (n + 1) j N ρ hρ (h n.succ_ne_zero)

theorem main_of (hD : D.Out l) : Main l := fun d j =>
  (global_of (local_of hD) d j).imp fun N hN {_} _ F κ ε 𝒜 n =>
    ⟨fun k => (level_all F κ ε k n j N 0 slow_zero fun hn => hN F κ ε k n 0 slow_zero hn (Or.inr rfl) 𝒜).1,
      (level_all F κ ε false n j N id slow_id fun hn => hN F κ ε false n id slow_id hn (Or.inl rfl) 𝒜).2⟩

end CrystallineSemistableComparison.B
