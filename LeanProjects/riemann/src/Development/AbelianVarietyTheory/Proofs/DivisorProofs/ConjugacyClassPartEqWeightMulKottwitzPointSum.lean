import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetEqFinsumOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixLineConjIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPositivityInvariant
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxUnfoldGen

open GlobalTheory.CxUnfold

section Abstract

variable {Γ : Type} [Group Γ]

theorem card_stabilizer_smul_inf {X : Type} [MulAction Γ X] (Z : Subgroup Γ) {ζ : Γ} (hζ : ζ ∈ Z) (a : X) :
    Nat.card (MulAction.stabilizer Γ (ζ • a) ⊓ Z : Subgroup Γ) = Nat.card (MulAction.stabilizer Γ a ⊓ Z : Subgroup Γ) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨ζ⁻¹ * g.1 * ζ, ?_⟩
      invFun := fun g => ⟨ζ * g.1 * ζ⁻¹, ?_⟩
      left_inv := fun g => by ext; simp [mul_assoc]
      right_inv := fun g => by ext; simp [mul_assoc] }
  · obtain ⟨g, hg⟩ := g
    rw [Subgroup.mem_inf] at hg
    have hg1 : g • ζ • a = ζ • a := hg.1
    refine Subgroup.mem_inf.2 ⟨?_, Z.mul_mem (Z.mul_mem (Z.inv_mem hζ) hg.2) hζ⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hg1, inv_smul_smul]
  · obtain ⟨g, hg⟩ := g
    rw [Subgroup.mem_inf] at hg
    have hg1 : g • a = a := hg.1
    refine Subgroup.mem_inf.2 ⟨?_, Z.mul_mem (Z.mul_mem hζ hg.2) (Z.inv_mem hζ)⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, hg1]

theorem finsum_orbit_prod_line {U P : Type} [MulAction Γ U] [MulAction Γ P] (Z : Subgroup Γ) (l₀ : P)
    (hl₀ : ∀ ζ ∈ Z, ζ • l₀ = l₀) (F : U × P → ℂ) (c : U → ℂ) (hF0 : ∀ u l, l ≠ l₀ → F (u, l) = 0)
    (hF1 : ∀ u, F (u, l₀) = c u) (hc : ∀ ζ ∈ Z, ∀ u, c (ζ • u) = c u) :
    ∑ᶠ o : MulAction.orbitRel.Quotient Z (U × P),
        ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Z : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) =
      ∑ᶠ o : MulAction.orbitRel.Quotient Z U,
        ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Z : Subgroup Γ) : ℕ) : ℂ)⁻¹ * c (Quotient.out o) := by
  set S : U × P → ℂ := fun a => ((Nat.card (MulAction.stabilizer Γ a ⊓ Z : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F a with hS

  have hstab : ∀ u, (MulAction.stabilizer Γ ((u, l₀) : U × P) ⊓ Z : Subgroup Γ) = MulAction.stabilizer Γ u ⊓ Z := by
    intro u; ext g
    simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Prod.smul_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hl₀ g h2⟩, h2⟩

  have hSinv : ∀ ζ ∈ Z, ∀ a, S (ζ • a) = S a := by
    intro ζ hζ a
    simp only [hS]
    rw [card_stabilizer_smul_inf Z hζ a]
    congr 1
    obtain ⟨u, l⟩ := a
    rw [Prod.smul_mk]
    by_cases hl : l = l₀
    · subst hl; rw [hl₀ ζ hζ, hF1, hF1, hc ζ hζ]
    · have hl' : ζ • l ≠ l₀ := by
        intro h; apply hl
        have := congrArg (fun m => ζ⁻¹ • m) h
        simpa [hl₀ ζ⁻¹ (Z.inv_mem hζ)] using this
      rw [hF0 _ _ hl, hF0 _ _ hl']

  let φ : MulAction.orbitRel.Quotient Z U → MulAction.orbitRel.Quotient Z (U × P) :=
    Quotient.map' (fun u => (u, l₀)) (by
      rintro u u' ⟨ζ, rfl⟩
      refine ⟨ζ, ?_⟩
      show ((ζ : Γ) • u', (ζ : Γ) • l₀) = ((ζ : Γ) • u', l₀)
      rw [hl₀ _ ζ.2])
  have hφ : Function.Injective φ := by
    intro q q' h
    induction q using Quotient.inductionOn' with | h u => ?_
    induction q' using Quotient.inductionOn' with | h u' => ?_
    have h' := Quotient.exact' h
    obtain ⟨ζ, hζ⟩ := h'
    apply Quotient.sound'
    refine ⟨ζ, ?_⟩
    exact congrArg Prod.fst hζ

  have hsupp : Function.support (fun o : MulAction.orbitRel.Quotient Z (U × P) => S (Quotient.out o)) ⊆ Set.range φ := by
    intro o ho
    have hne : F (Quotient.out o) ≠ 0 := by
      intro h0; apply ho; simp [hS, h0]
    have hl : (Quotient.out o).2 = l₀ := by
      by_contra hl
      exact hne (by rw [← Prod.mk.eta (p := Quotient.out o)]; exact hF0 _ _ hl)
    refine ⟨Quotient.mk'' (Quotient.out o).1, ?_⟩
    show Quotient.mk'' ((Quotient.out o).1, l₀) = o
    rw [← hl, Prod.mk.eta]
    exact Quotient.out_eq' o
  have hval : ∀ q : MulAction.orbitRel.Quotient Z U, S (Quotient.out (φ q)) =
      ((Nat.card (MulAction.stabilizer Γ (Quotient.out q) ⊓ Z : Subgroup Γ) : ℕ) : ℂ)⁻¹ * c (Quotient.out q) := by
    intro q
    have h1 : (Quotient.mk'' (Quotient.out (φ q)) : MulAction.orbitRel.Quotient Z (U × P)) =
        Quotient.mk'' (Quotient.out q, l₀) := by
      rw [Quotient.out_eq']
      conv_lhs => rw [← Quotient.out_eq' q]
      rfl
    obtain ⟨ζ, hζ⟩ := Quotient.exact' h1
    rw [← hζ]
    change S ((ζ : Γ) • _) = _
    rw [hSinv _ ζ.2]
    simp only [hS]
    rw [hstab, hF1]
  calc ∑ᶠ o : MulAction.orbitRel.Quotient Z (U × P), S (Quotient.out o)
      = ∑ᶠ o ∈ Set.range φ, S (Quotient.out o) := by
        rw [← finsum_mem_inter_support, Set.inter_eq_right.2 hsupp, finsum_mem_support]
    _ = ∑ᶠ q, S (Quotient.out (φ q)) := finsum_mem_range hφ
    _ = _ := finsum_congr hval

end Abstract

end GlobalTheory.CxUnfoldGen

noncomputable section

namespace GlobalTheory.CxUnfoldGen

open GlobalTheory.CxUnfold

section Point

variable {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂]

def cosetVal (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂)
    (f₁ : G₁ → ℂ) (φ : G₂ → ℂ) (u : LeftCosets (ι₁.prod ι₂) (K₁.prod K₂)) : ℂ :=
  f₁ ((LeftCosets.rep _ _ u).1⁻¹ * γ * (LeftCosets.rep _ _ u).1) *
    φ ((LeftCosets.rep _ _ u).2⁻¹ * δ * (LeftCosets.rep _ _ u).2)

variable (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) {K₁ : Subgroup G₁} {K₂ : Subgroup G₂} (γ : G₁) (δ : G₂)
  {f₁ : G₁ → ℂ} {φ : G₂ → ℂ}

theorem cosetVal_mk (hf₁ : ∀ k ∈ K₁, ∀ g, f₁ (k⁻¹ * g * k) = f₁ g) (hφ : ∀ k ∈ K₂, ∀ g, φ (k⁻¹ * g * k) = φ g)
    (x : G₁ × G₂) :
    cosetVal ι₁ ι₂ K₁ K₂ γ δ f₁ φ (LeftCosets.mk _ _ x) = f₁ (x.1⁻¹ * γ * x.1) * φ (x.2⁻¹ * δ * x.2) := by
  obtain ⟨k, hk, e⟩ := LeftCosets.rep_mk (ι := ι₁.prod ι₂) (K := K₁.prod K₂) x
  rw [Subgroup.mem_prod] at hk
  rw [cosetVal, e]
  have e1 : (x * k).1⁻¹ * γ * (x * k).1 = k.1⁻¹ * (x.1⁻¹ * γ * x.1) * k.1 := by
    simp only [Prod.fst_mul]; group
  have e2 : (x * k).2⁻¹ * δ * (x * k).2 = k.2⁻¹ * (x.2⁻¹ * δ * x.2) * k.2 := by
    simp only [Prod.snd_mul]; group
  rw [e1, e2, hf₁ _ hk.1, hφ _ hk.2]

theorem cosetVal_smul (hf₁ : ∀ k ∈ K₁, ∀ g, f₁ (k⁻¹ * g * k) = f₁ g) (hφ : ∀ k ∈ K₂, ∀ g, φ (k⁻¹ * g * k) = φ g)
    (η : Γ) (h₁ : ι₁ η * γ = γ * ι₁ η) (h₂ : ι₂ η * δ = δ * ι₂ η) (u : LeftCosets (ι₁.prod ι₂) (K₁.prod K₂)) :
    cosetVal ι₁ ι₂ K₁ K₂ γ δ f₁ φ (η • u) = cosetVal ι₁ ι₂ K₁ K₂ γ δ f₁ φ u := by
  conv_lhs => rw [← LeftCosets.mk_rep u, LeftCosets.smul_mk]
  conv_rhs => rw [← LeftCosets.mk_rep u]
  rw [cosetVal_mk ι₁ ι₂ γ δ hf₁ hφ, cosetVal_mk ι₁ ι₂ γ δ hf₁ hφ]
  simp only [Prod.fst_mul, Prod.snd_mul, MonoidHom.prod_apply]
  have e1 : (ι₁ η * (LeftCosets.rep _ _ u).1)⁻¹ * γ * (ι₁ η * (LeftCosets.rep _ _ u).1) =
      (LeftCosets.rep _ _ u).1⁻¹ * γ * (LeftCosets.rep _ _ u).1 := by
    have h : (ι₁ η)⁻¹ * γ * ι₁ η = γ := by rw [mul_assoc, ← h₁, ← mul_assoc, inv_mul_cancel, one_mul]
    calc _ = (LeftCosets.rep _ _ u).1⁻¹ * ((ι₁ η)⁻¹ * γ * ι₁ η) * (LeftCosets.rep _ _ u).1 := by group
      _ = _ := by rw [h]
  have e2 : (ι₂ η * (LeftCosets.rep _ _ u).2)⁻¹ * δ * (ι₂ η * (LeftCosets.rep _ _ u).2) =
      (LeftCosets.rep _ _ u).2⁻¹ * δ * (LeftCosets.rep _ _ u).2 := by
    have h : (ι₂ η)⁻¹ * δ * ι₂ η = δ := by rw [mul_assoc, ← h₂, ← mul_assoc, inv_mul_cancel, one_mul]
    calc _ = (LeftCosets.rep _ _ u).2⁻¹ * ((ι₂ η)⁻¹ * δ * ι₂ η) * (LeftCosets.rep _ _ u).2 := by group
      _ = _ := by rw [h]
  rw [e1, e2]

theorem pointSum_centralizer_eq (hf₁ : ∀ k ∈ K₁, ∀ g, f₁ (k⁻¹ * g * k) = f₁ g)
    (hφ : ∀ k ∈ K₂, ∀ g, φ (k⁻¹ * g * k) = φ g) (y₀ : Γ) :
    pointSum (ι₁.comp (Subgroup.centralizer {y₀}).subtype) (ι₂.comp (Subgroup.centralizer {y₀}).subtype)
        (MonoidHom.id G₂) K₁ K₂ (ι₁ y₀) (ι₂ y₀) f₁ φ =
      ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {y₀}) (LeftCosets (ι₁.prod ι₂) (K₁.prod K₂)),
        ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {y₀} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
          cosetVal ι₁ ι₂ K₁ K₂ (ι₁ y₀) (ι₂ y₀) f₁ φ (Quotient.out o) := by
  set Z := Subgroup.centralizer {y₀} with hZ
  have hcomm : ∀ η ∈ Z, η * y₀ = y₀ * η := by
    intro η hη
    exact ((Subgroup.mem_centralizer_iff.1 hη) y₀ (Set.mem_singleton _)).symm
  set g : LeftCosets (ι₁.prod ι₂) (K₁.prod K₂) → ℂ := fun u =>
    ((Nat.card (MulAction.stabilizer Γ u ⊓ Z : Subgroup Γ) : ℕ) : ℂ)⁻¹ * cosetVal ι₁ ι₂ K₁ K₂ (ι₁ y₀) (ι₂ y₀) f₁ φ u
    with hg
  have hginv : ∀ η ∈ Z, ∀ u, g (η • u) = g u := by
    intro η hη u
    simp only [hg]
    rw [card_stabilizer_smul_inf Z hη u,
      cosetVal_smul ι₁ ι₂ _ _ hf₁ hφ η (by rw [← map_mul, ← map_mul, hcomm η hη]) (by rw [← map_mul, ← map_mul, hcomm η hη])]
  have hr : (((ι₁.comp Z.subtype).prod (ι₂.comp Z.subtype)).range : Set (G₁ × G₂)) =
      ((Z.map (ι₁.prod ι₂) : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.prod_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype, Subtype.exists, exists_prop]
  have hcard : ∀ x : G₁ × G₂, Nat.card (stab (ι₁.comp Z.subtype) (ι₂.comp Z.subtype) K₁ K₂ x) =
      Nat.card (MulAction.stabilizer Γ (LeftCosets.mk (ι₁.prod ι₂) (K₁.prod K₂) x) ⊓ Z : Subgroup Γ) := by
    intro x
    rw [← stab_eq_stabilizer ι₁ ι₂]
    exact Nat.card_congr
      { toFun := fun η => ⟨η.1.1, Subgroup.mem_inf.2 ⟨η.2, η.1.2⟩⟩
        invFun := fun η => ⟨⟨η.1, (Subgroup.mem_inf.1 η.2).2⟩, (Subgroup.mem_inf.1 η.2).1⟩
        left_inv := fun η => rfl
        right_inv := fun η => rfl }
  unfold pointSum
  rw [hr, ← GlobalTheory.LKCount.finsum_doubleCoset_eq_finsum_orbit (ι₁.prod ι₂) Z (K₁.prod K₂) g hginv]
  refine finsum_congr fun q => ?_
  simp only [hg]
  rw [cosetVal_mk ι₁ ι₂ _ _ hf₁ hφ, hcard]
  rfl

end Point

end GlobalTheory.CxUnfoldGen

noncomputable section

namespace GlobalTheory.CxUnfoldGen

open GlobalTheory.CxUnfold

theorem finsum_mul_const_complex {α : Type} (g : α → ℂ) (w : ℂ) : ∑ᶠ i, g i * w = (∑ᶠ i, g i) * w := by
  exact (finsum_mul _ _).symm

theorem cls_eq_of_uniq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y₀ : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0 → ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re → FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z) → ∀ y₀ : grp G β, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {y₀}) (GlobalTheory.CxUnfold.Ys G v β x t hx Kf K'), ((Nat.card (MulAction.stabilizer (grp G β) (Quotient.out o) ⊓ Subgroup.centralizer {y₀} : Subgroup (grp G β)) : ℕ) : ℂ)⁻¹ * GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y₀ = if (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y₀ z) then wt (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * pointSum ((toAfF G β x t hx).comp (Subgroup.centralizer {y₀}).subtype) ((toP1 G β).comp (Subgroup.centralizer {y₀}).subtype) (MonoidHom.id (Gr G 1)) Kf K' (toAfF G β x t hx y₀) (toP1 G β y₀) f f' else 0 := by
  intro p _ G v wt Kf f hf₁ K' f' hφ β x t hx huniq' y₀
  set Z := Subgroup.centralizer {y₀} with hZ
  have hcomm : ∀ η ∈ Z, η * y₀ = y₀ * η := by
    intro η hη
    exact ((Subgroup.mem_centralizer_iff.1 hη) y₀ (Set.mem_singleton _)).symm
  by_cases hpos : ∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y₀ z
  swap
  · rw [if_neg hpos]
    refine finsum_eq_zero_of_forall_eq_zero fun o => ?_
    rw [cxF, if_neg (fun h => hpos ⟨_, h⟩), mul_zero]
  rw [if_pos hpos]
  obtain ⟨z₀, hz₀pos, hz₀fix⟩ := hpos
  by_cases hf0 : ∃ h, f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0
  swap
  · push_neg at hf0
    have hl : ∀ o : MulAction.orbitRel.Quotient Z (Ys G v β x t hx Kf K'),
        cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y₀ = 0 := by
      intro o
      rw [cxF]
      split_ifs
      · rw [hf0, zero_mul, zero_mul]
      · rfl
    simp only [hl, mul_zero, finsum_zero, pointSum, hf0, zero_mul]
  obtain ⟨h₀, hh₀⟩ := hf0
  have huniq : ∀ z', 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z₀ :=
    fun z' hp hfx => huniq' y₀ h₀ hh₀ z₀ z' hz₀pos hp hz₀fix hfx
  have hz₀ne : z₀ ≠ 0 := by
    rintro rfl; simp at hz₀pos
  let l₀ : PLv G v β := Projectivization.mk ℂ z₀ hz₀ne

  have hl₀ : ∀ ζ ∈ Z, ζ • l₀ = l₀ := by
    intro ζ hζ
    change Projectivization.map _ _ (Projectivization.mk ℂ z₀ hz₀ne) = Projectivization.mk ℂ z₀ hz₀ne
    rw [Projectivization.map_mk]
    have hp := (GlobalTheory.LKCx.pos_iff_smul_toV p G v β ζ z₀ 1 one_ne_zero).1 hz₀pos
    rw [one_smul] at hp
    have hfx := (GlobalTheory.LKCx.fixL_conj_iff p G v β y₀ ζ z₀).1 hz₀fix
    rw [hcomm ζ hζ, mul_inv_cancel_right] at hfx
    obtain ⟨c, hc⟩ := huniq _ hp hfx
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨c, by rw [Matrix.toLin'_apply]; exact hc.symm⟩

  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ (Projectivization.rep_nonzero (l₀ : Projectivization ℂ (Fin G.n → ℂ))) hz₀ne).1
    (Projectivization.mk_rep (l₀ : Projectivization ℂ (Fin G.n → ℂ)))
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact Projectivization.rep_nonzero (l₀ : Projectivization ℂ (Fin G.n → ℂ)) (by rw [← ha, zero_smul])
  set F : Ys G v β x t hx Kf K' → ℂ := fun b => cxF G v wt β x t hx Kf f K' f' b y₀ with hF
  set c : LeftCosets ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') → ℂ := fun u =>
    cosetVal (toAfF G β x t hx) (toP1 G β) Kf K' (toAfF G β x t hx y₀) (toP1 G β y₀) f f' u *
      wt (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) with hc
  have hF0 : ∀ u l, l ≠ l₀ → F (u, l) = 0 := by
    intro u l hl
    simp only [hF]
    rw [cxF, if_neg]
    rintro ⟨hp, hfx⟩
    obtain ⟨d, hd⟩ := huniq _ hp hfx
    apply hl
    exact (Projectivization.mk_rep (l : Projectivization ℂ (Fin G.n → ℂ))).symm.trans
      ((Projectivization.mk_eq_mk_iff' ℂ _ _ (Projectivization.rep_nonzero _) hz₀ne).2 ⟨d, hd.symm⟩)
  have hF1 : ∀ u, F (u, l₀) = c u := by
    intro u
    simp only [hF, hc]
    rw [cxF, if_pos]
    · rfl
    refine ⟨?_, ?_⟩
    · have hp := (GlobalTheory.LKCx.pos_iff_smul_toV p G v β 1 z₀ a ha0).1 hz₀pos
      have e : ((toV G v β 1 : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z₀ = z₀ := by simp
      rw [e, ha] at hp
      exact hp
    · obtain ⟨d, hd⟩ := hz₀fix
      refine ⟨d, ?_⟩
      rw [← ha, Matrix.mulVec_smul, hd, smul_comm]
  have hcinv : ∀ ζ ∈ Z, ∀ u, c (ζ • u) = c u := by
    intro ζ hζ u
    simp only [hc]
    rw [cosetVal_smul (toAfF G β x t hx) (toP1 G β) _ _ hf₁ hφ ζ
      (by rw [← map_mul, ← map_mul, hcomm ζ hζ]) (by rw [← map_mul, ← map_mul, hcomm ζ hζ])]
  refine (finsum_orbit_prod_line Z l₀ hl₀ F c hF0 hF1 hcinv).trans ?_
  rw [pointSum_centralizer_eq (toAfF G β x t hx) (toP1 G β) hf₁ hφ y₀, mul_comm, ← finsum_mul_const_complex]
  refine finsum_congr fun o => ?_
  simp only [hc]
  ring

end GlobalTheory.CxUnfoldGen
