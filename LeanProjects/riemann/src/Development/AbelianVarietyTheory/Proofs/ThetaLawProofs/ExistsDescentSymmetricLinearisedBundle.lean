import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced

noncomputable section

namespace GlobalTheory.LinDescent

open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Sym

variable {X Y : Scheme.{0}} {L : LB X} {C : Type} {t : C → (X ⟶ X)} {π : X ⟶ Y}

def Compat (u : ∀ c, LB.Gen (twist L (t c))) {M : LB Y} (w : LB.Iso L (M.pull π)) : Prop :=
  ∀ c (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) y i k, π (r z) ∈ M.U y → r z ∈ L.U i →
    (r ≫ t c) z ∈ L.U k → gw w (r ≫ t c) z y k = uv (u c) r z i k * gw w r z y i

theorem exists_descent_compat_of_invGen [Flat π] [Surjective π] [QuasiCompact π] (hL : L.IsLB)
    (hπ : ∀ c, t c ≫ π = π) (h : LocTransitive t π) {u : ∀ c, LB.Gen (twist L (t c))}
    (V : Y → Y.Opens) (hV : ∀ y, y ∈ V y) (e : ∀ y i, Γ(X, π ⁻¹ᵁ V y ⊓ L.U i)ˣ)
    (he : ∀ y, IsInvGen u (π ⁻¹ᵁ V y) (e y)) :
    ∃ M : LB Y, M.IsLB ∧ ∃ w : LB.Iso L (M.pull π), w.IsGen ∧ Compat u w := by
  have hmem : ∀ (U : Y.Opens) c {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ U →
      (r ≫ t c) z ∈ π ⁻¹ᵁ U := fun U c Z r z hz => by
    change ((r ≫ t c) ≫ π) z ∈ U
    rw [Category.assoc, hπ]
    exact hz
  have H : ∀ y y', ∃ g : Γ(Y, V y ⊓ V y')ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i,
      r z ∈ π ⁻¹ᵁ V y → r z ∈ π ⁻¹ᵁ V y' → r z ∈ L.U i →
      gm (r ≫ π) z _ g = gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹ := fun y y' => by
    let O : L.ι → X.Opens := fun i => π ⁻¹ᵁ (V y ⊓ V y') ⊓ L.U i
    have l : ∀ i, O i ≤ π ⁻¹ᵁ V y ⊓ L.U i := fun i x hx => ⟨hx.1.1, hx.2⟩
    have l' : ∀ i, O i ≤ π ⁻¹ᵁ V y' ⊓ L.U i := fun i x hx => ⟨hx.1.2, hx.2⟩
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ O i →
        gs r z (O i) (res (l' i) (e y' i) * (res (l i) (e y i))⁻¹).val =
        (gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹).val := fun Z r z i hz => by
      rw [gs_unit r z _ hz, map_mul, map_inv, gm_res r z _ hz, gm_res r z _ hz]
    obtain ⟨ρ, hρ⟩ := glue_fn (π ⁻¹ᵁ (V y ⊓ V y')) O (fun _ => inf_le_left)
      (fun x hx => (exists_chart hL x).imp fun i hi => ⟨hx, hi⟩)
      (fun i => (res (l' i) (e y' i) * (res (l i) (e y i))⁻¹).val) (fun i j x hi hj => by
        rw [v _ (𝟙 X) x i hi, v _ (𝟙 X) x j hj, (he y).1 _ (𝟙 X) x i j hi.1.1 hi.2 hj.2,
          (he y').1 _ (𝟙 X) x i j hi.1.2 hi.2 hj.2, ← div_eq_mul_inv, mul_div_mul_left_eq_div,
          div_eq_mul_inv])
    have hρ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ π ⁻¹ᵁ (V y ⊓ V y') →
        r z ∈ L.U i → gs r z _ ρ = (gm r z _ (e y' i) * (gm r z _ (e y i))⁻¹).val :=
      fun Z r z i h1 h2 => (hρ Z r z i ⟨h1, h2⟩).trans (v Z r z i ⟨h1, h2⟩)
    obtain ⟨a, ha⟩ := h.exists_descend (V y ⊓ V y') ρ fun c Z r z hz => by
      obtain ⟨i, hi⟩ := exists_chart hL (r z)
      obtain ⟨k, hk⟩ := exists_chart hL ((r ≫ t c) z)
      rw [hρ' Z r z i hz hi, hρ' Z (r ≫ t c) z k (hmem _ c r z hz) hk,
        (he y).2 c Z r z i k hz.1 hi hk, (he y').2 c Z r z i k hz.2 hi hk,
        ← div_eq_mul_inv (_ * _), mul_div_mul_left_eq_div, div_eq_mul_inv]
    have hu : IsUnit a := isUnit_of_mem_basicOpen a fun b hb => by
      obtain ⟨x, rfl⟩ := π.surjective b
      obtain ⟨i, hi⟩ := exists_chart hL x
      refine (isUnit_gs_iff (𝟙 X ≫ π) x (V y ⊓ V y') hb a).1 ?_
      rw [ha _ (𝟙 X) x hb, hρ' _ (𝟙 X) x i hb hi]
      exact Units.isUnit _
    refine ⟨hu.unit, fun Z r z i h1 h2 hi => Units.ext ?_⟩
    exact (gs_unit (r ≫ π) z (V y ⊓ V y') ⟨h1, h2⟩ hu.unit).symm.trans
      ((ha Z r z ⟨h1, h2⟩).trans (hρ' Z r z i ⟨h1, h2⟩ hi))
  choose g hg using H
  let M : LB Y := ⟨Y, V, g⟩
  refine ⟨M, ⟨eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hV y⟩, fun y => ?_,
    fun y₁ y₂ y₃ => ?_⟩, ?_⟩
  · refine unit_ext_of_flat (π := π) fun x hx => ?_
    obtain ⟨i, hi⟩ := exists_chart hL x
    refine (gm_res (𝟙 X ≫ π) x _ hx _).trans ((hg y y _ (𝟙 X) x i hx hx hi).trans ?_)
    rw [mul_inv_cancel, map_one]
  · refine unit_ext_of_flat (π := π) fun x hx => ?_
    obtain ⟨i, hi⟩ := exists_chart hL x
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res (𝟙 X ≫ π) x _ hx _).trans (hg y₁ y₂ _ (𝟙 X) x i hx.1.1 hx.1.2 hi))
      ((gm_res (𝟙 X ≫ π) x _ hx _).trans (hg y₂ y₃ _ (𝟙 X) x i hx.1.2 hx.2 hi)))).trans
      (Eq.trans ?_ ((gm_res (𝟙 X ≫ π) x _ hx _).trans
        (hg y₁ y₃ _ (𝟙 X) x i hx.1.1 hx.2 hi)).symm)
    rw [mul_comm, mul_assoc, inv_mul_cancel_left]
  · have l : ∀ p : (PUnit → Y) × L.ι, (M.pull π).U p.1 ⊓ L.U p.2 ≤
        π ⁻¹ᵁ V (p.1 PUnit.unit) ⊓ L.U p.2 := fun p x hx => ⟨mem_pull.1 hx.1, hx.2⟩
    let w : LB.Iso L (M.pull π) := ⟨fun p => (res (l p) (e (p.1 PUnit.unit) p.2))⁻¹⟩
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (y : Y) i, π (r z) ∈ V y → r z ∈ L.U i →
        gw w r z y i = (gm r z _ (e y i))⁻¹ := fun Z r z y i h1 h2 =>
      (map_inv _ _).trans (congrArg _ (gm_res r z (l (fun _ => y, i))
        ⟨(mem_pull (L := M)).2 h1, h2⟩ _))
    refine ⟨w, (isGen_iff w).2 fun Z r z y y' i i' h1 h2 h3 h4 => ?_,
      fun c Z r z y i k h1 h2 h3 => ?_⟩
    swap
    · rw [v Z r z y i h1 h2, v Z (r ≫ t c) z y k (hmem _ c r z h1) h3,
        (he y).2 c Z r z i k h1 h2 h3, mul_inv, mul_inv_cancel_left]
    rw [v Z r z y i h1 h3, v Z r z y' i' h2 h4]
    refine Eq.trans ?_ (congrArg (· * _ * _) (hg y y' Z r z i' h1 h2 h4)).symm
    rw [(he y).1 Z r z i i' h1 h3 h4]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem exists_descent_compat_of_galois [Group C] [Finite C] [IsFinite π] [Flat π] [Surjective π]
    (hL : L.IsLB) (ht1 : t 1 = 𝟙 X) (ht : ∀ c c', t c ≫ t c' = t (c * c'))
    (hπ : ∀ c, t c ≫ π = π) (h : LocTransitive t π)
    (hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      Function.Injective fun c => r ≫ t c)
    {u : ∀ c, LB.Gen (twist L (t c))} (hu : ∀ c, (u c).IsGen)
    (hc : ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
      (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (t c)))) :
    ∃ M : LB Y, M.IsLB ∧ ∃ w : LB.Iso L (M.pull π), w.IsGen ∧ Compat u w := by
  have H : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ e, IsInvGen u (π ⁻¹ᵁ V) e := fun y => by
    obtain ⟨x, rfl⟩ := π.surjective y
    obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hx, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (π x)) isOpen_univ
    have hinv : ∀ (V : Y.Opens) c, π ⁻¹ᵁ V ≤ t c ⁻¹ᵁ π ⁻¹ᵁ V := fun V c => by
      rw [← Scheme.Hom.comp_preimage, hπ]
    obtain ⟨s, h1, h2, i₀, h3⟩ := exists_inv_sec hL ht1 ht hfree hu hc
      (IsAffineOpen.preimage hV₀ π) (hinv V₀) x hx
    let N : X.Opens := ⨆ i, X.basicOpen (s i)
    let V : Y.Opens := ⟨(π '' (N : Set X)ᶜ)ᶜ, (π.isClosedMap _ N.isOpen.isClosed_compl).isOpen_compl⟩
    have hN : ∀ x', x' ∈ π ⁻¹ᵁ V → ∃ i, x' ∈ X.basicOpen (s i) := fun x' hx' => by
      by_contra hh
      exact hx' ⟨x', fun hh' => hh (Opens.mem_iSup.1 hh'), rfl⟩
    have hN' : ∀ x', x' ∈ π ⁻¹ᵁ V → x' ∈ π ⁻¹ᵁ V₀ := fun x' hx' => by
      obtain ⟨i, hi⟩ := hN x' hx'
      exact (X.basicOpen_le _ hi).1
    have l : ∀ i, π ⁻¹ᵁ V ⊓ L.U i ≤ π ⁻¹ᵁ V₀ ⊓ L.U i := fun i x' hx' => ⟨hN' x' hx'.1, hx'.2⟩
    have hu' : ∀ i, IsUnit (rs (l i) (s i)) := fun i => isUnit_of_mem_basicOpen _ fun x' hx' => by
      obtain ⟨j, hj⟩ := hN x' hx'.1
      have hj' := X.basicOpen_le _ hj
      refine (isUnit_gs_iff (𝟙 X) x' _ hx' _).1 ?_
      rw [gs_res (𝟙 X) x' _ hx', h1 _ (𝟙 X) x' i j hj'.1 hx'.2 hj'.2]
      exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 X) x' _ hj' _).2 hj)
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ π ⁻¹ᵁ V → r z ∈ L.U i →
        (gm r z _ (hu' i).unit).val = gs r z _ (s i) := fun Z r z i a b =>
      (gs_unit r z (π ⁻¹ᵁ V ⊓ L.U i) ⟨a, b⟩ _).symm.trans (gs_res r z (l i) ⟨a, b⟩ _)
    refine ⟨V, ?_, fun i => (hu' i).unit, fun Z r z i j a b c => Units.ext ?_,
      fun c Z r z i k a b d => Units.ext ?_⟩
    · rintro ⟨x', hx', e⟩
      obtain ⟨c, rfl⟩ := h.exists_apply_eq e
      obtain ⟨k, hk⟩ := exists_chart hL (t c x)
      have h4 := X.basicOpen_le _ h3
      have h5 := (isUnit_gs_iff (𝟙 X) x _ h4 _).2 h3
      rw [h2 c _ (𝟙 X) x i₀ k hx h4.2 hk] at h5
      exact hx' (Opens.mem_iSup.2 ⟨k, (isUnit_gs_iff (𝟙 X ≫ t c) x (π ⁻¹ᵁ V₀ ⊓ L.U k)
        ⟨hinv V₀ c hx, hk⟩ _).1 (isUnit_of_mul_isUnit_right h5)⟩)
    · rw [Units.val_mul, v Z r z i a b, v Z r z j a c]
      exact h1 Z r z i j (hN' _ a) b c
    · rw [Units.val_mul, v Z r z i a b, v Z (r ≫ t c) z k (hinv V c a) d]
      exact h2 c Z r z i k (hN' _ a) b d
  choose V hV e he using H
  exact exists_descent_compat_of_invGen hL hπ h V hV e he

theorem LocTransitive.exists_descend_unit [Flat π] [Surjective π] [QuasiCompact π]
    (h : LocTransitive t π) (V : Y.Opens) {κ : Type} (O : κ → X.Opens)
    (hO : ∀ k, O k ≤ π ⁻¹ᵁ V) (hc : ∀ x ∈ π ⁻¹ᵁ V, ∃ k, x ∈ O k) (a : ∀ k, Γ(X, O k)ˣ)
    (ha : ∀ k l x, x ∈ O k → x ∈ O l → gm (𝟙 X) x (O k) (a k) = gm (𝟙 X) x (O l) (a l))
    (hi : ∀ c (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ V →
      ∃ k l, r z ∈ O k ∧ (r ≫ t c) z ∈ O l ∧ gm (r ≫ t c) z (O l) (a l) = gm r z (O k) (a k)) :
    ∃ g : Γ(Y, V)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k, r z ∈ O k →
      gm (r ≫ π) z V g = gm r z (O k) (a k) := by
  obtain ⟨ρ, hρ⟩ := glue_fn (π ⁻¹ᵁ V) O hO hc (fun k => (a k).val) (fun k l x hk hl => by
    rw [gs_unit (𝟙 X) x _ hk, gs_unit (𝟙 X) x _ hl, ha k l x hk hl])
  have hρ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k, r z ∈ O k →
      gs r z _ ρ = (gm r z _ (a k)).val := fun Z r z k hk =>
    (hρ Z r z k hk).trans (gs_unit r z _ hk _)
  obtain ⟨b, hb⟩ := h.exists_descend V ρ fun c Z r z hz => by
    obtain ⟨k, l, hk, hl, e⟩ := hi c Z r z hz
    rw [hρ' Z r z k hk, hρ' Z _ z l hl, e]
  have hu : IsUnit b := isUnit_of_mem_basicOpen b fun y hy => by
    obtain ⟨x, rfl⟩ := π.surjective y
    obtain ⟨k, hk⟩ := hc x hy
    refine (isUnit_gs_iff (𝟙 X ≫ π) x V hy b).1 ?_
    rw [hb _ (𝟙 X) x hy, hρ' _ (𝟙 X) x k hk]
    exact Units.isUnit _
  refine ⟨hu.unit, fun Z r z k hk => Units.ext ?_⟩
  exact (gs_unit (r ≫ π) z V (hO k hk) hu.unit).symm.trans
    ((hb Z r z (hO k hk)).trans (hρ' Z r z k hk))

theorem isGen_of_flat [Flat π] [Surjective π] {Y' : Scheme.{0}} {M : LB Y} {N : LB Y'}
    {F : Y ⟶ Y'} (w : LB.Iso M (N.pull F))
    (h : ∀ (x : X) j j' k k', F (π x) ∈ N.U j → F (π x) ∈ N.U j' → π x ∈ M.U k → π x ∈ M.U k' →
      gw w (𝟙 X ≫ π) x j k = gm ((𝟙 X ≫ π) ≫ F) x _ (N.g j j') *
        (gm (𝟙 X ≫ π) x _ (M.g k k'))⁻¹ * gw w (𝟙 X ≫ π) x j' k') : w.IsGen := by
  rintro ⟨J, k⟩ ⟨J', k'⟩
  apply unit_ext_of_flat (π := π)
  intro x hx
  have hj := mem_pull.1 hx.1.1
  have hj' := mem_pull.1 hx.2.1
  have := h x (J PUnit.unit) (J' PUnit.unit) k k' hj hj' hx.1.2 hx.2.2
  rw [← gm_div_g (𝟙 X ≫ π) x _ _ k k' hj hj' hx.1.2 hx.2.2] at this
  exact (gm_res (𝟙 X ≫ π) x _ hx _).trans (this.trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res (𝟙 X ≫ π) x _ hx _))).symm)

theorem descend_iso [Flat π] [Surjective π] [QuasiCompact π] (hL : L.IsLB)
    (hπ : ∀ c, t c ≫ π = π) (h : LocTransitive t π) {u : ∀ c, LB.Gen (twist L (t c))}
    {M : LB Y} {w : LB.Iso L (M.pull π)} (hw : w.IsGen) (hc : Compat u w)
    {ν : X ⟶ X} {ν' : Y ⟶ Y} (hν : ν ≫ π = π ≫ ν') (σ : C → C)
    (hσ : ∀ c, t c ≫ ν = ν ≫ t (σ c)) {j : LB.Gen (twist L ν)} (hj : j.IsGen)
    (huj : ∀ c (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) J, Good L z J →
      val (u c) r z J * val j (r ≫ t c) z J = val j r z J * val (u (σ c)) (r ≫ ν) z J) :
    LBIso M (M.pull ν') := by
  have hw' := (isGen_iff w).1 hw
  have hν₁ : ∀ {Z : Scheme.{0}} (r : Z ⟶ X), (r ≫ ν) ≫ π = (r ≫ π) ≫ ν' := fun r => by
    rw [Category.assoc, Category.assoc, hν]
  have hν₂ : ∀ x, π (ν x) = ν' (π x) := fun x => congrArg (fun q : X ⟶ Y => q x) hν
  have hπ₂ : ∀ c x, π (t c x) = π x := fun c x => congrArg (fun q : X ⟶ Y => q x) (hπ c)
  have tr : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) y₁ y₁' y₂ y₂' i k i' k',
      ν' (π (r z)) ∈ M.U y₁ → ν' (π (r z)) ∈ M.U y₁' → π (r z) ∈ M.U y₂ → π (r z) ∈ M.U y₂' →
      r z ∈ L.U i → ν (r z) ∈ L.U k → r z ∈ L.U i' → ν (r z) ∈ L.U k' →
      gw w (r ≫ ν) z y₁ k * (gw w r z y₂ i)⁻¹ * (uv j r z i k)⁻¹ =
        gg M ((r ≫ π) ≫ ν') z y₁ y₁' * (gg M (r ≫ π) z y₂ y₂')⁻¹ *
        (gw w (r ≫ ν) z y₁' k' * (gw w r z y₂' i')⁻¹ * (uv j r z i' k')⁻¹) :=
    fun Z r z y₁ y₁' y₂ y₂' i k i' k' a a' b b' hi hk hi' hk' => by
      rw [hw' Z (r ≫ ν) z y₁ y₁' k k' ((hν₂ _).symm ▸ a :) ((hν₂ _).symm ▸ a' :) hk hk',
        hw' Z r z y₂ y₂' i i' b b' hi hi', uv_trans hj r z hi hk hi' hk', hν₁]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
  have H : ∀ y₁ y₂, ∃ g : Γ(Y, (M.pull ν').U (fun _ => y₁) ⊓ M.U y₂)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i k, ν' (π (r z)) ∈ M.U y₁ → π (r z) ∈ M.U y₂ →
        r z ∈ L.U i → ν (r z) ∈ L.U k → gm (r ≫ π) z _ g =
          gw w (r ≫ ν) z y₁ k * (gw w r z y₂ i)⁻¹ * (uv j r z i k)⁻¹ := fun y₁ y₂ => by
    let V : Y.Opens := (M.pull ν').U (fun _ => y₁) ⊓ M.U y₂
    let O : L.ι × L.ι → X.Opens := fun p =>
      π ⁻¹ᵁ V ⊓ LB.wchart L (K := Fin 2) ![𝟙 X, ν] ![p.1, p.2]
    have l₁ : ∀ p, O p ≤ ν ⁻¹ᵁ ((M.pull π).U (fun _ => y₁) ⊓ L.U p.2) := fun p x hx =>
      ⟨mem_pull.2 ((hν₂ x).symm ▸ mem_pull.1 hx.1.1 :), (mem_twist.1 hx.2).2⟩
    have l₂ : ∀ p, O p ≤ (M.pull π).U (fun _ => y₂) ⊓ L.U p.1 := fun p x hx =>
      ⟨mem_pull.2 hx.1.2, (mem_twist.1 hx.2).1⟩
    let a : ∀ p, Γ(X, O p)ˣ := fun p => res (l₁ p) (pullU ν _ (w.s (fun _ => y₁, p.2))) *
      (res (l₂ p) (w.s (fun _ => y₂, p.1)))⁻¹ * (res inf_le_right (j.s ![p.1, p.2]))⁻¹
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) p, r z ∈ O p → gm r z (O p) (a p) =
        gw w (r ≫ ν) z y₁ p.2 * (gw w r z y₂ p.1)⁻¹ * (uv j r z p.1 p.2)⁻¹ :=
      fun Z r z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) ((gm_res r z (l₁ p) hz _).trans (gm_pull r ν z
          ((M.pull π).U (fun _ => y₁) ⊓ L.U p.2) (l₁ p hz) _))
          ((map_inv _ _).trans (congrArg _ (gm_res r z (l₂ p) hz _)))))
        ((map_inv _ _).trans (congrArg _ (gm_res r z inf_le_right hz _))))
    obtain ⟨g, hg⟩ := h.exists_descend_unit V O (fun _ => inf_le_left) (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hL x
      obtain ⟨k, hk⟩ := exists_chart hL (ν x)
      exact ⟨(i, k), hx, mem_twist.2 ⟨hi, hk⟩⟩) a (fun p q x hp hq => by
      have a₁ : ν' (π x) ∈ M.U y₁ := mem_pull.1 hp.1.1
      have hp' := mem_twist.1 hp.2
      have hq' := mem_twist.1 hq.2
      have e := tr _ (𝟙 X) x y₁ y₁ y₂ y₂ p.1 p.2 q.1 q.2 a₁ a₁ hp.1.2 hp.1.2 hp'.1 hp'.2 hq'.1 hq'.2
      have e' := tr _ (𝟙 X) x y₁ y₁ y₂ y₂ q.1 q.2 q.1 q.2 a₁ a₁ hp.1.2 hp.1.2 hq'.1 hq'.2 hq'.1 hq'.2
      rw [v _ (𝟙 X) x p hp, v _ (𝟙 X) x q hq, e, ← e']) (fun c Z r z hz => by
      choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
      have e : (r ≫ t c) ≫ ν = (r ≫ ν) ≫ t (σ c) := by rw [Category.assoc, Category.assoc, hσ]
      have hz' : (r ≫ t c) z ∈ π ⁻¹ᵁ V := by
        change π (t c (r z)) ∈ V
        rw [hπ₂]
        exact hz
      have m₁ : r z ∈ O (J r, J (r ≫ ν)) := ⟨hz, mem_twist.2 ⟨hJ r, hJ (r ≫ ν)⟩⟩
      have m₂ : (r ≫ t c) z ∈ O (J (r ≫ t c), J ((r ≫ t c) ≫ ν)) :=
        ⟨hz', mem_twist.2 ⟨hJ (r ≫ t c), hJ ((r ≫ t c) ≫ ν)⟩⟩
      refine ⟨_, _, m₁, m₂, ?_⟩
      have key := huj c Z r z J hJ
      rw [val_eq_uv, val_eq_uv, val_eq_uv, val_eq_uv] at key
      rw [v Z r z _ m₁, v Z _ z _ m₂]
      dsimp only
      rw [hc c Z r z y₂ (J r) _ hz.2 (hJ r) (hJ _)]
      rw [e] at key ⊢
      rw [hc (σ c) Z (r ≫ ν) z y₁ (J (r ≫ ν)) _ (mem_pull.1 (l₁ _ m₁).1) (hJ _) (hJ _),
        ← mul_inv_eq_iff_eq_mul.2 key]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    refine ⟨g, fun Z r z i k a₁ a₂ hi hk => ?_⟩
    have m : r z ∈ O (i, k) := ⟨⟨mem_pull.2 a₁, a₂⟩, mem_twist.2 ⟨hi, hk⟩⟩
    exact (hg Z r z _ m).trans (v Z r z _ m)
  choose g hg using H
  refine ⟨⟨fun p => g (p.1 PUnit.unit) p.2⟩, isGen_of_flat (π := π) _
    fun x y₁ y₁' y₂ y₂' a a' b b' => ?_⟩
  obtain ⟨i, hi⟩ := exists_chart hL x
  obtain ⟨k, hk⟩ := exists_chart hL (ν x)
  exact (hg y₁ y₂ _ (𝟙 X) x i k a b hi hk).trans
    ((tr _ (𝟙 X) x y₁ y₁' y₂ y₂' i k i k a a' b b' hi hk hi hk).trans
      (congrArg _ (hg y₁' y₂' _ (𝟙 X) x i k a' b' hi hk).symm))

end Sym

end GlobalTheory.LinDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.LinDescent

theorem exists_descent_symmetric :
    ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] (ψ : A ⟶ B) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over S) ⟶ A)) (L : LB A.left), L.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ c, i c ≫ ψ = 1) → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), (∀ x : Over.mk t ⟶ A, x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧ ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1) → ∀ (u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ((toUnit A ≫ i c) * 𝟙 A).left] ![1, -1])) (j : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, -1])), ((∀ c, (u c).IsGen) ∧ (∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c')) (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') ((toUnit A ≫ i c) * 𝟙 A).left))) ∧ j.IsGen ∧ ∀ c (T : Over S) (x : T ⟶ A) (z : T.left) (J), Good L z J → val (u c) x.left z J * val j ((toUnit T ≫ i c) * x).left z J = val j x.left z J * val (u c⁻¹) (x⁻¹).left z J) → ∃ M : LB B.left, M.IsLB ∧ LBIso L (M.pull ψ.left) ∧ LBIso M (M.pull (GrpObj.inv : B ⟶ B).left) := by
  rintro S A B _ _ _ _ ψ C _ _ i L hL hψ _ _ _ hi hk u j ⟨hu, hc, hj, huj⟩
  have hπ : ∀ c, ((toUnit A ≫ i c) * 𝟙 A).left ≫ ψ.left = ψ.left := fun c => by
    rw [← Over.comp_left, MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul,
      Category.id_comp]
  have hT : LocTransitive (fun c => ((toUnit A ≫ i c) * 𝟙 A).left) ψ.left := fun Z g₁ g₂ e z => by
    let Z' : Over S := Over.mk (g₂ ≫ A.hom)
    let k₂ : Z' ⟶ A := Over.homMk g₂ rfl
    let k₁ : Z' ⟶ A := Over.homMk g₁ (by
      change g₁ ≫ A.hom = g₂ ≫ A.hom
      rw [← Over.w ψ, reassoc_of% e])
    have e' : k₁ ≫ ψ = k₂ ≫ ψ := Over.OverMorphism.ext e
    obtain ⟨c, W, a, ha, ⟨w, hw⟩, h⟩ := exists_local_section ψ i hi
      (fun k _ _ t x hx => ((hk k t).1 x).1 hx) (k₁ * k₂⁻¹)
      (by rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]) z
    rw [MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_iff_eq_mul, ← comp_transl] at h
    exact ⟨c, W.left, a.left, ha, w, hw, congrArg (·.left) h⟩
  have hinv : ∀ {T : Over S} (x : T ⟶ A), x ≫ GrpObj.inv = x⁻¹ := fun x => rfl
  obtain ⟨M, hM, w, hw, hw'⟩ := exists_descent_compat_of_galois
    (t := fun c => ((toUnit A ≫ i c) * 𝟙 A).left) hL (by
      beta_reduce
      rw [map_one, MonObj.comp_one, _root_.one_mul, Over.id_left])
    (fun c c' => by
      rw [← Over.comp_left, comp_transl, ← _root_.mul_assoc, ← MonObj.comp_mul, ← map_mul,
        mul_comm c']) hπ hT (fun k _ _ r c c' e => by
      let x : Over.mk (r ≫ A.hom) ⟶ A := Over.homMk r rfl
      have e' : x ≫ ((toUnit A ≫ i c) * 𝟙 A) = x ≫ ((toUnit A ≫ i c') * 𝟙 A) :=
        Over.OverMorphism.ext e
      rw [comp_transl, comp_transl, mul_left_inj, ← mul_inv_eq_one, ← GrpObj.comp_inv,
        ← MonObj.comp_mul, ← map_inv, ← map_mul] at e'
      exact mul_inv_eq_one.1 ((hk k _).2 _ e')) hu hc
  refine ⟨M, hM, ⟨w, hw⟩, descend_iso hL hπ hT hw hw' ?_ (fun c => c⁻¹) (fun c => ?_) hj
    fun c Z r z J hJ => ?_⟩
  · rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]
  · rw [← Over.comp_left, ← Over.comp_left, comp_transl, hinv, map_inv, GrpObj.comp_inv, mul_inv,
      ← hinv (𝟙 A), Category.id_comp]
  · let x : Over.mk (r ≫ A.hom) ⟶ A := Over.homMk r rfl
    have := huj c _ x z J hJ
    rw [← comp_transl x (i c), ← hinv x] at this
    exact this

end GlobalTheory.LinDescent
