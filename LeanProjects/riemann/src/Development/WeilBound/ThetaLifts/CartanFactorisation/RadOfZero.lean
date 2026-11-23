import Development.WeilBound.ThetaLifts.CartanFactorisation.SpanOrbitStab
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

noncomputable section

namespace PositivityTheory.ThKF

open scoped InnerProductSpace
open Abs

section

variable {Q : Type} [AddCommGroup Q] [Module ℂ Q] (β : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ)

theorem rad_of_zero (hs : ∀ x y, β x y = starRingEnd ℂ (β y x)) (hp : ∀ x, 0 ≤ (β x x).re) {x : Q} (h : β x x = 0) :
    β x = 0 := by
  let c : PreInnerProductSpace.Core ℂ Q :=
    { inner := fun x y => β x y
      conj_inner_symm := fun x y => (hs x y).symm
      re_inner_nonneg := hp
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  ext y
  have := InnerProductSpace.Core.inner_mul_inner_self_le (c := c) x y
  change ‖β x y‖ * ‖β y x‖ ≤ RCLike.re (β x x) * RCLike.re (β y y) at this
  rw [h, map_zero, zero_mul, hs y x, RCLike.norm_conj] at this
  have h2 : ‖β x y‖ = 0 := by nlinarith [norm_nonneg (β x y)]
  simpa using h2

def QR : Type := Q ⧸ LinearMap.ker β

instance : AddCommGroup (QR β) := inferInstanceAs (AddCommGroup (Q ⧸ LinearMap.ker β))
instance : Module ℂ (QR β) := inferInstanceAs (Module ℂ (Q ⧸ LinearMap.ker β))

def mkR : Q →ₗ[ℂ] QR β := (LinearMap.ker β).mkQ

theorem mkR_surj : Function.Surjective (mkR β) := (LinearMap.ker β).mkQ_surjective

theorem mkR_eq_zero {x : Q} : mkR β x = 0 ↔ β x = 0 := Submodule.Quotient.mk_eq_zero _

theorem ex_form (hs : ∀ x y, β x y = starRingEnd ℂ (β y x)) :
    ∃ b : QR β → QR β → ℂ, ∀ x y, b (mkR β x) (mkR β y) = β x y := by
  refine ⟨fun u v => β (mkR_surj β u).choose (mkR_surj β v).choose, fun x y => ?_⟩
  have e : ∀ x, β (mkR_surj β (mkR β x)).choose = β x := fun x => by
    rw [← sub_eq_zero, ← map_sub, ← mkR_eq_zero, map_sub, (mkR_surj β (mkR β x)).choose_spec, sub_self]
  show β _ _ = _
  rw [e x, hs, e y, ← hs]

theorem ex_desc (A : Module.End ℂ Q) (h : ∀ x, β x = 0 → β (A x) = 0) :
    ∃ A' : Module.End ℂ (QR β), ∀ x, A' (mkR β x) = mkR β (A x) :=
  ⟨(LinearMap.ker β).mapQ (LinearMap.ker β) A fun x hx => h x hx, fun _ => rfl⟩

end

theorem absUnit : AbsUnit := by
  intro Q _ _ β 𝒪 A₀ hs hp h0 hadj hadm N hN huniq
  classical
  obtain ⟨b, hb⟩ := ex_form β hs
  have sj := mkR_surj β
  let c : InnerProductSpace.Core ℂ (QR β) :=
    { inner := b
      conj_inner_symm := fun x y => by obtain ⟨x, rfl⟩ := sj x; obtain ⟨y, rfl⟩ := sj y; rw [hb, hb]; exact (hs x y).symm
      re_inner_nonneg := fun x => by obtain ⟨x, rfl⟩ := sj x; rw [hb]; exact hp x
      add_left := fun x y z => by
        obtain ⟨x, rfl⟩ := sj x; obtain ⟨y, rfl⟩ := sj y; obtain ⟨z, rfl⟩ := sj z
        rw [← map_add, hb, hb, hb]; simp
      smul_left := fun x y r => by
        obtain ⟨x, rfl⟩ := sj x; obtain ⟨y, rfl⟩ := sj y
        rw [← map_smul, hb, hb]; simp
      definite := fun x hx => by
        obtain ⟨x, rfl⟩ := sj x
        rw [hb] at hx
        exact (mkR_eq_zero β).2 (rad_of_zero β hs hp hx) }
  letI : NormedAddCommGroup (QR β) := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (QR β) := InnerProductSpace.ofCore c.toCore
  have hin : ∀ x y, ⟪mkR β x, mkR β y⟫_ℂ = β x y := hb
  have hrad : ∀ A ∈ 𝒪, ∀ x, β x = 0 → β (A x) = 0 := fun A hA x hx => by
    obtain ⟨A', -, c, h⟩ := hadj A hA
    ext y; simp [h, hx]
  have hA₀ : ∀ x ∈ A₀, mkR β x = 0 := fun x hx => (mkR_eq_zero β).2 (rad_of_zero β hs hp (h0 x hx))
  let St : Submodule ℂ (QR β) → Prop := fun S => ∀ A ∈ 𝒪, ∀ x, mkR β x ∈ S → mkR β (A x) ∈ S
  have hproj : Proj St := by
    intro u
    obtain ⟨f, rfl⟩ := sj u
    obtain ⟨K, _, κ, hκ, hiso, hfin, hhom⟩ := hadm f
    choose D hD using fun k => ex_desc β (κ k) (hrad _ (hκ k))
    let κ' : K →* Module.End ℂ (QR β) :=
      { toFun := D
        map_one' := LinearMap.ext fun u => by obtain ⟨x, rfl⟩ := sj u; simp [hD]
        map_mul' := fun k k' => LinearMap.ext fun u => by obtain ⟨x, rfl⟩ := sj u; simp [hD] }
    have hκ' : ∀ k x, κ' k (mkR β x) = mkR β (κ k x) := hD
    have hi : ∀ k x y, ⟪κ' k x, κ' k y⟫_ℂ = ⟪x, y⟫_ℂ := fun k x y => by
      obtain ⟨x, rfl⟩ := sj x; obtain ⟨y, rfl⟩ := sj y; rw [hκ', hκ', hin, hin, hiso]
    have hf : ∀ u, FiniteDimensional ℂ (orb κ' u) := fun u => by
      obtain ⟨x, rfl⟩ := sj u
      obtain ⟨t, ht⟩ := hfin x
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (t : Set Q)).map (mkR β)) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1 (ht k)
      exact ⟨y, hy, by show _ = κ' k _; rw [hκ', ← e, map_add, hA₀ z hz, add_zero]⟩
    have := hf (mkR β f)
    let W := orb κ' (mkR β f)
    let bs : W ≃ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := (Module.finBasis ℂ W).equivFun
    let r : K → Module.End ℂ W := fun k => (κ' k).restrict (span_orbit_stab κ' (mkR β f) k)
    let ρ : K →* Module.End ℂ (Fin (Module.finrank ℂ W) → ℂ) :=
      { toFun := fun k => bs.toLinearMap ∘ₗ r k ∘ₗ bs.symm.toLinearMap
        map_one' := LinearMap.ext fun y => by
          have : r 1 (bs.symm y) = bs.symm y := Subtype.ext (by show κ' 1 _ = _; simp)
          simp [this]
        map_mul' := fun k k' => LinearMap.ext fun y => by
          have : r (k * k') (bs.symm y) = r k (r k' (bs.symm y)) := Subtype.ext (by show κ' (k * k') _ = κ' k (κ' k' _); simp)
          simp [this] }
    obtain ⟨t, ht⟩ := hhom _ ρ fun hfix k => LinearMap.ext fun y => by
      have h1 : ∀ w ∈ W, κ' k w = w := fun w hw => by
        induction hw using Submodule.span_induction with
        | mem y h => obtain ⟨k', rfl⟩ := h; simp only [hκ', hfix]
        | zero => simp
        | add a b _ _ ha hb => rw [map_add, ha, hb]
        | smul c a _ ha => rw [map_smul, ha]
      have : r k (bs.symm y) = bs.symm y := Subtype.ext (h1 _ (bs.symm y).2)
      show bs (r k (bs.symm y)) = y
      simp [this]
    have hH : FiniteDimensional ℂ (homs κ' W) := by
      let j : homs κ' W →ₗ[ℂ] Submodule.span ℂ (t : Set (Q →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ))) :=
        { toFun := fun L => ⟨bs.toLinearMap ∘ₗ (L.1.codRestrict W L.2.1) ∘ₗ mkR β, ht _
            (fun x hx => by simp [hA₀ x hx]) fun k x => by
              show bs _ = bs (r k (bs.symm (bs _)))
              rw [bs.symm_apply_apply]
              exact congrArg bs (Subtype.ext (by show L.1 (mkR β (κ k x)) = κ' k (L.1 (mkR β x)); rw [← hκ', L.2.2]))⟩
          map_add' := fun a b => Subtype.ext (LinearMap.ext fun x => bs.map_add ⟨_, a.2.1 _⟩ ⟨_, b.2.1 _⟩)
          map_smul' := fun c a => Subtype.ext (LinearMap.ext fun x => bs.map_smul c ⟨_, a.2.1 _⟩) }
      refine Module.Finite.of_injective j ((injective_iff_map_eq_zero j).2 fun L hL => Subtype.ext (LinearMap.ext fun u => ?_))
      obtain ⟨x, rfl⟩ := sj u
      have h1 : bs ⟨L.1 (mkR β x), L.2.1 _⟩ = 0 := LinearMap.congr_fun (congrArg Subtype.val hL) x
      exact congrArg Subtype.val (bs.map_eq_zero_iff.1 h1)
    obtain ⟨Z, Z', h1, h2, h3, h4⟩ := exists_e κ' hi hf _ hH
    refine ⟨Z, Z', h1, h2, h3, fun S hS => h4 S fun k y hy => ?_⟩
    obtain ⟨x, rfl⟩ := sj y
    rw [hκ']
    exact hS _ (hκ k) x hy
  have hbot := eq_bot hproj (fun s hs A hA x hx => Submodule.mem_sInf.2 fun S hS => hs S hS A hA x (Submodule.mem_sInf.1 hx S hS))
    (fun S hS A hA x hx => by
      obtain ⟨A', hA', c, h⟩ := hadj A hA
      rw [Submodule.mem_orthogonal']
      intro u hu
      obtain ⟨y, rfl⟩ := sj u
      rw [hin, h, ← hin, (Submodule.mem_orthogonal' _ _).1 hx _ (hS A' hA' y hu), mul_zero])
    (N.map (mkR β)) (fun A hA x hx => by
      obtain ⟨y, hy, e⟩ := hx
      refine ⟨A y, hN.prop.1.2 A hA y hy, ?_⟩
      rw [← sub_eq_zero, ← map_sub, ← map_sub, mkR_eq_zero]
      exact hrad A hA _ ((mkR_eq_zero β).1 (by rw [map_sub, e, sub_self])))
    fun M hM => by
      have : M.comap (mkR β) = N := huniq _ ⟨⟨⟨fun x hx => by simp [hA₀ x hx], fun A hA x hx => hM.prop.1 A hA x hx⟩,
        fun ht => hM.prop.2 (eq_top_iff.2 fun u _ => by obtain ⟨x, rfl⟩ := sj u; exact (ht ▸ Submodule.mem_top : x ∈ M.comap (mkR β)))⟩,
        fun P hP hle => by
          have hk : ∀ x y, y ∈ P → mkR β y = mkR β x → x ∈ P := fun x y hy e => by
            have : x - y ∈ P := hle (show mkR β (x - y) ∈ M by rw [map_sub, e, sub_self]; exact M.zero_mem)
            simpa using P.add_mem this hy
          have h1 : P.map (mkR β) ≤ M := hM.le_of_ge ⟨fun A hA x ⟨y, hy, e⟩ => ⟨A x, hP.1.2 A hA x (hk x y hy e), rfl⟩,
            fun ht => hP.2 (eq_top_iff.2 fun x _ => by
              obtain ⟨y, hy, e⟩ : mkR β x ∈ P.map (mkR β) := ht ▸ Submodule.mem_top
              exact hk x y hy e)⟩ fun u hu => by obtain ⟨x, rfl⟩ := sj u; exact ⟨x, hle hu, rfl⟩
          exact fun x hx => h1 ⟨x, hx, rfl⟩⟩
      rw [← this]
      exact Submodule.map_comap_le _ _
  intro x hx
  have : mkR β x = 0 := (Submodule.eq_bot_iff _).1 hbot _ ⟨x, hx, rfl⟩
  simp [(mkR_eq_zero β).1 this]

end PositivityTheory.ThKF

end
