import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

section Generic

variable {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)}

theorem finG_mem_box (P : RPG G Gv K) (U : ∀ v, Subgroup (Gv v)) (g : G) : g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := by
  simp [RPG.box, Subgroup.mem_iInf]

theorem finG_box_finite (P : RPG G Gv K) (U : ∀ v, Subgroup (Gv v)) (S : Finset I) (B : ∀ v, Set (Gv v ⧸ U v))
    (hB : ∀ v ∈ S, (B v).Finite) :
    {x : G ⧸ P.box U | (∀ v ∉ S, P.p v x.out ∈ U v) ∧ ∀ v ∈ S, (P.p v x.out : Gv v ⧸ U v) ∈ B v}.Finite := by
  classical
  let f : G ⧸ P.box U → ((v : S) → Gv v ⧸ U v) := fun x v => (P.p v x.out : Gv v ⧸ U v)
  apply Set.Finite.of_finite_image (f := f)
  · apply Set.Finite.subset (Set.Finite.pi (t := fun v : S => B v) (fun v => hB v v.2))
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, forall_const]
    intro v
    exact hx.2 v v.2
  · intro x hx y hy hxy
    have ex : ((x.out : G) : G ⧸ P.box U) = x := Quotient.out_eq x
    have ey : ((y.out : G) : G ⧸ P.box U) = y := Quotient.out_eq y
    rw [← ex, ← ey, QuotientGroup.eq, finG_mem_box]
    intro v
    rw [map_mul, map_inv]
    by_cases hv : v ∈ S
    · exact QuotientGroup.eq.mp (congrFun hxy ⟨v, hv⟩)
    · exact (U v).mul_mem ((U v).inv_mem (hx.1 v hv)) (hy.1 v hv)

theorem finG_finite_image_of_relIndex {H : Type} [Group H] {J L : Subgroup H} (h : J.relIndex L ≠ 0) :
    ((fun a : H => (a : H ⧸ J)) '' (L : Set H)).Finite := by
  have hf : Finite (L ⧸ J.subgroupOf L) := Subgroup.index_ne_zero_iff_finite.mp h
  let g : L ⧸ J.subgroupOf L → H ⧸ J :=
    Quotient.lift (fun a : L => ((a : H) : H ⧸ J)) (by
      intro a b hab
      apply QuotientGroup.eq.mpr
      have := (QuotientGroup.leftRel_apply).mp hab
      simpa [Subgroup.mem_subgroupOf] using this)
  apply Set.Finite.subset (Set.finite_range g)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨(⟨a, ha⟩ : L), rfl⟩

theorem finG_cls_of_box {Γ : Type} (ι : Γ → G) (P : RPG G Gv K) (L U : ∀ v, Subgroup (Gv v)) (S : Finset I)
    (hle : ∀ v, U v ≤ L v) (hoff : ∀ v ∉ S, L v ≤ U v) (hfin : ∀ v ∈ S, (U v).relIndex (L v) ≠ 0)
    (h : ∃ T : Finset G, ∀ g, ∃ γ, ∃ s ∈ T, ∃ u : G, (∀ v, P.p v u ∈ L v) ∧ g = ι γ * s * u) :
    ∃ T : Finset G, ∀ g, ∃ γ, ∃ s ∈ T, ∃ u ∈ P.box U, g = ι γ * s * u := by
  classical
  obtain ⟨T, hT⟩ := h
  have hX := finG_box_finite P U S (fun v => (fun a : Gv v => (a : Gv v ⧸ U v)) '' (L v : Set (Gv v)))
    (fun v hv => finG_finite_image_of_relIndex (hfin v hv))
  refine ⟨(T ×ˢ hX.toFinset).image (fun q => q.1 * q.2.out), ?_⟩
  intro g
  obtain ⟨γ, s, hs, u, hu, rfl⟩ := hT g
  let x : G ⧸ P.box U := (u : G ⧸ P.box U)
  have e : ((x.out : G) : G ⧸ P.box U) = (u : G ⧸ P.box U) := Quotient.out_eq x
  have hw : x.out⁻¹ * u ∈ P.box U := QuotientGroup.eq.mp e
  have hwv := (finG_mem_box P U _).mp hw
  have hxX : x ∈ {x : G ⧸ P.box U | (∀ v ∉ S, P.p v x.out ∈ U v) ∧
      ∀ v ∈ S, (P.p v x.out : Gv v ⧸ U v) ∈ (fun a : Gv v => (a : Gv v ⧸ U v)) '' (L v : Set (Gv v))} := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have hxo : x.out = u * (x.out⁻¹ * u)⁻¹ := by simp
      rw [hxo, map_mul, map_inv]
      exact (U v).mul_mem (hoff v hv (hu v)) ((U v).inv_mem (hwv v))
    · refine ⟨P.p v u, hu v, ?_⟩
      refine (QuotientGroup.eq.mpr ?_).symm
      rw [← map_inv, ← map_mul]
      exact hwv v
  refine ⟨γ, s * x.out, ?_, x.out⁻¹ * u, hw, ?_⟩
  · exact Finset.mem_image.mpr ⟨(s, x), Finset.mem_product.mpr ⟨hs, hX.mem_toFinset.mpr hxX⟩, rfl⟩
  · simp [mul_assoc]

end Generic

section Local

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {Δ : K}

theorem finG_theta_mem_KU (g : U3 Δ) : theta Δ g ∈ KU O Δ ↔ g ∈ KU O Δ := by
  show (∀ i j, IsInt O (((theta Δ g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) ∧
      IsInt O (star (((theta Δ g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j))) ↔
    ∀ i j, IsInt O ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) ∧
      IsInt O (star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j))
  have hc : ∀ i j, ((theta Δ g : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j =
      star ((g : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j) := fun i j => rfl
  simp only [hc, star_star]
  exact ⟨fun h i j => (h i j).symm, fun h i j => (h i j).symm⟩

end Local

variable {F : Type} [Field F] [NumberField F] {Δ : F} {D : Dat Δ}

theorem finG_Jv_of_mem {v : Pl F} (hv : v ∈ D.Sg) : D.Jv v = (D.S v).J := by simp [Dat.Jv, hv]

theorem finG_Jv_of_not_mem {v : Pl F} (hv : v ∉ D.Sg) : D.Jv v = KU (Ov v) _ := by simp [Dat.Jv, hv]

theorem finG_cls_of (hD : D.Ok) (ι : U3 Δ →* GA Δ)
    (h : ∃ S : Finset (GA Δ), ∀ g, ∃ γ, ∃ s ∈ S, ∃ u : GA Δ, (∀ v, u.1 v ∈ KU (Ov v) (cv v Δ)) ∧ g = ι γ * s * u) :
    ∃ S : Finset (GA Δ), ∀ g, ∃ γ, ∃ s ∈ S, ∃ u ∈ D.UG, g = ι γ * s * u := by
  refine finG_cls_of_box ι (rpg _ _) (fun v => KU (Ov v) (cv v Δ)) D.Jv D.Sg (fun v => ?_) (fun v hv => ?_) (fun v hv => ?_) h
  · by_cases hv : v ∈ D.Sg
    · rw [finG_Jv_of_mem hv]; exact (hD.sig v hv).J_le
    · rw [finG_Jv_of_not_mem hv]
  · rw [finG_Jv_of_not_mem hv]
  · rw [finG_Jv_of_mem hv]; exact (hD.sig v hv).J_fin

theorem finG_fGv_inv (hD : D.Ok) {t : Dat.Par F} (ht : D.Cone t) (v : Pl F) (u : U3 (cv v Δ)) (hu : u ∈ D.Jv v) (y : U3 (cv v Δ)) :
    D.fGv t v (u * y) = D.fGv t v y ∧ D.fGv t v (y * theta _ u) = D.fGv t v y := by
  by_cases hv : v ∈ D.Sg
  · rw [finG_Jv_of_mem hv] at hu
    simp only [Dat.fGv, hv, if_true]
    exact (hD.sig v hv).G_inv (t v) (ht v hv) u hu y
  · rw [finG_Jv_of_not_mem hv] at hu
    simp only [Dat.fGv, hv, if_false]
    have hθ : theta _ u ∈ KU (Ov v) (cv v Δ) := (finG_theta_mem_KU u).mpr hu
    constructor
    · rw [Subgroup.mul_mem_cancel_left _ hu]
    · rw [Subgroup.mul_mem_cancel_right _ hθ]

theorem finG_fGv_ne_zero {t : Dat.Par F} {g : GA Δ} (h : D.FG t g ≠ 0) (v : Pl F) : D.fGv t v (g.1 v) ≠ 0 := by
  intro h0
  apply h
  have hae := (rpg (fun v => U3 (cv v Δ)) (fun v => KU (Ov v) (cv v Δ))).ae g
  have hfin : {w | ¬ (g.1 w ∈ KU (Ov w) (cv w Δ))}.Finite := Filter.eventually_cofinite.mp hae
  show ∏ᶠ w, D.fGv t w (g.1 w) = 0
  apply finprod_eq_zero _ v h0
  apply ((D.Sg.finite_toSet).union hfin).subset
  intro w hw
  by_contra hc
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hc
  apply hw
  simp [Dat.fGv, hc.1, hc.2, one]

theorem finG_test (hD : D.Ok) {V : Type} [AddCommGroup V] [Module ℂ V] {ch : F → ℂ} {B : Base (U3 Δ) (GA Δ) V} {s : B.Tw}
    (hB : D.IsBG ch B s) (t : Dat.Par F) (ht : D.Cone t) : s.IsTest (D.FG t) := by
  have hU := hB.U
  have hω := hB.ω
  have hθ := hB.θ
  let P := rpg (fun v => U3 (cv v Δ)) (fun v => KU (Ov v) (cv v Δ))
  have hL : ∀ u ∈ D.UG, ∀ y : GA Δ, D.FG t (u * y) = D.FG t y := by
    intro u hu y
    have huv := (finG_mem_box P D.Jv u).mp hu
    show ∏ᶠ v, D.fGv t v ((u * y).1 v) = ∏ᶠ v, D.fGv t v (y.1 v)
    congr 1
    funext v
    exact (finG_fGv_inv hD ht v (u.1 v) (huv v) (y.1 v)).1
  have hR : ∀ u ∈ D.UG, ∀ y : GA Δ, D.FG t (y * s.θ u) = D.FG t y := by
    intro u hu y
    have huv := (finG_mem_box P D.Jv u).mp hu
    show ∏ᶠ v, D.fGv t v ((y * s.θ u).1 v) = ∏ᶠ v, D.fGv t v (y.1 v)
    congr 1
    funext v
    have e : (y * s.θ u).1 v = y.1 v * theta _ (u.1 v) := by
      show y.1 v * (s.θ u).1 v = _
      rw [hθ]
    rw [e]
    exact (finG_fGv_inv hD ht v (u.1 v) (huv v) (y.1 v)).2
  have hUm : ∀ u : B.U, (u : GA Δ) ∈ D.UG := fun u => hU ▸ u.2
  have hmemU : ∀ g : GA Δ, g ∈ D.UG → g ∈ B.U := fun g hg => hU ▸ hg
  refine ⟨fun u y => ?_, fun u y => ?_, ?_⟩
  · rw [hω]
    simp only [MonoidHom.one_apply, inv_one, Units.val_one, one_mul]
    exact hL u (hUm u) y
  · rw [hω]
    simp only [MonoidHom.one_apply, inv_one, Units.val_one, one_mul]
    exact hR u (hUm u) y
  · let Bs : ∀ v, Set (U3 (cv v Δ) ⧸ D.Jv v) := fun v => {c | D.fGv t v (theta _ c.out) ≠ 0}
    have hBs : ∀ v ∈ D.Sg, (Bs v).Finite := by
      intro v hv
      have hG := (hD.sig v hv).G_fin (t v) (ht v hv)
      show {c : U3 (cv v Δ) ⧸ D.Jv v | D.fGv t v (theta _ c.out) ≠ 0}.Finite
      rw [finG_Jv_of_mem hv]
      simpa [Dat.fGv, hv] using hG
    have hX := finG_box_finite P D.Jv D.Sg Bs hBs
    have hcls : ∀ v (a : U3 (cv v Δ)),
        D.fGv t v (theta _ ((a : U3 (cv v Δ) ⧸ D.Jv v).out)) = D.fGv t v (theta _ a) := by
      intro v a
      have e : (((a : U3 (cv v Δ) ⧸ D.Jv v).out : U3 (cv v Δ)) : U3 (cv v Δ) ⧸ D.Jv v) =
          (a : U3 (cv v Δ) ⧸ D.Jv v) := Quotient.out_eq _
      have hj := QuotientGroup.eq.mp e
      have ha : a = (a : U3 (cv v Δ) ⧸ D.Jv v).out * ((a : U3 (cv v Δ) ⧸ D.Jv v).out⁻¹ * a) := by simp
      conv_rhs => rw [ha, map_mul]
      exact ((finG_fGv_inv hD ht v _ hj _).2).symm
    have hmem : ∀ x : GA Δ ⧸ B.U, D.FG t (s.θ x.out) ≠ 0 →
        ((x.out : GA Δ) : GA Δ ⧸ P.box D.Jv) ∈ {z : GA Δ ⧸ P.box D.Jv | (∀ v ∉ D.Sg, P.p v z.out ∈ D.Jv v) ∧
          ∀ v ∈ D.Sg, (P.p v z.out : U3 (cv v Δ) ⧸ D.Jv v) ∈ Bs v} := by
      intro x hx
      have hne : ∀ v, D.fGv t v (theta _ (x.out.1 v)) ≠ 0 := by
        intro v
        have h1 := finG_fGv_ne_zero hx v
        rwa [hθ] at h1
      let z : GA Δ ⧸ P.box D.Jv := ((x.out : GA Δ) : GA Δ ⧸ P.box D.Jv)
      have e : ((z.out : GA Δ) : GA Δ ⧸ P.box D.Jv) = z := Quotient.out_eq z
      have hw : z.out⁻¹ * x.out ∈ P.box D.Jv := QuotientGroup.eq.mp e
      have hwv : ∀ v, (z.out⁻¹ * x.out).1 v ∈ D.Jv v := (finG_mem_box P D.Jv _).mp hw
      have hzv : ∀ v, z.out.1 v = x.out.1 v * ((z.out⁻¹ * x.out).1 v)⁻¹ := by
        intro v
        simp
      have hz' : ∀ v, D.fGv t v (theta _ (z.out.1 v)) ≠ 0 := by
        intro v
        rw [hzv v, map_mul, (finG_fGv_inv hD ht v ((z.out⁻¹ * x.out).1 v)⁻¹ ((D.Jv v).inv_mem (hwv v))
          (theta _ (x.out.1 v))).2]
        exact hne v
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have h2 := hz' v
        simp [Dat.fGv, hv, one] at h2
        show z.out.1 v ∈ D.Jv v
        rw [finG_Jv_of_not_mem hv]
        exact (finG_theta_mem_KU _).mp h2
      · show D.fGv t v (theta _ ((z.out.1 v : U3 (cv v Δ) ⧸ D.Jv v).out)) ≠ 0
        rw [hcls]
        exact hz' v
    apply Set.Finite.of_finite_image (f := fun x : GA Δ ⧸ B.U => ((x.out : GA Δ) : GA Δ ⧸ P.box D.Jv))
    · exact hX.subset (by rintro _ ⟨x, hx, rfl⟩; exact hmem x hx)
    · intro x _ y _ hxy
      have hq := QuotientGroup.eq.mp hxy
      have ex : ((x.out : GA Δ) : GA Δ ⧸ B.U) = x := Quotient.out_eq x
      have ey : ((y.out : GA Δ) : GA Δ ⧸ B.U) = y := Quotient.out_eq y
      rw [← ex, ← ey]
      exact QuotientGroup.eq.mpr (hmemU _ hq)

end UpperTheory.V.Z.Sym.Glob
