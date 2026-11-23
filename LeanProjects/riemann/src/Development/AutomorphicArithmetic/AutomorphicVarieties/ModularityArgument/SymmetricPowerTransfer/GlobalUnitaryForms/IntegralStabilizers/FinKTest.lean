import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FzdLaw

namespace UpperTheory.V.Z.Sym.Glob

open NumberField Matrix Loc

section Abs

variable {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)}

private theorem supp_fin (P : RPG G Gv K) (f : ∀ v, Gv v → ℂ) (S : Finset I) (h1 : ∀ v ∉ S, ∀ k ∈ K v, f v k = 1) (y : G) :
    (Function.mulSupport fun v => f v (P.p v y)).Finite := by
  refine (S.finite_toSet.union (Filter.eventually_cofinite.1 (P.ae y))).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at h
  exact hv (h1 v h.1 _ h.2)

private theorem prod_law (P : RPG G Gv K) (f : ∀ v, Gv v → ℂ) (S : Finset I) (h1 : ∀ v ∉ S, ∀ k ∈ K v, f v k = 1) (x y : G)
    (c : I → ℂ) (hc : (Function.mulSupport c).Finite) (h : ∀ v, f v (P.p v x) = (c v)⁻¹ * f v (P.p v y)) :
    ∏ᶠ v, f v (P.p v x) = (∏ᶠ v, c v)⁻¹ * ∏ᶠ v, f v (P.p v y) := by
  rw [← finprod_inv_distrib, ← finprod_mul_distrib _ (supp_fin P f S h1 y)]
  · exact finprod_congr h
  · exact hc.subset fun v hv h => hv (by simp [h])

private theorem quot_fin (P : RPG G Gv K) (f : ∀ v, Gv v → ℂ) (S : Finset I) (h1 : ∀ v ∉ S, ∀ k ∈ K v, f v k = 1)
    (U : ∀ v, Subgroup (Gv v)) (hR : ∀ v, ∀ u ∈ U v, ∀ y, f v y ≠ 0 → f v (y * u) ≠ 0) (h2 : ∀ v ∉ S, ∀ g, f v g ≠ 0 → g ∈ U v)
    (h3 : ∀ v ∈ S, {x : Gv v ⧸ U v | f v x.out ≠ 0}.Finite) (H : Subgroup G) (hH : H = P.box U) :
    {x : G ⧸ H | ∏ᶠ v, f v (P.p v x.out) ≠ 0}.Finite := by
  have hne : ∀ y : G, ∏ᶠ v, f v (P.p v y) ≠ 0 → ∀ v, f v (P.p v y) ≠ 0 := fun y hy v h =>
    hy (finprod_eq_zero _ v h (supp_fin P f S h1 y))
  refine Set.Finite.of_finite_image (f := fun (x : G ⧸ H) (v : S) => (P.p v x.out : Gv v ⧸ U v)) ?_ ?_
  · refine (Set.Finite.pi' fun v : S => h3 v v.2).subset ?_
    rintro _ ⟨x, hx, rfl⟩ v
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (U v) (P.p v x.out)
    change f v (Quotient.out _) ≠ 0
    rw [hu]
    exact hR v u u.2 _ (hne _ hx v)
  · intro x hx x' hx' h
    rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x', QuotientGroup.eq]
    refine hH.ge (Subgroup.mem_iInf.2 fun v => ?_)
    rw [Subgroup.mem_comap, map_mul, map_inv]
    by_cases hv : v ∈ S
    · exact QuotientGroup.eq.1 (congrFun h ⟨v, hv⟩)
    · exact mul_mem (inv_mem (h2 v hv _ (hne _ hx v))) (h2 v hv _ (hne _ hx' v))

end Abs

section Local

variable {K : Type} [Field K] {Δ : K}

private theorem scal_comm {z : Kˣ} {s : DX Δ} (h : IsScal z s) (y : DX Δ) : s * y = y * s := by
  apply Subtype.ext
  apply Units.ext
  change mt s * mt y = mt y * mt s
  rw [h]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq

private theorem scal_one : IsScal (1 : Kˣ) (1 : DX Δ) := by
  simp [IsScal, mt]

private theorem scal_mul {z z' : Kˣ} {s s' : DX Δ} (h : IsScal z s) (h' : IsScal z' s') : IsScal (z * z') (s * s') := by
  change mt s * mt s' = _
  rw [h, h', ← map_mul, ← map_mul, Units.val_mul]

private theorem mem_ZD {s : DX Δ} : s ∈ ZD Δ ↔ ∃ z, IsScal z s := by
  rw [ZD, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [IsScal, mt, ← hz]
    rfl
  · rintro ⟨z, hz⟩
    exact ⟨z, Units.ext hz.symm⟩

private theorem sup_dec {J : Subgroup (DX Δ)} {u : DX Δ} (hu : u ∈ ZD Δ ⊔ J) : ∃ z s, IsScal z s ∧ s⁻¹ * u ∈ J := by
  have : (ZD Δ).Normal := ⟨fun s hs g => by
    obtain ⟨z, hz⟩ := mem_ZD.1 hs
    rw [← scal_comm hz g, mul_inv_cancel_right]; exact hs⟩
  obtain ⟨s, hs, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hu
  obtain ⟨z, hz⟩ := mem_ZD.1 hs
  exact ⟨z, s, hz, by simpa using hk⟩

private def Law (J : Subgroup (DX Δ)) (χ : Kˣ →* ℂˣ) (f : DX Δ → ℂ) : Prop :=
  ∀ z s u, IsScal z s → s⁻¹ * u ∈ J → ∀ y, f (u * y) = (χ z : ℂ)⁻¹ * f y ∧ f (y * u) = (χ z : ℂ)⁻¹ * f y

private theorem law_of {J : Subgroup (DX Δ)} {χ : Kˣ →* ℂˣ} {f : DX Δ → ℂ} (h1 : ∀ u ∈ J, ∀ y, f (u * y) = f y ∧ f (y * u) = f y)
    (h2 : ∀ z s, IsScal z s → ∀ y, f (s * y) = ((χ z)⁻¹ : ℂˣ) * f y) : Law J χ f := by
  intro z s u hs hu y
  obtain ⟨k, rfl⟩ : ∃ k, u = s * k := ⟨s⁻¹ * u, by simp⟩
  rw [inv_mul_cancel_left] at hu
  constructor
  · rw [mul_assoc, h2 z s hs, (h1 k hu y).1, Units.val_inv_eq_inv_val]
  · rw [← mul_assoc, ← scal_comm hs, mul_assoc, h2 z s hs, (h1 k hu y).2, Units.val_inv_eq_inv_val]

private theorem law_fzd {J : Subgroup (DX Δ)} {χ : Kˣ →* ℂˣ} {f : DX Δ → ℂ} (h1 : ∀ g, g ∉ ZD Δ ⊔ J → f g = 0)
    (h2 : ∀ z s k, IsScal z s → k ∈ J → f (s * k) = ((χ z)⁻¹ : ℂˣ)) : Law J χ f := by
  have key : ∀ y, y ∈ ZD Δ ⊔ J → ∃ z s k, IsScal z s ∧ k ∈ J ∧ y = s * k := fun y hy => by
    obtain ⟨z, s, hs, hk⟩ := sup_dec hy
    exact ⟨z, s, _, hs, hk, by simp⟩
  refine law_of (fun u hu y => ?_) fun z s hs y => ?_
  · by_cases hy : y ∈ ZD Δ ⊔ J
    · obtain ⟨z, s, k, hs, hk, rfl⟩ := key y hy
      rw [← mul_assoc, ← scal_comm hs u, mul_assoc, mul_assoc, h2 z s _ hs (mul_mem hu hk), h2 z s _ hs (mul_mem hk hu), h2 z s _ hs hk]
      exact ⟨rfl, rfl⟩
    · have hu' : u ∈ ZD Δ ⊔ J := Subgroup.mem_sup_right hu
      rw [h1 y hy, h1 _ (fun h => hy ((mul_mem_cancel_left hu').1 h)), h1 _ (fun h => hy ((mul_mem_cancel_right hu').1 h))]
      exact ⟨rfl, rfl⟩
  · by_cases hy : y ∈ ZD Δ ⊔ J
    · obtain ⟨z', s', k, hs', hk, rfl⟩ := key y hy
      rw [← mul_assoc, h2 _ _ _ (scal_mul hs hs') hk, h2 _ _ _ hs' hk, map_mul, mul_inv, Units.val_mul]
    · have hu' : s ∈ ZD Δ ⊔ J := Subgroup.mem_sup_left (mem_ZD.2 ⟨z, hs⟩)
      rw [h1 y hy, h1 _ (fun h => hy ((mul_mem_cancel_left hu').1 h)), mul_zero]

private theorem law_ne {J : Subgroup (DX Δ)} {χ : Kˣ →* ℂˣ} {f : DX Δ → ℂ} (h : Law J χ f) :
    ∀ u ∈ ZD Δ ⊔ J, ∀ y, f y ≠ 0 → f (y * u) ≠ 0 := by
  intro u hu y hy
  obtain ⟨z, s, hs, hk⟩ := sup_dec hu
  rw [(h z s u hs hk y).2]
  exact mul_ne_zero (inv_ne_zero (Units.ne_zero _)) hy

private theorem sup_dec' {J : Subgroup (DX Δ)} {u : DX Δ} (hu : u ∈ ZD Δ ⊔ J) :
    ∃ z s, (IsScal z s ∧ s⁻¹ * u ∈ J) ∧ (u ∈ J → z = 1) := by
  by_cases h : u ∈ J
  · exact ⟨1, 1, ⟨scal_one, by simpa using h⟩, fun _ => rfl⟩
  · obtain ⟨z, s, hs⟩ := sup_dec hu
    exact ⟨z, s, hs, fun h' => (h h').elim⟩

end Local

theorem finK_test : ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ)
    (B : Base (DX Δ) (DA Δ) V), D.IsBK ch B → ∀ t, D.Cone t → (Base.Tw.one B).IsTest (D.FK t) := by
  intro F _ _ Δ D hD V _ _ ch B hB t ht
  have hoffJ : ∀ v ∉ D.Sg, D.J2v v = KD _ (Ov v) := fun v hv => if_neg hv
  have hofff : ∀ v ∉ D.Sg, D.fKv t v = fZD (Ov v) (D.χ v) := fun v hv => funext fun _ => if_neg hv
  have honJ : ∀ v ∈ D.Sg, D.J2v v = (D.S v).J2 := fun v hv => if_pos hv
  have honf : ∀ v ∈ D.Sg, D.fKv t v = (D.S v).fK (t v) := fun v hv => funext fun _ => if_pos hv
  have hz := fun v (hv : v ∉ D.Sg) => Loc.fzdLaw (Ov v) (Kv v) (cv v Δ) (hD.off v hv) (D.χ v) (hD.chi v).1
  have hlaw : ∀ v, Law (D.J2v v) (D.χ v) (D.fKv t v) := fun v => by
    by_cases hv : v ∈ D.Sg
    · rw [honJ v hv, honf v hv]
      exact law_of ((hD.sig v hv).K_inv _ (ht v hv)).1 ((hD.sig v hv).K_inv _ (ht v hv)).2
    · rw [hoffJ v hv, hofff v hv]
      exact law_fzd (hz v hv).1 (hz v hv).2
  have h1 : ∀ v ∉ D.Sg, ∀ k ∈ KD (cv v Δ) (Ov v), D.fKv t v k = 1 := fun v hv k hk => by
    have := (hz v hv).2 1 1 k scal_one hk
    rw [one_mul, map_one, inv_one, Units.val_one] at this
    rw [hofff v hv, this]
  let P := rpg (fun v : Pl F => DX (cv v Δ)) fun v => KD (cv v Δ) (Ov v)
  have hu : ∀ u : B.U, ∃ c : Pl F → ℂ, (Function.mulSupport c).Finite ∧ (B.ω u : ℂ) = ∏ᶠ v, c v ∧
      ∀ v y, D.fKv t v (P.p v u.1 * y) = (c v)⁻¹ * D.fKv t v y ∧ D.fKv t v (y * P.p v u.1) = (c v)⁻¹ * D.fKv t v y := by
    intro u
    have hm : u.1 ∈ D.UZ := hB.U ▸ u.2
    have hm' : ∀ v, P.p v u.1 ∈ ZD _ ⊔ D.J2v v := fun v => Subgroup.mem_iInf.1 hm v
    choose z s hs h1' using fun v => sup_dec' (hm' v)
    refine ⟨fun v => D.χ v (z v), ?_, hB.ω u z s hs, fun v y => hlaw v _ _ _ (hs v).1 (hs v).2 y⟩
    refine (D.Sg.finite_toSet.union (Filter.eventually_cofinite.1 (P.ae u.1))).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at h
    refine hv ?_
    have := h1' v (hoffJ v h.1 ▸ h.2)
    simp only [this, map_one, Units.val_one]
  refine ⟨fun u y => ?_, fun u y => ?_, ?_⟩
  · obtain ⟨c, hc, e, h⟩ := hu u
    rw [Units.val_inv_eq_inv_val, e]
    exact prod_law P (D.fKv t) D.Sg h1 (u.1 * y) y c hc fun v => by rw [map_mul]; exact (h v _).1
  · obtain ⟨c, hc, e, h⟩ := hu u
    rw [Units.val_inv_eq_inv_val, e]
    exact prod_law P (D.fKv t) D.Sg h1 (y * u.1) y c hc fun v => by rw [map_mul]; exact (h v _).2
  · refine quot_fin P (D.fKv t) D.Sg h1 (fun v => ZD _ ⊔ D.J2v v) (fun v => law_ne (hlaw v)) (fun v hv g hg => ?_) (fun v hv => ?_) B.U hB.U
    · rw [hofff v hv] at hg
      rw [hoffJ v hv]
      by_contra h
      exact hg ((hz v hv).1 g h)
    · have := (hD.sig v hv).K_fin _ (ht v hv)
      rw [← honJ v hv, ← honf v hv] at this
      exact this

end UpperTheory.V.Z.Sym.Glob
