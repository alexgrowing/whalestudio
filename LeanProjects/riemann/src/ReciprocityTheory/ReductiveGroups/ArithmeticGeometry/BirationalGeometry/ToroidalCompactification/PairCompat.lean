import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ScalePowMono

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

theorem away_ext {S : Type} [CommRing S] (u : S) {B : Type} [CommRing B] [Algebra S B]
    (f g : Localization.Away u →ₐ[S] B) : f = g := by
  first
  | exact Subsingleton.elim f g
  | exact (IsLocalization.algHom_subsingleton (Submonoid.powers u)).elim f g
  | exact AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (Submonoid.powers u)
      (by ext x; simp))

abbrev Rv {S : Type} [CommRing S] (a b c : S) : Type := Localization.Away (algebraMap S (Qv a b) c)

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G] [∀ s : S, Smooth (Gs G s).hom]

set_option maxHeartbeats 800000 in

theorem pair_compat (a b t : S) (C : Chart (Gs G a)) {y₀ : sp (R₀ := S) (DualNumber (Localization.Away t)) ⟶ G}
    {za : sp (R₀ := S) (DualNumber (Localization.Away a)) ⟶ G} {zb : sp (R₀ := S) (DualNumber (Localization.Away b)) ⟶ G}
    (ha : TanS za) (hb : TanS zb) (N₁ : ℕ)
    (har : spMap (dualMapS (qL a t)) ≫ za =
      spMap (scaleS (S := S) (algebraMap S (Qv a t) t ^ N₁)) ≫ spMap (dualMapS (qR a t)) ≫ y₀)
    (hbr : spMap (dualMapS (qL b t)) ≫ zb =
      spMap (scaleS (S := S) (algebraMap S (Qv b t) t ^ N₁)) ≫ spMap (dualMapS (qR b t)) ≫ y₀) :
    ∃ M : ℕ, spMap (scaleS (S := S) (algebraMap S (Qv a b) t ^ M)) ≫ spMap (dualMapS (qL a b)) ≫ za =
      spMap (scaleS (S := S) (algebraMap S (Qv a b) t ^ M)) ≫ spMap (dualMapS (qR a b)) ≫ zb := by
  have ut : IsUnit (algebraMap S (Rv a b t) t) := by
    rw [IsScalarTower.algebraMap_apply S (Qv a b) (Rv a b t)]
    exact IsLocalization.Away.algebraMap_isUnit _
  have ua : IsUnit (algebraMap S (Rv a b t) a) :=
    unit_of_map (B := Qv a b) (unit_of_map (B := Localization.Away a) (away_unit a))
  have ub : IsUnit (algebraMap S (Rv a b t) b) := unit_of_map (B := Qv a b) (isUnit_qv a b)
  obtain ⟨ρa, -⟩ : ∃ f : Qv a t →ₐ[S] Rv a b t, True := ⟨qHom a t _ ua ut, trivial⟩
  obtain ⟨ρb, -⟩ : ∃ f : Qv b t →ₐ[S] Rv a b t, True := ⟨qHom b t _ ub ut, trivial⟩
  apply tanS_away_uniq C (A := Qv a b) t (tanS_restrict _ ha) (tanS_restrict _ hb)
  have e1 : spMap (dualMapS (IsScalarTower.toAlgHom S (Qv a b) (Rv a b t))) ≫ spMap (dualMapS (qL a b)) ≫ za =
      spMap (scaleS (S := S) (algebraMap S (Rv a b t) t ^ N₁)) ≫ spMap (dualMapS (ρa.comp (qR a t))) ≫ y₀ := by
    rw [res_res, show (IsScalarTower.toAlgHom S (Qv a b) (Rv a b t)).comp (qL a b) = ρa.comp (qL a t) from away_ext _ _ _,
      ← res_res, har, res_scale, map_pow, AlgHom.commutes, res_res]
  have e2 : spMap (dualMapS (IsScalarTower.toAlgHom S (Qv a b) (Rv a b t))) ≫ spMap (dualMapS (qR a b)) ≫ zb =
      spMap (scaleS (S := S) (algebraMap S (Rv a b t) t ^ N₁)) ≫ spMap (dualMapS (ρb.comp (qR b t))) ≫ y₀ := by
    rw [res_res, show (IsScalarTower.toAlgHom S (Qv a b) (Rv a b t)).comp (qR a b) = ρb.comp (qL b t) from away_ext _ _ _,
      ← res_res, hbr, res_scale, map_pow, AlgHom.commutes, res_res]
  rw [e1, e2, show ρa.comp (qR a t) = ρb.comp (qR b t) from away_ext _ _ _]

set_option maxHeartbeats 800000 in
theorem tan_extend {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤) (C : ∀ k, Chart (Gs G (s k)))
    (k0 : Fin n) {y₀ : sp (R₀ := S) (DualNumber (Localization.Away (s k0))) ⟶ G} (hy₀ : TanS y₀) :
    ∃ N : ℕ, ∃ w : sp (R₀ := S) (DualNumber S) ⟶ G, TanS w ∧
      spMap (dualMapS (Algebra.ofId S (Localization.Away (s k0)))) ≫ w =
        spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k0)) (s k0) ^ N)) ≫ y₀ := by
  classical
  have h1 : ∀ k, ∃ N : ℕ, ∃ z : sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G, TanS z ∧
      spMap (dualMapS (qL (s k) (s k0))) ≫ z =
        spMap (scaleS (S := S) (algebraMap S (Qv (s k) (s k0)) (s k0) ^ N)) ≫ spMap (dualMapS (qR (s k) (s k0))) ≫ y₀ :=
    fun k => tanS_away_lift (C k) (A := Localization.Away (s k)) (s k0) (tanS_restrict _ hy₀)
  choose N z hz hzr using h1
  let N₁ := Finset.univ.sup N
  obtain ⟨z', hz', hz'r⟩ : ∃ z' : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G, (∀ k, TanS (z' k)) ∧
      ∀ k, spMap (dualMapS (qL (s k) (s k0))) ≫ z' k =
        spMap (scaleS (S := S) (algebraMap S (Qv (s k) (s k0)) (s k0) ^ N₁)) ≫ spMap (dualMapS (qR (s k) (s k0))) ≫ y₀ := by
    refine ⟨fun k => spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) (s k0) ^ (N₁ - N k))) ≫ z k,
      fun k => tanS_scale _ (hz k), fun k => ?_⟩
    rw [res_scale, hzr k, map_pow, AlgHom.commutes, scale_pow_add,
      Nat.sub_add_cancel (Finset.le_sup (f := N) (Finset.mem_univ k))]
  have h3 : ∀ k l, ∃ M : ℕ,
      spMap (scaleS (S := S) (algebraMap S (Qv (s k) (s l)) (s k0) ^ M)) ≫ spMap (dualMapS (qL (s k) (s l))) ≫ z' k =
        spMap (scaleS (S := S) (algebraMap S (Qv (s k) (s l)) (s k0) ^ M)) ≫ spMap (dualMapS (qR (s k) (s l))) ≫ z' l :=
    fun k l => pair_compat (s k) (s l) (s k0) (C k) (hz' k) (hz' l) N₁ (hz'r k) (hz'r l)
  have h4 : ∃ M₀ : ℕ,
      spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k0)) (s k0) ^ M₀)) ≫ z' k0 =
        spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k0)) (s k0) ^ M₀)) ≫
          spMap (scaleS (algebraMap S (Localization.Away (s k0)) (s k0) ^ N₁)) ≫ y₀ := by
    apply tanS_away_uniq (C k0) (A := Localization.Away (s k0)) (s k0) (hz' k0) (tanS_scale _ hy₀)
    rw [hz'r k0, res_scale, map_pow, AlgHom.commutes, show qR (s k0) (s k0) = qL (s k0) (s k0) from away_ext _ _ _]
  choose M hM using h3
  obtain ⟨M₀, hM₀⟩ := h4
  let M₂ := max M₀ (Finset.univ.sup fun p : Fin n × Fin n => M p.1 p.2)
  obtain ⟨w, hwd⟩ : ∃ w : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G,
      ∀ k, w k = spMap (scaleS (S := S) (algebraMap S (Localization.Away (s k)) (s k0) ^ M₂)) ≫ z' k :=
    ⟨_, fun _ => rfl⟩
  have hw : ∀ k, TanS (w k) := fun k => by rw [hwd]; exact tanS_scale _ (hz' k)
  have hQ : ∀ k l, spMap (dualMapS (qL (s k) (s l))) ≫ w k = spMap (dualMapS (qR (s k) (s l))) ≫ w l := by
    intro k l
    rw [hwd k, hwd l, res_scale, res_scale (qR (s k) (s l)), map_pow, map_pow, AlgHom.commutes, AlgHom.commutes]
    exact scale_pow_mono _ (le_trans (Finset.le_sup (f := fun p : Fin n × Fin n => M p.1 p.2) (Finset.mem_univ (k, l)))
      (le_max_right _ _)) (hM k l)
  obtain ⟨v, hv, hres⟩ := glue_tan' s hs w hw hQ
  refine ⟨M₂ + N₁, v, hv, ?_⟩
  rw [hres k0, hwd k0, scale_pow_mono _ (le_max_left _ _) hM₀, scale_pow_add]

end ReciprocityTheory.ChartRestriction.G.Chart
