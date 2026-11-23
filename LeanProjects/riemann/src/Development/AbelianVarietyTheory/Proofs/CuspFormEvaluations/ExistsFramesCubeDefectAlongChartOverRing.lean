import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBFr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGenLiftOfIsNilpotent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

noncomputable section

namespace GlobalTheory.ChartFrames

section Alg

variable {S Ix : Type} [CommRing S]

theorem nilpotent_of_le (m : ℕ) (I : Ideal (Jet S Ix m))
    (h : ∀ p : MvPolynomial Ix S, Ideal.Quotient.mk _ p ∈ I → p ∈ orig S Ix) : IsNilpotent I := by
  refine ⟨m + 1, le_bot_iff.1 ?_⟩
  have h1 : I ≤ Ideal.map (Ideal.Quotient.mk (orig S Ix ^ (m + 1))) (orig S Ix) := by
    intro a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.mem_map_of_mem _ (h p ha)
  refine (Ideal.pow_right_mono h1 _).trans ?_
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem trunc_surj (m : ℕ) :
    Function.Surjective ((jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m) : Jet S Ix (m + 1) →+* Jet S Ix m) := by
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

theorem trunc_nil (m : ℕ) : IsNilpotent
    (RingHom.ker ((jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m) : Jet S Ix (m + 1) →+* Jet S Ix m)) :=
  nilpotent_of_le _ _ fun p hp => by
    have : Ideal.Quotient.mk (orig S Ix ^ (m + 1)) p = 0 := hp
    exact Ideal.pow_le_self (Nat.succ_ne_zero m) (Ideal.Quotient.eq_zero_iff_mem.1 this)

theorem aug_surj (m : ℕ) : Function.Surjective ((jetAug : Jet S Ix m →ₐ[S] S) : Jet S Ix m →+* S) :=
  fun a => ⟨algebraMap S _ a, (jetAug : Jet S Ix m →ₐ[S] S).commutes a⟩

theorem aug_nil (m : ℕ) : IsNilpotent (RingHom.ker ((jetAug : Jet S Ix m →ₐ[S] S) : Jet S Ix m →+* S)) :=
  nilpotent_of_le _ _ fun p hp => by
    have h1 : MvPolynomial.aeval (fun _ => (0 : S)) p = 0 := hp
    have h2 : MvPolynomial.constantCoeff p = 0 := by simpa using h1
    simpa [h2] using sub_const_mem_orig p

variable (d : ℕ)

theorem aug_axis0 (m : ℕ) : (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S).comp (axis0 d m) = jetAug := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  fin_cases i <;> simp [jetSubstP, jetMap_mk, jetAug_X]

theorem aug_axis1 (m : ℕ) : (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S).comp (axis1 d m) = jetAug := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  fin_cases i <;> simp [jetSubstP, jetMap_mk, jetAug_X]

theorem trunc_axis0 (m : ℕ) : (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _).comp (axis0 d (m + 1)) =
    (axis0 d m).comp (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _) := by
  apply jet_hom_ext
  intro p
  rfl

theorem trunc_axis1 (m : ℕ) : (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _).comp (axis1 d (m + 1)) =
    (axis1 d m).comp (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _) := by
  apply jet_hom_ext
  intro p
  rfl

theorem aug_trunc (m : ℕ) : (jetAug : Jet S Ix m →ₐ[S] S).comp (jetTrunc : Jet S Ix (m + 1) →ₐ[S] _) = jetAug := by
  apply jet_hom_ext
  intro p
  rfl

theorem cancel₀ {U : Type} [CommGroup U] (a b : U) : a * b⁻¹ * a⁻¹ * b = 1 := by
  rw [mul_right_comm a, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

theorem cancel₁ {U : Type} [CommGroup U] (a b : U) : a * a⁻¹ * b⁻¹ * b = 1 := by
  rw [mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

end Alg

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem exists_norm {T : Over X0} (p q : T ⟶ t.G) (s₁ s₂ s₀ : T ⟶ T)
    (h₁ : s₁ ≫ (p * q) = p) (h₂ : s₂ ≫ (p * q) = q) (h₀ : s₀ ≫ (p * q) = 1)
    (g₁ : LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (p * q).left) (fun _ => 1))) (hg₁ : g₁.IsGen) :
    ∃ e : LB.Gen (LB.LinComb t.PP.L (cφG t ![p, q]) (cε 2)), e.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good t.PP.L z J →
        val e r z J = val g₁ r z J * (val g₁ (r ≫ s₁.left) z J)⁻¹ * (val g₁ (r ≫ s₂.left) z J)⁻¹ *
          val g₁ (r ≫ s₀.left) z J := by
  obtain ⟨e, he, hv⟩ := exists_gen t.PP.isLB (φ' := cφG t ![p, q]) (ε' := cε 2) (fun U _ h => by
      have hc := prod_cube2 t.G (fun w : T ⟶ t.G => h w.left) ![p, q]
      refine Eq.trans ?_ hc.symm
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, ← Over.comp_left, h₁, h₂, h₀,
        Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one, zpow_neg, zpow_one]
      ac_rfl)
    (LB.mulGen t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ g₁
      (LB.invGen t.PP.L _ _ (LB.pullGen t.PP.L _ _ g₁ s₁.left))) (LB.invGen t.PP.L _ _ (LB.pullGen t.PP.L _ _ g₁ s₂.left)))
      (LB.pullGen t.PP.L _ _ g₁ s₀.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hg₁
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg₁ _)))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg₁ _))) (DVR.pullGen_isGen _ _ _ _ hg₁ _))
  refine ⟨e, he, fun Z r z J hJ => (hv Z r z J hJ).trans ?_⟩
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_pull hJ, val_pull hJ]

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem exists_tower {Ix : Type} (P : ∀ m, overAt x0 (Jet S Ix m) ⟶ t.G)
    (h0 : Formalism.L2.Pj.homAt x0 (jetAug : Jet S Ix 0 →ₐ[S] S) ≫ P 0 = 1)
    (htr : ∀ m, Formalism.L2.Pj.homAt x0 (jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m) ≫ P (m + 1) = P m) :
    ∃ g₁ : ∀ m, LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (P m).left) (fun _ => 1)), (∀ m, (g₁ m).IsGen) ∧
      ∀ m (Z : Scheme.{0}) (r : Z ⟶ (overAt x0 (Jet S Ix m)).left) (z : Z) (J), Good t.PP.L z J →
        val (g₁ (m + 1)) (r ≫ (Formalism.L2.Pj.homAt x0 (jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m)).left) z J =
          val (g₁ m) r z J := by
  obtain ⟨g0, hg0, -⟩ := GlobalTheory.NilGen.exists_gen_lift_of_isNilpotent t.G.left t.PP.L t.PP.isLB (Jet S Ix 0) S _ (aug_surj 0) (aug_nil 0)
    PUnit.{1} (fun _ => (P 0).left) (fun _ => 1) PUnit.{1} (fun _ => (overAt x0 S).hom ≫ eSec t.G) (fun _ => 1)
    (LB.pullGen t.PP.L (fun _ : PUnit.{1} => eSec t.G) (fun _ => 1) t.PP.rig (overAt x0 S).hom)
    (DVR.pullGen_isGen _ _ _ _ t.PP.rigGen _) (fun U _ h => by
      have := congrArg Over.Hom.left h0
      exact Finset.prod_congr rfl fun k _ => congrArg (fun w => h w ^ (1 : ℤ)) this)
  have step := fun m (g : LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (P m).left) (fun _ => 1))) (hg : g.IsGen) =>
    GlobalTheory.NilGen.exists_gen_lift_of_isNilpotent t.G.left t.PP.L t.PP.isLB (Jet S Ix (m + 1)) (Jet S Ix m) _ (trunc_surj m) (trunc_nil m)
      PUnit.{1} (fun _ => (P (m + 1)).left) (fun _ => 1) PUnit.{1} (fun _ => (P m).left) (fun _ => 1) g hg
      (fun U _ h => by
        have := congrArg Over.Hom.left (htr m)
        exact Finset.prod_congr rfl fun k _ => congrArg (fun w => h w ^ (1 : ℤ)) this)
  choose f hf hc using step
  let g₁ : ∀ m, {g : LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (P m).left) (fun _ => 1)) // g.IsGen} :=
    fun m => Nat.rec ⟨g0, hg0⟩ (fun m g => ⟨f m g.1 g.2, hf m g.1 g.2⟩) m
  refine ⟨fun m => (g₁ m).1, fun m => (g₁ m).2, fun m Z r z J hJ => ?_⟩
  exact (val_pull hJ _ _ _).symm.trans (val_corr hJ (hc m (g₁ m).1 (g₁ m).2) r)

end Geo

theorem exists_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∃ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) ∧ FrTrunc t x0 d x e ∧ FrAxes t x0 d x e := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x _ _ hch

  let c : ∀ m, Fin 2 → (jOG x0 d m 2 ⟶ jOG x0 d m 1) := fun m i => Formalism.L2.Pj.homAt x0 (jetCopy d m i)
  let a0 : ∀ m, jOG x0 d m 1 ⟶ jOG x0 d m 2 := fun m => Formalism.L2.Pj.homAt x0 (axis0 d m)
  let a1 : ∀ m, jOG x0 d m 1 ⟶ jOG x0 d m 2 := fun m => Formalism.L2.Pj.homAt x0 (axis1 d m)
  let o : ∀ m n, overAt x0 S ⟶ jOG x0 d m n := fun m n => Formalism.L2.Pj.homAt x0 jetAug
  let u : ∀ m n, jOG x0 d m n ⟶ overAt x0 S := fun m n => Formalism.L2.Pj.homAt x0 (Algebra.ofId S _)
  let tr : ∀ m n, jOG x0 d m n ⟶ jOG x0 d (m + 1) n := fun m n => Formalism.L2.Pj.homAt x0 jetTrunc
  have a0c0 : ∀ m, a0 m ≫ c m 0 = u m 1 ≫ o m 1 := fun m => by
    simp only [a0, c, u, o, homAt_comp, first_axis_at_first_copy]
  have a0c1 : ∀ m, a0 m ≫ c m 1 = 𝟙 _ := fun m => by
    simp only [a0, c, homAt_comp, first_axis_at_second_copy, homAt_id]
  have a1c0 : ∀ m, a1 m ≫ c m 0 = 𝟙 _ := fun m => by
    simp only [a1, c, homAt_comp, second_axis_at_first_copy, homAt_id]
  have a1c1 : ∀ m, a1 m ≫ c m 1 = u m 1 ≫ o m 1 := fun m => by
    simp only [a1, c, u, o, homAt_comp, second_axis_at_second_copy]
  have oa0 : ∀ m, o m 1 ≫ a0 m = o m 2 := fun m => by
    simp only [a0, o, homAt_comp, aug_axis0]
  have oa1 : ∀ m, o m 1 ≫ a1 m = o m 2 := fun m => by
    simp only [a1, o, homAt_comp, aug_axis1]
  have oc : ∀ m i, o m 2 ≫ c m i = o m 1 := fun m i => by
    simp only [c, o, homAt_comp, aug_copy]
  have a0u : ∀ m, a0 m ≫ u m 2 = u m 1 := fun m => by
    simp only [a0, u, homAt_comp, Algebra.comp_ofId]
  have a1u : ∀ m, a1 m ≫ u m 2 = u m 1 := fun m => by
    simp only [a1, u, homAt_comp, Algebra.comp_ofId]
  have tru : ∀ m, tr m 2 ≫ u (m + 1) 2 = u m 2 := fun m => by
    simp only [tr, u, homAt_comp, Algebra.comp_ofId]
  have otr : ∀ m, o m 2 ≫ tr m 2 = o (m + 1) 2 := fun m => by
    simp only [tr, o, homAt_comp, aug_trunc]
  have trc : ∀ m i, tr m 2 ≫ c (m + 1) i = c m i ≫ tr m 1 := fun m i => by
    simp only [tr, c, homAt_comp, copy_trunc]
  have tra0 : ∀ m, tr m 1 ≫ a0 (m + 1) = a0 m ≫ tr m 2 := fun m => by
    simp only [tr, a0, homAt_comp, trunc_axis0]
  have tra1 : ∀ m, tr m 1 ≫ a1 (m + 1) = a1 m ≫ tr m 2 := fun m => by
    simp only [tr, a1, homAt_comp, trunc_axis1]
  have ox : ∀ m, o m 1 ≫ x m = 1 := hch.zero
  have trx : ∀ m, tr m 1 ≫ x (m + 1) = x m := hch.trunc
  have hj : ∀ m i, jptG t x0 d x m i = c m i ≫ x m := fun _ _ => rfl
  obtain ⟨g₁, hg₁, hg₁t⟩ := exists_tower t x0
    (fun m => jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2))
    (by
      change o 0 2 ≫ _ = _
      simp only [hj, MonObj.comp_mul, reassoc_of% (oc 0), ox, _root_.mul_one])
    (fun m => by
      change tr m 2 ≫ _ = _
      simp only [hj, MonObj.comp_mul, reassoc_of% (trc m), trx])
  have key := fun m => exists_norm t (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))
    (c m 0 ≫ a1 m) (c m 1 ≫ a0 m) (u m 2 ≫ o m 2)
    (by simp only [hj, MonObj.comp_mul, Category.assoc, reassoc_of% (a1c0 m), reassoc_of% (a1c1 m), ox,
      MonObj.comp_one, _root_.mul_one])
    (by simp only [hj, MonObj.comp_mul, Category.assoc, reassoc_of% (a0c0 m), reassoc_of% (a0c1 m), ox,
      MonObj.comp_one, _root_.one_mul])
    (by simp only [hj, MonObj.comp_mul, Category.assoc, reassoc_of% (oc m), ox, MonObj.comp_one, _root_.mul_one])
    (g₁ m) (hg₁ m)
  choose e he hv using key
  refine ⟨e, he, fun m => corr_of_val t.PP.isLB fun y J hJ => ?_, fun m => ⟨corr_of_val t.PP.isLB fun y J hJ => ?_,
    corr_of_val t.PP.isLB fun y J hJ => ?_⟩⟩
  · refine (val_pull hJ _ _ _).trans ((hv (m + 1) _ _ y J hJ).trans (Eq.trans ?_ (hv m _ _ y J hJ).symm))
    have e1 : ∀ (s : jOG x0 d m 2 ⟶ jOG x0 d m 2) (s' : jOG x0 d (m + 1) 2 ⟶ jOG x0 d (m + 1) 2),
        tr m 2 ≫ s' = s ≫ tr m 2 →
        val (g₁ (m + 1)) ((𝟙 _ ≫ (tr m 2).left) ≫ s'.left) y J = val (g₁ m) (𝟙 _ ≫ s.left) y J := by
      intro s s' hs
      rw [Category.assoc, ← Over.comp_left, hs, Over.comp_left, ← Category.assoc]
      exact hg₁t m _ _ y J hJ
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (hg₁t m _ _ y J hJ)
      (congrArg _ (e1 _ _ ?_))) (congrArg _ (e1 _ _ ?_))) (e1 _ _ ?_)
    · simp only [Category.assoc, reassoc_of% (trc m), tra1]
    · simp only [Category.assoc, reassoc_of% (trc m), tra0]
    · simp only [Category.assoc, reassoc_of% (tru m), otr]
  · refine (val_pull hJ _ _ _).trans ((hv m _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
    change val (g₁ m) (𝟙 _ ≫ (a0 m).left) y J * (val (g₁ m) ((𝟙 _ ≫ (a0 m).left) ≫ _) y J)⁻¹ *
      (val (g₁ m) ((𝟙 _ ≫ (a0 m).left) ≫ _) y J)⁻¹ * val (g₁ m) ((𝟙 _ ≫ (a0 m).left) ≫ _) y J = 1
    simp only [Category.id_comp, ← Over.comp_left, reassoc_of% (a0c0 m), reassoc_of% (a0c1 m), reassoc_of% (a0u m), oa1]
    exact cancel₀ _ _
  · refine (val_pull hJ _ _ _).trans ((hv m _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
    change val (g₁ m) (𝟙 _ ≫ (a1 m).left) y J * (val (g₁ m) ((𝟙 _ ≫ (a1 m).left) ≫ _) y J)⁻¹ *
      (val (g₁ m) ((𝟙 _ ≫ (a1 m).left) ≫ _) y J)⁻¹ * val (g₁ m) ((𝟙 _ ≫ (a1 m).left) ≫ _) y J = 1
    simp only [Category.id_comp, ← Over.comp_left, reassoc_of% (a1c0 m), reassoc_of% (a1c1 m), reassoc_of% (a1u m), oa0]
    exact cancel₁ _ _

end GlobalTheory.ChartFrames
