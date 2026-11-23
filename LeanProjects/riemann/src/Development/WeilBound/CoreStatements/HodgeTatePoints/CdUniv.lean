import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifBijectiveOfParam
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet

noncomputable section
namespace PositivityTheory.HtPt.Cd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.ChartCompare GlobalTheory.FrameTangent GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws

section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X0 : Scheme.{0}}
  {t : SAB H X0} {S : Type} [CommRing S] {x : Sp S ⟶ X0} {d : ℕ} (g : GermAt t x d)

def jp : JetPts t.G x d := (famEquiv x t.G d).symm g.x

theorem fam_jp : famEquiv x t.G d (jp g) = g.x := Equiv.apply_symm_apply _ _

theorem x_eq (m : ℕ) : g.x m = homAt x (jIn S d m) ≫ jp g m := (congrFun (fam_jp g) m).symm

theorem jp_eq (m : ℕ) : jp g m = homAt x (jOut S d m) ≫ g.x m := rfl

theorem jp_zero (m : ℕ) : algMap x (jetAug : Jet S (Fin d) m →ₐ[S] S) ≫ jp g m = 1 :=
  (zero_iff t x (jp g) m).1 (by rw [fam_jp]; exact g.chart.zero m)

def gd : (Fin d → S) →ₗ[S] TanM x t.G := dif x (jp g 1) (jp_zero g 1)

theorem tg_eq (l : Fin d) : g.tg l = (tv (gd g (Pi.single l 1))).left := by
  have h := (tan_iff t x (jp g) (jp_zero g 1) (g.tg l) (fun j => if l = j then 1 else 0)).2
    (by rw [fam_jp]; exact g.chart.tan l)
  have e : (fun j => if l = j then (1 : S) else 0) = Pi.single l 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [e] at h
  exact h

theorem comb_iff (a : Fin d → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x g.tg a w ↔ (tv (gd g a)).left = w := by
  have e : g.tg = fun i => (tv (gd g (Pi.single ((Equiv.refl (Fin d)) i) 1))).left := funext (tg_eq g)
  have e₂ : ∑ i, a i • gd g (Pi.single i 1) = gd g a := by
    simp only [← map_smul, ← map_sum]
    congr 1
    funext k; simp [Pi.single_apply]
  rw [e, ← e₂]
  exact comb_iff_sum t x (Equiv.refl _) (fun i => gd g (Pi.single i 1)) a w

theorem gd_bij : Function.Bijective (gd g) := by
  rw [Function.bijective_iff_existsUnique]
  intro W
  refine (existsUnique_congr fun a => ?_).1 (g.basis _ (isTanAtG_of _ (tv_zero' W)))
  rw [comb_iff]
  exact ⟨fun h => tv_injective (Over.OverMorphism.ext h), fun h => by rw [h]⟩

theorem jp_param : IsFormalParam t.G x (jp g) :=
  param_of_dif_bijective t.semi.smooth
    (fun m => (trunc_iff t x (jp g) m).1 (by rw [fam_jp]; exact g.chart.trunc m)) (jp_zero g) (gd_bij g)

theorem coord_unique {m : ℕ} {B : Type} [CommRing B] [Algebra S B] (I : Ideal B) (hI : I ^ (m + 1) = ⊥)
    (y : overAt x B ⟶ t.G) (hy : homAt x (Ideal.Quotient.mkₐ S I) ≫ y = 1) :
    ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] B, y = homAt x χ ≫ g.x m := by
  obtain ⟨f, hf, hu⟩ := (jp_param g).2.2 m B I hI y hy
  refine ⟨f.comp (jOut S d m), ?_, fun χ hχ => ?_⟩
  · beta_reduce
    rw [← hcomp, ← jp_eq]; exact hf.symm
  · have := hu (χ.comp (jIn S d m)) (by
      beta_reduce
      rw [algMap_eq, ← hcomp, ← x_eq]; exact hχ.symm)
    rw [← this, AlgHom.comp_assoc, jIn_jOut, AlgHom.comp_id]

theorem coord_aug {m : ℕ} {B : Type} [CommRing B] [Algebra S B] (aug : B →ₐ[S] S)
    (hI : RingHom.ker aug ^ (m + 1) = ⊥) (y : overAt x B ⟶ t.G) (hy : homAt x aug ≫ y = 1) :
    ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] B, aug.comp χ = jetAug ∧ y = homAt x χ ≫ g.x m := by
  have e : Ideal.Quotient.mkₐ S (RingHom.ker aug) = (Algebra.ofId S _).comp aug := by
    refine AlgHom.ext fun r => ?_
    show Ideal.Quotient.mk _ r = Ideal.Quotient.mk _ (algebraMap S B (aug r))
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp
  obtain ⟨χ, hχ, hu⟩ := coord_unique g _ hI y (by rw [e, ← hcomp, hy, MonObj.comp_one])
  refine ⟨χ, ⟨?_, hχ⟩, fun χ' h => hu χ' h.2⟩
  exact (coord_unique g (m := m) (B := S) ⊥ (Ideal.bot_pow (by omega)) 1 (MonObj.comp_one _)).unique
    (by rw [← hcomp, ← hχ, hy]) (g.chart.zero m).symm

theorem ker_aug_pow (J : Type) (m : ℕ) : RingHom.ker (jetAug : Jet S J m →ₐ[S] S) ^ (m + 1) = ⊥ :=
  Chart.ker_jetAug_pow (R := S) J m

theorem coord_jet (J : Type) (m : ℕ) (y : overAt x (Jet S J m) ⟶ t.G)
    (hy : homAt x (jetAug : Jet S J m →ₐ[S] S) ≫ y = 1) :
    ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S J m,
      (∀ q, (jetAug : Jet S J m →ₐ[S] S) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧ y = homAt x χ ≫ g.x m := by
  refine (existsUnique_congr fun χ => and_congr_left fun _ => ?_).1 (coord_aug g jetAug (ker_aug_pow J m) y hy)
  exact ⟨fun h q => (AlgHom.congr_fun h (z m q)).trans (jetAug_z m q),
    fun h => jext fun q => (h q).trans (jetAug_z m q).symm⟩

theorem aeval_inr {κ : Type} [Fintype κ] [DecidableEq κ] (c : κ → S) (P : MvPolynomial κ S) :
    MvPolynomial.aeval (fun s => (TrivSqZeroExt.inr (c s) : DualNumber S)) P =
      TrivSqZeroExt.inl (MvPolynomial.constantCoeff P) +
        TrivSqZeroExt.inr (∑ s, P.coeff (Finsupp.single s 1) * c s) := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    have : ∀ s : κ, (MvPolynomial.C r : MvPolynomial κ S).coeff (Finsupp.single s 1) = 0 := fun s => by
      rw [MvPolynomial.coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm]
    simp [this, TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
    rw [map_add, hp, hq]
    ext <;> simp [add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have : ∀ s : κ, (p * MvPolynomial.X n).coeff (Finsupp.single s 1) =
        if s = n then MvPolynomial.constantCoeff p else 0 := fun s => by
      rw [MvPolynomial.coeff_mul_X']
      by_cases h : s = n
      · subst h; simp [MvPolynomial.constantCoeff_eq]
      · simp [h, Ne.symm h]
    rw [map_mul, hp, MvPolynomial.aeval_X]
    ext <;> simp [this, mul_comm]

theorem vec_subst (φ : Germ.Pt S 1 d) (c : Fin d → S) :
    ((jetVec c).comp (jOut S d 1)).comp (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (φ p.2)) =
      (jetVec ((lin φ 1).mulVec c)).comp (jOut S d 1) := by
  have hT : ∀ (c : Fin d → S) (P : MvPolynomial (Fin 1 × Fin d) S),
      ((jetVec c).comp (jOut S d 1)) (Ideal.Quotient.mk _ P) =
        MvPolynomial.aeval (fun s : Fin 1 × Fin d => (TrivSqZeroExt.inr (c s.2) : DualNumber S)) P := fun c P => by
    have : ((jetVec c).comp (jOut S d 1)).comp (Ideal.Quotient.mkₐ S _) =
        MvPolynomial.aeval (fun s : Fin 1 × Fin d => (TrivSqZeroExt.inr (c s.2) : DualNumber S)) :=
      MvPolynomial.algHom_ext fun s => by
        rw [MvPolynomial.aeval_X]
        refine Eq.trans ?_ (jetVec_z_one c s.2)
        exact congrArg (jetVec c) (jetMap_z (S := S) 1 (fun p : Fin 1 × Fin d => MvPolynomial.X p.2)
          (fun _ => X_mem_orig _) s)
    exact AlgHom.congr_fun this P
  refine jext fun p => ?_
  rw [AlgHom.comp_apply, jetSubstP, jetMap_z, hT, hT, map_sub, aeval_inr, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  have : ∀ s : Fin 1 × Fin d, (psTrunc 1 (φ p.2)).coeff (Finsupp.single s 1) =
      MvPowerSeries.coeff (Finsupp.single s 1) (φ p.2) := fun s => by
    rw [FBIdJet.psTrunc_eq, MvPowerSeries.coeff_truncTotal _ (by simp)]
  simp only [this, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]
  ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [lin, Matrix.mulVec, dotProduct, TrivSqZeroExt.algebraMap_eq_inl]

theorem tv_gd (c : Fin d → S) : tv (gd g c) = homAt x ((jetVec c).comp (jOut S d 1)) ≫ g.x 1 := by
  rw [← hcomp]; rfl

theorem gd_act (a : 𝓞 E) (c : Fin d → S) :
    tv (gd g c) ≫ t.act.act a = tv (gd g ((rho g.B a).mulVec c)) := by
  rw [tv_gd, tv_gd, Category.assoc, g.chart.act 1 a, hcomp, vec_subst]
  rfl

end Gen

theorem germ_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), (∀ (d₂ : ℕ) (_ : GermAt t x d₂), d = d₂) ∧ ∀ (J : Type) [Finite J] (m : ℕ) (y : overAt x (Jet S J m) ⟶ t.G), homAt x (jetAug : Jet S J m →ₐ[S] S) ≫ y = 1 → ∃! χ : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S J m, (∀ q, (jetAug : Jet S J m →ₐ[S] S) (χ (Ideal.Quotient.mk _ (MvPolynomial.X q))) = 0) ∧ y = homAt x χ ≫ g.x m := by
  intro E _ _ _ H _ _ X0 t S _ _ x d g
  refine ⟨fun d₂ g₂ => ?_, fun J _ m y hy => coord_jet g J m y hy⟩
  have e := ((LinearEquiv.ofBijective _ (gd_bij g)).trans (LinearEquiv.ofBijective _ (gd_bij g₂)).symm).finrank_eq
  simpa using e

theorem germ_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (V : Type) [AddCommGroup V] [Module S V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V), ∃ e : V ≃ₗ[S] (Fin d → S), (∀ v, IsCombAtG t x g.tg (e v) (M.pt v).left) ∧ ∀ r : 𝓞 E →+* Module.End S V, M.IsActOf t.act.act r → ∀ a v, e (r a v) = (rho g.B a).mulVec (e v) := by
  intro E _ _ _ H _ _ X0 t S _ x d g V _ _ M
  have ht : ∀ v, IsTanAtG t x (M.pt v).left := fun v => ⟨Over.w (M.pt v), M.tan v⟩
  let L : V →ₗ[S] TanM x t.G :=
    { toFun := fun v => mkT (ovT (ht v)) (smT_zero_ovT (ht v))
      map_add' := fun v w => tv_injective (M.add v w)
      map_smul' := fun c v => tv_injective (Over.OverMorphism.ext (M.smul c v)) }
  have hL : ∀ v, tv (L v) = M.pt v := fun v => rfl
  have hb : Function.Bijective L := by
    refine ⟨fun v w h => M.inj ((hL v).symm.trans ((congrArg tv h).trans (hL w))), fun W => ?_⟩
    obtain ⟨v, hv⟩ := M.onto (tv W) (isTanAtG_of _ (tv_zero' W)).2
    exact ⟨v, tv_injective hv⟩
  let e : V ≃ₗ[S] (Fin d → S) := (LinearEquiv.ofBijective L hb).trans (LinearEquiv.ofBijective _ (gd_bij g)).symm
  have he : ∀ v, gd g (e v) = L v := fun v => (LinearEquiv.ofBijective _ (gd_bij g)).apply_symm_apply _
  refine ⟨e, fun v => (comb_iff g _ _).2 (by rw [he, hL]), fun r hr a v => (gd_bij g).1 (tv_injective ?_)⟩
  rw [← gd_act, he, he, hL, hL]
  exact hr a v

end PositivityTheory.HtPt.Cd
