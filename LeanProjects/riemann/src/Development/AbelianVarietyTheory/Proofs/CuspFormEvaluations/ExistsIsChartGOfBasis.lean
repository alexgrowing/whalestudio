import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartCut
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsPtJ

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (FGLaw)
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChartData

open GlobalTheory.ChartJet (Q gen sq_gen)

theorem mk_psTrunc {S : Type} [CommRing S] {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    ChartJet.pj m f = Ideal.Quotient.mk _ (psTrunc m f - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m f))) := by
  have co : ∀ e : κ →₀ ℕ, e.degree < m + 1 → (psTrunc m f).coeff e = MvPowerSeries.coeff e f := fun e he => by
    have hm : e ∈ degLE m := Finset.mem_filter.2 ⟨Finset.mem_image.2
      ⟨fun i => ⟨e i, lt_of_le_of_lt (Finsupp.le_degree i e) he⟩, Finset.mem_univ _, by ext i; simp⟩, Nat.le_of_lt_succ he⟩
    rw [psTrunc, MvPolynomial.coeff_sum, Finset.sum_eq_single e (fun b _ hb => by rw [MvPolynomial.coeff_monomial, if_neg hb])
      (fun h => absurd hm h), MvPolynomial.coeff_monomial, if_pos rfl]
  have c0 : MvPolynomial.constantCoeff (psTrunc m f) = 0 := (co 0 (by simp)).trans hf
  rw [c0, map_zero, sub_zero]
  exact ChartJet.pj_eq_mk.2 fun e he => (co e he).symm

theorem jetMap_zR {S : Type} [CommRing S] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (h) (s : κ) :
    (jetMap φ h : Jet S κ m →ₐ[S] Jet S κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X s)) = Ideal.Quotient.mk _ (φ s) := by
  show Ideal.Quotient.mkₐ S _ (MvPolynomial.aeval φ (MvPolynomial.X s)) = _
  rw [MvPolynomial.aeval_X]; rfl

theorem subst_zR {S : Type} [CommRing S] {d n : ℕ} (m : ℕ) (p : Q S d n) (s : Fin 1 × Fin d) :
    jetSubstP m (fun s : Fin 1 × Fin d => psTrunc m (p.1 s.2)) (Chart.zR m s) = ChartJet.pj m (p.1 s.2) :=
  (jetMap_zR m _ _ s).trans (mk_psTrunc m _ (p.2 _)).symm

theorem copy_zR {S : Type} [CommRing S] {d n : ℕ} (m : ℕ) (i : Fin n) (s : Fin 1 × Fin d) :
    jetCopy (S := S) d m i (Chart.zR m s) = ChartJet.pj m ((gen i : Q S d n).1 s.2) :=
  (jetMap_zR m _ _ s).trans (ChartJet.pj_X m (i, s.2)).symm

set_option maxHeartbeats 1600000 in

theorem exists_isChartG_of_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)), (∀ ℓ, IsTanAtG t x0 (tg ℓ)) → (∀ w, IsTanAtG t x0 w → ∃! a : κ → S, IsCombAtG t x0 (m := Fintype.card κ) (fun i => tg ((Fintype.equivFin κ).symm i)) (fun i => a ((Fintype.equivFin κ).symm i)) w) → ∃ (d : ℕ) (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), d = Fintype.card κ ∧ (∀ ℓ (j : Fin d), uvec ℓ j = if (j : ℕ) = (Fintype.equivFin κ ℓ : ℕ) then 1 else 0) ∧ IsChartG t x0 d G.F A.act tg uvec x := by
  classical
  intro E _ _ _ H X0 t S _ x0 κ _ tg htan hb
  have hp := isGrpPullback_pullback t.G x0
  have := t.semi.smooth
  have : Smooth ((Over.pullback x0).obj t.G).hom :=
    smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  let φ := pullback.fst t.G.hom x0
  let up : ∀ w : Sp (DualNumber S) ⟶ t.G.left, w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x0 →
      (epsR S ⟶ (Over.pullback x0).obj t.G) := fun w h => Over.homMk (pullback.lift w _ h) (pullback.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => pullback.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ (Over.pullback x0).obj t.G}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (pullback.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk (T.hom ≫ x0) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have tan : ∀ w : epsR S ⟶ (Over.pullback x0).obj t.G, IsTangent w ↔ IsTanAtG t x0 (w.left ≫ φ) := fun w => by
    have e : (1 : Chart.sp (R₀ := S) S ⟶ (Over.pullback x0).obj t.G).left ≫ φ = (1 : Over.mk x0 ⟶ t.G).left :=
      (one _).trans (congrArg (· ≫ (η[t.G]).left) (show Spec.map (CommRingCat.ofHom (RingHom.id S)) ≫ x0 = x0 by simp))
    rw [← Chart.isTan_iff]
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => inj ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEpsG x0 ⟶ t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ (Over.pullback x0).obj t.G)) w,
      IsLieComb c v w ↔ IsCombAtG t x0 (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => pullback.hom_ext ?_ ?_, inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (Over.w (Chart.spMap (Chart.scaleD (c i)))).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEpsG x0 ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x0 ⟶ t.G) => (List.ofFn q).prod.left) this
  let e := Fintype.equivFin κ
  let v : Fin (Fintype.card κ) → (epsR S ⟶ (Over.pullback x0).obj t.G) := fun i => up (tg (e.symm i)) (htan _).1
  have hv : (fun i => (v i).left ≫ φ) = fun i => tg (e.symm i) := funext fun i => hup _ _
  have hB : IsLieBasis v := ⟨fun i => (tan _).2 (by rw [hup]; exact htan _), fun w hw => by
    obtain ⟨a, ha, hu⟩ := hb _ ((tan w).1 hw)
    refine ⟨fun i => a (e.symm i), (comb _ _ _).2 (hv ▸ ha), fun c hc => ?_⟩
    have := hu (fun l => c (e l)) (by simpa only [e, Equiv.apply_symm_apply] using hv ▸ (comb _ _ _).1 hc)
    funext i; rw [← this]; simp⟩
  obtain ⟨x, hx, hxv'⟩ := GlobalTheory.exists_isUnivChart_of_isLieBasis S ((Over.pullback x0).obj t.G) this _ v hB
  have hxv := fun j => (hxv' j).symm
  obtain ⟨F, A, hF, hA⟩ := ChartJet.exists_series hx (OAct.pullback x0 t.G t.act)
  have sub : ∀ {n} m (p : Q S (Fintype.card κ) n) (g : Jet S (Fin 1 × Fin (Fintype.card κ)) m →ₐ[S] Jet S (Fin n × _) m),
      (∀ s, g (Chart.zR m s) = ChartJet.pj m (p.1 s.2)) →
      homAt x0 g ≫ pushPt hp.1.w (ChartJet.ptJ x m (gen 0)) = pushPt hp.1.w (ChartJet.ptJ x m p) := fun m p g hg => by
    have e₁ : g = ChartJet.jQ m ![p] := Chart.jet_ext fun s => (hg s).trans (by
      obtain ⟨i, j⟩ := s
      obtain rfl := Subsingleton.elim i 0
      exact (ChartJet.jS_zR m (fun s : Fin 1 × _ => ((![p] : Fin 1 → _) s.1).1 s.2) (fun s => ((![p] : Fin 1 → _) s.1).2 s.2)
        (0, j)).symm)
    have e₂ := ChartJet.ptJ_sq x m ![p] (gen 0)
    rw [sq_gen, ← e₁] at e₂
    exact Over.OverMorphism.ext ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q.left ≫ φ) e₂))
  have sp := fun {n} m (p : Q S (Fintype.card κ) n) => subst_zR m p
  have cp : ∀ {n} m (i : Fin n), jptG t x0 _ (fun m => pushPt hp.1.w (ChartJet.ptJ x m (gen 0))) m i =
      pushPt hp.1.w (ChartJet.ptJ x m (gen i)) := fun m i => sub m (gen i) _ (copy_zR m i)
  refine ⟨_, F, A, fun l => Pi.single (e l) 1, fun m => pushPt hp.1.w (ChartJet.ptJ x m (gen 0)), rfl,
    fun l j => by simp only [Pi.single_apply, Fin.ext_iff, e], fun m => ?_, fun m => ?_,
    fun m => ?_, fun m a => ?_, fun l => ?_, fun w => ?_⟩
  · exact Over.OverMorphism.ext ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q.left ≫ φ) (ChartJet.ptJ_aug hx m (gen 0))).trans (one _)))
  · exact Over.OverMorphism.ext ((Category.assoc _ _ _).symm.trans
      (congrArg (fun q => q.left ≫ φ) (ChartJet.ptJ_trunc hx m (gen 0))))
  · rw [cp, cp]
    exact (sub m ⟨F.F, F.const⟩ _ (sp m _)).trans ((congrArg _ (hF m)).trans (map_mul (pushHom hp _) _ _))
  · refine Eq.trans ?_ ((sub m ⟨A.act a, A.const a⟩ _ (sp m _)).trans (congrArg _ (hA a m))).symm
    exact Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (pullback.lift_fst _ _ _ : ((OAct.pullback x0 t.G t.act).act a).left ≫ φ = φ ≫ (t.act.act a).left).symm).trans
      (Category.assoc _ _ _).symm))
  · have h := (comb _ _ _).1 (ChartJet.comb_single hx hxv (e l))
    rw [hup, Equiv.symm_apply_apply] at h
    convert h using 2 with j
    let T : Chart.JetR S (Fin 1 × Fin (Fintype.card κ)) 1 →ₐ[S] DualNumber S := (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (Fintype.card κ)) (0 + 1) →ₐ[S] DualNumber S)
    have e₁ : T.comp (ChartJet.jP 1 (gen 0 : Q S _ 1)) = Chart.dualLift (Pi.single j 1) := Chart.jet_ext fun i => by
      rw [AlgHom.comp_apply, ChartJet.jP_zR, Chart.dualLift_zR]
      refine (congrArg T (ChartJet.pj_X 1 ((0 : Fin 1), i))).trans ?_
      show MvPolynomial.aeval (fun i => if i = ((0 : Fin 1), j) then (DualNumber.eps : DualNumber S) else 0)
        (MvPolynomial.X ((0 : Fin 1), i)) = _
      rw [MvPolynomial.aeval_X]
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl, Pi.single_eq_same]; rfl
      · rw [if_neg (fun h => hij (Prod.ext_iff.1 h).2), Pi.single_eq_of_ne hij, TrivSqZeroExt.inr_zero]
    have e₂ : Chart.spMap T ≫ ChartJet.ptJ x 1 (gen 0) = v j := by
      rw [hxv, ← e₁, ← Chart.spMap_comp, Category.assoc]; rfl
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun q => q.left ≫ φ) e₂)
  · refine ⟨fun l => w (e l), fun j => ?_, fun a ha => funext fun l => ?_⟩
    · rw [Finset.sum_eq_single (e.symm j) (fun b _ hb => by
        rw [Pi.single_eq_of_ne (fun h => hb (by rw [h, Equiv.symm_apply_apply])), mul_zero]) (by simp)]
      simp
    · rw [← ha, Finset.sum_eq_single l (fun b _ hb => by
        rw [Pi.single_eq_of_ne (fun h => hb (e.injective h).symm), mul_zero]) (by simp)]
      simp

end GlobalTheory.ChartData
