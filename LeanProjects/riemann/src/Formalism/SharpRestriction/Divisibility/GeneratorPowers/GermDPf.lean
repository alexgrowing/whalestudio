import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDVal

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

attribute [local instance] Over.cartesianMonoidalCategory

namespace GermD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem genPowG_isGen {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (hg : g.IsGen) (k : ℕ) : (genPowG t φ ε g k).IsGen := by
  unfold LB.Gen.IsGen at hg ⊢
  intro i j
  simp only [genPowG]
  erw [map_pow, map_pow, hg i j, mul_pow]
  congr 1
  unfold LB.LinComb
  dsimp only
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm]

theorem val_genPowG {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (k : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) :
    val (genPowG t φ ε g k) r z J = val g r z J ^ k := by
  simp only [genPowG, val]
  exact map_pow _ _ _

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

abbrev ρT (m : ℕ) : jOG x0 d m 1 ⟶ jOG x0 d (m + 1) 1 :=
  homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m)

theorem jBase_trunc (m : ℕ) : ρT x0 d m ≫ jBaseG x0 d (m + 1) 1 = jBaseG x0 d m 1 := by
  apply Over.OverMorphism.ext
  simp only [ρT, jBaseG, Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left]
  rw [spMap_comp_alg]

variable {t x0 d x}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}

private lemma formEq_eL_lemma (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) S) :
    (sL m g).comp (jetCopy d m (0 : Fin 2)) = AlgHom.id S _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  fin_cases i
  simp [sL, jetCopy, jetMap, jetSubstP, liftJet, Ideal.Quotient.liftₐ_apply]
  erw [Ideal.Quotient.lift_mk]
  simp

private lemma formEq_eL_lemma_2 (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) S) :
    (sL m g).comp (jetCopy d m (1 : Fin 2)) = jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (g p.2) := by
  have hq : ∀ q : MvPolynomial (Fin 1 × Fin d) S,
      MvPolynomial.rename (fun p : Fin 1 × Fin d => ((0 : Fin 1), p.2)) q = q := by
    intro q
    rw [show (fun p : Fin 1 × Fin d => ((0 : Fin 1), p.2)) = id from
      funext fun p => Prod.ext (Subsingleton.elim _ _) rfl]
    simp
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  fin_cases i
  simp [sL, jetCopy, jetMap, jetSubstP, liftJet, Ideal.Quotient.liftₐ_apply]
  erw [Ideal.Quotient.lift_mk]
  simp [psIn, hq]
  erw [Ideal.Quotient.lift_mk]
  simp [psIn, hq]

theorem formEq_eL (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) (I : ULift (Finset (Fin 2))) :
    (x m).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (homAt x0 (sL m (act H.w0))).left ≫ cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := by
  have hp : ∀ {T T' : Over X0} (f : T' ⟶ T) (a b : T ⟶ t.G),
      f ≫ padd t.G a b = padd t.G (f ≫ a) (f ≫ b) := by
    intro T T' f a b
    simp only [padd, ← Category.assoc, comp_lift]
  have nat : ∀ {T T' : Over X0} (f : T' ⟶ T) (xs : Fin 2 → (T ⟶ t.G)) (l : List (Fin 2)),
      f ≫ l.foldr (fun k acc => padd t.G (xs k) acc) (pzero t.G T) =
        l.foldr (fun k acc => padd t.G (f ≫ xs k) acc) (pzero t.G T') := by
    intro T T' f xs l
    induction l with
    | nil => simp only [List.foldr_nil, pzero, ← Category.assoc, comp_toUnit]
    | cons k l ih => simp only [List.foldr_cons, hp, ih]
  have natp : ∀ {T T' : Over X0} (f : T' ⟶ T) (xs : Fin 2 → (T ⟶ t.G)) (J : Finset (Fin 2)),
      f ≫ psum t.G xs J = psum t.G (fun i => f ≫ xs i) J := by
    intro T T' f xs J
    unfold psum
    exact nat f xs _
  simp only [cφG]
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [natp, natp]
  congr 1
  funext i
  fin_cases i
  · simp [jptG, ← Category.assoc, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp, formEq_eL_lemma, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_id]
  · simp [jptG, ← Category.assoc, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp, formEq_eL_lemma_2, hch.act m H.w0]

theorem val_eL_trunc (hch : IsChartG t x0 d F act tg uvec x) (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t)
    (htr : FrTrunc t x0 d x e) (m : ℕ) (y : (jOG x0 d m 1).left) (J : ((jOG x0 d m 1).left ⟶ t.G.left) → t.PP.L.ι)
    (hJ : Good t.PP.L y J) :
    val (eLG t x0 d x act e wP (m + 1)) (ρT x0 d m).left y J = val (eLG t x0 d x act e wP m) (𝟙 _) y J := by
  have hx : (ρT x0 d m).left ≫ (x (m + 1)).left = (x m).left := by
    rw [← Over.comp_left, hch.trunc m]
  have hs : (ρT x0 d m).left ≫ (homAt x0 (sL (m + 1) (act H.w0))).left =
      (homAt x0 (sL m (act H.w0))).left ≫ (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left := by
    rw [← Over.comp_left, ← Over.comp_left, homAt_comp, homAt_comp, sL_trunc]
  refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
  · exact (val_pull hJ wP _ _).trans ((congrArg (fun r => val wP r y J) (hx.trans (Category.id_comp _).symm)).trans
      (val_pull hJ wP _ _).symm)
  · exact (val_pull hJ (e (m + 1)) _ _).trans ((congrArg (fun r => val (e (m + 1)) r y J) hs).trans
      ((val_pull hJ (e (m + 1)) _ _).symm.trans ((val_corr hJ (htr m) _).trans
        ((congrArg (fun r => val (e m) r y J) (Category.id_comp _).symm).trans (val_pull hJ (e m) _ _).symm))))

theorem ptSec_trunc (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) :
    (ptSecT t.G (x m)).left ≫ (jBaseG x0 d m 1 ▷ t.G).left =
      (ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left ≫ (jBaseG x0 d (m + 1) 1 ▷ t.G).left := by
  unfold ptSecT
  rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left]
  congr 1
  simp only [lift_whiskerRight, comp_lift, Category.id_comp, jBase_trunc]
  rw [show ρT x0 d m ≫ x (m + 1) = x m from hch.trunc m]

end GermD

open GermD in

theorem germSt_holds : GermSt := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x ph1 ph2 sy ad e wP hch hfr hpr htr k Fs
  have hL := t.PP.isLB
  have heL : ∀ m, (eLG t x0 d x act e wP m).IsGen := fun m =>
    ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen t.PP.L _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ hpr.1 _)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ (hfr.gen m) _)
  have hτ : ∀ m, ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y := (jOG x0 d m 1).left) (K := Fin 1) (fun _ => (x m).left)
      fun _ => (k : ℤ)), τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG x0 d m 1).left) (z : Z)
        (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
          val τ r z J = val (genPowG t _ _ (eLG t x0 d x act e wP m) k) r z J := by
    intro m
    refine exists_gen hL ?_ _ (genPowG_isGen t _ _ _ (heL m) k)
    intro U _ hU
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, _root_.mul_one,
      formEq_eL hch m]
    rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
    simp only [← zpow_add, _root_.mul_neg, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  choose τ hτg hτv using hτ
  have hcorr : ∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (τ m) (genPowG t _ _ (eLG t x0 d x act e wP m) k) :=
    fun m => corr_of_val hL fun y J hJ => hτv m _ (𝟙 _) y J hJ
  choose F' hF' using fun m =>
    exists_pullSec t.G t.PP.L (k : ℤ) (jBaseG x0 d m 1 ▷ t.G) (whiskerRight_snd _ _) Fs
  choose v hv using fun m => exists_value t.G t.PP.L hL (k : ℤ) (F' m) (x m) (τ m) (hτg m)
  have hvc : ∀ m, v m = (ρT x0 d m).left.appTop.hom (v (m + 1)) := by
    intro m
    refine fn_ext (V := ⊤) fun y _ => ?_
    obtain ⟨i, hi⟩ := exists_chart hL ((x m).left y)
    have hρx : (ρT x0 d m).left ≫ (x (m + 1)).left = (x m).left := by
      rw [← Over.comp_left, hch.trunc m]
    have hm : (𝟙 _ : (jOG x0 d m 1).left ⟶ _) y ∈ LB.wchart t.PP.L (fun _ : Fin 1 => (x m).left) (fun _ => i) :=
      Set.mem_iInter.2 fun _ => hi
    have app_eq : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C), f ≫ g = h → ∀ a, g (f a) = h a :=
      fun f g h e a => congrArg (fun q => q a) e
    have hps0 : (𝟙 _ ≫ (ptSecT t.G (x m)).left) ≫ (snd (jOG x0 d m 1) t.G).left = (x m).left := by
      rw [Category.id_comp, ← Over.comp_left, ptSecT, lift_snd]
    have hps1 : ((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) ≫ (snd (jOG x0 d (m + 1) 1) t.G).left =
        (x m).left := by
      rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd, hρx]
    have hm1 : (ρT x0 d m).left y ∈ LB.wchart t.PP.L (fun _ : Fin 1 => (x (m + 1)).left) (fun _ => i) := by
      refine Set.mem_iInter.2 fun _ => ?_
      show (x (m + 1)).left ((ρT x0 d m).left y) ∈ (t.PP.L.U i : Set t.G.left)
      rw [app_eq _ _ _ hρx]
      exact hi
    have mem0 : (𝟙 _ ≫ (ptSecT t.G (x m)).left) y ∈ (LPow t.G t.PP.L (k : ℤ) (jOG x0 d m 1)).U (fun _ => i) := by
      refine Set.mem_iInter.2 fun _ => ?_
      show (snd (jOG x0 d m 1) t.G).left ((𝟙 _ ≫ (ptSecT t.G (x m)).left) y) ∈ (t.PP.L.U i : Set t.G.left)
      rw [app_eq _ _ _ hps0]
      exact hi
    have mem1 : ((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) y ∈
        (LPow t.G t.PP.L (k : ℤ) (jOG x0 d (m + 1) 1)).U (fun _ => i) := by
      refine Set.mem_iInter.2 fun _ => ?_
      show (snd (jOG x0 d (m + 1) 1) t.G).left (((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) y) ∈
        (t.PP.L.U i : Set t.G.left)
      rw [app_eq _ _ _ hps1]
      exact hi
    have e0 := value_stalk t.G t.PP.L hL (k : ℤ) (hv m) (𝟙 _) y (fun _ => i) hm
    have e1 := value_stalk t.G t.PP.L hL (k : ℤ) (hv (m + 1)) (ρT x0 d m).left y (fun _ => i) hm1
    have l0 := pullSec_stalk t.G t.PP.L (k : ℤ) (hF' m) (𝟙 _ ≫ (ptSecT t.G (x m)).left) y (fun _ => i) mem0
    have l1 := pullSec_stalk t.G t.PP.L (k : ℤ) (hF' (m + 1)) ((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) y
      (fun _ => i) mem1
    have hmor : (𝟙 _ ≫ (ptSecT t.G (x m)).left) ≫ (jBaseG x0 d m 1 ▷ t.G).left =
        ((ρT x0 d m).left ≫ (ptSecT t.G (x (m + 1))).left) ≫ (jBaseG x0 d (m + 1) 1 ▷ t.G).left := by
      rw [Category.id_comp, ptSec_trunc hch m, Category.assoc]
    obtain ⟨J, hJ, hJi⟩ := exists_good t.PP.L hL y (fun _ : Fin 1 => (x m).left) (fun _ => i) (fun _ _ _ => rfl)
      (fun _ => hi)
    have hunit : gm (𝟙 _) y (LB.wchart t.PP.L (fun _ : Fin 1 => (x m).left) (fun _ => i)) ((τ m).s (fun _ => i)) =
        gm (ρT x0 d m).left y (LB.wchart t.PP.L (fun _ : Fin 1 => (x (m + 1)).left) (fun _ => i))
          ((τ (m + 1)).s (fun _ => i)) :=
      (val_of (τ m) (𝟙 _) y J (fun _ => i) (fun _ => by rw [Category.id_comp]; exact hJi 0)).symm.trans
        ((hτv m _ (𝟙 _) y J hJ).trans ((val_genPowG t _ _ _ k _ y J).trans
          ((congrArg (· ^ k) (val_eL_trunc hch e wP htr m y J hJ)).symm.trans
            ((val_genPowG t _ _ _ k _ y J).symm.trans ((hτv (m + 1) _ _ y J hJ).symm.trans
              (val_of (τ (m + 1)) _ y J (fun _ => i) (fun _ => by rw [hρx]; exact hJi 0)))))))
    have hmain := e0.symm.trans (l0.trans ((congrArg (fun r => gs r y _ (Fs.f (fun _ => i))) hmor).trans
      (l1.symm.trans e1)))
    have h2 := (Units.mul_left_inj (gm (𝟙 _) y _ ((τ m).s (fun _ => i)))).1
      (hmain.trans (congrArg (fun u => gs (ρT x0 d m).left y ⊤ (v (m + 1)) * (u : (_ : Type)ˣ).val) hunit.symm))
    have h3 := gs_pull (𝟙 _) (ρT x0 d m).left y ⊤ (by trivial) (v (m + 1))
    rw [Category.id_comp] at h3
    exact h2.trans h3.symm
  choose a ha using fun m => (⟨_, congrArg (fun f => CommRingCat.Hom.hom f (v m))
    (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin 1 × Fin d) m))))⟩ :
      ∃ b, toΓ (Jet S (Fin 1 × Fin d) m) b = v m)
  have hac : ∀ m, (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _) (a (m + 1)) = a m := by
    intro m
    apply toΓ_injective
    rw [ha m, hvc m, ← ha (m + 1)]
    exact congrArg (fun f => CommRingCat.Hom.hom f (a (m + 1)))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _) :
        Jet S (Fin 1 × Fin d) (m + 1) →+* Jet S (Fin 1 × Fin d) m)))
  obtain ⟨f, hf⟩ := exists_ps_of_jets a hac
  refine ⟨f, fun m => ⟨F' m, τ m, hF' m, hcorr m, ?_⟩⟩
  rw [hf m, ha m]
  exact hv m

end Formalism.MainNotions.ModuliIntegralCharts.H1
