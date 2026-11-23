import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsAbelianSchemePullbackUniversalTriple

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

namespace GlobalTheory.TransportGerm
open GlobalTheory.RegularGerm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

omit [StarRing (𝓞 E)] in
theorem base₁ (y : IntFr Xo c T io) :
    (𝟙 (Sp T.Fr) : (baseOver (Sp T.Fr)).left ⟶ (ptO Xo (xOf y)).left) ≫ (ptO Xo (xOf y)).hom =
      (baseOver (Sp T.Fr)).hom ≫ xOf y := rfl

theorem base₂ (T : CDVR) :
    (spMap (algebraMap T.V T.Fr) : (baseOver (Sp T.Fr)).left ⟶ (baseOver (Sp T.V)).left) ≫ (baseOver (Sp T.V)).hom =
      (baseOver (Sp T.Fr)).hom ≫ spMap (algebraMap T.V T.Fr) :=
  (Category.comp_id _).trans (Category.id_comp _).symm

def RelFibre (C : IntegralChartA3 Xo c T io y) {k : ℕ} (s : LB.Sec (LPow C.I.t'.G C.I.t'.PP.L (k : ℤ) (baseOver (Sp T.Fr))))
    (F : SecN Xo (xOf y) k) : Prop :=
  ThetaPtMove.SecRel (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) C.I.w1 s F

def RelModel (C : IntegralChartA3 Xo c T io y) {k : ℕ} (s : LB.Sec (LPow C.I.t'.G C.I.t'.PP.L (k : ℤ) (baseOver (Sp T.Fr))))
    (σ : LB.Sec (LPow C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V)))) : Prop :=
  ThetaPtMove.SecRel C.I.m2.cart
      (T := baseOver (Sp T.Fr)) (T₀ := baseOver (Sp T.V)) (spMap (algebraMap T.V T.Fr)) (base₂ T) C.I.w2 s σ

set_option maxHeartbeats 1600000 in

theorem germIs_of_rel (hFT : ReciprocityTheory.ChartRestriction.G.PullbackSections.FrameTieSt Xo c) (C : IntegralChartA3 Xo c T io y) {k : ℕ}
    {s : LB.Sec (LPow C.I.t'.G C.I.t'.PP.L (k : ℤ) (baseOver (Sp T.Fr)))} {F : SecN Xo (xOf y) k}
    {σ : LB.Sec (LPow C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V)))} (h₁ : RelFibre C s F) (h₂ : RelModel C s σ)
    {g : PS T.V 1 (chD C.ch)} (hg : IsGermG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.actT C.eT C.wPT k σ g) :
    GermIs C k F g := by
  letI := io.toAlgebra
  obtain ⟨x', hx1, hx2, eL', heL'⟩ := hFT T io y C
  refine (isGerm_iff y.1 _ _ _ _ _ _ _ _).2
    (isGerm_of_sv ((isChart_iff y.1 _ _ _ _ _).1 C.ch.chart) C.ch.prim.1 C.ch.frame.gen fun m z J hJ => ?_)
  obtain ⟨J', hJ', -⟩ := exists_good C.I.t'.PP.L C.I.t'.PP.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  obtain ⟨J'', hJ'', -⟩ := exists_good C.I.G.PP.L C.I.G.PP.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  let ρ : Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) ⟶ Sp (Jet T.V (Fin 1 × Fin (chD C.ch)) m) :=
    spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin (chD C.ch)) m)
  let i : Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) ⟶ Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) := 𝟙 _
  obtain ⟨f₁, f₂⟩ := heL' m _ i z J J' J'' hJ hJ' hJ''
  have a₁ := h₁ _ (i ≫ jetPt (x' m)) z J J' hJ hJ'
  have a₂ := h₂ _ (i ≫ jetPt (x' m)) z J'' J' hJ'' hJ'
  have a₃ := sv_of_isGerm hg m (i ≫ ρ) z hJ''
  have e₀ : (i ≫ jetPt (x' m)) ≫ (snd (baseOver (Sp T.Fr)) C.I.t'.G).left = i ≫ (x' m).left :=
    (Category.assoc _ _ _).trans (congrArg (i ≫ ·) (jetPt_snd (x' m)))
  have e₁ : (i ≫ jetPt (x' m)) ≫ ThetaPtMove.psi (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) = i ≫ jetPt (C.ch.x m) := by
    refine (Category.assoc _ _ _).trans (congrArg (i ≫ ·) (ThetaPtMove.psi_ext ?_ ?_))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_fst' _ _ _)).trans
        ((congrArg (_ ≫ ·) (Category.comp_id _)).trans ((jetPt_fst (x' m)).trans (jetPt_fst (C.ch.x m)).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (jetPt_snd (x' m))).trans
          ((hx1 m).trans (jetPt_snd (C.ch.x m)).symm))))
  have e₂ : (i ≫ jetPt (x' m)) ≫ ThetaPtMove.psi C.I.m2.cart
      (T := baseOver (Sp T.Fr)) (T₀ := baseOver (Sp T.V)) (spMap (algebraMap T.V T.Fr)) (base₂ T) = (i ≫ ρ) ≫ jetPt (C.xT m) := by
    refine (Category.assoc _ _ _).trans ((congrArg (i ≫ ·) (ThetaPtMove.psi_ext ?_ ?_)).trans
      (Category.assoc _ _ _).symm)
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_fst' _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (jetPt_fst (x' m))).trans
          (Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (ρ ≫ ·) (jetPt_fst (C.xT m)))).symm))))
      have q := congrArg (· ≫ C.I.G.G.hom) (hx2 m)
      have q₁ : (x' m).left ≫ C.I.t'.G.hom = spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m)) :=
        (Over.w (x' m)).trans (Category.comp_id _)
      have q₂ : (C.xT m).left ≫ C.I.G.G.hom = spMap (algebraMap T.V (Jet T.V (Fin 1 × Fin (chD C.ch)) m)) :=
        (Over.w (C.xT m)).trans (Category.comp_id _)
      exact (congrArg (· ≫ _) q₁).symm.trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) C.I.m2.cart.1.w.symm).trans ((Category.assoc _ _ _).symm.trans
          (q.trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) q₂))))))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (jetPt_snd (x' m))).trans
          ((hx2 m).trans ((Category.assoc _ _ _).trans (congrArg (ρ ≫ ·) (jetPt_snd (C.xT m)))).symm))))
  rw [e₀, e₁, zpow_natCast, Units.val_pow_eq_pow_val] at a₁
  rw [e₀, e₂, zpow_natCast, Units.val_pow_eq_pow_val] at a₂
  rw [Category.comp_id] at f₁ f₂
  refine (tie_alg a₁ a₂ a₃ f₁ f₂).trans (congrArg₂ (· * ·) ?_ rfl)
  rw [psJet_map]
  exact gs_spMap_toΓ _ i z _

set_option maxHeartbeats 800000 in

theorem exists_rel (C : IntegralChartA3 Xo c T io y) {k : ℕ} {F : SecN Xo (xOf y) k} (hF : Regular C k F) :
    ∃ s σ, RelFibre C s F ∧ RelModel C s σ := by
  letI := io.toAlgebra
  obtain ⟨σ, σt, hT1, hT2⟩ := hF
  obtain ⟨σ', hσ'⟩ := exists_sec_id C.I.G (k : ℤ) σ (baseOver (Sp T.V))
  obtain ⟨s, hs⟩ := exists_sec_id C.I.t' (k : ℤ) σt (baseOver (Sp T.Fr))
  refine ⟨s, σ', fun Z r z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · have q := hT1 Z (r ≫ (snd (baseOver (Sp T.Fr)) C.I.t'.G).left)
      (r ≫ ThetaPtMove.psi (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y))
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans
        (Category.assoc _ _ _).symm))
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((ThetaPtMove.psi_fst' _ _ _).trans
        ((Over.w (fst (baseOver (Sp T.Fr)) C.I.t'.G)).trans (Over.w (snd (baseOver (Sp T.Fr)) C.I.t'.G)).symm))).trans
          (Category.assoc _ _ _).symm)) z J J' hJ hJ'
    rw [Category.comp_id, ← hs Z r z J' hJ'] at q
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
    exact q
  · have q := hT2 Z (r ≫ (snd (baseOver (Sp T.Fr)) C.I.t'.G).left) z J J' hJ hJ'
    rw [Category.comp_id, ← hs Z r z J' hJ'] at q
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
    refine (hσ' Z _ z J hJ).trans (Eq.trans (congrArg (fun p => sval σ p z J) ?_) q)
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ThetaPtMove.psi_snd' _ _ _)).trans
      (Category.assoc _ _ _).symm)

set_option maxHeartbeats 800000 in

theorem germIs_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (k : ℕ), Odd k → ∀ (a : ptO Xo (xOf y) ⟶ Xo.univ.t.G) (aV : baseOver (Sp T.V) ⟶ C.I.G.G) (r : Sp T.Fr ⟶ C.I.t'.G.left), r ≫ C.I.t'.G.hom = 𝟙 _ → r ≫ C.I.m1.φ = a.left → r ≫ C.I.m2.φ = spMap (algebraMap T.V T.Fr) ≫ aV.left → ∀ U : ThetaGrp C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V)), SymLift C.I.G.G C.I.G.PP.L (k : ℤ) k aV U → ∀ (F F' : SecN Xo (xOf y) k) (f f' : PS T.V 1 (chD C.ch)), Regular C k F → GermIs C k F f → Moves Xo a F F' → (∀ σ σ' : LB.Sec (LPow C.I.G.G C.I.G.PP.L (k : ℤ) (baseOver (Sp T.V))), IsGermG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.actT C.eT C.wPT k σ f → IsActOf C.I.G.G C.I.G.PP.L (k : ℤ) U σ σ' → IsGermG C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.actT C.eT C.wPT k σ' f') → GermIs C k F' f' := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hC k hk a aV r hr hr1 hr2 U hU F F' f f' hF hf hM hyp
  letI := io.toAlgebra
  have hFT := GlobalTheory.PlaceInt.frameTie_holds E H Dw l Xo c hstar
  have hA : IsAbelianScheme C.I.t'.G := isAbelianScheme_of_pullback_univ E H Dw l Xo _ C.I.t' _ C.I.m1
  obtain ⟨hak, U₀, hU₀, hact⟩ := hM
  obtain ⟨s, σ, h₁, h₂⟩ := exists_rel C hF
  obtain ⟨g, hg⟩ := germSt_holds E H (Sp T.V) C.I.G T.V (𝟙 _) (chD C.ch) C.FT C.actT
    (Fin (chD C.ch)) C.tgT (fun j => Pi.single j (1 : T.V)) C.xT C.ph1T C.ph2T C.syT C.adT C.eT C.wPT
    C.chartT C.frameT C.primT hC k σ
  obtain rfl : g = f := germIs_unique C k F _ _ (germIs_of_rel hFT C h₁ h₂ hg) hf
  obtain ⟨σ', hσ', -⟩ := existsUnique_isTwistPull _ _ _ C.I.G.PP.isLB _ (translT _ U.pt) (translPt _ U.pt)
    (lift_snd _ _) k k U.φ U.isGen σ
  let x : baseOver (Sp T.Fr) ⟶ C.I.t'.G := Over.homMk r hr
  have hx₁ : (𝟙 (Sp T.Fr) : (baseOver (Sp T.Fr)).left ⟶ (ptO Xo (xOf y)).left) ≫ a.left = x.left ≫ C.I.m1.φ :=
    (Category.id_comp _).trans hr1.symm
  have hx₂ : (spMap (algebraMap T.V T.Fr) : (baseOver (Sp T.Fr)).left ⟶ (baseOver (Sp T.V)).left) ≫ aV.left =
      x.left ≫ C.I.m2.φ := hr2.symm
  have hn : x ^ k = 1 := by
    refine Over.OverMorphism.ext (C.I.m1.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have p := ThetaPtMove.over_pow (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) hx₁ k
    rw [hak] at p
    exact p.symm.trans (ThetaPtMove.over_one (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y))
  obtain ⟨θ₁, l₁, m₁⟩ := ThetaPtMove.symLift_move (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) C.I.rig1.1
    Xo.univ.t.PP.isLB C.I.t'.PP.isLB hx₁ hn hU₀
  obtain ⟨θ₂, l₂, m₂⟩ := ThetaPtMove.symLift_move C.I.m2.cart
      (T := baseOver (Sp T.Fr)) (T₀ := baseOver (Sp T.V)) (spMap (algebraMap T.V T.Fr)) (base₂ T) C.I.rig2.1
    C.I.G.PP.isLB C.I.t'.PP.isLB hx₂ hn hU
  obtain ⟨s₁, r₁⟩ := ThetaPtMove.exists_secRel (f := xOf y) C.I.m1.cart
      (T := baseOver (Sp T.Fr)) (T₀ := ptO Xo (xOf y)) (𝟙 (Sp T.Fr)) (base₁ y) C.I.rig1.1
    Xo.univ.t.PP.isLB C.I.t'.PP.isLB F'
  obtain ⟨s₂, r₂⟩ := ThetaPtMove.exists_secRel C.I.m2.cart
      (T := baseOver (Sp T.Fr)) (T₀ := baseOver (Sp T.V)) (spMap (algebraMap T.V T.Fr)) (base₂ T) C.I.rig2.1
    C.I.G.PP.isLB C.I.t'.PP.isLB σ'
  obtain rfl : s₁ = s₂ := SymMove.act_unique firstFiveLaws.1.globalFns hA C.I.t'.PP.isLB hk l₁ l₂
    (m₁ _ _ _ _ h₁ r₁ hact) (m₂ _ _ _ _ h₂ r₂ hσ')
  exact germIs_of_rel hFT C r₁ r₂ (hyp σ σ' hg hσ')

end GlobalTheory.TransportGerm
