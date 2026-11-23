import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.SymmetricAdjointUnits
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
open MvPolynomial (X)

section Gen

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_iff (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) :
    LB.Gen.Corr L φ ε φ' ε' t t' ↔ ∀ y J, Good L y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J :=
  ⟨fun h _ _ hJ => val_corr hJ h _, corr_of_val hL⟩

theorem val_unitGen {B : Type} [CommRing B] (u : Bˣ) (r : Z ⟶ Sp B) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (unitGen L u) r z J = gm r z ⊤ (unitΓ u) :=
  gm_res r z le_top (hJ.mem (PEmpty.elim : PEmpty → (Sp B ⟶ X)) r) _

def genIso (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Gen (LB.LinComb L (K := K' ⊕ K) (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k))) :
    LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') where
  s := fun p => res (fun _ hy => Set.mem_iInter.2 fun k => by
      rcases k with k | k
      exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k] :
    LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2 ≤ LB.wchart L (Sum.elim φ' φ) (Sum.elim p.1 p.2)) (w.s (Sum.elim p.1 p.2))

theorem isoGen_genIso (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Gen (LB.LinComb L (K := K' ⊕ K) (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k))) :
    isoGen L φ ε φ' ε' (genIso φ ε φ' ε' w) = w := by
  have key : ∀ (j j' : K' ⊕ K → L.ι) (y : Y), j = j' →
      gm (𝟙 Y) y (LB.wchart L (Sum.elim φ' φ) j) (w.s j) = gm (𝟙 Y) y (LB.wchart L (Sum.elim φ' φ) j') (w.s j') := by
    rintro j _ y rfl; rfl
  refine congrArg LB.Gen.mk (funext fun j => unit_ext fun y hy => ?_)
  have h2 : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) :=
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩
  exact (gm_res _ y _ hy _).trans ((gm_res _ y _ h2 _).trans (key _ _ y (Sum.elim_comp_inl_inr j)))

theorem genIso_isoGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    genIso φ ε φ' ε' (isoGen L φ ε φ' ε' w) = w := by
  refine congrArg LB.Gen.mk (funext fun p => unit_ext fun y hy => ?_)
  have h2 : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (Sum.elim φ' φ) (Sum.elim p.1 p.2) := Set.mem_iInter.2 fun k => by
    rcases k with k | k
    exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k]
  exact (gm_res _ y _ hy _).trans (gm_res _ y _ h2 _)

def isoEquiv (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ≃
      LB.Gen (LB.LinComb L (K := K' ⊕ K) (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)) :=
  ⟨isoGen L φ ε φ' ε', genIso φ ε φ' ε', genIso_isoGen φ ε φ' ε', isoGen_genIso φ ε φ' ε'⟩

theorem genIso_isGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Gen (LB.LinComb L (K := K' ⊕ K) (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k))) (hw : w.IsGen) :
    (genIso φ ε φ' ε' w).IsGen := fun p q => unit_ext fun y hy => by
  have le : ∀ p : (K' → L.ι) × (K → L.ι), LB.wchart L φ' p.1 ⊓ LB.wchart L φ p.2 ≤
      LB.wchart L (Sum.elim φ' φ) (Sum.elim p.1 p.2) := fun p _ hy => Set.mem_iInter.2 fun k => by
    rcases k with k | k
    exacts [Set.mem_iInter.1 hy.1 k, Set.mem_iInter.1 hy.2 k]
  have h := gen_trans hw (𝟙 Y) y (le p hy.1) (le q hy.2)
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans (h.trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (GermB.gm_divLC L φ' ε' φ ε p q y hy.1 hy.2)
      ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm)))
  refine congrArg₂ (· * ·) ?_ rfl
  rw [trF, Fintype.prod_sum_type]
  simp only [trF, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

theorem isoGen_isGen_iff (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (w : LB.Iso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) : (isoGen L φ ε φ' ε' w).IsGen ↔ w.IsGen :=
  ⟨fun h => by simpa only [genIso_isoGen] using genIso_isGen φ ε φ' ε' _ h, GermB.divLin_isGen L φ' ε' φ ε w⟩

end Gen

section Jets

variable {S : Type} [CommRing S] {d : ℕ}

theorem jetSubstP_congr {κ κ' : Type} (m : ℕ) {φ ψ : κ → MvPolynomial κ' S}
    (h : ∀ s, (Ideal.Quotient.mk _ (φ s) : Jet S κ' m) = Ideal.Quotient.mk _ (ψ s)) : jetSubstP m φ = jetSubstP m ψ :=
  jet_hom_ext fun s => by
    have aug : ∀ P : MvPolynomial κ' S, (jetAug : Jet S κ' m →ₐ[S] S) (Ideal.Quotient.mk _ P) =
        MvPolynomial.constantCoeff P := fun P => by
      show MvPolynomial.aeval (fun _ => (0 : S)) P = _
      rw [MvPolynomial.aeval_zero']; rfl
    have hc : MvPolynomial.constantCoeff (φ s) = MvPolynomial.constantCoeff (ψ s) := by rw [← aug, ← aug, h]
    rw [jetSubstP, jetSubstP, jetMap_mk, jetMap_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X, map_sub, map_sub, h, hc]

theorem subst2_eq {n : ℕ} (m : ℕ) (a b : Pt S n d) (φ ψ : Fin d → MvPolynomial (Fin n × Fin d) S)
    (ha : ∀ i, (Ideal.Quotient.mk _ (φ i) : Jet S (Fin n × Fin d) m) = psJet m (a i))
    (hb : ∀ i, (Ideal.Quotient.mk _ (ψ i) : Jet S (Fin n × Fin d) m) = psJet m (b i)) :
    subst2 m a b = jetSubstP m fun p : Fin 2 × Fin d => (![φ, ψ] : Fin 2 → _) p.1 p.2 :=
  jetSubstP_congr m (φ := fun p : Fin 2 × Fin d => psTrunc m ((![a, b] : Fin 2 → Pt S n d) p.1 p.2)) (by
    rintro ⟨l, i⟩
    fin_cases l
    exacts [(ha i).symm, (hb i).symm])

theorem mk_X {n : ℕ} (m : ℕ) (k : Fin n) (i : Fin d) :
    (Ideal.Quotient.mk _ (X (k, i)) : Jet S (Fin n × Fin d) m) = psJet m (pt S d k i) := (psJet_X m _).symm

theorem mk_zero {n : ℕ} (m : ℕ) (i : Fin d) :
    (Ideal.Quotient.mk _ 0 : Jet S (Fin n × Fin d) m) = psJet m ((0 : Pt S n d) i) :=
  (map_zero _).trans (psJet_zero m).symm

theorem mk_add {n : ℕ} (m : ℕ) (F : Fin d → PS S 2 d) (k k' : Fin n) (i : Fin d) :
    (Ideal.Quotient.mk _ (psIn d m ![k, k'] (F i)) : Jet S (Fin n × Fin d) m) =
      psJet m (Germ.addOf F (pt S d k) (pt S d k') i) :=
  (mk_psIn m _ _).trans (congrArg (psJet m) ((sb_apply _ _).trans
    (congrArg (ev · (F i)) (funext fun l => by fin_cases l <;> rfl))))

theorem mk_comp {n : ℕ} (m : ℕ) (A : Pt S 1 d) (k : Fin n) (i : Fin d) :
    (Ideal.Quotient.mk _ (psIn d m ![k] (A i)) : Jet S (Fin n × Fin d) m) = psJet m (Germ.comp1 A (pt S d k) i) :=
  (mk_psIn m _ _).trans (congrArg (psJet m) ((sb_apply _ _).trans
    (congrArg (ev · (A i)) (funext fun l => by fin_cases l; rfl))))

end Jets

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {d : ℕ}

def ptsOf (j : JetPts t.G x0 d) : ∀ m, jOG x0 d m 1 ⟶ t.G := fun m => jPt t.G x0 j 1 m 0

def ptsEquiv : JetPts t.G x0 d ≃ ∀ m, jOG x0 d m 1 ⟶ t.G where
  toFun := ptsOf t x0
  invFun := fun x m => homAt x0 (jetMap (fun p : Fin 1 × Fin d => X p.2) fun _ => X_mem_orig _) ≫ x m
  left_inv := fun j => funext fun m => by
    show homAt x0 _ ≫ homAt x0 _ ≫ j m = j m
    rw [← Category.assoc, homAt_comp]
    have : (jetMap (fun p : Fin 1 × Fin d => X p.2) fun _ => X_mem_orig _ :
        Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin d) m).comp (jetIn (0 : Fin 1)) = AlgHom.id S _ :=
      jet_hom_ext fun s => by
        rw [AlgHom.comp_apply, jetIn, jetMap_mk, MvPolynomial.aeval_X, jetMap_mk, MvPolynomial.aeval_X]; rfl
    rw [this]
    exact (congrArg (· ≫ j m) (Over.OverMorphism.ext (Spec.map_id _) : homAt x0 (AlgHom.id S _) = 𝟙 _)).trans
      (Category.id_comp _)
  right_inv := fun x => funext fun m => by
    show homAt x0 _ ≫ homAt x0 _ ≫ x m = x m
    rw [← Category.assoc, homAt_comp]
    have : (jetIn (0 : Fin 1) : Jet S (Fin d) m →ₐ[S] _).comp
        (jetMap (fun p : Fin 1 × Fin d => X p.2) fun _ => X_mem_orig _) = AlgHom.id S _ :=
      jet_hom_ext fun s => by
        obtain ⟨k, s⟩ := s
        obtain rfl := Subsingleton.elim k 0
        rw [AlgHom.comp_apply, jetIn, jetMap_mk, MvPolynomial.aeval_X, jetMap_mk, MvPolynomial.aeval_X]; rfl
    rw [this]
    exact (congrArg (· ≫ x m) (Over.OverMorphism.ext (Spec.map_id _) : homAt x0 (AlgHom.id S _) = 𝟙 _)).trans
      (Category.id_comp _)

theorem jptG_ptsOf (j : JetPts t.G x0 d) {n : ℕ} (m : ℕ) (k : Fin n) :
    jptG t x0 d (ptsOf t x0 j) m k = jPt t.G x0 j n m k := by
  show homAt x0 _ ≫ homAt x0 _ ≫ j m = homAt x0 _ ≫ j m
  rw [← Category.assoc, homAt_comp]
  refine congrArg (fun g => homAt x0 g ≫ j m) (jet_hom_ext fun s => ?_)
  rw [AlgHom.comp_apply, jetIn, jetIn, jetCopy, jetMap_mk, MvPolynomial.aeval_X, jetMap_mk, MvPolynomial.aeval_X,
    jetMap_mk, MvPolynomial.aeval_X]

theorem pair_eq (j : JetPts t.G x0 d) (m : ℕ) : jPt t.G x0 j 2 m =
    ![jptG t x0 d (ptsOf t x0 j) m (0 : Fin 2), jptG t x0 d (ptsOf t x0 j) m (1 : Fin 2)] :=
  funext fun k => by fin_cases k <;> exact (jptG_ptsOf t x0 j m _).symm

def castGen {T : Over X0} {p q : Fin 2 → (T ⟶ t.G)} (h : p = q) :
    LB.Gen (cubeLB t.G p t.PP.L) ≃ LB.Gen (cubeLB t.G q t.PP.L) :=
  Equiv.cast (congrArg (fun p => LB.Gen (cubeLB t.G p t.PP.L)) h)

theorem castGen_isGen {T : Over X0} {p q : Fin 2 → (T ⟶ t.G)} (h : p = q) (g : LB.Gen (cubeLB t.G p t.PP.L)) :
    (castGen t h g).IsGen ↔ g.IsGen := by subst h; rfl

theorem val_castGen {T : Over X0} {p q : Fin 2 → (T ⟶ t.G)} (h : p = q) (g : LB.Gen (cubeLB t.G p t.PP.L))
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) :
    val (L := t.PP.L) (φ := cφG t q) (ε := cε 2) (castGen t h g) r z J =
      val (L := t.PP.L) (φ := lamφ t.G p) (ε := lamε) g r z J := by subst h; rfl

attribute [irreducible] castGen

def frEquiv (j : JetPts t.G x0 d) : FrameFam t.G x0 t.PP.L j ≃ ∀ m, FrTyG t x0 d (ptsOf t x0 j) m where
  toFun := fun e m => castGen t (pair_eq t x0 j m) (e m)
  invFun := fun e m => (castGen t (pair_eq t x0 j m)).symm (e m)
  left_inv := fun e => funext fun m => (castGen t (pair_eq t x0 j m)).symm_apply_apply (e m)
  right_inv := fun e => funext fun m => (castGen t (pair_eq t x0 j m)).apply_symm_apply (e m)

theorem frEquiv_apply (j : JetPts t.G x0 d) (e : FrameFam t.G x0 t.PP.L j) (m : ℕ) :
    frEquiv t x0 j e m = castGen t (pair_eq t x0 j m) (e m) := rfl

variable {t x0} {j : JetPts t.G x0 d} (e : FrameFam t.G x0 t.PP.L j)

theorem val_frEquiv (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (jOG x0 d m 2).left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) :
    val (L := t.PP.L) (φ := cφG t ![jptG t x0 d (ptsOf t x0 j) m (0 : Fin 2), jptG t x0 d (ptsOf t x0 j) m (1 : Fin 2)])
      (ε := cε 2) (frEquiv t x0 j e m) r z J =
      val (L := t.PP.L) (φ := lamφ t.G (jPt t.G x0 j 2 m)) (ε := lamε) (e m) r z J := by
  rw [frEquiv_apply]
  exact val_castGen t (pair_eq t x0 j m) (e m) r z J

theorem val_frAt {n : ℕ} (m : ℕ) (a b : Pt S n d) (φ ψ : Fin d → MvPolynomial (Fin n × Fin d) S)
    (ha : ∀ i, (Ideal.Quotient.mk _ (φ i) : Jet S (Fin n × Fin d) m) = psJet m (a i))
    (hb : ∀ i, (Ideal.Quotient.mk _ (ψ i) : Jet S (Fin n × Fin d) m) = psJet m (b i))
    {Z : Scheme.{0}} (r : Z ⟶ (jOG x0 d m n).left) {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) :
    val (peG t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) m ![φ, ψ]) r z J = val (frAt e m a b) r z J := by
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  rw [subst2_eq m a b φ ψ ha hb]
  exact val_frEquiv e m _ z J

theorem val_scale' {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) :
    val (scaleGenG t φ ε u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) u) rfl)

theorem val_cub' {T : Over X0} (a b c : T ⟶ t.G) {z : T.left} {J : (T.left ⟶ t.G.left) → t.PP.L.ι}
    (hJ : Good t.PP.L z J) :
    val (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift a (lift b c)).left) (𝟙 T.left) z J =
      cubV t.cub z J a b c :=
  (val_cub t.cub (𝟙 T) hJ a b c).trans (by simp only [Category.id_comp])

theorem gen_iff : (∀ m, (e m).IsGen) ↔ ∀ m, (frEquiv t x0 j e m).IsGen :=
  forall_congr' fun m => by rw [frEquiv_apply]; exact (castGen_isGen t (pair_eq t x0 j m) (e m)).symm

theorem isFrame_iff : IndefiniteRowSideFullHecke.RigidAdjointFrameLaws.IsFrame e ↔ (∀ m, (frEquiv t x0 j e m).IsGen) ∧
    FrTrunc t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) ∧ FrAxes t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) := by
  have hL := t.PP.isLB
  refine and_congr (gen_iff e) (and_congr (forall_congr' fun m => ?_) ?_)
  · refine (corr_iff hL _ _).trans (Iff.trans (forall₃_congr fun y J hJ => ?_) (corr_iff hL _ _).symm)
    exact Eq.congr ((val_pull hJ _ _ _).trans ((val_pull hJ _ _ _).trans (val_frEquiv e (m + 1) _ y J)).symm)
      (val_frEquiv e m _ y J).symm
  · refine forall_and.symm.trans (forall_congr' fun m => and_congr ?_ ?_)
    · refine (corr_iff hL _ _).trans (Iff.trans (forall₃_congr fun y J hJ => ?_) (corr_iff hL _ _).symm)
      exact Eq.congr (val_frAt e m _ _ _ _ (mk_zero m) (mk_X m 0) _ hJ).symm rfl
    · refine (corr_iff hL _ _).trans (Iff.trans (forall₃_congr fun y J hJ => ?_) (corr_iff hL _ _).symm)
      exact Eq.congr (val_frAt e m _ _ _ _ (mk_X m 0) (mk_zero m) _ hJ).symm rfl

section Clauses

variable (t x0 d) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (e' : ∀ m, FrTyG t x0 d x m)

def Ph1Clause (F : Fin d → PS S 2 d) (ph1 : PS S 3 d) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph1 ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
        (lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left)
      (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _
        (peG t x0 d x e' m ![fun j => psIn d m ![0, 1] (F j), fun j => X ((2 : Fin 3), j)])
        (LB.mulGen t.PP.L _ _ _ _
          (LB.invGen t.PP.L _ _ (peG t x0 d x e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))
          (LB.invGen t.PP.L _ _ (peG t x0 d x e' m ![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))

def Ph2Clause (F : Fin d → PS S 2 d) (ph2 : PS S 3 d) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t
        (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left)
      (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _
        (peG t x0 d x e' m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)])
        (LB.mulGen t.PP.L _ _ _ _
          (LB.invGen t.PP.L _ _ (peG t x0 d x e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)]))
          (LB.invGen t.PP.L _ _ (peG t x0 d x e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))

def SyClause (sy : PS S 2 d) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (e' m)
      (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e' m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))

abbrev AdTy (a : 𝓞 E) : Type :=
  LB.Gen (LB.LinComb t.PP.L
    (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
      (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
    (Sum.elim (cε 2) fun I => -cε 2 I))

def AdClause (act : 𝓞 E → Pt S 1 d) (a : 𝓞 E) (wL : AdTy t a) (ad : PS S 2 d) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m ad ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.mulGen t.PP.L _ _ _ _
        (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
        (peG t x0 d x e' m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)]))
      (scaleGenG t _ _ (unitΓ u)
        (peG t x0 d x e' m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))

def AdRigid (a : 𝓞 E) (wL : AdTy t a) : Prop :=
  LB.Gen.Corr t.PP.L _ _ (Y := t.G.left) _ _
      (LB.pullGen t.PP.L _ _ wL (lift (𝟙 t.G) (1 : t.G ⟶ t.G)).left) (LB.oneGen t.PP.L) ∧
    LB.Gen.Corr t.PP.L _ _ (Y := t.G.left) _ _
      (LB.pullGen t.PP.L _ _ wL (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L)

set_option maxHeartbeats 1000000 in

theorem isFrameG_iff (F : Fin d → PS S 2 d) (act : 𝓞 E → Pt S 1 d) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d)
    (ad : 𝓞 E → PS S 2 d) : IsFrameG t x0 d x F act ph1 ph2 sy ad e' ↔
      (∀ m, (e' m).IsGen) ∧ Ph1Clause t x0 d x e' F ph1 ∧ Ph2Clause t x0 d x e' F ph2 ∧ SyClause t x0 d x e' sy ∧
        ∀ a, ∃ wL : AdTy t a, wL.IsGen ∧ AdClause t x0 d x e' act a wL (ad a) :=
  ⟨fun h => ⟨h.gen, h.ph1, h.ph2, h.sy, h.ad⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

end Clauses

theorem law_alg {U : Type} [CommGroup U] (a b c u f : U) : a * b * c = u * f ↔ c = u * (f * (a⁻¹ * b⁻¹)) := by
  rw [← mul_inv, ← _root_.mul_assoc, eq_mul_inv_iff_mul_eq, mul_comm c]

theorem first_cubical_law_iff_clause (F : Fin d → PS S 2 d) (ph1 : PS S 3 d) :
    FrameFamilyFirstCubicLaw t.cub e F ph1 ↔ Ph1Clause t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) F ph1 := by
  have hL := t.PP.isLB
  refine forall_congr' fun m => exists_congr fun u => and_congr_right fun _ => ?_
  refine (corr_iff hL _ _).trans (Iff.trans (forall₃_congr fun y J hJ => ?_) (corr_iff hL _ _).symm)
  refine (Eq.congr ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) (val_cub' _ _ _ hJ)))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_unitGen u _ hJ) rfl))).trans ((law_alg _ _ _ _ _).trans
    (Eq.congr ((val_cub' _ _ _ hJ).trans ?_) ((val_scale' _ _ _ hJ).trans (congrArg₂ (· * ·) rfl
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_frAt e m _ _ _ _ (mk_add m F 0 1) (mk_X m 2) _ hJ)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
          ((val_inv _ _).trans (congrArg (·⁻¹) (val_frAt e m _ _ _ _ (mk_X m 0) (mk_X m 2) _ hJ)))
          ((val_inv _ _).trans (congrArg (·⁻¹) (val_frAt e m _ _ _ _ (mk_X m 1) (mk_X m 2) _ hJ)))))))))).symm)
  rw [jptG_ptsOf, jptG_ptsOf, jptG_ptsOf]

theorem second_cubical_law_iff_clause (F : Fin d → PS S 2 d) (ph2 : PS S 3 d) :
    FrameFamilySecondCubicLaw t.cub e F ph2 ↔ Ph2Clause t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) F ph2 := by
  have hL := t.PP.isLB
  refine forall_congr' fun m => exists_congr fun u => and_congr_right fun _ => ?_
  refine (corr_iff hL _ _).trans (Iff.trans (forall₃_congr fun y J hJ => ?_) (corr_iff hL _ _).symm)
  refine (Eq.congr ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) (val_cub' _ _ _ hJ)))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_unitGen u _ hJ) rfl))).trans ((law_alg _ _ _ _ _).trans
    (Eq.congr ((val_cub' _ _ _ hJ).trans ?_) ((val_scale' _ _ _ hJ).trans (congrArg₂ (· * ·) rfl
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_frAt e m _ _ _ _ (mk_X m 0) (mk_add m F 1 2) _ hJ)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
          ((val_inv _ _).trans (congrArg (·⁻¹) (val_frAt e m _ _ _ _ (mk_X m 0) (mk_X m 1) _ hJ)))
          ((val_inv _ _).trans (congrArg (·⁻¹) (val_frAt e m _ _ _ _ (mk_X m 0) (mk_X m 2) _ hJ)))))))))).symm)
  have C := isCub_cubV t.cub (T := jOG x0 d m 3) hJ
  rw [jptG_ptsOf, jptG_ptsOf, jptG_ptsOf]
  exact (C.s12 _ _ _).trans (C.s01 _ _ _)

theorem sym_iff (sy : PS S 2 d) : SymIs e sy ↔ SyClause t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) sy := by
  have hL := t.PP.isLB
  refine forall_congr' fun m => exists_congr fun u => and_congr_right fun _ => ?_
  refine (corr_iff hL _ _).trans (Iff.trans (forall₃_congr fun y J hJ => ?_) (corr_iff hL _ _).symm)
  refine (Eq.congr rfl ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_unitGen u _ hJ) rfl))).trans
    (Iff.trans ?_ (Eq.congr (val_frEquiv e m _ y J) ((val_scale' _ _ _ hJ).trans (congrArg₂ (· * ·)
      ((congrArg _ (map_inv (Units.map (toΓ _).toMonoidHom) u)).trans (map_inv _ _))
      (val_frAt e m _ _ _ _ (mk_X m 1) (mk_X m 0) _ hJ)))).symm)
  exact eq_comm.trans eq_inv_mul_iff_mul_eq.symm

def adEquiv (a : 𝓞 E) : LB.Iso (cubeLB t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] t.PP.L)
    (cubeLB t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] t.PP.L) ≃ AdTy t a :=
  isoEquiv (L := t.PP.L) (lamφ t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) lamε
    (lamφ t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) lamε

theorem adjVia_iff (A : 𝓞 E → Pt S 1 d) (a : 𝓞 E)
    (w : LB.Iso (cubeLB t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] t.PP.L)
      (cubeLB t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] t.PP.L)) (ad : PS S 2 d) :
    AdjVia e w (A a) (A (H.bar a)) ad ↔
      AdClause t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) A a (adEquiv a w) ad := by
  have hL := t.PP.isLB
  refine forall_congr' fun m => exists_congr fun u => and_congr_right fun _ => ?_
  refine (corr_iff hL _ _).trans (Iff.trans (forall₃_congr fun y J hJ => ?_) (corr_iff hL _ _).symm)
  refine Eq.congr ((val_mul hJ _ _ _).trans (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _)
      (val_frAt e m _ _ _ _ (mk_comp m (A a) 0) (mk_X m 1) _ hJ))).symm))
    (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_unitGen u _ hJ) rfl)).trans ((val_scale' _ _ _ hJ).trans
      (congrArg₂ (· * ·) rfl (val_frAt e m _ _ _ _ (mk_X m 0) (mk_comp m (A (H.bar a)) 1) _ hJ))).symm)
  refine congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans ?_) rfl
  rw [jptG_ptsOf, jptG_ptsOf]
  rfl

theorem isRigAdj_iff (a : 𝓞 E) (w : LB.Iso (cubeLB t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] t.PP.L)
      (cubeLB t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] t.PP.L)) :
    IsRigAdj t.G t.PP.L (t.act.act a) (t.act.act (H.bar a)) w ↔ (adEquiv a w).IsGen ∧ AdRigid t a (adEquiv a w) :=
  and_congr (isoGen_isGen_iff (L := t.PP.L) (lamφ t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) lamε
    (lamφ t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) lamε w).symm Iff.rfl

theorem adj_iff (A : 𝓞 E → Pt S 1 d) (a : 𝓞 E) (ad : PS S 2 d) :
    AdjIs e (t.act.act a) (t.act.act (H.bar a)) (A a) (A (H.bar a)) ad ↔ ∃ wL : AdTy t a, (wL.IsGen ∧ AdRigid t a wL) ∧
      AdClause t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) A a wL ad :=
  (adEquiv a).exists_congr fun w => and_congr (isRigAdj_iff a w) (adjVia_iff e A a w ad)

theorem hasUnits_iff_clauses (F : Fin d → PS S 2 d) (A : 𝓞 E → Pt S 1 d) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d)
    (ad : 𝓞 E → PS S 2 d) : HasUnits t x0 e F A ph1 ph2 sy ad ↔
      IsFrameG t x0 d (ptsOf t x0 j) F A ph1 ph2 sy ad (frEquiv t x0 j e) ∧
      FrTrunc t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) ∧ FrAxes t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) ∧
      ∀ a, ∃ wL : AdTy t a, (wL.IsGen ∧ AdRigid t a wL) ∧
        AdClause t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) A a wL (ad a) := by
  rw [HasUnits, isFrame_iff, first_cubical_law_iff_clause, second_cubical_law_iff_clause, sym_iff, isFrameG_iff]
  simp only [adj_iff]
  exact ⟨fun ⟨⟨g, tr, ax⟩, p1, p2, s, a⟩ => ⟨⟨g, p1, p2, s, fun b => (a b).imp fun _ h => ⟨h.1.1, h.2⟩⟩, tr, ax, a⟩,
    fun ⟨⟨g, p1, p2, s, _⟩, tr, ax, a⟩ => ⟨⟨g, tr, ax⟩, p1, p2, s, a⟩⟩

theorem formEq_pad {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (g₁ g₂ g₃ : Y ⟶ Y)
    (h₁ : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ i, h (g₁ ≫ φ i) ^ ε i = 1)
    (h₂ : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ i, h (g₂ ≫ φ i) ^ ε i = 1)
    (h₃ : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ i, h (g₃ ≫ φ i) ^ ε i = 1) :
    FormEq (Sum.elim φ (Sum.elim (fun k => g₁ ≫ φ k) (Sum.elim (fun k => g₂ ≫ φ k) (fun k => g₃ ≫ φ k))))
      (Sum.elim ε (Sum.elim (fun k => -ε k) (Sum.elim (fun k => -ε k) ε))) φ ε := fun U _ h => by
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, h₁ U h, h₂ U h,
    h₃ U h, inv_one, _root_.mul_one]

section Rigid

variable (t)

theorem prod_ad (a : 𝓞 E) {T : Over X0} (p q : T ⟶ t.G) (U : Type) [CommGroup U] (h : (T.left ⟶ t.G.left) → U) :
    ∏ i, h ((lift p q).left ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
      (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) ^ Sum.elim (cε 2) (fun I => -cε 2 I) i =
    h (p * (q ≫ t.act.act (H.bar a))).left * (h p.left)⁻¹ * (h (q ≫ t.act.act (H.bar a)).left)⁻¹ *
      ((h ((p ≫ t.act.act a) * q).left)⁻¹ * h (p ≫ t.act.act a).left * h q.left) := by
  have e₁ := prod_cube₂ (fst t.G t.G) (snd t.G t.G ≫ t.act.act (H.bar a)) fun r => h ((lift p q).left ≫ r)
  have e₂ := prod_neg _ _ (prod_cube₂ (fst t.G t.G ≫ t.act.act a) (snd t.G t.G) fun r => h ((lift p q).left ≫ r))
  rw [Fintype.prod_sum_type]
  refine (congrArg₂ (· * ·) e₁ e₂).trans ?_
  simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_rigid (a : 𝓞 E) (wL : AdTy t a) (hw : wL.IsGen) : ∃ w' : AdTy t a, (w'.IsGen ∧ AdRigid t a w') ∧
    ∀ {T : Over X0} (p q : T ⟶ t.G) (z : T.left) (J : (T.left ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      val₂ w' z J p q = val₂ wL z J p q * ((val₂ wL z J p 1)⁻¹ * ((val₂ wL z J 1 q)⁻¹ * val₂ wL z J (1 : T ⟶ t.G) 1)) := by
  have hL := t.PP.isLB
  have := t.act.hom
  have r1 : ∀ {T : Over X0} (p : T ⟶ t.G) (U : Type) [CommGroup U] (h : (T.left ⟶ t.G.left) → U),
      ∏ i, h ((lift p 1).left ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) ^ Sum.elim (cε 2) (fun I => -cε 2 I) i = 1 :=
    fun p U _ h => (prod_ad t a p 1 U h).trans (by simp [MonObj.one_comp])
  have r2 : ∀ {T : Over X0} (q : T ⟶ t.G) (U : Type) [CommGroup U] (h : (T.left ⟶ t.G.left) → U),
      ∏ i, h ((lift 1 q).left ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) ^ Sum.elim (cε 2) (fun I => -cε 2 I) i = 1 :=
    fun q U _ h => (prod_ad t a 1 q U h).trans (by
      simp only [MonObj.one_comp, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  obtain ⟨w', hw', hv⟩ := exists_gen hL
    (φ' := Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
      (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (ε' := Sum.elim (cε 2) fun I => -cε 2 I)
    (formEq_pad _ _ _ _ _ (r1 (fst t.G t.G)) (r2 (snd t.G t.G)) (r1 1))
    (LB.mulGen t.PP.L _ _ _ _ wL (LB.mulGen t.PP.L _ _ _ _
      (LB.invGen t.PP.L _ _ (LB.pullGen t.PP.L _ _ wL (lift (fst t.G t.G) 1).left))
      (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (LB.pullGen t.PP.L _ _ wL (lift 1 (snd t.G t.G)).left))
        (LB.pullGen t.PP.L _ _ wL (lift (1 : t.G ⊗ t.G ⟶ t.G) 1).left))))
    (mulGen_isGen _ _ _ _ _ _ _ hw (mulGen_isGen _ _ _ _ _ _ _ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hw _))
      (mulGen_isGen _ _ _ _ _ _ _ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hw _)) (pullGen_isGen _ _ _ _ hw _))))
  have key : ∀ {T : Over X0} (p q : T ⟶ t.G) (z : T.left) (J : (T.left ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      val₂ w' z J p q = val₂ wL z J p q *
        ((val₂ wL z J p 1)⁻¹ * ((val₂ wL z J 1 q)⁻¹ * val₂ wL z J (1 : T ⟶ t.G) 1)) := fun p q z J hJ => by
    refine (hv _ (lift p q).left z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) ((val_ros _ _ hJ _ _).trans ?_)))
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) ((val_ros _ _ hJ _ _).trans ?_)))
          ((val_ros _ _ hJ _ _).trans ?_)))))))
    · rw [lift_fst, MonObj.comp_one]
    · rw [lift_snd, MonObj.comp_one]
    · rw [MonObj.comp_one]
  refine ⟨w', ⟨hw', corr_of_val hL fun y J hJ => ?_, corr_of_val hL fun y J hJ => ?_⟩, key⟩
  · refine (val_ros w' (𝟙 t.G) hJ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [MonObj.comp_one, key _ _ y J hJ]; simp
  · refine (val_ros w' (𝟙 t.G) hJ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [MonObj.comp_one, key _ _ y J hJ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel

variable {t} {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {e' : ∀ m, FrTyG t x0 d x m} {G : FGLaw S d} {A : Germ.OAct (𝓞 E) G}
  (hz : ∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1)
include hz

theorem pp_zero {n m : ℕ} : PP m x (0 : Q S d n) = 1 := by
  have h : jQ m ![(0 : Q S d n)] = (Algebra.ofId S _).comp (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) :=
    jet_hom_ext fun s => by
      obtain ⟨k, s⟩ := s
      obtain rfl := Subsingleton.elim k 0
      rw [jQ_X, AlgHom.comp_apply]
      refine (psJet_zero m).trans (Eq.symm ?_)
      show Algebra.ofId S _ (MvPolynomial.aeval (fun _ => (0 : S)) (MvPolynomial.X _)) = _
      rw [MvPolynomial.aeval_X, map_zero]
  rw [PP, h, ← homAt_comp, Category.assoc, hz m, MonObj.comp_one]

theorem ad_axes_val (hax : FrAxes t x0 d x e') {a : 𝓞 E} {wL : AdTy t a} {ad : PS S 2 d}
    (h : AdClause t x0 d x e' A.act a wL ad) {n m : ℕ} {y : (jOG x0 d m n).left}
    {J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L y J) (u : Q S d n) :
    VV m y (E2 ad u 0) = (val₂ wL y J (PP m x u) 1).val ∧ VV m y (E2 ad 0 u) = (val₂ wL y J 1 (PP m x u)).val := by
  obtain ⟨U, h₁, h₂⟩ := h m
  have k₁ := dict_ad (ad := fun _ => ad) hJ a wL U h₁ h₂ u 0
  have k₂ := dict_ad (ad := fun _ => ad) hJ a wL U h₁ h₂ 0 u
  rw [ac0, (dict_ax hJ hax _).2, (dict_ax hJ hax _).2, pp_zero hz, inv_one, _root_.mul_one, _root_.mul_one] at k₁
  rw [ac0, (dict_ax hJ hax _).1, (dict_ax hJ hax _).1, pp_zero hz, inv_one, _root_.mul_one, _root_.mul_one] at k₂
  exact ⟨k₁, k₂⟩

theorem rigid_iff (hax : FrAxes t x0 d x e') (a : 𝓞 E) (ad : PS S 2 d) :
    (∃ wL : AdTy t a, (wL.IsGen ∧ AdRigid t a wL) ∧ AdClause t x0 d x e' A.act a wL ad) ↔
      (∃ wL : AdTy t a, wL.IsGen ∧ AdClause t x0 d x e' A.act a wL ad) ∧
        ev (n := 1) ![0, pt S d 0] ad = 1 ∧ ev (n := 1) ![pt S d 0, 0] ad = 1 := by
  have hL := t.PP.isLB
  constructor
  · rintro ⟨wL, ⟨hw, hr⟩, h⟩
    refine ⟨⟨wL, hw, h⟩, (formalSeriesValueAtTwoPoints_eq_ev ad 0 (gen 0)).symm.trans (VV_ext (x0 := x0) hL fun m y J hJ => ?_),
      (formalSeriesValueAtTwoPoints_eq_ev ad (gen 0) 0).symm.trans (VV_ext (x0 := x0) hL fun m y J hJ => ?_)⟩
    · have k := (val_ros wL (PP m x (gen 0)) hJ _ _).symm.trans ((val_corr hJ hr.2 _).trans (val_one _))
      rw [MonObj.comp_one, Category.comp_id] at k
      rw [(ad_axes_val hz hax h hJ _).2, k, VV_one, Units.val_one]
    · have k := (val_ros wL (PP m x (gen 0)) hJ _ _).symm.trans ((val_corr hJ hr.1 _).trans (val_one _))
      rw [MonObj.comp_one, Category.comp_id] at k
      rw [(ad_axes_val hz hax h hJ _).1, k, VV_one, Units.val_one]
  · rintro ⟨⟨wL, hw, h⟩, h0, h1⟩
    obtain ⟨w', hw', hv⟩ := exists_rigid t a wL hw
    refine ⟨w', hw', fun m => (h m).imp fun U hU => ⟨hU.1, corr_of_val hL fun y J hJ => ?_⟩⟩
    have z0 : ∀ u : Q S d 2, val₂ wL y J 1 (PP m x u) = 1 := fun u => Units.ext (by
      have k := congrArg (sb ![u]) ((formalSeriesValueAtTwoPoints_eq_ev ad 0 (gen 0)).trans h0)
      rw [formalPointSubstitutionSeries_valueAtTwoPoints, map_zero, sq_gen, map_one] at k
      exact (ad_axes_val hz hax h hJ u).2.symm.trans ((congrArg (VV m y) k).trans (VV_one m y)))
    have z1 : ∀ u : Q S d 2, val₂ wL y J (PP m x u) 1 = 1 := fun u => Units.ext (by
      have k := congrArg (sb ![u]) ((formalSeriesValueAtTwoPoints_eq_ev ad (gen 0) 0).trans h1)
      rw [formalPointSubstitutionSeries_valueAtTwoPoints, map_zero, sq_gen, map_one] at k
      exact (ad_axes_val hz hax h hJ u).1.symm.trans ((congrArg (VV m y) k).trans (VV_one m y)))
    have z2 := z0 0
    rw [pp_zero hz] at z2
    refine Eq.trans ((val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ rfl) (val_mul hJ _ _ _).symm))
      (val_corr hJ hU.2 _)
    refine (val_ros w' (𝟙 (jOG x0 d m 2)) hJ _ _).trans (Eq.trans ?_ (val_ros wL (𝟙 (jOG x0 d m 2)) hJ _ _).symm)
    rw [Category.id_comp, Category.id_comp, hv _ _ y J hJ, PP_gen, PP_gen, z0, z1, z2]
    simp

theorem frAxes_of_laws {ph1 ph2 : PS S 3 d} {sy : PS S 2 d} {ad : 𝓞 E → PS S 2 d}
    (hf : IsFrameG t x0 d x G.F A.act ph1 ph2 sy ad e')
    (h1 : ev (n := 2) ![0, pt S d 0, pt S d 1] ph1 = 1) (h2 : ev (n := 2) ![pt S d 0, 0, pt S d 1] ph2 = 1) :
    FrAxes t x0 d x e' := by
  have hL := t.PP.isLB
  intro m
  have hid : (homAt x0 (jQ m (gen : Fin 1 → Q S d 1))).left = 𝟙 _ := by
    have : jQ m (gen : Fin 1 → Q S d 1) = AlgHom.id S _ := jet_hom_ext fun s => by
      rw [jQ_X]; exact psJet_X m _
    rw [this]; exact Spec.map_id _
  have z : ∀ i, (Ideal.Quotient.mk _ 0 : Jet S (Fin 1 × Fin d) m) = psJet m ((0 : Q S d 1).1 i) := mk_zero m
  refine ⟨corr_of_val hL fun y J hJ => ?_, corr_of_val hL fun y J hJ => ?_⟩
  · have e₀ := val_peG x hJ e' gen ![fun _ => 0, fun j => X ((0 : Fin 1), j)] 0 (gen 0)
      (by rintro ⟨l, j⟩; fin_cases l; exacts [z j, hX 0 j])
      (by rintro ⟨l, j⟩; fin_cases l; exacts [map_zero _, MvPolynomial.constantCoeff_X _ _])
    rw [map_zero, sq_gen, hid] at e₀
    have k := congrArg (sb ![(0 : Q S d 1), gen 0]) ((formalSeriesValueAtThreePoints_eq_ev ph1 0 (gen 0) (gen 1)).trans h1)
    rw [formalPointSubstitutionSeries_valueAtThreePoints, map_zero, sq_gen, sq_gen, map_one] at k
    have k' := (frame_biext_dictionary_first_partial_law hJ hf 0 0 (gen 0)).symm.trans ((congrArg (VV m y) k).trans (VV_one m y))
    rw [op0, pp_zero hz, (isCub_cubV t.cub hJ).face, _root_.one_mul, inv_mul_cancel, _root_.one_mul] at k'
    exact e₀.trans ((Units.ext k').trans (val_one _).symm)
  · have e₁ := val_peG x hJ e' gen ![fun j => X ((0 : Fin 1), j), fun _ => 0] (gen 0) 0
      (by rintro ⟨l, j⟩; fin_cases l; exacts [hX 0 j, z j])
      (by rintro ⟨l, j⟩; fin_cases l; exacts [MvPolynomial.constantCoeff_X _ _, map_zero _])
    rw [map_zero, sq_gen, hid] at e₁
    have k := congrArg (sb ![(gen 0 : Q S d 1), 0]) ((formalSeriesValueAtThreePoints_eq_ev ph2 (gen 0) 0 (gen 1)).trans h2)
    rw [formalPointSubstitutionSeries_valueAtThreePoints, map_zero, sq_gen, sq_gen, map_one] at k
    have k' := (frame_biext_dictionary_second_partial_law hJ hf (gen 0) 0 0).symm.trans ((congrArg (VV m y) k).trans (VV_one m y))
    rw [op0, pp_zero hz, (isCub_cubV t.cub hJ).face₂, _root_.one_mul, inv_mul_cancel, _root_.one_mul] at k'
    exact e₁.trans ((Units.ext k').trans (val_one _).symm)

end Rigid

theorem zero_ptsOf (hz : ∀ m, algMap x0 (jetAug : Jet S (Fin d) m →ₐ[S] S) ≫ j m = 1) (m : ℕ) :
    homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ ptsOf t x0 j m = 1 := by
  refine Eq.trans ?_ (hz m)
  show homAt x0 _ ≫ homAt x0 _ ≫ j m = homAt x0 _ ≫ j m
  rw [← Category.assoc, homAt_comp]
  refine congrArg (fun g => homAt x0 g ≫ j m) (jet_hom_ext fun s => ?_)
  rw [AlgHom.comp_apply, jetIn, jetMap_mk, MvPolynomial.aeval_X]
  exact (MvPolynomial.aeval_X (fun _ => (0 : S)) _).trans (MvPolynomial.aeval_X (fun _ => (0 : S)) _).symm

theorem hasUnits_iff (hz : ∀ m, algMap x0 (jetAug : Jet S (Fin d) m →ₐ[S] S) ≫ j m = 1)
    (G : FGLaw S d) (A : Germ.OAct (𝓞 E) G) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d) :
    HasUnits t x0 e G.F A.act ph1 ph2 sy ad ↔
      IsFrameG t x0 d (ptsOf t x0 j) G.F A.act ph1 ph2 sy ad (frEquiv t x0 j e) ∧
      FrTrunc t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) ∧ FrAxes t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) ∧
      ∀ a, ev (n := 1) ![0, pt S d 0] (ad a) = 1 ∧ ev (n := 1) ![pt S d 0, 0] (ad a) = 1 := by
  refine (hasUnits_iff_clauses e _ _ _ _ _ _).trans
    (and_congr_right fun hf => and_congr_right fun _ => and_congr_right fun hax => forall_congr' fun a => ?_)
  exact (rigid_iff (zero_ptsOf hz) hax a (ad a)).trans (and_iff_right (hf.ad a))

theorem hasUnits_iff_of_biext [StarRing (𝓞 E)] (hz : ∀ m, algMap x0 (jetAug : Jet S (Fin d) m →ₐ[S] S) ≫ j m = 1)
    (B : Germ.FB S d (𝓞 E)) : HasUnits t x0 e B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad ↔
      IsFrameG t x0 d (ptsOf t x0 j) B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad (frEquiv t x0 j e) ∧
      FrTrunc t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) :=
  (hasUnits_iff e hz B.G B.A _ _ _ _).trans (and_congr_right fun hf => and_iff_left_of_imp fun _ =>
    ⟨frAxes_of_laws (zero_ptsOf hz) hf B.cocycleLeft_zero_fst B.cocycleRight_zero_snd, fun a => ⟨B.adjoint_zero_fst a, B.adjoint_zero_snd a⟩⟩)

theorem realises_iff [StarRing (𝓞 E)] (B : Germ.FB S d (𝓞 E)) : Realises t x0 j e B ↔
    ((∀ a : 𝓞 E, star a = H.bar a) ∧ IsFormalParam t.G x0 j ∧ LawIs t.G x0 j B.G.F ∧
      ∀ a, EndIs t.G x0 j (t.act.act a) (B.A.act a)) ∧
    IsFrameG t x0 d (ptsOf t x0 j) B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad (frEquiv t x0 j e) ∧
    FrTrunc t x0 d (ptsOf t x0 j) (frEquiv t x0 j e) :=
  ⟨fun ⟨s, p, l, a, h⟩ => ⟨⟨s, p, l, a⟩, (hasUnits_iff_of_biext e p.2.1 B).1 h⟩,
    fun ⟨⟨s, p, l, a⟩, h⟩ => ⟨s, p, l, a, (hasUnits_iff_of_biext e p.2.1 B).2 h⟩⟩

end GlobalTheory.FrameCompare
