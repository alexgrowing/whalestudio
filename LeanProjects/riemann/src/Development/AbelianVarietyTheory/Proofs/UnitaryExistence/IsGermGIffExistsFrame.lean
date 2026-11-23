import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.PrimitiveGermFrames
import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GermSectionCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

section General

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_iff_val (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) :
    LB.Gen.Corr L φ ε φ' ε' t t' ↔ ∀ y J, Good L y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J :=
  ⟨fun h _ _ hJ => val_corr hJ h _, corr_of_val hL⟩

theorem isGen_iff_gm {M : LB Y} (t : LB.Gen M) :
    t.IsGen ↔ ∀ i j y, y ∈ M.U i ⊓ M.U j →
      gm (𝟙 Y) y (M.U i) (t.s i) = gm (𝟙 Y) y (M.U i ⊓ M.U j) (M.g i j) * gm (𝟙 Y) y (M.U j) (t.s j) := by
  constructor
  · intro h i j y hy
    exact (gm_res (𝟙 Y) y _ hy _).symm.trans ((congrArg (gm (𝟙 Y) y _) (h i j)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))))
  · intro h i j
    exact unit_ext fun y hy => (gm_res (𝟙 Y) y _ hy _).trans ((h i j y hy).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))).symm)

def genCast {φ φ' : K → (Y ⟶ X)} (ε : K → ℤ) (h : φ = φ') :
    LB.Gen (LB.LinComb L φ ε) ≃ LB.Gen (LB.LinComb L φ' ε) where
  toFun t := ⟨fun j => res (le_of_eq (congrArg (fun ψ => LB.wchart L ψ j) h.symm)) (t.s j)⟩
  invFun t := ⟨fun j => res (le_of_eq (congrArg (fun ψ => LB.wchart L ψ j) h)) (t.s j)⟩
  left_inv t := by
    subst h
    exact congrArg LB.Gen.mk (funext fun j => unit_ext fun y hy => (gm_res _ y _ hy _).trans (gm_res _ y _ hy _))
  right_inv t := by
    subst h
    exact congrArg LB.Gen.mk (funext fun j => unit_ext fun y hy => (gm_res _ y _ hy _).trans (gm_res _ y _ hy _))

theorem genCast_rfl {φ : K → (Y ⟶ X)} (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) : genCast ε rfl t = t :=
  congrArg LB.Gen.mk (funext fun _ => unit_ext fun y hy => gm_res _ y _ hy _)

theorem val_genCast {φ φ' : K → (Y ⟶ X)} (ε : K → ℤ) (h : φ = φ') (t : LB.Gen (LB.LinComb L φ ε))
    (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) : val (genCast ε h t) r z J = val t r z J := by
  subst h; rw [genCast_rfl]

theorem isGen_genCast {φ φ' : K → (Y ⟶ X)} (ε : K → ℤ) (h : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) :
    (genCast ε h t).IsGen ↔ t.IsGen := by
  subst h; rw [genCast_rfl]

theorem le_div (φ : K → (X ⟶ X)) (ε : K → ℤ) (j : Fin 1 ⊕ K → L.ι) :
    LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j ≤
      (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)) := fun _ hy =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k), Set.mem_iInter.1 hy (Sum.inl 0)⟩

theorem div_le (φ : K → (X ⟶ X)) (ε : K → ℤ) (p : (K → L.ι) × L.ι) :
    (LB.div (LB.LinComb L φ ε) L).U p ≤
      LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => p.2) p.1) := fun _ hy =>
  Set.mem_iInter.2 fun k => by
    rcases k with k | k
    · exact hy.2
    · exact Set.mem_iInter.1 hy.1 k

omit [Fintype K] in
theorem idx_split (j : Fin 1 ⊕ K → L.ι) : ∃ p : (K → L.ι) × L.ι, j = Sum.elim (fun _ => p.2) p.1 :=
  ⟨(j ∘ Sum.inr, j (Sum.inl 0)), funext fun k => by
    rcases k with k | k
    · rw [Subsingleton.elim k 0]; rfl
    · rfl⟩

def divEquiv (φ : K → (X ⟶ X)) (ε : K → ℤ) : LB.Iso L (LB.LinComb L φ ε) ≃
    LB.Gen (LB.LinComb L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => 1) fun k => -ε k)) where
  toFun w := ⟨fun j => res (le_div φ ε j) (w.s (j ∘ Sum.inr, j (Sum.inl 0)))⁻¹⟩
  invFun v := ⟨fun p => res (div_le φ ε p) (v.s (Sum.elim (fun _ => p.2) p.1))⁻¹⟩
  left_inv w := by
    obtain ⟨s⟩ := w
    refine congrArg LB.Gen.mk (funext fun p => unit_ext fun y hy => ?_)
    refine (gm_res _ y _ hy _).trans ((map_inv _ _).trans (inv_eq_iff_eq_inv.2 ?_))
    exact (gm_res _ y _ (div_le φ ε p hy) _).trans (map_inv _ _)
  right_inv v := by
    obtain ⟨s⟩ := v
    refine congrArg LB.Gen.mk (funext fun j => ?_)
    obtain ⟨p, rfl⟩ := idx_split j
    refine unit_ext fun y hy => ?_
    refine (gm_res _ y _ hy _).trans ((map_inv _ _).trans (inv_eq_iff_eq_inv.2 ?_))
    exact (gm_res _ y _ (le_div φ ε _ hy) _).trans (map_inv _ _)

theorem gm_g_div (φ : K → (X ⟶ X)) (ε : K → ℤ) (i j : Fin 1 ⊕ K → L.ι) (y : X)
    (hi : y ∈ LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) i)
    (hj : y ∈ LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j) :
    gm (𝟙 X) y _ ((LB.LinComb L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => 1) fun k => -ε k)).g i j) =
      (gm (𝟙 X) y _ ((LB.div (LB.LinComb L φ ε) L).g (i ∘ Sum.inr, i (Sum.inl 0)) (j ∘ Sum.inr, j (Sum.inl 0))))⁻¹ := by
  have hi' := le_div φ ε i hi
  have hj' := le_div φ ε j hj
  refine (gm_linComb L _ _ (𝟙 _) y i j hi hj).trans (inv_eq_iff_eq_inv.1 (Eq.symm ?_))
  refine (gm_div L (LB.LinComb L φ ε) (𝟙 X) y (i ∘ Sum.inr, i (Sum.inl 0)) (j ∘ Sum.inr, j (Sum.inl 0))
    ⟨hi', hj'⟩).trans ?_
  refine (congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 _) y _ _ hi'.1 hj'.1) rfl).trans ?_
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Fin.prod_univ_one, zpow_one,
    Category.comp_id, Category.id_comp, mul_inv_rev, inv_inv]
  rfl

theorem isGen_divEquiv (φ : K → (X ⟶ X)) (ε : K → ℤ) (w : LB.Iso L (LB.LinComb L φ ε)) :
    (divEquiv φ ε w).IsGen ↔ w.IsGen := by
  have hv : ∀ (j : Fin 1 ⊕ K → L.ι) (y : X), y ∈ LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j →
      gm (𝟙 X) y (LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j) ((divEquiv φ ε w).s j) =
        (gm (𝟙 X) y _ (w.s (j ∘ Sum.inr, j (Sum.inl 0))))⁻¹ := fun j y hy =>
    (gm_res _ y _ hy _).trans (map_inv _ _)
  rw [isGen_iff_gm, isGen_iff_gm]
  constructor
  · intro h p q y hy
    have hp := div_le φ ε p hy.1
    have hq := div_le φ ε q hy.2
    have e := (hv _ y hp).symm.trans ((h _ _ y ⟨hp, hq⟩).trans
      (congrArg₂ (· * ·) (gm_g_div φ ε _ _ y hp hq) (hv _ y hq)))
    exact inv_injective (e.trans (mul_inv _ _).symm)
  · intro h i j y hy
    have e := h (i ∘ Sum.inr, i (Sum.inl 0)) (j ∘ Sum.inr, j (Sum.inl 0)) y ⟨le_div φ ε i hy.1, le_div φ ε j hy.2⟩
    exact (hv i y hy.1).trans (((congrArg (·⁻¹) e).trans (mul_inv _ _)).trans
      (congrArg₂ (· * ·) (gm_g_div φ ε i j y hy.1 hy.2) (hv j y hy.2)).symm)

end General

section Jets

variable {S : Type} [CommRing S] {d : ℕ}

def jetOut (m : ℕ) : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin d) m :=
  jetMap (fun p => MvPolynomial.X p.2) fun _ => X_mem_orig _

theorem jetOut_in (m : ℕ) : (jetOut m).comp (jetIn (0 : Fin 1)) = AlgHom.id S (Jet S (Fin d) m) := by
  apply jet_hom_ext
  intro i
  simp [jetOut, jetIn, jetMap_mk]

theorem jetIn_out (m : ℕ) : (jetIn (0 : Fin 1)).comp (jetOut m) = AlgHom.id S (Jet S (Fin 1 × Fin d) m) := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [jetOut, jetIn, jetMap_mk]

theorem jetCopy_in {n : ℕ} (m : ℕ) (i : Fin n) :
    (jetCopy (S := S) d m i).comp (jetIn (0 : Fin 1)) = jetIn i := by
  apply jet_hom_ext
  intro j
  simp [jetCopy, jetIn, jetMap_mk]

theorem germCompOne_identityPoint_left (A : Germ.Pt S 1 d) : Germ.comp1 A (Germ.pt S d 0) = A := by
  funext i
  have h : (fun p : Fin 1 × Fin d => (![Germ.pt S d (0 : Fin 1)] : Fin 1 → Germ.Pt S 1 d) p.1 p.2) =
      MvPowerSeries.X := by
    funext p
    obtain ⟨a, b⟩ := p
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
  simp only [Germ.comp1, Germ.ev, h, MvPowerSeries.subst_self, id]

theorem psTrunc_X_sub {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (i : κ) :
    psTrunc m (MvPowerSeries.X i : MvPowerSeries κ S) - MvPolynomial.X i ∈ orig S κ ^ (m + 1) := by
  refine mem_orig_pow_of fun e he => ?_
  by_contra hlt
  apply MvPolynomial.mem_support_iff.1 he
  rw [MvPolynomial.coeff_sub, Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.coeff_psTrunc _ _ _ (by omega), ← MvPolynomial.coe_X,
    MvPolynomial.coeff_coe, sub_self]

theorem subst2_eq (m : ℕ) (A : Germ.Pt S 1 d) :
    subst2 m (Germ.pt S d 0) (Germ.comp1 A (Germ.pt S d 0)) = sL m A := by
  rw [germCompOne_identityPoint_left]
  apply jet_hom_ext
  rintro ⟨i, j⟩
  simp only [subst2, jetSubstPS, sL, jetSubstP, jetMap_mk, MvPolynomial.aeval_X]
  apply Ideal.Quotient.eq.2
  fin_cases i
  · have hc : MvPolynomial.constantCoeff (psTrunc m (MvPowerSeries.X ((0 : Fin 1), j) : Germ.PS S 1 d)) = 0 := by
      rw [MvPolynomial.constantCoeff_eq, Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.coeff_psTrunc _ _ _ (by simp)]
      simp
    simpa [Germ.pt, hc] using psTrunc_X_sub (S := S) m ((0 : Fin 1), j)
  · simp [power_series_in_fin_one]

end Jets

section Compare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X₀ : Scheme.{0}} (t : SAB H X₀)

def primEquiv : PrimIso t ≃ PrimTyG t := divEquiv (cφG t ![𝟙 t.G, t.act.act H.w0]) (cε 2)

theorem isGen_primEquiv (w : PrimIso t) : (primEquiv t w).IsGen ↔ w.IsGen := isGen_divEquiv _ _ w

theorem val_primEquiv (w : PrimIso t) {Z : Scheme.{0}} (r : Z ⟶ t.G.left) (z : Z)
    {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) :
    val (primEquiv t w) r z J = (val (primGen t.G t.PP.L (t.act.act H.w0) w) r z J)⁻¹ :=
  (gm_res r z _ (hJ.mem _ r) _).trans ((map_inv _ _).trans
    (congrArg (·⁻¹) (gm_res r z _ (hJ.mem (primφ t.G (t.act.act H.w0)) r) _).symm))

theorem isPrim_iff_isPrimG (w : PrimIso t) : GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames.IsPrim t w ↔ IsPrimG t (primEquiv t w) := by
  refine and_congr (isGen_primEquiv t w).symm ?_
  refine (corr_iff_val t.PP.isLB _ _).trans (Iff.trans ?_ (corr_iff_val t.PP.isLB _ _).symm)
  refine forall_congr' fun y => forall_congr' fun J => forall_congr' fun hJ => ?_
  rw [val_mul hJ, val_pull hJ, val_pull hJ, val_one, val_primEquiv t w _ y hJ]
  exact mul_eq_one_iff_inv_eq

theorem corr_pow (hL : t.PP.L.IsLB) {T : Over X₀} {p : T ⟶ t.G} {K : Type} [Fintype K]
    {φ : K → (T.left ⟶ t.G.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb t.PP.L (Y := T.left) (K := Fin 1) (fun _ => p.left) (fun _ => 1)))
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (k : ℕ) (h : LB.Gen.Corr t.PP.L _ _ _ _ u g) :
    LB.Gen.Corr t.PP.L _ _ _ _ (Out.powFrame t.G t.PP.L p u (k : ℤ)) (genPowG t φ ε g k) :=
  corr_of_val hL fun _ _ hJ => (map_zpow _ _ _).trans ((zpow_natCast _ _).trans
    ((congrArg (· ^ k) (val_corr hJ h (𝟙 _))).trans (map_pow _ _ _).symm))

variable {S : Type} [CommRing S] (x : Sp S ⟶ X₀) {d : ℕ}

theorem funOn_eq {B : Type} [CommRing B] (b : B) : funOn b = toΓ B b := rfl

theorem algMap_eq {B B' : Type} [CommRing B] [Algebra S B] [CommRing B'] [Algebra S B'] (f : B →ₐ[S] B') :
    algMap x f = homAt x f := rfl

def chartEquiv : JetPts t.G x d ≃ ∀ m, jOG x d m 1 ⟶ t.G where
  toFun j m := jPt t.G x j 1 m 0
  invFun y m := homAt x (jetOut m) ≫ y m
  left_inv j := funext fun m => by
    show homAt x (jetOut m) ≫ homAt x (jetIn (0 : Fin 1)) ≫ j m = j m
    rw [← Category.assoc, homAt_comp, jetOut_in, homAt_id, Category.id_comp]
  right_inv y := funext fun m => by
    show homAt x (jetIn (0 : Fin 1)) ≫ homAt x (jetOut m) ≫ y m = y m
    rw [← Category.assoc, homAt_comp, jetIn_out, homAt_id, Category.id_comp]

theorem jptG_chartEquiv (j : JetPts t.G x d) {n : ℕ} (m : ℕ) (i : Fin n) :
    jptG t x d (chartEquiv t x j) m i = jPt t.G x j n m i := by
  show homAt x (jetCopy d m i) ≫ homAt x (jetIn (0 : Fin 1)) ≫ j m = homAt x (jetIn i) ≫ j m
  rw [← Category.assoc, homAt_comp, jetCopy_in]

theorem lamφ_eq (j : JetPts t.G x d) (m : ℕ) : lamφ t.G (jPt t.G x j 2 m) =
    cφG t ![jptG t x d (chartEquiv t x j) m (0 : Fin 2), jptG t x d (chartEquiv t x j) m (1 : Fin 2)] := by
  have h : jPt t.G x j 2 m =
      ![jptG t x d (chartEquiv t x j) m (0 : Fin 2), jptG t x d (chartEquiv t x j) m (1 : Fin 2)] := by
    funext i
    fin_cases i
    · exact (jptG_chartEquiv t x j m _).symm
    · exact (jptG_chartEquiv t x j m _).symm
  rw [h]
  rfl

def frameEquiv (j : JetPts t.G x d) :
    FrameFam t.G x t.PP.L j ≃ ∀ m, FrTyG t x d (chartEquiv t x j) m where
  toFun e m := genCast (L := t.PP.L) lamε (lamφ_eq t x j m) (e m)
  invFun e m := (genCast (L := t.PP.L) lamε (lamφ_eq t x j m)).symm (e m)
  left_inv e := funext fun m => (genCast (L := t.PP.L) lamε (lamφ_eq t x j m)).symm_apply_apply (e m)
  right_inv e := funext fun m => (genCast (L := t.PP.L) lamε (lamφ_eq t x j m)).apply_symm_apply (e m)

theorem frameEquiv_apply (j : JetPts t.G x d) (e : FrameFam t.G x t.PP.L j) (m : ℕ) :
    frameEquiv t x j e m = genCast (L := t.PP.L) lamε (lamφ_eq t x j m) (e m) := rfl

variable {t x}

theorem isGen_frameEquiv {j : JetPts t.G x d} (e : FrameFam t.G x t.PP.L j) (m : ℕ) :
    (frameEquiv t x j e m).IsGen ↔ (e m).IsGen := by
  rw [frameEquiv_apply]
  exact isGen_genCast (L := t.PP.L) lamε (lamφ_eq t x j m) (e m)

variable {j : JetPts t.G x d} (act : 𝓞 E → Germ.Pt S 1 d) (e : FrameFam t.G x t.PP.L j) (w : PrimIso t)

theorem val_eLG (m : ℕ) (y : (jOG x d m 1).left) {J : ((jOG x d m 1).left ⟶ t.G.left) → t.PP.L.ι}
    (hJ : Good t.PP.L y J) :
    val (eLG t x d (chartEquiv t x j) act (frameEquiv t x j e) (primEquiv t w) m) (𝟙 _) y J =
      (val (LB.pullGen t.PP.L _ _ (primGen t.G t.PP.L (t.act.act H.w0) w) (jPt t.G x j 1 m 0).left) (𝟙 _) y J)⁻¹ *
        val (frAt e (n := 1) m (Germ.pt S d 0) (Germ.comp1 (act H.w0) (Germ.pt S d 0))) (𝟙 _) y J := by
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)
  · exact (val_pull hJ _ _ _).trans ((val_primEquiv t w _ y hJ).trans (congrArg (·⁻¹) (val_pull hJ _ _ _).symm))
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [subst2_eq, frameEquiv_apply]
    exact val_genCast (L := t.PP.L) lamε (lamφ_eq t x j m) (e m) _ y J

theorem frameL_clause_iff (m : ℕ)
    (u : LB.Gen (LB.LinComb t.PP.L (Y := (algO x (Jet S (Fin 1 × Fin d) m)).left) (K := Fin 1)
      (fun _ => (jPt t.G x j 1 m 0).left) (fun _ => 1))) :
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.mulGen t.PP.L _ _ _ _
        (LB.pullGen t.PP.L _ _ (primGen t.G t.PP.L (t.act.act H.w0) w) (jPt t.G x j 1 m 0).left) u)
      (frAt e (n := 1) m (Germ.pt S d 0) (Germ.comp1 (act H.w0) (Germ.pt S d 0))) ↔
    LB.Gen.Corr t.PP.L _ _ _ _ u (eLG t x d (chartEquiv t x j) act (frameEquiv t x j e) (primEquiv t w) m) := by
  refine (corr_iff_val t.PP.isLB _ _).trans (Iff.trans ?_ (corr_iff_val t.PP.isLB _ _).symm)
  refine forall_congr' fun y => forall_congr' fun J => forall_congr' fun hJ => ?_
  rw [val_mul hJ, val_eLG act e w m y hJ]
  exact eq_inv_mul_iff_mul_eq.symm

theorem isFrameLVia_iff (eL : FrameL t.G x t.PP.L j) :
    IsFrameLVia w e (act H.w0) eL ↔ GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws.IsFrame e ∧ EndIs t.G x j (t.act.act H.w0) (act H.w0) ∧
      ∀ m, (eL m).IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _ (eL m)
        (eLG t x d (chartEquiv t x j) act (frameEquiv t x j e) (primEquiv t w) m) :=
  and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun m =>
    and_congr_right fun _ => frameL_clause_iff act e w m (eL m)

theorem isGermIn_iff (eL : FrameL t.G x t.PP.L j)
    (h : ∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (eL m)
      (eLG t x d (chartEquiv t x j) act (frameEquiv t x j e) (primEquiv t w) m))
    (k : ℕ) (F : LB.Sec (Out.LPow t.G t.PP.L k (Over.mk x))) (f : Germ.PS S 1 d) :
    IsGermIn eL (k : ℤ) F f ↔
      IsGermG t x d (chartEquiv t x j) act (frameEquiv t x j e) (primEquiv t w) k F f := by
  have hL := t.PP.isLB
  have hc : ∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (Out.powFrame t.G t.PP.L (jPt t.G x j 1 m 0) (eL m) (k : ℤ))
      (genPowG t _ _ (eLG t x d (chartEquiv t x j) act (frameEquiv t x j e) (primEquiv t w) m) k) := fun m =>
    corr_pow t hL _ _ k (h m)
  constructor
  · intro hh m
    obtain ⟨F', h1, h2⟩ := hh m
    refine ⟨F', Out.powFrame t.G t.PP.L (jPt t.G x j 1 m 0) (eL m) (k : ℤ), ?_, ?_, ?_⟩
    · exact h1
    · exact hc m
    · exact h2
  · intro hh m
    obtain ⟨F', τ, h1, h2, h3⟩ := hh m
    have hτ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.gen_eq_of_corr _ hL _ _ _ _ _ _ _ h2 (hc m)
    rw [hτ] at h3
    refine ⟨F', ?_, ?_⟩
    · exact h1
    · exact h3

theorem exists_frameL (hw : w.IsGen) (he : ∀ m, (e m).IsGen)
    (hA : ∀ m, chartEquiv t x j m ≫ t.act.act H.w0 =
      homAt x (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act H.w0 p.2)) ≫ chartEquiv t x j m) :
    ∃ eL : FrameL t.G x t.PP.L j, ∀ m, (eL m).IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _ (eL m)
      (eLG t x d (chartEquiv t x j) act (frameEquiv t x j e) (primEquiv t w) m) := by
  have hL := t.PP.isLB
  have hφ : ∀ (m : ℕ) (I : ULift (Finset (Fin 2))),
      (chartEquiv t x j m).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
        (homAt x (sL m (act H.w0))).left ≫ cφG t ![jptG t x d (chartEquiv t x j) m (0 : Fin 2),
          jptG t x d (chartEquiv t x j) m (1 : Fin 2)] I := by
    intro m I
    have hpt : (fun i => chartEquiv t x j m ≫ (![𝟙 t.G, t.act.act H.w0] : Fin 2 → (t.G ⟶ t.G)) i) =
        fun i => homAt x (sL m (act H.w0)) ≫ (![jptG t x d (chartEquiv t x j) m (0 : Fin 2),
          jptG t x d (chartEquiv t x j) m (1 : Fin 2)] : Fin 2 → (jOG x d m 2 ⟶ t.G)) i := by
      funext i
      fin_cases i
      · show chartEquiv t x j m ≫ 𝟙 t.G =
          homAt x (sL m (act H.w0)) ≫ homAt x (jetCopy d m (0 : Fin 2)) ≫ chartEquiv t x j m
        rw [Category.comp_id, ← Category.assoc, homAt_comp, sL_copy0, homAt_id, Category.id_comp]
      · show chartEquiv t x j m ≫ t.act.act H.w0 =
          homAt x (sL m (act H.w0)) ≫ homAt x (jetCopy d m (1 : Fin 2)) ≫ chartEquiv t x j m
        rw [← Category.assoc, homAt_comp, sL_copy1, hA m]
    exact (comp_lamφ _ _ I).trans ((congrArg (fun p => lamφ t.G p I) hpt).trans (comp_lamφ _ _ I).symm)
  have hex : ∀ m, ∃ u : LB.Gen (LB.LinComb t.PP.L (Y := (jOG x d m 1).left) (K := Fin 1)
      (fun _ => (chartEquiv t x j m).left) fun _ => (1 : ℤ)), u.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _ u
      (eLG t x d (chartEquiv t x j) act (frameEquiv t x j e) (primEquiv t w) m) := by
    intro m
    have hg : (eLG t x d (chartEquiv t x j) act (frameEquiv t x j e) (primEquiv t w) m).IsGen :=
      DVR.mulGen_isGen_of_isGen _ (DVR.pullGen_isGen_of_isGen _ _ _ ((isGen_primEquiv t w).2 hw) _) _
        (DVR.pullGen_isGen_of_isGen _ _ _ ((isGen_frameEquiv e m).2 (he m)) _)
    obtain ⟨u, hu, hv⟩ := exists_gen hL (K' := Fin 1) (φ' := fun _ => (chartEquiv t x j m).left)
      (ε' := fun _ => (1 : ℤ)) (by
        intro U _ hU
        rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, hφ m]
        rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
        simp only [← zpow_add, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]) _ hg
    exact ⟨u, hu, corr_of_val hL fun y J hJ => hv _ _ y J hJ⟩
  choose u hu using hex
  exact ⟨u, hu⟩

end Compare

end GlobalTheory.GermSectionCompare
