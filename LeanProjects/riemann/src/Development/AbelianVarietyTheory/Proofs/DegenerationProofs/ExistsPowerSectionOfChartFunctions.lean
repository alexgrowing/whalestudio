import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulqLawsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivOfIsPushout

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.ThetaInValues

theorem exists_powerSection_of_chartFunctions {X : Scheme.{0}} {L : LB X} (u : LB.Sec L) : ∃ u' : H0 L 1, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z)
    (k : L.ι), r z ∈ L.U k → gs r z _ (u'.f fun _ => k) = gs r z _ (u.f k) := by
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun j _ hy => Set.mem_iInter.1 hy 0
  refine ⟨⟨fun j => (X.presheaf.map (homOfLE (le j)).op).hom (u.f (j 0)), fun j j' => fn_ext fun y hy => ?_⟩,
    fun Z r z k hk => gs_res r z (le _) (Set.mem_iInter.2 fun _ => hk) _⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.1 _)).trans (Eq.trans ?_ ((gs_mul (𝟙 X) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 X) y j j' hy.1 hy.2)))
      ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j') hy.2 _)))).symm)
  rw [FlatSec.gs_sec_trans u (𝟙 X) y (le j hy.1) (le j' hy.2), Fin.prod_univ_one, Nat.cast_one, zpow_one, Category.id_comp]

theorem isGenSec_of_flat {R F : Type} [CommRing R] [CommRing F] (g : R →+* F) (hg : g.Flat) (P : PolAV (Sp R))
    (th : H0 P.L 1) (hth : ∀ s : H0 P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal P.A.hom r) * th.f j)
    (q : Sp F ⟶ Sp R) (hq : q = Spec.map (CommRingCat.ofHom g)) :
    ∃ th' : LB.Sec (LPow P.A P.L 1 (Over.mk q)), IsGenSec P.A P.L 1 th' ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk q ⊗ P.A).left) (z : Z) (J), Good P.L z J →
        sval (φ := fun _ : Fin 1 => (snd (Over.mk q) P.A).left) (ε := fun _ => 1) th' r z J =
          sval th (r ≫ (snd (Over.mk q) P.A).left) z J := by
  subst hq
  set T : Over (Sp R) := Over.mk (Spec.map (CommRingCat.ofHom g)) with hT
  have hL := P.isLB
  have := P.isAb.proper
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have : QuasiSeparatedSpace P.A.left := quasiSeparatedSpace_of_quasiSeparated P.A.hom
  let th' : LB.Sec (LPow P.A P.L 1 T) := VVRank.pullTo (φ' := fun _ : Fin 1 => (snd T P.A).left) th (snd T P.A).left
    (fun _ => Category.comp_id _)
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ P.A).left) (z : Z) (J), Good P.L z J →
      sval (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => 1) th' r z J =
        sval th (r ≫ (snd T P.A).left) z J := fun Z r z J hJ => VVRank.sval_pullTo _ _ _ r z hJ
  refine ⟨th', fun s => ?_, hv⟩
  obtain ⟨σ, hσ⟩ := exists_sec hL (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => 1)
    (φ' := fun _ : PUnit => (snd T P.A).left) (ε' := fun _ => 1) (fun U _ h => by simp) s
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat R F g hg P.A.left P.A.hom (T ⊗ P.A).left (snd T P.A).left
    (fst T P.A).left (IsPullback.of_hasPullback T.hom P.A.hom).flip P.L hL σ
  choose u' hu' using fun i => exists_powerSection_of_chartFunctions (u i)
  choose r hr using fun i => hth (u' i)
  have key : SecM.ofSec P.A s = (show Γ(T.left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
      (∑ i, c i * g (r i))) • SecM.ofSec P.A th' := ThetaAct.sv_ext hL fun y J hJ => by
    let κ : F →+* (T ⊗ P.A).left.presheaf.stalk y := (((T ⊗ P.A).left.presheaf.germ ⊤ y trivial).hom.comp
      (fst T P.A).left.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    have k₁ : ∀ a, gs (fst T P.A).left y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a) = κ a :=
      fun a => gs_eq _ y ⊤ trivial _
    have k₂ : ∀ a, gs (𝟙 _) y ⊤ (AbLaw.cst (fst T P.A).left ⊤ a) = κ a := fun a =>
      (gs_res (𝟙 _) y (V := ⊤) le_top trivial _).trans ((gs_pull (𝟙 _) (fst T P.A).left y ⊤ trivial _).trans
        (by rw [Category.id_comp]; exact k₁ a))
    have k₃ : ∀ a, gs (snd T P.A).left y ⊤ (scal P.A.hom a) = κ (g a) := fun a => by
      refine (gs_pull (snd T P.A).left P.A.hom y ⊤ trivial _).trans ?_
      rw [show (snd T P.A).left ≫ P.A.hom = (fst T P.A).left ≫ T.hom from (pullback.condition (f := T.hom) (g := P.A.hom)).symm, ← k₁]
      refine (gs_pull (fst T P.A).left T.hom y ⊤ trivial _).symm.trans (congrArg _ ?_)
      exact (congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))).symm
    have hk : (snd T P.A).left y ∈ P.L.U (J (snd T P.A).left) := hJ _
    have hm : (snd T P.A).left y ∈ LB.wchart P.L (fun _ : Fin 1 => 𝟙 P.A.left) (fun _ => J (snd T P.A).left) :=
      Set.mem_iInter.2 fun _ => hk
    rw [ThetaAct.sv_smul _ _ _ _ hJ, Category.id_comp]
    refine (hσ _ _ y J hJ).symm.trans ((hu y _ (hJ (𝟙 _ ≫ (snd T P.A).left))).trans (Eq.trans ?_ (congrArg₂ (· * ·) (k₁ _) (hv _ _ y J hJ)).symm))
    rw [map_sum, Finset.sum_mul, Category.id_comp, sval_of th _ y J (fun _ => J (snd T P.A).left)
      (fun _ => by rw [Category.comp_id])]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [k₂, map_mul, _root_.mul_assoc, ← hu' i _ _ y _ hk, ← k₃]
    exact congrArg _ (((congrArg (gs _ y _) (hr i _)).trans (gs_mul _ y _ hm _ _)).trans (congrArg (· * _) (gs_res _ y _ hm _)))
  exact ⟨_, fun j => congrArg (fun q => q.1 j) key⟩

section Field

variable {F : Type} [Field F]

abbrev stkU (y : Sp F) : Fˣ →* ((Sp F).presheaf.stalk y)ˣ := Units.map (toStk y).toMonoidHom

theorem gm_unitOn (y : Sp F) (u : Fˣ) : gm (𝟙 (Sp F)) y ⊤ (unitOn u) = stkU y u :=
  Units.ext (gm_val _ y ⊤ trivial _)

theorem gs_fnOf (y : Sp F) (a : F) : gs (𝟙 (Sp F)) y ⊤ (fnOf a) = toStk y a := gs_eq _ y ⊤ trivial _

theorem toStk_valF' {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F)
    (h : x z ∈ U) (a : Γ(X, U)) : toStk z (valF x U a) = gs x z U a := by
  rw [valF, dif_pos ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

variable {X Y : Scheme.{0}} {M : LB X} {K : Type} [Fintype K]

theorem toStk_vF {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M φ ε)) (r : Sp F ⟶ Y) {y : Sp F} {J}
    (hJ : Good M y J) : toStk y (vF t r J) = (val t r y J).val := toStk_valF r _ y (hJ.mem φ r) _

theorem toStk_sF {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb M φ ε)) (r : Sp F ⟶ Y) {y : Sp F} {J}
    (hJ : Good M y J) : toStk y (sF s r J) = sval s r y J := toStk_valF' r _ y (hJ.mem φ r) _

theorem exists_gen_of_value (hM : M.IsLB) (φ : K → (Sp F ⟶ X)) (ε : K → ℤ) {y : Sp F} {J} (hJ : Good M y J)
    (u : Fˣ) : ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ val t (𝟙 _) y J = stkU y u := by
  have all : ∀ w : Sp F, w ∈ LB.wchart M φ fun k => J (𝟙 _ ≫ φ k) := fun w =>
    (top_le_iff_mem (𝟙 (Sp F)) _ y).2 (hJ.mem φ (𝟙 _)) trivial
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ fun k => J (𝟙 _ ≫ φ k) := fun j w hw => ⟨hw, all w⟩
  let t : LB.Gen (LB.LinComb M φ ε) := ⟨fun j => res (le j) ((LB.LinComb M φ ε).g j fun k => J (𝟙 _ ≫ φ k)) *
    res le_top (unitOn u)⟩
  have e : ∀ w j, w ∈ LB.wchart M φ j → gm (𝟙 _) w (LB.wchart M φ j) (t.s j) =
      trF φ ε (𝟙 _) w j (fun k => J (𝟙 _ ≫ φ k)) * stkU w u := fun w j h =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ w (le j) h _).trans (gm_linComb M _ ε (𝟙 _) w j _ h (all w)))
      ((gm_res _ w le_top h _).trans (gm_unitOn w u)))
  refine ⟨t, SymLiftOdd.isGen_of_gm fun w j j' h h' => ?_, (e y _ (all y)).trans ?_⟩
  · rw [e w j h, e w j' h', ← _root_.mul_assoc, trF_trans hM _ ε (𝟙 _) w h h' (all w)]
  · rw [mul_eq_left.1 (trF_trans hM φ ε (𝟙 _) y (all y) (all y) (all y)), _root_.one_mul]

end Field

open ThetaCompare

section RegSec

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {y : T.left}
  {J : (T.left ⟶ A.left) → L.ι}

theorem reg_gen (hL : L.IsLB) (hJ : Good L y J) {w} {F : (T ⟶ A) → (T.left.presheaf.stalk y)ˣ} (h : Reg L y J w F)
    (m m' : T ⊗ A ⟶ A) (a b : ℤ) (e : ∀ (U : Type) [CommGroup U] h, w U h = h m ^ a * h m' ^ b) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![m.left, m'.left] ![a, b]), u.IsGen ∧
      ∀ x, val u (ptSecT A x).left y J = F x := by
  obtain ⟨K, _, φ, ε, u, hu, hw, hF⟩ := h
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![m.left, m'.left]) (ε' := ![a, b])
    (fun U _ h => (hw U h).trans ((e U _).trans (by rw [Fin.prod_univ_two]; rfl))) u hu
  exact ⟨t, ht, fun x => (hv _ _ y J hJ).trans (hF x)⟩

theorem reg_base (hJ : Good L y J) (p : T ⟶ A) (a : ℤ)
    (t : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => p.left) (fun _ => a))) (ht : t.IsGen) :
    Reg L y J (fun _ _ h => h (fst T A ≫ p) ^ a) (fun _ => val t (𝟙 _) y J) :=
  ⟨_, _, _, _, LB.pullGen L _ _ t (fst T A).left, DVR.pullGen_isGen _ _ _ _ ht _,
    fun U _ h => Fin.prod_univ_one _, fun x => (val_pull hJ _ _ _).trans (by
      rw [← Over.comp_left, ptSecT, lift_fst]; rfl)⟩

theorem reg_sym (hJ : Good L y J) (s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1]))
    (hs : s.IsGen) : Reg L y J (fun _ _ h => h (snd T A)⁻¹ * (h (snd T A))⁻¹) (fun x => val s x.left y J) :=
  (Reg.two (LB.pullGen L _ _ s (snd T A).left) (DVR.pullGen_isGen _ _ _ _ hs _) (snd T A)⁻¹ (snd T A) rfl
    (Category.comp_id _)).congr (fun U _ h => by simp) (fun x => (val_pull hJ _ _ _).trans (by
      rw [← Over.comp_left, pt_snd]))

theorem corr_one [Subsingleton T.left] (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (hJ : Good L y J)
    {K : Type} [Fintype K] {φ : K → ((T ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
    (hF : ∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), ∏ k, h (φ k) ^ ε k = 1)
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (h : val u (ptSecT A (1 : T ⟶ A)).left y J = 1) :
    LB.Gen.Corr L _ _ _ _ u (LB.oneGen L) := by
  have e : (ptSecT A (1 : T ⟶ A)).left ≫ (fst T A).left = 𝟙 _ := by rw [← Over.comp_left, ptSecT, lift_fst]; rfl
  obtain ⟨c, hc⟩ := SymLiftOdd.exists_const hL (fst T A).left _ e (SymLiftOdd.surj_fst hG hA T) hF hu
  have c1 : c = 1 := unit_ext fun z _ => by
    obtain rfl := Subsingleton.elim y z
    rw [hc _ _ y J hJ, e] at h
    rw [h, map_one]
  exact corr_of_val hL fun z I hI => by rw [hc _ _ z I hI, c1, map_one, val_one]

theorem form_sym (hA : IsAbelianScheme A) {k : ℤ} (θ : ThetaGrp A L k T) {nu : LB.Gen (negLB A L k T)} (hnu : nu.IsGen)
    [Subsingleton T.left] (hG : GlobalFnsSt) (hL : L.IsLB) (hJ : Good L y J)
    (h : val (symGen A L k θ nu) (ptSecT A (1 : T ⟶ A)).left y J = 1) :
    LB.Gen.Corr L _ _ _ _ (symGen A L k θ nu) (LB.oneGen L) := by
  have := hA.comm
  refine corr_one hG hA hL hJ (fun U _ h => ?_) (SymLiftOdd.symGen_isGen θ hnu) h
  simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, ← Over.comp_left]
  have e : snd T A ≫ (GrpObj.inv : A ⟶ A) = (snd T A)⁻¹ := rfl
  rw [e, SymLiftOdd.translT_eq, SymLiftOdd.negT_eq, SymLiftOdd.comp_inv', SymLiftOdd.comp_inv', lift_snd, lift_snd,
    SymLiftOdd.lift_translPt, SymLiftOdd.lift_translPt, mul_inv_cancel_left, mul_inv, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_one]
  module

end RegSec

section Cube

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) {T : Over S}
  {y : T.left} {J : (T.left ⟶ A.left) → L.L.ι}

theorem reg_cub (hJ : Good L.L y J) (a b d : T ⊗ A ⟶ A) :
    Reg L.L y J (fun _ _ h => h (a * b * d) * (h (a * b))⁻¹ * (h (a * d))⁻¹ * (h (b * d))⁻¹ * h a * h b * h d * (h 1)⁻¹)
      (fun x => cubV c y J (ptSecT A x ≫ a) (ptSecT A x ≫ b) (ptSecT A x ≫ d)) :=
  ⟨_, _, _, _, LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift a (lift b d)).left, DVR.pullGen_isGen _ _ _ _ c.isGen _,
    fun _ _ h => prod_cub a b d h, fun x => val_cub c (ptSecT A x) hJ a b d⟩

theorem reg_cubN (hJ : Good L.L y J) (k : ℕ) (m d : T ⊗ A ⟶ A) :
    Reg L.L y J (fun _ _ h => h (m ^ k * d) * (h (m ^ k))⁻¹ * (h d)⁻¹ * h 1 * ((h (m * d))⁻¹ * h m * h d * (h 1)⁻¹) ^ k)
      (fun x => cubN (cubV c y J) k 1 (ptSecT A x ≫ m) (ptSecT A x ≫ d)) := by
  obtain ⟨t, ht, hv⟩ := exists_cubN c (1 : T ⊗ A ⟶ A) m d k
  refine ⟨_, _, _, _, t, ht, fun U _ h => ?_, fun x => (hv _ (ptSecT A x) y J hJ).trans (by rw [MonObj.comp_one])⟩
  apply Additive.ofMul.injective
  simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  module

theorem reg_mulq (hJ : Good L.L y J) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1]))
    (hs : s.IsGen) (n : ℕ) :
    Reg L.L y J (fun _ _ h => h (snd T A ^ n) * (h (snd T A) ^ (n ^ 2))⁻¹ * h 1 ^ (n ^ 2) * (h 1)⁻¹)
      (mulq (cubV c y J) (fun x => val s x.left y J) n) := by
  induction n with
  | zero =>
    exact ((reg_sym hJ s hs).pow hJ 0).congr (fun U _ h => by simp) (fun x => by simp [mulq])
  | succ n ih =>
    refine (ih.mul hJ ((reg_cubN c hJ n (snd T A) (snd T A)).mul hJ (((reg_cub c hJ (snd T A) (snd T A)⁻¹ (snd T A)).mul hJ
      (reg_sym hJ s hs).inv).pow hJ n).inv)).congr (fun U _ h => ?_) (fun x => ?_)
    · simp only [mul_inv_cancel, inv_mul_cancel, _root_.one_mul, ← pow_succ]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      module
    · simp only [mulq, dbl, Finset.prod_range_succ, SymLiftOdd.comp_inv', pt_snd, div_eq_mul_inv]

end Cube

section Alg

variable {A A' U U' : Type} [CommGroup A] [CommGroup A'] [CommGroup U] [CommGroup U'] {θ : A → A → A → U}
  {θ' : A' → A' → A' → U'} {σ : A → U} {σ' : A' → U'}

theorem cubN_map (e : A →* A') (f : U →* U') (h : ∀ x y u, θ' (e x) (e y) (e u) = f (θ x y u)) (k : ℕ) (b x : A) :
    cubN θ' k 1 (e b) (e x) = f (cubN θ k 1 b x) := by
  simp only [cubN, map_prod, _root_.one_mul, ← map_pow, h]

theorem mulq_map (e : A →* A') (f : U →* U') (h : ∀ x y u, θ' (e x) (e y) (e u) = f (θ x y u))
    (h' : ∀ x, σ' (e x) = f (σ x)) (k : ℕ) (x : A) : mulq θ' σ' k (e x) = f (mulq θ σ k x) := by
  simp only [mulq, dbl, map_prod, map_div, map_pow f, cubN_map e f h, ← map_inv e, h, h']

theorem cubN_mul (h : IsCub θ) {k : ℕ} {b : A} (hb : b ^ k = 1) (x y : A) :
    cubN θ k 1 b (x * y) * θ b x y ^ k = cubN θ k 1 b x * cubN θ k 1 b y := by
  simpa only [hb, _root_.mul_one, _root_.one_mul, h.face] using h.N_add k 1 b x y

theorem cubN_pow (h : IsCub θ) {k : ℕ} {b : A} (hb : b ^ k = 1) (j : ℕ) :
    cubN θ k 1 b (b ^ j) * cubN θ j 1 b b ^ k = cubN θ k 1 b b ^ j := by
  induction j with
  | zero => rw [pow_zero, h.N_one]; simp [cubN]
  | succ j ih =>
    have a := cubN_mul h hb (b ^ j) b
    have e : cubN θ (j + 1) 1 b b = cubN θ j 1 b b * θ b (b ^ j) b := by
      rw [cubN, Finset.prod_range_succ, _root_.one_mul, h.s01]; rfl
    rw [e, pow_succ, pow_succ, ← ih, mul_pow, mul_left_comm, a, mul_left_comm, _root_.mul_assoc]

variable {O : Type} [CommRing O] (B : NumB O)

theorem prod_cubN_wS {k : ℕ} (hk : Odd k) {b : B.A} (hb : b ^ k = 1) :
    ∏ j ∈ Finset.range k, cubN B.θ k 1 b (b ^ j) * B.wS k b 1 1 = 1 := by
  have e : ∏ j ∈ Finset.range k, cubN B.θ k 1 b (b ^ j) * (cubN B.θ j 1 b b / dbl B.θ B.σ b ^ j) ^ k =
      ∏ j ∈ Finset.range k, (cubN B.θ k 1 b b / dbl B.θ B.σ b ^ k) ^ j := Finset.prod_congr rfl fun j _ => by
    rw [div_pow, div_pow, ← cubN_pow B.cub hb j, ← pow_mul, ← pow_mul, mul_comm j k, mul_div_assoc]
  have s : ∑ j ∈ Finset.range k, j = (k - 1) / 2 * k := by
    obtain ⟨l, rfl⟩ := hk
    have := Finset.sum_range_id_mul_two (2 * l + 1)
    rw [Nat.add_sub_cancel] at this ⊢
    rw [Nat.mul_div_cancel_left l two_pos]
    nlinarith
  rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow_eq_pow_sum, s] at e
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, NumB.wS, _root_.one_mul, _root_.one_mul, div_pow,
    ← pow_mul, ← e, ← mul_div_assoc]
  exact div_self' _

theorem cubN_wS_sym {k : ℕ} (hk : Odd k) {b : B.A} (hb : b ^ k = 1) :
    cubN B.θ k 1 b b⁻¹ * B.wS k b 1 1 * (B.wS k b 1 1 * B.σ b⁻¹ ^ k) = 1 := by
  have a₁ := (GlobalTheory.T.mulq_dbl_cubN_relations O B k 1 b b).2.2.1
  have a₂ := cubN_mul B.cub hb b⁻¹ b
  have a₃ := B.σ_inv b
  rw [hb, B.cub.N_one, dbl, B.cub.face, B.σ_one] at a₁
  rw [inv_mul_cancel, B.cub.N_one] at a₂
  obtain ⟨l, rfl⟩ := hk
  rw [NumB.wS, Nat.add_sub_cancel, Nat.mul_div_cancel_left l two_pos]
  rw [dbl] at a₁ ⊢
  apply Additive.ofMul.injective
  replace a₁ := congrArg Additive.ofMul a₁
  replace a₂ := congrArg Additive.ofMul a₂
  replace a₃ := congrArg Additive.ofMul a₃
  simp only [ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₁ a₂ a₃ ⊢
  linear_combination (norm := module) -a₁ - a₂ + (2 * l + 1) • a₃

end Alg

section Main

open ThetaCompare CommPairing

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N) (y : (TF (R := R) F).left)

def sU : Fˣ →* ((TF (R := R) F).left.presheaf.stalk y)ˣ := stkU (F := F) y

def sR : F →+* (TF (R := R) F).left.presheaf.stalk y := toStk (F := F) y

theorem sU_val (u : Fˣ) : (sU y u).val = sR y u := rfl

theorem good : Good D.P.L y ν.J := fun ψ => ν.good ψ trivial

theorem cubV_eq (a b d : N.A) : cubV D.cub y ν.J (ν.eA a) (ν.eA b) (ν.eA d) = sU y (N.θ a b d) :=
  Units.ext ((toStk_vF _ _ (good ν y)).symm.trans (congrArg (toStk y) (ν.θ_eq a b d).symm))

theorem sym_eq (a : N.A) : val D.sym (ν.eA a).left y ν.J = sU y (N.σ a) :=
  Units.ext ((toStk_vF _ _ (good ν y)).symm.trans (congrArg (toStk y) (ν.σ_eq a).symm))

theorem reg_const (p : TF (R := R) F ⟶ D.P.A) (a : ℤ) (w : Fˣ) :
    Reg D.P.L y ν.J (fun _ _ h => h (fst _ D.P.A ≫ p) ^ a) (fun _ => sU y w) := by
  obtain ⟨t, ht, hv⟩ := exists_gen_of_value D.P.isLB (fun _ : Fin 1 => p.left) (fun _ => a) (good ν y) w
  exact (reg_base (good ν y) p a t ht).congr (fun _ _ _ => rfl) (fun _ => hv)

theorem exists_theta {k : ℕ} {κ : ℤ} (hκ : κ = k) {b : N.A} (hb : b ^ k = 1) (w : Fˣ) :
    ∃ U : ThetaGrp D.P.A D.P.L κ (TF (R := R) F), U.pt = ν.eA b ∧
      ∀ x, tval U (ptSecT D.P.A (ν.eA x)).left y ν.J = sU y (cubN N.θ k 1 b x * w) := by
  subst hκ
  have hJ := good ν y
  have e : (fst (TF (R := R) F) D.P.A ≫ ν.eA b) ^ k = 1 := by
    rw [← SymLiftOdd.comp_pow', ← map_pow, hb, map_one, MonObj.comp_one]
  obtain ⟨u, hu, hv⟩ := reg_gen D.P.isLB hJ
    (((reg_cubN D.cub hJ k (fst _ D.P.A ≫ ν.eA b) (snd _ D.P.A)).mul hJ (reg_const ν y (ν.eA b) (-k) w)).mul hJ
      (reg_const ν y 1 k 1)) (snd _ D.P.A) (translPt D.P.A (ν.eA b)) k (-k) (fun U _ h => by
      rw [e, MonObj.comp_one, _root_.one_mul, show translPt D.P.A (ν.eA b) = (fst _ D.P.A ≫ ν.eA b) * snd _ D.P.A from rfl]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
      module)
  refine ⟨⟨ν.eA b, u, hu⟩, rfl, fun x => (hv _).trans ?_⟩
  rw [map_one, _root_.mul_one, pt_snd, ptSecT, lift_fst_assoc, Category.id_comp, map_mul]
  exact congrArg (· * _) (cubN_map ν.eA.toMonoidHom (sU y) (cubV_eq ν y) k b x)

theorem weilIs_weil (hG : GlobalFnsSt) {k : ℕ} {b b' : N.A} (hb : b ^ k = 1) (hb' : b' ^ k = 1) :
    WeilIs D.P.A D.P.L k (ν.eA b) (ν.eA b') (unitOn (N.weil k b b')) := by
  obtain ⟨y⟩ : Nonempty (TF (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have : Subsingleton (TF (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨U, e, v⟩ := exists_theta ν y rfl hb 1
  obtain ⟨U', e', v'⟩ := exists_theta ν y rfl hb' 1
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_commIsOf hG D.P.isAb D.P.isLB U U'
  have q := (commIsOf_iff D.P.isLB U U' c).1 hc _ (ptSecT D.P.A (ν.eA 1)).left y ν.J (good ν y)
  rw [pt_translT, pt_translT, e, e', ← map_mul, ← map_mul, v, v, v', v', ← Over.comp_left, ptSecT, lift_fst] at q
  simp only [_root_.mul_one, N.cub.N_one, map_one, _root_.one_mul] at q
  obtain rfl : c = unitOn (N.weil k b b') := unit_ext fun z _ => by
    obtain rfl := Subsingleton.elim y z
    refine Eq.trans ?_ (show sU y _ = _ from (gm_unitOn y _).symm)
    rw [NumB.weil, map_div, q]
    exact (mul_div_cancel_left _ _).symm
  rw [← e, ← e']
  exact GlobalLift.weilIs_of_commIsOf hG D.P.isAb D.P.isLB hc

theorem exists_symLift (hG : GlobalFnsSt) {k : ℕ} (hk : Odd k) {κ : ℤ} (hκ : κ = k) {b : N.A} (hb : b ^ k = 1) :
    ∃ U : ThetaGrp D.P.A D.P.L κ (TF (R := R) F), SymLift D.P.A D.P.L κ k (ν.eA b) U ∧
      ∀ x, tval U (ptSecT D.P.A (ν.eA x)).left y ν.J = sU y (cubN N.θ k 1 b x * N.wS k b 1 1) := by
  have : Subsingleton (TF (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  have hJ := good ν y
  obtain ⟨U, e, v⟩ := exists_theta ν y hκ hb (N.wS k b 1 1)
  obtain ⟨n, hn, w⟩ := reg_gen D.P.isLB hJ ((reg_sym hJ D.sym D.sym_gen).pow hJ k).inv (snd _ D.P.A)
    (snd _ D.P.A ≫ (GrpObj.inv : D.P.A ⟶ D.P.A)) κ (-κ) (fun U _ h => by
      rw [hκ, show snd _ D.P.A ≫ (GrpObj.inv : D.P.A ⟶ D.P.A) = (snd _ D.P.A)⁻¹ from rfl]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
      module)
  have w' : ∀ x, GlobalLift.nval (k := κ) n (ptSecT D.P.A (ν.eA x)).left y ν.J = sU y (N.σ x ^ k)⁻¹ := fun x =>
    (w _).trans (by rw [sym_eq, map_inv, map_pow])
  refine ⟨U, ⟨e, corr_one hG D.P.isAb D.P.isLB hJ (SymLiftOdd.form_pow (by rw [e, ← map_pow, hb, map_one]))
    (SymLiftOdd.powGen_isGen U k) ?_, n, hn, form_sym D.P.isAb U hn hG D.P.isLB hJ ?_⟩, v⟩
  · rw [GlobalLift.val_powGen _ _ _ hJ, ← (sU y).map_one, ← prod_cubN_wS N.toNumB hk hb, map_prod, Finset.prod_range]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [pt_translT, e, _root_.mul_one, ← map_pow, v]
  · refine (GlobalLift.val_symGen U n _ hJ).trans ?_
    rw [pt_translT, pt_negT, e, _root_.mul_one, inv_one, ← map_inv, ← map_one ν.eA, v, v,
      w', w']
    refine Eq.trans ?_ ((congrArg (sU y) (cubN_wS_sym N.toNumB hk hb)).trans (map_one _))
    simp only [N.σ_one, N.cub.N_one, one_pow, inv_one, map_one, _root_.mul_one, _root_.one_mul, map_mul, map_inv, inv_inv]

theorem exists_th : ∃ (th : LB.Sec (LPow D.P.A D.P.L 1 (TF (R := R) F))) (ρ : Fˣ), IsGenSec D.P.A D.P.L 1 th ∧
    ∀ x, sval (φ := fun _ : Fin 1 => (snd (TF (R := R) F) D.P.A).left) (ε := fun _ => 1) th
      (ptSecT D.P.A (ν.eA x)).left y ν.J = sR y (N.th x * ρ) := by
  have hJ := good ν y
  have flat : ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))).Flat :=
    RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R)))
      (RingHom.flat_algebraMap_iff.2 inferInstance)
  obtain ⟨th, hth, vth⟩ := isGenSec_of_flat _ flat D.P ν.th ν.th_gen (jFK (R := R) F ≫ jK R)
    (by rw [CommRingCat.ofHom_comp, Spec.map_comp])
  have vρ := toStk_vF (M := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom hJ
  refine ⟨th, Units.mk0 _ fun h => Units.ne_zero _ (vρ.symm.trans ((congrArg (toStk y) h).trans (map_zero _))), hth,
    fun x => (vth _ _ y _ hJ).trans ?_⟩
  rw [← Over.comp_left, pt_snd]
  exact (toStk_sF ν.th (ν.eA x).left hJ).symm.trans (congrArg (toStk y) (ν.th_eq x).symm)

theorem exists_alpha (m : ℕ) : ∃ α : LB.Gen (LB.LinComb D.P.L (K := Fin 2)
      ![(snd (TF (R := R) F) D.P.A).left, (snd (TF (R := R) F) D.P.A ^ m).left] ![(m : ℤ) ^ 2, -1]), α.IsGen ∧
    ∀ a, val α (ptSecT D.P.A (ν.eA a)).left y ν.J = sU y (mulq N.θ N.σ m a)⁻¹ := by
  have hJ := good ν y
  have r₁ := reg_mulq D.cub hJ D.sym D.sym_gen m
  have r₂ := Reg.mul hJ (Reg.inv r₁) (reg_const ν y 1 ((m : ℤ) ^ 2 - 1) 1)
  obtain ⟨α, hα, vα⟩ := reg_gen D.P.isLB hJ r₂ (snd _ D.P.A) (snd _ D.P.A ^ m) ((m : ℤ) ^ 2) (-1) (fun U _ h => by
      rw [MonObj.comp_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
      module)
  refine ⟨α, hα, fun a => (vα _).trans ?_⟩
  have q := mulq_map (θ' := cubV D.cub y ν.J) (σ' := fun x => val D.sym x.left y ν.J) ν.eA.toMonoidHom (sU y)
    (cubV_eq ν y) (sym_eq ν y) m a
  exact (congrArg₂ (fun p q => p⁻¹ * q) q (map_one (sU y))).trans ((_root_.mul_one _).trans (map_inv (sU y) _).symm)

theorem isUnit_natCast {m : ℕ} (hF : (m : F) ≠ 0) : IsUnit (m : Γ((TF (R := R) F).left, ⊤)) := by
  have := (IsUnit.mk0 _ hF).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  rwa [map_natCast] at this

theorem isCoordPt_uth (hG : GlobalFnsSt) {m : ℕ} (hm : Odd m) (hF : (m : F) ≠ 0) {Ix : Type} {b : Ix → N.A}
    (hb : ∀ i, b i ^ m ^ 2 = 1) (x : N.A) :
    IsCoordPt D.P m (T := TF (R := R) F) (fun i => ν.eA (b i)) (ν.eA x) fun i => fnOf (N.uth m (b i) x) := by
  obtain ⟨y⟩ : Nonempty (TF (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have : Subsingleton (TF (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  have hJ := good ν y
  have hL := D.P.isLB
  obtain ⟨th, ρ, hth, vth⟩ := exists_th ν y
  obtain ⟨α, hα, vα⟩ := exists_alpha ν y m
  obtain ⟨τ, hτ, vτ⟩ : ∃ τ : LB.Gen (LB.LinComb D.P.L (Y := (TF (R := R) F).left) (K := Fin 1)
      (fun _ => (ν.eA x).left) (fun _ => (m : ℤ) ^ 2)), τ.IsGen ∧ val τ (𝟙 _) y ν.J = sU y ρ :=
    exists_gen_of_value hL (fun _ : Fin 1 => (ν.eA x).left) (fun _ => (m : ℤ) ^ 2) hJ ρ
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT D.P.A _ m) (snd _ D.P.A ^ m) (lift_snd _ _)
    ((m : ℤ) ^ 2) 1 α hα th
  choose U hU vU using fun i => exists_symLift ν y hG hm.pow (κ := (m : ℤ) ^ 2) (Nat.cast_pow m 2).symm (hb i)
  choose s₂ hs₂ using fun i => ThetaPtExist.exists_isTwistPull hL (translT D.P.A (U i).pt) (translPt D.P.A (U i).pt)
    (lift_snd _ _) ((m : ℤ) ^ 2) ((m : ℤ) ^ 2) (U i).φ (U i).isGen s₁
  refine ⟨hm, isUnit_natCast hF, th, s₁, α, τ, U, s₂, hth, hα, hτ, hs₁, hU, hs₂, fun i => ?_⟩
  obtain ⟨v, hv⟩ := ThetaPtExist.exists_isValueAt hL (s₂ i) (ν.eA x) τ hτ
  have b₁ := sval_valueAt hv hJ
  have b₂ := (sval_twist (hs₂ i) (ptSecT D.P.A (ν.eA x)).left hJ).trans (congrArg (fun q => Units.val q * _) (vU i x))
  have b₃ := (sval_twist hs₁ (ptSecT D.P.A (ν.eA (x * b i))).left hJ).trans
    (congrArg (fun q => Units.val q * _) (vα (x * b i)))
  rw [pt_mulT, ← map_pow, vth] at b₃
  rw [pt_translT, (hU i).pt_eq, ← map_mul ν.eA, mul_comm (b i), b₃, b₁, vτ] at b₂
  obtain rfl : v = fnOf (N.uth m (b i) x) := fn_ext fun z _ => by
    obtain rfl := Subsingleton.elim y z
    refine Eq.trans ?_ (show sR y _ = _ from (gs_fnOf y _).symm)
    refine (Units.mul_left_inj (sU y ρ)).1 (b₂.trans ?_)
    rw [sU_val, sU_val, sU_val, ← map_mul, ← map_mul, ← map_mul, NumB.uth, NumB.uV, NumB.mth, N.cub.face, div_one]
    congr 1
    ring
  exact hv

theorem isThetaPt_uth (hG : GlobalFnsSt) {m : ℕ} (hm : Odd m) (hF : (m : F) ≠ 0) {Ix : Type} {b : Ix → N.A}
    (hb : ∀ i, b i ^ m ^ 2 = 1) :
    IsThetaPt D.P m (T := TF (R := R) F) (fun i => ν.eA (b i)) fun i => fnOf (N.uth m (b i) 1) := by
  refine ⟨hm, isUnit_natCast hF, fun p => ⟨⊤, trivial, ?_⟩⟩
  have : Subsingleton (TF (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨h, hh⟩ := GlobalLift.exists_section (T := TF (R := R) F) (V := ⊤) (p := p) trivial
  have hi : overResι (T := TF (R := R) F) ⊤ ≫ h = 𝟙 _ := by
    haveI : Mono (overResι (T := TF (R := R) F) ⊤) :=
      Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : (TF (R := R) F).left.Opens).ι))
    rw [← cancel_mono (overResι (T := TF (R := R) F) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]
  have H := isCoordPt_uth ν hG hm hF hb 1
  rw [map_one] at H
  obtain ⟨-, -, th, s₁, α, τ, U, s₂, a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩ := H
  exact ThetaCoord.isThetaPtOver_pull D.P ⟨th, s₁, α, τ, U, s₂, _, 1, a₁, a₂, a₃, a₄, a₅, a₆, a₇,
    fun i => (_root_.one_mul _).symm⟩ _ h hi

end Main

end GlobalTheory.ThetaInValues
