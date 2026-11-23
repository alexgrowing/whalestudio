import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecMInvariantEqBotOrUnivAtGeometricPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSecValueIsUnit
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.CoordSep

open GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank

theorem exists_ratio_base {X Y S₀ : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ c : Γ(S₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val u r z J = val u' r z J * gm (r ≫ p) z ⊤ c := by
  obtain ⟨c, hc⟩ := SymLiftOdd.exists_const hL p e he hp (fun U _ h => (Fintype.prod_sum_type _).trans (by
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]))
    (DVR.mulGen_isGen L _ _ _ _ u (LB.invGen L _ _ u') hu (DVR.invGen_isGen _ _ _ _ hu'))
  refine ⟨c, fun Z r z J hJ => ?_⟩
  rw [← hc Z r z J hJ, val_mul hJ, val_inv, mul_comm, inv_mul_cancel_right]

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ}

abbrev Frame (L : LB A.left) (k : ℤ) (z : T ⟶ A) :=
  LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => k))

theorem sv_value {s : LB.Sec (LPow A L k T)} {z : T ⟶ A} {τ : Frame L k z} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L k s z τ v) {y : T.left} {J} (hJ : Good L y J) :
    sv A s (lift (𝟙 T) z).left y J = gs (𝟙 T.left) y ⊤ v * (val τ (𝟙 T.left) y J).val := by
  have := sv_of_isValueAt H (𝟙 T) hJ
  rwa [Category.id_comp] at this

theorem value_unique (hL : L.IsLB) {s : LB.Sec (LPow A L k T)} {z : T ⟶ A} {τ : Frame L k z} {v v' : Γ(T.left, ⊤)}
    (H : IsValueAt A L k s z τ v) (H' : IsValueAt A L k s z τ v') : v = v' := fn_ext fun y _ => by
  choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ y)
  exact (Units.mul_left_inj _).1 ((sv_value H hJ).symm.trans (sv_value H' hJ))

theorem value_smul (hL : L.IsLB) {s s' : LB.Sec (LPow A L k T)} {c : Γ(T.left, ⊤)}
    (e : SecM.ofSec A s' = c • SecM.ofSec A s) {z : T ⟶ A} {τ : Frame L k z} (hτ : τ.IsGen) {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L k s z τ v) : IsValueAt A L k s' z τ (c * v) :=
  isValueAt_of_sv hL hτ fun y J hJ => by
    have := ThetaAct.sv_smul c (SecM.ofSec A s) (lift (𝟙 T) z).left y hJ
    rw [← e, lift_fst_left] at this
    refine this.trans ?_
    rw [gs_mul _ _ ⊤ trivial, _root_.mul_assoc, ← sv_value H hJ]
    rfl

theorem exists_unit_frame (hL : L.IsLB) {z : T ⟶ A} {τ τ' : Frame L k z} (hτ : τ.IsGen) (hτ' : τ'.IsGen) :
    ∃ d : Γ(T.left, ⊤)ˣ, ∀ s v, IsValueAt A L k s z τ v → IsValueAt A L k s z τ' (d * v) := by
  obtain ⟨d, hd⟩ := exists_ratio_base hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun a => ⟨a, rfl⟩) hτ hτ'
  refine ⟨d, fun s v H => isValueAt_of_sv hL hτ' fun y J hJ => ?_⟩
  have := hd _ (𝟙 _) y J hJ
  rw [Category.id_comp] at this
  rw [sv_value H hJ, this, gs_mul _ _ ⊤ trivial, gs_unit _ _ ⊤ trivial, Units.val_mul]
  ring

theorem exists_rescale {z : T ⟶ A} {τ : Frame L k z} (hτ : τ.IsGen) (u : Γ(T.left, ⊤)ˣ) :
    ∃ τ' : Frame L k z, τ'.IsGen ∧ ∀ s v, IsValueAt A L k s z τ v → IsValueAt A L k s z τ' (u * v) := by
  refine ⟨⟨fun j => τ.s j * res le_top u⁻¹⟩, fun i j => ?_, fun s v H j => ?_⟩
  · rw [map_mul, map_mul, hτ i j, _root_.mul_assoc]
    refine congrArg (fun q => _ * (_ * q)) (unit_ext fun y hy => ?_)
    exact ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.1 _)).trans
      ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.2 _)).symm
  · rw [H j, map_mul]
    have e : (T.left.presheaf.map (homOfLE (le_top : LB.wchart L (fun _ : Fin 1 => z.left) j ≤ ⊤)).op).hom u.val *
        (T.left.presheaf.map (homOfLE (le_top : LB.wchart L (fun _ : Fin 1 => z.left) j ≤ ⊤)).op).hom
          (u⁻¹).val = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have key : ∀ {R : Type} [CommRing R] (a b c d : R), a * b = 1 → c * d = a * c * (d * b) := fun a b c d h => by
      linear_combination (-(c * d)) * h
    exact key _ _ _ _ e

omit [GrpObj A] in

theorem exists_frame (hL : L.IsLB) [Subsingleton T.left] [Nonempty T.left] (z : T ⟶ A) :
    ∃ τ : Frame L k z, τ.IsGen := by
  obtain ⟨p⟩ := ‹Nonempty T.left›
  obtain ⟨i, hi⟩ := exists_chart hL (z.left p)
  exact AbSquare.exists_gen_of_mem_chart hL _ _ (fun _ => i) fun _ y => by rwa [Subsingleton.elim y p]

theorem rel_of_mem_span {I : Type} {t : I → SecM A L k T} {z z' : T ⟶ A} {y : T.left} {J} (hJ : Good L y J)
    {a b : T.left.presheaf.stalk y}
    (h : ∀ i, ThetaAct.sv (t i) (lift (𝟙 T) z).left y J * a = ThetaAct.sv (t i) (lift (𝟙 T) z').left y J * b)
    {w : SecM A L k T} (hw : w ∈ Submodule.span Γ(T.left, ⊤) (Set.range t)) :
    ThetaAct.sv w (lift (𝟙 T) z).left y J * a = ThetaAct.sv w (lift (𝟙 T) z').left y J * b := by
  have sm : ∀ (c : Γ(T.left, ⊤)) (w : SecM A L k T),
      ThetaAct.sv w (lift (𝟙 T) z).left y J * a = ThetaAct.sv w (lift (𝟙 T) z').left y J * b →
      ThetaAct.sv (c • w) (lift (𝟙 T) z).left y J * a = ThetaAct.sv (c • w) (lift (𝟙 T) z').left y J * b :=
    fun c w h => by
      rw [ThetaAct.sv_smul _ _ _ _ hJ, ThetaAct.sv_smul _ _ _ _ hJ, lift_fst_left, lift_fst_left, _root_.mul_assoc, h,
        _root_.mul_assoc]
  induction hw using Submodule.span_induction with
  | mem w hw => obtain ⟨i, rfl⟩ := hw; exact h i
  | zero =>
    rw [← zero_smul Γ(T.left, ⊤) (0 : SecM A L k T), ThetaAct.sv_smul _ _ _ _ hJ, ThetaAct.sv_smul _ _ _ _ hJ,
      gs_eq _ _ ⊤ trivial, gs_eq _ _ ⊤ trivial]
    simp only [map_zero, zero_mul]
  | add w w' _ _ h h' => rw [ThetaAct.sv_add _ _ _ _ hJ, ThetaAct.sv_add _ _ _ _ hJ, add_mul, add_mul, h, h']
  | smul c w _ h => exact sm c w h

theorem value_eq_of_span (hL : L.IsLB) {I : Type} {t : I → LB.Sec (LPow A L k T)} {z z' : T ⟶ A} {τ : Frame L k z}
    {τ' : Frame L k z'} {v : I → Γ(T.left, ⊤)} (hv : ∀ i, IsValueAt A L k (t i) z τ (v i))
    (hv' : ∀ i, IsValueAt A L k (t i) z' τ' (v i)) {T' : Over S} (h : T' ⟶ T)
    (H : Submodule.span Γ(T'.left, ⊤) (Set.range fun i => pullM A L k h (SecM.ofSec A (t i))) = ⊤)
    {σ : Frame L k (h ≫ z)} {σ' : Frame L k (h ≫ z')}
    (hσ : ∀ y J, Good L y J → val σ (𝟙 T'.left) y J = val τ h.left y J)
    (hσ' : ∀ y J, Good L y J → val σ' (𝟙 T'.left) y J = val τ' h.left y J)
    {w : LB.Sec (LPow A L k T')} {a a' : Γ(T'.left, ⊤)} (ha : IsValueAt A L k w (h ≫ z) σ a)
    (ha' : IsValueAt A L k w (h ≫ z') σ' a') : a = a' := fn_ext fun y _ => by
  choose J hJ using fun χ : T'.left ⟶ A.left => exists_chart hL (χ y)
  replace hJ : Good L y J := hJ
  have e : ∀ (i) {z : T ⟶ A} {τ : Frame L k z}, IsValueAt A L k (t i) z τ (v i) →
      ThetaAct.sv (pullM A L k h (SecM.ofSec A (t i))) (lift (𝟙 T') (h ≫ z)).left y J =
        gs h.left y ⊤ (v i) * (val τ h.left y J).val := fun i z τ hv => by
    refine (sv_pullS A k h (t i) _ y hJ).trans ?_
    rw [← Over.comp_left, lift_whiskerRight, Category.id_comp]
    exact sv_of_isValueAt hv h hJ
  have q : sv A w (lift (𝟙 T') (h ≫ z)).left y J * (val τ' h.left y J).val =
      sv A w (lift (𝟙 T') (h ≫ z')).left y J * (val τ h.left y J).val :=
    rel_of_mem_span hJ (fun i => by rw [e i (hv i), e i (hv' i), mul_right_comm]) (w := SecM.ofSec A w)
      (H.ge trivial)
  rw [sv_value ha hJ, sv_value ha' hJ, hσ y J hJ, hσ' y J hJ, mul_right_comm] at q
  exact (Units.mul_left_inj _).1 ((Units.mul_left_inj _).1 q)

end General

variable {S : Scheme.{0}} (P : PolAV S) {T : Over S}

def IsThetaFam (k : ℕ) (a : ℤ) {I : Type} (x : I → (T ⟶ P.A)) (t : I → LB.Sec (LPow P.A P.L a T)) : Prop :=
  ∃ (th : LB.Sec (LPow P.A P.L 1 T)) (s1 : LB.Sec (LPow P.A P.L a T))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![a, -1]))
    (U : I → ThetaGrp P.A P.L a T), IsGenSec P.A P.L 1 th ∧ α.IsGen ∧
    IsTwistPull P.A P.L (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _) a 1 α th s1 ∧
    (∀ i, SymLift P.A P.L a (k ^ 2) (x i) (U i)) ∧ ∀ i, IsActOf P.A P.L a (U i) s1 (t i)

theorem isCoordPt_iff {k : ℕ} (hk : Odd k) (hu : IsUnit (k : Γ(T.left, ⊤))) {I : Type} (x : I → (T ⟶ P.A))
    (z : T ⟶ P.A) (v : I → Γ(T.left, ⊤)) :
    IsCoordPt P k x z v ↔ ∃ (t : I → LB.Sec (LPow P.A P.L ((k : ℤ) ^ 2) T)) (τ : Frame P.L ((k : ℤ) ^ 2) z),
      IsThetaFam P k _ x t ∧ τ.IsGen ∧ ∀ i, IsValueAt P.A P.L _ (t i) z τ (v i) :=
  ⟨fun ⟨_, _, th, s1, α, τ, U, t, h1, h2, h3, h4, h5, h6, h7⟩ => ⟨t, τ, ⟨th, s1, α, U, h1, h2, h4, h5, h6⟩, h3, h7⟩,
    fun ⟨t, τ, ⟨th, s1, α, U, h1, h2, h4, h5, h6⟩, h3, h7⟩ =>
      ⟨hk, hu, th, s1, α, τ, U, t, h1, h2, h3, h4, h5, h6, h7⟩⟩

variable {P}

theorem IsThetaFam.exists_unit (hG : GlobalFnsSt) [Subsingleton T.left] {k : ℕ} (hk : Odd k) {a : ℤ} {I : Type}
    {x : I → (T ⟶ P.A)} {t t' : I → LB.Sec (LPow P.A P.L a T)} (H : IsThetaFam P k a x t)
    (H' : IsThetaFam P k a x t') :
    ∃ e : Γ(T.left, ⊤)ˣ, ∀ i, SecM.ofSec P.A (t' i) = (e : Γ(T.left, ⊤)) • SecM.ofSec P.A (t i) := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, U, hth, hα, hs₁, hU, ht⟩ := H
  obtain ⟨th', s₁', α', U', hth', hα', hs₁', hU', ht'⟩ := H'
  obtain ⟨ρ, hρ⟩ := exists_unit_of_isGenSec hth' hth
  obtain ⟨c, hc⟩ := exists_ratio_base hL (fst T P.A).left (lift (𝟙 T) (1 : T ⟶ P.A)).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (SymLiftOdd.surj_fst hG P.isAb T) hα' hα
  refine ⟨ρ * c, fun i => ThetaAct.sv_ext hL fun y J hJ => ?_⟩
  rw [ThetaAct.sv_smul _ _ _ _ hJ, gs_unit _ _ ⊤ trivial, map_mul, Category.id_comp, SymLiftOdd.id_eq_lift]
  change sv P.A (t' i) _ y J = _ * sv P.A (t i) _ y J
  have a₀ : tval (U' i) (lift (fst T P.A) (snd T P.A)).left y J = tval (U i) (lift (fst T P.A) (snd T P.A)).left y J :=
    val_corr hJ (SymLiftOdd.symLift_unique hG P.isAb hL hk.pow _ _ (hU' i) (hU i)) _
  have a₁ : ∀ p : T ⊗ P.A ⟶ P.A, bval (b := 1) α' (lift (fst T P.A) p).left y J =
      bval (b := 1) α (lift (fst T P.A) p).left y J * gm (fst T P.A).left y ⊤ c := fun p => by
    have := hc _ (lift (fst T P.A) p).left y J hJ
    rw [lift_fst_left] at this
    exact this
  have a₃ : ∀ p : T ⊗ P.A ⟶ P.A, sv P.A th' (lift (fst T P.A) p).left y J =
      (gm (fst T P.A).left y ⊤ ρ).val * sv P.A th (lift (fst T P.A) p).left y J := fun p => by
    have := ThetaAct.sv_smul (ρ : Γ(T.left, ⊤)) (SecM.ofSec P.A th) (lift (fst T P.A) p).left y hJ
    rw [← hρ, lift_fst_left, gs_unit _ _ ⊤ trivial] at this
    exact this
  rw [sv_act (hU' i).pt_eq (ht' i) _ hJ, sv_act (hU i).pt_eq (ht i) _ hJ, sv_mulPull hs₁ _ hJ, sv_mulPull hs₁' _ hJ,
    a₀, a₁, a₃, Units.val_mul, Units.val_mul]
  ring

theorem isThetaPt_iff [Subsingleton T.left] [Nonempty T.left] {k : ℕ} (hk : Odd k) (hu : IsUnit (k : Γ(T.left, ⊤)))
    {I : Type} (x : I → (T ⟶ P.A)) (v : I → Γ(T.left, ⊤)) : IsThetaPt P k x v ↔ IsCoordPt P k x 1 v := by
  rw [isCoordPt_iff P hk hu]
  constructor
  · intro H
    obtain ⟨th, s1, α, τ, U, t, w, u, h1, h2, h3, h4, h5, h6, h7, h8⟩ := isThetaPtOver_of_subsingleton P H
    obtain ⟨τ', hτ', h⟩ := exists_rescale h3 u
    exact ⟨t, τ', ⟨th, s1, α, U, h1, h2, h4, h5, h6⟩, hτ', fun i => h8 i ▸ h _ _ (h7 i)⟩
  · rintro ⟨t, τ, ⟨th, s1, α, U, h1, h2, h4, h5, h6⟩, h3, h7⟩
    refine ⟨hk, hu, fun p => ⟨⊤, trivial, ?_⟩⟩
    obtain ⟨h, hh⟩ := exists_section (T := T) (V := ⊤) (p := p) trivial
    have hi : overResι (T := T) ⊤ ≫ h = 𝟙 _ := by
      haveI : Mono (overResι (T := T) ⊤) :=
        Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : T.left.Opens).ι))
      rw [← cancel_mono (overResι (T := T) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]
    exact isThetaPtOver_pull P ⟨th, s1, α, τ, U, t, v, 1, h1, h2, h3, h4, h5, h6, h7,
      fun i => (_root_.one_mul _).symm⟩ (overResι ⊤) h hi

theorem isCoordPt_iff_unit (hG : GlobalFnsSt) [Subsingleton T.left] {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)}
    {z : T ⟶ P.A} {v : I → Γ(T.left, ⊤)} (H : IsCoordPt P k x z v) (v' : I → Γ(T.left, ⊤)) :
    IsCoordPt P k x z v' ↔ ∃ u : Γ(T.left, ⊤)ˣ, ∀ i, v' i = u * v i := by
  have hk := H.1
  have hu := H.2.1
  rw [isCoordPt_iff P hk hu] at H ⊢
  obtain ⟨t, τ, ht, hτ, hv⟩ := H
  constructor
  · rintro ⟨t', τ', ht', hτ', hv'⟩
    obtain ⟨e, he⟩ := ht.exists_unit hG hk ht'
    obtain ⟨d, hd⟩ := exists_unit_frame P.isLB hτ hτ'
    exact ⟨d * e, fun i => by
      rw [Units.val_mul, _root_.mul_assoc]
      exact value_unique P.isLB (hv' i) (hd _ _ (value_smul P.isLB (he i) hτ (hv i)))⟩
  · rintro ⟨u, hu⟩
    obtain ⟨τ', hτ', h⟩ := exists_rescale hτ u
    exact ⟨t, τ', ht, hτ', fun i => hu i ▸ h _ _ (hv i)⟩

section Field

variable (hLaw : Laws) {K : Type} [Field K] [IsAlgClosed K] [IsLocallyNoetherian S] (s : Sp K ⟶ S)
include hLaw

theorem exists_isThetaFam {k : ℕ} (hk : Odd k) {I : Type} (x : I → (Over.mk s ⟶ P.A)) (hx : ∀ i, x i ^ k ^ 2 = 1) :
    ∃ t, IsThetaFam P k ((k : ℤ) ^ 2) x t := by
  have hL := P.isLB
  let T : Over S := Over.mk s
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨t, -, ht⟩ : ∃ t : SecM P.A P.L 1 T, t ≠ 0 ∧ ∀ s, ∃ r : Γ(T.left, ⊤), r • t = s :=
    ThetaPtExist.exists_generator_of_isField (MulEquiv.isField (Field.toIsField K) e.symm.toMulEquiv)
      (((secM_invariant_eq_bot_or_univ_at_geometric_point hLaw.polBaseChange).1 hLaw.globalSectionsRank S P K s 1 le_rfl).trans (one_pow _))
  obtain ⟨th, hth⟩ := ThetaPtExist.exists_isGenSec_of_retract hL (𝟙 T) (𝟙 T) (Category.comp_id _) t ht
  obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ P k
  obtain ⟨α, hα, -⟩ := exists_gen_pullTo (φ' := ![(snd T P.A).left, (snd T P.A ^ k).left]) α₀ hα₀ (snd T P.A).left
    (fun i => by
      fin_cases i
      · exact Category.comp_id _
      · change (snd T P.A).left ≫ (mulA P.A k).left = (snd T P.A ^ k).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _)
    ((k : ℤ) ^ 2) 1 α hα th
  have sym := (symLift_odd hLaw.globalFns
    (kerPow_of_square (AbSquare.square_of_cube AbLaw.CubeAssembly.cube_gen).1).2.2 (exists_gen_negLB hLaw.globalFns)).1
  have hU : ∀ i, ∃ θ : ThetaGrp P.A P.L ((k : ℤ) ^ 2) T, SymLift P.A P.L ((k : ℤ) ^ 2) (k ^ 2) (x i) θ := fun i => by
    obtain ⟨V, hV, θ, hθ⟩ := (sym S P (k ^ 2) hk.pow T (x i) (hx i)).1 p
    obtain ⟨h, hh⟩ := exists_section hV
    obtain ⟨θ', hθ'⟩ := exists_symLift_pull hL h hθ
    rw [← Category.assoc, hh, Category.id_comp] at hθ'
    rw [← Nat.cast_pow]
    exact ⟨θ', hθ'⟩
  choose U hU using hU
  choose s₂ hs₂ using fun i => ThetaPtExist.exists_isTwistPull hL (translT P.A (U i).pt) (translPt P.A (U i).pt)
    (lift_snd _ _) ((k : ℤ) ^ 2) ((k : ℤ) ^ 2) (U i).φ (U i).isGen s₁
  exact ⟨s₂, th, s₁, α, U, hth, hα, hs₁, hU, hs₂⟩

theorem IsThetaFam.span_eq_top {k N : ℕ} (hk : 1 ≤ k) (hN : 4 ≤ N) (hK : (N : K) ≠ 0) {I : Type}
    {x : I → (Over.mk s ⟶ P.A)} (hx : ∀ y : Over.mk s ⟶ P.A, y ^ N = 1 → ∃ i, x i = y)
    {t : I → LB.Sec (LPow P.A P.L N (Over.mk s))} (H : IsThetaFam P k N x t) :
    Submodule.span Γ((Over.mk s).left, ⊤) (Set.range fun i => SecM.ofSec P.A (t i)) = ⊤ := by
  obtain ⟨th, s₁, α, U, hth, -, hs₁, hU, ht⟩ := H
  obtain ⟨ρ, k₁, -, k₃, k₄⟩ := thetaGrp_acts_linearly hLaw.globalFns S P N (Over.mk s)
  obtain ⟨h0, irr⟩ := secM_invariant_eq_bot_or_univ_at_geometric_point hLaw.polBaseChange
  haveI : Nonempty I := let ⟨i, _⟩ := hx 1 (one_pow _); ⟨i⟩
  have e : ∀ i, SecM.ofSec P.A (t i) = ρ (U i) (SecM.ofSec P.A s₁) := fun i => ((k₁ _ _ _).1 (ht i)).symm
  simp only [e]
  refine span_translates_eq_top P.A (irr hLaw.irred S P K s N (Or.inr hN) hK) ρ k₁ k₃ k₄ U (fun θ => ?_) _ fun hz => ?_
  · obtain ⟨i, hi⟩ := hx θ.pt ((hLaw.kerPow S P N (by omega) (Over.mk s) θ.pt).1 fun _ =>
      ⟨⊤, trivial, _, LB.isGen_genPull _ θ.φ θ.isGen _⟩)
    exact ⟨i, (hU i).pt_eq.trans hi⟩
  · have hint : IsIntegral (Over.mk s ⊗ P.A).left :=
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom P.isAb.smooth
        P.isAb.geomConnected).geometrically_isIntegral s _ _ (IsPullback.of_hasPullback s P.A.hom).flip
    have hz' := ofSec_eq_zero_of_twist P.A P.isLB (surjective_mulT P.A k (hLaw.mulN S P k hk).2.2.1 _) hs₁ hz
    have hr : Module.finrank Γ((Over.mk s).left, ⊤) (SecM P.A P.L 1 (Over.mk s)) = 1 :=
      (h0 hLaw.globalSectionsRank S P K s 1 le_rfl).trans (one_pow _)
    obtain ⟨w, hw, -⟩ := ThetaPtExist.exists_generator_of_isField (MulEquiv.isField (Field.toIsField K)
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv) hr
    obtain ⟨r, hr'⟩ := hth (SecM.toSec P.A w)
    have : w = r • SecM.ofSec P.A th := Subtype.ext (funext hr')
    exact hw (by rw [this, hz', smul_zero])

omit [IsAlgClosed K] in

theorem span_pull_eq_top {N : ℕ} (hN : 1 ≤ N) {I : Type} {t : I → SecM P.A P.L N (Over.mk s)}
    (H : Submodule.span Γ((Over.mk s).left, ⊤) (Set.range t) = ⊤) (T' : Over S) [IsAffine T'.left]
    (h : T' ⟶ Over.mk s) :
    Submodule.span Γ(T'.left, ⊤) (Set.range fun i => pullM P.A P.L N h (t i)) = ⊤ := by
  obtain ⟨V, hV, b, hb⟩ := hLaw.secBaseChange S P N hN (s (IsLocalRing.closedPoint K))
  let h₀ : Over.mk s ⟶ overRes (T := baseOver S) V := Over.homMk (IsOpenImmersion.lift V.ι s (by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι, Subsingleton.elim (α := PrimeSpectrum K) q (IsLocalRing.closedPoint K)]
      exact hV))
    ((congrArg (_ ≫ ·) (Category.comp_id V.ι)).trans (IsOpenImmersion.lift_fac _ _ _))
  obtain ⟨c, hc⟩ := exists_basis P N b hb T' (h ≫ h₀)
  have key : ∀ w ∈ Submodule.span Γ((Over.mk s).left, ⊤) (Set.range t), pullM P.A P.L N h w ∈
      Submodule.span Γ(T'.left, ⊤) (Set.range fun i => pullM P.A P.L N h (t i)) := fun w hw =>
    (Submodule.span_le (p := Submodule.comap (pullM P.A P.L N h)
      (Submodule.span Γ(T'.left, ⊤) (Set.range fun i => pullM P.A P.L N h (t i))))).2 (by
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩) hw
  rw [eq_top_iff, ← c.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [hc, ← pullM_comp P.A P.isLB]
  exact key _ (H.ge trivial)

omit [IsAlgClosed K] in

theorem eq_of_span {N : ℕ} (hN : 3 ≤ N) {I : Type} {t : I → LB.Sec (LPow P.A P.L N (Over.mk s))}
    (H : Submodule.span Γ((Over.mk s).left, ⊤) (Set.range fun i => SecM.ofSec P.A (t i)) = ⊤)
    {z z' : Over.mk s ⟶ P.A} {τ : Frame P.L N z} {τ' : Frame P.L N z'} (hτ : τ.IsGen) (hτ' : τ'.IsGen)
    {v : I → Γ((Over.mk s).left, ⊤)} (hv : ∀ i, IsValueAt P.A P.L N (t i) z τ (v i))
    (hv' : ∀ i, IsValueAt P.A P.L N (t i) z' τ' (v i)) : z = z' := by
  haveI : IsLocallyNoetherian (Over.mk s).left := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
  refine SepPoints.eq_of_forall_value_eq forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    AbLaw.CubeAssembly.cube_gen hLaw.secBaseChange (fun S _ P n hn => let h := hLaw.mulN S P n hn;
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) S P N hN _ z z' τ τ' hτ hτ' fun T' _ h w a a' ha ha' => ?_
  exact value_eq_of_span P.isLB hv hv' h (span_pull_eq_top hLaw s (by omega) H T' h)
    (fun y J hJ => (val_pull hJ τ h.left (𝟙 _)).trans (by rw [Category.id_comp]))
    (fun y J hJ => (val_pull hJ τ' h.left (𝟙 _)).trans (by rw [Category.id_comp])) ha ha'

theorem ne_zero_of_span {N : ℕ} (hN : 2 ≤ N) {I : Type} {t : I → LB.Sec (LPow P.A P.L N (Over.mk s))}
    (H : Submodule.span Γ((Over.mk s).left, ⊤) (Set.range fun i => SecM.ofSec P.A (t i)) = ⊤)
    {z : Over.mk s ⟶ P.A} {τ : Frame P.L N z} {v : I → Γ((Over.mk s).left, ⊤)}
    (hv : ∀ i, IsValueAt P.A P.L N (t i) z τ (v i)) : ¬ ∀ i, v i = 0 := fun h0 => by
  obtain ⟨w, τ', a, -, ha, hu⟩ := NoBasePoint.exists_sec_value_isUnit
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    (AbSquare.square_of_cube AbLaw.CubeAssembly.cube_gen).1
    ((secM_invariant_eq_bot_or_univ_at_geometric_point hLaw.polBaseChange).1 hLaw.globalSectionsRank) (fun S _ P n hn => let h := hLaw.mulN S P n hn;
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) S P K s N hN z
  let y : (Over.mk s).left := IsLocalRing.closedPoint K
  choose J hJ using fun χ : (Over.mk s).left ⟶ P.A.left => exists_chart P.isLB (χ y)
  replace hJ : Good P.L y J := hJ
  have q := rel_of_mem_span (z := z) (z' := z) (a := 1) (b := 0) hJ
    (fun i => by
      rw [_root_.mul_one, mul_zero]
      refine (sv_value (hv i) hJ).trans ?_
      rw [h0, gs_eq _ _ ⊤ trivial, map_zero, map_zero, zero_mul]) (w := SecM.ofSec P.A w) (H.ge trivial)
  rw [_root_.mul_one, mul_zero] at q
  obtain ⟨u, rfl⟩ := hu
  have := (sv_value ha hJ).symm.trans q
  rw [gs_unit _ _ ⊤ trivial, ← Units.val_mul] at this
  exact Units.ne_zero _ this

theorem eq_and_ne_zero {k : ℕ} (hk : 3 ≤ k) (hK : (k : K) ≠ 0) {a : ℤ} (ha : a = (k ^ 2 : ℕ)) {I : Type}
    {x : I → (Over.mk s ⟶ P.A)} (hx : ∀ y : Over.mk s ⟶ P.A, y ^ k ^ 2 = 1 → ∃ i, x i = y)
    {t : I → LB.Sec (LPow P.A P.L a (Over.mk s))} (H : IsThetaFam P k a x t)
    {z z' : Over.mk s ⟶ P.A} {τ : Frame P.L a z} {τ' : Frame P.L a z'} (hτ : τ.IsGen) (hτ' : τ'.IsGen)
    {v : I → Γ((Over.mk s).left, ⊤)} (hv : ∀ i, IsValueAt P.A P.L a (t i) z τ (v i))
    (hv' : ∀ i, IsValueAt P.A P.L a (t i) z' τ' (v i)) : z = z' ∧ ¬ ∀ i, v i = 0 := by
  subst ha
  have h4 : 4 ≤ k ^ 2 := by nlinarith
  have hs := H.span_eq_top hLaw s (by omega) h4 (by rw [Nat.cast_pow]; exact pow_ne_zero _ hK) hx
  exact ⟨eq_of_span hLaw s (by omega) hs hτ hτ' hv hv', ne_zero_of_span hLaw s (by omega) hs hv⟩

end Field

theorem coord_exists_unique_separate : Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (s : Sp K ⟶ S) (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (Ix : Type) (x : Ix → (Over.mk s ⟶ P.A)), (∀ i, x i ^ m ^ 2 = 1) → (∀ z, ∃ v : Ix → K, IsCoordPt P m x z fun i => fnOf (v i)) ∧ (∀ z (v v' : Ix → K), (IsCoordPt P m x z fun i => fnOf (v i)) → ((IsCoordPt P m x z fun i => fnOf (v' i)) ↔ ∃ c : Kˣ, v' = (c : K) • v)) ∧ (∀ v : Ix → K, (IsThetaPt P m x fun i => fnOf (v i)) ↔ IsCoordPt P m x 1 fun i => fnOf (v i)) ∧ (3 ≤ m → (∀ y : Over.mk s ⟶ P.A, y ^ m ^ 2 = 1 → ∃ i, x i = y) → ∀ z z' (v : Ix → K), (IsCoordPt P m x z fun i => fnOf (v i)) → (IsCoordPt P m x z' fun i => fnOf (v i)) → z = z' ∧ v ≠ 0) := by
  intro hLaw K _ _ S _ P s m hm hK Ix x hx
  let e : Γ((Over.mk s).left, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have he : ∀ a : K, fnOf a = e.symm a := fun _ => rfl
  haveI : Subsingleton (Over.mk s).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI : Nonempty (Over.mk s).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have hu : IsUnit (m : Γ((Over.mk s).left, ⊤)) := by
    rw [← map_natCast e.symm]
    exact (IsUnit.mk0 _ hK).map e.symm
  refine ⟨fun z => ?_, fun z v v' H => ?_, fun v => isThetaPt_iff hm hu x _, fun h3 hall z z' v H H' => ?_⟩
  · obtain ⟨t, ht⟩ := exists_isThetaFam hLaw s hm x hx
    obtain ⟨τ, hτ⟩ := exists_frame (k := (m : ℤ) ^ 2) P.isLB z
    choose w hw using fun i => ThetaPtExist.exists_isValueAt P.isLB (t i) z τ hτ
    refine ⟨fun i => e (w i), (isCoordPt_iff P hm hu x z _).2 ⟨t, τ, ht, hτ, fun i => ?_⟩⟩
    rw [he, e.symm_apply_apply]
    exact hw i
  · refine (isCoordPt_iff_unit hLaw.globalFns H _).trans ⟨fun ⟨u, h⟩ => ⟨Units.map e.toMonoidHom u, funext fun i => ?_⟩,
      fun ⟨c, h⟩ => ⟨Units.map e.symm.toMonoidHom c, fun i => ?_⟩⟩
    · have q := (congrArg e (h i)).trans (map_mul e _ _)
      exact (e.apply_symm_apply (v' i)).symm.trans (q.trans (congrArg (_ * ·) (e.apply_symm_apply (v i))))
    · subst h
      exact map_mul e.symm (c : K) (v i)
  · obtain ⟨t, τ, ht, hτ, hv⟩ := (isCoordPt_iff P hm hu x z _).1 H
    obtain ⟨t', τ', ht', hτ', hv'⟩ := (isCoordPt_iff P hm hu x z' _).1 H'
    obtain ⟨u, hu'⟩ := ht'.exists_unit hLaw.globalFns hm ht
    obtain ⟨τ'', hτ'', h⟩ := exists_rescale hτ' u⁻¹
    obtain ⟨h₁, h₂⟩ := eq_and_ne_zero hLaw s h3 hK (Nat.cast_pow m 2).symm hall ht hτ hτ'' hv fun i => by
      have := h _ _ (value_smul P.isLB (hu' i) hτ' (hv' i))
      rwa [Units.inv_mul_cancel_left] at this
    exact ⟨h₁, fun h0 => h₂ fun i => by rw [h0]; exact map_zero e.symm⟩

end GlobalTheory.CoordSep
