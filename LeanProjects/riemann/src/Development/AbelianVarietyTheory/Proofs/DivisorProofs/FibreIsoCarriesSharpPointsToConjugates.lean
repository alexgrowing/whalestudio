import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.ConjPt

open GlobalTheory.UT.SymFrame

section Tools

variable {X Y Y' : Scheme.{0}} {L : LB X}

theorem exists_powSec (hL : L.IsLB) {K K₃ K' : Type} [Fintype K] [Fintype K₃] [Fintype K'] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (N : ℕ) {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) (φ' : K' → (Y' ⟶ X)) (ε' : K' → ℤ)
    (hF : ∀ (U : Type) [CommGroup U] (f : (Y' ⟶ X) → U),
      (∏ k, f (h ≫ φ k) ^ ε k) ^ N * ∏ k, f (φ₃ k) ^ ε₃ k = ∏ k, f (φ' k) ^ ε' k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε'), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J ^ N * (val u r z J).val := by
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := φ') (ε' := ε') (fun U _ f => by
      rw [← hF U f, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin])
    (pullMulSec (H1.SectionArithmetic.powSec (fun _ : Fin N => s)) h u hu)
  refine ⟨s', fun Z r z J hJ => ?_⟩
  rw [hs' Z r z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, H1.SectionArithmetic.sval_powSec _ _ _ hJ]
  simp

theorem exists_fn (s : LB.Sec (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim)) :
    ∃ a : Γ(Y, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), sval s r z J = gs r z ⊤ a := by
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Y.presheaf.map (homOfLE le).op).hom (s.f PEmpty.elim), fun Z r z J => ?_⟩
  rw [sval_of s r z J PEmpty.elim (fun k => k.elim)]
  exact (gs_res r z le trivial _).symm

theorem exists_gen_of_lbIso {p p' : Y ⟶ X} (h : LBIso (L.pull p) (L.pull p')) :
    ∃ ω : LB.Gen (LB.LinComb L ![p', p] ![1, -1]), ω.IsGen := by
  obtain ⟨w, hw⟩ := h
  have l : ∀ j : Fin 2 → L.ι, LB.wchart L ![p', p] j ≤ (L.pull p').U (fun _ => j 0) ⊓ (L.pull p).U (fun _ => j 1) :=
    fun j y hy => ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1⟩
  refine ⟨⟨fun j => res (l j) (w.s (fun _ => j 0, fun _ => j 1))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have hm : y ∈ (LB.div (L.pull p') (L.pull p)).U (fun _ => i 0, fun _ => i 1) ⊓
      (LB.div (L.pull p') (L.pull p)).U (fun _ => j 0, fun _ => j 1) := ⟨l i hy.1, l j hy.2⟩
  have e := congrArg (gm (𝟙 Y) y _) (hw (fun _ => i 0, fun _ => i 1) (fun _ => j 0, fun _ => j 1))
  refine ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans (((gm_res _ y _ hm _).symm.trans e).trans ?_)
  rw [map_mul, map_mul]
  refine congrArg₂ (· * ·) ?_ ((gm_res _ y _ hm _).trans ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)).symm)
  refine Eq.trans ?_ (gm_linComb L ![p', p] ![1, -1] (𝟙 Y) y i j hy.1 hy.2).symm
  refine (map_mul _ _ _).trans ?_
  rw [Fin.prod_univ_two]
  refine congrArg₂ (· * ·) ((gm_res _ y _ hm _).trans ((gm_linComb L _ _ (𝟙 Y) y _ _ (l i hy.1).1 (l j hy.2).1).trans
    (Fintype.prod_unique _))) ((map_inv _ _).trans ?_)
  refine (congrArg (·⁻¹) ((gm_res _ y _ hm _).trans ((gm_linComb L _ _ (𝟙 Y) y _ _ (l i hy.1).2 (l j hy.2).2).trans
    (Fintype.prod_unique _)))).trans ?_
  simp

theorem grep_const (hL : L.IsLB) {S : Scheme.{0}} {B : Over S} (e : S ⟶ B.left) (he : e ≫ B.hom = 𝟙 S)
    (hp : Function.Surjective B.hom.appTop.hom) {P v} (h : GRep L B P v)
    (hP : ∀ (U : Type) [CommGroup U] (h : (B.left ⟶ X) → U), P U h = 1) :
    ∃ a : Γ(S, ⊤)ˣ, ∀ (T : Over S) (r : T ⟶ B) (z : T.left) (J), Good L z J → v T r z J = gm T.hom z ⊤ a := by
  obtain ⟨K, _, φ, ε, s, hs, h₁, h₂⟩ := h
  obtain ⟨a, ha⟩ := SymLiftOdd.exists_const hL B.hom e he hp (fun U _ h => (h₁ U h).trans (hP U h)) hs
  exact ⟨a, fun T r z J hJ => by rw [← h₂ T r z J hJ, ha _ _ z J hJ, Over.w]⟩

theorem grep_unit {S : Scheme.{0}} (B : Over S) (a : Γ(S, ⊤)ˣ) :
    GRep L B (fun _ _ _ => 1) (fun T _ z _ => gm T.hom z ⊤ a) := by
  refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, ⟨fun _ => res le_top (pullU B.hom ⊤ a)⟩, fun i j => ?_,
    fun _ _ _ => Fintype.prod_empty _, fun T r z J _ => ?_⟩
  · refine Eq.trans ?_ ((congrArg₂ (· * ·) (Fintype.prod_empty _) rfl).trans (_root_.one_mul _)).symm
    exact unit_ext fun y hy => ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.1 _)).trans
      ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.2 _)).symm
  · refine (gm_res r.left z le_top (Set.mem_iInter.2 fun k => k.elim) _).trans ((gm_pull r.left B.hom z ⊤ trivial a).trans ?_)
    rw [Over.w]

end Tools

section Theta

open GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank GlobalTheory.CoordSep

variable {S : Scheme.{0}} (P : PolAV S)

abbrev Th : Type := LB.Sec (LB.LinComb P.L (fun _ : Fin 1 => 𝟙 P.A.left) (fun _ => 1))

def GenAll (θ : Th P) : Prop :=
  ∀ (K : Type) [Field K] (s : Sp K ⟶ S) (t : LB.Sec (LPow P.A P.L 1 (Over.mk s))), ∃ c : Γ(Sp K, ⊤),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk s ⊗ P.A).left) (z : Z) (J), Good P.L z J →
      sv P.A t r z J = gs (r ≫ (fst (Over.mk s) P.A).left) z ⊤ c * sval θ (r ≫ (snd (Over.mk s) P.A).left) z J

theorem exists_genAll {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (P : PolAV (Sp V)) :
    ∃ θ : Th P, GenAll P θ := by
  obtain ⟨U, hU, b, hb⟩ := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange (Sp V) P 1 le_rfl (closedPoint V)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  let T₀ : Over (Sp V) := overRes (T := baseOver (Sp V)) ⊤
  let h : ∀ T : Over (Sp V), T ⟶ T₀ := fun T => Over.homMk (IsOpenImmersion.lift (⊤ : (Sp V).Opens).ι T.hom (by
      rw [Scheme.Opens.range_ι]; exact fun _ _ => trivial))
    ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  have hu : ∀ {T : Over (Sp V)} (a a' : T ⟶ T₀), a = a' := fun a a' => by
    apply Over.OverMorphism.ext
    rw [← cancel_mono (⊤ : (Sp V).Opens).ι]
    have e := Over.w a
    have e' := Over.w a'
    exact (congrArg (_ ≫ ·) (Category.comp_id _).symm).trans ((e.trans e'.symm).trans
      (congrArg (_ ≫ ·) (Category.comp_id _)))
  let i : Fin (1 ^ P.g) := ⟨0, by simp⟩
  obtain ⟨θ, hθ⟩ := exists_sec P.isLB (φ' := fun _ : Fin 1 => 𝟙 P.A.left) (ε' := fun _ => 1)
    (fun U _ f => Finset.prod_congr rfl fun _ _ => by
      rw [← Over.comp_left, lift_snd]; rfl)
    (H1.SectionArithmetic.pullSec (φ := fun _ : Fin 1 => (snd T₀ P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) (b i)
      (lift (h P.A) (𝟙 P.A)).left)
  refine ⟨θ, fun K _ s t => ?_⟩
  haveI : IsAffine (Over.mk s).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  obtain ⟨c, hc⟩ := exists_basis P 1 b hb (Over.mk s) (h _)
  haveI : Subsingleton (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  have e := c.sum_repr (SecM.ofSec P.A t)
  rw [Fintype.sum_subsingleton _ i, hc] at e
  refine ⟨c.repr (SecM.ofSec P.A t) i, fun Z r z J hJ => ?_⟩
  have q := ThetaAct.sv_smul (c.repr (SecM.ofSec P.A t) i)
    (pullM P.A P.L ((1 : ℕ) : ℤ) (h (Over.mk s)) (SecM.ofSec P.A (b i))) r z hJ
  refine ((congrArg (fun w => ThetaAct.sv w r z J) e).symm.trans q).trans (congrArg (_ * ·) ?_)
  refine (sv_pullS P.A _ (h _) (b i) r z hJ).trans ?_
  refine Eq.trans ?_ ((hθ _ _ z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ)).symm
  rw [Category.assoc, ← Over.comp_left]
  refine congrArg (fun q : Over.mk s ⊗ P.A ⟶ T₀ ⊗ P.A => sv P.A (b i) (r ≫ q.left) z J) ?_
  apply CartesianMonoidalCategory.hom_ext
  · exact hu _ _
  · simp

abbrev psiLB (N : ℕ) (b : 𝟙_ (Over S) ⟶ P.A) : LB P.A.left :=
  LB.LinComb P.L ![𝟙 P.A.left, ((toUnit P.A ≫ b) * 𝟙 P.A).left] ![(N : ℤ), -(N : ℤ)]

theorem comp_transl {T : Over S} (x : T ⟶ P.A) (b : 𝟙_ (Over S) ⟶ P.A) :
    x.left ≫ ((toUnit P.A ≫ b) * 𝟙 P.A).left = ((toUnit T ≫ b) * x).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem eq_of_translates [IsLocallyNoetherian S] {θ : Th P} (hθ : GenAll P θ) {K : Type} [Field K] [IsAlgClosed K]
    (s : Sp K ⟶ S) {N : ℕ} (hN : 4 ≤ N) (hK : (N : K) ≠ 0) {C : Type} (b : C → (𝟙_ (Over S) ⟶ P.A))
    (hb : ∀ y : Over.mk s ⟶ P.A, y ^ N = 1 → ∃ c, y = toUnit _ ≫ b c)
    (Ψ : ∀ c, LB.Gen (psiLB P N (b c))) (hΨ : ∀ c, (Ψ c).IsGen) (y y' : Over.mk s ⟶ P.A)
    (z : (Over.mk s).left) (J) (hJ : Good P.L z J) (m : (Over.mk s).left.presheaf.stalk z)
    (H : ∀ c, sval θ ((toUnit _ ≫ b c) * y').left z J ^ N * (val (Ψ c) y'.left z J).val =
      m * (sval θ ((toUnit _ ≫ b c) * y).left z J ^ N * (val (Ψ c) y.left z J).val)) : y = y' := by
  have hLaw := GlobalTheory.abelianSchemeLaws_all.1
  have hL := P.isLB
  let T : Over S := Over.mk s
  haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI : Nonempty T.left := ⟨z⟩
  have hF : IsField Γ(T.left, ⊤) := MulEquiv.isField (Field.toIsField K)
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨s₁, hs₁⟩ := exists_powSec hL θ (snd T P.A).left N (LB.oneGen P.L) (Frames.oneGen_gen _)
    (fun _ : Fin 1 => (snd T P.A).left) (fun _ => (N : ℤ)) (fun U _ f => by simp)
  choose φ hφ vφ using fun c => exists_gen_pullTo (φ' := ![(snd T P.A).left, (translPt P.A (toUnit T ≫ b c)).left])
    (Ψ c) (hΨ c) (snd T P.A).left (fun k => by
      fin_cases k
      · exact Category.comp_id _
      · refine (comp_transl P _ _).trans (congrArg (fun q : T ⊗ P.A ⟶ P.A => q.left) ?_)
        show _ = (fst T P.A ≫ toUnit T ≫ b c) * snd T P.A
        rw [← Category.assoc, comp_toUnit])
  let U : C → ThetaGrp P.A P.L N T := fun c => ⟨toUnit T ≫ b c, φ c, hφ c⟩
  choose t ht using fun c => ThetaPtExist.exists_isTwistPull hL (translT P.A (U c).pt) (translPt P.A (U c).pt)
    (lift_snd _ _) (N : ℤ) (N : ℤ) (U c).φ (U c).isGen s₁
  have hspan : Submodule.span Γ(T.left, ⊤) (Set.range fun i => SecM.ofSec P.A (t i)) = ⊤ := by
    obtain ⟨ρ, k₁, -, k₃, k₄⟩ := thetaGrp_acts_linearly hLaw.globalFns S P N T
    obtain ⟨h0, irr⟩ := secM_invariant_eq_bot_or_univ_at_geometric_point hLaw.polBaseChange
    haveI : Nonempty C := let ⟨i, _⟩ := hb 1 (one_pow _); ⟨i⟩
    have e : ∀ i, SecM.ofSec P.A (t i) = ρ (U i) (SecM.ofSec P.A s₁) := fun i => ((k₁ _ _ _).1 (ht i)).symm
    simp only [e]
    refine span_translates_eq_top P.A (irr hLaw.irred S P K s N (Or.inr hN) hK) ρ k₁ k₃ k₄ U (fun θ => ?_) _ fun hz => ?_
    · obtain ⟨i, hi⟩ := hb θ.pt ((hLaw.kerPow S P N (by omega) T θ.pt).1 fun _ =>
        ⟨⊤, trivial, _, LB.isGen_genPull _ θ.φ θ.isGen _⟩)
      exact ⟨i, hi.symm⟩
    · have hint : IsIntegral (T ⊗ P.A).left :=
        (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom P.isAb.smooth
          P.isAb.geomConnected).geometrically_isIntegral s _ _ (IsPullback.of_hasPullback s P.A.hom).flip
      have hr : Module.finrank Γ(T.left, ⊤) (SecM P.A P.L 1 T) = 1 :=
        (h0 hLaw.globalSectionsRank S P K s 1 le_rfl).trans (one_pow _)
      obtain ⟨w, hw, -⟩ := ThetaPtExist.exists_generator_of_isField hF hr
      obtain ⟨a, ha⟩ := hθ K s (SecM.toSec P.A w)
      refine hw (ThetaAct.sv_ext hL fun x I hI => ?_)
      have z0 : ∀ k, ThetaAct.sv (0 : SecM P.A P.L k T) (𝟙 _) x I = 0 := fun k => by
        rw [← zero_smul Γ(T.left, ⊤) (0 : SecM P.A P.L k T), ThetaAct.sv_smul _ _ _ _ hI, gs_eq _ _ ⊤ trivial]
        simp only [map_zero, zero_mul]
      have q := hs₁ _ (𝟙 _) x I hI
      rw [val_one, Units.val_one, _root_.mul_one] at q
      have q' : sval θ (𝟙 _ ≫ (snd T P.A).left) x I ^ N = 0 := q.symm.trans (by rw [← z0 N, ← hz]; rfl)
      rw [z0]
      refine (ha _ _ x I hI).trans ?_
      rw [pow_eq_zero_iff (by omega) |>.1 q', mul_zero]
  have hv : ∀ (x : T ⟶ P.A) c, sv P.A (t c) (lift (𝟙 T) x).left z J =
      sval θ ((toUnit _ ≫ b c) * x).left z J ^ N * (val (Ψ c) x.left z J).val := fun x c => by
    rw [sv_act (θ := U c) rfl (ht c) (𝟙 T) hJ x, mul_comm]
    refine congrArg₂ (· * ·) ((hs₁ _ _ z J hJ).trans ?_) (congrArg Units.val ((vφ c _ _ z J hJ).trans ?_))
    · rw [val_one, Units.val_one, _root_.mul_one, ← Over.comp_left, lift_snd, Category.id_comp]
    · rw [← Over.comp_left, lift_snd]
  obtain ⟨τ, hτ⟩ := exists_frame (k := (N : ℤ)) hL y
  obtain ⟨τ', hτ'⟩ := exists_frame (k := (N : ℤ)) hL y'
  choose v hv₁ using fun c => ThetaPtExist.exists_isValueAt hL (t c) y τ hτ
  choose v' hv₂ using fun c => ThetaPtExist.exists_isValueAt hL (t c) y' τ' hτ'
  have rel : ∀ c, gs (𝟙 T.left) z ⊤ (v' c) * (val τ' (𝟙 T.left) z J).val =
      m * (gs (𝟙 T.left) z ⊤ (v c) * (val τ (𝟙 T.left) z J).val) := fun c => by
    rw [← sv_value (hv₁ c) hJ, ← sv_value (hv₂ c) hJ, hv, hv, H]
  have inj : ∀ a a' : Γ(T.left, ⊤), gs (𝟙 T.left) z ⊤ a = gs (𝟙 T.left) z ⊤ a' → a = a' := fun a a' h =>
    fn_ext fun x _ => by rwa [Subsingleton.elim x z]
  have cross : ∀ c c', v' c * v c' = v' c' * v c := fun c c' => inj _ _ (by
    rw [gs_mul _ _ ⊤ trivial, gs_mul _ _ ⊤ trivial]
    refine (Units.mul_left_inj (val τ' (𝟙 T.left) z J)).1 ?_
    linear_combination gs (𝟙 T.left) z ⊤ (v c') * rel c - gs (𝟙 T.left) z ⊤ (v c) * rel c')
  obtain ⟨c₀, hc₀⟩ := not_forall.1 (ne_zero_of_span hLaw s (by omega) hspan hv₁)
  obtain ⟨c₁, hc₁⟩ := not_forall.1 (ne_zero_of_span hLaw s (by omega) hspan hv₂)
  letI := hF.toField
  have h₀ : v' c₀ ≠ 0 := fun h => mul_ne_zero hc₁ hc₀ (by rw [cross, h, zero_mul])
  obtain ⟨τ'', hτ'', h⟩ := exists_rescale hτ (Units.mk0 (v' c₀ / v c₀) (div_ne_zero h₀ hc₀))
  refine eq_of_span hLaw s (by omega) hspan hτ'' hτ' (v := v') (fun c => ?_) hv₂
  have := h _ _ (hv₁ c)
  rwa [Units.val_mk0, div_mul_eq_mul_div, ← cross, mul_div_cancel_right₀ _ hc₀] at this

end Theta

section Integral

open GlobalTheory.UT.CoefBasic GlobalTheory.TorusExt GlobalTheory.VVRank

variable {V : Type} [CommRing V] [IsDomain V] {D : DegPre V}

theorem kap_rel {N : ℕ} {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)} (hκ : Normd κ)
    {κ' : LB.Gen (kapLB D (𝟙 D.P.A ^ (N + 1)) ((N + 1) ^ 2) 1)} (hκ' : Normd κ')
    {T : Over (Sp V)} (b : T ⟶ D.P.A) (hb : b ^ N = 1) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val κ' b.left z J ^ (N ^ 2) = val κ b.left z J ^ (N * (N + 2)) := by
  have key := (((grep_kap κ' hκ'.1 (𝟙 D.P.A ^ N)).mul ((grep_kap κ hκ.1 (𝟙 D.P.A)).pow ((N + 1) ^ 2))).mul
    ((grep_kap κ hκ.1 (𝟙 D.P.A ^ (N + 1))).mul ((grep_kap κ' hκ'.1 (𝟙 D.P.A)).pow (N ^ 2))).inv).triv
    GlobalTheory.abelianSchemeLaws_all.1.globalFns (fun U _ h => by
      rw [← pow_mul, ← pow_mul, mul_comm (N + 1) N]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, ← natCast_zsmul]
      push_cast
      module)
    (fun y J hJ => by
      beta_reduce
      rw [comp_id_pow, comp_id_pow, one_pow, one_pow, Category.comp_id, normd_one hκ hJ, normd_one hκ' hJ]
      simp) T b z J hJ
  beta_reduce at key
  rw [comp_id_pow, comp_id_pow, pow_succ b, hb, _root_.one_mul b, Category.comp_id, normd_one hκ' hJ, _root_.one_mul,
    mul_inv_eq_one] at key
  refine (mul_left_cancel (Eq.trans ?_ key)).symm
  rw [← pow_succ']
  congr 1
  ring

theorem grep_cubProd {Y : Over (Sp V)} (c b : Y ⟶ D.P.A) (n : ℕ) :
    GRep D.P.L Y
      (fun _ _ h => h (c * b ^ n).left * (h (b ^ n).left)⁻¹ * (h c.left)⁻¹ * h (1 : Y ⟶ D.P.A).left *
        ((h (c * b).left)⁻¹ * h c.left * h b.left * (h (1 : Y ⟶ D.P.A).left)⁻¹) ^ n)
      (fun _ r z J => ∏ i ∈ Finset.range n, cubV D.cub z J (r ≫ c) (r ≫ b ^ i) (r ≫ b)) := by
  induction n with
  | zero =>
    exact ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen D.P.L, Frames.oneGen_gen _,
      fun _ _ _ => by simp, fun _ _ _ _ _ => by simp [val_one]⟩
  | succ n ih =>
    refine (ih.mul (SymFrame.grep_cub c (b ^ n) b)).congr (fun _ _ h => ?_)
      (fun _ _ _ _ _ => (Finset.prod_range_succ _ _).symm)
    rw [_root_.mul_assoc c, ← pow_succ b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

theorem exists_gen_local [IsLocalRing V] {K : Type} [Fintype K] (φ : K → (Sp V ⟶ D.P.A.left)) (ε : K → ℤ) :
    ∃ t : LB.Gen (LB.LinComb D.P.L φ ε), t.IsGen := by
  choose i hi using fun k => exists_chart D.P.isLB (φ k (closedPoint V))
  exact AbSquare.exists_gen_of_mem_chart D.P.isLB φ ε i fun k y => by
    have : φ k ⁻¹ᵁ D.P.L.U (i k) = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 (hi k)
    exact (this.ge trivial : y ∈ φ k ⁻¹ᵁ D.P.L.U (i k))

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_psi [IsLocalRing V] [IsNoetherianRing V] [IsIntegrallyClosed V] {N : ℕ} (hN : 1 ≤ N)
    (g : GtPtF D (FractionRing V)) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A)
    (hgb : g.b = toUnit _ ≫ b) (ho : ∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero)
    (w : Frm D (FractionRing V) 1 g.b)
    (hw : w.IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.P.L z J →
      val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J = 1) :
    ∃ Ψ : LB.Gen (psiLB D.P N b), Ψ.IsGen ∧
      (∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ (T : Over (Sp V)) (z : T.left) (J),
        Good D.P.L z J → val Ψ (1 : T ⟶ D.P.A).left z J ^ N * val κ (toUnit T ≫ b).left z J = 1) ∧
      ∀ χ z J, Good D.P.L z J → val Ψ (toUnit (TF (R := V) (FractionRing V)) ≫ D.c χ).left z J =
        (val (g.s χ) (𝟙 _) z J * val w (𝟙 _) z J) ^ N := by
  have hL := D.P.isLB
  obtain ⟨hgN, hbN⟩ := Frames.torsion_of_nsmul g b hgb ho
  obtain ⟨t, ht⟩ := exists_gen_local (D := D) ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)
  obtain ⟨u, hu, -⟩ := Frames.frame_unit hN g b hgb ho w hw t ht
  let a : Γ(Sp V, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.toMonoidHom u
  have ha : ∀ z J, Good D.P.L z J → val w (𝟙 _) z J = gm (TF (R := V) (FractionRing V)).hom z ⊤ a *
      val t (TF (R := V) (FractionRing V)).hom z J := fun z J hJ => Units.ext (by
    rw [hu z J hJ, Units.val_mul]
    refine congrArg (· * _) (Eq.trans ?_ (Frames.gm_top_eq a z).symm)
    congr 2
    exact ((Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.apply_symm_apply _).symm)
  obtain ⟨Ψ, hΨ, vΨ⟩ := ((grep_cubProd (𝟙 D.P.A) (toUnit _ ≫ b) N).mul
    (((grep_unit D.P.A a).mul (grep_gen t ht D.P.A.hom)).pow N)).out hL
    ![𝟙 D.P.A.left, ((toUnit D.P.A ≫ b) * 𝟙 D.P.A).left] ![(N : ℤ), -(N : ℤ)] (fun U _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two, ← MonObj.comp_pow, hbN, MonObj.comp_one, _root_.mul_one,
        mul_comm (𝟙 D.P.A)]
      show _ * (1 * (h (1 : D.P.A ⟶ D.P.A).left ^ ((1 : ℕ) : ℤ) * h (toUnit _ ≫ b).left ^ (-((1 : ℕ) : ℤ)))) ^ N =
        h (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (N : ℤ) * h ((toUnit D.P.A ≫ b) * 𝟙 D.P.A).left ^ (-(N : ℤ))
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, ← natCast_zsmul]
      push_cast
      module)
  have v1 : ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.P.L z J →
      val Ψ (1 : T ⟶ D.P.A).left z J = (gm T.hom z ⊤ a * val t T.hom z J) ^ N := fun T z J hJ => by
    have C : IsCub (cubV D.cub (T := T) z J) := isCub_cubV D.cub hJ
    rw [vΨ T 1 z J hJ]
    beta_reduce
    rw [Over.w, Category.comp_id, Finset.prod_eq_one fun i _ => C.face _ _, _root_.one_mul]
  refine ⟨Ψ, hΨ, fun κ hκ T z J hJ => ?_, fun χ z J hJ => ?_⟩
  · obtain ⟨x, hx⟩ := grep_const hL (B := 𝟙_ (Over (Sp V))) (𝟙 _) (Category.id_comp _) (fun a => ⟨a, rfl⟩)
      (((grep_gen Ψ hΨ (1 : 𝟙_ (Over (Sp V)) ⟶ D.P.A).left).pow N).mul (grep_kap κ hκ.1 b)) (fun U _ h => by
        rw [Fin.prod_univ_two, hbN]
        show (h ((1 : 𝟙_ (Over (Sp V)) ⟶ D.P.A).left ≫ 𝟙 _) ^ (N : ℤ) *
          h ((1 : 𝟙_ (Over (Sp V)) ⟶ D.P.A).left ≫ ((toUnit D.P.A ≫ b) * 𝟙 D.P.A).left) ^ (-(N : ℤ))) ^ N * _ = _
        rw [comp_transl, Category.comp_id, _root_.mul_one, toUnit_unit, Category.id_comp]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, ← natCast_zsmul]
        module)
    have hx' : ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.P.L z J →
        val Ψ (1 : T ⟶ D.P.A).left z J ^ N * val κ (toUnit T ≫ b).left z J = gm T.hom z ⊤ x := fun T z J hJ => by
      rw [← hx T (toUnit T) z J hJ, ← Over.comp_left, MonObj.comp_one]
    obtain ⟨z₀⟩ := exists_pt (R := V) (F := FractionRing V)
    obtain ⟨J₀, hJ₀⟩ := exists_good' hL z₀
    have e := hx' _ z₀ J₀ hJ₀
    rw [v1 _ z₀ J₀ hJ₀, ← ha z₀ J₀ hJ₀, ← pow_mul, ← sq, ← hgb, hw.2 κ hκ z₀ J₀ hJ₀] at e
    have e' := (congrArg Units.val e).trans (Frames.gm_top_eq x z₀)
    rw [Units.val_one, cst_eq, ← map_one (cstH z₀), ← map_one (algebraMap V (FractionRing V))] at e'
    have e'' := IsFractionRing.injective V (FractionRing V) (cstH_inj z₀ e')
    have hx1 : x = 1 := Units.ext ((Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.injective
      (e''.symm.trans (map_one _).symm))
    rw [hx' T z J hJ, hx1, map_one]
  · have d := Frames.charVal_nsmul g χ hJ N
    rw [hgN, zero_val χ hJ, _root_.one_mul] at d
    rw [vΨ _ _ z J hJ, mul_pow (val (g.s χ) _ z J), ha z J hJ]
    beta_reduce
    rw [Over.w]
    refine congrArg₂ (· * ·) (Eq.trans (Finset.prod_congr rfl fun i _ => ?_) d) rfl
    rw [Category.comp_id, MonObj.comp_pow, ← Category.assoc, comp_toUnit, ← hgb]
    rfl

theorem exists_vals [IsLocalRing V] {θ : Th D.P} (hθ : GenAll D.P θ) (N : ℕ) (χ : D.X)
    (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D (FractionRing V) χ) (DegPre.famε 1))) {C : Type}
    (g : C → GtPtF D (FractionRing V)) (b : C → (𝟙_ (Over (Sp V)) ⟶ D.P.A)) (hgb : ∀ c, (g c).b = toUnit _ ≫ b c)
    (w : ∀ c, Frm D (FractionRing V) 1 (g c).b) (Ψ : ∀ c, LB.Gen (psiLB D.P N (b c))) (hΨ : ∀ c, (Ψ c).IsGen)
    (vΨ : ∀ c z J, Good D.P.L z J → val (Ψ c) (toUnit (TF (R := V) (FractionRing V)) ≫ D.c χ).left z J =
      (val ((g c).s χ) (𝟙 _) z J * val (w c) (𝟙 _) z J) ^ N)
    (T : C → V) (hT : ∀ c, IsCoef 1 (g c) (w c) χ s (algebraMap V (FractionRing V) (T c))) :
    ∃ (ρ : LB.Gen (LB.LinComb D.P.L (fun _ : Fin 1 => (D.c χ).left) (fun _ => -1))) (a : C → Γ(Sp V, ⊤)),
      (∀ c c', T c ^ N * (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (a c') =
        T c' ^ N * (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (a c)) ∧
      ∀ c (T : Over (Sp V)) (z : T.left) (J), Good D.P.L z J →
        gs T.hom z ⊤ (a c) = sval θ ((toUnit T ≫ b c) * (toUnit _ ≫ D.c χ)).left z J ^ N *
          (val (Ψ c) (toUnit T ≫ D.c χ).left z J * val ρ T.hom z J ^ N).val := by
  have hL := D.P.isLB
  obtain ⟨ρ, hρ⟩ := exists_gen_local (D := D) (fun _ : Fin 1 => (D.c χ).left) (fun _ => -1)
  have hv : ∀ c, ∃ a : Γ(Sp V, ⊤), ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.P.L z J →
      gs T.hom z ⊤ a = sval θ ((toUnit T ≫ b c) * (toUnit _ ≫ D.c χ)).left z J ^ N *
        (val (Ψ c) (toUnit T ≫ D.c χ).left z J * val ρ T.hom z J ^ N).val := fun c => by
    obtain ⟨u, hu, vu⟩ := ((grep_gen (Y := 𝟙_ (Over (Sp V))) (Ψ c) (hΨ c) (D.c χ).left).mul
      ((grep_gen ρ hρ (𝟙 _)).pow N)).out hL (fun _ : Fin 1 => (b c * D.c χ).left) (fun _ => -(N : ℤ)) (fun U _ h => by
        rw [Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_one]
        show h ((D.c χ).left ≫ 𝟙 _) ^ (N : ℤ) *
          h ((D.c χ).left ≫ ((toUnit D.P.A ≫ b c) * 𝟙 D.P.A).left) ^ (-(N : ℤ)) * _ = _
        rw [comp_transl, Category.comp_id, Category.id_comp, toUnit_unit, Category.id_comp]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, ← natCast_zsmul]
        module)
    obtain ⟨s', hs'⟩ := exists_powSec hL θ (b c * D.c χ).left N u hu (K' := PEmpty) PEmpty.elim PEmpty.elim
      (fun U _ f => by simp)
    obtain ⟨a, ha⟩ := exists_fn s'
    refine ⟨a, fun T z J hJ => ?_⟩
    have e := hs' _ (toUnit T).left z J hJ
    rw [ha, vu T (toUnit T) z J hJ, ← Over.comp_left, MonObj.comp_mul, Category.comp_id] at e
    exact e
  choose a ha using hv
  refine ⟨ρ, a, fun c c' => ?_, ha⟩
  let T₁ : Over (Sp V) := TF (R := V) (FractionRing V)
  let tr : T₁ ⊗ D.P.A ⟶ T₁ ⊗ D.P.A := lift (fst _ _) (snd _ _ * (toUnit _ ≫ D.c χ)⁻¹)
  obtain ⟨u, hu, vu⟩ := ((grep_gen (Y := T₁ ⊗ D.P.A) ρ hρ (toUnit (T₁ ⊗ D.P.A)).left).mul
    (grep_gen (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig D.rig_gen
      (toUnit (T₁ ⊗ D.P.A)).left)).inv.out hL ![(toUnit (T₁ ⊗ D.P.A) ≫ D.c χ).left, (1 : T₁ ⊗ D.P.A ⟶ D.P.A).left] ![1, -1]
      (fun U _ h => by
        rw [Fin.prod_univ_two, Fin.prod_univ_one, Fintype.prod_unique]
        show (h (toUnit (T₁ ⊗ D.P.A) ≫ D.c χ).left ^ (-1 : ℤ) * h (1 : T₁ ⊗ D.P.A ⟶ D.P.A).left ^ (1 : ℤ))⁻¹ = _
        exact (mul_inv _ _).trans (congrArg₂ (· * ·) (by rw [zpow_neg_one, inv_inv]; exact (zpow_one _).symm)
          (by rw [zpow_one]; exact (zpow_neg_one _).symm)))
  obtain ⟨t, ht⟩ := exists_powSec hL s tr.left 1 u hu (fun _ : Fin 1 => (snd T₁ D.P.A).left) (fun _ => 1)
    (fun U _ h => by
      have e₁ : tr.left ≫ DegPre.famφ D (FractionRing V) χ 1 = (snd T₁ D.P.A).left := by
        show (tr ≫ (snd T₁ D.P.A * (toUnit _ ≫ D.c χ))).left = _
        rw [MonObj.comp_mul, lift_snd, ← Category.assoc, comp_toUnit, inv_mul_cancel_right]
      have e₂ : tr.left ≫ DegPre.famφ D (FractionRing V) χ 2 = (toUnit (T₁ ⊗ D.P.A) ≫ D.c χ).left := by
        show (tr ≫ (toUnit _ ≫ D.c χ)).left = _
        rw [← Category.assoc, comp_toUnit]
      have e₃ : tr.left ≫ DegPre.famφ D (FractionRing V) χ 3 = (1 : T₁ ⊗ D.P.A ⟶ D.P.A).left := by
        show (tr ≫ (1 : T₁ ⊗ D.P.A ⟶ D.P.A)).left = _
        rw [MonObj.comp_one]
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_one, e₁, e₂, e₃]
      show (_ ^ (((1 : ℕ) : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ)) ^ 1 *
        (h (toUnit (T₁ ⊗ D.P.A) ≫ D.c χ).left ^ (1 : ℤ) * h (1 : T₁ ⊗ D.P.A ⟶ D.P.A).left ^ (-1 : ℤ)) = _
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
  obtain ⟨lam, hlam⟩ := hθ (FractionRing V) T₁.hom t
  obtain ⟨z⟩ := exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have key : ∀ c, cstH z (algebraMap V (FractionRing V) (T c)) ^ N = gs (𝟙 _) z ⊤ lam ^ N *
      cstH z (algebraMap V (FractionRing V) ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (a c))) := fun c => by
    have e₀ := hT c z J hJ
    have e₁ := ht _ (lift (𝟙 T₁) ((toUnit T₁ ≫ b c) * (toUnit _ ≫ D.c χ))).left z J hJ
    have e₂ := hlam _ (lift (𝟙 T₁) ((toUnit T₁ ≫ b c) * (toUnit _ ≫ D.c χ))).left z J hJ
    have e₃ : gs T₁.hom z ⊤ (a c) = cstH z (algebraMap V (FractionRing V)
        ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (a c))) := by
      rw [← cst_eq]
      exact ((congrArg (fun q => gs q z ⊤ (a c)) (Frames.toUnit_left_eq (V := V))).trans
        (GlobalTheory.RatioVal.gs_specMap _ z _)).trans (GlobalTheory.RatioVal.gs_id_const z _).symm
    have a₁ : (lift (𝟙 T₁) ((toUnit T₁ ≫ b c) * (toUnit _ ≫ D.c χ))).left ≫ tr.left = (lift (𝟙 T₁) (g c).b).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, MonObj.comp_mul, lift_snd, GrpObj.comp_inv, ← Category.assoc,
        comp_toUnit, mul_inv_cancel_right, hgb]
    have a₂ : (lift (𝟙 T₁) ((toUnit T₁ ≫ b c) * (toUnit _ ≫ D.c χ))).left ≫ (toUnit (T₁ ⊗ D.P.A)).left = T₁.hom :=
      Over.w _
    have a₃ : (lift (𝟙 T₁) ((toUnit T₁ ≫ b c) * (toUnit _ ≫ D.c χ))).left ≫ (fst T₁ D.P.A).left = 𝟙 _ := by
      rw [← Over.comp_left, lift_fst]; rfl
    have a₄ : (lift (𝟙 T₁) ((toUnit T₁ ≫ b c) * (toUnit _ ≫ D.c χ))).left ≫ (snd T₁ D.P.A).left =
        ((toUnit T₁ ≫ b c) * (toUnit _ ≫ D.c χ)).left := by rw [← Over.comp_left, lift_snd]
    rw [a₁, vu _ _ z J hJ, a₂, pow_one] at e₁
    have e₄ := e₁.symm.trans (e₂.trans (congrArg₂ (fun q q' => gs q z ⊤ lam * sval θ q' z J) a₃ a₄))
    rw [Units.mul_inv_eq_iff_eq_mul] at e₄
    rw [← e₃, ha c T₁ z J hJ, vΨ c z J hJ, ← mul_pow, Units.val_pow_eq_pow_val, ← mul_pow, ← mul_pow, ← cst_eq]
    congr 1
    rw [pow_one, e₄] at e₀
    refine (Units.mul_left_inj (rigV D T₁.hom z J)).1 (e₀.trans ?_)
    simp only [Units.val_mul, rigV]
    ring
  refine IsFractionRing.injective V (FractionRing V) (cstH_inj z ?_)
  simp only [map_mul, map_pow]
  rw [key, key]
  ring

end Integral

section Transport

variable {S S' : Scheme.{0}} {A : Over S} {B : Over S'} {L : LB A.left}

theorem grep_zpow {X : Scheme.{0}} {L : LB X} {P v} (h : GRep L B P v) (n : ℤ) :
    GRep L B (fun U _ h => P U h ^ n) (fun T r z J => v T r z J ^ n) := by
  cases n with
  | ofNat n => exact (h.pow n).congr (fun _ _ _ => (zpow_natCast _ _).symm) (fun _ _ _ _ _ => (zpow_natCast _ _).symm)
  | negSucc n =>
    exact (h.pow (n + 1)).inv.congr (fun _ _ _ => (zpow_negSucc _ _).symm) (fun _ _ _ _ _ => (zpow_negSucc _ _).symm)

theorem transport_gen (hL : L.IsLB) (e : S' ⟶ B.left) (he : e ≫ B.hom = 𝟙 S')
    (hB : Function.Surjective B.hom.appTop.hom) {p p' : B.left ⟶ A.left}
    (ω : LB.Gen (LB.LinComb L ![p', p] ![1, -1])) (hω : ω.IsGen) {K : Type} [Fintype K] {φ : K → (A.left ⟶ A.left)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (ψ : K → (B ⟶ B))
    (h₁ : ∀ k, p ≫ φ k = (ψ k).left ≫ p) (h₂ : ∀ k, p' ≫ φ k = (ψ k).left ≫ p') :
    ∃ a : Γ(S', ⊤)ˣ, ∀ (T : Over S') (r : T ⟶ B) (z : T.left) (J), Good L z J →
      val t (r.left ≫ p') z J = gm T.hom z ⊤ a * val t (r.left ≫ p) z J * ∏ k, val ω (r ≫ ψ k).left z J ^ ε k := by
  classical
  have G : ∀ s : Finset K, GRep L B
      (fun _ _ h => ∏ k ∈ s, (h ((ψ k).left ≫ p') * (h ((ψ k).left ≫ p))⁻¹) ^ ε k)
      (fun _ r z J => ∏ k ∈ s, val ω (r ≫ ψ k).left z J ^ ε k) := fun s => by
    induction s using Finset.induction_on with
    | empty => exact (grep_unit B 1).congr (fun _ _ _ => by simp) (fun _ _ _ _ _ => by simp)
    | insert k s hk ih =>
      exact ((grep_zpow (grep_gen ω hω (ψ k).left) (ε k)).mul ih).congr
        (fun _ _ _ => by rw [Finset.prod_insert hk, Fin.prod_univ_two]; simp)
        (fun _ _ _ _ _ => by rw [Finset.prod_insert hk]; rfl)
  obtain ⟨a, ha⟩ := grep_const hL e he hB
    (((grep_gen t ht p').mul (grep_gen t ht p).inv).mul (G Finset.univ).inv) (fun U _ h => by
      simp only [h₁, h₂, mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv_cancel])
  refine ⟨a, fun T r z J hJ => ?_⟩
  rw [← ha T r z J hJ, mul_right_comm, inv_mul_cancel_right, inv_mul_cancel_right]

variable [GrpObj A] [GrpObj B] {s : S' ⟶ S} {p : B.left ⟶ A.left}

def ptHom (h : IsGrpPullback B A s p) (T : Over S') : (T ⟶ B) →* (Over.mk (T.hom ≫ s) ⟶ A) :=
  MonoidHom.mk' (fun x => toBase h.1.w x) fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem pb_pow (h : IsGrpPullback B A s p) (n : ℕ) : p ≫ (𝟙 A ^ n).left = (𝟙 B ^ n).left ≫ p := by
  have e := congrArg (fun q => q.left) (map_pow (ptHom h B) (𝟙 B) n)
  refine Eq.trans ?_ e.symm
  have e' : ptHom h B (𝟙 B) ≫ 𝟙 A ^ n = ptHom h B (𝟙 B) ^ n := by rw [MonObj.comp_pow, Category.comp_id]
  rw [← e', Over.comp_left]
  exact congrArg (· ≫ (𝟙 A ^ n).left) (Category.id_comp p).symm

theorem pb_one (h : IsGrpPullback B A s p) : p ≫ (1 : A ⟶ A).left = (1 : B ⟶ B).left ≫ p := by
  simpa only [pow_zero] using pb_pow h 0

theorem pb_transl (h : IsGrpPullback B A s p) {b : 𝟙_ (Over S) ⟶ A} {β : 𝟙_ (Over S') ⟶ B}
    (hβ : β.left ≫ p = s ≫ b.left) :
    p ≫ ((toUnit A ≫ b) * 𝟙 A).left = ((toUnit B ≫ β) * 𝟙 B).left ≫ p := by
  have e := congrArg (fun q => q.left) (map_mul (ptHom h B) (toUnit B ≫ β) (𝟙 B))
  refine Eq.trans ?_ e.symm
  have e' : ptHom h B (𝟙 B) ≫ ((toUnit A ≫ b) * 𝟙 A) = ptHom h B (toUnit B ≫ β) * ptHom h B (𝟙 B) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
    refine congrArg (· * _) (Over.OverMorphism.ext ?_)
    show (B.hom ≫ s) ≫ b.left = (B.hom ≫ β.left) ≫ p
    rw [Category.assoc, Category.assoc, hβ]
  rw [← e', Over.comp_left]
  exact congrArg (· ≫ ((toUnit A ≫ b) * 𝟙 A).left) (Category.id_comp p).symm

end Transport

section Fibre

open GlobalTheory.VVRank

variable {V : Type} [CommRing V] [IsDomain V] {D : DegPre V} {K : Type} [Field K] {B : Over (Sp K)} [GrpObj B]

theorem fibre_vals {N : ℕ} {b : 𝟙_ (Over (Sp V)) ⟶ D.P.A} (hb : b ^ N = 1) (Ψ : LB.Gen (psiLB D.P N b))
    {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)} (hκ : Normd κ)
    {κ' : LB.Gen (kapLB D (𝟙 D.P.A ^ (N + 1)) ((N + 1) ^ 2) 1)} (hκ' : Normd κ') (ξ : Γ(Sp V, ⊤)ˣ)
    (h₁ : ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.P.L z J →
      val Ψ (1 : T ⟶ D.P.A).left z J ^ N * val κ (toUnit T ≫ b).left z J = 1)
    (h₂ : ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.P.L z J →
      val Ψ (1 : T ⟶ D.P.A).left z J ^ (N + 2) * val κ' (toUnit T ≫ b).left z J = gm T.hom z ⊤ ξ)
    (ev : V →+* K) {p : B.left ⟶ D.P.A.left} (hp : IsGrpPullback B D.P.A (spMap ev) p)
    {β : 𝟙_ (Over (Sp K)) ⟶ B} (hβ : β.left ≫ p = spMap ev ≫ b.left)
    (z : (𝟙_ (Over (Sp K))).left) (J) (hJ : Good D.P.L z J) :
    val Ψ ((1 : 𝟙_ (Over (Sp K)) ⟶ B).left ≫ p) z J ^ N * val κ (β.left ≫ p) z J = 1 ∧
    (val Ψ ((1 : 𝟙_ (Over (Sp K)) ⟶ B).left ≫ p) z J ^ (N + 2) * val κ' (β.left ≫ p) z J).val =
      GlobalTheory.RatioVal.germConst K z (ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom ξ.val)) ∧
    ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom ξ.val) ^ (N ^ 2) = 1 ∧
    val κ ((1 : 𝟙_ (Over (Sp K)) ⟶ B).left ≫ p) z J = 1 ∧ val κ' ((1 : 𝟙_ (Over (Sp K)) ⟶ B).left ≫ p) z J = 1 := by
  let T : Over (Sp V) := Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap ev)
  have e₁ : (1 : T ⟶ D.P.A).left = (1 : 𝟙_ (Over (Sp K)) ⟶ B).left ≫ p :=
    (congrArg (fun q => q.left) (map_one (ptHom hp (𝟙_ _)))).symm
  have e₂ : (toUnit T ≫ b).left = β.left ≫ p := by
    rw [hβ]
    exact congrArg (· ≫ b.left) (Category.id_comp (spMap ev))
  have e₃ : (gm T.hom z ⊤ ξ).val =
      GlobalTheory.RatioVal.germConst K z (ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom ξ.val)) :=
    ((gs_unit _ z ⊤ trivial _).symm.trans (congrArg (fun q => gs q z ⊤ ξ.val) (Category.id_comp (spMap ev)))).trans
      (GlobalTheory.RatioVal.gs_specMap ev z _)
  have a₁ := h₁ T z J hJ
  have a₂ := h₂ T z J hJ
  have a₃ := kap_rel hκ hκ' (toUnit T ≫ b) (by rw [← MonObj.comp_pow, hb, MonObj.comp_one]) z J hJ
  have a₄ : gm T.hom z ⊤ ξ ^ (N ^ 2) = 1 := by
    rw [← a₂, mul_pow, a₃, ← pow_mul, show (N + 2) * N ^ 2 = N * (N * (N + 2)) by ring, pow_mul, ← mul_pow, a₁, one_pow]
  have a₅ := normd_one hκ (T := T) hJ
  have a₆ := normd_one hκ' (T := T) hJ
  rw [e₁] at a₅ a₆
  rw [e₁, e₂] at a₁ a₂
  refine ⟨a₁, (congrArg Units.val a₂).trans e₃, (GlobalTheory.RatioVal.germConst K z).injective ?_, a₅, a₆⟩
  rw [map_pow, map_one, ← e₃]
  exact (Units.val_pow_eq_pow_val _ _).symm.trans (congrArg Units.val a₄)

theorem psi_transport [IsNoetherianRing V] (hB : Function.Surjective B.hom.appTop.hom) {N : ℕ} (hN : Odd N)
    {b : 𝟙_ (Over (Sp V)) ⟶ D.P.A} (hb : b ^ N = 1) (Ψ : LB.Gen (psiLB D.P N b)) (hΨ : Ψ.IsGen)
    (nΨ : ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ (T : Over (Sp V)) (z : T.left) (J),
      Good D.P.L z J → val Ψ (1 : T ⟶ D.P.A).left z J ^ N * val κ (toUnit T ≫ b).left z J = 1)
    (ev ev' : V →+* K) (hev : ∀ x, ev x ^ (N ^ 2) = 1 → ev' x = ev x) {p p' : B.left ⟶ D.P.A.left}
    (hp : IsGrpPullback B D.P.A (spMap ev) p) (hp' : IsGrpPullback B D.P.A (spMap ev') p')
    (ω : LB.Gen (LB.LinComb D.P.L ![p', p] ![1, -1])) (hω : ω.IsGen)
    {β : 𝟙_ (Over (Sp K)) ⟶ B} (hβ : β.left ≫ p = spMap ev ≫ b.left) (hβ' : β.left ≫ p' = spMap ev' ≫ b.left)
    (y : 𝟙_ (Over (Sp K)) ⟶ B) (z : (𝟙_ (Over (Sp K))).left) (J) (hJ : Good D.P.L z J) :
    val Ψ (y.left ≫ p') z J = val Ψ (y.left ≫ p) z J * val ω y.left z J ^ N * (val ω (β * y).left z J ^ N)⁻¹ := by
  have hL := D.P.isLB
  have hM := GlobalTheory.abelianSchemeLaws_all.1.mulPull
  obtain ⟨κ, hκ⟩ := exists_kap (D := D) hM N
  obtain ⟨κ', hκ'⟩ := exists_kap (D := D) hM (N + 1)
  obtain ⟨ξ, hξ⟩ := grep_const hL (B := 𝟙_ (Over (Sp V))) (𝟙 _) (Category.id_comp _) (fun a => ⟨a, rfl⟩)
    (((grep_gen Ψ hΨ (1 : 𝟙_ (Over (Sp V)) ⟶ D.P.A).left).pow (N + 2)).mul (grep_kap κ' hκ'.1 b)) (fun U _ h => by
      rw [Fin.prod_univ_two, pow_succ b, hb, _root_.one_mul b]
      show (h ((1 : 𝟙_ (Over (Sp V)) ⟶ D.P.A).left ≫ 𝟙 _) ^ (N : ℤ) *
        h ((1 : 𝟙_ (Over (Sp V)) ⟶ D.P.A).left ≫ ((toUnit D.P.A ≫ b) * 𝟙 D.P.A).left) ^ (-(N : ℤ))) ^ (N + 2) * _ = _
      rw [comp_transl, Category.comp_id, _root_.mul_one, toUnit_unit, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, ← natCast_zsmul]
      push_cast
      module)
  have hξ' : ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.P.L z J →
      val Ψ (1 : T ⟶ D.P.A).left z J ^ (N + 2) * val κ' (toUnit T ≫ b).left z J = gm T.hom z ⊤ ξ := fun T z J hJ => by
    rw [← hξ T (toUnit T) z J hJ, ← Over.comp_left, MonObj.comp_one]
  obtain ⟨a₁, a₂, a₃, a₄, a₅⟩ := fibre_vals hb Ψ hκ hκ' ξ (nΨ κ hκ) hξ' ev hp hβ z J hJ
  obtain ⟨b₁, b₂, -, b₄, b₅⟩ := fibre_vals hb Ψ hκ hκ' ξ (nΨ κ hκ) hξ' ev' hp' hβ' z J hJ
  have c₂ := Units.ext (b₂.trans ((congrArg _ (hev _ a₃)).trans a₂.symm))
  have hβN : β ^ N = 1 := by
    apply Over.OverMorphism.ext
    refine hp.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)
    have e : ptHom hp _ β = toUnit _ ≫ b := Over.OverMorphism.ext
      (hβ.trans (congrArg (· ≫ b.left) (Category.id_comp (spMap ev)).symm))
    have e' : ptHom hp _ (β ^ N) = ptHom hp _ 1 := by
      rw [map_pow, map_one, e, ← MonObj.comp_pow, hb, MonObj.comp_one]
    exact congrArg (fun q => q.left) e'
  have he : (η[B]).left ≫ B.hom = 𝟙 _ := Over.w η[B]
  have tk : ∀ (m : ℕ) (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ m) (m ^ 2) 1)), κ.IsGen →
      val κ ((1 : 𝟙_ (Over (Sp K)) ⟶ B).left ≫ p) z J = 1 → val κ ((1 : 𝟙_ (Over (Sp K)) ⟶ B).left ≫ p') z J = 1 →
      val κ (β.left ≫ p') z J = val κ (β.left ≫ p) z J * (val ω β.left z J ^ ((m : ℤ) ^ 2) *
        (val ω (β ^ m).left z J)⁻¹ * val ω (1 : 𝟙_ (Over (Sp K)) ⟶ B).left z J ^ (1 - (m : ℤ) ^ 2)) := fun m κ hκ k₁ k₂ => by
    obtain ⟨a, ha⟩ := transport_gen hL _ he hB ω hω κ hκ ![𝟙 B, 𝟙 B ^ m, 1]
      (fun k => by
        fin_cases k
        exacts [(Category.comp_id _).trans (Category.id_comp _).symm, pb_pow hp m, pb_one hp])
      (fun k => by
        fin_cases k
        exacts [(Category.comp_id _).trans (Category.id_comp _).symm, pb_pow hp' m, pb_one hp'])
    have v : ∀ r : 𝟙_ (Over (Sp K)) ⟶ B, val κ (r.left ≫ p') z J = gm (𝟙_ (Over (Sp K))).hom z ⊤ a *
        val κ (r.left ≫ p) z J * (val ω r.left z J ^ ((m : ℤ) ^ 2) * (val ω (r ^ m).left z J)⁻¹ *
          val ω (1 : 𝟙_ (Over (Sp K)) ⟶ B).left z J ^ (1 - (m : ℤ) ^ 2)) := fun r => by
      rw [ha _ r z J hJ, Fin.prod_univ_three]
      show _ * (val ω (r ≫ 𝟙 B).left z J ^ ((m ^ 2 : ℕ) : ℤ) * val ω (r ≫ 𝟙 B ^ m).left z J ^ (-((1 : ℕ) : ℤ)) *
        val ω (r ≫ (1 : B ⟶ B)).left z J ^ (((1 : ℕ) : ℤ) - ((m ^ 2 : ℕ) : ℤ))) = _
      rw [MonObj.comp_pow, MonObj.comp_one, Category.comp_id]
      refine congrArg₂ (· * ·) rfl ?_
      rw [Nat.cast_pow, Nat.cast_one, zpow_neg_one]
    have v₁ := v 1
    rw [k₁, k₂, one_pow, mul_right_comm (_ ^ _), ← zpow_add, add_sub_cancel, zpow_one, mul_inv_cancel, _root_.mul_one,
      _root_.mul_one] at v₁
    rw [v β, ← v₁, _root_.one_mul]
  have t₁ := tk N κ hκ.1 a₄ b₄
  have t₂ := tk (N + 1) κ' hκ'.1 a₅ b₅
  rw [hβN] at t₁
  rw [pow_succ β, hβN, _root_.one_mul β] at t₂
  obtain ⟨a, ha⟩ := transport_gen hL _ he hB ω hω Ψ hΨ ![𝟙 B, (toUnit B ≫ β) * 𝟙 B]
    (fun k => by
      fin_cases k
      exacts [(Category.comp_id _).trans (Category.id_comp _).symm, pb_transl hp hβ])
    (fun k => by
      fin_cases k
      exacts [(Category.comp_id _).trans (Category.id_comp _).symm, pb_transl hp' hβ'])
  have v : ∀ r : 𝟙_ (Over (Sp K)) ⟶ B, val Ψ (r.left ≫ p') z J = gm (𝟙_ (Over (Sp K))).hom z ⊤ a *
      (val Ψ (r.left ≫ p) z J * val ω r.left z J ^ N * (val ω (β * r).left z J ^ N)⁻¹) := fun r => by
    rw [ha _ r z J hJ, Fin.prod_univ_two]
    show _ * (val ω (r ≫ 𝟙 B).left z J ^ (N : ℤ) * val ω (r ≫ ((toUnit B ≫ β) * 𝟙 B)).left z J ^ (-(N : ℤ))) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp, zpow_neg,
      zpow_natCast, zpow_natCast]
    simp only [_root_.mul_assoc]
  have v₁ := v 1
  rw [_root_.mul_one β] at v₁
  have alg : ∀ {U : Type} [CommGroup U] (g P P' k k' l l' o w : U), P ^ N * k = 1 → P' ^ N * k' = 1 →
      P' ^ (N + 2) * l' = P ^ (N + 2) * l → k' = k * (w ^ ((N : ℤ) ^ 2) * o⁻¹ * o ^ (1 - (N : ℤ) ^ 2)) →
      l' = l * (w ^ (((N + 1 : ℕ) : ℤ) ^ 2) * w⁻¹ * o ^ (1 - ((N + 1 : ℕ) : ℤ) ^ 2)) →
      P' = g * (P * o ^ N * (w ^ N)⁻¹) → g = 1 := by
    intro U _ g P P' k k' l l' o w h₁ h₂ h₃ h₄ h₅ h₆
    subst h₄ h₅ h₆
    obtain ⟨n, rfl⟩ := hN
    have a₁ := congrArg Additive.ofMul h₁
    have a₂ := congrArg Additive.ofMul h₂
    have a₃ := congrArg Additive.ofMul h₃
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow, ofMul_one, ← natCast_zsmul] at a₁ a₂ a₃ ⊢
    push_cast at a₁ a₂ a₃
    linear_combination (norm := module) ((n : ℤ) + 1) • (a₂ - a₁) - (n : ℤ) • a₃
  rw [v y, alg _ _ _ _ _ _ _ _ _ a₁ b₁ c₂ t₁ t₂ v₁, _root_.one_mul]

theorem theta_transport {θ : Th D.P} (hθ : GenAll D.P θ) {s' : Sp K ⟶ Sp V} {p p' : B.left ⟶ D.P.A.left}
    (hp' : IsPullback p' B.hom D.P.A.hom s') (ω : LB.Gen (LB.LinComb D.P.L ![p', p] ![1, -1])) (hω : ω.IsGen) :
    ∃ c : Γ(Sp K, ⊤), ∀ (y : 𝟙_ (Over (Sp K)) ⟶ B) (z : (𝟙_ (Over (Sp K))).left) (J), Good D.P.L z J →
      sval θ (y.left ≫ p) z J * (val ω y.left z J).val =
        gs (𝟙_ (Over (Sp K))).hom z ⊤ c * sval θ (y.left ≫ p') z J := by
  have hL := D.P.isLB
  let i : (Over.mk s' ⊗ D.P.A).left ⟶ B.left := hp'.lift (snd (Over.mk s') D.P.A).left (fst (Over.mk s') D.P.A).left
    ((Over.w (snd (Over.mk s') D.P.A)).trans (Over.w (fst (Over.mk s') D.P.A)).symm)
  obtain ⟨t, ht⟩ := exists_powSec hL θ (i ≫ p) 1 (LB.pullGen D.P.L _ _ ω i) (pullGen_isGen _ _ _ _ hω _)
    (fun _ : Fin 1 => (snd (Over.mk s') D.P.A).left) (fun _ => 1) (fun U _ h => by
      rw [Fin.prod_univ_one, Fin.prod_univ_one, Fin.prod_univ_two]
      show (h ((i ≫ p) ≫ 𝟙 _) ^ (1 : ℤ)) ^ 1 * (h (i ≫ p') ^ (1 : ℤ) * h (i ≫ p) ^ (-1 : ℤ)) = _
      rw [hp'.lift_fst, Category.comp_id, pow_one, zpow_one, zpow_neg_one, mul_comm (h _ ^ (1 : ℤ)),
        mul_inv_cancel_left])
  obtain ⟨c, hc⟩ := hθ K s' t
  refine ⟨c, fun y z J hJ => ?_⟩
  let x : Over.mk s' ⟶ D.P.A := Over.homMk (y.left ≫ p') (by
    rw [Category.assoc, hp'.w, ← Category.assoc, Over.w y]; exact Category.id_comp _)
  let r : (𝟙_ (Over (Sp K))).left ⟶ (Over.mk s' ⊗ D.P.A).left := (lift (𝟙 (Over.mk s')) x).left
  have e₁ : r ≫ (fst (Over.mk s') D.P.A).left = (𝟙_ (Over (Sp K))).hom :=
    congrArg (fun q => q.left) (lift_fst (𝟙 (Over.mk s')) x)
  have e₂ : r ≫ (snd (Over.mk s') D.P.A).left = y.left ≫ p' := congrArg (fun q => q.left) (lift_snd (𝟙 (Over.mk s')) x)
  have e₃ : r ≫ i = y.left := hp'.hom_ext (by rw [Category.assoc, hp'.lift_fst, e₂])
    (by rw [Category.assoc, hp'.lift_snd, Over.w y]; exact e₁)
  have q := ht _ r z J hJ
  rw [val_pull hJ, ← Category.assoc, e₃, pow_one] at q
  exact q.symm.trans ((hc _ r z J hJ).trans (congrArg₂ (fun q q' => gs q z ⊤ c * sval θ q' z J) e₁ e₂))

end Fibre

section Main

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]

theorem conj_point [IsNoetherianRing V] [IsIntegrallyClosed V] (D : DegPre V) {N : ℕ} (hN : Odd N) (h4 : 4 ≤ N)
    {X C : Type} [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V) (mo : X → V) (mu : X) (hmo : mo mu ≠ 0) (c₀ : C)
    (hu : IsUnit (u mu c₀)) (hT : IsThetaTerms D N e (fun mu c => u mu c * mo mu))
    {K : Type} [Field K] [IsAlgClosed K] (hK : (N : K) ≠ 0) (ev : V →+* K) (σ : K →+* K)
    (hσ : ∀ x : K, x ^ (N ^ 2) = 1 → σ x = x) (hr : ∀ c, ∃ r, σ r = r ∧ ev (u mu c) = r * ev (u mu c₀))
    {B : Over (Sp K)} [GrpObj B] (hB : Function.Surjective B.hom.appTop.hom) {p p' : B.left ⟶ D.P.A.left}
    (hp : IsGrpPullback B D.P.A (spMap ev) p) (hp' : IsGrpPullback B D.P.A (spMap (σ.comp ev)) p')
    (hiso : LBIso (D.P.L.pull p) (D.P.L.pull p'))
    (htor : ∀ y : Over.mk (spMap ev) ⟶ D.P.A, y ^ N = 1 → ∀ q : Sp K ⟶ B.left, q ≫ p = y.left → q ≫ B.hom = 𝟙 _ →
      q ≫ p' = spMap σ ≫ y.left)
    (q : Sp K ⟶ B.left) (hq : q ≫ p = spMap ev ≫ (D.c (e mu)).left) (hq' : q ≫ B.hom = 𝟙 _) :
    q ≫ p' = spMap σ ≫ q ≫ p := by
  have hL := D.P.isLB
  have hs : spMap σ ≫ spMap ev = spMap (σ.comp ev) := (Spec.map_comp _ _).symm
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅, -⟩ := hT
  have hb : ∀ c, b c ^ N = 1 := fun c => (Frames.torsion_of_nsmul (g c) (b c) (h₁ c) (h₂ c)).2
  obtain ⟨θ, hθ⟩ := exists_genAll D.P
  obtain ⟨ω, hω⟩ := exists_gen_of_lbIso hiso
  choose Ψ hΨ nΨ vΨ using fun c => exists_psi (by omega) (g c) (b c) (h₁ c) (h₂ c) (w c) (h₄ c)
  obtain ⟨ρ, a, cross, ha⟩ := exists_vals hθ N (e mu) (th.s (e mu)) g b h₁ w Ψ hΨ (fun c => vΨ c (e mu)) _ (h₅ mu)
  obtain ⟨k, hk⟩ := theta_transport hθ hp'.1 ω hω
  obtain ⟨lam, hlam⟩ : ∃ lam : K, ∀ c, σ (ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (a c))) =
      lam * ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (a c)) := by
    set v : C → K := fun c => ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (a c))
    have hv : ∀ c, ∃ r, σ r = r ∧ v c = r ^ N * v c₀ := fun c => by
      obtain ⟨r, r₁, r₂⟩ := hr c
      have x := cross c c₀
      rw [mul_pow, mul_pow, mul_right_comm, mul_right_comm (u mu c₀ ^ N)] at x
      have x' := congrArg ev (mul_right_cancel₀ (pow_ne_zero N hmo) x)
      rw [map_mul, map_mul, map_pow, map_pow, r₂] at x'
      refine ⟨r, r₁, mul_left_cancel₀ (pow_ne_zero N (hu.map ev).ne_zero) (x'.symm.trans ?_)⟩
      simp only [v]
      ring
    refine ⟨σ (v c₀) / v c₀, fun c => ?_⟩
    obtain ⟨r, r₁, r₂⟩ := hv c
    show σ (v c) = _ * v c
    rw [r₂, map_mul, map_pow, r₁]
    by_cases h0 : v c₀ = 0
    · simp [h0]
    · field_simp
  let U : Over (Sp K) := 𝟙_ (Over (Sp K))
  let y : U ⟶ B := Over.homMk q hq'
  have hβ : ∀ c, ∃ β : U ⟶ B, β.left ≫ p = spMap ev ≫ (b c).left ∧ β.left ≫ p' = spMap (σ.comp ev) ≫ (b c).left :=
    fun c => by
      have w₀ : (spMap ev ≫ (b c).left) ≫ D.P.A.hom = 𝟙 _ ≫ spMap ev := by
        rw [Category.assoc, Over.w, Category.id_comp]; exact Category.comp_id _
      refine ⟨Over.homMk (hp.1.lift _ _ w₀) (hp.1.lift_snd _ _ _), hp.1.lift_fst _ _ _, ?_⟩
      refine (htor (toUnit _ ≫ b c) (by rw [← MonObj.comp_pow, hb, MonObj.comp_one]) _ (hp.1.lift_fst _ _ w₀)
        (hp.1.lift_snd _ _ _)).trans ?_
      rw [← hs, Category.assoc]
      rfl
  choose β hβ hβ' using hβ
  let Y : Over.mk (spMap (σ.comp ev)) ⟶ D.P.A := Over.homMk (q ≫ p') (by
    rw [Category.assoc, hp'.1.w, ← Category.assoc, hq']; exact Category.id_comp _)
  obtain ⟨z⟩ : Nonempty U.left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨J, hJ⟩ := GlobalTheory.UT.CoefBasic.exists_good' hL z
  have tr : ∀ {s : Sp K ⟶ Sp V} {π : B.left ⟶ D.P.A.left}, IsGrpPullback B D.P.A s π → ∀ c,
      (β c).left ≫ π = s ≫ (b c).left → ∀ x : Over.mk s ⟶ D.P.A, x.left = y.left ≫ π →
      ((toUnit _ ≫ b c) * x).left = (β c * y).left ≫ π := fun {s π} hπ c hc x hx => by
    rw [← comp_transl, hx, Category.assoc, pb_transl hπ hc, ← Category.assoc, ← Over.comp_left, MonObj.comp_mul,
      Category.comp_id, ← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  have alg : ∀ {R : Type} [CommRing R] (E E' l k t t' t'' : R) (P P' P'' r r' o o' : Rˣ), E' = l * E →
      E = t ^ N * (P * r ^ N).val → E' = t'' ^ N * (P'' * r' ^ N).val → t * o'.val = k * t' →
      P' = P * o ^ N * (o' ^ N)⁻¹ →
      t'' ^ N * P''.val = (l * k ^ N * (r ^ N * (r' ^ N)⁻¹ * (o ^ N)⁻¹).val) * (t' ^ N * P'.val) := by
    intro R _ E E' l k t t' t'' P P' P'' r r' o o' a₁ a₂ a₃ a₄ a₅
    have a₆ : t = k * t' * (o'⁻¹).val := by rw [← a₄, Units.mul_inv_cancel_right]
    have a₇ : t'' ^ N * P''.val = E' * ((r' ^ N)⁻¹).val := by
      rw [a₃, Units.val_mul, ← _root_.mul_assoc, Units.mul_inv_cancel_right]
    have a₈ : (o ^ N).val * ((o ^ N)⁻¹).val = 1 := Units.mul_inv _
    rw [a₇, a₁, a₂, a₅, a₆, ← inv_pow o', mul_pow, mul_pow]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val o'⁻¹]
    linear_combination (-(l * k ^ N * t' ^ N * (o'⁻¹).val ^ N * P.val * (r ^ N).val * ((r' ^ N)⁻¹).val)) * a₈
  have main : Y = toUnit _ ≫ D.c (e mu) := by
    refine eq_of_translates D.P hθ (spMap (σ.comp ev)) h4 hK b (h₃ K _) Ψ hΨ Y _ z J hJ
      (@id (U.left.presheaf.stalk z) (GlobalTheory.RatioVal.germConst K z lam) * gs U.hom z ⊤ k ^ N * (val (Z := U.left) ρ (spMap ev) z J ^ N *
        (val (Z := U.left) ρ (spMap (σ.comp ev)) z J ^ N)⁻¹ * (val ω y.left z J ^ N)⁻¹).val) fun c => ?_
    have e₁ := (GlobalTheory.RatioVal.gs_specMap ev z _).symm.trans (ha c (Over.mk (spMap ev)) z J hJ)
    have e₂ := (GlobalTheory.RatioVal.gs_specMap (σ.comp ev) z _).symm.trans (ha c (Over.mk (spMap (σ.comp ev))) z J hJ)
    rw [tr hp c (hβ c) _ hq.symm, show (toUnit (Over.mk (spMap ev)) ≫ D.c (e mu)).left = y.left ≫ p from hq.symm] at e₁
    rw [tr hp' c (hβ' c) Y rfl]
    exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ ((congrArg _ (hlam c)).trans (map_mul _ _ _)) e₁ e₂ (hk (β c * y) z J hJ)
      (psi_transport hB hN (hb c) (Ψ c) (hΨ c) (nΨ c) ev (σ.comp ev) (fun x hx => hσ _ hx) hp hp' ω hω (hβ c) (hβ' c)
        y z J hJ)
  rw [hq, ← Category.assoc, hs]
  exact congrArg (fun x => x.left) main

end Main

end GlobalTheory.Poinc.Sep.ConjPt

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep

theorem GlobalTheory.Poinc.Sep.conj_sharp_points : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) → (∀ mu (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left), q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu)).left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst D.P.A.hom (spMap ev)) := by
  intro g l hl hodd W _
  refine ⟨1, fun j hj V V₁ _ _ _ _ _ hV hlu Q _ ρ _ D e _ C u mo hu hT K _ _ ev k₀ hk₀ hr σ hσ f hf hiso htor mu q hq hq' => ?_⟩
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  have h2 : 2 ≤ l ^ j := hl.two_le.trans (Nat.le_self_pow (by omega) l)
  have h4 : 4 ≤ (l ^ j) ^ 2 := by nlinarith
  obtain ⟨hmo, c₀, hc₀⟩ := hu mu
  have hA := D.P.isAb
  have hB : IsAbelianScheme ((Over.pullback (spMap ev)).obj D.P.A) :=
    { comm := by have := hA.comm; infer_instance
      smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hp' := hf.comp (isGrpPullback_pullback D.P.A (spMap (σ.toRingHom.comp ev)))
  rw [Category.id_comp] at hp'
  refine ConjPt.conj_point D hodd.pow.pow h4 e u mo mu hmo c₀ hc₀ hT ?_ ev σ.toRingHom (fun x hx => hσ x ?_)
    (fun c => ?_) (GlobalTheory.abelianSchemeLaws_all.1.globalFns _ _ hB).2 (isGrpPullback_pullback D.P.A (spMap ev)) hp' hiso
    htor q hq hq'
  · have : (l : K) ≠ 0 := by simpa using (hlu.map ev).ne_zero
    simpa using fun h => absurd h this
  · exact Frames.mem_of_pow_mem k₀ (Nat.one_le_pow _ _ (by omega)) (hx ▸ k₀.one_mem)
  · obtain ⟨r, r₁, r₂⟩ := hr mu c c₀ hc₀
    exact ⟨r, hσ r r₁, r₂⟩
