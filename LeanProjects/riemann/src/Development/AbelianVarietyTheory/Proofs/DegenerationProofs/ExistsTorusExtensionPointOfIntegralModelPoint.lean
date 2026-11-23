import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitLevels
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMaximalComapMaximalIdealOO
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadicStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.IntegralGt

section Glue

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) {S : Type} [CommRing S] {φ : R →+* S} [IsLocalRing S]

open FormalPoint RedTotal in

theorem exists_gtPt [IsAdicComplete (I.map φ) S] (x : Over.mk (spMap φ) ⟶ G) :
    ∃ g : GtPt D.toPre (Over.mk (spMap φ)), ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp S)
      (y : Z ⟶ (thickObj R I e G).left), y ≫ (fstG I e G).left = r ≫ x.left →
      y ≫ (U.gt e).pG.left = r ≫ g.b.left ∧ ∀ χ z C, Good D.toPre.P.L z C →
        val ((U.gt e).t χ) y z C = val (g.s χ) r z C := by
  have hL := D.toPre.P.isLB
  have hf : IsAdicFamily (I.map φ) fun e => reduction I x e ≫ (U.gt e).pG.left := fun e => by
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [reduction_succ, Category.assoc, U.gt_q]
  obtain ⟨b₀, ⟨hb₁, hb₂⟩, -⟩ := existsUnique_over_of_isAdicFamily (spMap φ) D.toPre.P.A.hom hf fun e => by
    have h₁ : (U.gt e).pG.left ≫ D.toPre.P.A.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (U.gt e).pG
    rw [Category.assoc, h₁, ← Category.assoc, reduction_hom, levelMap_thick]
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (spMap φ)
  let b : T ⟶ D.toPre.P.A := Over.homMk b₀ hb₁
  have hb : ∀ e, adicLevelι (I.map φ) (e + 1) ≫ b.left = reduction I x e ≫ (U.gt e).pG.left := hb₂
  choose s hs vs using fun χ => exists_gen_levels (I.map φ) hL (DegPre.gtφT D.toPre T b χ) DegPre.gtε
    (fun e => (U.gt e).t χ) (fun e => (U.gt e).t_gen χ) (reduction I x)
    (fun e => TorusCoord.formEq_of_left b (U.gt e).pG _ _ (hb e) χ) fun e z C hC => by
      rw [reduction_succ]
      exact (val_pull hC _ _ _).symm.trans (val_corr hC (U.gt_t e χ) _)
  have hm : ∀ χ χ' : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _
      (LB.mulGen D.toPre.P.L _ _ _ _ (s (χ + χ'))
        (DegPre.cubAtT D.toPre T (DegPre.cT D.toPre T χ) (DegPre.cT D.toPre T χ') b))
      (LB.mulGen D.toPre.P.L _ _ _ _ (s χ) (s χ')) := fun χ χ' => by
    refine corr_of_levels (I.map φ) hL (formEq_mult b χ χ')
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hs _) (DVR.pullGen_isGen _ _ _ _ D.toPre.cub.isGen _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hs _) (hs _)) fun e z C hC => ?_
    have v : ∀ α, val ((U.gt e).t α) (reduction I x e) z C = val (s α) (adicLevelι (I.map φ) (e + 1)) z C :=
      fun α => by simpa only [Category.id_comp] using vs α e _ (𝟙 _) z C hC
    have m := TorusCoord.val_t_mul (U.gt e) (reduction I x e) χ χ' z C hC
    rw [v, v, v, ← (TorusCoord.comp_eq_of_left b (U.gt e).pG _ _ (hb e)).2 χ χ'] at m
    exact (val_mul hC _ _ _).trans ((congrArg₂ (· * ·) rfl (val_pull hC _ _ _)).trans
      (m.trans (val_mul hC _ _ _).symm))
  refine ⟨⟨b, s, hs, corr_of_val hL fun y C hC => ?_, hm⟩, fun e Z r y hy => ?_⟩
  · have h := ((val_mul hC _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hC _ _ _))).symm.trans
      ((val_corr hC (hm 0 0) (𝟙 _)).trans (val_mul hC _ _ _))
    have c0 : DegPre.cT D.toPre T 0 = 1 := cPoint_zero T
    have c1 : TorusCoord.cubVal
        (𝟙 _ ≫ (lift (DegPre.cT D.toPre T 0) (lift (DegPre.cT D.toPre T 0) b)).left) y C = 1 := by
      rw [c0, Category.id_comp]
      exact (isCub_cubV D.toPre.cub hC).face 1 b
    have h' := (congrArg (_ * ·) c1).symm.trans h
    rw [add_zero, _root_.mul_one] at h'
    exact (mul_eq_left.1 h'.symm).trans (val_one _).symm
  · have w : r ≫ (Over.mk (spMap φ)).hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← Over.w x, ← Category.assoc, ← hy, Category.assoc, Over.w (fstG I e G), Category.assoc]; rfl
    obtain ⟨l, rfl⟩ := exists_factor_level I φ r _ w
    obtain rfl : y = l ≫ reduction I x e := by
      rw [← cancel_mono (fstG I e G).left, Category.assoc, reduction_fstG]
      exact hy.trans (Category.assoc _ _ _)
    exact ⟨(Category.assoc _ _ _).trans ((congrArg (l ≫ ·) (hb e).symm).trans (Category.assoc _ _ _).symm),
      fun χ z C hC => vs χ e Z l z C hC⟩

end Glue

section Values

variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {ε : K → ℤ}

theorem valR_eq_of_val (hL : L.IsLB) {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) {t' : LB.Gen (LB.LinComb L φ' ε)} (ht' : t'.IsGen) {C : Type} [CommRing C] [IsLocalRing C]
    (r : Sp C ⟶ Y) (r' : Sp C ⟶ Y') (h : ∀ k, r ≫ φ k = r' ≫ φ' k)
    (hv : ∀ z J, Good L z J → val t r z J = val t' r' z J) (j : K → L.ι) (hj : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j) :
    ⊤ ≤ r' ⁻¹ᵁ LB.wchart L φ' j ∧ valR r _ (t.s j).val = valR r' _ (t'.s j).val := by
  have hj' : ⊤ ≤ r' ⁻¹ᵁ LB.wchart L φ' j := fun z hz => Set.mem_iInter.2 fun k => by
    have : (r ≫ φ k) z ∈ L.U (j k) := Set.mem_iInter.1 (hj hz) k
    rw [h k] at this
    exact this
  refine ⟨hj', toStkA_injective ?_⟩
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL (cpt C)
  refine (toStkA_valR r _ _ hj _).trans (Eq.trans (congrArg Units.val ?_) (toStkA_valR r' _ _ hj' _).symm)
  refine (gen_trans ht r _ (hj trivial) (hJ.mem φ r)).trans
    (Eq.trans ?_ (gen_trans ht' r' _ (hj' trivial) (hJ.mem φ' r')).symm)
  refine congrArg₂ (· * ·) ?_ (hv _ J hJ)
  exact Finset.prod_congr rfl fun k _ =>
    congrArg (fun q => gm q (cpt C) (L.U (j k) ⊓ L.U (J q)) (L.g (j k) (J q)) ^ ε k) (h k)

end Values

section Pull

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_gtPtF {T : Over (Spec (CommRingCat.of R))} (ξ : GtPt D T) (σ : TF (R := R) F ⟶ T) :
    ∃ g : GtPtF D F, g.b = σ ≫ ξ.b ∧ ∀ χ y J, Good D.P.L y J → val (g.s χ) (𝟙 _) y J = val (ξ.s χ) σ.left y J := by
  have e := TorusCoord.comp_eq_of_left ξ.b (σ ≫ ξ.b) σ.left (𝟙 _) (Category.id_comp _).symm
  have vp : ∀ χ y J, Good D.P.L y J →
      val (LB.pullGen D.P.L _ _ (ξ.s χ) σ.left) (𝟙 _) y J = val (ξ.s χ) σ.left y J := fun χ y J hJ => by
    rw [val_pull hJ, Category.id_comp]
  obtain ⟨g, hb, hv⟩ := exists_gt (σ ≫ ξ.b) (fun χ => LB.pullGen D.P.L _ _ (ξ.s χ) σ.left)
    (fun χ => DVR.pullGen_isGen _ _ _ _ (ξ.isGen χ) _)
    (fun χ U _ f => Finset.prod_congr rfl fun k _ => congrArg (fun q => f q ^ DegPre.gtε k)
      ((e.1 χ k).trans ((Category.id_comp _).trans (congrFun (TorusCoord.gtφT_eq (σ ≫ ξ.b) χ) k).symm)))
    (fun y J hJ => (vp 0 y J hJ).trans ((val_corr hJ ξ.s_zero _).trans (val_one _)))
    (fun χ χ' y J hJ => by
      rw [vp _ y J hJ, vp _ y J hJ, vp _ y J hJ, ← TorusCoord.val_s_mul ξ σ.left χ χ' y J hJ, e.2 χ χ',
        ← val_cubAt hJ]
      exact congrArg (_ * ·) (val_pull hJ _ _ _))
  exact ⟨g, hb, fun χ y J hJ => (hv χ y J hJ).trans (vp χ y J hJ)⟩

end Pull

section Factor

theorem exists_finset_factor {V C : Type} [CommRing V] [CommRing C] [IsLocalRing C] (j : V →+* C) {X : Scheme.{0}}
    (q : X ⟶ Sp V) [LocallyOfFiniteType q] (c : Sp C ⟶ X) (hc : c ≫ q = spMap j) :
    ∃ s : Finset C, ∀ (W : Type) [CommRing W] (φ : V →+* W) (io : W →+* C), Function.Injective io → io.comp φ = j →
      (∀ x ∈ s, x ∈ io.range) → ∃ c' : Sp W ⟶ X, spMap io ≫ c' = c ∧ c' ≫ q = spMap φ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (c (cpt C))) isOpen_univ
  have hU : IsAffineOpen U := hU
  have ht : ⊤ ≤ c ⁻¹ᵁ U := (top_le_iff_cpt c U).2 hx
  have hft : (q.appLE ⊤ U le_top).hom.FiniteType :=
    q.finiteType_appLE (isAffineOpen_top _) hU le_top
  let := (q.appLE ⊤ U le_top).hom.toAlgebra
  obtain ⟨t, hgen⟩ := (show Algebra.FiniteType Γ(Sp V, ⊤) Γ(X, U) from hft).out
  let v := (GlobalTheory.Points.valMap c U ht).hom
  refine ⟨t.image v, fun W _ φ io hio hj hs => ?_⟩
  have hall : ∀ f, v f ∈ io.range := fun f => by
    have hf : f ∈ Algebra.adjoin Γ(Sp V, ⊤) (t : Set Γ(X, U)) := hgen ▸ Algebra.mem_top
    induction hf using Algebra.adjoin_induction with
    | mem x hx => exact hs _ (Finset.mem_image_of_mem _ hx)
    | algebraMap a =>
      obtain ⟨a, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.symm.surjective a
      refine ⟨φ a, ?_⟩
      rw [← RingHom.comp_apply, hj, ← GlobalTheory.Points.valR_constFn_of_over q j c hc U ht a, GlobalTheory.Points.valR_eq c U ht]
      rfl
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let e : W ≃+* io.range := RingEquiv.ofBijective io.rangeRestrict
    ⟨fun a b h => hio (congrArg Subtype.val h), io.rangeRestrict_surjective⟩
  let ψ : Γ(X, U) →+* W := e.symm.toRingHom.comp (v.codRestrict io.range hall)
  have hψ : io.comp ψ = v := RingHom.ext fun f => congrArg Subtype.val (e.apply_symm_apply ⟨v f, hall f⟩)
  have h1 : spMap io ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec = c := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
    exact GlobalTheory.Points.specMap_valMap_fromSpec hU c ht
  refine ⟨_, h1, ?_⟩
  obtain ⟨θ, hθ⟩ := Spec.map_surjective ((Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) ≫ q)
  have h2 : θ ≫ CommRingCat.ofHom io = CommRingCat.ofHom j := Spec.map_injective (by
    rw [Spec.map_comp, hθ, ← Category.assoc, h1, hc])
  rw [← hθ]
  congr 1
  ext a
  exact hio ((congrArg (fun k => k.hom a) h2).trans (congrArg (fun k => k a) hj).symm)

end Factor

section Subring

open IsLocalRing

variable {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem exists_complete_subring [IsAdicComplete (maximalIdeal V) V] [CharZero V] (j : V →+* OO p)
    (hj : Function.Injective j) (hZ : ∀ a : ℤ_[p], padicIntToOO p a ∈ j.range) (s : Finset (OO p)) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (φ : V →+* W) (io : W →+* OO p), Function.Injective io ∧
      io.comp φ = j ∧ (∀ x ∈ s, x ∈ io.range) ∧ IsAdicComplete ((maximalIdeal V).map φ) W := by
  let : Algebra V (OO p) := j.toAlgebra
  let : Algebra V (PadicAlgCl p) := ((OO p).subtype.comp j).toAlgebra
  have : IsScalarTower V (OO p) (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul V (PadicAlgCl p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (Subtype.val_injective.comp hj)
  have hint : ∀ x : OO p, IsIntegral V (x : PadicAlgCl p) := fun x => by
    obtain ⟨q, hq, h⟩ := isIntegral_padicIntToOO x
    have hl : q.map (padicIntToOO p) ∈ Polynomial.lifts j := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      exact hZ _
    obtain ⟨q', h1, -, h2⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (hq.map _)
    have : IsIntegral V x := ⟨q', h2, by
      rw [Polynomial.eval₂_eq_eval_map]
      exact (congrArg (Polynomial.eval x) h1).trans ((Polynomial.eval_map _ _).trans h)⟩
    exact this.algebraMap (B := PadicAlgCl p)
  have : Algebra.IsAlgebraic V (PadicAlgCl p) := ⟨fun x => by
    rcases (OO p).mem_or_inv_mem x with h | h
    · exact (hint ⟨x, h⟩).isAlgebraic
    · exact IsAlgebraic.inv_iff.1 (hint ⟨_, h⟩).isAlgebraic⟩
  obtain ⟨W, hd, -, hc, hf, -, -, -, hs⟩ :=
    GlobalTheory.exists_complete_dvr_finite_subalgebra V (PadicAlgCl p) (s.image Subtype.val)
  have hW : ∀ w : W, (w : PadicAlgCl p) ∈ OO p := fun w => by
    have h1 : IsIntegral V (w : PadicAlgCl p) := (Algebra.IsIntegral.isIntegral (R := V) w).map W.val
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h1.tower_top (A := OO p))
    exact hy ▸ y.2
  refine ⟨W, inferInstance, inferInstance, algebraMap V W, W.val.toRingHom.codRestrict (OO p) hW,
    fun a b h => Subtype.ext (congrArg (fun y : OO p => (y : PadicAlgCl p)) h), RingHom.ext fun _ => rfl,
    fun x hx => ⟨⟨x, hs _ (Finset.mem_image_of_mem _ hx) (hint x)⟩, rfl⟩, hc⟩

end Subring

theorem exists_lev : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (c : Sp (OO p) ⟶ u.G.left), c ≫ u.G.hom = spMap u.j → ∃ g, u.Lev c g := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u c hc
  obtain ⟨h0, hloc, hinj, K, -, hK⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u
  have := u.complete
  have := u.U.smooth
  have hL := u.D.toPre.P.isLB
  have hZ : ∀ a : ℤ_[p], padicIntToOO p a ∈ u.j.range := fun a => by
    have h1 : (padicIntToOO p a : PadicAlgCl p) ∈ (K : Set (PadicAlgCl p)) := K.algebraMap_mem (a : ℚ_[p])
    rw [hK] at h1
    obtain ⟨x, hx⟩ := h1
    obtain ⟨v, rfl⟩ := (u.norm_le x).1 (hx ▸ (mem_OO_iff _).1 (padicIntToOO p a).2)
    exact ⟨v, Subtype.ext hx⟩
  obtain ⟨s, hs⟩ := exists_finset_factor u.j u.G.hom c hc
  obtain ⟨W, _, _, φ, io, hio, hφ, hsW, hW⟩ := exists_complete_subring u.j hinj hZ s
  obtain ⟨c', hc₁, hc₂⟩ := hs W φ io hio hφ hsW
  obtain ⟨ξ, hξ⟩ := exists_gtPt u.U.toUnifPre (φ := φ) (Over.homMk c' hc₂)
  let σ : TF (R := u.V) (PadicAlgCl p) ⟶ Over.mk (spMap φ) := Over.homMk (gPt p ≫ spMap io) (by
    show (gPt p ≫ spMap io) ≫ spMap φ = jFK (R := u.V) (PadicAlgCl p) ≫ jK u.V
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [RingHom.comp_assoc, hφ]
    rfl)
  obtain ⟨g, hb, hv⟩ := exists_gtPtF ξ σ
  refine ⟨g, spMap io ≫ ξ.b.left, ?_, fun e ce hce => ?_⟩
  · rw [hb, ← Category.assoc]; rfl
  have hne : u.lev e ≠ ⊤ := by
    refine ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal (OO p)).ne_top (Ideal.map_le_iff_le_comap.2 ?_)
    exact (Ideal.pow_le_self e.succ_ne_zero).trans (IsLocalRing.map_maximalIdeal_le u.j |> Ideal.map_le_iff_le_comap.1)
  have : Nontrivial (OO p ⧸ u.lev e) := Ideal.Quotient.nontrivial_iff.2 hne
  have : IsLocalRing (OO p ⧸ u.lev e) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk (u.lev e)) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨h₁, h₂⟩ := hξ e _ (spMap (Ideal.Quotient.mk (u.lev e)) ≫ spMap io) ce (by
    rw [hce, ← hc₁, Category.assoc]; rfl)
  refine ⟨h₁.trans (Category.assoc _ _ _), fun χ jj hjj => ?_⟩
  obtain ⟨m₁, v₁⟩ := valR_eq_of_val hL ((u.U.gt e).t_gen χ) (ξ.isGen χ) ce
    (spMap (Ideal.Quotient.mk (u.lev e)) ≫ spMap io)
    (fun k => ((TorusCoord.comp_eq_of_left ξ.b (u.U.gt e).pG _ ce h₁.symm).1 χ k).symm) (h₂ χ) jj hjj
  have m₂ : ⊤ ≤ spMap io ⁻¹ᵁ LB.wchart u.D.toPre.P.L (DegPre.gtφT u.D.toPre _ ξ.b χ) jj := by
    refine (top_le_iff_cpt _ _).2 ?_
    have := (top_le_iff_cpt _ _).1 m₁
    have e1 : spMap (Ideal.Quotient.mk (u.lev e)) (cpt _) = cpt (OO p) :=
      IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (u.lev e))
    rw [← e1]
    exact this
  obtain ⟨-, v₂⟩ := valR_eq_of_val hL (ξ.isGen χ) (g.isGen χ) (gPt p ≫ spMap io) (𝟙 _)
    (fun k => ((TorusCoord.comp_eq_of_left ξ.b g.b σ.left (𝟙 _)
      ((congrArg (·.left) hb).symm.trans (Category.id_comp _).symm)).1 χ k).trans
        (congrArg (𝟙 _ ≫ ·) (congrFun (TorusCoord.gtφT_eq g.b χ) k).symm))
    (fun z J hJ => (hv χ z J hJ).symm) jj (fun _ _ => m₂ trivial)
  exact ⟨valR (spMap io) _ ((ξ.s χ).s jj).val,
    (GlobalTheory.Points.valR_spMap_comp (OO p).subtype _ _ m₂ _).symm.trans v₂,
    (GlobalTheory.Points.valR_spMap_comp _ _ _ m₂ _).symm.trans v₁.symm⟩

end GlobalTheory.IntegralGt
end
