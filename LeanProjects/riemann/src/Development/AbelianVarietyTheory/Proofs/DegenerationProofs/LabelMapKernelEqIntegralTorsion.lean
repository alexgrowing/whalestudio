import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFactorOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FurtherLawsOfLaws
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointsIntegral
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTorusExtensionPointOfGroupPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointQkStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUOfIntegralTorsionPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbeddingStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.LabelKernel

open GlobalTheory.TorsionIntegral

theorem gm_spMap {F : Type} [Field F] (σ : F →+* F) (z : Sp F) (U : (Sp F).Opens) (hz : z ∈ U) (a : Γ(Sp F, U)ˣ)
    (x : F) (hx : toStalkField F z x = (gm (𝟙 (Sp F)) z U a).val) :
    toStalkField F z (σ x) = (gm (spMap σ) z U a).val := by
  obtain rfl : U = ⊤ := top_unique fun y _ => Subsingleton.elim (α := PrimeSpectrum F) z y ▸ hz
  obtain ⟨x', hx'⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a.val
  rw [gm_val _ z ⊤ trivial, ← hx'] at hx ⊢
  obtain rfl : x = x' := (toStalkField F z).injective hx
  exact (germTop_specMap σ z x).symm

section Generic

variable {V F : Type} [CommRing V] [IsDomain V] [Field F] {f : V →+* F} (hf : Function.Injective f)
  {φ : Sp F ⟶ Sp V} (hφ : φ = spMap f) (z : Sp F)
include hf hφ

omit [IsDomain V] in
theorem germTop_injective : Function.Injective (germTop φ z) := fun a b e => by
  subst hφ
  have hbij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv
  obtain ⟨a, rfl⟩ := hbij.2 a
  obtain ⟨b, rfl⟩ := hbij.2 b
  exact congrArg _ (hf ((toStalkField F z).injective
    ((germTop_specMap _ z a).symm.trans (e.trans (germTop_specMap _ z b)))))

omit [IsDomain V] in
theorem mem_of_mem (U : (Sp V).Opens) (y : Sp V) (hy : y ∈ U) : φ z ∈ U := by
  subst hφ
  refine Specializes.mem_open ((PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_) U.isOpen hy
  have ha' : f a ∈ z.asIdeal := ha
  rw [Subsingleton.elim (α := PrimeSpectrum F) z ⊥, PrimeSpectrum.asIdeal_bot, Ideal.mem_bot,
    map_eq_zero_iff _ hf] at ha'
  exact ha' ▸ zero_mem _

theorem ext_of_separated {B : Over (Sp V)} [IsSeparated B.hom] (ψ ψ' : Sp V ⟶ B.left) (h : φ ≫ ψ = φ ≫ ψ') :
    ψ = ψ' := by
  subst hφ
  have : IsDominant (spMap f) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hf]; exact bot_le)⟩
  have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
  exact ext_of_isDominant (spMap f) h

end Generic

section Descent

variable {V : Type} [CommRing V] [IsDomain V] {F : Type} [Field F] [Algebra (FractionRing V) F]

omit [IsDomain V] in
theorem toUnit_left : (toUnit (TF (R := V) F)).left =
    spMap ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))) :=
  (Spec.map_comp _ _).symm

theorem base_injective :
    Function.Injective ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))) :=
  (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))

omit [IsDomain V] in
theorem spMap_jFK (σ : F ≃ₐ[FractionRing V] F) : spMap (σ : F →+* F) ≫ jFK (R := V) F = jFK (R := V) F := by
  rw [jFK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext σ.commutes

theorem exists_integral_of_fixed [ValuationRing V] [CharZero V] [IsAlgClosed F] {D : DegPre V} {N : ℕ} (hN : 1 ≤ N)
    (g : GtPtF D F) (hg : UU.GtTors D N g)
    (hb : ∀ σ : F ≃ₐ[FractionRing V] F, g.b.left = spMap (σ : F →+* F) ≫ g.b.left)
    (hs : ∀ (σ : F ≃ₐ[FractionRing V] F) χ,
      LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.pullGen D.P.L _ _ (g.s χ) (spMap (σ : F →+* F)))) :
    ∃ g' : GtPt D (𝟙_ (Over (Sp V))), GtPt.IsPullF F (toUnit (TF (R := V) F)).left g' g ∧
      ∃ h, GtPt.IsNsmul N g' h ∧ h.IsZero := by
  have := D.P.isAb.proper
  have : CharZero (FractionRing V) := charZero_of_injective_algebraMap (IsFractionRing.injective V _)
  obtain ⟨b₀, hb₀⟩ := (FixedPoint.existsUnique_factor_of_isAlgClosed (K₀ := FractionRing V) (L := F) g.b.left
    fun σ => (hb σ).symm).exists
  have hw : b₀ ≫ D.P.A.hom = jK V :=
    FixedPoint.point_ext (K₁ := F) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ D.P.A.hom) hb₀).trans (Over.w g.b)))
  obtain ⟨S₀, hS₀⟩ := exists_finset_extend D.P.A b₀ hw
  obtain ⟨l, hl₁, hl₂⟩ := hS₀ V (IsFractionRing.injective V _) fun x _ => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) x
    have hb' := nonZeroDivisors.ne_zero hb
    exact ⟨a, b, hb', div_mul_cancel₀ _ ((map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hb')⟩
  let b' : 𝟙_ (Over (Sp V)) ⟶ D.P.A := Over.homMk l (hl₂.trans (Spec.map_id _))
  let φ := toUnit (TF (R := V) F)
  have hbb : φ ≫ b' = g.b := Over.OverMorphism.ext
    ((Category.assoc _ _ _).trans ((congrArg (jFK (R := V) F ≫ ·) hl₁).trans hb₀))
  let z : Sp F := IsLocalRing.closedPoint F
  have hρ := germTop_injective base_injective (toUnit_left (V := V) (F := F)) z
  have he := ext_of_separated (B := D.P.A) base_injective (toUnit_left (V := V) (F := F))
  have : PreValuationRing Γ(Sp V, ⊤) :=
    Function.Surjective.preValuationRing (R := V) (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).2
  obtain ⟨J₀, hJ₀, h₀⟩ := exists_good_global (Y := Sp V) D.P.isLB φ.left z (IsLocalRing.closedPoint V)
    (fun U y hy => (IsLocalRing.specializes_closedPoint y).mem_open U.isOpen hy) he
  refine exists_torsion_extend φ z (mem_of_mem base_injective toUnit_left z) (gm_injective (Y := Sp V) φ.left z hρ) he
    hJ₀ h₀ g hg b' hbb Set.univ Submodule.span_univ ?_
  rintro χ - ⟨u, hu⟩
  obtain ⟨x, hx⟩ := toStalkField_surjective F z (val (g.s χ) (𝟙 _) z J₀).val
  obtain ⟨y, rfl⟩ : x ∈ Set.range (algebraMap (FractionRing V) F) :=
    GaloisDescent.mem_range_algebraMap_of_forall_algEquiv x fun σ => (toStalkField F z).injective (by
      have e := (val_corr hJ₀ (hs σ χ) (𝟙 _)).trans (val_pull hJ₀ _ _ _)
      rw [Category.id_comp] at e
      have e' := val_of (g.s χ) (spMap (σ : F →+* F)) z J₀ (fun k => J₀ (𝟙 _ ≫ DegPre.gtφ D F g.b χ k)) fun k => by
        refine congrArg J₀ ?_
        rw [Category.id_comp, gtφ_comp φ hbb χ k, ← Category.assoc]
        exact congrArg (· ≫ _) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK V) (spMap_jFK σ)))
      exact (gm_spMap (σ : F →+* F) z _ (hJ₀.mem _ (𝟙 _)) _ x hx).trans
        ((congrArg Units.val (e.trans e').symm).trans hx.symm))
  have hfrac : val (g.s χ) (𝟙 _) z J₀ ∈ fracUnits (germTop (Y := Sp V) φ.left z) := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) y
    have hb' := (map_ne_zero_iff _ (base_injective (V := V) (F := F))).2 (nonZeroDivisors.ne_zero hb)
    have k : ∀ c : V, germTop (Y := Sp V) φ.left z ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c) =
        toStalkField F z (algebraMap (FractionRing V) F (algebraMap V _ c)) := fun c =>
      (congrArg (fun q : Sp F ⟶ Sp V => germTop q z _) toUnit_left).trans (germTop_specMap _ z c)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a, (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b, ?_, ?_⟩
    · rw [k]
      exact (Ne.isUnit hb').map _
    · rw [k, k]
      refine (congrArg (· * _) hx.symm).trans ((map_mul _ _ _).symm.trans (congrArg _ ?_))
      rw [map_div₀]
      exact div_mul_cancel₀ _ hb'
  obtain ⟨u', hu'⟩ := exists_unit_of_pow hρ hfrac hN (u := u)
    ((gm_val φ.left z ⊤ trivial u).symm.trans (congrArg Units.val hu))
  exact ⟨u', Units.ext ((gm_val φ.left z ⊤ trivial u').trans hu')⟩

end Descent

section Points

open GlobalTheory.FormalPoint GlobalTheory.TorusExt

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {I : Ideal V} {D : DegData V I}
  {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]

omit [IsLocalRing V] in
theorem exists_level {U : UnifPre I D A G} {gp : GtPt D.toPre (𝟙_ (Over (Sp V)))} {x : 𝟙_ (Over (Sp V)) ⟶ G}
    (hx : IsPointOf U gp x) (e : ℕ) :
    ∃ xe : Over.mk (thick V I e) ⟶ (Over.map (thick V I e)).obj (thickObj V I e G),
      xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧
      ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left)
        (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick V I e))).left) := by
  obtain ⟨y, hy⟩ := exists_hasCoords U e gp (toUnit (Over.mk (thick V I e))).left (𝟙 _)
    ((Category.id_comp _).trans (Over.w (toUnit (Over.mk (thick V I e)))).symm)
  have h₁ := hx.comp_fstG_eq hy
  exact ⟨Over.homMk y ((congrArg (y ≫ ·) (Over.w (fstG I e G)).symm).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ G.hom) h₁).trans (Over.w (toUnit (Over.mk (thick V I e)) ≫ x))))),
    Over.OverMorphism.ext h₁, Over.OverMorphism.ext hy.1, hy.2⟩

theorem pow_eq_one_of_chain (hG : GlobalFnsSt) [IsAdicComplete I V] {U : UnifPre I D A G}
    {gp h : GtPt D.toPre (𝟙_ (Over (Sp V)))} {x : 𝟙_ (Over (Sp V)) ⟶ G} (hx : IsPointOf U gp x) {k : ℕ}
    (hk : GtPt.IsNsmul k gp h) (h₀ : h.IsZero) : x ^ k = 1 := by
  obtain ⟨gs, hz, hs, rfl⟩ := hk
  have key : ∀ i : Fin (k + 1), IsPointOf U (gs i) (x ^ i.val) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [Fin.val_zero, pow_zero]
      exact isPointOf_one U hz
    | succ i ih =>
      rw [Fin.val_succ, pow_succ]
      exact ih.mul hG hx (hs i)
  exact (existsUnique_isPointOf_unit U _).unique (key (Fin.last k)) (isPointOf_one U h₀)

variable (hR : AdmBase V I) (hI : I ≠ ⊤) (U : Unif I D A G) {F : Type} [Field F] [Algebra (FractionRing V) F]
  {k : ℕ} (hk : 1 ≤ k)
include hR hI hk

theorem exists_pair_of_integral (hL : Laws) (X : 𝟙_ (Over (Sp V)) ⟶ G) (x : TFK (R := V) F ⟶ A.A) (hx : x ^ k = 1)
    (h : x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = (toUnit (TF (R := V) F) ≫ X).left) :
    ∃ p : QkPt D.toPre F k, p.y = 0 ∧ QkToAkU U.toUnifPre F k p x := by
  have := U.gen_hom
  have := U.separated
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gpb : IsGrpPullback A.A G (jK V) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl
  have e := IntegralTorsionImage.push_eq gpb X x (h.trans (Category.assoc _ _ _)) (𝟙 _)
  rw [Category.id_comp] at e
  have e₁ : toUnit (TF (R := V) F) ≫ X ^ k = toUnit (TF (R := V) F) ≫ 1 :=
    (map_pow (preHom _) X k).trans ((congrArg (· ^ k) e.symm).trans ((map_pow _ x k).symm.trans
      ((congrArg _ hx).trans ((map_one _).trans (MonObj.comp_one _).symm))))
  have hX : X ^ k = 1 := Over.OverMorphism.ext
    (ext_of_separated (B := G) base_injective (toUnit_left (V := V) (F := F)) _ _ (congrArg (fun q => q.left) e₁))
  obtain ⟨gp, hgp, -⟩ := existsUnique_gtPt_of_point V I hR hI D A G U.toUnifPre X
  obtain ⟨p, hp, hpg⟩ := (T.torsionPoint_qk_alt hL.globalFns V I hR hI D A G U.toUnifPre k X gp hX hgp).2 F
  exact ⟨p, hp, qkToAkU_of_integral_torsion hL V I hR hI D A G U k hk X gp hX hgp F p x hp hpg h⟩

attribute [local instance] gtGroup in

theorem exists_integral_of_pair [ValuationRing V] [CharZero V] [IsAlgClosed F] (hL : Laws) (hL₂ : Laws2)
    (hG : IsSemiAbelian G) (f : QkPt D.toPre F k → (TFK (R := V) F ⟶ A.A))
    (h₁ : ∀ p x, QkToAkU U.toUnifPre F k p x ↔ x = f p) (h₂ : ∀ p p', f p = f p' ↔ QkPt.Equiv D.toPre F p p')
    (p : QkPt D.toPre F k) (hp : p.y = 0) (xK : Sp (FractionRing V) ⟶ A.A.left)
    (hx : (f p).left = jFK (R := V) F ≫ xK) :
    ∃ X : 𝟙_ (Over (Sp V)) ⟶ G, xK ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = jK V ≫ X.left := by
  have := hR.2.2.2
  obtain ⟨l₃, l₄, l₅, -⟩ := furtherLaws_of_laws hL twistBaseChange
  have hB := D.tau_bimult
  have fix : ∀ σ : F ≃ₐ[FractionRing V] F, p.g.b.left = spMap (σ : F →+* F) ≫ p.g.b.left ∧ ∀ χ,
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (p.g.s χ) (LB.pullGen D.toPre.P.L _ _ (p.g.s χ) (spMap (σ : F →+* F))) := by
    intro σ
    have hσ : (σ : F →+* F).comp (algebraMap (FractionRing V) F) = algebraMap (FractionRing V) F :=
      RingHom.ext σ.commutes
    have e := (T.qkToAkU_iff_galois_equivariant ⟨hL, hL₂, l₃, l₄, l₅⟩ V I hR D A G hG U F F σ.toAlgHom k hk p (qkExt hB _ hσ p) (f p) (f p)
      ((qkExt_iff hB _ hσ _ _).2 rfl) (hx.trans ((congrArg (· ≫ xK) (spMap_jFK σ).symm).trans
        ((Category.assoc _ _ _).trans (congrArg (spMap (σ : F →+* F) ≫ ·) hx.symm))))).1 ((h₁ _ _).2 rfl)
    obtain ⟨z, hz, hg⟩ := (equiv_iff hB _ _).1 ((h₂ _ _).1 ((h₁ _ _).1 e))
    have hz' : (k : ℤ) • z = 0 := by
      rw [natCast_zsmul]
      exact left_eq_add.1 (show p.y = p.y + k • z from hz)
    obtain rfl : z = 0 := (smul_eq_zero.1 hz').resolve_left (by omega)
    rw [map_zero, add_zero] at hg
    exact (eq_gtExt_iff _ hσ _ _).1 hg.symm
  obtain ⟨gp, hgp, h, hh, h₀⟩ := exists_integral_of_fixed hk p.g
    ⟨k • p.g, (isNsmul_iff_eq _ _ _).2 rfl, (isZero_iff_eq _).2 (by rw [qk_nsmul hB, hp, map_zero])⟩
    (fun σ => (fix σ).1) fun σ => (fix σ).2
  obtain ⟨X, hX, -⟩ := existsUnique_isPointOf_unit U.toUnifPre gp
  let y : TFK (R := V) F ⟶ (Over.pullback (jK V)).obj G :=
    Over.homMk (pullback.lift (toUnit (TF (R := V) F) ≫ X).left (jFK (R := V) F)
      (Over.w (toUnit (TF (R := V) F) ≫ X))) (pullback.lift_snd _ _ _)
  have hy : (y ≫ U.gen.hom).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) =
      (toUnit (TF (R := V) F) ≫ X).left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  have e := (h₁ _ _).1 (qkToAkU_of_integral_torsion hL V I hR hI D A G U k hk X gp
    (pow_eq_one_of_chain hL.globalFns hX hh h₀) (exists_level hX) F p _ hp hgp hy)
  rw [e, hx] at hy
  exact ⟨X, FixedPoint.point_ext (K₁ := F) ((Category.assoc _ _ _).symm.trans (hy.trans (Category.assoc _ _ _)))⟩

end Points

theorem pt_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) (a : S.Gam) :
    ρ.pt a ^ (S.r * S.N) = 1 := by
  have h₀ : ρ.pt 0 = 1 := mul_eq_left.1 ((ρ.pt_add 0 0).symm.trans (congrArg _ (add_zero _)))
  have h : ∀ n : ℕ, ρ.pt a ^ n = ρ.pt (n • a) := fun n => by
    induction n with
    | zero => rw [pow_zero, zero_nsmul, h₀]
    | succ n ih => rw [pow_succ, succ_nsmul, ρ.pt_add, ih]
  have hz : (S.r * S.N) • a = 0 := funext fun i => by
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]; rfl
  rw [h, hz, h₀]

theorem main : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range), Function.Surjective yy → (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ a, a ∈ yy.ker ↔ u.Integral a := by
  intro hL hL₂ hT o Ω _ _ _ _ S ρ p _ y₀ u yy _ hyy _ a
  have : CharZero u.V := ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V _)).charZero
  have hk : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (lt_of_lt_of_le two_pos S.N_ge)
  have hR : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hI := (IsLocalRing.maximalIdeal.isMaximal u.V).ne_top
  obtain ⟨f, h₁, h₂, h₃, -⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) _ hk
  obtain ⟨xK, x₁, x₂⟩ : ∃ xK : Sp (FractionRing u.V) ⟶ u.A.A.left,
      xK ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left ∧ xK ≫ u.A.A.hom = 𝟙 _ :=
    ⟨u.cart.1.lift (spMap u.yK ≫ (ρ.pt a).left) (𝟙 _) ((Category.assoc _ _ _).trans
      ((congrArg _ (Over.w (ρ.pt a))).trans ((Category.comp_id _).trans (Category.id_comp _).symm))),
      u.cart.1.lift_fst _ _ _, u.cart.1.lift_snd _ _ _⟩
  let x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A := Over.homMk (jFK (R := u.V) (PadicAlgCl p) ≫ xK)
    ((Category.assoc _ _ _).trans ((congrArg _ x₂).trans (Category.comp_id _)))
  have hx₁ : x.left ≫ u.φ = jFK (R := u.V) (PadicAlgCl p) ≫ spMap u.yK ≫ (ρ.pt a).left :=
    (Category.assoc _ _ _).trans (congrArg _ x₁)
  have hy : jFK (R := u.V) (PadicAlgCl p) ≫ spMap u.yK = spMap y₀ :=
    (Spec.map_comp _ _).symm.trans (congrArg spMap u.fac)
  have hx₂ : x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left :=
    hx₁.trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (ρ.pt a).left) hy))
  have hx : x ^ (S.r * S.N) = 1 := IntegralTorsionImage.pow_eq_one_of_push u.cart (ρ.pt a) x hx₁ (pt_pow_eq_one ρ a)
  have ih : u.U.gen.inv.left ≫ u.U.gen.hom.left = 𝟙 _ := congrArg Over.Hom.left u.U.gen.inv_hom_id
  have hi : u.U.gen.hom.left ≫ u.U.gen.inv.left = 𝟙 _ := congrArg Over.Hom.left u.U.gen.hom_inv_id
  constructor
  · intro ha
    obtain ⟨q, hq⟩ := h₂ x hx
    obtain ⟨z, hz⟩ := (QuotientAddGroup.eq_zero_iff _).1 ((hyy a q x ((h₁ _ _).2 hq.symm) hx₂).symm.trans ha)
    obtain ⟨X, hX⟩ := exists_integral_of_pair hR hI u.U hk hL hL₂ u.semi f h₁ h₃
      (TorusExt.qkShift u.D.tau_bimult q (-z)) (by
        show q.y + (S.r * S.N) • -z = 0
        rw [← hz, smul_neg]
        exact add_neg_cancel _) xK
      (congrArg (fun t => t.left) (((h₃ _ _).2 (TorusExt.equiv_qkShift u.D.tau_bimult q (-z))).symm.trans hq))
    refine ⟨X.left, xK ≫ u.U.gen.inv.left, Over.w X, (Category.assoc _ _ _).trans hX,
      (Category.assoc _ _ _).trans ((congrArg _ (Over.w u.U.gen.inv)).trans x₂), ?_⟩
    exact (Category.assoc _ _ _).trans ((congrArg (xK ≫ ·) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ u.φ) ih).trans (Category.id_comp _)))).trans x₁)
  · rintro ⟨h, w, w₁, w₂, w₃, w₄⟩
    have e : xK = w ≫ u.U.gen.hom.left := u.cart.1.hom_ext (x₁.trans (w₄.symm.trans (Category.assoc _ _ _).symm))
      (x₂.trans (w₃.symm.trans ((congrArg (w ≫ ·) (Over.w u.U.gen.hom).symm).trans (Category.assoc _ _ _).symm)))
    have e' : xK ≫ u.U.gen.inv.left ≫ pullback.fst u.G.hom (jK u.V) = jK u.V ≫ h :=
      (congrArg (· ≫ _) e).trans ((Category.assoc _ _ _).trans ((congrArg (w ≫ ·) ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) hi).trans (Category.id_comp _)))).trans w₂))
    obtain ⟨q, hq, hqx⟩ := exists_pair_of_integral hR hI u.U hk hL (Over.homMk h w₁) x hx
      ((Category.assoc _ _ _).trans ((congrArg _ e').trans (Category.assoc _ _ _).symm))
    rw [AddMonoidHom.mem_ker, hyy a q x hqx hx₂, hq]
    rfl

end GlobalTheory.ZH.LabelKernel
