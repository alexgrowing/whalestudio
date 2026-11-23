import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalBasisAlong
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExtendedArcUAdicUniformisationOfArcData
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniversalSectionBasisPolarisedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNzOfPolAtStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyUniformisationTraitInAbelianLocusStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeneratingSectionFiniteExtNormalDomainIsBasisStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteNormalAdjoinAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationOverFiniteDvrExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtensStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsAtUniformisedTraitStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.Ex.OneGen

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

section Mod
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

def fnR {K : Type} [CommRing K] (x : Sp K ⟶ S) : K ≃+* Γ((Over.mk x).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm

def pl {K K' : Type} [CommRing K] [CommRing K'] (i : K →+* K') {x : Sp K ⟶ S} {x' : Sp K' ⟶ S} (h : spMap i ≫ x = x')
    (s : SecM G L ((1 : ℕ) : ℤ) (Over.mk x)) : SecM G L ((1 : ℕ) : ℤ) (Over.mk x') :=
  VVRank.pullM G L _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) s

variable {K K' K'' : Type} [CommRing K] [CommRing K'] [CommRing K''] {x : Sp K ⟶ S} {x' : Sp K' ⟶ S} {x'' : Sp K'' ⟶ S}

theorem pl_smul (i : K →+* K') (h : spMap i ≫ x = x') (a : K) (s : SecM G L ((1 : ℕ) : ℤ) (Over.mk x)) :
    pl i h (fnR x a • s) = fnR x' (i a) • pl i h s := by
  refine ((VVRank.pullM G L _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x)).map_smulₛₗ _ _).trans
    (congrArg (· • pl i h s) ?_)
  exact (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm

theorem pl_ofSec (i : K →+* K') (h : spMap i ≫ x = x') (s : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))) :
    pl i h (SecM.ofSec G s) =
      SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) s) := rfl

theorem ofSec_toSec {T : Over S} (f : SecM G L ((1 : ℕ) : ℤ) T) : SecM.ofSec G (SecM.toSec G f) = f := rfl

theorem pl_comp (hL : L.IsLB) (i : K →+* K') (j : K' →+* K'') (k : K →+* K'') (e : j.comp i = k) (h : spMap i ≫ x = x')
    (h' : spMap j ≫ x' = x'') (h'' : spMap k ≫ x = x'') (s : SecM G L ((1 : ℕ) : ℤ) (Over.mk x)) :
    pl j h' (pl i h s) = pl k h'' s := by
  subst e
  refine (VVRank.pullM_comp G hL _ _ _ s).trans (congrArg (fun q => VVRank.pullM G L _ q s) ?_)
  exact Over.OverMorphism.ext (sp_comp i j).symm

variable {e : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))}

theorem UnivBasis.ex (he : UnivBasis G L x e) (i : K →+* K') (h : spMap i ≫ x = x')
    (s : SecM G L ((1 : ℕ) : ℤ) (Over.mk x')) : ∃ a : K', s = fnR x' a • pl i h (SecM.ofSec G e) := by
  obtain ⟨c, hc, -⟩ := he K' i x' h s
  obtain ⟨a, rfl⟩ := (fnR x').surjective c
  exact ⟨a, hc⟩

theorem UnivBasis.inj (he : UnivBasis G L x e) (i : K →+* K') (h : spMap i ≫ x = x') {a b : K'}
    (H : fnR x' a • pl i h (SecM.ofSec G e) = fnR x' b • pl i h (SecM.ofSec G e)) : a = b :=
  (fnR x').injective ((he K' i x' h _).unique rfl H)

theorem UnivBasis.smul_pull (hL : L.IsLB) (he : UnivBasis G L x e) (i : K →+* K') (h : spMap i ≫ x = x') {a : K'}
    (ha : IsUnit a) : UnivBasis G L x' (SecM.toSec G (fnR x' a • pl i h (SecM.ofSec G e))) := by
  intro K'' _ j x'' h' s
  have h'' : spMap (j.comp i) ≫ x = x'' := by rw [sp_comp, Category.assoc, h, h']
  obtain ⟨u, rfl⟩ := ha
  have E : ∀ c : K'', fnR x'' c • pl j h' (fnR x' u.val • pl i h (SecM.ofSec G e)) =
      fnR x'' (c * j u.val) • pl _ h'' (SecM.ofSec G e) := fun c => by
    rw [pl_smul, pl_comp hL i j _ rfl h h' h'', smul_smul, map_mul]
  obtain ⟨b, hb⟩ := he.ex _ h'' s
  refine ⟨fnR x'' (b * j u⁻¹.val), hb.trans (Eq.trans ?_ (E _).symm), fun c hc => ?_⟩
  · rw [_root_.mul_assoc, ← map_mul, u.inv_mul, map_one, _root_.mul_one]
  · obtain ⟨c, rfl⟩ := (fnR x'').surjective c
    rw [he.inj _ h'' (hb.symm.trans (hc.trans (E c))), _root_.mul_assoc, ← map_mul, u.mul_inv, map_one, _root_.mul_one]

theorem isGenSec_iff {T : Over S} (th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) : IsGenSec G L ((1 : ℕ) : ℤ) th ↔
    ∀ s : SecM G L ((1 : ℕ) : ℤ) T, ∃ r : Γ(T.left, ⊤), s = r • SecM.ofSec G th :=
  ⟨fun h s => (h (SecM.toSec G s)).imp fun _ hr => Subtype.ext (funext hr),
    fun h s => (h (SecM.ofSec G s)).imp fun _ hr j => congrArg (fun q => q.1 j) hr⟩

theorem UnivBasis.ne_zero [Nontrivial K'] (he : UnivBasis G L x e) (i : K →+* K') (h : spMap i ≫ x = x')
    {th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x'))} (hth : IsGenSec G L ((1 : ℕ) : ℤ) th) {s : K'}
    (hs : SecM.ofSec G th = fnR x' s • pl i h (SecM.ofSec G e)) : s ≠ 0 := by
  rintro rfl
  obtain ⟨r, hr⟩ := (isGenSec_iff th).1 hth (pl i h (SecM.ofSec G e))
  refine one_ne_zero (he.inj i h (a := 1) (b := 0) ?_)
  rw [map_zero, zero_smul] at hs
  rw [hs, smul_zero] at hr
  rw [hr, smul_zero, smul_zero]

theorem UnivBasis.pl_ne_zero [Nontrivial K'] (he : UnivBasis G L x e) (i : K →+* K') (h : spMap i ≫ x = x') :
    pl i h (SecM.ofSec G e) ≠ 0 := fun h0 =>
  one_ne_zero (he.inj i h (a := 1) (b := 0) (by rw [h0, smul_zero, smul_zero]))

theorem isGenSec_unit (i : K →+* K') (h : spMap i ≫ x = x') (u : Kˣ)
    (H : IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) e)) :
    IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x)
      (SecM.toSec G (fnR x u⁻¹.val • SecM.ofSec G e))) := by
  refine (isGenSec_iff _).2 fun s => ?_
  obtain ⟨r, hr⟩ := (isGenSec_iff _).1 H s
  refine ⟨r * fnR x' (i u.val), ?_⟩
  change s = _ • pl i h (fnR x u⁻¹.val • SecM.ofSec G e)
  rw [pl_smul, smul_smul, _root_.mul_assoc, ← map_mul, ← map_mul, u.mul_inv, map_one, map_one, _root_.mul_one]
  exact hr

theorem lin_of_pl (hL : L.IsLB) (i : K →+* K') (h : spMap i ≫ x = x') (s : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x')))
    (H : pl i h (SecM.ofSec G e) = SecM.ofSec G s) :
    GlobalTheory.LN.Lin G L 1 (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) (fun _ : Fin 1 => e) (fun _ => 1) s :=
  (GlobalTheory.LN.PolFrames.lin_iff G L 1 _ hL (fun _ => VVRank.isPullSec_pullS G _ _ e) _ _).2 (by
    rw [Fin.sum_univ_one, one_smul]; exact H)

end Mod

theorem val_eq_zero {F I : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (a : F) (y : I → F) (h₁ : ∀ i, 0 ≤ v (y i))
    (h₂ : ∃ i, v (y i) = 0) (h₃ : ∀ i, 0 ≤ v (a * y i)) (h₄ : ∃ i, v (a * y i) = 0) : v a = 0 := by
  obtain ⟨i, hi⟩ := h₂
  obtain ⟨j, hj⟩ := h₄
  have e := h₃ i
  rw [AddValuation.map_mul, hi, add_zero] at e
  rw [AddValuation.map_mul] at hj
  exact le_antisymm (hj ▸ le_add_of_nonneg_right (h₁ j)) e

theorem exists_prime {O : Type} [CommRing O] [IsDomain O] {ϖ : O} (h : GlobalTheory.LN.ArcBase O ϖ) :
    ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : O) := by
  have : IsLocalRing O := by
    rcases h with h | h
    · letI := h.1.toField; infer_instance
    · have := h.1; infer_instance
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := ((3 : ℕ) : O) * 2) (b := ((5 : ℕ) : O) * (-1)) (by push_cast; ring) with
    h | h
  · exact ⟨3, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩
  · exact ⟨5, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩

set_option maxHeartbeats 800000 in

theorem basis_at_trait (hV : HV) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}
    (t : SAB H S) {K₂ K : Type} [Field K₂] [Field K] (e : K₂ →+* K) {x₂ : Sp K₂ ⟶ S} {x₀ : Sp K ⟶ S}
    (he : spMap e ≫ x₂ = x₀) {θ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk x₂))} (hθ : UnivBasis t.G t.PP.L x₂ θ)
    (hext : ∀ (F : Type) [Field F] [IsAlgClosed F] (g : K₂ →+* F), ∃ g' : K →+* F, g'.comp e = g)
    {th : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk x₀))} (eth : pl e he (SecM.ofSec t.G θ) = SecM.ofSec t.G th)
    {m : ℕ} (hm : Odd m) (h3 : 3 ≤ m) {I : Type} (y : I → K)
    (hy : ∀ (F : Type) [Field F] [IsAlgClosed F] (g : K →+* F) (x' : Sp F ⟶ S) (h : spMap g ≫ x₀ = x') (a : F)
      (th' : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk x'))),
      SecM.ofSec t.G th' = @id Γ((Over.mk x').left, ⊤) (fnOf a) •
        SecM.ofSec t.G (VVRank.pullS t.G _ (Over.homMk (spMap g) h : Over.mk x' ⟶ Over.mk x₀) th) →
      (∀ i, ∃ z, ThG t.G t.PP.L t.PP.rig m th' z (fnOf (a * g (y i)))) ∧
        ∀ z (c : F), ThG t.G t.PP.L t.PP.rig m th' z (fnOf c) → ∃ i, c = a * g (y i))
    {R : Type} (a₂ : R → K₂) (hint : ∀ A : ValuationSubring K, (∀ r, e (a₂ r) ∈ A) → (∀ i, y i ∈ A) ∧ ∃ i, A.valuation (y i) = 1)
    {W W' : Type} [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing W'] [IsDomain W'] [IsLocalRing W']
    (hW : GlobalTheory.LN.CDvr W) (hW' : GlobalTheory.LN.CDvr W') (io : W →+* W') (hi : Function.Injective io) (hf : io.Finite)
    (hu : IsUnit (m : W)) (gam : K₂ →+* FractionRing W) (hg : ∀ r, ∃ w, gam (a₂ r) = algebraMap W _ w) (χ : Sp W ⟶ S)
    (hχ : spMap gam ≫ x₂ = jK W ≫ χ) {t₁ : SAB H (Sp W)} (m₁ : SABMap t₁ t χ) (hp : GlobalTheory.LN.PolAt t₁ (jK W))
    {t' : SAB H (Sp W')} (m' : SABMap t' t (spMap io ≫ χ)) (P : PELUnif (maximalIdeal W') t') :
    ∃ b : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ)),
      GlobalTheory.LN.BasisAlong t.G t.PP.L 1 (𝟙 (Over.mk χ)) (fun _ : Fin 1 => b) ∧
      pl (algebraMap W (FractionRing W)) (x' := jK W ≫ χ) rfl (SecM.ofSec t.G b) = pl gam hχ (SecM.ofSec t.G θ) := by
  have hL := t.PP.isLB
  have := hW.1
  have := hW'.1
  have := t.semi.smooth
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_nz_of_polAt' hV.1.1 hV.1.2.1 E H S t W χ t₁ m₁ hp
  obtain ⟨hgen, hval⟩ := GlobalTheory.T.theta_constants_at_uniformised_trait hV E H S t W' hW' _ t' m' P _ (hσ W' io _ rfl)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W'
  let F := AlgebraicClosure (FractionRing W')
  obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 W' ϖ hϖ
  obtain ⟨hpos, ⟨io', hio', hun⟩, hA⟩ := GlobalTheory.T.valuation_over_finite_dvr_extension W W' io hi hf ϖ hϖ F v hv
  let j : FractionRing W →+* F := (algebraMap (FractionRing W') F).comp io'
  let k : W' →+* F := (algebraMap (FractionRing W') F).comp (algebraMap W' _)
  obtain ⟨g, hge⟩ := hext F (j.comp gam)
  obtain ⟨A, hA⟩ := hA K g
  obtain ⟨hy₁, hy₂⟩ := hint A fun r => (hA _).1.2 (by
    obtain ⟨w, hw⟩ := hg r
    rw [← RingHom.comp_apply, hge, RingHom.comp_apply, hw]
    exact (congrArg (fun q => 0 ≤ v (algebraMap _ F q)) (hio' w)).mpr (hpos _))
  have ejk : j.comp (algebraMap W _) = k.comp io := RingHom.ext fun w => congrArg (algebraMap _ F) (hio' w)
  have h₁ : spMap j ≫ jK W ≫ χ = spMap g ≫ x₀ := by
    rw [← hχ, ← he, ← Category.assoc, ← Category.assoc, ← sp_comp, ← sp_comp, hge]
  have h₂ : spMap (k.comp io) ≫ χ = spMap g ≫ x₀ := by rw [← ejk, sp_comp, Category.assoc]; exact h₁
  have h₃ : spMap k ≫ spMap io ≫ χ = spMap g ≫ x₀ := by rw [← Category.assoc, ← sp_comp, h₂]
  have h₄ : spMap (j.comp gam) ≫ x₂ = spMap g ≫ x₀ := by rw [sp_comp, Category.assoc, hχ, h₁]
  obtain ⟨a, ha⟩ := hθ.ex gam hχ (pl (algebraMap W (FractionRing W)) (x' := jK W ≫ χ) rfl (SecM.ofSec t.G σ))
  have hF : pl k h₃ (pl io rfl (SecM.ofSec t.G σ)) = fnR (spMap g ≫ x₀) (j a) • pl g rfl (pl e he (SecM.ofSec t.G θ)) := by
    rw [pl_comp hL io k _ rfl rfl h₃ h₂, ← pl_comp hL _ j _ ejk (x' := jK W ≫ χ) rfl h₁ h₂, ha, pl_smul,
      pl_comp hL gam j _ rfl hχ h₁ h₄, pl_comp hL e g _ hge he rfl h₄]
  rw [pl_ofSec io, pl_ofSec k, eth, pl_ofSec g] at hF
  obtain ⟨q₁, q₂⟩ := hy F g _ rfl (j a) _ hF
  obtain ⟨p₁, z, c, p₂, p₃⟩ := hval ϖ hϖ F v hv m hm (by simpa using hu.map io) h3 _
    (Over.homMk (spMap k) h₃ : Over.mk (spMap g ≫ x₀) ⟶ Over.mk (spMap io ≫ χ)) (sp_comp _ _)
  obtain ⟨u, hu'⟩ := hun a (val_eq_zero v (j a) (fun i => g (y i)) (fun i => (hA _).1.1 (hy₁ i))
    (hy₂.imp fun i hi => (hA _).2 hi) (fun i => (q₁ i).elim fun z hz => p₁ z _ hz)
    ((q₂ z c p₂).elim fun i hi => ⟨i, (congrArg v hi).symm.trans p₃⟩))
  have hb : pl (algebraMap W (FractionRing W)) (x' := jK W ≫ χ) rfl (fnR χ u⁻¹.val • SecM.ofSec t.G σ) =
      pl gam hχ (SecM.ofSec t.G θ) := by
    rw [pl_smul, ha, smul_smul, ← map_mul, ← hu', ← map_mul, u.inv_mul, map_one, map_one, one_smul]
  exact ⟨SecM.toSec _ (fnR χ u⁻¹.val • SecM.ofSec t.G σ), GlobalTheory.T.generatingSection_finite_ext_normal_domain_isBasis S t.G t.PP.L hL W W' io hi hf χ _
    (isGenSec_unit io rfl u hgen) ⟨_, hθ.smul_pull hL gam hχ isUnit_one⟩
    (fun h0 => hθ.pl_ne_zero gam hχ (hb.symm.trans h0)), hb⟩

theorem exists_unif (hU : GlobalTheory.LN.UDvrSt) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R₁ : Type} [CommRing R₁] [IsDomain R₁]
    {g : PowerSeries O' →+* R₁} {y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c} (hT : GlobalTheory.LN.TraitData Y a g y₁)
    {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W) (ψ : R₁ →+* W)
    (gam : FractionRing R₁ →+* FractionRing W) (hg : ∀ r, gam (algebraMap R₁ _ r) = algebraMap W _ (ψ r))
    (χ : Sp W ⟶ Y.X) (hχ : spMap gam ≫ y₁ ≫ Y.j = jK W ≫ χ) :
    (∃ (t₁ : SAB H (Sp W)) (_ : SABMap t₁ Y.t χ), GlobalTheory.LN.PolAt t₁ (jK W)) ∧
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W')
      (io : W →+* W'), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ ∃ (t' : SAB H (Sp W'))
      (_ : SABMap t' Y.t (spMap io ≫ χ)), Nonempty (PELUnif (maximalIdeal W') t') := by
  obtain ⟨t₁, ⟨m₁⟩⟩ := GlobalTheory.ArcData.exists_sab χ Y.t
  have hp₁ := GlobalTheory.ArcData.polAt_of_point Y m₁ (jK W) (spMap gam ≫ y₁) ((Category.assoc _ _ _).trans hχ)
  have T := hT.2 W hW ψ gam hg χ hχ
  refine ⟨⟨t₁, m₁, hp₁⟩, ?_⟩
  by_cases hu : IsUnit (ψ (g PowerSeries.X))
  · have e₀ : spMap (RingHom.id W) ≫ χ = χ := (congrArg (· ≫ χ) (Spec.map_id _)).trans (Category.id_comp _)
    exact ⟨W, inferInstance, inferInstance, inferInstance, RingHom.id W, hW, fun _ _ h => h, RingHom.Finite.id W, t₁,
      e₀.symm ▸ m₁, GlobalTheory.T.nonempty_uniformisation_trait_in_abelianLocus hU E H _ Y.t W hW χ t₁ m₁ hp₁ (T.1 hu)⟩
  · obtain ⟨W', _, _, _, io, hW', hi, hf, t', m', P, -⟩ := T.2 hu
    exact ⟨W', _, _, _, io, hW', hi, hf, t', m', ⟨P⟩⟩

set_option maxHeartbeats 800000 in

theorem main : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → GlobalTheory.LN.TraitData Y a g y₁ → ThetaInt Y g y₁ → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) ∧ ∃ θ, GlobalTheory.LN.IsFrame Y.t.G Y.t.PP.L 1 ((spMap h' ≫ y₁) ≫ Y.j) (fun _ : Fin 1 => θ) := by
  intro hV _ hU _ _ _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hϖ R₁ _ _ g y₁ hg hfin hn hT ⟨o, ⟨φ, hp, hw, _⟩, hθ⟩
  have hL := Y.t.PP.isLB
  obtain ⟨n, hn₁, hn₂, hn₃⟩ := exists_prime hϖ
  have h3 : 3 ≤ n ^ 1 := by
    have := hn₁.two_le
    obtain ⟨k, rfl⟩ := hn₂
    rw [pow_one]
    omega
  obtain ⟨v, hv, hint⟩ := hθ n 1 hn₁ hn₂ hn₃ le_rfl
  have : IsNoetherianRing O' := by
    rcases hϖ with h | h
    · letI := h.1.toField; infer_instance
    · have := h.1; infer_instance
  have : IsNoetherianRing R₁ := by
    letI := g.toAlgebra
    have : Module.Finite (PowerSeries O') R₁ := hfin
    exact IsNoetherianRing.of_finite (PowerSeries O') R₁
  have : CharZero (PowerSeries O') := (RingHom.charZero_iff (PowerSeries.C_injective (R := O'))).1 ‹_›
  have : CharZero R₁ := (RingHom.charZero_iff hg).1 ‹_›
  have := o.charZero
  have hw₀ : LBIso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ) := Y.m.lin.imp fun _ h => h.1
  have hw' : LBIso o.P.L (Y.t.PP.L.pull (φ ≫ Y.m.φ)) :=
    LBIso.trans o.P.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) (LB.isLB_pull hL _) hw
      (LBIso.chartPull (Geo.Tor.chartPullPull _ φ φ rfl) (chartPullSame _ _ _ _ φ fun _ => rfl) hw₀)
  obtain ⟨th, hth, hy⟩ := GlobalTheory.T.exists_generator_thetaConstants_over_algClosedExtensions hV.1.1 hV.1.2.1 _ Y.t.G Y.t.PP.L Y.t.PP.rig hL Y.t.PP.rigGen _ _ o.P _
    (hp.comp Y.m.cart) hw' (n ^ 1) hn₂.pow _ _ v (o.I.onto _ (by positivity)) hv
  obtain ⟨e₁, he₁⟩ := GlobalTheory.T.exists_universal_section_basis_polarised_fibre hV.1.2.1 _ _ Y.t.G Y.t.PP.L hL (objPolAV Y.oF) Y.j Y.m.φ Y.m.cart hw₀ _ y₁ _ rfl
  have hx₀ : spMap (algebraMap (FractionRing R₁) (AlgebraicClosure (FractionRing R₁))) ≫ y₁ ≫ Y.j =
      (spMap (algebraMap _ _) ≫ y₁) ≫ Y.j := (Category.assoc _ _ _).symm
  obtain ⟨s, hs⟩ := he₁.ex _ hx₀ (SecM.ofSec _ th)
  have hs₀ : s ≠ 0 := he₁.ne_zero _ hx₀ hth hs
  obtain ⟨R₂, _, _, h, h', e, i₁, i₂, i₃, hh, heh, ⟨s₂, rfl⟩, hext⟩ := GlobalTheory.T.exists_integrally_closed_extension_of_adjoin R₁ s
  have hx₂ : spMap h' ≫ y₁ ≫ Y.j = (spMap h' ≫ y₁) ≫ Y.j := (Category.assoc _ _ _).symm
  have he : spMap e ≫ (spMap h' ≫ y₁) ≫ Y.j = (spMap (algebraMap (FractionRing R₁) _) ≫ y₁) ≫ Y.j := by
    rw [← heh, sp_comp]; simp only [Category.assoc]
  have hb := he₁.smul_pull hL h' hx₂ (a := s₂) (IsUnit.mk0 _ fun h0 => hs₀ (by rw [h0, map_zero]))
  have eth : pl e he (fnR ((spMap h' ≫ y₁) ≫ Y.j) s₂ • pl h' hx₂ (SecM.ofSec _ e₁)) = SecM.ofSec _ th := by
    rw [pl_smul, pl_comp hL h' e _ heh hx₂ he hx₀]
    exact hs.symm
  obtain ⟨θ, hb, eth⟩ : ∃ θ, UnivBasis Y.t.G Y.t.PP.L ((spMap h' ≫ y₁) ≫ Y.j) θ ∧
      pl e he (SecM.ofSec _ θ) = SecM.ofSec _ th := ⟨_, hb, (congrArg (pl e he) (ofSec_toSec _)).trans eth⟩
  refine ⟨R₂, inferInstance, inferInstance, h, h', i₁, i₂, i₃, hh, θ, fun W _ _ _ hW ψ gam hgam χ hχ => ?_⟩
  have hχ' : spMap (gam.comp h') ≫ y₁ ≫ Y.j = jK W ≫ χ := by rw [sp_comp, Category.assoc, hx₂, hχ]
  obtain ⟨⟨t₁, m₁, hp₁⟩, W', _, _, _, io, hW', hi, hf, t', m', ⟨P⟩⟩ := exists_unif hU Y hT hW (ψ.comp h) (gam.comp h')
    (fun r => (congrArg gam (hh r)).trans (hgam _)) χ hχ'
  have hint' : ∀ A : ValuationSubring (AlgebraicClosure (FractionRing R₁)), (∀ r : R₁, e (h' (algebraMap R₁ _ r)) ∈ A) →
      (∀ i, v i ∈ A) ∧ ∃ i, A.valuation (v i) = 1 := fun A hA =>
    (hint A fun r => (congrArg (· ∈ A) (RingHom.congr_fun heh (algebraMap R₁ _ r))).mp (hA r)).imp_right fun h => h.1
  have hu : IsUnit ((n ^ 1 : ℕ) : W) := by
    have := hn₃.map (ψ.comp (h.comp (g.comp (PowerSeries.C (R := O')))))
    rwa [map_natCast, ← pow_one n] at this
  have hg' : ∀ r : R₁, ∃ w, gam (h' (algebraMap R₁ _ r)) = algebraMap W _ w :=
    fun r => ⟨_, (congrArg gam (hh r)).trans (hgam _)⟩
  obtain ⟨b', hb₁, hb₂⟩ := basis_at_trait hV Y.t e he hb hext eth hn₂.pow h3 v hy
    (fun r : R₁ => h' (algebraMap R₁ _ r)) hint' hW hW' io hi hf hu gam hg' χ hχ m₁ hp₁ m' P
  exact ⟨fun _ => b', hb₁, fun _ => ⟨SecM.toSec _ (pl gam hχ (SecM.ofSec _ θ)), lin_of_pl hL gam hχ _ (ofSec_toSec _).symm,
    lin_of_pl hL (algebraMap W _) rfl _ (hb₂.trans (ofSec_toSec _).symm)⟩⟩

end GlobalTheory.Ex.OneGen
end
