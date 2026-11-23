import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPhiRelSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecExpandsAtOfIntegralFamily
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PhiSpecialises
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanGenerateValuationRingsStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaSpecialise

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar GlobalTheory.ThetaBaseChange

set_option maxHeartbeats 1600000 in

theorem exists_families (hL : Laws) (hT : DVR.TwistBaseChangeStatement) {R R' : Type} [CommRing R] [IsDomain R]
    [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'} (hR : AdmBase R I) (φ : R →+* R') (D : DegData R I)
    (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) {S : Type} [CommRing S] [IsDomain S] [ValuationRing S]
    (σ : R →+* S) {F : Type} [Field F] [Algebra (FractionRing R) F] (g : S →+* F) (hg : Function.Injective g)
    (ρ : TF (R := R) F ⟶ Over.mk (specOf σ)) (hρ : ρ.left = specOf g) {F' : Type} [Field F']
    [Algebra (FractionRing R') F'] (π : S →+* F') (hπl : IsLocalHom π)
    (hπ : ∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r)))
    (hτ' : specOf π ≫ specOf σ = (jFK (R := R') F' ≫ jK R') ≫ specOf φ)
    (k : ℕ) (hk : 1 ≤ k) (gp : GtPt D.toPre (Over.mk (specOf σ))) (p₀ : QkPt D.toPre F k) (p₁ : QkPt D'.toPre F' k)
    (h₁ : GtPt.IsPullF F ρ.left gp p₀.g) (h₂ : p₁.y = hD.xe.symm p₀.y)
    (h₃ : p₁.g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = specOf π ≫ gp.b.left)
    (h₄ : ∀ χ, PMaps hD.w (DegPre.gtφ D'.toPre F' p₁.g.b χ)
      (DegPre.gtφT D.toPre (Over.mk (specOf σ)) gp.b (hD.xe χ)) DegPre.gtε (p₁.g.s χ) (gp.s (hD.xe χ)) (specOf π)) :
    ∃ (n : ℕ) (F₀ : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α)
      (f' : Fin n → ∀ α, D'.toPre.SecB k α) (s : Fin n → Fam D.toPre F k) (s' : Fin n → Fam D'.toPre F' k)
      (c : Fin n → Fin n → S)
      (ν : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₀.g.b) (DegPre.lineε k)))
      (ν' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F' p₁.g.b) (DegPre.lineε k))),
      ν.IsGen ∧ ν'.IsGen ∧
      (∀ i α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F₀ i).s α)
        (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧
      (∀ i x, PSec hD.w (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k)
        (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) (f' i x) (f i (hD.xe x))) ∧
      (∀ i α, IsPull (DegPre.prB D.toPre F).left ((s i).s α) (f i α)) ∧
      (∀ i α, IsPull (DegPre.prB D'.toPre F').left ((s' i).s α) (f' i α)) ∧
      Submodule.span F' (Set.range s') = ⊤ ∧
      ∀ i, PhiRel D.toPre F k p₀ ν (s i) (∑ l, g (c i l) • s l) ∧
        PhiRel D'.toPre F' k p₁ ν' (s' i) (∑ l, π (c i l) • s' l) := by
  have hG := hL.globalFns
  have hM := D.toPre.P.isLB
  obtain ⟨n, F₀, f, F₁, f', hf, hspan, hgen⟩ := GlobalTheory.T.exists_integral_families_span_generate_valuationRings hL.polBaseChange hG hT R R' I hR φ D D'.toPre hD k hk
  obtain ⟨Θ, hΘ₁, hΘ₂, -⟩ := exists_psi (pull_grp hD) (T := TF (R := R') F') (T₀ := Over.mk (specOf σ)) (specOf π) hτ'
  obtain ⟨ν, ν', hν, hν', hΦ⟩ := GlobalTheory.phi_specialises hG R R' I I' φ D D' hD S σ F g hg ρ hρ F' π hπl hπ Θ hΘ₁.w hΘ₂
    k hk gp p₀ p₁ h₁ h₂ h₃ h₄
  obtain ⟨πB, hπB⟩ : ∃ πB : (Over.mk (specOf σ) ⊗ D.toPre.P.A).left ⟶ Spec (CommRingCat.of S),
    πB = (fst (Over.mk (specOf σ)) D.toPre.P.A).left := ⟨_, rfl⟩
  have pb₀ : IsPullback (snd (Over.mk (specOf σ)) D.toPre.P.A).left πB D.toPre.P.A.hom
      (Spec.map (CommRingCat.ofHom σ)) := by rw [hπB]; exact (IsPullback.of_hasPullback _ _).flip
  have r₂ : (ρ ▷ D.toPre.P.A).left ≫ (snd (Over.mk (specOf σ)) D.toPre.P.A).left = (DegPre.prB D.toPre F).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have pb : IsPullback (ρ ▷ D.toPre.P.A).left (famBase D.toPre F) πB (Spec.map (CommRingCat.ofHom g)) := by
    refine IsPullback.of_right ?_ ?_ pb₀
    · have e : Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom σ) = (TF (R := R) F).hom :=
        (congrArg (· ≫ specOf σ) hρ).symm.trans (Over.w ρ)
      rw [r₂, e]
      exact (IsPullback.of_hasPullback _ _).flip
    · rw [hπB]
      exact (congrArg (fun q => q.left) (whiskerRight_fst ρ D.toPre.P.A)).trans
        (congrArg ((fst (TF (R := R) F) D.toPre.P.A).left ≫ ·) hρ)
  have : Flat πB := by
    have := D.toPre.P.isAb.smooth
    exact MorphismProperty.of_isPullback (P := @Flat) pb₀ inferInstance
  have c₁ : ∀ α κ, DegPre.famφ D.toPre F α κ = (ρ ▷ D.toPre.P.A).left ≫
      (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α κ := fun α κ => by
    rw [← Category.assoc, r₂, famφ_prB]
  have c₂ : ∀ x κ, DegPre.famφ D'.toPre F' x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) =
      Θ ≫ (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB (hD.xe x) κ := fun x κ => by
    rw [← Category.assoc Θ, hΘ₂, famφ_prB, Category.assoc, ExpGTrans.famφB_pull hD x κ]
    exact (Category.assoc _ _ _).symm
  let s : Fin n → Fam D.toPre F k := fun i => famPull D.toPre (FractionRing R) F hG k (F₀ i)
  let s' : Fin n → Fam D'.toPre F' k := fun i => famPull D'.toPre (FractionRing R') F' hG k (F₁ i)
  have hs : ∀ i α, IsPull (DegPre.prB D.toPre F).left ((s i).s α) (f i α) := fun i α =>
    isPull_famPull D.toPre F hG (F₀ i) α (f i α) ((hf i).1 α)
  have hs' : ∀ i α, IsPull (DegPre.prB D'.toPre F').left ((s' i).s α) (f' i α) := fun i α =>
    isPull_famPull D'.toPre F' hG (F₁ i) α (f' i α) ((hf i).2.1 α)
  obtain ⟨b, hb⟩ : ∃ b : Fin n → ∀ α, SecOver πB (LB.LinComb D.toPre.P.L
      (fun κ => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α κ) (DegPre.famε k)),
      ∀ i α, IsPull (snd (Over.mk (specOf σ)) D.toPre.P.A).left (b i α) (f i α) :=
    ⟨fun i α => pullOver D.toPre.P.L _ pb₀.w (fun _ => rfl) (f i α), fun i α => isPull_pullOver _ _ _⟩
  have b₁ : ∀ i α, GeneratorPullback.SecScal D.toPre.P.L _ _ ((s i).s α) _ _ (b i α) (ρ ▷ D.toPre.P.A).left 1 := fun i α =>
    (secScal_one_iff hM).2 fun y J hJ => by
      rw [(hb i α).sval _ hJ, (hs i α).sval _ hJ, Category.assoc, r₂]
  have b₂ : ∀ i x, PSec hD.w (DegPre.famφ D'.toPre F' x) _ (DegPre.famε k) Θ ((s' i).s x) (b i (hD.xe x)) :=
    fun i x => (psec_iff_of_isPull (c₂ x) (hb i (hD.xe x)) hΘ₂).2 (PSec.pull_left ((hf i).2.2 x) (hs' i x))
  choose s₂ s₂' b₀ q₁ q₂ q₃ q₄ using fun i => hΦ (s i) (s' i) (b i) (b₁ i) (b₂ i)
  choose c hc using fun i => hgen S σ F g hg ρ hρ F' π hπl hπ (s₂ i) ⟨b₀ i, q₃ i⟩
  let b' : Fin n → ∀ α, SecOver πB (LB.LinComb D.toPre.P.L
      (fun κ => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α κ) (DegPre.famε k)) := b₀
  have hc' : ∀ i α, famProj D.toPre F k α (s₂ i) = ∑ l, g (c i l) • famProj D.toPre F k α (s l) := fun i α =>
    (secLin_iff (π' := famBase D.toPre F) hM (famProj D.toPre F k α (s₂ i)) (fun l => f l α) _ (fun l => g (c i l))
      (fun l => famProj D.toPre F k α (s l)) (fun l y J hJ => (hs l α).sval _ hJ)).1 (hc i α)
  have e₁ : ∀ i, s₂ i = ∑ l, g (c i l) • s l := fun i => fam_ext fun α j => congrArg (fun q => LB.Sec.f q j)
    ((hc' i α).trans (by simp only [map_sum, map_smul]) : famProj D.toPre F k α (s₂ i) =
      famProj D.toPre F k α (∑ l, g (c i l) • s l))
  have e₂ : ∀ i α, b' i α = ∑ l, c i l • b l α := fun i α => by
    refine sub_eq_zero.1 (sec_indep pb (DegPre.famε k) (c₁ α) (n := 1) (fun _ => 1) (fun a ha i => ?_)
      (fun _ => b' i α - ∑ l, c i l • b l α) ?_ 0)
    · rw [Fin.sum_univ_one, _root_.mul_one] at ha
      rw [Subsingleton.elim i 0]; exact hg (ha.trans (map_zero _).symm)
    · rw [Fin.sum_univ_one, one_smul, map_sub, map_sum, sub_eq_zero]
      refine (eq_pullOver_of_secScal hM pb.w (c₁ α) (q₃ i α)).trans
        ((hc' i α).trans (Finset.sum_congr rfl fun l _ => ?_))
      rw [map_smulₛₗ]
      exact congrArg (fun q : FamTerm D.toPre F k α => g (c i l) • q)
        (eq_pullOver_of_secScal hM pb.w (c₁ α) (b₁ l α)).symm
  have e₃ : ∀ i, s₂' i = ∑ l, π (c i l) • s' l := fun i => fam_ext fun x j => by
    obtain ⟨mv, hmv⟩ := exists_moveMap (π := πB) (π' := famBase D'.toPre F') (fS := π) (ε := DegPre.famε k) hM
      D'.toPre.P.isLB hD.w_gen (c₂ x) (by rw [hπB]; exact hΘ₁.w)
    refine congrArg (fun q => LB.Sec.f q j) (?_ : famProj D'.toPre F' k x (s₂' i) =
      famProj D'.toPre F' k x (∑ l, π (c i l) • s' l))
    refine ((hmv _ _).1 (q₄ i x)).symm.trans ((congrArg mv (e₂ i (hD.xe x))).trans ?_)
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smulₛₗ, map_smul, (hmv _ _).1 (b₂ l x)]
    rfl
  refine ⟨n, F₀, f, f', s, s', c, ν, ν', hν, hν', fun i => (hf i).1, fun i => (hf i).2.2, hs, hs', ?_,
    fun i => ⟨e₁ i ▸ q₁ i, e₃ i ▸ q₂ i⟩⟩
  refine eq_top_iff.2 ((isExtension_famPull D'.toPre (FractionRing R') F' hG hk).span.ge.trans
    (Submodule.span_le.2 ?_))
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ Submodule.span (FractionRing R') (Set.range F₁) := hspan ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  rw [map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.ThetaSpecialise

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar GlobalTheory.ThetaBaseChange
  GlobalTheory.ThetaSpecialise in
set_option maxHeartbeats 1600000 in

theorem qkToAkU_specialises : Laws → Laws2 → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R') (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → IsSemiAbelian G → ∀ (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] (σ : R →+* S) (F : Type) [Field F] [Algebra (FractionRing R) F] (ιF : S →+* F), Function.Injective ιF → ∀ (ρ : TF (R := R) F ⟶ (Over.mk (specOf σ))), ρ.left = specOf ιF → ∀ (F' : Type) [Field F'] [Algebra (FractionRing R') F'] (π : S →+* F'), IsLocalHom π → (∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r))) → ∀ (k : ℕ), 1 ≤ k → ∀ (gp : GtPt D.toPre (Over.mk (specOf σ))) (p₀ : QkPt D.toPre F k) (p₁ : QkPt D'.toPre F' k), GtPt.IsPullF F ρ.left gp p₀.g → p₁.y = hD.xe.symm p₀.y → p₁.g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = specOf π ≫ gp.b.left → (∀ χ, Geo.Tor.PMaps hD.w (DegPre.gtφ D'.toPre F' p₁.g.b χ) (DegPre.gtφT D.toPre (Over.mk (specOf σ)) gp.b (hD.xe χ)) DegPre.gtε (p₁.g.s χ) (gp.s (hD.xe χ)) (specOf π)) → ∀ (xS : (Over.mk (specOf σ)) ⟶ G) (x : TFK (R := R) F ⟶ A.A) (x' : TFK (R := R') F' ⟶ A'.A), x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = ρ.left ≫ xS.left → x'.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf π ≫ xS.left → QkToAkU U.toUnifPre F k p₀ x → QkToAkU U'.toUnifPre F' k p₁ x' := by
  intro hL _ hT R R' _ _ _ _ I I' hR _ φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU hsa S _ _ _ σ F _ _ g hg ρ hρ F' _ _
    π hπl hπ k hk gp p₀ p₁ h₁ h₂ h₃ h₄ xS x x' hx hx' H w' hw'
  have hG := hL.globalFns
  obtain ⟨wL, hwL, -, -, hlev⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨hx1, H⟩ := H w hw
  have gA := grp_generic U.toUnifPre
  have gΨ : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have gA' := (grp_generic U'.toUnifPre).comp gΨ
  have hτ : specOf g ≫ specOf σ = jFK (R := R) F ≫ jK R := (congrArg (· ≫ specOf σ) hρ).symm.trans (Over.w ρ)
  have hτ' : specOf π ≫ specOf σ = jFK (R := R') F' ≫ jK R' ≫ specOf φ := by
    rw [jFK, jK, specOf, specOf, specOf, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext hπ : π.comp σ =
      ((algebraMap (FractionRing R') F').comp (algebraMap R' (FractionRing R'))).comp φ)
  have hx₁ : specOf g ≫ xS.left = x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) :=
    (congrArg (· ≫ xS.left) hρ).symm.trans hx.symm
  have hx₂ : specOf π ≫ xS.left = x'.left ≫ (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R')) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ) := hx'.symm.trans (by simp only [Category.assoc])
  have := U.separated
  have hxS : xS ^ k = 1 := pow_eq_one_of_injective hg ρ hρ xS (by
    have e : pushHom gA (TFK (R := R) F) x = ρ ≫ xS := Over.OverMorphism.ext hx
    exact (congrArg (· ^ k) e).symm.trans ((map_pow _ _ _).symm.trans ((congrArg _ hx1).trans (map_one _))))
  have hx'1 : x' ^ k = 1 := by
    let o : Over.mk (jFK (R := R') F' ≫ jK R' ≫ specOf φ) ⟶ Over.mk (specOf σ) := Over.homMk (specOf π) hτ'
    exact pow_eq_one_of_push rfl gA' (x := o ≫ xS) hx₂.symm
      ((map_pow (preHom o) xS k).symm.trans ((congrArg _ hxS).trans (map_one _)))
  refine ⟨hx'1, fun θ' hθ' => ?_⟩
  obtain ⟨θS, rfl⟩ := TorsionThetaLocal.exists_theta_of_pow_eq_one _ G U.LG U.cubG S (specOf σ) k xS hxS
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have n₂ : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  obtain ⟨u, hu, hu₁⟩ := exists_unpull hw _ n₁ rfl
  obtain ⟨u', hu', hu₁'⟩ := exists_unpull hw' _ n₂ rfl
  obtain ⟨v', T⟩ := exists_comp U'.LG.isLB wL u' ((isGen_iff _).1 hwL) hu' U.LG.isLB A'.isLB
  have hv' := (isGen_iff _).2 (T.pgen_comp U'.LG.isLB ((isGen_iff _).1 hwL) hu')
  obtain ⟨π₀, hπ₀⟩ : ∃ π₀ : (Over.mk (specOf σ) ⊗ G).left ⟶ Spec (CommRingCat.of S),
    π₀ = (fst (Over.mk (specOf σ)) G).left := ⟨_, rfl⟩
  obtain ⟨θ, mv, hθ, act, ps, ind⟩ := exists_side_map gA g hτ U.LG.isLB A.isLB u ((isGen_iff _).2 hu) k x θS hx₁
    π₀ hπ₀ (abelianBase A F) rfl
  obtain ⟨θ₀, mv', hθ₀, act', ps', -⟩ := exists_side_map gA' π hτ' U.LG.isLB A'.isLB v' hv' k x' θS hx₂
    π₀ hπ₀ (abelianBase A' F') rfl
  obtain ⟨aS, -, haS⟩ := exists_actMap U.LG.isLB θS (𝟙 _) π₀ (hπ₀.trans (Category.comp_id _).symm)
  obtain ⟨a', inj', ha'⟩ := exists_actMap A'.isLB θ₀ (𝟙 _) (abelianBase A' F') (Category.comp_id _).symm
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG U F hk w hw
  obtain ⟨e', he'⟩ := exists_linearEquiv_expandsF hG U' F' hk w' hw'
  obtain ⟨n, F₀, f, f', s, s', c, ν, ν', hν, hν', f₁, f₂, hs, hs', hspan, hc⟩ := exists_families hL hT hR φ D D' hD σ g hg
    ρ hρ π hπl hπ (hτ'.trans (Category.assoc _ _ _).symm) k hk gp p₀ p₁ h₁ h₂ h₃ h₄
  have := hsa.geomConnected
  have := hsa.quasiCompact
  choose τ hτE using fun i => exists_sec_expandsAt_of_integral_family R I hR D A G U.toUnifPre k
    (fun F => ((U.expand k hk).2 F).exists) (F₀ i) (f i) (f₁ i)
  have hΨ : ∀ _ : Fin 1, 𝟙 G'.left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) =
      (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ≫ 𝟙 G.left := fun _ =>
    (Category.id_comp _).trans (Category.comp_id _).symm
  choose τ' hτ₁ using fun i => (SecPull.existsUnique_secPull _ _ _ _ _ _ _ U.LG.isLB U'.LG.isLB wL hwL (Fin 1)
    (fun _ => 𝟙 G'.left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)) _ hΨ (τ i)).exists
  have hτE' : ∀ i m, U'.ExpandsAt m k (τ' i) (f' i) := fun i m => by
    obtain ⟨h, hh⟩ := hlev m
    exact expandsAt_transport R R' I I' D D' A A' G G' U.toUnifPre U'.toUnifPre _ hD.w hD.xe _ wL hD.w_gen hwL
      (ExpGTrans.famφB_pull hD) m m k h hh (τ i) (τ' i) (f i) (f' i) (hτ₁ i) (f₂ i) (hτE i m)
  obtain ⟨b, hb⟩ : ∃ b : Fin n → SecOver π₀ (LPow G U.LG.L (k : ℤ) (Over.mk (specOf σ))),
      ∀ i, IsPull (φ₁ := fun _ : Fin 1 => (snd (Over.mk (specOf σ)) G).left) (snd (Over.mk (specOf σ)) G).left
        (b i) (τ i) := by
    have pw : (snd (Over.mk (specOf σ)) G).left ≫ G.hom = π₀ ≫ Spec.map (CommRingCat.ofHom σ) := by
      rw [hπ₀]; exact (Over.w (snd (Over.mk (specOf σ)) G)).trans (Over.w (fst (Over.mk (specOf σ)) G)).symm
    exact ⟨fun i => pullOver U.LG.L _ pw (fun _ => (Category.comp_id _).symm) (τ i),
      fun i => isPull_pullOver pw (fun _ => (Category.comp_id _).symm) (τ i)⟩
  have E : ∀ i, e (mv (b i)) = s i := fun i => (he _ _).1 (expandsF_of_integral U.toUnifPre F hu₁ (τ i) (f i) (hτE i)
    (s i) (fun α y J hJ => (hs i α).sval _ hJ) _ (ps _ _ (hb i)))
  have E' : ∀ i, e' (mv' (b i)) = s' i := fun i => (he' _ _).1 (expandsF_of_integral U'.toUnifPre F' hu₁' (τ' i) (f' i)
    (hτE' i) (s' i) (fun α y J hJ => (hs' i α).sval _ hJ) _ (PSec.cancel T U.LG.isLB
      (fun _ => (Category.comp_id _).symm) (hτ₁ i) (by rw [Category.assoc (snd (TFK (R := R') F') A'.A).left]; exact ps' _ _ (hb i))))
  obtain ⟨ν₀, hν₀, Hν⟩ := H θ hθ
  obtain ⟨l, -, hl⟩ := TorsionImage.exists_smul_of_phiVal p₀ ν ν₀ hν hν₀
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG R' I' D' F' k hk p₁ ν' hν'
  have m : ∀ i, mv (aS (b i)) = l • mv (∑ j, c i j • b j) := fun i => e.injective (by
    rw [map_smul, map_sum, map_sum]
    simp only [map_smulₛₗ, RingHom.id_apply, E]
    exact hl _ _ _ ((phiRel_iff hG p₀ ν hν _ _).1 (hc i).1) ((phiRel_iff hG p₀ ν₀ hν₀ _ _).1
      (Hν _ _ _ _ ((he _ _).2 (E i)) ((he _ _).2 rfl) (act _ _ ((haS _ _).2 rfl)))))
  have m₁ : ∀ i, mv' (aS (b i)) = a' (mv' (b i)) := fun i => ((ha' _ _).1 (act' _ _ ((haS _ _).2 rfl))).symm
  have m₂ : ∀ i, e' (mv' (∑ j, c i j • b j)) = Φ' (s' i) := fun i => by
    rw [map_sum, map_sum]
    simp only [map_smulₛₗ, RingHom.id_apply, E']
    exact (hΦ' _ _).1 (hc i).2
  obtain ⟨l', hl', m'⟩ : ∃ l' : F', l' ≠ 0 ∧ ∀ i, e' (a' (mv' (b i))) = l' • Φ' (s' i) := by
    by_cases z : ∀ i, s' i = 0
    · refine ⟨1, one_ne_zero, fun i => ?_⟩
      rw [e'.map_eq_zero_iff.1 ((E' i).trans (z i)), z i, map_zero, map_zero, map_zero, smul_zero]
    · obtain ⟨i, hi⟩ := not_forall.1 z
      have := U.smooth
      obtain ⟨l', hl', m'⟩ := exists_ratio hg mv mv' (ind inferInstance) _ _ l m
        ⟨i, fun h => hi (by rw [← E', inj' ((m₁ i).symm.trans (h.trans (map_zero _).symm)), map_zero])⟩
        ⟨i, fun h => hi (eq_zero_of_phiVal p₁ ν' _ ((phiRel_iff hG p₁ ν' hν' _ _).1 ((hΦ' _ _).2
          (by rw [← m₂, h, map_zero]))))⟩
      exact ⟨l', hl', fun i => by rw [← m₁, m', map_smul, m₂]⟩
  have key : e'.toLinearMap ∘ₗ a' ∘ₗ e'.symm.toLinearMap = l' • Φ' := LinearMap.ext_on_range hspan fun i => by
    refine Eq.trans ?_ (m' i)
    rw [← E']
    exact congrArg (fun q => e' (a' q)) (e'.symm_apply_apply _)
  obtain ⟨d, hd, hd'⟩ := exists_act_ratio hG A'.isAb A'.isLB θ₀ θ' (hθ₀.trans hθ'.symm) (abelianBase A' F') rfl
  obtain ⟨ν₁, hν₁, Hν₁⟩ := ProdTorsion.exists_phiRel_smul hG p₁ ν' hν' (d * l') (mul_ne_zero hd hl')
  refine ⟨ν₁, hν₁, fun t t₂ q q₂ X X₂ hA => ?_⟩
  obtain rfl := (he' _ _).1 X
  obtain rfl := (he' _ _).1 X₂
  have y : e' t₂ = (d * l') • Φ' (e' t) := by
    refine (congrArg e' (hd' t _ t₂ ((ha' _ _).2 rfl) hA)).trans ((map_smul e' _ _).trans ?_)
    rw [mul_smul]
    exact congrArg (d • ·) ((congrArg (fun q => e' (a' q)) (e'.symm_apply_apply _)).symm.trans
      (LinearMap.congr_fun key (e' t)))
  rw [y]
  exact Hν₁ _ _ ((hΦ' _ _).2 rfl)

end GlobalTheory
