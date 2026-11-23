import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegUniqueAndComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackFractionFieldFiniteLocalExt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPrimitiveRootUnitOnIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionOfDimOneNormal
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ClosureDescent

open GlobalTheory.ThetaDescent

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

def Fib {K K' : Type} [CommRing K] [CommRing K'] (A' : PolAV (Sp K')) (A : PolAV (Sp K)) (f : K →+* K')
    (a : A'.A.left ⟶ A.A.left) : Prop :=
  IsGrpPullback A'.A A.A (spMap f) a ∧ LBIso A'.L (A.L.pull a)

section

variable {K K' K'' : Type} [CommRing K] [CommRing K'] [CommRing K'']

theorem Fib.exists (A : PolAV (Sp K)) (f : K →+* K') : ∃ (A' : PolAV (Sp K')) (a : A'.A.left ⟶ A.A.left), Fib A' A f a :=
  GlobalTheory.ArcDataDescent.exists_polPull GlobalTheory.firstFiveLaws.1.polBaseChange (spMap f) A

theorem Fib.comp {A : PolAV (Sp K)} {A' : PolAV (Sp K')} {A'' : PolAV (Sp K'')} {f : K →+* K'} {g : K' →+* K''}
    {a : A'.A.left ⟶ A.A.left} {b : A''.A.left ⟶ A'.A.left} (hb : Fib A'' A' g b) (ha : Fib A' A f a)
    {h : K →+* K''} (e : g.comp f = h) : Fib A'' A h (b ≫ a) := by
  subst e
  exact ⟨(hb.1.comp ha.1).congr (spMap_comp' f g).symm rfl,
    LBIso.trans A''.isLB (pull_isLB A'.isLB _) (pull_isLB A.isLB _) hb.2 (GlobalTheory.ArcDataDescent.lbIso_pull ha.2 b rfl)⟩

theorem Fib.cancel {A : PolAV (Sp K)} {A' : PolAV (Sp K')} {A'' : PolAV (Sp K'')} {f : K →+* K'} (g : K' →+* K'')
    {a : A'.A.left ⟶ A.A.left} {c : A''.A.left ⟶ A.A.left} {h : K →+* K''} (ha : Fib A' A f a) (hc : Fib A'' A h c)
    (e : g.comp f = h) : ∃ b, b ≫ a = c ∧ Fib A'' A' g b := by
  subst e
  have w : c ≫ A.A.hom = (A''.A.hom ≫ spMap g) ≫ spMap f := by
    rw [hc.1.1.w, spMap_comp', Category.assoc]
  have e₁ := ha.1.1.lift_fst _ _ w
  refine ⟨ha.1.1.lift _ _ w, e₁, IsGrpPullback.cancel ha.1 (hc.1.congr (spMap_comp' f g) e₁.symm) (ha.1.1.lift_snd _ _ w), ?_⟩
  exact LBIso.trans A''.isLB (pull_isLB A.isLB _) (pull_isLB A'.isLB _) hc.2
    (GlobalTheory.ArcDataDescent.lbIso_pull ha.2 _ e₁.symm).symm

end

theorem finite_gen {L Ω : Type} [Field L] [Field Ω] (β : L →+* Ω) (hβ : β.IsIntegral) (s : Finset Ω) :
    (β.codRestrict _ (mem_gen β s)).Finite := by
  letI := β.toAlgebra
  have : FiniteDimensional L (IntermediateField.adjoin L (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => hβ x
  exact this

theorem exists_fib_gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) (t : PolAV (Sp K))
    (ht : letI := t.isAb.comm; GlobalTheory.ZH.HypS t.A t.L) :
    ∃ (s : Finset K) (Q : PolAV (Sp (gen β s))) (ψ : t.A.left ⟶ Q.A.left), Fib t Q (gen β s).subtype ψ ∧
      (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) := by
  obtain ⟨w, wd, hw, hwd, hsum, hpol, hadj⟩ := ht
  classical
  let act : Bool → (t.A ⟶ t.A) := fun j => cond j w wd
  obtain ⟨s₀, H₀⟩ := GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield K (gen β ∅) t.A.left t.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple t.ample)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ (gen β s₀) (gen_mono β (Finset.empty_subset _)) (subset_gen β le_rfl)
  have : IsProper p₀ := isProper_of_isProjOver hp₀
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := GlobalTheory.grpObj_descends_to_large_subfield K (gen β s₀) (Over.mk p₀) t.A φ sq
  obtain ⟨s₂, H₂⟩ := GlobalTheory.T.exists_lineBundle_descent_to_subfield K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ t.L t.isLB sq
  obtain ⟨s₃, H₃⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ X₀ p₀ Bool (fun j => (act j).left ≫ φ) sq
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, Over.w])
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃
  have h : gen β s₀ ≤ gen β s := gen_mono β (fun x hx => by simp [s, hx])
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp (gen β s)) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : t.A.left ⟶ A₁.left := sq₁.lift φ (t.A.hom ≫ spMap (gen β s).subtype)
    (by rw [Category.assoc, spMap_subtype h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = t.A.hom ≫ spMap (gen β s).subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hL⟩ := H₂ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨f₁, hf₁⟩ := H₃ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  let act₁ : Bool → (A₁ ⟶ A₁) := fun j =>
    Over.homMk (sq₁.lift (f₁ j) A₁.hom (by rw [(hf₁ j).2, sq₁.w])) (sq₁.lift_snd _ _ _)
  have hact : ∀ j, (act j).left ≫ ψ = ψ ≫ (act₁ j).left := fun j => by
    have e₁ : (act₁ j).left ≫ φ₁ = f₁ j := sq₁.lift_fst _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, e₁, (hf₁ j).1]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hψ₂]
  obtain ⟨hab, hdim⟩ := GlobalTheory.T.abelian_scheme_descent_smooth_dimension _ K (gen β s).subtype A₁ t.A ψ hG t.isAb
  obtain ⟨hr, hs, hk⟩ := GlobalTheory.T.rigidified_symmetric_kernelTrivial_descend_fieldExt _ K (gen β s).subtype A₁ t.A ψ L₁ t.L hab hG hL₁ t.isLB hL
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension _ K (gen β s).subtype A₁ t.A ψ L₁ t.L hab hG hL₁ t.isLB hL
    t.ample
  refine ⟨s, ⟨A₁, hab, t.g, hdim _ t.smoothDim, L₁, hL₁, hr t.rigid, hs t.sym, hamp, hk t.ktriv⟩, ψ, ⟨hG, hL⟩, ?_⟩
  have := t.isAb.comm
  have := hab.comm
  exact GlobalTheory.SymLevelDescent.hypS_descend (gen β s).subtype hab hG hL₁ t.isLB hL (hact true).symm (hact false).symm hw hwd
    hsum hpol hadj

theorem exists_map_desc {Ω : Type} [Field Ω] (M₀ : Subfield Ω) (P₁ P₂ : PolAV (Sp M₀)) (B : PolAV (Sp Ω))
    {b₁ : B.A.left ⟶ P₁.A.left} {b₂ : B.A.left ⟶ P₂.A.left} (h₁ : Fib B P₁ M₀.subtype b₁) (h₂ : Fib B P₂ M₀.subtype b₂) :
    ∃ s : Finset Ω, ∀ (M : Subfield Ω) (h : M₀ ≤ M), (s : Set Ω) ⊆ M → ∀ (Q₁ Q₂ : PolAV (Sp M))
      (q₁ : Q₁.A.left ⟶ P₁.A.left) (q₂ : Q₂.A.left ⟶ P₂.A.left) (c₁ : B.A.left ⟶ Q₁.A.left) (c₂ : B.A.left ⟶ Q₂.A.left),
      Fib Q₁ P₁ (Subfield.inclusion h) q₁ → Fib Q₂ P₂ (Subfield.inclusion h) q₂ → c₁ ≫ q₁ = b₁ → c₂ ≫ q₂ = b₂ →
      Fib B Q₁ M.subtype c₁ → Fib B Q₂ M.subtype c₂ → ∃ u : Q₁.A ⟶ Q₂.A, c₁ ≫ u.left = c₂ := by
  have := P₁.isAb.proper
  have := P₂.isAb.smooth
  obtain ⟨s, H⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield Ω M₀ P₁.A.left B.A.left P₁.A.hom B.A.hom b₁ P₂.A.left P₂.A.hom PUnit (fun _ => b₂) h₁.1.1
    (fun _ => h₂.1.1.w.trans h₁.1.1.w.symm)
  refine ⟨s, fun M h hs Q₁ Q₂ q₁ q₂ c₁ c₂ k₁ k₂ e₁ e₂ l₁ l₂ => ?_⟩
  obtain ⟨f, hf⟩ := H M h hs Q₁.A.left Q₁.A.hom q₁ c₁ k₁.1.1 e₁ l₁.1.1.w
  have w := (hf PUnit.unit).2.trans k₁.1.1.w
  refine ⟨Over.homMk (k₂.1.1.lift _ _ w) (k₂.1.1.lift_snd _ _ w), k₂.1.1.hom_ext ?_ ?_⟩
  · exact (Category.assoc _ _ _).trans
      ((congrArg (c₁ ≫ ·) (k₂.1.1.lift_fst _ _ w)).trans ((hf PUnit.unit).1.trans e₂.symm))
  · exact (Category.assoc _ _ _).trans
      ((congrArg (c₁ ≫ ·) (k₂.1.1.lift_snd _ _ w)).trans (l₁.1.1.w.trans l₂.1.1.w.symm))

theorem exists_common_fib {Ω : Type} [Field Ω] (M₀ : Subfield Ω) (P₁ P₂ : PolAV (Sp M₀)) (B : PolAV (Sp Ω))
    {b₁ : B.A.left ⟶ P₁.A.left} {b₂ : B.A.left ⟶ P₂.A.left} (h₁ : Fib B P₁ M₀.subtype b₁) (h₂ : Fib B P₂ M₀.subtype b₂) :
    ∃ s : Finset Ω, ∀ (M : Subfield Ω) (h : M₀ ≤ M), (s : Set Ω) ⊆ M → ∃ (Q : PolAV (Sp M))
      (q₁ : Q.A.left ⟶ P₁.A.left) (q₂ : Q.A.left ⟶ P₂.A.left),
      Fib Q P₁ (Subfield.inclusion h) q₁ ∧ Fib Q P₂ (Subfield.inclusion h) q₂ := by
  classical
  obtain ⟨s, H⟩ := exists_map_desc M₀ P₁ P₂ B h₁ h₂
  obtain ⟨s', H'⟩ := exists_map_desc M₀ P₂ P₁ B h₂ h₁
  refine ⟨s ∪ s', fun M h hs => ?_⟩
  rw [Finset.coe_union, Set.union_subset_iff] at hs
  obtain ⟨Q₁, q₁, k₁⟩ := Fib.exists P₁ (Subfield.inclusion h)
  obtain ⟨Q₂, q₂, k₂⟩ := Fib.exists P₂ (Subfield.inclusion h)
  obtain ⟨c₁, e₁, l₁⟩ := Fib.cancel M.subtype k₁ h₁ rfl
  obtain ⟨c₂, e₂, l₂⟩ := Fib.cancel M.subtype k₂ h₂ rfl
  obtain ⟨u, hu⟩ := H M h hs.1 Q₁ Q₂ q₁ q₂ c₁ c₂ k₁ k₂ e₁ e₂ l₁ l₂
  obtain ⟨v, hv⟩ := H' M h hs.2 Q₂ Q₁ q₂ q₁ c₂ c₁ k₂ k₁ e₂ e₁ l₂ l₁
  have F := GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff M Ω M.subtype
  haveI : Epi c₁ := (F.1 _ _ _ _ c₁ l₁.1.1).1
  haveI : Epi c₂ := (F.1 _ _ _ _ c₂ l₂.1.1).1
  let e : Q₁.A ≅ Q₂.A := ⟨u, v,
    Over.OverMorphism.ext (by rw [← cancel_epi c₁, Over.comp_left, ← Category.assoc, hu, hv, Over.id_left, Category.comp_id]),
    Over.OverMorphism.ext (by rw [← cancel_epi c₂, Over.comp_left, ← Category.assoc, hv, hu, Over.id_left, Category.comp_id])⟩
  haveI : IsMonHom e.hom := (F.2 _ _ _ _ c₁ c₂ u (𝟙 B.A) l₁.1 l₂.1 (hu.trans (Category.id_comp _).symm)).1 inferInstance
  have hid : spMap (RingHom.id M) = 𝟙 _ := Spec.map_id _
  have k : Fib Q₁ Q₂ (RingHom.id M) u.left := by
    refine ⟨(isGrpPullback_of_iso e).congr hid.symm rfl, ?_⟩
    refine (GlobalTheory.lb_gen_iso_descend_field M Ω M.subtype _ _ Q₁.A.hom B.A.hom c₁ Q₁.isAb.smooth Q₁.isAb.proper
      Q₁.isAb.geomConnected l₁.1.1).2 _ _ Q₁.isLB (pull_isLB Q₂.isLB _) ?_
    exact LBIso.trans (pull_isLB Q₁.isLB _) B.isLB (pull_isLB (pull_isLB Q₂.isLB _) _) l₁.2.symm
      (LBIso.trans B.isLB (pull_isLB Q₂.isLB _) (pull_isLB (pull_isLB Q₂.isLB _) _) l₂.2
        (GlobalTheory.ArcDataDescent.lbIso_pull_pull Q₂.isLB _ _ hu.symm).symm)
  exact ⟨Q₁, q₁, u.left ≫ q₂, k₁, k.comp k₂ rfl⟩

section

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

theorem exists_unif_fib {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I')
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) (ga : FractionRing R →+* FractionRing R')
    (hga : ga.comp (algebraMap R _) = (algebraMap R' _).comp g) :
    ∃ (D' : DegData R' I') (_ : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
      (_ : Unif I' D' A' ((Over.pullback (specOf g)).obj G)) (a : A'.A.left ⟶ A.A.left), Fib A' A ga a := by
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have sq : spMap ga ≫ jK R = jK R' ≫ spMap g :=
    (spMap_comp' _ _).symm.trans ((congrArg spMap hga).trans (spMap_comp' _ _))
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hL.polBaseChange _ _ (spMap ga) A
  have gpA : IsGrpPullback A'.A A.A (spMap ga) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap ga ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) =
      pullback.fst G.hom (spMap g) := Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (Geo.Tor.chartPullPull A'.L _ _ rfl) (Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec ((Over.pullback (specOf g)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) :=
    ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
      rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := h5.psiOnExists R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, -, -⟩ := h4.unifBaseChange R R' I I' hR hR' g hI D A G hG U Wo hψ hgen
    ((Over.pullback (specOf g)).obj G) (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB)
    (fun p => hr p.1 p.2)
  exact ⟨D', hD, A', U', gA, gpA, LBIso.symm tA⟩

end

theorem cDvr_of_finExt {R R' : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] {ρ : R →+* R'} (hR : GlobalTheory.LN.CDvr R) (h : FinExt ρ) : GlobalTheory.LN.CDvr R' := by
  obtain ⟨hdvr, -, h0⟩ := hR
  obtain ⟨⟨hn, -, hic, hc⟩, hinj, hfin⟩ := h
  letI := ρ.toAlgebra
  haveI : Algebra.IsIntegral R R' := ⟨fun x => (RingHom.IsIntegral.of_finite hfin) x⟩
  have hd : ringKrullDim R' = 1 := by
    rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one R
  exact ⟨GlobalTheory.CdvrExt.isDVR_of_ringKrullDim_eq_one hd, hc, charZero_of_injective_ringHom hinj⟩

theorem exists_extend {R R₁ F Ω : Type} [CommRing R] [CommRing R₁] [IsDomain R₁] [Field F] [Field Ω] [IsAlgClosed Ω]
    {ρ : R →+* R₁} (hρ : ρ.Finite) (i : R →+* F) (τ : F →+* FractionRing R₁)
    (hτ : τ.comp i = (algebraMap R₁ _).comp ρ) (j : F →+* Ω) : ∃ j₁ : FractionRing R₁ →+* Ω, j₁.comp τ = j := by
  letI := τ.toAlgebra
  letI := j.toAlgebra
  have hint : ∀ r : R₁, IsIntegral F (algebraMap R₁ (FractionRing R₁) r) := fun r => by
    obtain ⟨p, hp, e⟩ := RingHom.IsIntegral.of_finite hρ r
    refine ⟨p.map i, hp.map i, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.algebraMap_toAlgebra, hτ, ← Polynomial.hom_eval₂, e, map_zero]
  haveI : Algebra.IsAlgebraic F (FractionRing R₁) := ⟨fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R₁) x
    rw [div_eq_mul_inv]
    exact (hint a).isAlgebraic.mul (hint b).isAlgebraic.inv⟩
  let l : FractionRing R₁ →ₐ[F] Ω := IsAlgClosed.lift
  exact ⟨l.toRingHom, RingHom.ext fun x => l.commutes x⟩

theorem exists_range_le_gen {R R₁ L Ω : Type} [CommRing R] [CommRing R₁] [IsDomain R₁] [CommRing L] [Field Ω]
    {ρ : R →+* R₁} (hρ : ρ.Finite) (β : L →+* Ω) (χ : R →+* L) (j : FractionRing R₁ →+* Ω)
    (h : ∀ r, j (algebraMap R₁ _ (ρ r)) = β (χ r)) : ∃ s : Finset Ω, ∀ x, j x ∈ gen β s := by
  classical
  letI := ρ.toAlgebra
  obtain ⟨t, ht⟩ := (show Module.Finite R R₁ from hρ).fg_top
  refine ⟨t.image fun r => j (algebraMap R₁ _ r), fun x => ?_⟩
  have key : ∀ r : R₁, j (algebraMap R₁ _ r) ∈ gen β (t.image fun r => j (algebraMap R₁ _ r)) := fun r => by
    have hr : r ∈ Submodule.span R (t : Set R₁) := ht ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem x hx => exact subset_gen β le_rfl (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx))
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, map_mul, RingHom.algebraMap_toAlgebra, h]
      exact mul_mem (mem_gen β _ _) hx
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R₁) x
  rw [map_div₀]
  exact div_mem (key a) (key b)

theorem exists_restrict {R R₁ W : Type} [CommRing R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁]
    [CommRing W] [IsDomain W] [IsLocalRing W] [IsIntegrallyClosed W] {ρ : R →+* R₁} (hρ : ρ.Finite) (χ : R →+* W)
    [IsLocalHom χ] (ga : FractionRing R₁ →+* FractionRing W) (h : ∀ r, ga (algebraMap R₁ _ (ρ r)) = algebraMap W _ (χ r)) :
    ∃ φ : R₁ →+* W, (∀ r, ga (algebraMap R₁ _ r) = algebraMap W _ (φ r)) ∧ φ.comp ρ = χ ∧ Function.Injective φ ∧
      IsLocalHom φ := by
  have inj := IsFractionRing.injective W (FractionRing W)
  have hint : ∀ r : R₁, ∃ y, algebraMap W (FractionRing W) y = ga (algebraMap R₁ _ r) := fun r => by
    obtain ⟨p, hp, e⟩ := RingHom.IsIntegral.of_finite hρ r
    refine IsIntegrallyClosed.isIntegral_iff.1 ⟨p.map χ, hp.map χ, ?_⟩
    have e' : (algebraMap W (FractionRing W)).comp χ = (ga.comp (algebraMap R₁ _)).comp ρ := RingHom.ext fun r => (h r).symm
    rw [Polynomial.eval₂_map, e', ← RingHom.comp_apply, ← Polynomial.hom_eval₂, e, map_zero]
  choose f hf using hint
  let φ : R₁ →+* W :=
    { toFun := f
      map_one' := inj (by simp only [hf, map_one])
      map_mul' := fun a b => inj (by simp only [hf, map_mul])
      map_zero' := inj (by simp only [hf, map_zero])
      map_add' := fun a b => inj (by simp only [hf, map_add]) }
  have hc : φ.comp ρ = χ := RingHom.ext fun r => inj ((hf _).trans (h r))
  refine ⟨φ, fun r => (hf r).symm, hc, fun a b e => ?_, ?_⟩
  · exact IsFractionRing.injective R₁ (FractionRing R₁)
      (ga.injective ((hf a).symm.trans ((congrArg (algebraMap W _) e).trans (hf b))))
  · have hm : ((maximalIdeal W).comap φ).IsMaximal := by
      refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ (RingHom.IsIntegral.of_finite hρ) _ ?_
      rw [Ideal.comap_comap, hc, IsLocalRing.maximalIdeal_comap]
      infer_instance
    exact ((IsLocalRing.local_hom_TFAE φ).out 4 0).1 (IsLocalRing.eq_maximalIdeal hm)

theorem exists_fib_finite {K Ω : Type} [Field K] [Field Ω] (α : K →+* Ω) (hα : α.IsIntegral) (t : PolAV (Sp Ω))
    (ht : letI := t.isAb.comm; GlobalTheory.ZH.HypS t.A t.L) :
    ∃ (F : Type) (_ : Field F) (i : K →+* F) (j : F →+* Ω) (Q : PolAV (Sp F)) (ψ : t.A.left ⟶ Q.A.left),
      i.Finite ∧ (∀ x, j (i x) = α x) ∧ Fib t Q j ψ ∧ (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) := by
  obtain ⟨s, Q, ψ, hQ, hQS⟩ := exists_fib_gen α t ht
  exact ⟨gen α s, inferInstance, _, _, Q, ψ, finite_gen α hα s, fun _ => rfl, hQ, hQS⟩

theorem exists_common_fib_finite {K L Ω : Type} [Field K] [Field L] [Field Ω] (β : L →+* Ω) (hβ : β.IsIntegral)
    (j : K →+* Ω) {s₀ : Finset Ω} (hs₀ : ∀ x, j x ∈ gen β s₀) {A : PolAV (Sp K)} {A' : PolAV (Sp L)} {B : PolAV (Sp Ω)}
    {b : B.A.left ⟶ A.A.left} {b' : B.A.left ⟶ A'.A.left} (hb : Fib B A j b) (hb' : Fib B A' β b') :
    ∃ (M : Type) (_ : Field M) (i : L →+* M) (k : K →+* M) (m : M →+* Ω) (C : PolAV (Sp M)) (c : C.A.left ⟶ A.A.left)
      (c' : C.A.left ⟶ A'.A.left), i.Finite ∧ (∀ x, m (i x) = β x) ∧ (∀ x, m (k x) = j x) ∧ Fib C A k c ∧ Fib C A' i c' := by
  classical
  obtain ⟨P₁, p₁, hP₁⟩ := Fib.exists A (j.codRestrict _ hs₀)
  obtain ⟨P₂, p₂, hP₂⟩ := Fib.exists A' (β.codRestrict _ (mem_gen β s₀))
  obtain ⟨b₁, -, hb₁⟩ := Fib.cancel (gen β s₀).subtype hP₁ hb (RingHom.ext fun _ => rfl)
  obtain ⟨b₂, -, hb₂⟩ := Fib.cancel (gen β s₀).subtype hP₂ hb' (RingHom.ext fun _ => rfl)
  obtain ⟨s₁, H⟩ := exists_common_fib _ P₁ P₂ B hb₁ hb₂
  have h : gen β s₀ ≤ gen β (s₀ ∪ s₁) := gen_mono β Finset.subset_union_left
  obtain ⟨C, c₁, c₂, hc₁, hc₂⟩ := H _ h (subset_gen β Finset.subset_union_right)
  exact ⟨gen β (s₀ ∪ s₁), inferInstance, β.codRestrict _ (mem_gen β _), j.codRestrict _ fun x => h (hs₀ x),
    (gen β (s₀ ∪ s₁)).subtype, C, _, _, finite_gen β hβ _, fun _ => rfl, fun _ => rfl,
    hc₁.comp hP₁ (RingHom.ext fun _ => rfl), hc₂.comp hP₂ (RingHom.ext fun _ => rfl)⟩

theorem exists_uniTrait_of_fib {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R)
    (D : DegData R (maximalIdeal R)) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W)
    (φ : R →+* W) (hφ : Function.Injective φ) [IsLocalHom φ] (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W))
    [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))) (hD' : IsPullDeg φ D.toPre D'.toPre)
    (hG' : IsSemiAbelian G') (U' : Unif (maximalIdeal W) D' A' G') {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] [IsAlgClosed Ω]
    (α : FractionRing R →+* Ω₀) (hα : α.IsIntegral) (β : FractionRing W →+* Ω) (hβ : β.IsIntegral)
    (A₀ : PolAV (Sp Ω₀)) (e₀ : Ω₀ →+* Ω) (he₀ : ∀ r, e₀ (α (algebraMap R _ r)) = β (algebraMap W _ (φ r)))
    (hS : letI := A₀.isAb.comm; GlobalTheory.ZH.HypS A₀.A A₀.L) (hI : GeomIso A₀ A' e₀ β) :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁)
      (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ ∧
      Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ UniTrait D₁.toPre A := by
  classical
  obtain ⟨B, b₀, b', g₀, l₀, g', l'⟩ := hI
  have hB₀ : Fib B A₀ e₀ b₀ := ⟨g₀, l₀⟩
  have hB' : Fib B A' β b' := ⟨g', l'⟩
  obtain ⟨F, _, i₀, j₀, Q, ψ, hi₀, hj₀, hQ, hQS⟩ := exists_fib_finite α hα A₀ hS
  obtain ⟨R₁, _, _, _, ρ, τ, hρ, hρl, hτ⟩ := GlobalTheory.CommonCover.exists_cover_field R hR F i₀ hi₀
  obtain ⟨A, a, hA⟩ := Fib.exists Q τ
  obtain ⟨D₁, ⟨hD₁⟩⟩ := GlobalTheory.MumPull.exists_pull R R₁ ρ hρ.2.1 hρl D
  refine ⟨R₁, _, _, _, ρ, D₁, A, hρ, ⟨hD₁⟩, ?_, ?_⟩
  · exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ Q.A A.A _ a Q.L A.L Q.isLB A.isLB hA.1 hA.2 hQS
  obtain ⟨j₁, hj₁⟩ := exists_extend hρ.2.2 _ τ hτ (e₀.comp j₀)
  obtain ⟨b, -, hb⟩ := Fib.cancel j₁ hA (hB₀.comp hQ rfl) hj₁
  have hjρ : ∀ r, j₁ (algebraMap R₁ _ (ρ r)) = β (algebraMap W _ (φ r)) := fun r =>
    (congrArg j₁ (DFunLike.congr_fun hτ r)).symm.trans
      ((DFunLike.congr_fun hj₁ _).trans ((congrArg e₀ (hj₀ _)).trans (he₀ r)))
  obtain ⟨s₀, hs₀⟩ := exists_range_le_gen hρ.2.2 β ((algebraMap W _).comp φ) j₁ hjρ
  obtain ⟨M, _, i, k, m, C, c₁, c₂, hi, hmi, hmk, hc₁, hc₂⟩ := exists_common_fib_finite β hβ j₁ hs₀ hb hB'
  have := hW.1
  have hWb : Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩, hW.2.2⟩
  obtain ⟨W₁, _, _, _, io, σ, hio, hiol, hσ⟩ := GlobalTheory.CommonCover.exists_cover_field W hWb M i hi
  obtain ⟨C₁, c, hc⟩ := Fib.exists C σ
  have f₁ : Fib C₁ A (σ.comp k) _ := hc.comp hc₁ rfl
  have f₂ : Fib C₁ A' (σ.comp i) _ := hc.comp hc₂ rfl
  obtain ⟨D₂, hD₂, A₂, U₂, a₂, hA₂⟩ := exists_unif_fib hWb.1 hio.1 io hio.2.1 (map_maximalIdeal_le io) hG' U' (σ.comp i)
    ((RingHom.comp_assoc _ _ _).trans hσ)
  obtain ⟨d, -, hd⟩ := Fib.cancel (RingHom.id _) f₂ hA₂ (RingHom.id_comp _)
  haveI := hio.1.2.2.1
  obtain ⟨φ₁, hφ₁, hcomp, hinj, hl⟩ := exists_restrict hρ.2.2 (io.comp φ) (σ.comp k) fun r =>
    (congrArg σ (m.injective ((hmk _).trans ((hjρ r).trans (hmi _).symm)))).trans (DFunLike.congr_fun hσ (φ r))
  obtain ⟨q⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hφ hio.2.1 hD' hD₂
  rw [← hcomp] at q
  obtain ⟨q₁⟩ := GlobalTheory.PullDegUniq.nonempty_isPullDeg_cancel hρ.2.1 hinj hD₁ q
  have f₃ : Fib A₂ A (σ.comp k) _ := hd.comp f₁ (RingHom.id_comp _)
  exact ⟨W₁, _, _, _, φ₁, _, inferInstance, inferInstance, D₂, A₂, U₂, q₁, _, cDvr_of_finExt hW hio, hinj, hl,
    IsSemiAbelian.pullback _ G' hG', σ.comp k, hφ₁, f₃.1, f₃.2⟩

theorem exists_uniTrait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∀ (A₀ : PolAV (Sp (Kb R))) (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) → (letI := A₀.isAb.comm; GlobalTheory.ZH.HypS A₀.A A₀.L) → GeomIso A₀ A' e₀ (algebraMap (FractionRing W) (Kb W)) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ UniTrait D₁.toPre A := by
  intro R _ _ _ hR D n _ _ _ W _ _ _ hW φ hφ hloc D' G' _ _ A' ⟨hD'⟩ hG' ⟨U'⟩ _ A₀ e₀ he₀ hS hI
  exact exists_uniTrait_of_fib hR D hW φ hφ D' G' A' hD' hG' U' _
    (fun x => Algebra.IsIntegral.isIntegral (R := FractionRing R) x) _
    (fun x => Algebra.IsIntegral.isIntegral (R := FractionRing W) x) A₀ e₀ he₀ hS hI

end GlobalTheory.Mum.ClosureDescent
