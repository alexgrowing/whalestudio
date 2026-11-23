import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstant
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.ThLocal
open GlobalTheory.ThetaPtMove GlobalTheory.ThetaPtExist

theorem sec_eq {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem exists_local : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x) (R₁ : Type) [CommRing R₁] [Algebra R R₁] [IsNoetherianRing R₁] (N : ℕ) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Odd m → IsUnit (m : R) → PolFib G L g x → (∀ a, q a ^ (m ^ 2) = 1) → ∀ p : Ideal R₁, p.IsPrime → ∃ f ∉ p, ∃ c : Fin N → Localization.Away f, ∀ (K : Type) [Field K] (j : Localization.Away f →+* K) (a : Fin N) (pt : Over.mk (spMap ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁)) ≫ x) ⟶ G), pt.left = spMap (j.comp (algebraMap R₁ (Localization.Away f))) ≫ (q a).left → ThG G L ρ m (SecAt.pull G L θ ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁))) pt (fn (j (c a))) := by
  intro S G _ _ L ρ hL hρ g m R _ _ x θ R₁ _ _ _ N q hm hmu hP hq p hp
  obtain ⟨P, α, -, hpb, w, hw⟩ := hP
  have hL₁ := P.isLB
  haveI := P.isAb.comm
  obtain ⟨ρ₁, hρ₁, hr⟩ := exists_rigidificationPullbackCompatibleIso hpb hw hL hL₁ hρ
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  obtain ⟨α₀, hα₀⟩ := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1 (Sp R) P m
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  let T : Over (Sp R) := Over.mk (spMap (algebraMap R R₁))
  let T₁ : Over S := Over.mk (spMap (algebraMap R R₁) ≫ x)
  have hτ₁ : 𝟙 T.left ≫ T₁.hom = T.hom ≫ x := Category.id_comp _
  choose y hy hym using fun a => exists_torsion_down hpb (𝟙 T.left) (T₀ := T₁) hτ₁ (q a) (hq a)
  let pt₀ : T.left := (⟨p, hp⟩ : PrimeSpectrum R₁)
  choose V hV U hU using fun a => (sym (Sp R) P (m ^ 2) hm.pow T (y a) (hym a)).1 pt₀
  have hO : IsOpen (⋂ a, ((V a : T.left.Opens) : Set T.left)) := isOpen_iInter_of_finite fun a => (V a).2
  obtain ⟨_, ⟨f, rfl⟩, hf, hfO⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show pt₀ ∈ ⋂ a, ((V a : T.left.Opens) : Set T.left) from Set.mem_iInter.2 hV) hO
  refine ⟨f, hf, ?_⟩
  let Lf := Localization.Away f
  let af : R₁ →+* Lf := algebraMap R₁ Lf
  let i_f : R →+* Lf := af.comp (algebraMap R R₁)
  let Tf : Over (Sp R) := Over.mk (spMap i_f)
  let β : Tf ⟶ T := Over.homMk (spMap af) (by
    show spMap af ≫ spMap (algebraMap R R₁) = spMap (af.comp (algebraMap R R₁))
    exact (spMap_comp _ _).symm)
  have hrange : ∀ a, Set.range (spMap af) ⊆ Set.range (V a).ι := by
    intro a
    rintro _ ⟨p', rfl⟩
    rw [Scheme.Opens.range_ι]
    exact Set.mem_iInter.1 (hfO ((PrimeSpectrum.localization_away_comap_range Lf f).le ⟨p', rfl⟩)) a
  have hsym : ∀ a, ∃ θ' : ThetaGrp P.A P.L ((m : ℤ) ^ 2) Tf,
      SymLift P.A P.L ((m : ℤ) ^ 2) (m ^ 2) (β ≫ y a) θ' := by
    intro a
    let u := IsOpenImmersion.lift (V a).ι (spMap af) (hrange a)
    have hu : u ≫ (V a).ι = spMap af := IsOpenImmersion.lift_fac _ _ _
    let r : Tf ⟶ overRes (V a) := Over.homMk u (by
      show u ≫ (V a).ι ≫ T.hom = Tf.hom
      rw [← Category.assoc, hu]
      exact Over.w β)
    obtain ⟨θ', h'⟩ := GlobalLift.exists_symLift_pull hL₁ r (hU a)
    have e : r ≫ overResι (V a) = β := Over.OverMorphism.ext hu
    rw [← Category.assoc, e] at h'
    rw [← Nat.cast_pow]
    exact ⟨θ', h'⟩
  let T₀ : Over S := Over.mk (spMap i_f ≫ x)
  have hτ : 𝟙 Tf.left ≫ T₀.hom = Tf.hom ≫ x := Category.id_comp _
  obtain ⟨th, hth⟩ := exists_secRel hpb (𝟙 Tf.left) (T₀ := T₀) hτ hw hL hL₁ (SecAt.pull G L θ i_f)
  have e₁ : (snd Tf P.A).left ≫ (mulA P.A m).left = (snd Tf P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨αf, hαf, -⟩ := exists_gen hL₁ (φ' := ![(snd Tf P.A).left, (snd Tf P.A ^ m).left]) (ε' := ![(m : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((m : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd Tf P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨τf, hτf, -⟩ := exists_gen hL₁ (φ' := fun _ : Fin 1 => (1 : Tf ⟶ P.A).left) (ε' := fun _ => (m : ℤ) ^ 2)
    (fun U _ f => by
      rw [Fintype.prod_unique, Fin.prod_univ_one]
      exact congrArg₂ (fun q n => f q ^ n) rfl (by simp))
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ₁ (toUnit Tf).left) (m ^ 2))
    (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ₁ _) _)
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL₁ (mulT P.A Tf m) (snd Tf P.A ^ m) (lift_snd _ _)
    ((m : ℤ) ^ 2) 1 αf hαf th
  choose Uf hUf using hsym
  choose s₂ hs₂ using fun a => ThetaPtExist.exists_isTwistPull hL₁ (translT P.A (Uf a).pt) (translPt P.A (Uf a).pt)
    (lift_snd _ _) ((m : ℤ) ^ 2) ((m : ℤ) ^ 2) (Uf a).φ (Uf a).isGen s₁
  choose wv hwv using fun a => ThetaPtExist.exists_isValueAt hL₁ (s₂ a) 1 τf hτf
  have hyf : ∀ a, (β ≫ y a) ^ (m ^ 2) = 1 := fun a => by rw [← MonObj.comp_pow, hym a, MonObj.comp_one]
  obtain ⟨e, he⟩ := exists_thG hL₁ hρ₁ m ((m : ℤ) ^ 2) (Nat.cast_pow m 2).symm hyf (th := th) (α := αf)
    hαf hτf hs₁ hUf hs₂ hwv
  refine ⟨fun a => (Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a), ?_⟩
  intro K _ j a pt hpt
  clear hUf hs₂ hwv hs₁ sym hU hV hfO hO cg neg hG hrange
  let ξ : T₀ ⟶ T₁ := Over.homMk (spMap af) (by
    show spMap af ≫ spMap (algebraMap R R₁) ≫ x = spMap (af.comp (algebraMap R R₁)) ≫ x
    rw [← Category.assoc, ← spMap_comp])
  have hx₀ : 𝟙 Tf.left ≫ (ξ ≫ q a).left = (β ≫ y a).left ≫ α := by
    have h := hy a
    rw [Category.id_comp] at h
    rw [Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, ← h]
    rfl
  have hn₀ : (ξ ≫ q a) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, hq a, MonObj.comp_one]
  have up := ThG.up hpb (T := Tf) (T₀ := T₀) (𝟙 Tf.left) hτ hw hL hL₁ hr hx₀ hn₀ hth (he a)
  let δ : Over.mk (spMap ((j.comp af).comp (algebraMap R R₁)) ≫ x) ⟶ T₀ := Over.homMk (spMap j) (by
    show spMap j ≫ spMap (af.comp (algebraMap R R₁)) ≫ x = spMap ((j.comp af).comp (algebraMap R R₁)) ≫ x
    rw [← Category.assoc, ← spMap_comp])
  have down := ThPull.thG_pull hL hρ δ up
  have ept : pt = δ ≫ ξ ≫ q a := by
    refine Over.OverMorphism.ext ?_
    rw [hpt, Over.comp_left, Over.comp_left, ← Category.assoc]
    exact congrArg (· ≫ (q a).left) (spMap_comp af j)
  have eθ : SecAt.pull G L θ ((j.comp af).comp (algebraMap R R₁)) = VVRank.pullS G _ δ (SecAt.pull G L θ i_f) := by
    unfold SecAt.pull
    rw [pullS_comp G hL]
    congr 1
    refine Over.OverMorphism.ext ?_
    exact spMap_comp i_f j
  have ec : δ.left.appTop.hom ((inv (𝟙 Tf.left)).appTop.hom ((e : Γ(Tf.left, ⊤)) * wv a)) =
      fn (j ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a))) := by
    have h1 : (inv (𝟙 Tf.left)).appTop.hom ((e : Γ(Tf.left, ⊤)) * wv a) =
        fn ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a)) := by
      simp only [IsIso.inv_id, Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply]
      exact ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom_inv_id_apply _).symm
    rw [h1]
    exact (congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a)))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm
  rw [ept, eθ, ← ec]
  exact down

end GlobalTheory.UMin.ThLocal
