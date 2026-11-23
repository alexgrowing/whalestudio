import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPAdicArcBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowerSeriesArcAbelianLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataIsoOfTwoWitnesses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericIsoOfUniformisationsIsoData
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ArcUniqueGlobal

open GlobalTheory.WitnessData GlobalTheory.ArcUnique

set_option maxHeartbeats 1000000 in

theorem witness_data_iso' : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F)
    (Y : Model Xo c β) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : O →+* O') (a : ArcIn D l β O' b)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R),
    AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ χ' : Sp R ⟶ Y.X) (W : ArcWit Y a I f u χ)
    (W' : ArcWit Y a I f u χ'), ∃ hD : IsPullDeg (RingHom.id R) W.P.D.toPre W'.P.D.toPre, (∀ y, hD.xe (W'.e y) = W.e y) ∧ (∀ x, (letI := H.starRing; W'.P.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (W.P.oD.onB.act x))) ∧ ∃ w' : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ)), W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ ∧ HEq W'.w w' ∧ Tri W.w hD.w w' := by
  intro _ _ h5 E _ _ _ H D l Xo c O _ β Y O' _ _ _ b a R _ _ _ _ I f u hR _ hf χ χ' W W'
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  obtain ⟨s1', s2', s3', s4', s5', s6'⟩ := W'.spec
  obtain ⟨Wo, hWo, ⟨ψW⟩⟩ := h5.psiOnExists R I hR W.P.D
  let F := AlgebraicClosure (FractionRing R)
  have hi : Function.Injective (((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))).comp f) :=
    ((algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)).comp hf
  letI : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hi).toAlgebra
  have hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
      algebraMap (FractionRing R) F (algebraMap R _ (f x)) := fun x => IsFractionRing.lift_algebraMap hi x
  obtain ⟨hD, h₁, w', h₂, h₃, h₄⟩ := exists_isPullDeg_pre W.he W'.he W.e.toAddEquiv W'.e.toAddEquiv s1 s1' s2 s2'
    s3 s3' s5 s5' F _ (s6 F _ hF rfl).1 (s6' F _ hF rfl).1 hWo ψW
  exact ⟨hD, h₁, fun x => comm_of_pullback (specOf_id R) s1.1 hD.e.hom h₂ (s4 x) (s4' x), w', h₂, h₃, h₄⟩

set_option maxHeartbeats 1000000 in

theorem eq_of_hasArcData' : Laws → Laws2 → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (hm : Mono (spMap β)) (Y : Model Xo c β) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ χ' : Sp R ⟶ Y.X) (y y' : Sp (FractionRing R) ⟶ Xo.XF c), y ≫ Y.j = jK R ≫ χ → y' ≫ Y.j = jK R ≫ χ' → χ ≫ Y.s = spMap f ≫ spMap b → χ' ≫ Y.s = spMap f ≫ spMap b → Y.HasArcData a I f u χ → Y.HasArcData a I f u χ' → χ = χ' := by
  intro h1 h2 h3 h4 h5 E _ _ _ H D l Xo c O _ β hm Y O' _ _ _ b a R _ _ _ _ I f u hR hI hf χ χ' y y' hy hy' hs hs' hχ hχ'
  let _ := H.starRing
  obtain ⟨W⟩ := (Y.hasArcData_iff a I f u χ).1 hχ
  obtain ⟨W'⟩ := (Y.hasArcData_iff a I f u χ').1 hχ'
  obtain ⟨hD, he, hact, w', hφ, hw, T⟩ := witness_data_iso' h1 h2 h5 E H D l Xo c O β Y O' b a R I f u hR hI hf χ χ' W W'
  obtain ⟨ψ, mψ, hL, hQ, hO⟩ := GlobalTheory.exists_generic_iso_of_unif h1 h2 R I hR hI W.P.D W'.P.D W.P.A W'.P.A W.t.G W'.t.G W.t.semi W'.t.semi
    W.P.U W'.P.U hD
  have hψ := hO (𝓞 E) W.P.oD W'.P.oD W.P.oA W'.P.oA _ _ W.P.lin W'.P.lin (fun x z => by
    obtain ⟨z, rfl⟩ := W'.e.surjective z
    rw [← map_smul, he, he, map_smul]) hact
  obtain ⟨φ, eφ, fφ⟩ := exists_isFibre W hy
  obtain ⟨φ', eφ', fφ'⟩ := exists_isFibre W' hy'
  have fψ := fφ.precomp W.P.A.isLB W'.P.A.isLB (act' := W'.P.oA.act) (isGrpPullback_of_iso ψ)
    (fun x => by rw [← Over.comp_left, hψ, Over.comp_left]) hL
  rw [Category.id_comp] at fψ
  let F := AlgebraicClosure (FractionRing R)
  let g : O' →+* F := ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))).comp f
  have hinj : Function.Injective ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)
  have hg : Function.Injective g := hinj.comp hf
  letI : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hg).toAlgebra
  have hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
      algebraMap (FractionRing R) F (algebraMap R _ (f x)) :=
    fun x => IsFractionRing.lift_algebraMap (K := FractionRing O') hg x
  let j : Sp F ⟶ Sp (FractionRing R) := jFK (R := R) F
  have lev : ∀ (k : ℕ) (p₀ : QkPt a.D₀ (FractionRing O') k) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G), 1 ≤ k → k ∣ l.M' →
      ((k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Y.oF.etaA v) ∨
        (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
          HEq p₀ (a.eta v) ∧ σ = Y.oF.eta v)) →
      ∀ x : Over.mk j ⟶ W'.P.A.A, x.left ≫ ψ.hom.left ≫ φ = j ≫ y ≫ σ.left → x.left ≫ φ' = j ≫ y' ≫ σ.left := by
    intro k p₀ σ hk hd hσ x hx
    obtain ⟨q₀, hq₀, -⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing O') F) (by ext; rfl) p₀
    obtain ⟨q, hq⟩ := MatchRigid.exists_transport (match_of_wit W) hF rfl h1.globalFns hd q₀
    obtain ⟨q', hq'⟩ := MatchRigid.exists_transport (match_of_wit W') hF rfl h1.globalFns hd q₀
    have t₁ := (W.spec.2.2.2.2.2 F _ hF rfl).2 (j ≫ y) (by rw [Category.assoc, hy]) k p₀ σ hσ q₀ q (x ≫ ψ.hom) hq₀
      hq.1 hq.2 (by
        rw [← eφ, Over.comp_left, Category.assoc, Category.assoc]
        exact (by simpa only [Category.assoc] using congrArg (· ≫ Y.m.φ) hx))
    have t₂ := (hQ F k hk q q' x (by rw [hq'.1, hq.1, ← he, AddEquiv.symm_apply_apply])
      (isPullGtF_of_transport W W' hD he w' hφ hw T hq.2 hq'.2)).2 t₁
    have w₀ : (j ≫ y' ≫ σ.left) ≫ Y.oF.t.G.hom = j ≫ y' := by
      rw [Category.assoc, Category.assoc, Over.w]
      exact congrArg _ (Category.comp_id _)
    let x' : Over.mk j ⟶ W'.P.A.A := Over.homMk (fφ'.1.1.lift (j ≫ y' ≫ σ.left) j w₀) (fφ'.1.1.lift_snd _ _ _)
    have hx' : x'.left ≫ φ' = j ≫ y' ≫ σ.left := fφ'.1.1.lift_fst _ _ _
    have t₃ := (W'.spec.2.2.2.2.2 F _ hF rfl).2 (j ≫ y') (by rw [Category.assoc, hy']) k p₀ σ hσ q₀ q' x' hq₀
      hq'.1 hq'.2 (by
        rw [← eφ']
        exact (by simpa only [Category.assoc] using congrArg (· ≫ Y.m.φ) hx'))
    obtain ⟨τ, hτ, -⟩ := TorsionIso.torsion_eq ⟨h1, h2, h3, h4, h5⟩ R I hR W'.P.D W'.P.A W'.t.G W'.t.semi W'.P.U F k hk
    rw [((hτ _ _).1 t₂).trans ((hτ _ _).1 t₃).symm]
    exact hx'
  have sn : ∀ {z : Sp (FractionRing R) ⟶ Xo.XF c} {ξ : Sp R ⟶ Y.X}, z ≫ Y.j = jK R ≫ ξ →
      (z ≫ pullback.snd _ _) ≫ spMap β = jK R ≫ ξ ≫ Y.s := fun {z ξ} hz => by
    rw [← Y.jQ_over, Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc (jK R), ← hz, Model.j,
      Category.assoc, Category.assoc]
  have key : j ≫ y = j ≫ y' := points_eq Xo c Y.oF Y.m0 j W'.P.A.isLB fψ fφ'
    ((cancel_mono (spMap β)).1 (by rw [sn hy, sn hy', hs, hs']))
    (fun v => lev _ (a.etaA v) _ l.A_pos (Nat.dvd_lcm_right _ _) (Or.inl ⟨rfl, v, HEq.rfl, rfl⟩))
    (fun v hv => lev _ (a.eta v) _ (le_trans (by norm_num) l.three_le) (Nat.dvd_lcm_left _ _)
      (Or.inr ⟨rfl, v, hv, HEq.rfl, rfl⟩))
  have := ThetaDescent.isProper_of_isProjOver Y.proj
  have : IsDominant (j ≫ jK R) := by
    have e : j ≫ jK R = spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) :=
      (Spec.map_comp _ _).symm
    rw [e]
    exact ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 hinj).le.trans bot_le)⟩
  refine ext_of_isDominant_of_isSeparated Y.s (hs.trans hs'.symm) (j ≫ jK R) ?_
  rw [Category.assoc, Category.assoc, ← hy, ← hy', ← Category.assoc, key, Category.assoc]

theorem ringOfIntegers_injective (K : Type) [Field K] [NumberField K] {O' : Type} [CommRing O'] [IsDomain O']
    [CharZero O'] (b : 𝓞 K →+* O') : Function.Injective b := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hc : (RingHom.ker b).comap (algebraMap ℤ (𝓞 K)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hne hx (Algebra.IsIntegral.isIntegral x)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  have : b (algebraMap ℤ (𝓞 K) n) = 0 := hn
  rw [eq_intCast, map_intCast, Int.cast_eq_zero] at this
  exact hn0 this

set_option maxHeartbeats 1000000 in

theorem eq_of_hasArcData_global : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O']
    (b : 𝓞 c.F →+* O') (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f →
    ∀ χ χ' : Sp R ⟶ Z.X, Set.range (Out.jK R ≫ χ) ⊆ Set.range Z.j → Set.range (Out.jK R ≫ χ') ⊆ Set.range Z.j →
      χ ≫ Z.s = spMap f ≫ spMap b → χ' ≫ Z.s = spMap f ≫ spMap b → Z.HasArcData a I f u χ → Z.HasArcData a I f u χ' →
      χ = χ' := by
  intro E _ _ _ H D l Xo c Z O' _ _ _ b a R _ _ _ _ I f u hR hI hf χ χ' hr hr' hs hs' hχ hχ'
  haveI := c.fin
  haveI : NumberField c.F := ⟨⟩
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have hpre : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors _)
  have hm : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := inferInstance
  have hb := ringOfIntegers_injective c.F b
  have hinj : Function.Injective ((algebraMap R (FractionRing R)).comp (f.comp b)) :=
    (IsFractionRing.injective R (FractionRing R)).comp (hf.comp hb)
  let g : c.F →+* FractionRing R := IsFractionRing.lift (A := 𝓞 c.F) (K := c.F) hinj
  have hg : g.comp (algebraMap (𝓞 c.F) c.F) = (algebraMap R (FractionRing R)).comp (f.comp b) :=
    RingHom.ext fun v => IsFractionRing.lift_algebraMap (A := 𝓞 c.F) (K := c.F) hinj v
  have hpf : IsPreimmersion (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) := inferInstance
  have lift : ∀ ξ : Sp R ⟶ Z.X, Set.range (Out.jK R ≫ ξ) ⊆ Set.range Z.j →
      ξ ≫ Z.s = spMap f ≫ spMap b → ∃ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Z.j = Out.jK R ≫ ξ := by
    intro ξ hr hs
    have hsq : (Out.jK R ≫ ξ) ≫ Z.s = spMap g ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
      rw [Category.assoc, hs]
      simp only [Out.jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]
    let q := pullback.lift (Out.jK R ≫ ξ) (spMap g) hsq
    have hrange : Set.range q ⊆ Set.range Z.jQ := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨z, hz⟩ := hr ⟨x, rfl⟩
      refine ⟨z, (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
      exact hz
    haveI := Z.jQ_open
    refine ⟨IsOpenImmersion.lift Z.jQ q hrange, ?_⟩
    rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  obtain ⟨y, hy⟩ := lift χ hr hs
  obtain ⟨y', hy'⟩ := lift χ' hr' hs'
  exact eq_of_hasArcData' h1 h2 h3 h4 h5 E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) hm Z O' b a R I f u hR hI hf
    χ χ' y y' hy hy' hs hs' hχ hχ'

end GlobalTheory.ArcUniqueGlobal
