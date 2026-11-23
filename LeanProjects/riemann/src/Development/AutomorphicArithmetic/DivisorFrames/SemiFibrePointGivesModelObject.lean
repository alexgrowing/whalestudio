import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AutomorphicArithmetic.DivisorFrames.LieLatticeGenerator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

namespace UpperTheory.FibObj

open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

private theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

private theorem dualMapR_comp_epsMul {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    (dualMapR f).comp (epsMul a) = (epsMul (f a)).comp (dualMapR f) := by
  apply RingHom.ext; intro x; ext <;> simp [dualMapR, epsMul, _root_.mul_comm]

private theorem epsMul_comp_alg {A : Type} [CommRing A] (a : A) :
    (epsMul a).comp (algebraMap A (DualNumber A)) = algebraMap A (DualNumber A) := by
  apply RingHom.ext; intro x; ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

private theorem epi_of_local {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (d : A →+* B)
    [IsLocalHom d] (hd : Function.Injective d) : Epi (spMap d) := by
  refine ⟨fun {X} a b h => ?_⟩
  obtain ⟨⟨x, f, hf⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.surjective a
  obtain ⟨⟨y, g, hg⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.surjective b
  have h1 : IsLocalHom (f ≫ CommRingCat.ofHom d).hom := by
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d f.hom
  have h2 : IsLocalHom (g ≫ CommRingCat.ofHom d).hom := by
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d g.hom
  have h3 : (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨x, _, h1⟩ =
      (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨y, _, h2⟩ := by
    simpa [SpecToEquivOfLocalRing] using h
  have h4 := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.injective h3
  obtain rfl : x = y := congrArg Sigma.fst h4
  have h5 : f ≫ CommRingCat.ofHom d = g ≫ CommRingCat.ofHom d :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj h4).2)
  obtain rfl : f = g := by
    ext s
    exact hd (congrArg (fun k => k.hom s) h5)
  rfl

private theorem epi_dualMapR {K L : Type} [Field K] [Field L] (φ : K →+* L) : Epi (spMap (dualMapR φ)) := by
  have : IsLocalHom (dualMapR φ) := ⟨fun a ha => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero] at ha ⊢
    intro h
    exact ha (by simp [dualMapR, h])⟩
  refine epi_of_local _ fun a b h => ?_
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  ext
  · exact φ.injective (by simpa [dualMapR] using h1)
  · exact φ.injective (by simpa [dualMapR] using h2)

private theorem epi_spMap_field {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  letI := f.toAlgebra
  haveI : Flat (spMap f) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (show Module.Flat K L from inferInstance)
  haveI : Surjective (spMap f) := ⟨fun z => ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

end UpperTheory.FibObj

open CategoryTheory.Limits ReciprocityTheory.ChartRestriction.G GlobalTheory.ShFam.Pad UpperTheory.FibObj GlobalTheory.CM in
private theorem fibobj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (Z : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (y : FlagPt Z Qb) (hy : y.y (IsLocalRing.closedPoint Qb) ∉ GlobalTheory.Toroidal.genBd Z)
    {K : Type} [Field K] [NumberField K] (ι : K →+* Qb) (jF : c.F →+* K) (hj : ι.comp jF = y.fK)
    (x : Sp K ⟶ Z.X) (hx : spMap ι ≫ x = y.y ≫ GlobalTheory.Toroidal.genι Z)
    (A : Over (Sp K)) [GrpObj A] (θ : A.left ⟶ Z.t.G.left) (hθ : IsGrpPullback A Z.t.G x θ) :
    ∃ (o : Obj Dw l (baseKA l) (spMap jF ≫ spMap (IntermediateField.inclusion c.le).toRingHom))
      (e : A ≅ o.t.G), IsMonHom e.hom ∧ LBIso (Z.t.PP.L.pull θ) (o.t.PP.L.pull e.hom.left) ∧
      ∀ (ρ : E →+* ℂ) (i : Fin (Dw.mult ρ)) (v : epsR K ⟶ A), IsTangent v →
        y.u ρ i = spMap (Chart.dualMapR ι) ≫ v.left ≫ θ →
        EigenvectorLieDegree.IsEigVec o.t.act ((EigenvectorLieDegree.embIn c jF ρ).comp (algebraMap (𝓞 E) E)) (v ≫ e.hom) := by
  haveI := epi_spMap_field ι
  haveI := epi_dualMapR ι
  have hov : y.y ≫ pullback.snd Z.s (spMap (algebraMap (𝓞 c.F) c.F)) = spMap ι ≫ spMap jF := by
    rw [sp_comp, hj]; exact y.y_over
  have hw : x ≫ Z.s = spMap jF ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [← cancel_epi (spMap ι), reassoc_of% hx, ← reassoc_of% hov, ← pullback.condition]
  let yK : Sp K ⟶ GlobalTheory.Toroidal.gen Z := pullback.lift x (spMap jF) hw
  have hyK : spMap ι ≫ yK = y.y := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, hx]
    · rw [Category.assoc, pullback.lift_snd, hov]
  have hr : Set.range yK ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    have hp : p = spMap ι (IsLocalRing.closedPoint Qb) := Subsingleton.elim _ _
    subst hp
    by_contra h
    refine hy (GlobalTheory.Toroidal.mem_genBd.2 ?_)
    rw [← hyK]
    exact h
  haveI := Z.jQ_open
  let y' := IsOpenImmersion.lift Z.jQ yK hr
  have hy' : y' ≫ Z.jQ = yK := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨t', ⟨m₁⟩⟩ : ∃ t' : SAB H (Sp K), Nonempty (SABMap t' Z.oF.t y') := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull y' Z.oF.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.m m₁
  have ex : y' ≫ Z.jQ ≫ pullback.fst _ _ = x := by
    rw [← Category.assoc, hy']; exact pullback.lift_fst _ _ _
  have key : ∀ s, y' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = s →
      ∃ o : Obj Dw l (baseKA l) s, o.t = t' := by
    rintro _ rfl
    exact ⟨GlobalTheory.ModelCompare.objOfSABMap Z.oF m₁, rfl⟩
  obtain ⟨o, rfl⟩ := key (spMap jF ≫ spMap (IntermediateField.inclusion c.le).toRingHom) (by
    rw [pullback.condition, ← Z.jQ_over, Category.assoc, reassoc_of% hy', ← Category.assoc]
    exact congrArg (· ≫ _) (pullback.lift_snd _ _ _))
  obtain ⟨e, he, hφ⟩ := grpPullback_iso hθ (n.cart.congr ex rfl)
  have hL : LBIso o.t.PP.L (Z.t.PP.L.pull n.cm.F) := by
    obtain ⟨w, hw, -⟩ := n.lin
    exact ⟨w, hw⟩
  refine ⟨o, e, he, hφ ▸ EllComp.lbIso_pull_comp hL.symm _, fun ρ i v hv hu => ⟨?_, fun a => ?_⟩⟩
  · unfold IsTangent at hv ⊢
    rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]
  · have hs : ∀ s : K, epsScaleR s = epsMul s := fun s => rfl
    refine n.cart.1.hom_ext ?_ ?_
    · have := y.eig ρ i a
      rw [hu, ← hj] at this
      rw [Over.comp_left, Category.assoc, Category.assoc, n.act a, Over.comp_left, Category.assoc, Category.assoc,
        reassoc_of% hφ, hφ, ← cancel_epi (spMap (Chart.dualMapR ι)), hs]
      simp only [Category.assoc] at this
      rw [this, ← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp,
        dualMapR_comp_epsMul]
      rfl
    · rw [Over.w, Category.assoc, Over.w, hs]
      exact ((sp_comp _ _).trans (congrArg spMap (UpperTheory.FibObj.epsMul_comp_alg _))).symm

theorem UpperTheory.semi_fibre_point_gives_model_object :
    ∀ (D : D7) (O : GlobalTheory.Mean4O.Setup D) (y : GlobalTheory.ShFam.Pad.Pt O.s), GlobalTheory.TrueGeo.below y.y ∉ GlobalTheory.Toroidal.genBd O.s.T.Z → ∀ (K : Type) [Field K] [NumberField K] (F : GlobalTheory.LieHt.SemiFib K) (ι : K →+* GlobalTheory.ShFam.Pad.Qb), GlobalTheory.LieRead.FibTie O y F ι → ∃ (jF : O.κ.c.F →+* K) (o : Obj O.S.Dw O.κ.l (baseKA O.κ.l) (spMap jF ≫ spMap (IntermediateField.inclusion O.κ.c.le).toRingHom)) (e : F.P₀.A ≅ o.t.G), IsMonHom e.hom ∧ LBIso F.P₀.L (o.t.PP.L.pull e.hom.left) ∧ ∀ (ρ : D.host.E →+* ℂ) (w : Fin (O.S.Dw.mult ρ) → (epsR K ⟶ F.P₀.A)), (∀ i : Fin (O.S.Dw.mult ρ), IsLieComb (GlobalTheory.LieRead.stepVec O F ρ i) F.v (w i)) → ∀ i, EigenvectorLieDegree.IsEigVec o.t.act ((EigenvectorLieDegree.embIn O.κ.c jF ρ).comp (algebraMap (𝓞 D.host.E) D.host.E)) (w i ≫ e.hom) := by
  intro D O y hy K _ _ F ι ⟨jF, yO, ψ, hj, hyO, hψ, hL, hg, hu⟩
  obtain ⟨o, e, he, hL', hE⟩ := fibobj O.s.T.Z y hy ι jF hj (spMap (algebraMap (𝓞 K) K) ≫ yO)
    (by rw [← Category.assoc, UpperTheory.FibObj.sp_comp, hyO]) F.P₀.A (F.φ ≫ ψ) (F.fib.comp hψ)
  refine ⟨jF, o, e, he, LBIso.trans F.P₀.isLB (pull_isLB O.s.T.Z.t.PP.isLB _) (pull_isLB o.t.PP.isLB _) hL.symm hL',
    fun ρ w hw i => ?_⟩
  obtain ⟨q, hq, hv, -⟩ := UpperTheory.lie_lattice_generator D O K F ρ i i.2 hg
  haveI := F.P₀.isAb.comm
  obtain ⟨h1, -, -, h2, -⟩ := GlobalTheory.LieComb.lieComb_algebra K F.P₀.A _ F.v F.basis.1
  have hwi : w i = F.v q := (h1 _).unique (hv ▸ hw i) (h2 q)
  rw [hwi]
  exact hE ρ i _ (F.basis.1 q) (hu q _ hq)
