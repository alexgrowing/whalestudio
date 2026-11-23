import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyArithDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnSeqShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFlagGradedIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPullbackHermitianIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfEpiVectorBundleSameRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualDualMapEigenImageInclusion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagModelOfIsIsometry

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical

namespace GlobalTheory.FlagSpDual

open Limits GlobalTheory.DualFlag GlobalTheory.DualPull

section Flags

variable {T : Scheme.{0}} {P : T.Modules} {N : ℕ}

theorem sameStep_of_le (a b : Vert.Flag P N) (i : Fin (N + 1)) (t : a.F i ⟶ b.F i) (ht : t ≫ b.ι i = a.ι i) :
    a.SameStep b i := by
  let c : cokernel (a.ι i) ⟶ cokernel (b.ι i) := cokernel.desc _ (cokernel.π _) (by rw [← ht]; simp)
  have hc : cokernel.π _ ≫ c = cokernel.π _ := cokernel.π_desc _ _ _
  have : Epi c := epi_of_epi_fac hc
  have := isIso_of_epi_of_isVB c _ (a.isVB_cokernel i) (b.isVB_cokernel i)
  have h0 : b.ι i ≫ cokernel.π (a.ι i) = 0 := by
    rw [← cancel_mono c, Category.assoc, hc, cokernel.condition, zero_comp]
  let s : b.F i ⟶ a.F i := Abelian.monoLift (a.ι i) (b.ι i) h0
  have hs : s ≫ a.ι i = b.ι i := Abelian.monoLift_comp _ _ _
  refine ⟨⟨t, s, ?_, ?_⟩, ht⟩
  · rw [← cancel_mono (a.ι i), Category.assoc, hs, ht, Category.id_comp]
  · rw [← cancel_mono (b.ι i), Category.assoc, ht, hs, Category.id_comp]

theorem comp_dualMap_eq_zero_iff {A B : T.Modules} (a : A ⟶ P) (b : B ⟶ VB.dual P) :
    b ≫ dualMap a = 0 ↔ (a ≫ cartierDualToBidual P) ≫ dualMap b = 0 := by
  constructor
  · intro h
    rw [toBidual_naturality_dualSheafTranspose, Category.assoc, ← dualMap_comp, h, dualMap_zero, comp_zero]
  · intro h
    rw [← Category.comp_id b, ← LieVB.toBidual_dual_comp_dualMap, ← Category.assoc b, toBidual_naturality_dualSheafTranspose, Category.assoc,
      Category.assoc, ← dualMap_comp, ← dualMap_comp, h, dualMap_zero, comp_zero]

def Orth (n : Vert.Flag P N) (m : Vert.Flag (VB.dual P) N) : Prop := ∀ i, m.ι i ≫ dualMap (n.ι i.rev) = 0

theorem Orth.sameStep {n : Vert.Flag P N} {m : Vert.Flag (VB.dual P) N} (h : Orth n m) (i : Fin (N + 1)) :
    m.SameStep (dualFlag n) i :=
  sameStep_of_le m (dualFlag n) i (kernel.lift _ (m.ι i) (h i)) (kernel.lift_ι _ _ _)

theorem orth_dualFlag (n : Vert.Flag P N) : Orth n (dualFlag n) := fun _ => kernel.condition _

theorem Orth.right_unique {n : Vert.Flag P N} {m m' : Vert.Flag (VB.dual P) N} (h : Orth n m) (h' : Orth n m')
    (i : Fin (N + 1)) : m.SameStep m' i := by
  obtain ⟨e, he⟩ := h.sameStep i
  obtain ⟨e', he'⟩ := (h'.sameStep i).symm
  exact ⟨e ≪≫ e', by rw [Iso.trans_hom, Category.assoc, he', he]⟩

theorem Orth.flip {n : Vert.Flag P N} {m : Vert.Flag (VB.dual P) N} [IsIso (cartierDualToBidual P)] :
    Orth n m ↔ Orth m (n.ofIso (asIso (cartierDualToBidual P))) := by
  refine ⟨fun h i => ?_, fun h i => ?_⟩
  · have := (comp_dualMap_eq_zero_iff _ _).1 (h i.rev)
    rwa [Fin.rev_rev] at this
  · have := h i.rev
    rw [Fin.rev_rev] at this
    exact (comp_dualMap_eq_zero_iff _ _).2 this

theorem Orth.left_unique {n n' : Vert.Flag P N} {m : Vert.Flag (VB.dual P) N} (h : Orth n m) (h' : Orth n' m)
    (i : Fin (N + 1)) : n.SameStep n' i := by
  have := n.isVB_self.isIso_toBidual_of_local_frames
  obtain ⟨e, he⟩ := (Orth.flip.1 h).right_unique (Orth.flip.1 h') i
  refine ⟨e, ?_⟩
  rw [← cancel_mono (cartierDualToBidual P), Category.assoc]
  exact he

theorem exists_orth (hP : IsVB P N) (m : Vert.Flag (VB.dual P) N) : ∃ n : Vert.Flag P N, Orth n m := by
  have := hP.isIso_toBidual_of_local_frames
  refine ⟨(dualFlag m).ofIso (asIso (cartierDualToBidual P)).symm, Orth.flip.2 fun i => ?_⟩
  change (((dualFlag m).ι i ≫ inv (cartierDualToBidual P)) ≫ cartierDualToBidual P) ≫ _ = 0
  rw [Category.assoc _ _ (cartierDualToBidual P), IsIso.inv_hom_id, Category.comp_id]
  exact orth_dualFlag m i

theorem Orth.congr {n n' : Vert.Flag P N} {m m' : Vert.Flag (VB.dual P) N} (h : Orth n m) (hn : ∀ i, n'.SameStep n i)
    (hm : ∀ i, m'.SameStep m i) : Orth n' m' := fun i => by
  obtain ⟨e, he⟩ := hn i.rev
  obtain ⟨e', he'⟩ := hm i
  rw [← he, ← he', dualMap_comp, Category.assoc, reassoc_of% (h i), zero_comp, comp_zero]

end Flags

theorem theta_pullbackComp {B Y T : Scheme.{0}} (π : Y ⟶ B) (g : T ⟶ Y) (E : B.Modules) :
    (Scheme.Modules.pullbackComp g π).inv.app (VB.dual E) ≫ (Scheme.Modules.pullback g).map (theta π E) ≫
      theta g ((Scheme.Modules.pullback π).obj E) ≫ dualMap ((Scheme.Modules.pullbackComp g π).inv.app E) =
        theta (g ≫ π) E := by
  refine pull_ext (g ≫ π) fun V l => dual_pull_ext (g ≫ π) le_rfl fun W h S hS e s => ?_
  rw [dualApp_theta (g ≫ π) _ h, ← QCoh.app_app, ← QCoh.app_app, ← QCoh.app_app, dualApp_dualMap,
    Vert.DivPull.pullbackComp_inv_app g π _ (le_refl (π ⁻¹ᵁ V)) (T := (g ≫ π) ⁻¹ᵁ V) le_rfl,
    Vert.DivPull.pullbackComp_inv_app g π _ (le_refl (π ⁻¹ᵁ W)) e]
  erw [QCoh.pullback_map_app_pullbackSections]
  refine (dualApp_theta g _ (π.preimage_mono h) _ hS e _).trans ?_
  rw [dualApp_theta π _ h]
  exact congr($(Scheme.Hom.appLE_comp_appLE g π W _ S le_rfl e) _)

section Universal

variable {B Y T : Scheme.{0}} {E : B.Modules} {r : ℕ} (hE : IsVB E r)

def thetaIso (π : Y ⟶ B) : (Scheme.Modules.pullback π).obj (VB.dual E) ≅ VB.dual ((Scheme.Modules.pullback π).obj E) :=
  have := isIso_theta π hE
  asIso (theta π E)

def annFlag (π : Y ⟶ B) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r) :
    Vert.Flag ((Scheme.Modules.pullback π).obj (VB.dual E)) r :=
  (dualFlag fl).ofIso (thetaIso hE π).symm

theorem orth_carried (π : Y ⟶ B) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r) (g' : T ⟶ Y) (g : T ⟶ B)
    (w : g' ≫ π = g) :
    Orth (FlagConnect.carried π (fun _ : Unit => E) (fun _ => r) (fun _ => fl) g' g w ())
      ((FlagConnect.carried π (fun _ : Unit => VB.dual E) (fun _ => r) (fun _ => annFlag hE π fl) g' g w ()).ofIso
        (thetaIso hE g)) := by
  subst w
  intro i
  change ((((Scheme.Modules.pullback g').map ((dualFlag fl).ι i ≫ (thetaIso hE π).inv)) ≫
    (Scheme.Modules.pullbackComp g' π).hom.app _ ≫ 𝟙 _) ≫ theta (g' ≫ π) E) ≫
      dualMap ((Scheme.Modules.pullback g').map (fl.ι i.rev) ≫ (Scheme.Modules.pullbackComp g' π).hom.app _ ≫ 𝟙 _) = 0
  have e₁ : (Scheme.Modules.pullback g').map (thetaIso hE π).inv ≫ (Scheme.Modules.pullback g').map (theta π E) = 𝟙 _ := by
    rw [← Functor.map_comp, ← CategoryTheory.Functor.map_id]
    exact congrArg _ (thetaIso hE π).inv_hom_id
  have e₂ : dualMap ((Scheme.Modules.pullbackComp g' π).inv.app E) ≫
      dualMap ((Scheme.Modules.pullbackComp g' π).hom.app E) = 𝟙 _ := by
    rw [← dualMap_comp, Iso.hom_inv_id_app]
    rfl
  rw [← theta_pullbackComp, Category.comp_id, Category.comp_id, dualMap_comp, Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% e₁, reassoc_of% e₂, ← theta_naturality, ← Functor.map_comp_assoc, orth_dualFlag fl i,
    Functor.map_zero, zero_comp]

theorem isFlagBundle_annFlag (π : Y ⟶ B) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r)
    (H : IsFlagBundle π (fun _ : Unit => E) (fun _ => r) fun _ => fl) :
    IsFlagBundle π (fun _ : Unit => VB.dual E) (fun _ => r) fun _ => annFlag hE π fl := by
  intro T g m
  obtain ⟨n, hn⟩ := exists_orth (hE.pullback g) ((m ()).ofIso (thetaIso hE g))
  refine (existsUnique_congr fun g' => exists_congr fun w => ?_).1 (H T g fun _ => n)
  have hc := orth_carried hE π fl g' g w
  constructor
  · intro h _ i
    obtain ⟨e, he⟩ := (hc.congr (n' := n) (fun i => Vert.Flag.SameStep.symm (h () i))
      fun i => ⟨Iso.refl _, Category.id_comp _⟩).right_unique hn i
    refine ⟨e, ?_⟩
    rw [← cancel_mono (thetaIso hE g).hom, Category.assoc]
    exact he
  · intro h _ i
    refine (hc.congr (m' := (m ()).ofIso (thetaIso hE g)) (fun i => ⟨Iso.refl _, Category.id_comp _⟩)
      fun j => ?_).left_unique hn i
    obtain ⟨e, he⟩ := h () j
    refine Vert.Flag.SameStep.symm ⟨e, ?_⟩
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (thetaIso hE g).hom) he)

end Universal

theorem isIsometry_thetaIso {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {E : X.Modules}
    {r : ℕ} (h : VMetric p E r) (f : Y ⟶ X) (hf : f ≫ p = q) :
    (h.dual.pull f hf).IsIsometry (h.pull f hf).dual (thetaIso h.isVB f) := by
  have hE := h.isVB
  have := hE.isQuasicoherent
  refine VMetric.isIsometry_iff _ |>.2 (VMetric.ext (funext fun σ => Met.ext_of_exists fun z => ?_))
  have hc := hE.mem_pick (Points.PtsOver.map f hf _ z)
  set c := hE.pick (Points.PtsOver.map f hf _ z)
  have hch : (c.pull hE f).dual = (c.dual.pull hE.dual f).map (thetaIso hE f) := by
    have H : (c.pull hE f).dual.e = ((c.dual.pull hE.dual f).map (thetaIso hE f)).e := funext fun i =>
      (DualPullMet.theta_coord f c.isFrame i).symm
    exact congr(VB.Chart.mk _ $H _)
  refine ⟨(c.pull hE f).dual, hc, ?_⟩
  have e₁ : ((h.met σ).pull f hf).dual.G (c.pull hE f).dual z =
      HermFrame.dualGram ((h.met σ).G c (Points.PtsOver.map f hf _ z)) :=
    (Met.dual_G (y := z) _ (c.pull hE f) hc).trans (congrArg _ (Met.pull_G _ f hf c hc))
  have e₂ : (((h.met σ).dual.pull f hf).map (thetaIso hE f)).G ((c.dual.pull hE.dual f).map (thetaIso hE f)) z =
      HermFrame.dualGram ((h.met σ).G c (Points.PtsOver.map f hf _ z)) :=
    (Met.map_G (y := z) _ _ (c.dual.pull hE.dual f) hc).trans
      ((Met.pull_G _ f hf c.dual hc).trans (Met.dual_G _ c hc))
  rw [← hch] at e₂
  exact e₁.trans e₂.symm

theorem aeval_vdmPol (r e : ℕ) :
    aeval (fun o : Option (Fin r) => (o.elim (X none) fun i => -X (some i.rev) : MvPolynomial (Option (Fin r)) ℝ))
      (vdmPol r e) = vdmPol r e := by
  simp only [vdmPol, map_mul, map_sum, map_prod, map_pow, map_sub, aeval_X, aeval_C, Option.elim, neg_sq, algebraMap_eq]
  congr 2
  · congr 1
    exact Fintype.sum_equiv Fin.revPerm _ _ fun i => rfl
  · rw [Finset.prod_sigma', Finset.prod_sigma']
    refine Finset.prod_nbij' (fun z => ⟨z.2.rev, z.1.rev⟩) (fun z => ⟨z.2.rev, z.1.rev⟩) ?_ ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp
    · intro z _
      ring

def dualSp {X : Scheme.{0}} {E : X.Modules} {r : ℕ} (hE : IsVB E r) (F : FlagSp E r) : FlagSp (VB.dual E) r :=
  ⟨F.Y, F.π, annFlag hE F.π F.fl, isFlagBundle_annFlag hE F.π F.fl F.univ⟩

theorem icls_grLB_annFlag {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules} {r : ℕ}
    {h : VMetric p E r} (H : h.IsCInf) (π : Y ⟶ X) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r) (i : Fin r) :
    -(VMetric.grLB fl i.rev (H.pull π rfl)).icls = (VMetric.grLB (annFlag h.isVB π fl) i (H.dual.pull π rfl)).icls := by
  rw [← HermLB.icls_dual, annFlag,
    VMetric.grLB_ofIso (IsometryPullback.isIsometry_symm (isIsometry_thetaIso h π rfl)) (H.pull π rfl).dual]
  exact HermLB.icls_eq_iff.2 (T.dual_flag_graded_isometric k Y _ _ r _ (H.pull π rfl) fl i)

theorem exists_isArFun_vdmPol (hC : ArCalc) {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k} {D : ℕ}
    (hY : IsArithVar q D) {r : ℕ} {L L' : Option (Fin r) → HermLB q} (h₀ : L none = L' none)
    (h₁ : ∀ i : Fin r, -(L (some i.rev)).icls = (L' (some i)).icls) {Φ : MvPolynomial (Option (Fin r)) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun L D Φ) (e : ℕ) : ∃ Φ', IsArFun L' D Φ' ∧ Φ' (vdmPol r e) = Φ (vdmPol r e) := by
  obtain ⟨Φ', hΦ'⟩ := ((hC.arExists k Y _ _ hY).2 _ L').1
  refine ⟨Φ', hΦ', ?_⟩
  rw [← apply_aeval hC.arIso hY hΦ hΦ'
    (fun o : Option (Fin r) => (o.elim (X none) fun i => -X (some i.rev) : MvPolynomial (Option (Fin r)) ℝ)) ?_,
    aeval_vdmPol]
  rintro (_ | i)
  · exact ⟨Pi.single none 1, by simp [lin, Pi.single_apply, apply_ite], by simp [Pi.single_apply, h₀]⟩
  · exact ⟨Pi.single (some i.rev) (-1), by simp [lin, Pi.single_apply, apply_ite, ite_smul],
      by simp [Pi.single_apply, h₁]⟩

theorem eq_genericPoint {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {d : ℕ}
    (hX : IsArithVar p d) {E : X.Modules} {r : ℕ} (hE : IsVB E r) (F : FlagSp E r) [IsIntegral F.Y] {y : F.Y}
    (hy : F.IsTop (genericPoint X) y) : y = genericPoint F.Y := by
  have := hX.isLocallyNoetherian
  obtain ⟨y', hy', hcl, -⟩ := ((FlagTop.main k X p _ hX E r hE).2 F).2.2 (genericPoint X)
  rw [genericPoint_closure, Set.preimage_univ] at hcl
  have e' : y' = genericPoint F.Y := (show IsGenericPoint y' Set.univ from hcl).eq (genericPoint_spec F.Y)
  have := hy.2 y' hy'.1
  rw [e'] at this
  exact (this.antisymm (genericPoint_specializes y)).eq

section Families

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules} {r : ℕ} {h : VMetric p E r}
  (H : h.IsCInf) (F : FlagSp E r) (N : HermLB p)

def famDual : Option (Fin r) → HermLB (F.π ≫ p) := (dualSp h.isVB F).fam H.dual N

theorem famDual_none : F.fam H N none = famDual H F N none :=
  (show F.fam H N none = N.pull F.π rfl from rfl).trans (show famDual H F N none = N.pull F.π rfl from rfl).symm

theorem famDual_some (i : Fin r) : -(F.fam H N (some i.rev)).icls = (famDual H F N (some i)).icls :=
  icls_grLB_annFlag H F.π F.fl i

theorem isVal_dualSp {z : X} {y : F.Y} (hy : F.IsTop z y) {e : ℕ} {Φ : MvPolynomial (Option (Fin r)) ℝ →ₗ[ℝ] ℝ} {a : ℝ}
    (hΦ : IsHtFun (famDual H F N) y (e + 2 + r.choose 2) Φ) (ha : Φ (vdmPol r e) = a) :
    (dualSp h.isVB F).IsVal H.dual N z e a :=
  ⟨y, Φ, hy, hΦ, ha⟩

end Families

theorem exists_isVal_dual : ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (d : ℕ), IsArithVar p d → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (F : FlagSp E r), ∃ F' : FlagSp (VB.dual E) r, ∀ (N : HermLB p) (e : ℕ) (a : ℝ), d = e + 1 → F.IsVal H N (genericPoint X) e a → F'.IsVal H.dual N (genericPoint X) e a := by
  intro hC k _ X _ p d hX E r h H F
  refine ⟨dualSp h.isVB F, fun N e a hd ⟨y, Φ, hy, hΦ, ha⟩ => ?_⟩
  have := hX.isLocallyNoetherian
  have hY := ((FlagTop.main k X p _ hX E r h.isVB).2 F).1
  have := hY.isIntegral
  have hg := eq_genericPoint hX h.isVB F hy
  have hD : e + 2 + r.choose 2 = d + r.choose 2 + 1 := by omega
  rw [hD, hg, isHtFun_generic_iff] at hΦ
  obtain ⟨Φ', hΦ', hv⟩ := exists_isArFun_vdmPol hC hY (famDual_none H F N) (famDual_some H F N) hΦ e
  rw [← isHtFun_generic_iff, ← hg, ← hD] at hΦ'
  exact isVal_dualSp H F N hy hΦ' (hv.trans ha)

end GlobalTheory.FlagSpDual

end
