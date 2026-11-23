import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.Bridge
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArFormExistsOfInt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMixOfBaseInt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HeightProjectionOfInt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Set MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.TwistTop
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.ArithmeticHeightTower.Read1

open GlobalTheory.Amb GlobalTheory.AmbMetric GlobalTheory.Published GlobalTheory.Published.Amb

theorem isArithVar_mpZ (m : ℕ) (n : Fin (m + 1) → ℕ) : IsArithVar (mpStr ℤ m n) (∑ a, n a) :=
  isArithVar_mp ℤ inferInstance m n

theorem isArithVar_qp (n' m : ℕ) (n : Fin (m + 1) → ℕ) :
    IsArithVar (qpStr n' m n) (∑ a, (Fin.cons n' n : Fin (m + 2) → ℕ) a) := by
  have hA := isArithVar_mpZ m n
  have h1 : ringKrullDim ℤ = 1 := GlobalTheory.Amb.ringKrullDim_eq_one (Module.Finite.self ℤ)
  have hP := GlobalTheory.ProjModel.isArithVar_pspace ℤ h1 n'
  have hsum : ∑ a, (Fin.cons n' n : Fin (m + 2) → ℕ) a = n' + ∑ a, n a := Fin.sum_cons _ _
  rw [hsum]
  have hpc : GlobalTheory.Amb.PolyCovered (qpStr n' m n) (n' + ∑ a, n a) :=
    GlobalTheory.Amb.polyCovered_pullback (PSpace.str ℤ n') (mpStr ℤ m n) _ _ (GlobalTheory.Amb.polyCovered_pSpace n')
      (GlobalTheory.Amb.polyCovered_mp ℤ m n)
  have e : spMap (Int.castRingHom ℤ) = 𝟙 (Sp ℤ) := by simp
  have f1 : Flat (toSpecBase ℤ n') := by
    have := hP.flat
    rwa [e, Category.comp_id] at this
  have f2 : Flat (mpStr ℤ m n) := by
    have := hA.flat
    rwa [e, Category.comp_id] at this
  refine ⟨inferInstance, inferInstance, GlobalTheory.Amb.isIntegral_of_polyCovered _ _ hpc,
    GlobalTheory.ProjSpace.isProjOver_pullback hP.isProjOver hA.isProjOver, ?_,
    GlobalTheory.Amb.topologicalKrullDim_of_polyCovered h1 _ _ hpc⟩
  rw [e, Category.comp_id]
  infer_instance

theorem exists_lb_twB (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℤ) (D : ℕ) (hX : IsArithVar p D)
    (ι : Type) [Fintype ι] (B : ι → LB X) (hB : ∀ j, (B j).IsLB) :
    ∃ (m : ℕ) (n : Fin (m + 1) → ℕ) (i : X ⟶ MP ℤ m n) (_ : IsClosedImmersion i) (_ : i ≫ mpStr ℤ m n = p)
      (c : ι → Fin m) (t : ι → ℤ), ∀ j, LBIso ((twB m n (c j) (t j)).pull i) (B j) := by
  obtain ⟨N, e, he, hep⟩ := hX.isProjOver
  haveI := he
  choose tt r g hg hcls using fun j => GlobalTheory.Amb.exists_twist_map e (B j) (hB j)
  set eq := Fintype.equivFin ι
  let n : Fin (Fintype.card ι + 1) → ℕ := Fin.cons N (fun k => r (eq.symm k))
  let a : (i : Fin (Fintype.card ι + 1)) → X ⟶ projectiveSpace ℤ (n i) :=
    Fin.cases (motive := fun i => X ⟶ projectiveSpace ℤ (n i)) e (fun k => g (eq.symm k))
  have ha : ∀ i, a i ≫ toSpecBase ℤ (n i) = p := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hep
    · exact (hg (eq.symm k)).trans hep
  let i := GroundTheory.Arith.SchemeCoh.ProjSpace.lift (Fintype.card ι) n p a ha
  have hi0 : i ≫ pr ℤ (Fintype.card ι) n 0 = e := GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr _ n p a ha 0
  haveI := GlobalTheory.Amb.isSeparated_pr_zero ℤ (Fintype.card ι) n
  haveI : IsClosedImmersion (i ≫ pr ℤ (Fintype.card ι) n 0) := by rw [hi0]; exact he
  have hci : IsClosedImmersion i := IsClosedImmersion.of_comp i (pr ℤ (Fintype.card ι) n 0)
  have key : ∀ k : Fin (Fintype.card ι),
      LBIso ((twB (Fintype.card ι) n k (-(tt (eq.symm k) : ℤ))).pull i) (B (eq.symm k)) := by
    intro k
    exact GlobalTheory.Amb.lbIso_pull_tw i (pr ℤ (Fintype.card ι) n k.succ) (pr ℤ (Fintype.card ι) n 0) (a k.succ) e
      (GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr _ n p a ha k.succ) hi0 (tt (eq.symm k)) (B (eq.symm k)) (hB _)
      (hcls (eq.symm k))
  refine ⟨Fintype.card ι, n, i, hci, GroundTheory.Arith.SchemeCoh.ProjSpace.lift_mpStr _ n p a ha, fun j => eq j,
    fun j => -(tt j : ℤ), fun j => ?_⟩
  have := key (eq j)
  rwa [Equiv.symm_apply_apply] at this

theorem isLB_twB (m : ℕ) (n : Fin (m + 1) → ℕ) (c : Fin m) (t : ℤ) : (twB m n c t).IsLB :=
  isLB_tw (LB.isLB_pull (O1_isLB ℤ _) _) (LB.isLB_pull (O1_isLB ℤ _) _) _

theorem exists_metric_ext_B (k : Type) [CommRing k] (P : Scheme.{0}) [IsIntegral P] (q : P ⟶ Sp k) (N : ℕ)
    (hP : IsArithVar q N) (hs : GenSmooth q N) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ P) [IsClosedImmersion i]
    (p : X ⟶ Sp k) (hi : i ≫ q = p) (B' : LB P) (hB' : B'.IsLB) (L : HermLB p) (hL : LBIso (B'.pull i) L.B) :
    ∃ M : HermLB q, M.B = B' ∧ (M.pull i hi).Isometric L := by
  obtain ⟨χ, hc, hj, hT⟩ := GlobalTheory.AmbMetric.exists_transport (B'.pull i)
    (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hB' i) L hL
  obtain ⟨ψ, hψc, hψj, hext⟩ := GlobalTheory.AmbMetric.exists_weight_ext i hi hP hs B' hB' χ hc hj
  refine ⟨⟨B', hB', ψ, hψc, hψj⟩, rfl, ?_⟩
  refine GlobalTheory.HermLB.Isometric.trans ?_ hT
  refine GlobalTheory.HermLB.isometric_of_eqOn (fun σ a y hy => ?_)
  change (χ σ).φ a y = ((ψ σ).pull i hi).φ a y
  change y ∈ ptsIn p σ ((B'.pull i).U a) at hy
  have hm : PtsOver.map i hi (spMap σ) y ∈ ptsIn q σ (B'.U (a PUnit.unit)) :=
    (GlobalTheory.Published.mem_ptsIn_pull (m := PtsOver.map i hi (spMap σ)) (fun z => rfl)).1 hy
  have e1 := GlobalTheory.Weight.pull_φ (ψ σ) i hi a y
  rw [hext σ (a PUnit.unit) y hm] at e1
  exact e1.symm

theorem isTwB_of_eq {m : ℕ} {n : Fin (m + 1) → ℕ} (M : HermLB (mpStr ℤ m n)) (c : Fin m) (t : ℤ)
    (h : M.B = twB m n c t) : IsTwB M := by
  exact ⟨c, t, ⟨by rw [h]; exact GlobalTheory.lbIso_self (isLB_twB m n c t)⟩⟩

theorem exists_ambientZ {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℤ} {D : ℕ}
    (hX : IsArithVar p D) {ι : Type} [Fintype ι] (L : ι → HermLB p) :
    ∃ (m : ℕ) (n : Fin (m + 1) → ℕ) (i : X ⟶ MP ℤ m n) (_ : IsClosedImmersion i) (hi : i ≫ mpStr ℤ m n = p)
      (M : ι → HermLB (mpStr ℤ m n)), (∀ j, IsTwB (M j)) ∧ ∀ j, ((M j).pull i hi).Isometric (L j) := by
  obtain ⟨m, n, i, hci, hi, c, t, hiso⟩ :=
    exists_lb_twB X p D hX ι (fun j => (L j).B) (fun j => (L j).isLB)
  haveI := hci
  haveI := GlobalTheory.Amb.isIntegral_mp ℤ m n
  choose M hMB hMI using fun j => exists_metric_ext_B ℤ (MP ℤ m n) (mpStr ℤ m n) _ (isArithVar_mpZ m n)
    (GlobalTheory.Amb.genSmooth_mp ℤ m n) X i p hi (twB m n (c j) (t j)) (isLB_twB m n (c j) (t j)) (L j) (hiso j)
  exact ⟨m, n, i, hci, hi, M, fun j => isTwB_of_eq (M j) (c j) (t j) (hMB j), hMI⟩

theorem form (H : FormZ) : ArFormExists := by
  apply GlobalTheory.CompanionTheory.Ar.BaseZ.arFormExists_of_int
  intro X _ p D hX ι _ L
  obtain ⟨m, n, i, hci, hi, M, hM, hI⟩ := exists_ambientZ hX L
  haveI := hci
  subst hi
  obtain ⟨Φ, hΦ1, hΦ2⟩ := H m n X i D hX ι M hM
  refine ⟨Φ, fun c => ?_, hΦ2⟩
  exact (GlobalTheory.ArInt.isometric_comb_congr (fun j => hI j) c).isSelfInter hX (hΦ1 c)

theorem mix (H : MixZ) : ArMix := by
  apply GlobalTheory.CompanionTheory.Ar.BaseZ.arMix_of_base_int
  intro X _ _ p D hX ι _ M L Φ hΦ c h hh r hr
  obtain ⟨m, n, i, hci, hi, N, hN, hI⟩ := exists_ambientZ hX (fun o : Option ι => o.elim M L)
  haveI := hci
  subst hi
  have hmix := H m n X i D hX ι (N none) (fun j => N (some j)) (hN none) (fun j => hN (some j))
  have hmix' := GlobalTheory.Published.Amb.mixOn_congr hX (hI none) (fun j => hI (some j)) hmix
  exact hmix' Φ hΦ c h hh r hr

theorem proj (HH : HeightsZ) (HQ : HeightsQ) (HP : ProjQ) : HeightProjection := by
  apply GlobalTheory.CompanionTheory.Ar.BaseZ.heightProjection_of_int
  intro X Y _ p q D e hX hY π hπ hdim hdeg L h hh
  haveI := hX.isIntegral
  obtain ⟨m, n, i, hci, hi, M, hM, hI⟩ := exists_ambientZ hX (fun _ : Unit => L)
  haveI := hci
  obtain ⟨n', j0, hj0, hj0q⟩ := hY.isProjOver
  haveI := hj0
  have hπi : (π ≫ i) ≫ mpStr ℤ m n = q := by rw [Category.assoc, hi, hπ]
  have cond : j0 ≫ toSpecBase ℤ n' = (π ≫ i) ≫ mpStr ℤ m n := by
    rw [hπi]
    exact hj0q
  let j : Y ⟶ QP n' m n := pullback.lift j0 (π ≫ i) cond
  haveI : IsClosedImmersion j := GlobalTheory.Amb.isClosedImmersion_lift ℤ m n' n j0 (π ≫ i) cond
  have hjq : j ≫ qpStr n' m n = q := by
    simp only [j, qpStr, pullback.lift_fst_assoc]
    exact hj0q
  have hjs : j ≫ qpSnd n' m n = π ≫ i := pullback.lift_snd _ _ _
  have hAQ := isArithVar_qp n' m n
  have hAM := isArithVar_mpZ m n
  obtain ⟨hM0, hhM⟩ := HH m n (M ()) (hM ())
  obtain ⟨h', hh'⟩ := HQ n' m n (M ()) (hM ())
  have hXh : L.IsArithHeight (fun x => hM0 (i x)) := (hI ()).isArithHeight hX (hhM.restrict hAM i hi)
  have heq : h = fun x => hM0 (i x) := GlobalTheory.HermLB.IsArithHeight.unique hX hh hXh
  have hY1 := hh'.restrict hAQ j hjq
  have hY2 := (GlobalTheory.HermLB.refines_pull_pull (M ()) (qpSnd n' m n) (qpSnd_str n' m n) j hjq
    (by rw [Category.assoc, qpSnd_str, hjq])).isArithHeight hY hY1
  rw [GlobalTheory.Published.Amb.pull_congr (M ()) hjs _ hπi] at hY2
  have hY3 := (GlobalTheory.HermLB.refines_pull_comp (M ()) i hi π hπ hπi).isArithHeight hY hY2
  have hY4 := ((hI ()).pull π hπ).isArithHeight hY hY3
  refine ⟨fun y => h' (j y), hY4, ?_⟩
  have hpt : qpSnd n' m n (j (genericPoint Y)) = i (π (genericPoint Y)) := by
    rw [← Scheme.Hom.comp_apply, hjs, Scheme.Hom.comp_apply]
  have hrd : Scheme.Hom.residueDegree (qpSnd n' m n) (j (genericPoint Y)) =
      Scheme.Hom.residueDegree π (genericPoint Y) := by
    have e1 := GlobalTheory.CurveDegreesCompare.residueDegree_comp j (qpSnd n' m n) (genericPoint Y)
    have e2 := GlobalTheory.CurveDegreesCompare.residueDegree_comp π i (genericPoint Y)
    rw [hjs, e2, GlobalTheory.Published.residueDegree_of_isClosedImmersion i,
      GlobalTheory.Published.residueDegree_of_isClosedImmersion j] at e1
    simpa using e1.symm
  have hdimQ := hdim
  rw [← GlobalTheory.Published.Amb.dim_closure_image i, ← hpt] at hdimQ
  have hdegQ : Scheme.Hom.residueDegree (qpSnd n' m n) (j (genericPoint Y)) ≠ 0 := by
    rw [hrd]
    exact hdeg
  have hYj : IsArithVar (j ≫ qpStr n' m n) e := by
    rw [hjq]
    exact hY
  have key := HP n' m n Y j e hYj hdimQ hdegQ (M ()) (hM ()) hM0 h' hhM hh'
  show h' (j (genericPoint Y)) = _
  rw [key, hrd, hpt, heq]

end GlobalTheory.ArithmeticHeightTower.Read1
