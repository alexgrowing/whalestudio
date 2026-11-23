import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValHomEq
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecKIsUnit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.ZH.CrdMove

open GlobalTheory.VeryAmpleCharts GlobalTheory.ZH.CrdCalc GlobalTheory.FieldBaseChange

private lemma appLE_presheaf_map_eq_presheaf_map_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens} (hU : U' ≤ U)
    (hV : V' ≤ V) (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U') (a : Γ(Y, U)) :
    (f.appLE U' V' e').hom ((Y.presheaf.map (homOfLE hU).op).hom a) =
      (X.presheaf.map (homOfLE hV).op).hom ((f.appLE U V e).hom a) := by
  change (Y.presheaf.map (homOfLE hU).op ≫ f.appLE U' V' e').hom a = (f.appLE U V e ≫ X.presheaf.map (homOfLE hV).op).hom a
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

private lemma appLE_eq_unfold {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) (a : Γ(Y, U)) : (f.appLE U V e).hom a = (g.appLE U V e').hom a := by
  subst h
  rfl

private lemma appLE_appLE_appLE_eq_appLE_comp_comp {X Y Z T : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (U : T.Opens)
    (V : Z.Opens) (W : Y.Opens) (W' : X.Opens) (e₁ : V ≤ h ⁻¹ᵁ U) (e₂ : W ≤ g ⁻¹ᵁ V) (e₃ : W' ≤ f ⁻¹ᵁ W)
    (e : W' ≤ (f ≫ g ≫ h) ⁻¹ᵁ U) (a : Γ(T, U)) :
    (f.appLE W W' e₃).hom ((g.appLE V W e₂).hom ((h.appLE U V e₁).hom a)) = ((f ≫ g ≫ h).appLE U W' e).hom a := by
  change (h.appLE U V e₁ ≫ g.appLE V W e₂ ≫ f.appLE W W' e₃).hom a = _
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_unfold (Category.assoc _ _ _) _ _ _ _ _

theorem immBy_lbPow (hA : Out.AmpleSt) (K : Type) [Field K] (P : Out.PolAV (Sp K)) (N : ℕ) (hN : 4 ≤ N) :
    ∃ (m : ℕ) (s : Fin (m + 1) → (lbPow P.L N).Sec), ImmBy P.A.hom (lbPow P.L N) s Set.univ := by
  have h := (hA (Sp K) P N hN).2
  unfold Out.VeryAmpleAt at h
  obtain ⟨M, s, hcov, hs⟩ := h ⊤ (isAffineOpen_top _)
  have hiso : IsIso (P.A.hom ⁻¹ᵁ ⊤).ι := by
    rw [Scheme.Hom.preimage_top, ← Scheme.topIso_hom]
    infer_instance
  have hψ : inv (P.A.hom ⁻¹ᵁ ⊤).ι ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ := IsIso.inv_hom_id _
  have hL : P.L.IsLB := P.isLB
  refine ⟨M, fun i => GlobalTheory.VeryAmpleCharts.move P.L N hψ (s i), ?_, fun i _ => ?_⟩
  · dsimp only
    rw [eq_top_iff]
    intro y _
    have hy : inv (P.A.hom ⁻¹ᵁ ⊤).ι y ∈ (⨆ i, Out.nonzeroLocus (s i)) := by
      rw [hcov]
      trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hy
    obtain ⟨i, hi⟩ := hy
    simp only [TopologicalSpace.Opens.mem_iSup]
    exact ⟨i, Set.mem_univ _, (SetLike.ext_iff.1 (GlobalTheory.VeryAmpleCharts.locus_move P.L N hψ hL (s i)) y).2 hi⟩
  · obtain ⟨haff, r, hr, hsurj⟩ := hs i
    have hloc := GlobalTheory.VeryAmpleCharts.locus_move P.L N hψ hL (s i)
    refine ⟨(congrArg IsAffineOpen hloc).mpr (haff.preimage _), ?_⟩
    unfold IsRatio resG constFn
    refine ⟨fun j => ((inv (P.A.hom ⁻¹ᵁ ⊤).ι).appLE _ _ hloc.le).hom (r j), fun j l => ?_, ?_⟩
    · have le : Out.nonzeroLocus (move P.L N hψ (s i)) ⊓ (lbPow P.L N).U l ≤
          inv (P.A.hom ⁻¹ᵁ ⊤).ι ⁻¹ᵁ (Out.nonzeroLocus (s i) ⊓ (Out.powOver P.A P.L ⊤ N).U (fun _ => l PUnit.unit)) :=
        fun y hy => ⟨(SetLike.ext_iff.1 hloc y).1 hy.1, GlobalTheory.VeryAmpleCharts.chart_le P.L N hψ l hy.2⟩
      have e := congrArg ((inv (P.A.hom ⁻¹ᵁ ⊤).ι).appLE _ _ le).hom (hr j (fun _ => l PUnit.unit))
      rw [map_mul, appLE_presheaf_map_eq_presheaf_map_appLE, appLE_presheaf_map_eq_presheaf_map_appLE, appLE_presheaf_map_eq_presheaf_map_appLE] at e
      exact e
    · have hiso0 : IsIso (⊤ : (Sp K).Opens).ι := by
        rw [← Scheme.topIso_hom]
        infer_instance
      rw [eq_top_iff]
      intro f hf
      obtain ⟨g, rfl⟩ := GlobalTheory.VeryAmpleCharts.appLE_surjective (ψ := inv (P.A.hom ⁻¹ᵁ ⊤).ι)
        (Out.nonzeroLocus (s i)) _ hloc f
      obtain ⟨F, rfl⟩ := hsurj g
      clear hf
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.hom_eval₂]
      induction F using MvPolynomial.induction_on with
      | C a =>
        rw [MvPolynomial.eval₂_C, RingHom.comp_apply]
        apply Subring.subset_closure
        left
        obtain ⟨x, rfl⟩ := GlobalTheory.VeryAmpleCharts.appLE_surjective (ψ := (⊤ : (Sp K).Opens).ι) ⊤ ⊤
          (Scheme.Hom.preimage_top _).symm a
        refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom x, ?_⟩
        dsimp only
        have hx : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom x) = x := by
          simp
        rw [hx]
        exact (appLE_eq_unfold (f := P.A.hom)
          (g := inv (P.A.hom ⁻¹ᵁ ⊤).ι ≫ (P.A.hom ∣_ ⊤) ≫ (⊤ : (Sp K).Opens).ι)
          (by rw [morphismRestrict_ι, ← Category.assoc, hψ, Category.id_comp]) ⊤ _ _ (fun _ _ => trivial) x).trans
          (appLE_appLE_appLE_eq_appLE_comp_comp _ _ _ ⊤ _ _ _ _ _ _ (fun _ _ => trivial) x).symm
      | add p q hp hq =>
        rw [MvPolynomial.eval₂_add]
        exact add_mem hp hq
      | mul_X p n hp =>
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
        exact mul_mem hp (Subring.subset_closure (Or.inr ⟨n, rfl⟩))

variable {X X' Y : Scheme.{0}} {R : Type} [CommRing R] {I : Type}

theorem valR_appLE (x : Sp R ⟶ Y) (g : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (e : W ≤ g ⁻¹ᵁ U) (h : ⊤ ≤ x ⁻¹ᵁ W)
    (a : Γ(X, U)) : valR x W ((g.appLE U W e).hom a) = valR (x ≫ g) U a := by
  have h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := fun p _ => e (h trivial)
  have key : g.appLE U W e ≫ x.appLE W ⊤ h = (x ≫ g).appLE U ⊤ h' := by
    rw [Scheme.Hom.appLE_comp_appLE]
  rw [valR, valR, dif_pos h, dif_pos h', ← key]
  rfl

private lemma valR_rs_eq_valR {R : Type} [CommRing R] (x : Sp R ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, U)) : valR x V (rs hVU f) = valR x U f := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun p hp => hVU (h hp)
  have k : Y.presheaf.map (homOfLE hVU).op ≫ x.appLE V ⊤ h = x.appLE U ⊤ h' := by
    rw [Scheme.Hom.map_appLE]
  unfold rs
  rw [valR, valR, dif_pos h, dif_pos h', ← k]
  rfl

private lemma valR_mul_lemma_2 {R : Type} [CommRing R] (x : Sp R ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(Y, U)) : valR x U (f * g) = valR x U f * valR x U g := by
  rw [valR, valR, valR, dif_pos h, dif_pos h, dif_pos h, map_mul, map_mul]

private lemma isUnit_valR_of_unit {R : Type} [CommRing R] (x : Sp R ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (u : Γ(Y, U)ˣ) : IsUnit (valR x U (u : Γ(Y, U))) := by
  rw [valR, dif_pos h]
  exact (u.isUnit.map _).map _

theorem crd_secOfIso [IsLocalRing R] {A B : LB Y} {u : LB.Iso A B} (hu : u.IsGen) (hA : A.IsLB) (hB : B.IsLB)
    (t : I → B.Sec) {x : Sp R ⟶ Y} {v : I → R} (h : Crd A (fun i => secOfIso (t i) hu hA hB) x v) :
    Crd B t x v := by
  obtain ⟨l, c, hl, hv⟩ := h
  obtain ⟨b, hb⟩ : ∃ b, x (IsLocalRing.closedPoint R) ∈ A.U l ⊓ B.U b := by
    have := cover_inf hB l (hl (Set.mem_univ (IsLocalRing.closedPoint R)))
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  have hV : ⊤ ≤ x ⁻¹ᵁ (A.U l ⊓ B.U b) := fun p _ =>
    (IsLocalRing.specializes_closedPoint (R := R) p).mem_open (x ⁻¹ᵁ (A.U l ⊓ B.U b)).isOpen hb
  obtain ⟨w, hw⟩ := isUnit_valR_of_unit x _ hV ((res (divLe l b) (u.s (b, l)))⁻¹)
  refine ⟨b, c * w, hV.trans (Scheme.Hom.preimage_mono x inf_le_right), fun j => ?_⟩
  have e := congrArg (valR x (A.U l ⊓ B.U b)) (secOfIso_spec (t j) hu hA hB l b)
  rw [valR_rs_eq_valR x _ hV] at e
  unfold isoCand at e
  rw [valR_mul_lemma_2 x _ hV, valR_rs_eq_valR x _ hV] at e
  show v j = _
  rw [hv j]
  show (c : R) * valR x (A.U l) ((secOfIso (t j) hu hA hB).f l) = _
  rw [e, ← hw, Units.val_mul]
  ring

theorem pow_chart_le (L : LB X) (N : ℕ) (g : Y ⟶ X) (j : Fin 1 → L.ι) :
    (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => (N : ℤ))).U j ≤ g ⁻¹ᵁ (lbPow L N).U (fun _ => j 0) := by
  intro y hy
  have h0 := (mem_wchart (φ := fun _ : Fin 1 => g)).1 hy 0
  exact (mem_wchart (φ := fun _ : PUnit => 𝟙 X)).2 fun _ => h0

def pullPow {L : LB X} {N : ℕ} (g : Y ⟶ X) (t : (lbPow L N).Sec) :
    (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => (N : ℤ))).Sec where
  f j := (g.appLE _ _ (pow_chart_le L N g j)).hom (t.f (fun _ => j 0))
  compat j j' := fn_ext fun y hy => by
    have h₁ := pow_chart_le L N g j hy.1
    have h₂ := pow_chart_le L N g j' hy.2
    have e := sec_trans t g y h₁ h₂
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_appLE g _ _ _ (𝟙 Y) y hy.1,
      gs_appLE g _ _ _ (𝟙 Y) y hy.2, Category.id_comp, gs_unit _ y _ hy]
    refine e.trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
    refine Eq.trans ?_ (gm_linComb L (K := Fin 1) (fun _ => g) (fun _ => (N : ℤ)) (𝟙 Y) y j j' hy.1 hy.2).symm
    simp only [Geo.Tor.trF, Fintype.prod_unique, Category.comp_id, Category.id_comp]
    rfl

theorem crd_pullPow {L : LB X} {N : ℕ} (g : Y ⟶ X) (t : I → (lbPow L N).Sec) {x : Sp R ⟶ Y} {v : I → R}
    (h : Crd _ (fun i => pullPow g (t i)) x v) : Crd (lbPow L N) t (x ≫ g) v := by
  obtain ⟨l, c, hl, hv⟩ := h
  refine ⟨fun _ => l 0, c, fun p _ => pow_chart_le L N g l (hl trivial), fun i => ?_⟩
  rw [hv i]
  exact congrArg (fun r => (c : R) * r) (valR_appLE x g _ _ (pow_chart_le L N g l) hl ((t i).f fun _ => l 0))

theorem exists_transport {L : LB X} {M : LB X'} (hL : L.IsLB) (hM : M.IsLB)
    (g : Y ⟶ X) (gi : X ⟶ Y) (e₁ : gi ≫ g = 𝟙 X) (e₂ : g ≫ gi = 𝟙 Y) (p : Y ⟶ X')
    (H : LBIso (L.pull g) (M.pull p)) (k : ℕ) (t : I → (lbPow L k).Sec) :
    ∃ s : I → (LB.LinComb M (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))).Sec,
      ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ Y) (v : I → R), Crd _ s x v →
        Crd (lbPow L k) t (x ≫ g) v := by
  obtain ⟨w', hw'⟩ := LBIso.symm H
  obtain ⟨u, hu⟩ := H
  have hA : (LB.LinComb M (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))).IsLB := linComb_isLB M hM _ _
  have hC : (LB.LinComb (L.pull g) (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (k : ℤ))).IsLB :=
    linComb_isLB _ (pull_isLB hL g) _ _
  have hD : (LB.LinComb (M.pull p) (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (k : ℤ))).IsLB :=
    linComb_isLB _ (pull_isLB hM p) _ _
  have hB : (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => (k : ℤ))).IsLB := linComb_isLB L hL _ _
  have h1 : LBIso (LB.LinComb (L.pull g) (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (k : ℤ)))
      (LB.LinComb M (K := Fin 1) (fun _ => 𝟙 Y ≫ p) (fun _ => (k : ℤ))) :=
    iso_linComb ((isGen_iff u).1 hu) _ _
  have h2 : LBIso (LB.LinComb (M.pull p) (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (k : ℤ)))
      (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 Y ≫ g) (fun _ => (k : ℤ))) :=
    iso_linComb ((isGen_iff w').1 hw') _ _
  have h3 : LBIso (LB.LinComb (L.pull g) (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (k : ℤ)))
      (LB.LinComb (M.pull p) (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (k : ℤ))) :=
    ⟨LB.linCombIso u _ _, DVR.linCombIso_isGen u hu _ _⟩
  simp only [Category.id_comp] at h1 h2
  obtain ⟨w, hw⟩ := LBIso.trans hA hC hB (LBIso.symm h1) (LBIso.trans hC hD hB h3 h2)
  exact ⟨fun i => secOfIso (pullPow g (t i)) hw hA hB, fun R _ _ x v h =>
    crd_pullPow g t (crd_secOfIso hw hA hB (fun i => pullPow g (t i)) h)⟩

theorem valR_constHom {K : Type} [CommRing K] (π : Y ⟶ Sp K) (x : Sp R ⟶ Y) (ψ : K →+* R) (hx : x ≫ π = spMap ψ)
    (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : K) : valHom x U h (constHom π U a) = ψ a := by
  unfold valHom constHom
  have e1 : Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ x.appLE U ⊤ h = x.appTop := by
    rw [Scheme.Hom.map_appLE]
    rfl
  have key : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ π.appTop ≫
      (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ x.appLE U ⊤ h) ≫
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom = CommRingCat.ofHom ψ := by
    rw [e1, ← Category.assoc π.appTop, ← Scheme.Hom.comp_appTop, hx, spMap, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  exact congrArg (fun φ => φ.hom a) key

theorem crd_comb {V K : Type} [CommRing V] [CommRing K] {L : LB X} {T : Type} [Fintype T] {φ : T → (X' ⟶ X)}
    {φ' : T → (Y ⟶ X)} {ε : T → ℤ} {π : X' ⟶ Sp V} {π' : Y ⟶ Sp K} {f : V →+* K} {p : Y ⟶ X'}
    (hp : p ≫ π = π' ≫ spMap f) (hφ : ∀ k, φ' k = p ≫ φ k) {J : Type} [Fintype J]
    (σ : J → SecOver π (LB.LinComb L φ ε)) (s : I → SecOver π' (LB.LinComb L φ' ε)) (a : I → J → K)
    (hs : ∀ i, s i = ∑ j, a i j • pullOver L ε hp hφ (σ j)) (x : Sp R ⟶ Y) (ψ : K →+* R) (hx : x ≫ π' = spMap ψ)
    {w : J → R} (h : Crd (LB.LinComb L φ ε) σ (x ≫ p) w) :
    Crd (LB.LinComb L φ' ε) s x (fun i => ∑ j, ψ (a i j) * w j) := by
  obtain ⟨l, c, hl, hw⟩ := h
  have hl' : ⊤ ≤ x ⁻¹ᵁ (LB.LinComb L φ' ε).U l := fun q _ => (wchart_eq hφ l).ge (hl trivial)
  refine ⟨l, c, hl', fun i => ?_⟩
  have hpull : ∀ j, valR x ((LB.LinComb L φ' ε).U l) (LB.Sec.f (pullOver L ε hp hφ (σ j)) l) =
      valR (x ≫ p) ((LB.LinComb L φ ε).U l) (LB.Sec.f (σ j) l) := by
    intro j
    refine (valR_rs_eq_valR x (wchart_eq hφ l).le hl' ((p.app _).hom (LB.Sec.f (σ j) l))).trans ?_
    rw [Scheme.Hom.app_eq_appLE]
    exact valR_appLE x p _ _ le_rfl (fun q _ => hl trivial) _
  have hconst : ∀ k : K, valR x ((LB.LinComb L φ' ε).U l) (constHom π' _ k) = ψ k := by
    intro k
    rw [← valR_constHom π' x ψ hx _ hl' k]
    unfold valHom
    rw [valR, dif_pos hl']
    rfl
  have hsum : (LB.Sec.f (s i) l : Γ(Y, (LB.LinComb L φ' ε).U l)) =
      ∑ j, constHom π' _ (a i j) * LB.Sec.f (pullOver L ε hp hφ (σ j)) l := by
    rw [hs i]
    show chartLin π' _ l (∑ j, a i j • pullOver L ε hp hφ (σ j)) = _
    rw [map_sum]
    simp only [map_smul, Algebra.smul_def]
    rfl
  have hadd : ∀ f : J → Γ(Y, (LB.LinComb L φ' ε).U l),
      valR x ((LB.LinComb L φ' ε).U l) (∑ j, f j) = ∑ j, valR x ((LB.LinComb L φ' ε).U l) (f j) := by
    intro f
    simp only [valR, dif_pos hl', map_sum]
  show ∑ j, ψ (a i j) * w j = (c : R) * valR x _ (LB.Sec.f (s i) l)
  rw [hsum, hadd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [valR_mul_lemma_2 x _ hl', hconst, hpull, hw j]
  ring

end GlobalTheory.ZH.CrdMove
