import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueLimit

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.SecLimit

section Twist

variable {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (k : ℕ) (α : D.X)

abbrev twφ (T : Over (Spec (CommRingCat.of V))) : Fin 2 → ((T ⊗ D.P.A).left ⟶ D.P.A.left) :=
  ![(snd T D.P.A).left, (translPt D.P.A (toUnit T ≫ D.c α)).left]

abbrev ptφ : Fin 2 → (Spec (CommRingCat.of V) ⟶ D.P.A.left) := ![(D.c α).left, (η[D.P.A]).left]

abbrev famVals {Y : Scheme.{0}} (π : Y ⟶ D.P.A.left) : Set (Vals D.P.L Y) :=
  secVals D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε k)

variable {D k α}

theorem mul_mem_famVals (u : LB.Gen (LB.LinComb D.P.L (ptφ D α) ![-1, 1])) (hu : u.IsGen)
    (T : Over (Spec (CommRingCat.of V))) {Y : Scheme.{0}} (h : Y ⟶ (T ⊗ D.P.A).left) {π : Y ⟶ D.P.A.left}
    (hπ : h ≫ (snd T D.P.A).left = π) (w : Vals D.P.L Y) :
    w * evU (LB.pullGen D.P.L _ _ u (π ≫ D.P.A.hom)) ∈ famVals D k α π ↔
      w ∈ secVals D.P.L (fun j => h ≫ twφ D α T j) ![(k : ℤ) - 1, 1] := by
  have hZ : h ≫ (T ⊗ D.P.A).hom = π ≫ D.P.A.hom := by
    rw [← Over.w (snd T D.P.A), ← Category.assoc, hπ]
  let Z : Over (Spec (CommRingCat.of V)) := Over.mk (π ≫ D.P.A.hom)
  let hO : Z ⟶ T ⊗ D.P.A := Over.homMk h hZ
  let πO : Z ⟶ D.P.A := Over.homMk π
  have h1 : hO ≫ snd T D.P.A = πO := by
    ext
    simpa [hO, πO] using hπ
  have e1 : hO ≫ translPt D.P.A (toUnit T ≫ D.c α) = πO ≫ padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c α) := by
    unfold translPt padd
    simp only [comp_lift_assoc, comp_toUnit_assoc, h1, Category.comp_id]
    exact mul_comm (toUnit Z ≫ D.c α) πO
  have hmor : h ≫ (translPt D.P.A (toUnit T ≫ D.c α)).left =
      π ≫ (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c α)).left := by
    have e2 := congrArg Over.Hom.left e1
    simpa [hO, πO] using e2
  refine mul_mem_iff D.P.isLB _ (DVR.pullGen_isGen _ _ _ u hu _) ?_ w
  intro U _ g
  have hπ' : h ≫ pullback.snd T.hom D.P.A.hom = π := hπ
  simp [Fintype.prod_sum_type, Fin.prod_univ_four, twφ, ptφ, DegPre.famφB, DegPre.famε, hmor, hπ',
    Over.toUnit_left]
  exact (mul_assoc _ _ _).symm

theorem isPullback_snd (T : Over (Spec (CommRingCat.of V))) :
    IsPullback (snd T D.P.A).left (fst T D.P.A).left D.P.A.hom T.hom := by
  rw [Over.snd_left, Over.fst_left]
  exact (IsPullback.of_hasPullback T.hom D.P.A.hom).flip

set_option maxHeartbeats 1600000 in
private theorem exists_isBas_famVals_of_isPullback [IsLocalRing V] (hT : SecTwistSt) (hk : 1 ≤ k) {R : Type} [CommRing R] [IsLocalRing R]
    {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of V)} {Y : Scheme.{0}} {π : Y ⟶ D.P.A.left}
    {f : Y ⟶ Spec (CommRingCat.of R)} (H : IsPullback π f D.P.A.hom t) :
    ∃ b : Fin (k ^ D.P.g) → Vals D.P.L Y, IsBas (cst D.P.L f) (famVals D k α π) b := by
  obtain ⟨b0, hb0⟩ := (hT _ D.P k hk R t (toUnit (Over.mk t) ≫ D.c α)).1
  obtain ⟨u, hu⟩ := DVR.exists_gen_of_local D.P.L D.P.isLB (ptφ D α) ![-1, 1]
  let e := H.flip.isoPullback
  have hπ : e.hom ≫ (snd (Over.mk t) D.P.A).left = π := H.flip.isoPullback_hom_snd
  have hf : e.hom ≫ (fst (Over.mk t) D.P.A).left = f := H.flip.isoPullback_hom_fst
  let gR : R →+* Γ((Over.mk t ⊗ D.P.A).left, ⊤) :=
    (fst (Over.mk t) D.P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hb1 : IsBas ((fn D.P.L _).comp gR) (secVals D.P.L (twφ D α (Over.mk t)) ![(k : ℤ) - 1, 1])
      (fun i => ev (b0 i)) := by
    refine isBas_of_comb D.P.isLB gR b0 (fun s => ?_)
    obtain ⟨r, hr, hru⟩ := hb0 s
    refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (r i), fun j => ?_, fun a ha => ?_⟩
    · rw [hr j]
      simp [gR, resTop]
      try rfl
    · have h2 := hru (fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i))
        (fun j => by rw [ha j]; simp [gR, resTop]; try rfl)
      funext i
      rw [← h2]
      simp
  have key := fun w => mul_mem_famVals (k := k) u hu (Over.mk t) e.hom hπ w
  have hinj : Function.Injective (pull D.P.L e.hom) :=
    Function.LeftInverse.injective (g := pull D.P.L e.inv) (fun w => by rw [pull_pull, Iso.inv_hom_id, pull_id])
  have hS : ∀ s', s' ∈ famVals D k α π ↔
      ∃ s ∈ secVals D.P.L (twφ D α (Over.mk t)) ![(k : ℤ) - 1, 1], s' = pull D.P.L e.hom s * (evU (LB.pullGen D.P.L _ _ u (π ≫ D.P.A.hom))) := by
    intro s'
    constructor
    · intro hs'
      refine ⟨pull D.P.L e.inv (s' * ↑(evU (LB.pullGen D.P.L _ _ u (π ≫ D.P.A.hom)))⁻¹), pull_mem ((key _).1 (by rw [Units.inv_mul_cancel_right]; exact hs')) e.inv (fun j => by simp), ?_⟩
      rw [pull_pull, Iso.hom_inv_id, pull_id, Units.inv_mul_cancel_right]
    · rintro ⟨s, hs, rfl⟩
      exact (key _).2 (pull_mem hs e.hom (fun j => rfl))
  exact ⟨_, IsBas.transfer (fun a => pull_cst (RingHom.id R) (by simpa using hf) a) hinj (evU (LB.pullGen D.P.L _ _ u (π ≫ D.P.A.hom))) hS hb1⟩

variable [IsLocalRing V]

theorem exists_isBas (hT : SecTwistSt) (hk : 1 ≤ k) {R : Type} [CommRing R] [IsLocalRing R]
    {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of V)} {Y : Scheme.{0}} {π : Y ⟶ D.P.A.left}
    {f : Y ⟶ Spec (CommRingCat.of R)} (H : IsPullback π f D.P.A.hom t) :
    ∃ b : Fin (k ^ D.P.g) → Vals D.P.L Y, IsBas (cst D.P.L f) (famVals D k α π) b := exists_isBas_famVals_of_isPullback hT hk H

abbrev resPt (V : Type) [CommRing V] [IsLocalRing V] : Over (Spec (CommRingCat.of V)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) ≫ 𝟙 _)

theorem exists_lift (hT : SecTwistSt) (hk : 1 ≤ k) (w : Vals D.P.L (resPt V ⊗ D.P.A).left)
    (hw : w ∈ famVals D k α (snd (resPt V) D.P.A).left) :
    ∃ s ∈ famVals D k α (𝟙 _), w = pull D.P.L (snd (resPt V) D.P.A).left s := by
  obtain ⟨u, hu⟩ := DVR.exists_gen_of_local D.P.L D.P.isLB (ptφ D α) ![-1, 1]
  have keyX := fun v => mul_mem_famVals (k := k) u hu (resPt V) (𝟙 _) (π := (snd (resPt V) D.P.A).left)
    (Category.id_comp _) v
  have hw1 := (keyX (w * ↑(evU (LB.pullGen D.P.L _ _ u ((snd (resPt V) D.P.A).left ≫ D.P.A.hom)))⁻¹)).1
    (by rw [Units.inv_mul_cancel_right]; exact hw)
  let whisk : resPt V ⊗ D.P.A ⟶ Over.mk (𝟙 (Spec (CommRingCat.of V))) ⊗ D.P.A :=
    Over.homMk (V := Over.mk (𝟙 (Spec (CommRingCat.of V)))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
      rfl ▷ D.P.A
  have ht0 : whisk ≫ snd _ D.P.A = snd (resPt V) D.P.A := whiskerRight_snd _ _
  have ht1 : whisk ≫ translPt D.P.A (toUnit _ ≫ D.c α) = translPt D.P.A (toUnit (resPt V) ≫ D.c α) := by
    simp only [whisk, translPt, comp_lift_assoc, whiskerRight_snd, comp_toUnit_assoc]
  have hφ : (fun j => 𝟙 _ ≫ twφ D α (resPt V) j) = fun j => whisk.left ≫
      ![(snd (Over.mk (𝟙 (Spec (CommRingCat.of V)))) D.P.A).left,
        (translPt D.P.A (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of V)))) ≫ D.c α)).left] j := by
    funext j
    match j with
    | 0 =>
      simp only [twφ, Matrix.cons_val_zero, Category.id_comp]
      rw [← Over.comp_left, ht0]
    | 1 =>
      simp only [twφ, Matrix.cons_val_one, Matrix.cons_val_zero, Category.id_comp]
      rw [← Over.comp_left, ht1]
  rw [hφ] at hw1
  obtain ⟨sbar, hsbar⟩ := hw1
  obtain ⟨s, hs⟩ := (hT _ D.P k hk V (𝟙 _) (toUnit _ ≫ D.c α)).2 sbar
  have hps : sbar = DVR.pullSec D.P.L _ _ s whisk.left := DVR.SecOps.sec_ext (fun j => hs j)
  have hev : ev sbar = pull D.P.L whisk.left (ev s) := by
    rw [hps]
    exact ev_pullSec _ _
  let i : D.P.A.left ⟶ (Over.mk (𝟙 (Spec (CommRingCat.of V))) ⊗ D.P.A).left :=
    pullback.lift D.P.A.hom (𝟙 _) (by simp)
  have hi : i ≫ (snd (Over.mk (𝟙 (Spec (CommRingCat.of V)))) D.P.A).left = 𝟙 _ := pullback.lift_snd _ _ _
  have key0 := fun v => mul_mem_famVals (k := k) u hu (Over.mk (𝟙 (Spec (CommRingCat.of V)))) i hi v
  refine ⟨pull D.P.L i (ev s) * ↑(evU (LB.pullGen D.P.L _ _ u (𝟙 _ ≫ D.P.A.hom))),
    (key0 _).2 (pull_mem ⟨s, rfl⟩ i (fun j => rfl)), ?_⟩
  have hc := pullback.condition (f := (resPt V).hom) (g := D.P.A.hom)
  have hsi : (snd (resPt V) D.P.A).left ≫ i = whisk.left := by
    apply pullback.hom_ext
    · simp only [Category.assoc, i, pullback.lift_fst, whisk, Over.whiskerRight_left_fst]
      simpa using hc.symm
    · simp only [Category.assoc, i, pullback.lift_snd, Category.comp_id, whisk, Over.whiskerRight_left_snd]
      rfl
  rw [map_mul, pull_pull, hsi, ← hev, hsbar, pull_evU, pull_pull, Category.id_comp, ← pull_evU,
    Units.inv_mul_cancel_right]

theorem isBas_thick (hT : SecTwistSt) (hk : 1 ≤ k) {b : Fin (k ^ D.P.g) → Vals D.P.L D.P.A.left}
    (hb : IsBas (cst D.P.L D.P.A.hom) (famVals D k α (𝟙 _)) b) (e : ℕ) :
    IsBas (cst D.P.L (pullback.snd D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e)))
      (famVals D k α (pullback.fst D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e)))
      (fun i => pull D.P.L (pullback.fst D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e)) (b i)) := by
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal V).ne_top
      (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let g' : V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1) →+* IsLocalRing.ResidueField V :=
    Ideal.Quotient.lift _ (IsLocalRing.residue V) (fun a ha => (IsLocalRing.residue_eq_zero_iff a).2
      (Ideal.pow_le_self (Nat.succ_ne_zero e) ha))
  have hg' : ∀ v, g' (Ideal.Quotient.mk _ v) = IsLocalRing.residue V v := fun v => rfl
  have : IsLocalHom g' := ⟨fun a ha => by
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hg'] at ha
    exact (isUnit_of_map_unit (IsLocalRing.residue V) v ha).map _⟩
  have hm : (snd (resPt V) D.P.A).left ≫ D.P.A.hom =
      ((fst (resPt V) D.P.A).left ≫ Spec.map (CommRingCat.ofHom g')) ≫ thick V (IsLocalRing.maximalIdeal V) e := by
    rw [Over.w (snd (resPt V) D.P.A)]
    change pullback.fst _ _ ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) ≫ 𝟙 _) =
      (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom g')) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))
    rw [Category.comp_id, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let m := pullback.lift (snd (resPt V) D.P.A).left ((fst (resPt V) D.P.A).left ≫ Spec.map (CommRingCat.ofHom g')) hm
  obtain ⟨b', hb'⟩ := exists_isBas (α := α) hT hk
    (IsPullback.of_hasPullback D.P.A.hom (thick V (IsLocalRing.maximalIdeal V) e))
  obtain ⟨b'', hb''⟩ := exists_isBas (α := α) hT hk (isPullback_snd (D := D) (resPt V))
  refine IsBas.reduce (ρ' := pull D.P.L m) (g' := g') (fun a => pull_cst _ pullback.condition a)
    (fun a => pull_cst g' (pullback.lift_snd _ _ _) a) ?_ ?_ ?_ hb hb' hb''
  · intro s hs
    exact pull_mem hs _ (fun i => by simp)
  · intro s hs
    exact pull_mem hs m (fun i => (pullback.lift_fst_assoc _ _ _ _).symm)
  · intro s hs
    obtain ⟨s0, hs0, rfl⟩ := exists_lift hT hk s hs
    exact ⟨s0, hs0, by rw [pull_pull]; exact congrArg (fun x => pull D.P.L x s0) (pullback.lift_fst _ _ _).symm⟩

set_option maxHeartbeats 1000000 in
private theorem existsUnique_sec_of_isBas_lemma {X B : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (B ⟶ X)} {ε : K → ℤ} {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {p : B ⟶ Spec (CommRingCat.of R)} {Y : ℕ → Scheme.{0}} {π : ∀ e, Y e ⟶ B}
    {q : ∀ e, Y e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))} {θ : ∀ e, Y e ⟶ Y (e + 1)}
    (hθ : ∀ e, θ e ≫ π (e + 1) = π e) (hq : ∀ e, π e ≫ p = q e ≫ thick R I e) {m : ℕ} {b : Fin m → Vals L B}
    (hb : IsBas (cst L p) (secVals L (fun i => 𝟙 B ≫ φ i) ε) b)
    (hb' : ∀ e, IsBas (cst L (q e)) (secVals L (fun i => π e ≫ φ i) ε) (fun i => pull L (π e) (b i)))
    (f : ∀ e, LB.Sec (LB.LinComb L (fun i => π e ≫ φ i) ε))
    (hf : ∀ e z J, Good L z J → sval (f (e + 1)) (θ e) z J = sval (f e) (𝟙 _) z J) :
    ∃! s : LB.Sec (LB.LinComb L φ ε), ∀ e z J, Good L z J → sval s (π e) z J = sval (f e) (𝟙 _) z J := by
  simp only [Category.id_comp] at hb
  have hmem : ∀ e, ev (f e) ∈ secVals L (fun i => π e ≫ φ i) ε := fun e => ⟨f e, rfl⟩
  have hlim := existsUnique_limit I (T := fun e => Vals L (Y e)) (c := cst L p)
    (c' := fun e => cst L (q e)) (ρ := fun e => pull L (π e)) (τ := fun e => pull L (θ e))
    (fun e a => pull_cst (Ideal.Quotient.mk (I ^ (e + 1))) (by rw [hq e]) a)
    (fun e w => by simp only [pull_pull, hθ])
    (S := secVals L φ ε) (S' := fun e => secVals L (fun i => π e ≫ φ i) ε)
    (fun z => comb_mem (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) z hb.1) hb hb'
    (fun e => ev (f e)) hmem
    (fun e => secVals_ext hL (pull_mem (hmem (e + 1)) (θ e) (fun j => by simp only [← Category.assoc, hθ]))
      (hmem e) (fun y J => by
        change sval (f (e + 1)) (𝟙 _ ≫ θ e) y J.1 = sval (f e) (𝟙 _) y J.1
        rw [Category.id_comp]; exact hf e y J.1 J.2))
  obtain ⟨w, ⟨⟨s, rfl⟩, hwf⟩, hwu⟩ := hlim
  refine ⟨s, fun e z J hJ => ?_, fun s' hs' => ?_⟩
  · have h1 := congrFun (congrFun (congrFun (congrFun (hwf e) (Y e)) (𝟙 _)) z) ⟨J, hJ⟩
    change sval s (𝟙 _ ≫ π e) z J = sval (f e) (𝟙 _) z J at h1
    rwa [Category.id_comp] at h1
  · have hev : ev s' = ev s := hwu (ev s') ⟨⟨s', rfl⟩, fun e => secVals_ext hL
      (pull_mem ⟨s', rfl⟩ (π e) (fun j => rfl)) (hmem e) (fun y J => by
        change sval s' (𝟙 _ ≫ π e) y J.1 = sval (f e) (𝟙 _) y J.1
        rw [Category.id_comp]; exact hs' e y J.1 J.2)⟩
    exact eq_of_val hL (fun y J => by rw [hev])

end Twist

theorem existsUnique_sec_of_isBas {X B : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (B ⟶ X)} {ε : K → ℤ} {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {p : B ⟶ Spec (CommRingCat.of R)} {Y : ℕ → Scheme.{0}} {π : ∀ e, Y e ⟶ B}
    {q : ∀ e, Y e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))} {θ : ∀ e, Y e ⟶ Y (e + 1)}
    (hθ : ∀ e, θ e ≫ π (e + 1) = π e) (hq : ∀ e, π e ≫ p = q e ≫ thick R I e) {m : ℕ} {b : Fin m → Vals L B}
    (hb : IsBas (cst L p) (secVals L (fun i => 𝟙 B ≫ φ i) ε) b)
    (hb' : ∀ e, IsBas (cst L (q e)) (secVals L (fun i => π e ≫ φ i) ε) (fun i => pull L (π e) (b i)))
    (f : ∀ e, LB.Sec (LB.LinComb L (fun i => π e ≫ φ i) ε))
    (hf : ∀ e z J, Good L z J → sval (f (e + 1)) (θ e) z J = sval (f e) (𝟙 _) z J) :
    ∃! s : LB.Sec (LB.LinComb L φ ε), ∀ e z J, Good L z J → sval s (π e) z J = sval (f e) (𝟙 _) z J := existsUnique_sec_of_isBas_lemma hL I hθ hq hb hb' f hf

theorem existsUnique_sec_of_compatible : Laws → Laws2 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ), 1 ≤ k → ∀ (α : D.X) (f : ∀ e, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe (IsLocalRing.maximalIdeal V) e).left ≫ D.famφB α i) (DegPre.famε k))), (∀ e z J, Good D.P.L z J → sval (f (e + 1)) (thickMap V _ e D.P.A) z J = sval (f e) (𝟙 _) z J) → ∃! s : D.SecB k α, ∀ e z J, Good D.P.L z J → sval s (D.prBe (IsLocalRing.maximalIdeal V) e).left z J = sval (f e) (𝟙 _) z J) := by
  intro _ hL2 V _ _ _ hV D k hk α f hf
  have hT : SecTwistSt := by
    obtain ⟨⟩ := hL2
    assumption
  have : IsAdicComplete (IsLocalRing.maximalIdeal V) V := hV.2.1
  obtain ⟨b, hb⟩ := exists_isBas (α := α) (R := V) (t := 𝟙 _) hT hk
    (IsPullback.of_horiz_isIso (fst := 𝟙 D.P.A.left) (snd := D.P.A.hom) ⟨by simp⟩)
  exact existsUnique_sec_of_isBas D.P.isLB (IsLocalRing.maximalIdeal V) (p := D.P.A.hom)
    (π := fun e => (D.prBe (IsLocalRing.maximalIdeal V) e).left)
    (q := fun e => (thickObj V (IsLocalRing.maximalIdeal V) e D.P.A).hom)
    (θ := fun e => thickMap V (IsLocalRing.maximalIdeal V) e D.P.A)
    (fun e => by
      simp [thickMap, DegPre.prBe]
      exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)) (fun e => pullback.condition) hb
    (fun e => isBas_thick hT hk hb e) f hf

end GlobalTheory.SecLimit
