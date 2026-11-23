import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesIsoFieldPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitGeneratingSectionPullbackField

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.IdentifiedValues
open GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport GlobalTheory.ValuesPullIso
open GlobalTheory.PsiEvenPull (proj)
open ReciprocityTheory.ChartRestriction.G.DVR (cP)

section Symm
variable {O : Type} [CommRing O] {N N' : NumD O}

def invIso (I : NumD.Iso N' N) : NumD.Iso N N' where
  φ := I.φ.symm
  h x := (I.h (I.φ.symm x))⁻¹
  h_one := by rw [map_one, I.h_one, inv_one]
  θ_eq x y u := by
    have k := congrArg Additive.ofMul (I.θ_eq (I.φ.symm x) (I.φ.symm y) (I.φ.symm u))
    apply Additive.ofMul.injective
    simp only [MulEquiv.apply_symm_apply, map_mul, ofMul_mul, ofMul_inv] at k ⊢
    linear_combination (norm := abel) -k
  σ_eq x := by
    have k := congrArg Additive.ofMul (I.σ_eq (I.φ.symm x))
    apply Additive.ofMul.injective
    simp only [MulEquiv.apply_symm_apply, map_inv, ofMul_mul, ofMul_inv] at k ⊢
    linear_combination (norm := abel) -k
  lam := I.lam⁻¹
  th_eq x := by
    have k := I.th_eq (I.φ.symm x)
    rw [MulEquiv.apply_symm_apply] at k
    rw [k, ← mul_inv, Units.inv_mul_cancel_left]
  e := I.e.symm
  c_eq χ := by rw [MulEquiv.eq_symm_apply, ← I.c_eq, AddEquiv.apply_symm_apply]
  ψ_eq χ := by
    obtain ⟨χ, rfl⟩ := I.e.surjective χ
    rw [AddEquiv.symm_apply_apply, I.c_eq, MulEquiv.symm_apply_apply, ← I.ψ_eq, mul_inv_cancel_right]

theorem rel_invIso (I : NumD.Iso N' N) {c' : N'.Gt} {c : N.Gt} (h : I.Rel c' c) : (invIso I).Rel c c' := by
  refine ⟨(I.φ.eq_symm_apply.2 h.1.symm :), fun χ => ?_⟩
  obtain ⟨χ, rfl⟩ := I.e.surjective χ
  have k := congrArg Additive.ofMul (h.2 χ)
  show c'.s (I.e.symm (I.e χ)) * (I.h (I.φ.symm (N.c (I.e χ) * c.b)))⁻¹ =
    c.s (I.e χ) * (I.h (I.φ.symm (N.c (I.e χ))))⁻¹ * (I.h (I.φ.symm c.b))⁻¹
  apply Additive.ofMul.injective
  simp only [I.c_eq, h.1, ← map_mul, MulEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, ofMul_mul, ofMul_inv] at k ⊢
  linear_combination (norm := abel) -k
end Symm

theorem exists_iso_inv {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {w : LB.Iso L' (L.pull Φ)}
    (hw : w.IsGen) (a : Y ⟶ X) (b : Y ⟶ X') (hab : b ≫ Φ = a) : ∃ w' : LB.Iso (L.pull a) (L'.pull b), w'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) j k, (r ≫ a) z ∈ L.U j → (r ≫ b) z ∈ L'.U k →
        gw w' r z k (fun _ => j) = (gw w (r ≫ b) z j k)⁻¹ := by
  subst hab
  have le : ∀ p : (PUnit → L'.ι) × (PUnit → L.ι), (L'.pull b).U p.1 ⊓ (L.pull (b ≫ Φ)).U p.2 ≤
      b ⁻¹ᵁ ((L.pull Φ).U p.2 ⊓ L'.U (p.1 PUnit.unit)) := fun p y hy =>
    ⟨mem_pull.2 (mem_pull.1 (show y ∈ (L.pull (b ≫ Φ)).U p.2 from hy.2) :), mem_pull.1 hy.1⟩
  let w' : LB.Iso (L.pull (b ≫ Φ)) (L'.pull b) := ⟨fun p => (res (le p) (pullU b _ (w.s (p.2, p.1 PUnit.unit))))⁻¹⟩
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) k (j : PUnit → L.ι), Φ (b (r z)) ∈ L.U (j PUnit.unit) →
      b (r z) ∈ L'.U k → gw w' r z k j = (gw w (r ≫ b) z (j PUnit.unit) k)⁻¹ := fun Z r z k j hj hk =>
    have m : r z ∈ (L'.pull b).U (fun _ => k) ⊓ (L.pull (b ≫ Φ)).U j := ⟨mem_pull.2 hk, mem_pull.2 hj⟩
    (map_inv _ _).trans (congrArg (·⁻¹)
      ((gm_res r z (le (fun _ => k, j)) m _).trans (gm_pull r b z _ (le (fun _ => k, j) m) _)))
  refine ⟨w', (isGen_iff _).2 fun Z r z k k' j j' hk hk' hj hj' => ?_, fun Z r z j k => v Z r z k fun _ => j⟩
  rw [v Z r z k j (mem_pull.1 hj :) hk, v Z r z k' j' (mem_pull.1 hj' :) hk', gm_pull_g L (b ≫ Φ) r z j j' hj hj',
    ← Category.assoc, (isGen_iff _).1 hw Z (r ≫ b) z _ _ k k' (mem_pull.1 hj :) (mem_pull.1 hj' :) hk hk']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

section Pull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {F : Type} [Field F] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R') F]

theorem exists_lam (hφ : φ.Flat) {N N' : NumD F} (ν : NumOf D F N) (ν' : NumOf D' F N') (z : Sp F) :
    ∃ lam : ((Sp F).presheaf.stalk z)ˣ, ∀ x : TF (R := R') F ⟶ D'.P.A,
      sval (Z := Sp F) ν.th (x.left ≫ proj hD) z ν.J =
        (lam * om hD.w z ν.J ν'.J x.left).val * sval (Z := Sp F) ν'.th x.left z ν'.J := by
  have hc : ∀ _ : Fin 1, 𝟙 D'.P.A.left ≫ proj hD = proj hD ≫ 𝟙 D.P.A.left :=
    fun _ => (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L _ D.P.isLB D'.P.isLB hD.w hD.w_gen (Fin 1)
    (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)) (proj hD) hc ν.th
  obtain ⟨c, hac⟩ := ν'.th_gen a
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      sval ν.th (r ≫ proj hD) z J =
        cst (r ≫ D'.P.A.hom) z c * (om hD.w z J J' r).val * sval ν'.th r z J' := fun Z r z J J' hJ hJ' => by
    have e := FamFieldPull.IsSecPull.val ha hc r z hJ hJ'
    rw [IndivisibleSection.sval_of_secIsMul (p := D'.P.A.hom) hac r z hJ', Fin.prod_univ_one, Category.comp_id,
      zpow_natCast, pow_one] at e
    exact e.trans ((mul_left_comm _ _ _).trans (_root_.mul_assoc _ _ _).symm)
  by_cases h : c = 0
  · subst h
    have : IsProper D.P.A.hom := D.P.isAb.proper
    have : CompactSpace D.P.A.left := QuasiCompact.compactSpace_of_compactSpace D.P.A.hom
    have : QuasiSeparatedSpace D.P.A.left := quasiSeparatedSpace_of_quasiSeparated D.P.A.hom
    have h₀ : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul D'.P.A.hom (0 : R') ν'.th ν'.th :=
      IndivisibleSection.secIsMul_of_sval D'.P.isLB fun y J' hJ' => by
      rw [GenSecField.cst_zero', zero_mul]
      refine GenSecField.sval_eq_zero hφ (pull_grp hD).1 D.P.isLB D'.P.isLB hD.w_gen ν.th_gen
        (fun x J hJ => ?_) ν'.th y hJ'
      obtain ⟨I, hI⟩ := DegPull.exists_good' D'.P.isLB x
      have e := key _ (𝟙 _) x J I hJ hI
      rwa [Category.id_comp, GenSecField.cst_zero', zero_mul, zero_mul] at e
    refine ⟨1, fun x => ?_⟩
    have e := key (Sp F) x.left z ν.J ν'.J (good ν z) (good ν' z)
    rw [IndivisibleSection.sval_of_secIsMul h₀ _ z (good ν' z), GenSecField.cst_zero', zero_mul, zero_mul] at e
    have e' := IndivisibleSection.sval_of_secIsMul h₀ (show Sp F ⟶ _ from x.left) z (good ν' z)
    rw [GenSecField.cst_zero', zero_mul] at e'
    exact e.trans ((congrArg _ e').trans (mul_zero _)).symm
  · let u : (FractionRing R')ˣ := Units.mk0 (algebraMap R' _ c) fun e =>
      h (IsFractionRing.injective R' (FractionRing R') (e.trans (map_zero _).symm))
    refine ⟨TauTwist.unitAt (Z := Sp F) (jFK (R := R') F) z u, fun x => ?_⟩
    refine (key (Sp F) x.left z ν.J ν'.J (good ν z) (good ν' z)).trans (congrArg₂ (· * ·) ?_ rfl)
    rw [Units.val_mul, TauTwist.unitAt_val]
    refine congrArg₂ (· * ·) ?_ rfl
    exact (congrArg (fun q => cst (Z := Sp F) q z c) (Over.w x)).trans
      (cst_comp (Z := Sp F) (jFK (R := R') F) (algebraMap R' (FractionRing R')) z c)

theorem exists_iso_om (hG : GlobalFnsSt) (hφ : φ.Flat) (hF : ArcPull.Compat φ F) {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') (z : Sp F) :
    ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧
      (∀ x, (ν.eA (I.φ x)).left = (ν'.eA x).left ≫ proj hD) ∧
      (∀ x, stalkUnits z (I.h x) = om hD.w z ν.J ν'.J (ν'.eA x).left * (om hD.w z ν.J ν'.J (ν'.eA 1).left)⁻¹) ∧
      ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' →
        IsPullGtF φ hD F g g' → I.Rel c' c := by
  obtain ⟨lam, hth⟩ := exists_lam hD hφ ν ν' z
  have hJ := good ν z
  have hJ' := good ν' z
  let Ω : (TF (R := R') F ⟶ D'.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun x => om hD.w z ν.J ν'.J x.left
  obtain ⟨h, hh⟩ : ∃ h : N'.A → Fˣ, ∀ x, stalkUnits z (h x) = Ω (ν'.eA x) * (Ω 1)⁻¹ :=
    ⟨fun x => (stalkUnits z).symm _, fun x => (stalkUnits z).apply_symm_apply _⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : N'.A ≃* N.A, ∀ x, ν.eA (Φ x) = pushF (pull_grp hD) hF.base (ν'.eA x) :=
    ⟨(ν'.eA.trans (pushEquiv hD hF)).trans ν.eA.symm, fun x => ν.eA.apply_symm_apply _⟩
  obtain ⟨e, he⟩ : ∃ e : N'.X ≃+ N.X, ∀ y, ν.eX (e y) = hD.xe (ν'.eX y) :=
    ⟨(ν'.eX.trans hD.xe).trans ν.eX.symm, fun x => ν.eX.apply_symm_apply _⟩
  have hc : ∀ χ, ν'.eA (N'.c χ) = cP D' _ (ν'.eX χ) := ν'.c_eq
  have a₁ : ∀ χ, jFK (R := R') F ≫ D'.xK χ = (cP D' (TF (R := R') F) χ).left := fun χ => (Category.assoc _ _ _).symm
  have a₂ : jFK (R := R') F ≫ (1 : TK R' ⟶ D'.P.A).left = (1 : TF (R := R') F ⟶ D'.P.A).left :=
    (Category.assoc _ _ _).symm
  have rig : val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J = Ω 1 * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J :=
    (rig_val hD (Z := Sp F) _ _ hF.sq hJ hJ').trans
      (congrArg (fun q => om hD.w z ν.J ν'.J q * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J) a₂)
  refine ⟨{
    φ := Φ, h := h, lam := (stalkUnits z).symm lam, e := e
    h_one := ?_, θ_eq := fun x y u => ?_, σ_eq := fun x => ?_, th_eq := fun x => ?_
    c_eq := fun χ => ?_, ψ_eq := fun χ => ?_ }, he, fun x => congrArg (·.left) (hΦ x),
    fun x => by rw [map_one ν'.eA]; exact hh x, fun g g' c c' hg hg' H => ⟨?_, fun χ => ?_⟩⟩
  · apply (stalkUnits z).injective
    rw [hh, map_one, map_one, mul_inv_cancel]
  · apply (stalkUnits z).injective
    have k : thS D z ν.J (pushF (pull_grp hD) hF.base (ν'.eA x)) (pushF (pull_grp hD) hF.base (ν'.eA y))
        (pushF (pull_grp hD) hF.base (ν'.eA u)) =
        Ω (ν'.eA x * ν'.eA y * ν'.eA u) * (Ω (ν'.eA x * ν'.eA y))⁻¹ * (Ω (ν'.eA x * ν'.eA u))⁻¹ *
          (Ω (ν'.eA y * ν'.eA u))⁻¹ * Ω (ν'.eA x) * Ω (ν'.eA y) * Ω (ν'.eA u) * (Ω 1)⁻¹ *
          thS D' z ν'.J (ν'.eA x) (ν'.eA y) (ν'.eA u) :=
      thS_push (pull_grp hD) hF.base ((isGen_iff _).1 hD.w_gen) hG hJ hJ' _ _ _
    simp only [map_mul, hh, stalk_θ ν, stalk_θ ν', hΦ, k]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply (stalkUnits z).injective
    have k : val (Z := Sp F) D.sym (pushF (pull_grp hD) hF.base (ν'.eA x)).left z ν.J =
        Ω (ν'.eA x)⁻¹ * (Ω (ν'.eA x))⁻¹ * val (Z := Sp F) D'.sym (ν'.eA x).left z ν'.J :=
      PsiEvenPull.sym_pull hG hD (Z := Sp F) (ν'.eA x).left z hJ hJ'
    simp only [map_mul, map_inv, hh, stalk_σ ν, stalk_σ ν', hΦ, k]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply (stalkConst z).injective
    have k := stalk_th ν z (Φ x)
    have k' := stalk_th ν' z x
    rw [hΦ, rig] at k
    have k₁ := k.trans ((hth (ν'.eA x)).trans (congrArg _ k'.symm))
    rw [map_mul, ← stalkUnits_val, map_mul, hh, MulEquiv.apply_symm_apply]
    refine (Units.mul_left_inj (Ω 1 * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J)).1 (k₁.trans ?_)
    have := (Ω 1).inv_mul
    simp only [Units.val_mul]
    linear_combination (-(lam.val * (Ω (ν'.eA x)).val * stalkConst z (N'.th x) *
      (val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J).val)) * this
  · apply ν.eA.injective
    rw [hΦ, ν.c_eq, he, hc]
    exact Over.OverMorphism.ext ((cPoint_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _)
      (hF.base.trans (Category.id_comp _).symm) _).trans (Category.id_comp _)).symm
  · apply (stalkUnits z).injective
    have k : val (Z := Sp F) (D.psi (hD.xe (ν'.eX χ))) (jFK (R := R) F) z ν.J =
        (Ω (cP D' _ (ν'.eX χ)))⁻¹ * val (Z := Sp F) (D'.psi (ν'.eX χ)) (jFK (R := R') F) z ν'.J :=
      (psi_val hD (Z := Sp F) _ _ hF.sq hJ hJ' _).trans (congrArg (fun q => (om hD.w z ν.J ν'.J q)⁻¹ *
        val (Z := Sp F) (D'.psi (ν'.eX χ)) (jFK (R := R') F) z ν'.J) (a₁ _))
    rw [map_mul, hh, stalk_ψ ν, stalk_ψ ν', he, k, rig, hc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply ν.eA.injective
    refine hg.1.trans (Eq.trans ?_ (hΦ _).symm)
    rw [hg'.1]
    exact Over.OverMorphism.ext H.1.symm
  · apply (stalkUnits z).injective
    have k₀ := pullGt_val hD H (ν'.eX χ) (𝟙 _) hJ hJ'
    simp only [Category.id_comp] at k₀
    have k : val (Z := Sp F) (g.s (hD.xe (ν'.eX χ))) (𝟙 (Sp F)) z ν.J =
        (Ω (cP D' _ (ν'.eX χ) * g'.b))⁻¹ * Ω (cP D' _ (ν'.eX χ)) * Ω g'.b * (Ω 1)⁻¹ *
          val (Z := Sp F) (g'.s (ν'.eX χ)) (𝟙 (Sp F)) z ν'.J := k₀
    show stalkUnits z (c.s (e χ) * h (N'.c χ * c'.b)) = stalkUnits z (c'.s χ * h (N'.c χ) * h c'.b)
    rw [map_mul, map_mul, map_mul, hh, hh, hh, stalk_pt ν z hg, stalk_pt ν' z hg', he, k, map_mul, hc, hg'.1]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
end Pull

theorem exists_geoIso_rel : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D D' : DegPre V) (e : IsPullDeg (RingHom.id V) D D') (F : Type) [Field F] [Algebra (FractionRing V) F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N'), ∃ J : NumD.Iso N N', GeoIso ν ν' J.toIso ∧ ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D' F k) (q : N.QT k) (q' : N'.QT k), ν.QPt p q → ν'.QPt p' q' → GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition.Carries e p p' → q'.1.1.toAdd = J.e q.1.1.toAdd ∧ J.Rel q.1.2 q'.1.2 := by
  intro hL V _ _ _ D D' e F _ _ N N' ν ν'
  let z : Sp F := IsLocalRing.closedPoint F
  have hF : ArcPull.Compat (RingHom.id V) F := fun _ => rfl
  obtain ⟨I, hX, hA, hh, hR⟩ := exists_iso_om e hL.globalFns (RingHom.Flat.id V) hF ν ν' z
  refine ⟨invIso I, ?_, fun k p p' q q' hq hq' hC => ⟨?_, rel_invIso I (hR _ _ _ _ hq.2 hq'.2 ?_)⟩⟩
  · have gp := pull_grp e
    haveI : IsMonHom (Iso.refl D.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.P.A))
    obtain ⟨Ψ, -, hΨ⟩ := grpPullback_iso
      ((isGrpPullback_of_iso (Iso.refl D.P.A)).congr (Spec.map_id _).symm rfl) gp
    replace hΨ : Ψ.hom.left ≫ proj e = 𝟙 _ := hΨ
    have hp : ∀ x, (ν'.eA (I.φ.symm x)).left ≫ proj e = (ν.eA x).left := fun x => by
      rw [← hA, MulEquiv.apply_symm_apply]
    have hx : ∀ x, ν.eA x ≫ Ψ.hom = ν'.eA (I.φ.symm x) := fun x =>
      Over.OverMorphism.ext (gp.1.hom_ext (by
        rw [Over.comp_left, Category.assoc]
        exact ((congrArg (_ ≫ ·) hΨ).trans (Category.comp_id _)).trans (hp x).symm) (by rw [Over.w, Over.w]))
    have hl : ∀ x, lift (𝟙 _) (ν.eA x) ≫ (whiskerLeftIso (TF (R := V) F) Ψ).hom = lift (𝟙 _) (ν'.eA (I.φ.symm x)) :=
      fun x => by rw [whiskerLeftIso_hom, lift_whiskerLeft, hx]
    obtain ⟨w, hw, hv⟩ := exists_iso_inv e.w_gen (snd (TF (R := V) F) D.P.A).left
      ((whiskerLeftIso (TF (R := V) F) Ψ).hom ≫ snd (TF (R := V) F) D'.P.A).left (by
        rw [whiskerLeftIso_hom, whiskerLeft_snd, Over.comp_left, Category.assoc]
        exact (congrArg (_ ≫ ·) hΨ).trans (Category.comp_id _))
    have val : ∀ x, stalkConst z (valF (lift (𝟙 (TF (R := V) F)) (ν.eA x)).left _
        (w.s (fun _ => ν'.J (ν'.eA (I.φ.symm x)).left, fun _ => ν.J (ν.eA x).left)).val) =
        ((om e.w z ν.J ν'.J (ν'.eA (I.φ.symm x)).left)⁻¹).val := fun x => by
      have l₁ : (lift (𝟙 (TF (R := V) F)) (ν.eA x)).left ≫ (snd (TF (R := V) F) D.P.A).left = (ν.eA x).left := by
        rw [← Over.comp_left, lift_snd]
      have l₂ : (lift (𝟙 (TF (R := V) F)) (ν.eA x)).left ≫
          ((whiskerLeftIso (TF (R := V) F) Ψ).hom ≫ snd (TF (R := V) F) D'.P.A).left = (ν'.eA (I.φ.symm x)).left := by
        rw [← Over.comp_left, ← Category.assoc, hl, lift_snd]
      have m₁ : ((lift (𝟙 (TF (R := V) F)) (ν.eA x)).left ≫ (snd (TF (R := V) F) D.P.A).left) z ∈
        D.P.L.U (ν.J (ν.eA x).left) := by rw [l₁]; exact good ν z _
      have m₂ : ((lift (𝟙 (TF (R := V) F)) (ν.eA x)).left ≫
          ((whiskerLeftIso (TF (R := V) F) Ψ).hom ≫ snd (TF (R := V) F) D'.P.A).left) z ∈
        D'.P.L.U (ν'.J (ν'.eA (I.φ.symm x)).left) := by rw [l₂]; exact good ν' z _
      refine (toStk_valF (lift (𝟙 (TF (R := V) F)) (ν.eA x)).left
        ((D'.P.L.pull ((whiskerLeftIso (TF (R := V) F) Ψ).hom ≫ snd (TF (R := V) F) D'.P.A).left).U
          (fun _ => ν'.J (ν'.eA (I.φ.symm x)).left) ⊓
          (D.P.L.pull (snd (TF (R := V) F) D.P.A).left).U fun _ => ν.J (ν.eA x).left) z
        ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩ _).trans ?_
      refine congrArg Units.val ((hv (Sp F) _ z _ _ m₁ m₂).trans ?_)
      rw [l₂, ← hp]
      rfl
    refine ⟨whiskerLeftIso _ Ψ, w, _, whiskerLeft_fst _ _, hw, hl, fun _ => rfl, fun x => (stalkConst z).injective ?_⟩
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (stalkUnits_val _ _).symm (val 1)).trans
      (Eq.trans ?_ (val x).symm))
    rw [← Units.val_mul]
    refine congrArg Units.val ?_
    show stalkUnits z (I.h (I.φ.symm x))⁻¹ * _ = _
    rw [map_inv, hh, map_one I.φ.symm, mul_inv, inv_inv, mul_inv_cancel_right]
  · refine (I.e.eq_symm_apply.2 (ν.eX.injective ?_) :)
    rw [hX, hq'.1, hC.1, hq.1]
  · refine (isPullGtF_iff e hF _ _).2 fun χ => ?_
    have := hC.2 (e.xe.symm χ)
    rwa [AddEquiv.apply_symm_apply] at this

end GlobalTheory.IdentifiedValues
end
