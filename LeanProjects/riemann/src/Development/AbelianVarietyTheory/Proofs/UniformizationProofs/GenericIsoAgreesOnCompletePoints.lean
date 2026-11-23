import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomExtOfSecPullEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralSectionsCorrespond
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSecKIsUnit

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalGeneric

open SectionRingIso (vl ch mem_ch)

section Limit

variable {B : Type} [CommRing B] (J : Ideal B)

theorem appTop_spec {S : Type} [CommRing S] (φ : B →+* S) (b : B) :
    (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (φ b) :=
  (congrArg (fun q => q.hom b) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm

theorem inv_bijective (S : Type) [CommRing S] :
    Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).symm.commRingCatIsoToRingEquiv.bijective

theorem fn_ext_levels [IsHausdorff J B] {a b : Γ(Spec (CommRingCat.of B), ⊤)}
    (h : ∀ e, (adicLevelι J (e + 1)).appTop.hom a = (adicLevelι J (e + 1)).appTop.hom b) : a = b := by
  obtain ⟨a, rfl⟩ := (inv_bijective B).2 a
  obtain ⟨b, rfl⟩ := (inv_bijective B).2 b
  congr 1
  refine congrFun (IsHausdorff.StrictMono.funext' J (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => a) (g := fun _ => b) fun n _ => ?_) ()
  have := h n
  rw [appTop_spec, appTop_spec] at this
  exact (inv_bijective _).1 this

theorem fn_ext_germs [IsHausdorff J B] {a b : Γ(Spec (CommRingCat.of B), ⊤)}
    (h : ∀ e z, gs (adicLevelι J (e + 1)) z ⊤ a = gs (adicLevelι J (e + 1)) z ⊤ b) : a = b :=
  fn_ext_levels J fun e => fn_ext (V := ⊤) fun z _ => by
    have e₁ := gs_pull (𝟙 _) (adicLevelι J (e + 1)) z ⊤ trivial a
    have e₂ := gs_pull (𝟙 _) (adicLevelι J (e + 1)) z ⊤ trivial b
    rw [Category.id_comp] at e₁ e₂
    exact e₁.trans ((h e z).trans e₂.symm)

theorem exists_fn_levels [IsAdicComplete J B] (a : ∀ e : ℕ, Γ(Spec (CommRingCat.of (B ⧸ J ^ (e + 1))), ⊤))
    (h : ∀ e, (adicLevelMap J (Nat.le_succ (e + 1))).appTop.hom (a (e + 1)) = a e) :
    ∃ A : Γ(Spec (CommRingCat.of B), ⊤), ∀ e, (adicLevelι J (e + 1)).appTop.hom A = a e := by
  choose b hb using fun e => (inv_bijective (B ⧸ J ^ (e + 1))).2 (a e)
  have ha : StrictMono fun n : ℕ => n + 1 := strictMono_id.add_const 1
  let φ : ∀ e : ℕ, Polynomial ℤ →+* B ⧸ J ^ (e + 1) := fun e => Polynomial.eval₂RingHom (Int.castRingHom _) (b e)
  have hφ : ∀ e, φ e Polynomial.X = b e := fun e => Polynomial.eval₂_X _ _
  have hc : ∀ {m : ℕ}, (Ideal.Quotient.factorPow J (ha.monotone m.le_succ)).comp (φ (m + 1)) = φ m := by
    intro m
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, hφ, hφ]
    have := h m
    rw [← hb, ← hb, appTop_spec] at this
    exact (inv_bijective _).1 this
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    (IsAdicComplete.StrictMono.liftRingHom J ha φ hc Polynomial.X), fun e => ?_⟩
  rw [appTop_spec, ← hb, ← hφ]
  exact congrArg _ (congrArg (fun q => q Polynomial.X)
    (IsAdicComplete.StrictMono.mk_comp_liftRingHom J ha φ hc (n := e)))

theorem exists_unit_levels [IsAdicComplete J B] (v : ∀ e : ℕ, Γ(Spec (CommRingCat.of (B ⧸ J ^ (e + 1))), ⊤)ˣ)
    (h : ∀ e z, gm (adicLevelMap J (Nat.le_succ (e + 1))) z ⊤ (v (e + 1)) = gm (𝟙 _) z ⊤ (v e)) :
    ∃ V : Γ(Spec (CommRingCat.of B), ⊤)ˣ, ∀ (e : ℕ) (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of (B ⧸ J ^ (e + 1))))
      (z : Z), gm (q ≫ adicLevelι J (e + 1)) z ⊤ V = gm q z ⊤ (v e) := by
  obtain ⟨A, hA⟩ := exists_fn_levels J (fun e => (v e).val) fun e =>
    FormalPoint.appTop_eq_of_gm _ _ _ _ (h e)
  obtain ⟨A', hA'⟩ := exists_fn_levels J (fun e => ((v e)⁻¹).val) fun e =>
    FormalPoint.appTop_eq_of_gm _ (𝟙 _) (v (e + 1))⁻¹ (v e)⁻¹ fun z => by rw [map_inv, map_inv, h]
  have e₁ : A * A' = 1 := fn_ext_levels J fun e => by
    rw [map_mul, hA, hA', map_one, Units.mul_inv]
  refine ⟨⟨A, A', e₁, (mul_comm _ _).trans e₁⟩, fun e Z q z => ?_⟩
  refine (gm_pull q _ z ⊤ trivial _).symm.trans (congrArg (gm q z ⊤) (Units.ext (hA e)))

end Limit

theorem hom_ext_of_germs {X Z : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X] {L : LB X} (hL : L.IsLB)
    {N : ℕ} (hN : 1 ≤ N) {κ : Type} (s : κ → H0 L N) (hcov : ⨆ i, nonzeroLocus (s i) = ⊤)
    (haff : ∀ i, IsAffineOpen (nonzeroLocus (s i))) (f g : Z ⟶ X)
    (H : ∀ (z : Z) (j j' : L.ι), g z ∈ L.U j → f z ∈ L.U j' → ∃ u : (Z.presheaf.stalk z)ˣ, ∀ n : ℕ, 1 ≤ n →
      ∀ a : H0 L n, gs g z _ (a.f (fun _ => j)) = (u ^ n).val * gs f z _ (a.f (fun _ => j'))) : f = g := by
  have unit : ∀ (r : Z ⟶ X) (z : Z) (k : κ) (i : L.ι), r z ∈ L.U i →
      (r z ∈ nonzeroLocus (s k) ↔ IsUnit (gs r z _ ((s k).f fun _ => i))) := fun r z k i hi =>
    SectionRingIso.mem_iff_isUnit (s k) r z (j := fun _ => i) hi
  have hfg : ∀ (k : κ) (z : Z), f z ∈ nonzeroLocus (s k) → g z ∈ nonzeroLocus (s k) := by
    intro k z hz
    obtain ⟨j, hj⟩ := exists_chart hL (g z)
    obtain ⟨j', hj'⟩ := exists_chart hL (f z)
    obtain ⟨u, hu⟩ := H z j j' hj hj'
    rw [unit g z k j hj, hu N hN (s k), Units.isUnit_units_mul]
    exact (unit f z k j' hj').1 hz
  refine Scheme.hom_ext_of_forall f g fun z => ?_
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (show f z ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
  refine ⟨f ⁻¹ᵁ nonzeroLocus (s k), hk, ι_comp_eq_of_gs_eq f g (haff k) _ le_rfl (fun y hy => hfg k y hy) ?_⟩
  intro a y hy
  have hy' := hfg k y hy
  obtain ⟨m, t, hm, ht⟩ := exists_sec_extend_pos hL (s k) a
  obtain ⟨j, hj⟩ := exists_chart hL (g y)
  obtain ⟨j', hj'⟩ := exists_chart hL (f y)
  obtain ⟨u, hu⟩ := H y j j' hj hj'
  have e₁ := hu (N * m) (Nat.mul_pos hN hm) t
  have e₂ := hu N hN (s k)
  have u := ((unit g y k j hj).1 hy').pow m
  rw [gs_pull_extend (s k) t a ht g y j hy' hj, gs_pull_extend (s k) t a ht f y j' hy hj', pow_mul,
    Units.val_pow_eq_pow_val, ← _root_.mul_assoc, ← mul_pow, ← e₂] at e₁
  exact (u.mul_left_cancel e₁).symm

theorem exists_level_iso {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {L' : LB G'}
    (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB) {Φ : B' ⟶ B} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'}
    {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'} {h : Ge' ⟶ Ge} (e₁ : pG' ≫ Φ = h ≫ pG) (w : LB.Iso M' (M.pull Φ))
    (we : LB.Iso (L.pull fG) (M.pull pG)) (we' : LB.Iso (L'.pull fG') (M'.pull pG')) (hw : w.IsGen)
    (hwe : we.IsGen) (hwe' : we'.IsGen) :
    ∃ u : LB.Iso (L'.pull fG') ((L.pull fG).pull h),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
        Φ (pG' (r z)) ∈ M.U jM → pG' (r z) ∈ M'.U jM' → fG (h (r z)) ∈ L.U jL → fG' (r z) ∈ L'.U jL' →
        Geo.Tor.gw w (r ≫ pG') z jM jM' * Geo.Tor.gw we' r z jM' (fun _ => jL') =
          Geo.Tor.gw we (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw u r z (fun _ => jL) (fun _ => jL') := by
  rw [isGen_iff] at hw hwe hwe'
  obtain ⟨w₁, T₁⟩ := exists_comp hM' w we' hw hwe' hM (LB.isLB_pull hL' fG')
  have g₁ := T₁.pgen_comp hM' hw hwe'
  obtain ⟨w₂, g₂, e₂⟩ : ∃ w₂ : LB.Iso (L'.pull fG') (M.pull (h ≫ pG)), PGen w₂ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Ge') (z : Z) j k, Geo.Tor.gw w₂ r z j k = Geo.Tor.gw w₁ r z j k := by
    clear T₁
    generalize pG' ≫ Φ = F at e₁ w₁ g₁
    subst e₁
    exact ⟨w₁, g₁, fun _ _ _ _ _ => rfl⟩
  obtain ⟨u, T₂⟩ := exists_cancel hM we w₂ hwe g₂ (LB.isLB_pull hL fG) (LB.isLB_pull hL' fG')
  refine ⟨u, fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  have a₅ : pG (h (r z)) ∈ M.U jM := (congrArg (fun q : Ge' ⟶ B => q (r z) ∈ M.U jM) e₁).mp a₁
  exact (T₁ Z r z jM jM' (fun _ => jL') a₁ a₂ (mem_pull.2 a₄)).symm.trans ((e₂ Z r z jM (fun _ => jL')).symm.trans
    (T₂ Z r z jM (fun _ => jL) (fun _ => jL') a₅ (mem_pull.2 a₃) (mem_pull.2 a₄)))

section Formal

open FormalPoint

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I D' A' G')

theorem gw_thickMap (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι)
    (jL : U.LG.L.ι) (hM : (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM) (hL : (fstG I e G).left (r z) ∈ U.LG.L.U jL) :
    Geo.Tor.gw (U.w (e + 1)) (r ≫ thickMap R I e G) z jM (fun _ => jL) =
      Geo.Tor.gw (U.w e) r z jM (fun _ => jL) := by
  have hM' : (U.gt (e + 1)).pG.left (thickMap R I e G (r z)) ∈ D.toPre.P.L.U jM :=
    (congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (U.gt_q e)).mpr hM
  have hL' : (fstG I (e + 1) G).left (thickMap R I e G (r z)) ∈ U.LG.L.U jL :=
    (congrArg (fun g => g (r z) ∈ U.LG.L.U jL) (Algebraise.thickMap_fstG I e G)).mpr hL
  have hm : r z ∈ thickMap R I e G ⁻¹ᵁ ((D.toPre.P.L.pull (U.gt (e + 1)).pG.left).U (fun _ => jM) ⊓
        (U.LG.L.pull (fstG I (e + 1) G).left).U (fun _ => jL)) ⊓
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓
        (U.LG.L.pull (fstG I e G).left).U (fun _ => jL)) :=
    ⟨⟨mem_pull.2 hM', mem_pull.2 hL'⟩, mem_pull.2 hM, mem_pull.2 hL⟩
  have H := congrArg (gm r z _) (U.w_compat e (fun _ => jM, fun _ => jL) _ inf_le_left inf_le_right)
  have h₁ := gm_pull r (thickMap R I e G) z _ hm.1 ((U.w (e + 1)).s (fun _ => jM, fun _ => jL))
  exact h₁.symm.trans ((gm_res r z inf_le_left hm _).symm.trans (H.trans (gm_res r z inf_le_right hm _)))

variable {Φ : D'.toPre.P.A.left ⟶ D.toPre.P.A.left} (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ))
  (h : ∀ e, (thickObj R I e G').left ⟶ (thickObj R I e G).left)
  {B : Type} [CommRing B] [Algebra R B] (g' : Spec (CommRingCat.of B) ⟶ G'.left)
  (g : Spec (CommRingCat.of B) ⟶ G.left) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι)

def IsRatio (v : Γ(Spec (CommRingCat.of B), ⊤)ˣ) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left) (z : Z)
    (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι), r ≫ (fstG I e G').left = ρ ≫ g' →
    Φ ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
    (fstG I e G).left (h e (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' →
    Geo.Tor.gw w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') =
      Geo.Tor.gw (U.w e) (r ≫ h e) z jM (fun _ => jL) * gm ρ z ⊤ v

theorem exists_isRatio [IsAdicComplete (I.map (algebraMap R B)) B] (hw : w.IsGen)
    (hh : ∀ e, thickMap R I e G' ≫ h (e + 1) = h e ≫ thickMap R I e G)
    (hp : ∀ e, (U'.gt e).pG.left ≫ Φ = h e ≫ (U.gt e).pG.left)
    (hg' : g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B))) (c' : ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL')
    (c : ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL)
    (hgg : ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left),
      r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ h e ≫ (fstG I e G).left = ρ ≫ g) :
    ∃ v, IsRatio U U' w h g' jL jL' v := by
  let y : Over.mk (spMap (algebraMap R B)) ⟶ G' := Over.homMk g' hg'
  have hy : ∀ e, reduction I y e ≫ (fstG I e G').left = adicLevelι (I.map (algebraMap R B)) (e + 1) ≫ g' :=
    fun e => reduction_fstG I y e
  have m₁ : ∀ e z, (fstG I e G').left (reduction I y e z) ∈ U'.LG.L.U jL' := fun e z =>
    (congrArg (fun q => q z ∈ U'.LG.L.U jL') (hy e)).mpr (c' trivial)
  have m₂ : ∀ e z, (fstG I e G).left (h e (reduction I y e z)) ∈ U.LG.L.U jL := fun e z =>
    (congrArg (fun q => q z ∈ U.LG.L.U jL) (hgg e _ _ _ (hy e))).mpr (c trivial)
  choose u hu using fun e => exists_level_iso D.toPre.P.isLB D'.toPre.P.isLB U.LG.isLB U'.LG.isLB (hp e) w (U.w e)
    (U'.w e) hw (U.w_gen e) (U'.w_gen e)
  have hO : ∀ e, ⊤ ≤ reduction I y e ⁻¹ᵁ (((U.LG.L.pull (fstG I e G).left).pull (h e)).U (fun _ _ => jL) ⊓
      (U'.LG.L.pull (fstG I e G').left).U (fun _ => jL')) := fun e z _ =>
    ⟨mem_pull.2 (mem_pull.2 (m₂ e z)), mem_pull.2 (m₁ e z)⟩
  obtain ⟨ve, hve⟩ : ∃ ve : ∀ e : ℕ, Γ(Spec (CommRingCat.of (B ⧸ I.map (algebraMap R B) ^ (e + 1))), ⊤)ˣ,
      ∀ (e : ℕ) (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of (B ⧸ I.map (algebraMap R B) ^ (e + 1)))) (z : Z),
        gm q z ⊤ (ve e) = Geo.Tor.gw (u e) (q ≫ reduction I y e) z (fun _ => jL) (fun _ => jL') :=
    ⟨fun e => res (hO e) (pullU (reduction I y e) _ ((u e).s (fun _ _ => jL, fun _ => jL'))), fun e Z q z =>
      (gm_res q z (hO e) trivial _).trans (gm_pull q (reduction I y e) z _ (hO e trivial) _)⟩
  have cu : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z),
      (fstG I e G).left (h e (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' →
      Geo.Tor.gw (u (e + 1)) (r ≫ thickMap R I e G') z (fun _ => jL) (fun _ => jL') =
        Geo.Tor.gw (u e) r z (fun _ => jL) (fun _ => jL') := by
    intro e Z r z a₃ a₄
    obtain ⟨jM, a₁⟩ := exists_chart D.toPre.P.isLB (Φ ((U'.gt e).pG.left (r z)))
    obtain ⟨jM', a₂⟩ := exists_chart D'.toPre.P.isLB ((U'.gt e).pG.left (r z))
    have k₁ : (r ≫ thickMap R I e G') ≫ (U'.gt (e + 1)).pG.left = r ≫ (U'.gt e).pG.left := by
      rw [Category.assoc, U'.gt_q]
    have k₂ : (r ≫ thickMap R I e G') ≫ h (e + 1) = (r ≫ h e) ≫ thickMap R I e G := by
      rw [Category.assoc, Category.assoc, hh]
    have k₃ : ((r ≫ thickMap R I e G') ≫ h (e + 1)) ≫ (fstG I (e + 1) G).left = (r ≫ h e) ≫ (fstG I e G).left := by
      rw [k₂, Category.assoc, Algebraise.thickMap_fstG]
    have k₄ : (r ≫ thickMap R I e G') ≫ (fstG I (e + 1) G').left = r ≫ (fstG I e G').left := by
      rw [Category.assoc, Algebraise.thickMap_fstG]
    have a := hu (e + 1) Z (r ≫ thickMap R I e G') z jM jM' jL jL'
      ((congrArg (fun q : Z ⟶ _ => Φ (q z) ∈ D.toPre.P.L.U jM) k₁).mpr a₁)
      ((congrArg (fun q : Z ⟶ _ => q z ∈ D'.toPre.P.L.U jM') k₁).mpr a₂)
      ((congrArg (fun q : Z ⟶ _ => q z ∈ U.LG.L.U jL) k₃).mpr a₃)
      ((congrArg (fun q : Z ⟶ _ => q z ∈ U'.LG.L.U jL') k₄).mpr a₄)
    have a₅ : (U.gt e).pG.left ((r ≫ h e) z) ∈ D.toPre.P.L.U jM :=
      (congrArg (fun q => q (r z) ∈ D.toPre.P.L.U jM) (hp e)).mp a₁
    rw [k₁, k₂, gw_thickMap U' e r z jM' jL' a₂ a₄, gw_thickMap U e (r ≫ h e) z jM jL a₅ a₃] at a
    exact mul_left_cancel (a.symm.trans (hu e Z r z jM jM' jL jL' a₁ a₂ a₃ a₄))
  obtain ⟨v, hv⟩ := exists_unit_levels (I.map (algebraMap R B)) ve fun e z => by
    have h₁ : adicLevelMap (I.map (algebraMap R B)) (Nat.le_succ (e + 1)) ≫ reduction I y (e + 1) =
        reduction I y e ≫ thickMap R I e G' := by
      rw [← cancel_mono (fstG I (e + 1) G').left, Category.assoc, Category.assoc, hy, Algebraise.thickMap_fstG, hy,
        adicLevelMap_ι_assoc]
    rw [hve, hve, h₁, Category.id_comp]
    exact cu e _ _ z (m₂ e z) (m₁ e z)
  refine ⟨v, fun e Z ρ r z jM jM' hr a₁ a₂ a₃ a₄ => ?_⟩
  have w₀ : ρ ≫ spMap (algebraMap R B) = (r ≫ (thickObj R I e G').hom) ≫ thick R I e := by
    have hg'' : g' ≫ G'.hom = spMap (algebraMap R B) := hg'
    rw [← hg'', ← Category.assoc, ← hr, Category.assoc, Algebraise.fstG_hom, Category.assoc]
  obtain ⟨l, rfl⟩ := exists_factor_level I (algebraMap R B) ρ _ w₀
  obtain rfl : r = l ≫ reduction I y e := by
    rw [← cancel_mono (fstG I e G').left, Category.assoc, hy]
    exact hr.trans (Category.assoc _ _ _)
  rw [hv, hve]
  exact hu e Z _ z jM jM' jL jL' a₁ a₂ a₃ a₄

theorem IsRatio.vl_eq [IsHausdorff (I.map (algebraMap R B)) B] {v : Γ(Spec (CommRingCat.of B), ⊤)ˣ}
    (hv : IsRatio U U' w h g' jL jL' v)
    (hg' : g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B))) (c' : ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL')
    (c : ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL)
    (hgg : ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left),
      r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ h e ≫ (fstG I e G).left = ρ ≫ g)
    {k : ℕ} (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k)
    (hσ : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι)
      (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), Φ ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM →
      (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (h e (r z)) ∈ U.LG.L.U jL →
      (fstG I e G').left (r z) ∈ U'.LG.L.U jL' →
      (Geo.Tor.gw (U.w e) (r ≫ h e) z jM (fun _ => jL) ^ k).val *
          vl σ (r ≫ h e ≫ (fstG I e G).left) z (fun _ => jL) =
        ((Geo.Tor.gw w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL')) ^ k).val *
          vl σ' (r ≫ (fstG I e G').left) z (fun _ => jL'))
    (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z) :
    vl σ (ρ ≫ g) z (fun _ => jL) = (gm ρ z ⊤ v ^ k).val * vl σ' (ρ ≫ g') z (fun _ => jL') := by
  let y : Over.mk (spMap (algebraMap R B)) ⟶ G' := Over.homMk g' hg'
  have hy : ∀ e, reduction I y e ≫ (fstG I e G').left = adicLevelι (I.map (algebraMap R B)) (e + 1) ≫ g' :=
    fun e => reduction_fstG I y e
  obtain ⟨a, ha⟩ : ∃ a : Γ(Spec (CommRingCat.of B), ⊤), ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z),
      gs ρ z ⊤ a = vl σ (ρ ≫ g) z (fun _ => jL) :=
    ⟨_, fun Z ρ z => gs_appLE g (ch U.LG.L fun _ => jL) ⊤ (fun _ _ => mem_ch.2 (c trivial)) ρ z trivial _⟩
  obtain ⟨a', ha'⟩ : ∃ a : Γ(Spec (CommRingCat.of B), ⊤), ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z),
      gs ρ z ⊤ a = vl σ' (ρ ≫ g') z (fun _ => jL') :=
    ⟨_, fun Z ρ z => gs_appLE g' (ch U'.LG.L fun _ => jL') ⊤ (fun _ _ => mem_ch.2 (c' trivial)) ρ z trivial _⟩
  have pr : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (z : Z),
      gs ρ z ⊤ ((v ^ k).val * a') = (gm ρ z ⊤ v ^ k).val * vl σ' (ρ ≫ g') z (fun _ => jL') := fun Z ρ z =>
    (gs_mul ρ z ⊤ trivial _ _).trans (congrArg₂ (· * ·)
      ((gs_unit ρ z ⊤ trivial _).trans (congrArg Units.val (map_pow _ _ _))) (ha' Z ρ z))
  have E : a = (v ^ k).val * a' := fn_ext_germs (I.map (algebraMap R B)) fun e z => by
    obtain ⟨jM, a₁⟩ := exists_chart D.toPre.P.isLB (Φ ((U'.gt e).pG.left (reduction I y e z)))
    obtain ⟨jM', a₂⟩ := exists_chart D'.toPre.P.isLB ((U'.gt e).pG.left (reduction I y e z))
    have a₄ : (fstG I e G').left (reduction I y e z) ∈ U'.LG.L.U jL' :=
      (congrArg (fun q => q z ∈ U'.LG.L.U jL') (hy e)).mpr (c' trivial)
    have a₃ : (fstG I e G).left (h e (reduction I y e z)) ∈ U.LG.L.U jL :=
      (congrArg (fun q => q z ∈ U.LG.L.U jL) (hgg e _ _ _ (hy e))).mpr (c trivial)
    have H := hσ e _ (reduction I y e) z jM jM' jL jL' a₁ a₂ a₃ a₄
    rw [hv e _ _ (reduction I y e) z jM jM' (hy e) a₁ a₂ a₃ a₄, hgg e _ _ _ (hy e), hy, mul_pow, Units.val_mul,
      _root_.mul_assoc, Units.mul_right_inj] at H
    rw [ha, pr]
    exact H
  rw [← ha, E, pr]

end Formal

section Generic

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G]

abbrev vK {U : UnifPre I D A G} {k : ℕ} (s : U.SecK k) {Z : Scheme.{0}} (q : Z ⟶ pullback G.hom (jK R)) (z : Z)
    (j : U.LG.L.ι) : Z.presheaf.stalk z :=
  gs q z (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => j)) (s.f fun _ => j)

theorem exists_integral (U : Unif I D A G) {k : ℕ} (hk : 1 ≤ k) (s : U.SecK k) :
    ∃ (c : R) (σ : H0 U.LG.L k), c ≠ 0 ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ pullback G.hom (jK R)) (z : Z) (j : U.LG.L.ι),
      pullback.fst G.hom (jK R) (q z) ∈ U.LG.L.U j → vl σ (q ≫ pullback.fst G.hom (jK R)) z (fun _ => j) =
        cst ((q ≫ pullback.snd G.hom (jK R)) ≫ jK R) z c * vK s q z j := by
  obtain ⟨F, ⟨c, hc, σ, f, h₁, -, -⟩, -⟩ := (U.expand k hk).1 s
  refine ⟨c, σ, hc, fun Z q z j hj => ?_⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good U.LG.L U.LG.isLB z (K := Fin 1) (fun _ => q ≫ pullback.fst G.hom (jK R))
    (fun _ => j) (fun _ _ _ => rfl) (fun _ => hj)
  have e := ExpInt.secScal_sval h₁ q z hJ
  rw [sval_of σ _ z J (fun _ => j) (fun _ => by rw [Category.comp_id]; exact eJ 0),
    sval_of s q z J (fun _ => j) (fun _ => eJ 0), ExpInt.gs_scal, ← Category.assoc] at e
  exact e

theorem generic_ext (hA : AmpleSt) (U : UnifPre I D A G) {Z : Scheme.{0}} (q₁ q₂ : Z ⟶ pullback G.hom (jK R))
    (H : ∀ z : Z, ∃ (j₁ j₂ : U.LG.L.ι) (u : (Z.presheaf.stalk z)ˣ), pullback.fst G.hom (jK R) (q₁ z) ∈ U.LG.L.U j₁ ∧
      pullback.fst G.hom (jK R) (q₂ z) ∈ U.LG.L.U j₂ ∧
      ∀ k : ℕ, 1 ≤ k → ∀ s : U.SecK k, vK s q₁ z j₁ = (u ^ k).val * vK s q₂ z j₂) : q₁ = q₂ := by
  have : IsProper A.A.hom := A.isAb.proper
  have : CompactSpace A.A.left := QuasiCompact.compactSpace_of_compactSpace A.A.hom
  have : QuasiSeparatedSpace A.A.left := quasiSeparatedSpace_of_quasiSeparated A.A.hom
  obtain ⟨gn, hgn, w, hw⟩ : ∃ (gn : pullback G.hom (jK R) ⟶ A.A.left) (_ : Mono gn)
      (w : LB.Iso (A.L.pull gn) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w.IsGen :=
    ⟨U.gen.hom.left, inferInstanceAs (Mono ((Over.forget _).map U.gen.hom)), U.ext⟩
  obtain ⟨w', hw', -⟩ := Algebraise.exists_swap _ _ w hw (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _)
  obtain ⟨κ, t, hcov, haff⟩ := Algebraise.exists_cover hA A 4 le_rfl
  rw [← cancel_mono gn]
  refine (hom_ext_of_germs A.isLB (by norm_num) t hcov haff (q₂ ≫ gn) (q₁ ≫ gn) fun z j j' hj hj' => ?_).symm
  obtain ⟨j₁, j₂, u, m₁, m₂, hu⟩ := H z
  refine ⟨Geo.Tor.gw w' q₁ z j (fun _ => j₁) * u * (Geo.Tor.gw w' q₂ z j' (fun _ => j₂))⁻¹, fun n hn a => ?_⟩
  obtain ⟨s, hs⟩ := Algebraise.exists_down A.isLB U.LG.isLB gn _ w' hw' a
  have key : ∀ {T : Type} [CommRing T] (a b c : Tˣ) (x : T),
      a.val ^ n * ((b ^ n).val * x) = ((a * b * c⁻¹) ^ n).val * (c.val ^ n * x) := fun a b c x => by
    rw [mul_pow, mul_pow, inv_pow, Units.val_mul, Units.val_mul, ← Units.val_pow_eq_pow_val,
      ← Units.val_pow_eq_pow_val, _root_.mul_assoc, Units.inv_mul_cancel_left, _root_.mul_assoc]
  exact (hs Z q₁ z j j₁ hj m₁).trans ((congrArg (_ * ·) (hu n hn s)).trans ((key _ _ _ _).trans
    (congrArg (_ * ·) (hs Z q₂ z j' j₂ hj' m₂).symm)))

theorem eq_one_of_values (hA : AmpleSt) (U : UnifPre I D A G) {Z : Scheme.{0}} (q : Z ⟶ pullback G.hom (jK R))
    (z : Z) (j : U.LG.L.ι) (hj : pullback.fst G.hom (jK R) (q z) ∈ U.LG.L.U j) (u : (Z.presheaf.stalk z)ˣ)
    (H : ∀ k : ℕ, 1 ≤ k → ∀ s : U.SecK k, vK s q z j = (u ^ k).val * vK s q z j) : u = 1 := by
  obtain ⟨J, hJ, eJ⟩ := exists_good U.LG.L U.LG.isLB z (K := Fin 1) (fun _ => q ≫ pullback.fst G.hom (jK R))
    (fun _ => j) (fun _ _ _ => rfl) (fun _ => hj)
  have p : ∀ k : ℕ, 4 ≤ k → u ^ k = 1 := fun k hk => by
    obtain ⟨s, hs⟩ := GenericGenerated.exists_secK_isUnit hA R I D A G U k hk Z q z J hJ
    rw [sval_of s q z J (fun _ => j) (fun _ => eJ 0)] at hs
    exact Units.ext (hs.mul_right_cancel ((H k (le_trans (by norm_num) hk) s).symm.trans (_root_.one_mul _).symm))
  have := p (4 + 1) (Nat.le_succ 4)
  rwa [pow_succ, p 4 le_rfl, _root_.one_mul] at this

end Generic

end GlobalTheory.FormalGeneric

open GlobalTheory.FormalGeneric GlobalTheory.SectionRingIso in

theorem GlobalTheory.generic_iso_agrees_on_complete_points : Laws → Laws2 → ∀ (R : Type) [CommRing
    R] [IsDomain R] [IsDiscreteValuationRing R] (I
    : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A'
    : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of
    R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj
    G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD
    : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j
    : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j
    e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt
    e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j
    e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt
    e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j
    e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG
    x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j
    e).hom.left) → ∀ (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (wK
    : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (ΦK.hom.left ≫ pullback.fst
    G.hom (jK R)))), (wK.IsGen ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), (∀ (e
    : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM'
    : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst
    D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt
    e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r
    z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j
    e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e
    G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f
    (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z
    jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L
    (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (Z : Scheme.{0}) (r
    : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫
    ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL → (r ≫ pullback.fst G'.hom (jK
    R)) z ∈ U'.LG.L.U jL' → gs (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L
    (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw wK r z jL
    (fun _ => jL') ^ k).val * gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L
    (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (B : Type) [CommRing
    B] [Algebra R B] (g' : Spec (CommRingCat.of B) ⟶ G'.left) (g : Spec (CommRingCat.of
    B) ⟶ G.left) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), IsAdicComplete (I.map (algebraMap R B)) B → (g'
    ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ g ≫ G.hom = Spec.map
    (CommRingCat.ofHom (algebraMap R B)) ∧ ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL' ∧ ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL ∧ ∀ (e
    : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e
    G').left), r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e
    G).left = ρ ≫ g) → ∃ v : Γ(Spec (CommRingCat.of B), ⊤)ˣ, (∀ (Z : Scheme.{0}) (ρ
    : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ ((Over.pullback (jK R)).obj
    G').left), r ≫ pullback.fst G'.hom (jK R) = ρ ≫ g' → r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK
    R) = ρ ≫ g ∧ ∀ z : Z, Geo.Tor.gw wK r z jL (fun _ => jL') = gm ρ z ⊤ v) ∧ ∀ (e : ℕ) (Z
    : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM
    : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι), r ≫ (fstG I e G').left = ρ ≫ g' → (hD.e.hom.left ≫
    pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r
    z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j
    e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r
    ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w
    e) (r ≫ (j e).hom.left) z jM (fun _ => jL) * gm ρ z ⊤ v := by
  intro hL hL2 R _ _ _ I hR hI D D' A A' G G' _ _ _ _ hG hG' U U' hD j hj ΦK wK ⟨_, hK⟩ B _ _ g' g jL jL' hB
    ⟨hg', hg, c', c, hgg⟩
  obtain ⟨v, hv⟩ := exists_isRatio U.toUnifPre U'.toUnifPre hD.w (fun e => (j e).hom.left) g' g jL jL' hD.w_gen
    (fun e => (hj e).2.1) (fun e => (hj e).2.2.1) hg' c' c hgg
  refine ⟨v, fun Z ρ r hr => ?_, hv⟩
  have b₀ : (ρ ≫ g) ≫ G.hom = (r ≫ pullback.snd G'.hom (jK R)) ≫ jK R := by
    rw [Category.assoc, hg, ← hg', ← Category.assoc, ← hr, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨q₂, f₂, s₂⟩ : ∃ q₂ : Z ⟶ pullback G.hom (jK R), q₂ ≫ pullback.fst G.hom (jK R) = ρ ≫ g ∧
      q₂ ≫ pullback.snd G.hom (jK R) = r ≫ pullback.snd G'.hom (jK R) :=
    ⟨pullback.lift _ _ b₀, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨q₁, e₁, f₁, s₁⟩ : ∃ q₁ : Z ⟶ pullback G.hom (jK R), q₁ = r ≫ ΦK.hom.left ∧
      q₁ ≫ pullback.fst G.hom (jK R) = r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R) ∧
      q₁ ≫ pullback.snd G.hom (jK R) = r ≫ pullback.snd G'.hom (jK R) :=
    ⟨_, rfl, Category.assoc _ _ _, (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w ΦK.hom))⟩
  have m₂ : ∀ z, pullback.fst G.hom (jK R) (q₂ z) ∈ U.LG.L.U jL := fun z =>
    (congrArg (fun q : Z ⟶ _ => q z ∈ U.LG.L.U jL) f₂).mpr (c trivial)
  have K : ∀ (z : Z) (j₁ : U.LG.L.ι), pullback.fst G.hom (jK R) (q₁ z) ∈ U.LG.L.U j₁ → ∀ k : ℕ, 1 ≤ k →
      ∀ s : U.SecK k, vK s q₁ z j₁ =
        ((Geo.Tor.gw wK r z j₁ (fun _ => jL') * (gm ρ z ⊤ v)⁻¹) ^ k).val * vK s q₂ z jL := by
    intro z j₁ m₁ k hk s
    obtain ⟨c₀, σ₀, hc₀, h₀⟩ := exists_integral U hk s
    obtain ⟨c₁, σ', σ, hc₁, h₁, hσ⟩ :=
      (integral_sections_correspond hL hL2 R I hR hI D D' A A' G G' hG hG' U U' hD j hj k hk).1 σ₀
    have val : ∀ (q : Z ⟶ pullback G.hom (jK R)) (i : U.LG.L.ι), pullback.fst G.hom (jK R) (q z) ∈ U.LG.L.U i →
        q ≫ pullback.snd G.hom (jK R) = r ≫ pullback.snd G'.hom (jK R) →
        vl σ (q ≫ pullback.fst G.hom (jK R)) z (fun _ => i) =
          cst ((r ≫ pullback.snd G'.hom (jK R)) ≫ jK R) z c₁ *
            (cst ((r ≫ pullback.snd G'.hom (jK R)) ≫ jK R) z c₀ * vK s q z i) := fun q i hi hq => by
      have hm : (q ≫ pullback.fst G.hom (jK R)) z ∈ ch U.LG.L (fun _ => i) := mem_ch.2 hi
      have b : (q ≫ pullback.fst G.hom (jK R)) ≫ G.hom = (r ≫ pullback.snd G'.hom (jK R)) ≫ jK R := by
        rw [← hq, Category.assoc, Category.assoc, pullback.condition]
      refine (congrArg (gs _ z (ch U.LG.L fun _ => i)) (h₁ _)).trans ((gs_mul _ z _ hm _ _).trans
        (congrArg₂ (· * ·) ((gs_res _ z le_top hm _).trans ((ExpInt.gs_scal _ _ z c₁).trans ?_))
          ((h₀ Z q z i hi).trans ?_)))
      · rw [b]
      · rw [hq]
    have t₁ := hK k hk σ' σ hσ Z r z j₁ jL' ((congrArg (fun q : Z ⟶ _ => q z ∈ U.LG.L.U j₁) f₁).mp m₁)
      ((congrArg (fun q : Z ⟶ _ => q z ∈ U'.LG.L.U jL') hr).mpr (c' trivial))
    have t₂ := hv.vl_eq _ _ _ _ _ _ _ _ hg' c' c hgg σ' σ hσ Z ρ z
    rw [← f₁, hr] at t₁
    rw [← f₂] at t₂
    have key : ∀ {T : Type} [CommRing T] (a b : Tˣ) (d₁ d₀ x y t : T), IsUnit d₁ → IsUnit d₀ →
        d₁ * (d₀ * x) = (a ^ k).val * t → d₁ * (d₀ * y) = (b ^ k).val * t → x = ((a * b⁻¹) ^ k).val * y := by
      intro T _ a b d₁ d₀ x y t u₁ u₀ h₁ h₂
      refine u₀.mul_left_cancel (u₁.mul_left_cancel (h₁.trans ?_))
      rw [mul_left_comm d₀, mul_left_comm d₁, h₂, mul_pow, inv_pow, Units.val_mul, _root_.mul_assoc,
        Units.inv_mul_cancel_left]
    exact key _ _ _ _ _ _ _ (ExpInt.isUnit_cst _ z hc₁) (ExpInt.isUnit_cst _ z hc₀)
      ((val q₁ j₁ m₁ s₁).symm.trans t₁) ((val q₂ jL (m₂ z) s₂).symm.trans t₂)
  obtain rfl : q₁ = q₂ := generic_ext hL.ample U.toUnifPre q₁ q₂ fun z => by
    obtain ⟨j₁, m₁⟩ := exists_chart U.LG.isLB (pullback.fst G.hom (jK R) (q₁ z))
    exact ⟨j₁, jL, _, m₁, m₂ z, K z j₁ m₁⟩
  exact ⟨f₁.symm.trans f₂, fun z =>
    mul_inv_eq_one.1 (eq_one_of_values hL.ample U.toUnifPre q₁ z jL (m₂ z) _ (K z jL (m₂ z)))⟩
