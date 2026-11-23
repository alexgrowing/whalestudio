import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullDegEquivApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesAtRev
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification (CarriesAt PullIdent)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.PullDegSymm

namespace GlobalTheory.PullDegSymm

theorem carriesAt_gm {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {p' : Y ⟶ X'} {p : Y ⟶ X} {hp : p' ≫ F = p} {n : ℤ}
    {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p') (fun _ => n))}
    {b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))}
    (H : CarriesAt L L' F w p' p hp n a b) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (j : L.ι) (j' : L'.ι)
    (h₁ : F (p' (r z)) ∈ L.U j) (h₂ : p' (r z) ∈ L'.U j') :
    gm r z (LB.wchart L (fun _ : PUnit => p) (fun _ => j)) (b.s (fun _ => j)) =
      gw w (r ≫ p') z j j' ^ n * gm r z (LB.wchart L' (fun _ : PUnit => p') (fun _ => j')) (a.s (fun _ => j')) := by
  have hm : r z ∈ p' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') := ⟨mem_pull.2 h₁, h₂⟩
  have e := congrArg (gm r z _) (H j j')
  refine (gm_res _ z _ hm _).symm.trans (e.trans ?_)
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ n)
    (gm_pull _ _ z _ hm _))) (gm_res _ z _ hm _))

theorem exists_psiOn_rev : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (p : PullIdent (RingHom.id R) D D')
    (W : (Spec (CommRingCat.of R)).Opens) (ψW : PsiOn D W) (g : (TK R).left ⟶ (TW W).left)
    (hg : g ≫ W.ι = jK R ≫ GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)),
    (∀ χ : D'.X, CarriesAt D.P.L D'.P.L p.F p.w (D'.xK χ) (g ≫ (toUnit (TW W) ≫ D.c (p.xe χ)).left)
      (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.ptK_comp (RingHom.id R) p.F (D.c (p.xe χ)) (D'.c χ) (p.c_eq χ) W g hg) (-1) (D'.psi χ)
      (LB.pullGen D.P.L _ _ (ψW.psi (p.xe χ)) g)) →
    ∃ ψW' : PsiOn D' W, ∀ χ : D'.X, PMaps p.w (K := PUnit) (fun _ => (toUnit (TW W) ≫ D'.c χ).left)
      (fun _ => (toUnit (TW W) ≫ D.c (p.xe χ)).left) (fun _ => -1) (ψW'.psi χ) (ψW.psi (p.xe χ)) (𝟙 _) := by
  intro R _ _ D D' p W ψW g hg H
  have hgj : g ≫ W.ι = jK R := by rw [hg, specOf_id', Category.comp_id]
  have hc : ∀ χ : D'.X, ∀ _ : PUnit, (toUnit (TW W) ≫ D'.c χ).left ≫ p.F =
      𝟙 _ ≫ (toUnit (TW W) ≫ D.c (p.xe χ)).left := by
    intro χ _
    show (W.ι ≫ (D'.c χ).left) ≫ p.F = 𝟙 _ ≫ W.ι ≫ (D.c (p.xe χ)).left
    rw [Category.assoc, p.c_eq, specOf_id', Category.id_comp, Category.id_comp]
  choose ψ hψg hψm using fun χ : D'.X => GlobalTheory.DegPull.exists_pmaps ((isGen_iff _).1 p.w_gen) D.P.isLB
    D'.P.isLB (𝟙 _) (hc χ) (ψW.psi (p.xe χ)) (ψW.psi_gen _)
  refine ⟨⟨ψ, hψg, fun χ => ?_⟩, hψm⟩
  apply corr_of_val D'.P.isLB
  intro y J hJ
  rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]
  have hr : (jK R ∣_ W) ≫ W.ι = (jK R ⁻¹ᵁ W).ι ≫ jK R := morphismRestrict_ι _ _
  have hιg : (jK R ⁻¹ᵁ W).ι ≫ g = jK R ∣_ W := by
    rw [← cancel_mono W.ι, Category.assoc, hgj, hr]
  have hpt : (jK R ∣_ W) ≫ (toUnit (TW W) ≫ D'.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ D'.xK χ := by
    show (jK R ∣_ W) ≫ W.ι ≫ (D'.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ jK R ≫ (D'.c χ).left
    rw [← Category.assoc, hr, Category.assoc]
  obtain ⟨jD, hjD⟩ := exists_chart D.P.isLB (p.F (((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ) y))
  have mq : ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ) y ∈ D'.P.L.U (J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ)) := hJ _
  have k1 := hψm χ _ (jK R ∣_ W) y (fun _ => jD) (fun _ => J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ))
    (fun _ => (congrArg (fun f => p.F (f y) ∈ D.P.L.U jD) hpt).mpr hjD)
    (fun _ => (congrArg (fun f => f y ∈ D'.P.L.U (J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ))) hpt).mpr mq)
  rw [Category.comp_id, Fintype.prod_unique, hpt] at k1
  have k2 := carriesAt_gm (H χ) (jK R ⁻¹ᵁ W).ι y jD (J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ)) hjD mq
  have hq : (jK R ⁻¹ᵁ W).ι ≫ g ≫ (toUnit (TW W) ≫ D.c (p.xe χ)).left =
      ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ) ≫ p.F := by
    rw [← Category.assoc, hιg, ← hpt, Category.assoc, hc χ PUnit.unit, Category.id_comp]
  have a := gm_pullGen D.P.L _ _ (ψW.psi (p.xe χ)) g (jK R ⁻¹ᵁ W).ι y (fun _ => jD)
    (Set.mem_iInter.2 fun _ => (congrArg (fun f => f y ∈ D.P.L.U jD) hq).mpr hjD)
  rw [hιg] at a
  rw [val_of (ψ χ) (jK R ∣_ W) y J (fun _ => J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ)) (fun _ => by rw [hpt]),
      val_of (D'.psi χ) (jK R ⁻¹ᵁ W).ι y J (fun _ => J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ)) (fun _ => rfl)]
  exact mul_left_cancel (k1.symm.trans (a.symm.trans k2))

theorem psiOn_carries_pullbackIdent_reverse_of_pmaps {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} (p : PullIdent (RingHom.id R) D D')
    {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) {g : (TK R).left ⟶ (TW W).left}
    (hg : g ≫ W.ι = jK R ≫ GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) (ψW' : PsiOn D' W)
    (hψ : ∀ χ : D'.X, PMaps p.w (K := PUnit) (fun _ => (toUnit (TW W) ≫ D'.c χ).left)
      (fun _ => (toUnit (TW W) ≫ D.c (p.xe χ)).left) (fun _ => -1) (ψW'.psi χ) (ψW.psi (p.xe χ)) (𝟙 _))
    (χ : D.X) (χ' : D'.X) (hχ : p.xe χ' = χ) (hx : D.xK χ ≫ Finv p = g ≫ (toUnit (TW W) ≫ D'.c χ').left) :
    CarriesAt D'.P.L D.P.L (Finv p) (wInv p) (D.xK χ) (g ≫ (toUnit (TW W) ≫ D'.c χ').left) hx (-1) (D.psi χ)
      (LB.pullGen D'.P.L _ _ (ψW'.psi χ') g) := by
  subst hχ
  rw [carriesAt_iff]
  intro y j jD h₁ h₂
  have hgj : g ≫ W.ι = jK R := by rw [hg, specOf_id', Category.comp_id]
  have hP : g ≫ (toUnit (TW W) ≫ D.c (p.xe χ')).left = D.xK (p.xe χ') := by
    show g ≫ W.ι ≫ (D.c (p.xe χ')).left = jK R ≫ (D.c (p.xe χ')).left
    rw [← Category.assoc, hgj]
  have m₁ : (toUnit (TW W) ≫ D'.c χ').left (g y) ∈ D'.P.L.U j :=
    (congrArg (fun f => f y ∈ D'.P.L.U j) hx).mp h₁
  have m₂ : p.F ((toUnit (TW W) ≫ D'.c χ').left (g y)) ∈ D.P.L.U jD := by
    have : p.F ((toUnit (TW W) ≫ D'.c χ').left (g y)) = D.xK (p.xe χ') y := by
      have e := congrArg (fun f => f y) hx
      exact (congrArg p.F e.symm).trans (base_cancel (Finv_F p) _)
    rw [this]; exact h₂
  have k := hψ χ' (TK R).left g y (fun _ => jD) (fun _ => j) (fun _ => m₂) (fun _ => m₁)
  rw [Category.comp_id, Fintype.prod_unique] at k
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB y (fun _ : PUnit => D.xK (p.xe χ')) (fun _ => jD)
    (fun _ _ _ => rfl) (fun _ => h₂)
  have v := GlobalTheory.ArcSpecialise.psiOn_generic ψW (p.xe χ') g (𝟙 _) (by rw [hgj, Category.id_comp]) hJ
  rw [val_of _ g y J (fun _ => jD) (fun _ => by rw [hP]; exact eJ PUnit.unit),
    val_of _ (𝟙 _) y J (fun _ => jD) (fun _ => by rw [Category.id_comp]; exact eJ PUnit.unit)] at v
  have a₁ := gm_pullGen D'.P.L _ _ (ψW'.psi χ') g (𝟙 _) y (fun _ => j) (Set.mem_iInter.2 fun _ => m₁)
  rw [Category.id_comp] at a₁
  have key : ∀ {G : Type} [CommGroup G] (A B C E : G), C = A ^ (-1 : ℤ) * B → C = E → B = A⁻¹ ^ (-1 : ℤ) * E := by
    intro G _ A B C E h₁ h₂
    rw [← h₂, h₁]; group
  refine a₁.trans ?_
  rw [show gw (wInv p) (D.xK (p.xe χ')) y j jD = _ from gw_revIso p.w (Finv_F p) _ y j jD h₁ h₂, hx]
  exact key _ _ _ _ k v

theorem psi_carries_rev : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (p : PullIdent (RingHom.id R) D D')
    (W : (Spec (CommRingCat.of R)).Opens) (ψW : PsiOn D W) (g : (TK R).left ⟶ (TW W).left)
    (hg : g ≫ W.ι = jK R ≫ GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) (ψW' : PsiOn D' W),
    (∀ χ : D'.X, PMaps p.w (K := PUnit) (fun _ => (toUnit (TW W) ≫ D'.c χ).left)
      (fun _ => (toUnit (TW W) ≫ D.c (p.xe χ)).left) (fun _ => -1) (ψW'.psi χ) (ψW.psi (p.xe χ)) (𝟙 _)) →
    ∀ χ : D.X, CarriesAt D'.P.L D.P.L (GlobalTheory.PullDegSymm.Finv p) (GlobalTheory.PullDegSymm.wInv p) (D.xK χ)
      (g ≫ (toUnit (TW W) ≫ D'.c (p.xe.symm χ)).left)
      (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.ptK_comp (RingHom.id R) (GlobalTheory.PullDegSymm.Finv p) (D'.c (p.xe.symm χ)) (D.c χ)
        (GlobalTheory.PullDegSymm.c_eq' p χ) W g hg) (-1) (D.psi χ) (LB.pullGen D'.P.L _ _ (ψW'.psi (p.xe.symm χ)) g) := fun R _ _ D D' p W ψW g hg ψW' hψ χ =>
  psiOn_carries_pullbackIdent_reverse_of_pmaps p ψW hg ψW' hψ χ (p.xe.symm χ) (p.xe.apply_symm_apply χ) _

theorem isPullDeg_symm : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R),
    IsPullDeg (RingHom.id R) D D' → Nonempty (IsPullDeg (RingHom.id R) D' D) := by
  intro R _ _ D D' hD
  obtain ⟨p⟩ := GlobalTheory.PullDegCompare.nonempty_iff.1 ⟨hD⟩
  obtain ⟨W, ψW, g, hg, H⟩ := p.w_psi
  obtain ⟨ψW', hψ⟩ := exists_psiOn_rev R D D' p W ψW g hg H
  exact GlobalTheory.PullDegCompare.nonempty_iff.2 ⟨⟨Finv p, cart' p, F_one' p, F_mul' p, wInv p, wInv_isGen p, w_rig' p,
    p.xe.symm, c_eq' p, ⟨W, ψW', g, hg, psi_carries_rev R D D' p W ψW g hg ψW' hψ⟩⟩⟩

end GlobalTheory.PullDegSymm
