import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsIsoPairOfEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SameCoord

set_option maxHeartbeats 1600000 in

theorem psiCoord_of_isPullDeg_id {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D D' : DegPre R}
    (hD : IsPullDeg (RingHom.id R) D D') (x : D'.X) (r : R) (hr : PsiCoord D (hD.xe x) r) :
    ∃ u : Rˣ, PsiCoord D' x (u * r) := by
  obtain ⟨j, hj, h, hr⟩ := hr
  have hs := specOf_id R
  set Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) with hΦ
  have hc : (D'.c x).left ≫ Φ = (D.c (hD.xe x)).left := by
    rw [hΦ, hD.c_pr x]
    exact (congrArg (· ≫ (D.c (hD.xe x)).left) hs).trans (Category.id_comp _)
  obtain ⟨q, hq⟩ := exists_chart D'.P.isLB ((D'.c x).left (closedPoint R))
  have hq' : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D'.c x).left ⁻¹ᵁ D'.P.L.U q :=
    ((IsLocalRing.closedPoint_mem_iff _).1 hq).ge
  have hp : ∀ y : Spec (CommRingCat.of R), Φ ((D'.c x).left y) ∈ D.P.L.U (j PUnit.unit) := fun y =>
    (congrArg (fun g => g y ∈ D.P.L.U (j PUnit.unit)) hc).mpr (hj trivial)
  have hV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤
      (D'.c x).left ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => j PUnit.unit) ⊓ D'.P.L.U q) := fun y _ =>
    ⟨mem_pull.2 (hp y), hq' trivial⟩
  let u₀ : Γ(Spec (CommRingCat.of R), ⊤)ˣ := res hV (pullU (D'.c x).left _ (hD.w.s (fun _ => j PUnit.unit, q)))
  let u : Rˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom u₀
  have hu : DegPre.toOpen (R := R) ⊤ u = u₀.val := by
    show ((Spec (CommRingCat.of R)).presheaf.map (𝟙 _)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u₀.val)) = _
    rw [CategoryTheory.Functor.map_id]
    exact congrArg (fun g => g.hom u₀.val) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
  have h' : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D'.P.L (K := PUnit) (fun _ => D'.xK x) (fun _ => -1)).U (fun _ => q) :=
    fun z _ => Set.mem_iInter.2 fun _ => hq' (x := jK R z) trivial
  refine ⟨u, fun _ => q, hq', h', ?_⟩
  apply TopCat.Presheaf.section_ext (TK R).left.sheaf
  intro z hz
  have hF : jFK (R := R) (FractionRing R) = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
    simp
  have hFz : jFK (R := R) (FractionRing R) z = z := by rw [hF]; rfl
  have m₁ : Φ (D'.xK x (jFK (R := R) (FractionRing R) z)) ∈ D.P.L.U (j PUnit.unit) := by
    rw [hFz]; exact hp (jK R z)
  have m₂ : D'.xK x (jFK (R := R) (FractionRing R) z) ∈ D'.P.L.U q := by
    rw [hFz]; exact hq' (x := jK R z) trivial
  have m₃ : D.xK (hD.xe x) (jFK (R := R) (FractionRing R) z) ∈ D.P.L.U (j PUnit.unit) := by
    rw [hFz]; exact hj (x := jK R z) trivial
  have pm := pmaps_psi hD (FractionRing R) (by
    have : spMap (RingHom.id R) = 𝟙 _ := hs
    rw [this, Category.comp_id]) x _ (𝟙 _) z j (fun _ => q) (fun _ => m₁) (fun _ => m₂)
  rw [Category.comp_id, Fintype.prod_unique] at pm
  have pm' := (gm_pullGen D.P.L (fun _ : PUnit => D.xK (hD.xe x)) _ (D.psi (hD.xe x)) (jFK (R := R) (FractionRing R)) (𝟙 _) z j
    (Set.mem_iInter.2 fun _ => m₃)).symm.trans (pm.trans (congrArg (_ * ·)
      (gm_pullGen D'.P.L (fun _ : PUnit => D'.xK x) _ (D'.psi x) (jFK (R := R) (FractionRing R)) (𝟙 _) z (fun _ => q)
    (Set.mem_iInter.2 fun _ => m₂))))
  rw [hF, Category.comp_id, Category.id_comp, Category.id_comp, zpow_neg_one, eq_inv_mul_iff_mul_eq] at pm'
  have a₁ : gm (jK R) z ⊤ u₀ = gw hD.w (D'.xK x) z (j PUnit.unit) q :=
    (gm_res (jK R) z hV trivial _).trans (gm_pull (jK R) (D'.c x).left z _ (hV (x := jK R z) trivial) _)
  have a₂ := gm_res (𝟙 (TK R).left) z h hz ((D.psi (hD.xe x)).s j)
  have a₃ := gm_res (𝟙 (TK R).left) z h' hz ((D'.psi x).s (fun _ => q))
  have k := congrArg Units.val ((congrArg₂ (fun a b : ((TK R).left.presheaf.stalk z)ˣ => a * b) a₁ a₂).trans (pm'.trans a₃.symm))
  rw [Units.val_mul, gm_val (jK R) z ⊤ trivial, gm_val _ z _ hz, gm_val _ z _ hz] at k
  rw [map_mul, map_mul, hu, hr]
  exact (map_mul _ _ _).trans k

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

set_option maxHeartbeats 1600000 in

theorem exists_move (hU : UnifBaseChangeSt) (h5 : Laws5) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : AdmBase R I) {t t' : SAB H (Sp R)} (m : SABMap t' t (𝟙 _)) (P : PELUnif I t) :
    ∃ (P' : PELUnif I t') (hD : IsPullDeg (RingHom.id R) P.D.toPre P'.D.toPre),
      ∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y := by
  let _ := H.starRing
  have hs := specOf_id R
  have gp₁ : IsGrpPullback t'.G t.G (specOf (RingHom.id R)) m.φ := m.cart.congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback t.G (specOf (RingHom.id R)))
  have gpG : IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) := by
    have := P.U.gen_hom
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr
      (Category.id_comp _) rfl
  have gp₂ : IsGrpPullback ((Over.pullback (jK R)).obj t'.G) t.G (jK R)
      (pullback.fst t'.G.hom (jK R) ≫ m.φ) :=
    ((isGrpPullback_pullback t'.G (jK R)).comp m.cart).congr (Category.comp_id _) rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp₂ gpG
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (P.A.L.pull eA.hom.left) (P.U.LG.L.pull (pullback.fst t'.G.hom (jK R) ≫ bc.hom.left ≫
      pullback.fst t.G.hom (specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := eA.hom.left ≫ P.U.gen.inv.left)
      (chartPullSame P.A.L (fun _ => eA.hom.left) (fun _ => P.U.gen.hom.left) _ _ fun _ => by
        rw [Category.assoc, hgi, Category.comp_id])
      (chartPullSame P.U.LG.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ _ fun _ => by
        rw [hbc, ← heA]; simp only [Category.assoc]) P.U.ext
  obtain ⟨wL', he', gL, rL⟩ := rigIso_congr P.bundle m.cm m.lin hbc
    (e := specOf (RingHom.id R)) (hs.trans m.base.symm)
  obtain ⟨Wo, hWo, hψW⟩ := h5.psiOnExists R I hR P.D
  have hgen : (specOf (RingHom.id R)).base (genericPoint (Spec (CommRingCat.of R))) ∈ Wo := by
    rw [hs]; exact hWo
  have hI : I.map (RingHom.id R) ≤ I := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', hLG, hgenU, hPU⟩ := hU R R I I hR hR (RingHom.id R) hI P.D P.A t.G t.semi P.U
    Wo hψW hgen t'.G bc mbc P.A rfl eA mE wA t'.PP wL' he' gL rL
  have a₃ : ∀ x, (t'.act.act x).left ≫ m.φ = m.φ ≫ (t.act.act x).left := m.act
  have hbcact : ∀ x, t'.act.toRingAct.act x ≫ bc.hom =
      bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (t.act.toRingAct.act x) := by
    intro x
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have a₂ : ((Over.pullback (specOf (RingHom.id R))).map (t.act.act x)).left ≫
          pullback.fst t.G.hom (specOf (RingHom.id R)) = pullback.fst _ _ ≫ (t.act.act x).left :=
        pullback.lift_fst _ _ _
      show (t'.act.act x ≫ bc.hom).left ≫ _ =
        (bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (t.act.act x)).left ≫ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, hbc, ← Category.assoc, hbc, a₃]
    · exact (Over.w (t'.act.act x ≫ bc.hom)).trans
        (Over.w (bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (t.act.act x))).symm
  have actA : ∀ x, (P.oA.act x).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
      P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ (t.act.act x).left := by
    intro x
    have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have extA : ∀ x, (Over.pullback (jK R)).map (t'.act.toRingAct.act x) ≫ U''.gen.hom =
      U''.gen.hom ≫ P.oA.act x := by
    intro x
    rw [hgenU]
    apply Over.OverMorphism.ext
    apply gpG.1.hom_ext
    · have a₁ : ((Over.pullback (jK R)).map (t'.act.act x)).left ≫ pullback.fst t'.G.hom (jK R) =
          pullback.fst t'.G.hom (jK R) ≫ (t'.act.act x).left := pullback.lift_fst _ _ _
      show ((Over.pullback (jK R)).map (t'.act.act x) ≫ eA.hom).left ≫ _ = (eA.hom ≫ P.oA.act x).left ≫ _
      rw [Over.comp_left, Category.assoc, heA, ← Category.assoc, a₁, Category.assoc, a₃, Over.comp_left,
        Category.assoc, actA, reassoc_of% heA]
    · rw [Over.w, Over.w]
  obtain ⟨mod'', oD'', xl, -, lin'', w0''⟩ := h5.oLinBaseChange R R I I hR hR (RingHom.id R) P.D P.A t.G P.U
    t'.G bc mbc P.A D'' hD U'' hPU (𝓞 E) P.oD P.oA t.act.toRingAct P.lin t'.act.toRingAct hbcact
    P.oA extA
  exact ⟨{ D := D'', mod := mod'', oD := oD'', A := P.A, oA := P.oA, U := U'', bundle := hLG, lin := lin''
           w0 := w0'' H.w0 P.w0 }, hD, xl⟩

theorem exists_equiv_psiCoord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (t t' : SAB H (Sp R)) (_ : SABMap t' t (𝟙 _)) (U : PELUnif (maximalIdeal R) t) (U' : PELUnif (maximalIdeal R) t'), IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (maximalIdeal R) R → ∃ e : U.D.toPre.X ≃ₗ[𝓞 E] U'.D.toPre.X, ∀ χ r, PsiCoord U.D.toPre χ r → ∃ u : Rˣ, PsiCoord U'.D.toPre (e χ) (u * r) := by
  intro E _ _ _ H R _ _ _ _ t t' m U U' hN hC hA
  letI := H.starRing
  have hR : AdmBase R (maximalIdeal R) := ⟨hN, inferInstance, hC, hA⟩
  obtain ⟨-, -, -, h4, h5, h6⟩ := GlobalTheory.allSixLaws
  obtain ⟨P, hD₁, xl₁⟩ := exists_move h4.unifBaseChange h5 hR m U
  obtain ⟨wL, -, g₀, -, m₀, -, -⟩ := exists_iso_pair_of_eq (U'.bundle.trans P.bundle.symm)
  obtain ⟨hD₂, -, holin⟩ := h6.unifUniq R _ hR P.D U'.D P.A U'.A t'.G t'.semi P.U U'.U wL g₀ m₀
  obtain ⟨xl₂, -⟩ := holin (𝓞 E) P.oD U'.oD P.oA U'.oA t'.act.toRingAct P.lin U'.lin
  let e₁ : P.D.toPre.X ≃ₗ[𝓞 E] U.D.toPre.X := { hD₁.xe with map_smul' := xl₁ }
  let e₂ : U'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD₂.xe with map_smul' := xl₂ }
  refine ⟨e₁.symm.trans e₂.symm, fun χ r hr => ?_⟩
  have k₁ : hD₁.xe (e₁.symm χ) = χ := e₁.apply_symm_apply χ
  have k₂ : hD₂.xe (e₂.symm (e₁.symm χ)) = e₁.symm χ := e₂.apply_symm_apply _
  obtain ⟨u₁, hu₁⟩ := psiCoord_of_isPullDeg_id hD₁ (e₁.symm χ) r (by rw [k₁]; exact hr)
  obtain ⟨u₂, hu₂⟩ := psiCoord_of_isPullDeg_id hD₂ (e₂.symm (e₁.symm χ)) _ (by rw [k₂]; exact hu₁)
  exact ⟨u₂ * u₁, by rw [Units.val_mul, mul_assoc]; exact hu₂⟩

end GlobalTheory.SameCoord
