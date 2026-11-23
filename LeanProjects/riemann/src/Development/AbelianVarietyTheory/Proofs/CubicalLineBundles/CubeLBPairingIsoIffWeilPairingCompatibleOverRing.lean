import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LineBundleIsoDescendsFieldToDedekindDomainStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LambdaBundleIsoOfWeilPairingCompatible
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingEqOfIsomorphicCubePairingsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfInvariant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.PairingFibre

variable {S S' : Scheme.{0}} {s : S' ⟶ S}

theorem exists_hom {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H] [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hG : IsGrpPullback G' G s φ) (hH : IsGrpPullback H' H s ψ)
    (w : G ⟶ H) [IsMonHom w] : ∃ w' : G' ⟶ H', IsMonHom w' ∧ w'.left ≫ ψ = φ ≫ w.left := by
  let w' : G' ⟶ H' := Over.homMk (hH.1.lift (φ ≫ w.left) G'.hom (by rw [Category.assoc, Over.w, hG.1.w]))
    (hH.1.lift_snd _ _ _)
  have hw : w'.left ≫ ψ = φ ≫ w.left := hH.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ G'), Geo.Tor.pushPt hH.1.w (x ≫ w') = Geo.Tor.pushPt hG.1.w x ≫ w := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
  have mul : ∀ (T : Over S') (x y : T ⟶ G'), (x * y) ≫ w' = (x ≫ w') * (y ≫ w') := by
    intro T x y
    apply SymBaseChange.pushPt_injective hH
    have a : Geo.Tor.pushPt hG.1.w (x * y) = Geo.Tor.pushPt hG.1.w x * Geo.Tor.pushPt hG.1.w y := map_mul (Geo.Tor.pushHom hG T) x y
    have b : Geo.Tor.pushPt hH.1.w ((x ≫ w') * (y ≫ w')) = Geo.Tor.pushPt hH.1.w (x ≫ w') * Geo.Tor.pushPt hH.1.w (y ≫ w') :=
      map_mul (Geo.Tor.pushHom hH T) _ _
    rw [pa, a, b, pa, pa, MonObj.mul_comp]
  refine ⟨w', ⟨?_, ?_⟩, hw⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S') ⟶ G') ≫ w' = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul (G' ⊗ G') (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

theorem cube_pull {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G s φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LBIso L' (L.pull φ)) {T : Over S} {T' : Over S'} (U : T'.left ⟶ T.left)
    (hU : U ≫ T.hom = T'.hom ≫ s) {n : ℕ} (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G))
    (hx : ∀ i, (x' i).left ≫ φ = U ≫ (x i).left) : LBIso (cubeLB G' x' L') ((cubeLB G x L).pull U) := by
  have hc : (cubeLB G x L).IsLB := DVR.linComb_isLB L hL _ _
  refine LBIso.trans (B := cubeLB G' x' (L.pull φ)) (DVR.linComb_isLB L' hL' _ _)
    (DVR.linComb_isLB _ (Geo.Tor.pull_isLB hL φ) _ _) (Geo.Tor.pull_isLB hc U) (PowPrimitive.lbIso_linComb w _ _) ?_
  exact LBIso.chartPull (Geo.Tor.chartPullLinComb L φ _ _ _ U fun I =>
    Geo.Tor.psum_push h x' x (Over.homMk U hU) (fun i => Over.OverMorphism.ext (hx i)) I.down)
    (Geo.Tor.chartPullPull _ U U rfl) (PolBaseChange.lbIso_refl hc)

theorem exists_gen_cube_one {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (T : Over S) :
    ∃ t : LB.Gen (cubeLB G (fun _ : Fin 2 => (1 : T ⟶ G)) L), t.IsGen := by
  refine (PrimNorm.hasGen_iff hL _ _).2 ?_
  have e : ∀ I : Finset (Fin 2), psum G (fun _ : Fin 2 => (1 : T ⟶ G)) I = 1 := fun I =>
    (Geo.Tor.psum_hom (1 : (T ⟶ G) →* (T ⟶ G)) (fun _ => 1) I).symm
  simp only [e]
  have z : ∀ {M : Type} [CommGroup M] (c : M) (ε : ULift.{0} (Finset (Fin 2)) → ℤ),
      ∏ I, c ^ ε I = c ^ ∑ I, ε I := fun c ε => by
    induction (Finset.univ : Finset (ULift.{0} (Finset (Fin 2)))) using Finset.cons_induction with
    | empty => simp
    | cons a t ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add, ih]
  rw [z, show (∑ I : ULift.{0} (Finset (Fin 2)), (-1 : ℤ) ^ (2 - I.down.card)) = 0 by decide, zpow_zero]

theorem cube_zero {X Y G : Over S} [GrpObj X] [GrpObj Y] [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (f₁ : X ⟶ G) (f₂ : Y ⟶ G) [IsMonHom f₁] [IsMonHom f₂] :
    LBIso (cubeLB G (fun _ : Fin 2 => (1 : 𝟙_ (Over S) ⟶ G)) L)
      ((cubeLB G ![fst X Y ≫ f₁, snd X Y ≫ f₂] L).pull (eSec (X ⊗ Y))) := by
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  refine cube_pull (Geo.Tor.isGrpPullback_of_iso (Iso.refl G)) hL hL
    (LBIso.chartPull (Geo.Tor.chartPullId L) (Geo.Tor.chartPullPull L _ (𝟙 _) rfl) (PolBaseChange.lbIso_refl hL)) _
    (by rw [eSec, Over.w, Category.comp_id]) _ _ fun i => ?_
  rw [eSec, ← Over.comp_left, ← Over.comp_left]
  congr 1
  fin_cases i <;> simp [Hom.one_def]

theorem weilEq_iff {X Y A B : Over S} {X' Y' A' B' : Over S'} [GrpObj X] [GrpObj Y] [GrpObj A] [GrpObj B]
    [IsCommMonObj A] [IsCommMonObj B] [GrpObj X'] [GrpObj Y'] [GrpObj A'] [GrpObj B']
    {x : X'.left ⟶ X.left} {y : Y'.left ⟶ Y.left} {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left}
    (hX : IsGrpPullback X' X s x) (hY : IsGrpPullback Y' Y s y) (hA : IsGrpPullback A' A s a)
    (hB : IsGrpPullback B' B s b) {L : LB A.left} {M : LB B.left} {L' : LB A'.left} {M' : LB B'.left}
    (hL : L.IsLB) (hM : M.IsLB) (hL' : L'.IsLB) (hM' : M'.IsLB) (wL : LBIso L' (L.pull a)) (wM : LBIso M' (M.pull b))
    {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B} {f₁' : X' ⟶ A'} {f₂' : Y' ⟶ A'} {g₁' : X' ⟶ B'}
    {g₂' : Y' ⟶ B'} (e₁ : f₁'.left ≫ a = x ≫ f₁.left) (e₂ : f₂'.left ≫ a = y ≫ f₂.left)
    (e₃ : g₁'.left ≫ b = x ≫ g₁.left) (e₄ : g₂'.left ≫ b = y ≫ g₂.left) {k : Type} [Field k] (t : Sp k ⟶ S') :
    WeilEq L' f₁' f₂' M' g₁' g₂' t ↔ WeilEq L f₁ f₂ M g₁ g₂ (t ≫ s) := by
  have key : ∀ (n : ℕ) (p : Over.mk t ⟶ X') (q : Over.mk t ⟶ Y') (c : kˣ),
      ((Out.WeilIs A' L' n (p ≫ f₁') (q ≫ f₂') (unitOn c) ↔ Out.WeilIs B' M' n (p ≫ g₁') (q ≫ g₂') (unitOn c)) ↔
      (Out.WeilIs A L n (Geo.Tor.pushHom hX _ p ≫ f₁) (Geo.Tor.pushHom hY _ q ≫ f₂) (unitOn c) ↔
        Out.WeilIs B M n (Geo.Tor.pushHom hX _ p ≫ g₁) (Geo.Tor.pushHom hY _ q ≫ g₂) (unitOn c))) := by
    intro n p q c
    refine iff_congr (weilIs_grpPullback_of_comm S S' A A' s a L L' hL hL' hA wL _ _ _ _ _ _ _ ?_ ?_)
      (weilIs_grpPullback_of_comm S S' B B' s b M M' hM hM' hB wM _ _ _ _ _ _ _ ?_ ?_)
    all_goals
      show (_ ≫ _) ≫ _ = (_ ≫ _) ≫ _
      simp only [Category.assoc, e₁, e₂, e₃, e₄]
  have pw : ∀ {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G s φ)
      (n : ℕ) (p : Over.mk t ⟶ G'), p ^ n = 1 ↔ Geo.Tor.pushHom h _ p ^ n = 1 := fun h n p => by
    rw [← map_pow]
    exact (map_eq_one_iff _ fun u v e => SymBaseChange.pushPt_injective h e).symm
  have su : ∀ {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G s φ)
      (p₀ : Over.mk (t ≫ s) ⟶ G), ∃ p : Over.mk t ⟶ G', Geo.Tor.pushHom h _ p = p₀ := fun h p₀ =>
    ⟨Over.homMk (h.1.lift p₀.left t (Over.w p₀)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  constructor
  · intro H n p₀ q₀ c hn hp hq
    obtain ⟨p, rfl⟩ := su hX p₀
    obtain ⟨q, rfl⟩ := su hY q₀
    exact (key n p q c).1 (H n p q c hn ((pw hX n p).2 hp) ((pw hY n q).2 hq))
  · intro H n p q c hn hp hq
    exact (key n p q c).2 (H n _ _ c hn ((pw hX n p).1 hp) ((pw hY n q).1 hq))

theorem lamEq_weilEq_over_ring : Out.Laws → ∀ (R : Type) [CommRing R] (X Y A B : Out.PolAV (Sp R)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (β : R →+* k),
    (LamEq A.L f₁ f₂ B.L g₁ g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (spMap β)) ∧ (IsDedekindDomain R → Function.Injective β → WeilEq A.L f₁ f₂ B.L g₁ g₂ (spMap β) → LamEq A.L f₁ f₂ B.L g₁ g₂) := by
  intro laws R _ X Y A B f₁ f₂ g₁ g₂ _ _ _ _ k _ _ _ β
  have bc : ∀ P : Out.PolAV (Sp R), ∃ (P' : Out.PolAV (Sp k)) (φ : P'.A.left ⟶ P.A.left),
      IsGrpPullback P'.A P.A (spMap β) φ ∧ LBIso P'.L (P.L.pull φ) := fun P => by
    obtain ⟨P', φ, hφ, -, hm, t, ht⟩ := laws.polBaseChange _ _ (spMap β) P
    refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ⟨t, ht⟩⟩
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
    rfl
  obtain ⟨X', x, hX, -⟩ := bc X
  obtain ⟨Y', y, hY, -⟩ := bc Y
  obtain ⟨A', a, hA, wL⟩ := bc A
  obtain ⟨B', b, hB, wM⟩ := bc B
  have := A.isAb.comm
  have := B.isAb.comm
  have := A'.isAb.comm
  have := B'.isAb.comm
  obtain ⟨f₁', m₁, e₁⟩ := exists_hom hX hA f₁
  obtain ⟨f₂', m₂, e₂⟩ := exists_hom hY hA f₂
  obtain ⟨g₁', m₃, e₃⟩ := exists_hom hX hB g₁
  obtain ⟨g₂', m₄, e₄⟩ := exists_hom hY hB g₂
  have W := weilEq_iff hX hY hA hB A.isLB B.isLB A'.isLB B'.isLB wL wM e₁ e₂ e₃ e₄ (𝟙 (Sp k))
  rw [Category.id_comp] at W
  let π : Over.mk ((X'.A ⊗ Y'.A).hom ≫ spMap β) ⟶ X.A ⊗ Y.A :=
    lift (Geo.Tor.pushPt hX.1.w (fst X'.A Y'.A)) (Geo.Tor.pushPt hY.1.w (snd X'.A Y'.A))
  have π₁ : π.left ≫ (fst X.A Y.A).left = (fst X'.A Y'.A).left ≫ x := by
    rw [← Over.comp_left, lift_fst]; rfl
  have π₂ : π.left ≫ (snd X.A Y.A).left = (snd X'.A Y'.A).left ≫ y := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hN : (cubeLB A.A ![fst X.A Y.A ≫ f₁, snd X.A Y.A ≫ f₂] A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hN' : (cubeLB B.A ![fst X.A Y.A ≫ g₁, snd X.A Y.A ≫ g₂] B.L).IsLB := DVR.linComb_isLB _ B.isLB _ _
  have hP : (cubeLB A'.A ![fst X'.A Y'.A ≫ f₁', snd X'.A Y'.A ≫ f₂'] A'.L).IsLB := DVR.linComb_isLB _ A'.isLB _ _
  have hP' : (cubeLB B'.A ![fst X'.A Y'.A ≫ g₁', snd X'.A Y'.A ≫ g₂'] B'.L).IsLB := DVR.linComb_isLB _ B'.isLB _ _
  have cA := cube_pull hA A.isLB A'.isLB wL (T' := X'.A ⊗ Y'.A) π.left (Over.w π)
    ![fst X'.A Y'.A ≫ f₁', snd X'.A Y'.A ≫ f₂'] ![fst X.A Y.A ≫ f₁, snd X.A Y.A ≫ f₂] fun i => by
      fin_cases i
      · show (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
        rw [Category.assoc, e₁, reassoc_of% π₁]
      · show (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
        rw [Category.assoc, e₂, reassoc_of% π₂]
  have cB := cube_pull hB B.isLB B'.isLB wM (T' := X'.A ⊗ Y'.A) π.left (Over.w π)
    ![fst X'.A Y'.A ≫ g₁', snd X'.A Y'.A ≫ g₂'] ![fst X.A Y.A ≫ g₁, snd X.A Y.A ≫ g₂] fun i => by
      fin_cases i
      · show (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
        rw [Category.assoc, e₃, reassoc_of% π₁]
      · show (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
        rw [Category.assoc, e₄, reassoc_of% π₂]
  refine ⟨fun H => W.1 (T.weil_pairing_eq_of_isomorphic_cube_pairings laws k X' Y' A' B' _ _ _ _ m₁ m₂ m₃ m₄ ?_), fun hR hβ H => ?_⟩
  · exact cA.trans hP (Geo.Tor.pull_isLB hN _) hP' (LBIso.trans (Geo.Tor.pull_isLB hN _) (Geo.Tor.pull_isLB hN' _) hP'
      (PowPrimitive.lbIso_linComb H _ _) cB.symm)
  · have H' := GlobalTheory.CM.lamEq_of_weilEq laws k X' Y' A' B' _ _ _ _ m₁ m₂ m₃ m₄ (W.2 H)
    have H'' := cA.symm.trans (Geo.Tor.pull_isLB hN _) hP (Geo.Tor.pull_isLB hN' _) (LBIso.trans hP hP' (Geo.Tor.pull_isLB hN' _) H' cB)
    let F := pullback.fst (X.A ⊗ Y.A).hom (spMap β)
    let p := pullback.snd (X.A ⊗ Y.A).hom (spMap β)
    have wF : F ≫ (X.A ⊗ Y.A).hom = p ≫ spMap β := pullback.condition
    let u : Over.mk p ⟶ X'.A := Over.homMk (hX.1.lift (F ≫ (fst X.A Y.A).left) p
      (by rw [Category.assoc, Over.w, wF])) (hX.1.lift_snd _ _ _)
    let v : Over.mk p ⟶ Y'.A := Over.homMk (hY.1.lift (F ≫ (snd X.A Y.A).left) p
      (by rw [Category.assoc, Over.w, wF])) (hY.1.lift_snd _ _ _)
    have hu : u.left ≫ x = F ≫ (fst X.A Y.A).left := hX.1.lift_fst _ _ _
    have hv : v.left ≫ y = F ≫ (snd X.A Y.A).left := hY.1.lift_fst _ _ _
    have hr : F = (lift u v).left ≫ π.left := by
      refine pullback.hom_ext (f := X.A.hom) (g := Y.A.hom) ?_ ?_
      · show F ≫ (fst X.A Y.A).left = (_ ≫ _) ≫ (fst X.A Y.A).left
        rw [Category.assoc, π₁, ← Category.assoc, ← Over.comp_left, lift_fst, hu]
      · show F ≫ (snd X.A Y.A).left = (_ ≫ _) ≫ (snd X.A Y.A).left
        rw [Category.assoc, π₂, ← Category.assoc, ← Over.comp_left, lift_snd, hv]
    refine T.lineBundleIso_descends_field_to_dedekindDomain R k β hβ (X.A ⊗ Y.A) (AbelianSchemeGerms.isAbelianScheme_tensor _ _ X.isAb Y.isAb) _ F p
      (IsPullback.of_hasPullback _ _) _ _ hN hN' ?_
      (LBIso.chartPull (Geo.Tor.chartPullSame _ _ _ _ (lift u v).left fun _ => hr)
        (Geo.Tor.chartPullSame _ _ _ _ (lift u v).left fun _ => hr) H'')
    obtain ⟨t, ht⟩ := exists_gen_cube_one A.isLB (𝟙_ _)
    obtain ⟨t', ht'⟩ := exists_gen_cube_one B.isLB (𝟙_ _)
    exact (cube_zero A.isLB f₁ f₂).symm.trans (Geo.Tor.pull_isLB hN _) (DVR.linComb_isLB _ A.isLB _ _) (Geo.Tor.pull_isLB hN' _)
      (LBIso.trans (DVR.linComb_isLB _ A.isLB _ _) (DVR.linComb_isLB _ B.isLB _ _) (Geo.Tor.pull_isLB hN' _)
        (IsoDescent.lbIso_of_gens A.isLB B.isLB _ _ _ _ t ht t' ht') (cube_zero B.isLB g₁ g₂))

end GlobalTheory.PairingFibre
end
