import Mathlib
import Development.AbelianVarietyTheory.Statements.LocalTrivialization.ConnectedSpaceTorus
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.WeightBundle
import Development.AbelianVarietyTheory.Definitions.Uniformization.NotExistsEvenTwistSymOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothProjOfFree
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BiTrivTransport
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfIsWtZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UU GlobalTheory.IndefiniteRowSideFullHecke.CubicalBundleRestrictions
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TrivDescentCompare

section General

theorem smooth_conn {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S}
    [GrpObj G] (Q : TQ G X) : Smooth G.hom ∧ GeometricallyConnected G.hom := by
  have := Q.q_hom
  have := Q.isAb.smooth
  have := Q.isAb.geomConnected
  have hs := Q.smooth_proj_of_free
  have : TwoUniqueSums X := twoUniqueSums_of_free X
  have sq := (H1.torsor_pullback Q.i Q.q Q.isKernel).map (Over.forget _)
  have hc : GeometricallyConnected Q.q.left := by
    have h₁ : GeometricallyConnected ((Over.forget _).map (snd (splitTorus S X) G)) :=
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) (IsPullback.of_hasPullback _ _)
        (GlobalTheory.Diag.geometricallyConnected_hom S X)
    have h₂ : Surjective ((Over.forget _).map Q.q) := Q.q_surj
    exact @GlobalTheory.geometricallyConnected_of_isPullback_of_surjective _ _ _ _ _ _ _ _ sq h₂ h₁
  rw [← Over.w Q.q]
  exact ⟨inferInstance, GeometricallyConnected.comp _ _⟩

theorem connected {S : Scheme.{0}} [ConnectedSpace S] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X) : ConnectedSpace G.left :=
  have := (smooth_conn Q).2
  GroupConn.connectedSpace_of_section G.hom (η : 𝟙_ (Over S) ⟶ G).left (Over.w _)

variable {Y Y' : Scheme.{0}} {L : LB Y} {L' : LB Y'} {F : Y' ⟶ Y}

theorem exists_iso_ratio (hL : L.IsLB) (hL' : L'.IsLB) {w₁ w₂ : LB.Iso L' (L.pull F)} (g₁ : w₁.IsGen) (g₂ : w₂.IsGen) :
    ∃ u : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z) (j : L.ι) (k : L'.ι), F (r y) ∈ L.U j → r y ∈ L'.U k →
      gw w₁ r y j k = gm r y ⊤ u * gw w₂ r y j k := by
  have h₁ := (isGen_iff _).1 g₁
  have h₂ := (isGen_iff _).1 g₂
  let W : L.ι × L'.ι → Y'.Opens := fun p => (L.pull F).U (fun _ => p.1) ⊓ L'.U p.2
  let v : ∀ p, Γ(Y', W p)ˣ := fun p => w₁.s (fun _ => p.1, p.2) * (w₂.s (fun _ => p.1, p.2))⁻¹
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z) p, gm r y (W p) (v p) =
      gw w₁ r y p.1 p.2 * (gw w₂ r y p.1 p.2)⁻¹ := fun Z r y p =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨u, hu⟩ := glue_unit ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hL (F x)
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, k), mem_pull.2 hj, hk⟩) v (fun p q x hx => by
      have a := h₁ _ (𝟙 Y') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      have b := h₂ _ (𝟙 Y') x p.1 q.1 p.2 q.2 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1) hx.1.2 hx.2.2
      rw [hv, hv, a, b, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
  refine ⟨u, fun Z r y j k hj hk => ?_⟩
  have hy : r y ∈ W (j, k) := ⟨mem_pull.2 hj, hk⟩
  rw [← gm_res r y (le_top : W (j, k) ≤ ⊤) hy u, hu, hv, inv_mul_cancel_right]

theorem iso_ext (hL : L.IsLB) (hL' : L'.IsLB) {w₁ w₂ : LB.Iso L' (L.pull F)} (g₁ : w₁.IsGen) (g₂ : w₂.IsGen)
    {Z : Scheme.{0}} (π : Z ⟶ Y') [Flat π] [Surjective π]
    (h : ∀ z J J', Good L z J → Good L' z J' → isoV w₁ z J J' π = isoV w₂ z J J' π) : w₁ = w₂ := by
  obtain ⟨a, ha⟩ := exists_iso_ratio hL hL' g₁ g₂
  have h1 : pullU π ⊤ a = 1 := unit_ext fun z _ => by
    obtain ⟨J, hJ⟩ := exists_good_pt hL z
    obtain ⟨J', hJ'⟩ := exists_good_pt hL' z
    have := (h z J J' hJ hJ').symm.trans (ha _ π z _ _ (hJ (π ≫ F)) (hJ' π))
    rw [gm_pull (𝟙 Z) π z ⊤ trivial, Category.id_comp, map_one]
    exact (mul_eq_right.1 this.symm)
  have h2 : a = 1 := Units.ext (GlobalTheory.FunDescent.app_injective π ⊤
    ((congrArg Units.val h1).trans (map_one _).symm))
  refine congrArg LB.Gen.mk (funext fun p => unit_ext fun y hy => ?_)
  have := ha _ (𝟙 _) y (p.1 PUnit.unit) p.2 (mem_pull.1 hy.1) hy.2
  rw [h2, map_one, _root_.one_mul] at this
  exact this

end General

section Restrict
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {G' H' : Over S'}
  [GrpObj G'] [IsCommMonObj G'] [GrpObj H'] {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
  {E : H'.left ⟶ H.left} {P : CP G} {P' : CP G'} {w : LB.Iso P'.L.L (P.L.L.pull F)} {i : H ⟶ G} {i' : H' ⟶ G'}

theorem cube_vals (hP : IsCPMap P' P f F hw w) {T : Over S'} {z : T.left} {J J'} (hJ : Good P.L.L z J)
    (hJ' : Good P'.L.L z J') : ∃ (W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ)
      (C : (T ⟶ G') → (T ⟶ G') → (T ⟶ G') → (T.left.presheaf.stalk z)ˣ), (∀ x, W x = isoV w z J J' x.left) ∧
      (∀ x y u, C x y u = cubV P.c (T := Over.mk (T.hom ≫ f)) z J (toBase hw x) (toBase hw y) (toBase hw u)) ∧
      (∀ x : T ⟶ G', val P.sym (x.left ≫ F) z J * W x = W x⁻¹ * val P'.sym x.left z J') ∧
      ∀ x y u, C x y u * W (x * y) * W (x * u) * W (y * u) * W 1 =
        W (x * y * u) * W x * W y * W u * cubV P'.c z J' x y u :=
  ⟨_, _, fun _ => rfl, fun _ _ _ => rfl, (hP.vals T z J' J hJ' hJ _ fun _ => rfl).2⟩

theorem exists_cubTriv_restrict [IsMonHom i'] (hP : IsCPMap P' P f F hw w) (hE : E ≫ H.hom = H'.hom ≫ f)
    (mul : ∀ (T : Over S') (x y : T ⟶ H'), toBase hE (x * y) = toBase hE x * toBase hE y)
    (hi : E ≫ i.left = i'.left ≫ F) (σ : CubTriv P.c i) :
    ∃ σ' : CubTriv P'.c i', (σ.Even → σ'.Even) ∧ ∀ (Z : Over S') (t : Z ⟶ H') (z : Z.left) (J) (J'), Good P.L.L z J →
      Good P'.L.L z J' → val σ.s (t.left ≫ E) z J =
        isoV w z J J' (t ≫ i').left * (isoV w z J J' (1 : Z ⟶ G').left)⁻¹ * val σ'.s t.left z J' := by
  have hc : ∀ k : Fin 2, ![i'.left, (1 : H' ⟶ G').left] k ≫ F = E ≫ ![i.left, (1 : H ⟶ G).left] k := fun k => by
    fin_cases k
    · exact hi.symm
    · refine (one_left_comp hP.mul H').trans ?_
      show _ = E ≫ (1 : H ⟶ G).left
      rw [one_left, ← Category.assoc, hE]
  obtain ⟨a, ha, Ha⟩ := CubTransport.exists_pmaps ((isGen_iff w).1 hP.gen) P.L.isLB P'.L.isLB E hc σ.s σ.gen
  have v : ∀ (Z : Over S') (t : Z ⟶ H') (z : Z.left) (J) (J'), Good P.L.L z J →
      Good P'.L.L z J' → val σ.s (t.left ≫ E) z J =
        isoV w z J J' (t ≫ i').left * (isoV w z J J' (1 : Z ⟶ G').left)⁻¹ * val a t.left z J' :=
    fun Z t z J J' hJ hJ' => by
    refine (CubTransport.val_pmaps hc Ha t.left hJ hJ').trans (congrArg (· * _) ?_)
    rw [Fin.prod_univ_two]
    show isoV w z J J' (t ≫ i').left ^ (1 : ℤ) * isoV w z J J' (t ≫ (1 : H' ⟶ G')).left ^ (-1 : ℤ) = _
    rw [MonObj.comp_one, zpow_one, zpow_neg, zpow_one]
  refine ⟨⟨a, ha, fun T x y u z J' hJ' => ?_⟩, fun hσ T x z J' hJ' => ?_, v⟩
  all_goals
    obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨W, C, hW, hC, c₁, c⟩ := cube_vals hP hJ hJ'
    have v' := fun t => v T t z J J' hJ hJ'
    simp only [← hW] at v'
  · have l : val σ.s ((x * y * u).left ≫ E) z J * val σ.s (x.left ≫ E) z J * val σ.s (y.left ≫ E) z J *
        val σ.s (u.left ≫ E) z J = C (x ≫ i') (y ≫ i') (u ≫ i') * val σ.s ((x * y).left ≫ E) z J *
        val σ.s ((x * u).left ≫ E) z J * val σ.s ((y * u).left ≫ E) z J := by
      have l := σ.cub (Over.mk (T.hom ≫ f)) (toBase hE x) (toBase hE y) (toBase hE u) z J hJ
      simp only [← mul, BiTransport.toBase_comp (hw := hw) hE hi] at l
      rw [hC]; exact l
    simp only [v', MonObj.mul_comp] at l
    apply Additive.ofMul.injective
    have c'' := congrArg Additive.ofMul (c (x ≫ i') (y ≫ i') (u ≫ i'))
    have l'' := congrArg Additive.ofMul l
    simp only [ofMul_mul, ofMul_inv] at c'' l'' ⊢
    linear_combination (norm := abel) l'' + c''
  · have l := hσ (Over.mk (T.hom ≫ f)) (toBase hE x) z J hJ
    have e : (toBase hE x)⁻¹ = toBase hE x⁻¹ := (map_inv (toBaseHom mul T) x).symm
    rw [e, BiTransport.toBase_comp (hw := hw) hE hi] at l
    change val σ.s ((x⁻¹).left ≫ E) z J = val P.sym ((x ≫ i').left ≫ F) z J * val σ.s (x.left ≫ E) z J at l
    simp only [v', GrpObj.inv_comp] at l
    show val a _ z J' = _ * val a _ z J'
    apply Additive.ofMul.injective
    have c'' := congrArg Additive.ofMul (c₁ (x ≫ i'))
    have l'' := congrArg Additive.ofMul l
    simp only [ofMul_mul, ofMul_inv] at c'' l'' ⊢
    linear_combination (norm := abel) l'' + c''

end Restrict

section Lift
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] [IsCommMonObj G]
  {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
  {P : CP G} {P' : CP G'} {w : LB.Iso P'.L.L (P.L.L.pull F)} {i : splitTorus S X ⟶ G} {i' : splitTorus S' X ⟶ G'}

end Lift

section Nil
variable {A : Type} [CommRing A] {J : Ideal A} {X : Type} [AddCommGroup X] {G : Over (Spec (CommRingCat.of A))}
  [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of (A ⧸ J)))} [GrpObj G'] [IsCommMonObj G']
  {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ red J} {P : CP G} {P' : CP G'}
  {w : LB.Iso P'.L.L (P.L.L.pull F)} {i : splitTorus _ X ⟶ G} {i' : splitTorus _ X ⟶ G'}

end Nil

section Descent
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] [IsCommMonObj G]

end Descent

section Iso
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {X : Type} [AddCommGroup X]

def IsEvenCubic (G : Over S) [GrpObj G] (u : Γ(G.left, ⊤)ˣ) : Prop :=
  ∀ (T : Over S) (U : (T ⟶ G) → Γ(T.left, ⊤)), (∀ x, U x = x.left.appTop.hom u.val) →
    U 1 = 1 ∧ (∀ x, U x⁻¹ = U x) ∧ ∀ x y v, U (x * y * v) * U x * U y * U v = U (x * y) * U (x * v) * U (y * v)

theorem isEvenCubic_iff {u : Γ(G.left, ⊤)ˣ} : IsEvenCubic G u ↔ ∀ (T : Over S) (z : T.left),
    (∀ x : T ⟶ G, gm (x⁻¹).left z ⊤ u = gm x.left z ⊤ u) ∧
    ∀ x y v : T ⟶ G, gm (x * y * v).left z ⊤ u * gm x.left z ⊤ u * gm y.left z ⊤ u * gm v.left z ⊤ u =
      gm (x * y).left z ⊤ u * gm (x * v).left z ⊤ u * gm (y * v).left z ⊤ u := by
  refine forall_congr' fun T => ?_
  let V : (T ⟶ G) → Γ(T.left, ⊤)ˣ := fun x => Units.map x.left.appTop.hom.toMonoidHom u
  have hV : ∀ (x : T ⟶ G) z, gm x.left z ⊤ u = gm (𝟙 T.left) z ⊤ (V x) := fun x z => gm_top _ z u
  simp only [hV, ← map_mul]
  refine ⟨fun h z => ?_, fun h U hU => ?_⟩
  · obtain ⟨-, a, b⟩ := h (fun x => (V x).val) fun _ => rfl
    simp only [← Units.val_mul, Units.val_inj] at a b
    exact ⟨fun x => by rw [a], fun x y v => by rw [b]⟩
  · have hU' : ∀ x, U x = (V x).val := hU
    have b : ∀ x y v, V (x * y * v) * V x * V y * V v = V (x * y) * V (x * v) * V (y * v) :=
      fun x y v => unit_ext fun z _ => (h z).2 x y v
    simp only [hU', ← Units.val_mul, Units.val_inj]
    refine ⟨?_, fun x => unit_ext fun z _ => (h z).1 x, b⟩
    have := b 1 1 1
    simp only [_root_.mul_one] at this
    exact congrArg Units.val (mul_eq_left.1 this)

theorem cpMap_unique (cu : ∀ u, IsEvenCubic G' u → u = 1) {P' : CP G'} {P : CP G} {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    {hw : F ≫ G.hom = G'.hom ≫ f} {w₁ w₂ : LB.Iso P'.L.L (P.L.L.pull F)} (h₁ : IsCPMap P' P f F hw w₁)
    (h₂ : IsCPMap P' P f F hw w₂) : w₁ = w₂ := by
  obtain ⟨u, hu⟩ := exists_iso_ratio P.L.isLB P'.L.isLB h₁.gen h₂.gen
  have e : u = 1 := cu u (isEvenCubic_iff.2 fun T z => by
    obtain ⟨J', hJ'⟩ := exists_good_pt P'.L.isLB z
    obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
    obtain ⟨A, C, hA, hC, a₂, a₃⟩ := cube_vals h₁ hJ hJ'
    obtain ⟨B, C', hB, hC', b₂, b₃⟩ := cube_vals h₂ hJ hJ'
    have k : ∀ x, A x = gm x.left z ⊤ u * B x := fun x => by
      rw [hA, hB]; exact hu _ x.left z _ _ (hJ (x.left ≫ F)) (hJ' x.left)
    have c : ∀ x y v, C x y v = C' x y v := fun x y v => (hC x y v).trans (hC' x y v).symm
    have a₁ := (h₁.vals T z J' J hJ' hJ A hA).1
    have c₁ : gm (1 : T ⟶ G').left z ⊤ u = 1 := by
      rw [k] at a₁
      exact mul_eq_right.1 (mul_right_cancel (a₁.symm.trans (h₂.vals T z J' J hJ' hJ B hB).1))
    simp only [k, c, c₁, _root_.one_mul] at a₂ a₃
    refine ⟨fun x => ?_, fun x y v => ?_⟩
    · have a := congrArg Additive.ofMul (a₂ x)
      have b := congrArg Additive.ofMul (b₂ x)
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at a b ⊢
      linear_combination (norm := abel) b - a
    · have a := congrArg Additive.ofMul (a₃ x y v)
      have b := congrArg Additive.ofMul (b₃ x y v)
      apply Additive.ofMul.injective
      simp only [ofMul_mul] at a b ⊢
      linear_combination (norm := abel) b - a)
  refine iso_ext P.L.isLB P'.L.isLB h₁.gen h₂.gen (𝟙 _) fun z J J' hJ hJ' => ?_
  rw [isoV, hu _ _ z _ _ (hJ (𝟙 _ ≫ F)) (hJ' _), e, map_one, _root_.one_mul, isoV]

theorem comp_of_eq {P : CP G} {P' : CP G'} {P'' : CP G''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {f'' : S'' ⟶ S}
    {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F'' : G''.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
    {hw' : F' ≫ G'.hom = G''.hom ≫ f'} (hw'' : F'' ≫ G.hom = G''.hom ≫ f'') (ef : f' ≫ f = f'') (eF : F' ≫ F = F'')
    {w : LB.Iso P'.L.L (P.L.L.pull F)} {w' : LB.Iso P''.L.L (P'.L.L.pull F')}
    (h : IsCPMap P' P f F hw w) (h' : IsCPMap P'' P' f' F' hw' w') :
    ∃ w'', IsCPMap P'' P f'' F'' hw'' w'' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (J J' J''),
      Good P.L.L z J → Good P'.L.L z J' → Good P''.L.L z J'' →
      isoV w'' z J J'' r = isoV w z J J' (r ≫ F') * isoV w' z J' J'' r := by
  subst ef eF
  obtain ⟨w'', T, H⟩ := h.exists_comp h' hw''
  refine ⟨w'', H, fun Z r z J J' J'' hJ hJ' hJ'' => ?_⟩
  rw [isoV, ← Category.assoc]
  exact T _ r z _ _ _ (hJ ((r ≫ F') ≫ F)) (hJ' (r ≫ F')) (hJ'' r)

theorem cpMap_congr {P : CP G} {P' : CP G'} {f f' : S' ⟶ S} {F F' : G'.left ⟶ G.left} (e : f = f') (e' : F = F')
    {hw w} (h : IsCPMap P' P f F hw w) (hw') : ∃ w', IsCPMap P' P f' F' hw' w' := by
  subst e e'
  exact ⟨w, h⟩

end Iso

section Endo
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] [IsCommMonObj G] {Q : TQ G X} {P : CP G}

end Endo

def CubicUnitOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (_ : TQ G X) (u : Γ(G.left, ⊤)ˣ), IsEvenCubic G u → u = 1

def DeltaOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (P : CP G) (i : splitTorus S X ⟶ G), IsMonHom i →
    ∀ (s : BiTriv P.c i) (σ : CubTriv P.c i) (T : Over S) (t t' : T ⟶ splitTorus S X) (z : T.left) (J), Good P.L.L z J →
      val σ.s (t * t').left z J = val s.s (lift t (t' ≫ i)).left z J * val σ.s t.left z J * val σ.s t'.left z J

def EquivDescOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (P : CP G) (s : BiTriv P.c Q.i) (σ : CubTriv P.c Q.i), σ.Even →
  ∀ a : LB.Gen (LB.LinComb P.L.L (K := Fin 2)
    ![((fst (splitTorus S X) G ≫ Q.i) * snd (splitTorus S X) G).left, (snd (splitTorus S X) G).left] ![1, -1]), a.IsGen →
  (∀ (T : Over S) (t : T ⟶ splitTorus S X) (x : T ⟶ G) (z : T.left) (J), Good P.L.L z J →
    val a (lift t x).left z J = val s.s (lift t x).left z J * val σ.s t.left z J) →
  (∀ (T : Over S) (t t' : T ⟶ splitTorus S X) (x : T ⟶ G) (z : T.left) (J), Good P.L.L z J →
    val a (lift (t * t') x).left z J = val a (lift t ((t' ≫ Q.i) * x)).left z J * val a (lift t' x).left z J) →
  ∃ (M : LB Q.B.left) (w : LB.Iso P.L.L (M.pull Q.q.left)), M.IsLB ∧ w.IsGen ∧
    ∀ (T : Over S) (t : T ⟶ splitTorus S X) (x : T ⟶ G) (z : T.left) (J) (j : M.ι), Good P.L.L z J →
      Q.q.left (x.left z) ∈ M.U j →
      gw w ((t ≫ Q.i) * x).left z j (J ((t ≫ Q.i) * x).left) * val a (lift t x).left z J = gw w x.left z j (J x.left)

def DescOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (P : CP G), Nonempty (BiTriv P.c Q.i) → (∃ σ : CubTriv P.c Q.i, σ.Even) → Nonempty (Q.Desc P)

def IsoDescOver (S' : Scheme.{0}) : Prop :=
  ∀ (S : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (Q : TQ G' X) (P' : CP G') (D : Q.Desc P')
  (B : Over S) [GrpObj B] [IsCommMonObj B] (M : CP B) (β : Q.B.left ⟶ B.left) (hβ : β ≫ B.hom = Q.B.hom ≫ f) (hw) (w),
  (∀ (T : Over S') (x y : T ⟶ Q.B), toBase hβ (x * y) = toBase hβ x * toBase hβ y) →
  IsCPMap P' M f (Q.q.left ≫ β) hw w → ∃ v, IsCPMap D.M M f β hβ v

def WtExistsOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (χ : X), ∃ (N : LB Q.B.left) (t : LB.Gen (N.pull Q.q.left)), N.IsLB ∧ Q.GenWt N t χ

def WtPresentedOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (χ : X), ∃ N t, IsWtBundle Q χ N t

def BiLiftAlong {A : Type} [CommRing A] (J : Ideal A) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (Q : TQ G X)
  (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] [IsCommMonObj G₀]
  (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G (red J) F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P (red J) F hw w →
  ∀ (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i₀ → TorusCompat (red J) F i₀ Q.i →
  Nonempty (BiTriv P₀.c i₀) → Nonempty (BiTriv P.c Q.i)

def CubLiftAlong {A : Type} [CommRing A] (J : Ideal A) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (Q : TQ G X)
  (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] [IsCommMonObj G₀]
  (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G (red J) F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P (red J) F hw w →
  ∀ (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i₀ → TorusCompat (red J) F i₀ Q.i →
  Nonempty (BiTriv P.c Q.i) → (∃ σ₀ : CubTriv P₀.c i₀, σ₀.Even) → ∃ σ : CubTriv P.c Q.i, σ.Even

def BiTrivLiftExt {A : Type} [CommRing A] (J : Ideal A) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (Q : TQ G X)
    (G' : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G'] [IsCommMonObj G']
    (F : G'.left ⟶ G.left) (hF : IsPullback F G'.hom G.hom (red J))
    (i' : splitTorus _ X ⟶ G'), IsMonHom i' → TorusCompat (red J) F i' Q.i →
    ∀ (P : CP G) (P' : CP G') (w : LB.Iso P'.L.L (P.L.L.pull F)), IsCPMap P' P (red J) F hF.w w →
    ∀ s' : BiTriv P'.c i', ∃! s : BiTriv P.c Q.i, BiRestricts (red J) w s s'

def EvenTrivLiftExt {A : Type} [CommRing A] (J : Ideal A) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (Q : TQ G X)
    (G' : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G'] [IsCommMonObj G']
    (F : G'.left ⟶ G.left) (hF : IsPullback F G'.hom G.hom (red J))
    (i' : splitTorus _ X ⟶ G'), IsMonHom i' → TorusCompat (red J) F i' Q.i →
    ∀ (P : CP G) (P' : CP G') (w : LB.Iso P'.L.L (P.L.L.pull F)), IsCPMap P' P (red J) F hF.w w →
    ∀ σ' : CubTriv P'.c i', σ'.Even →
      ∃ σ : CubTriv P.c Q.i, σ.Even ∧ CubRestricts (red J) w σ σ' ∧
        ∀ τ : CubTriv P.c Q.i, CubRestricts (red J) w τ σ' → τ = σ

def BiTrivExistsSym (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (P : CP G), Nonempty (BiTriv P.c Q.i)

section Clauses
variable {S : Scheme.{0}}

end Clauses

structure FirstOver (S : Scheme.{0}) : Prop where
  cubic : CubicUnitOver S
  biUniq : BiTrivUniqueOver S
  delta : DeltaOver S
  evenUniq : EvenTrivUniqueOver S
  equivDesc : EquivDescOver S
  desc : DescOver S
  isoDesc : IsoDescOver S
  wt : WtExistsOver S

structure TrivializationOver (S : Scheme.{0}) : Prop where
  biUniq : BiTrivUniqueOver S
  bimul : BimulTrivialOver S
  evenUniq : EvenTrivUniqueOver S
  descExists : DescExistsOver S
  descUnique : DescUniqueOver S
  descAdj : DescAdjOver S
  descDiag : DescDiagOver S
  wt : WtPresentedOver S

section Along
variable {A : Type} [CommRing A] {J : Ideal A}

end Along

def IsThickPoint (A : Type) [CommRing A] : Prop := ∃ _ : IsLocalRing A, IsNilpotent (IsLocalRing.maximalIdeal A)

example (k : Type) [Field k] : IsThickPoint k := ⟨inferInstance, 1, by rw [pow_one]; exact IsLocalRing.maximalIdeal_eq_bot⟩

structure FirstCore : Prop where
  field : ∀ (k : Type) [Field k], BiTrivExistsOver (Spec (CommRingCat.of k))
  base : ∀ (A : Type) [CommRing A], IsThickPoint A → FirstOver (Spec (CommRingCat.of A))
  biLift : ∀ (A : Type) [CommRing A] (J : Ideal A), IsThickPoint A → IsNilpotent J → BiLiftAlong J
  cubLift : ∀ (A : Type) [CommRing A] (J : Ideal A), IsThickPoint A → IsNilpotent J → CubLiftAlong J

structure TrivializationThickPoints : Prop where
  field : ∀ (k : Type) [Field k], BiTrivExistsOver (Spec (CommRingCat.of k))
  thick : ∀ (A : Type) [CommRing A], IsThickPoint A → BiTrivExistsSym (Spec (CommRingCat.of A))
  base : ∀ (A : Type) [CommRing A], IsThickPoint A → TrivializationOver (Spec (CommRingCat.of A))
  biLift : ∀ (A : Type) [CommRing A] (J : Ideal A), IsThickPoint A → IsNilpotent J → BiTrivLiftExt J
  evenLift : ∀ (A : Type) [CommRing A] (J : Ideal A), IsThickPoint A → IsNilpotent J → EvenTrivLiftExt J
  restricts : ∀ (A : Type) [CommRing A] (J : Ideal A), IsThickPoint A → IsNilpotent J → DescRestrictsAlong J

def First : Prop := CubicUnitSt ∧ BiTrivUniqSt ∧ BiTrivFieldSt ∧ BiTrivLiftSt ∧ CubTrivLiftSt ∧ CubTrivDeltaSt ∧
  EquivDescSt ∧ DescSt ∧ IsoDescSt ∧ WtBundleSt

section Diag
open GlobalTheory.PairingLevels

variable {S : Scheme.{0}} {G : Over S} {Y : Over S} {L : LB G.left}

theorem rep_pull {K : Type} [Fintype K] {V : Over S} {φ : K → (V.left ⟶ G.left)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (p : Y ⟶ V) :
    Rep L (∑ k, ε k • FreeAbelianGroup.of (p.left ≫ φ k)) (fun Z r z J => val t (r ≫ p).left z J) :=
  ⟨K, inferInstance, _, _, LB.pullGen L φ ε t p.left, DVR.pullGen_isGen _ _ _ _ ht _, rfl,
    fun _ _ _ _ hJ => val_pull hJ _ _ _⟩

theorem exists_gen_of_rep (hL : L.IsLB) {D} {f : ValFam L Y} (h : Rep L D f) {K : Type} [Fintype K]
    (φ : K → (Y.left ⟶ G.left)) (ε : K → ℤ) (hD : D = ∑ k, ε k • FreeAbelianGroup.of (φ k)) :
    ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen ∧
      ∀ (Z : Over S) (r : Z ⟶ Y) (z : Z.left) (J), Good L z J → val u r.left z J = f Z r z J := by
  obtain ⟨K', _, φ', ε', t, ht, hs, hv⟩ := h
  obtain ⟨u, hu, k⟩ := exists_gen hL (φ' := φ) (ε' := ε) (fun U _ g => by
    have := congrArg (FreeAbelianGroup.lift (fun q => Additive.ofMul (g q))) (hs.trans hD)
    simp only [map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of] at this
    apply Additive.ofMul.injective
    simpa only [ofMul_prod, ofMul_zpow] using this) t ht
  exact ⟨u, hu, fun Z r z J hJ => (k _ _ z J hJ).trans (hv Z r z J hJ)⟩

variable [GrpObj G] [IsCommMonObj G] {H : Over S} [GrpObj H] [IsCommMonObj H]

end Diag

section Invariant
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem act_q (Q : TQ G X) {T : Over S} (t : T ⟶ splitTorus S X) (x : T ⟶ G) :
    ((t ≫ Q.i) * x).left ≫ Q.q.left = x.left ≫ Q.q.left := by
  have := Q.q_hom
  rw [← Over.comp_left, MonObj.mul_comp, Q.comp_i_q, _root_.one_mul, Over.comp_left]

end Invariant

section Torus
open GlobalTheory.PairingLevels
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]

theorem biTriv_of_cubTriv {L : RigLB H} {c : CubicalStr H L} (σ : CubTriv c (𝟙 H)) : Nonempty (BiTriv c (𝟙 H)) := by
  have R : ∀ p : H ⊗ H ⟶ H, Rep L.L (pt p - pt (1 : H ⊗ H ⟶ H)) (fun Z r z J => val σ.s (r ≫ p).left z J) :=
    fun p => (rep_pull σ.gen p).congr (by
      rw [Fin.sum_univ_two]
      show (1 : ℤ) • pt (p ≫ 𝟙 H) + (-1 : ℤ) • pt (p ≫ (1 : H ⟶ H)) = _
      rw [MonObj.comp_one, Category.comp_id]
      abel) fun _ _ _ _ => rfl
  obtain ⟨a, ha, v⟩ := exists_gen_of_rep L.isLB
    (((R (fst H H * snd H H)).mul (R (fst H H)).inv).mul (R (snd H H)).inv) (lamφ (𝟙 H)) Oε (by
    rw [Fin.sum_univ_four]
    show _ = (1 : ℤ) • pt ((fst H H ≫ 𝟙 H) * snd H H) + (-1 : ℤ) • pt (fst H H ≫ 𝟙 H) + (-1 : ℤ) • pt (snd H H) +
      (1 : ℤ) • pt (1 : H ⊗ H ⟶ H)
    rw [Category.comp_id]
    abel)
  have v' : ∀ (Z : Over S) (t x : Z ⟶ H) (z : Z.left) (J), Good L.L z J → val a (lift t x).left z J =
      val σ.s (t * x).left z J * (val σ.s t.left z J)⁻¹ * (val σ.s x.left z J)⁻¹ := fun Z t x z J hJ => by
    simpa only [MonObj.comp_mul, lift_fst, lift_snd] using v Z (lift t x) z J hJ
  refine ⟨⟨a, ha, fun T t t' x z J hJ => ?_, fun T t t' x z J hJ => ?_⟩⟩
  all_goals
    have b := congrArg Additive.ofMul (σ.cub T t t' x z J hJ)
    rw [v' _ _ _ _ _ hJ, v' _ _ _ _ _ hJ, v' _ _ _ _ _ hJ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, Category.comp_id, ← _root_.mul_assoc t] at b ⊢
    linear_combination (norm := abel) b

theorem exists_cubTriv_push {i : H ⟶ G} [IsMonHom i] {P : CP G} {P₀ : CP H} {hw w}
    (hP : IsCPMap P₀ P (𝟙 S) i.left hw w) (σ₀ : CubTriv P₀.c (𝟙 H)) (e₀ : σ₀.Even) : ∃ σ : CubTriv P.c i, σ.Even := by
  have hc : ∀ k : Fin 2, ![(𝟙 H :).left, (1 : H ⟶ H).left] k ≫ i.left = 𝟙 _ ≫ ![i.left, (1 : H ⟶ G).left] k :=
    fun k => by
    fin_cases k
    · rfl
    · exact (congrArg (·.left) (MonObj.one_comp i)).trans (Category.id_comp _).symm
  have up : ∀ φ : Fin 2 → (H.left ⟶ G.left), (∀ k, ![(𝟙 H :).left, (1 : H ⟶ H).left] k ≫ i.left = 𝟙 _ ≫ φ k) →
      ∃ t : LB.Gen (LB.LinComb P.L.L φ ![1, -1]), t.IsGen ∧ PMaps w _ φ _ σ₀.s t (𝟙 _) := fun φ hφ => by
    obtain rfl : φ = fun k => ![(𝟙 H :).left, (1 : H ⟶ H).left] k ≫ i.left :=
      funext fun k => ((hφ k).trans (Category.id_comp _)).symm
    obtain ⟨t, ht, h⟩ := exists_up ((isGen_iff w).1 hP.gen) P.L.isLB P₀.L.isLB σ₀.s σ₀.gen
    refine ⟨t, ht, fun Z r z p q hp hq => ?_⟩
    rw [Category.comp_id]
    exact h Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
  obtain ⟨a, ha, Ha⟩ := up _ hc
  have v : ∀ (Z : Over S) (t : Z ⟶ H) (z : Z.left) (J) (J'), Good P.L.L z J → Good P₀.L.L z J' → val a t.left z J =
      isoV w z J J' t.left * (isoV w z J J' (1 : Z ⟶ H).left)⁻¹ * val σ₀.s t.left z J' := fun Z t z J J' hJ hJ' => by
    refine (congrArg (fun r => val a r z J) (Category.comp_id _).symm).trans
      ((CubTransport.val_pmaps hc Ha t.left hJ hJ').trans (congrArg (· * _) ?_))
    rw [Fin.prod_univ_two]
    show isoV w z J J' (t ≫ 𝟙 H).left ^ (1 : ℤ) * isoV w z J J' (t ≫ (1 : H ⟶ H)).left ^ (-1 : ℤ) = _
    rw [MonObj.comp_one, Category.comp_id, zpow_one, zpow_neg, zpow_one]
  refine ⟨⟨a, ha, fun T x y u z J hJ => ?_⟩, fun T x z J hJ => ?_⟩
  all_goals
    obtain ⟨J', hJ'⟩ := exists_good_pt P₀.L.isLB z
    obtain ⟨W, C, hW, hC, c₁, c⟩ := cube_vals hP hJ hJ'
    have v' := fun t => v T t z J J' hJ hJ'
    simp only [← hW] at v'
  · let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
    have e : ∀ b : T ⟶ H, toBase hw b = ρ ≫ b ≫ i := fun b => Over.OverMorphism.ext (Category.id_comp _).symm
    have e' : (lift (toBase hw x) (lift (toBase hw y) (toBase hw u))).left =
        (lift (x ≫ i) (lift (y ≫ i) (u ≫ i))).left := by
      rw [e, e, e, ← comp_lift, ← comp_lift]; exact Category.id_comp _
    have k : C x y u = cubV P.c z J (x ≫ i) (y ≫ i) (u ≫ i) := (hC x y u).trans
      (congrArg (fun r => val (L := P.L.L) (φ := thφ G (x3 G)) (ε := thε) P.c.t r z J) e')
    have b := congrArg Additive.ofMul (σ₀.cub T x y u z J' hJ')
    have d := congrArg Additive.ofMul (c x y u)
    apply Additive.ofMul.injective
    simp only [v', k, ofMul_mul, ofMul_inv, Category.comp_id] at b d ⊢
    linear_combination (norm := abel) b - d
  · have b := congrArg Additive.ofMul (e₀ T x z J' hJ')
    have d := congrArg Additive.ofMul (c₁ x)
    show val a _ z J = val P.sym (x.left ≫ i.left) z J * val a _ z J
    apply Additive.ofMul.injective
    simp only [v', ofMul_mul, ofMul_inv, Category.comp_id] at b d ⊢
    linear_combination (norm := abel) b - d

end Torus

theorem exists_even_lift {A : Type} [CommRing A] {J : Ideal A} (hb : BiLiftAlong J) (hc : CubLiftAlong J)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over (Spec (CommRingCat.of A))}
    [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of (A ⧸ J)))} [GrpObj G'] [IsCommMonObj G']
    {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ red J} {P : CP G} {P' : CP G'} {w}
    (hP : IsCPMap P' P (red J) F hw w) {i : splitTorus _ X ⟶ G} {i' : splitTorus _ X ⟶ G'} [IsMonHom i] [IsMonHom i']
    (hi : TorusCompat (red J) F i' i) (h : ∃ σ' : CubTriv P'.c i', σ'.Even) : ∃ σ : CubTriv P.c i, σ.Even := by
  obtain ⟨σ', e'⟩ := h
  obtain ⟨P₀, w₀, h₀⟩ := exists_pull P (toBase_mul_of_isMonHom i (by simp))
  obtain ⟨P₁, w₁, h₁⟩ := exists_pull P' (toBase_mul_of_isMonHom i' (by simp))
  have hh : (SplitTorus.bcMap (red J) X ≫ i.left) ≫ G.hom = (splitTorus _ X).hom ≫ red J ≫ 𝟙 _ := by
    rw [Category.assoc, Over.w, SplitTorus.bcMap_hom, Category.comp_id]
  obtain ⟨w₂, h₂, -⟩ := comp_of_eq hh ((Category.id_comp _).trans (Category.comp_id _).symm)
    (torusCompat_iff.1 hi).symm hP h₁
  obtain ⟨w₃, h₃, -⟩ := (isCPMap_comp_cancel _ _ _ (𝟙 _) (red J) G _ _ P P₀ P₁ _ _ w₀ _
    (SplitTorus.bcMap_hom (red J) X) hh h₀).2 (BiextCheck.toBase_mul_bcMap _) w₂ h₂
  obtain ⟨σ₁, e₁, -⟩ := exists_cubTriv_restrict (i' := 𝟙 _) (E := 𝟙 _) h₁ (by simp)
    (toBase_mul_of_isMonHom (𝟙 _) _) rfl σ'
  have gp := SplitTorus.isGrpPullback_bcMap (red J) X
  obtain ⟨σ₀, e₀⟩ := hc X _ (TQ.torus _ X) _ _ _ gp P₀ P₁ w₃ h₃ (𝟙 _) inferInstance (torusCompat_bcMap _)
    (hb X _ (TQ.torus _ X) _ _ _ gp P₀ P₁ w₃ h₃ (𝟙 _) inferInstance (torusCompat_bcMap _) (biTriv_of_cubTriv σ₁))
    ⟨σ₁, e₁ e'⟩
  exact exists_cubTriv_push h₀ σ₀ e₀

def IsBase (A : Type) [CommRing A] : Prop :=
  ConnectedSpace (Spec (CommRingCat.of A)) ∧ ∃ J : Ideal A, IsNilpotent J ∧ IsReduced (A ⧸ J)

example (A : Type) [CommRing A] [IsDomain A] : IsBase A :=
  ⟨inferInstance, ⊥, IsNilpotent.zero, isReduced_of_injective _ (RingEquiv.quotientBot A).injective⟩

def EquivDescFull (S : Scheme.{0}) : Prop := ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (G : Over S) [GrpObj G] (Q : TQ G X) (L : LB G.left), L.IsLB →
  ∀ a : LB.Gen (LB.LinComb L (K := Fin 2)
    ![((fst (splitTorus S X) G ≫ Q.i) * snd (splitTorus S X) G).left, (snd (splitTorus S X) G).left] ![1, -1]), a.IsGen →
  (∀ (T : Over S) (t t' : T ⟶ splitTorus S X) (x : T ⟶ G) (z : T.left) (J), Good L z J →
    val a (lift (t * t') x).left z J = val a (lift t ((t' ≫ Q.i) * x)).left z J * val a (lift t' x).left z J) →
  ∃ (M : LB Q.B.left) (w : LB.Iso L (M.pull Q.q.left)), M.IsLB ∧ w.IsGen ∧
    ∀ (T : Over S) (t : T ⟶ splitTorus S X) (x : T ⟶ G) (z : T.left) (J) (j : M.ι), Good L z J →
      Q.q.left (x.left z) ∈ M.U j →
      gw w ((t ≫ Q.i) * x).left z j (J ((t ≫ Q.i) * x).left) * val a (lift t x).left z J = gw w x.left z j (J x.left)

def WtFullOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (χ : X), ∃ (N : LB Q.B.left) (t : LB.Gen (N.pull Q.q.left)), N.IsLB ∧ Q.GenWt N t χ ∧
      ∃ u : LB.Gen (abelian₂ Q.B N), u.IsGen

def LamTrivialOver (S : Scheme.{0}) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (Q : TQ G X) (χ : X) (N : LB Q.B.left) (t : LB.Gen (N.pull Q.q.left)), N.IsLB → Q.GenWt N t χ →
      ∃ u : LB.Gen (abelian₂ Q.B N), u.IsGen

def CubLiftFull {A : Type} [CommRing A] (J : Ideal A) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G]
  (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] [IsCommMonObj G₀]
  (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G (red J) F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P (red J) F hw w →
  ∀ (i : splitTorus _ X ⟶ G) (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i → IsMonHom i₀ → TorusCompat (red J) F i₀ i →
  Nonempty (BiTriv P.c i) → (∃ σ₀ : CubTriv P₀.c i₀, σ₀.Even) → ∃ σ : CubTriv P.c i, σ.Even

section MoreClauses
variable {S : Scheme.{0}}

end MoreClauses

structure FirstOn : Prop where
  cubicUnit : ∀ (A : Type) [CommRing A], IsBase A → CubicUnitOver (Spec (CommRingCat.of A))
  biTrivUniq : ∀ (A : Type) [CommRing A], IsBase A → BiTrivUniqueOver (Spec (CommRingCat.of A))
  biTrivField : ∀ (k : Type) [Field k], BiTrivExistsOver (Spec (CommRingCat.of k))
  biTrivLift : ∀ (A : Type) [CommRing A] (J : Ideal A), IsBase A → IsNilpotent J → BiLiftAlong J
  cubTrivLift : ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsBase A → IsNilpotent J → CubLiftFull J
  cubTrivDelta : ∀ (A : Type) [CommRing A], IsBase A →
    DeltaOver (Spec (CommRingCat.of A)) ∧ EvenTrivUniqueOver (Spec (CommRingCat.of A))
  equivDesc : ∀ (A : Type) [CommRing A], IsBase A → EquivDescFull (Spec (CommRingCat.of A))
  desc : ∀ (A : Type) [CommRing A], IsBase A → DescOver (Spec (CommRingCat.of A))
  isoDesc : ∀ (A : Type) [CommRing A], IsBase A → IsoDescOver (Spec (CommRingCat.of A))
  wtBundle : ∀ (A : Type) [CommRing A] [IsLocalRing A], IsBase A → WtFullOver (Spec (CommRingCat.of A))

structure TrivializationClauses : Prop where
  biTriv_exists_field : ∀ (k : Type) [Field k], BiTrivExistsOver (Spec (CommRingCat.of k))
  biTriv_exists_thick : ∀ (A : Type) [CommRing A] [IsLocalRing A], IsNilpotent (IsLocalRing.maximalIdeal A) →
    BiTrivExistsOver (Spec (CommRingCat.of A))
  biTriv_unique : ∀ (A : Type) [CommRing A], IsBase A → BiTrivUniqueOver (Spec (CommRingCat.of A))
  biTriv_lift : ∀ (A : Type) [CommRing A] (J : Ideal A), IsBase A → IsNilpotent J → BiTrivLiftExt J
  bimul_trivial : ∀ (A : Type) [CommRing A], IsBase A → BimulTrivialOver (Spec (CommRingCat.of A))
  evenTriv_lift : ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsBase A → IsNilpotent J →
    EvenTrivLiftAlong J
  evenTriv_unique : ∀ (A : Type) [CommRing A], IsBase A → EvenTrivUniqueOver (Spec (CommRingCat.of A))
  even_defect : ∀ (A : Type) [CommRing A] [IsLocalRing A], IsNilpotent (IsLocalRing.maximalIdeal A) →
    EvenDefectOver (Spec (CommRingCat.of A))
  end_preserves : ∀ (A : Type) [CommRing A], IsBase A → EndPreservesTorusOver (Spec (CommRingCat.of A))
  diag_triv : ∀ (A : Type) [CommRing A], IsBase A → DiagTrivOver (Spec (CommRingCat.of A))
  desc_exists : ∀ (A : Type) [CommRing A], IsBase A → DescExistsOver (Spec (CommRingCat.of A))
  desc_unique : ∀ (A : Type) [CommRing A], IsBase A → DescUniqueOver (Spec (CommRingCat.of A))
  equivDesc_unique : ∀ (A : Type) [CommRing A], IsBase A → EquivDescUniqueOver (Spec (CommRingCat.of A))
  desc_restricts : ∀ (A : Type) [CommRing A] (J : Ideal A), IsBase A → IsNilpotent J → DescRestrictsAlong J
  desc_adj : ∀ (A : Type) [CommRing A], IsBase A → DescAdjOver (Spec (CommRingCat.of A))
  desc_diag : ∀ (A : Type) [CommRing A], IsBase A → DescDiagOver (Spec (CommRingCat.of A))
  wtBundle : ∀ (A : Type) [CommRing A] [IsLocalRing A], IsBase A → WtBundleOver (Spec (CommRingCat.of A))

structure FirstShared : Prop where
  cubicUnit : ∀ (A : Type) [CommRing A], IsBase A → CubicUnitOver (Spec (CommRingCat.of A))
  biTrivUniq : ∀ (A : Type) [CommRing A], IsBase A → BiTrivUniqueOver (Spec (CommRingCat.of A))
  biTrivField : ∀ (k : Type) [Field k], BiTrivExistsOver (Spec (CommRingCat.of k))
  biTrivLift : ∀ (A : Type) [CommRing A] (J : Ideal A), IsBase A → IsNilpotent J → BiLiftAlong J
  cubTrivLift : ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsBase A → IsNilpotent J → CubLiftFull J
  cubTrivDelta : ∀ (A : Type) [CommRing A], IsBase A →
    DeltaOver (Spec (CommRingCat.of A)) ∧ EvenTrivUniqueOver (Spec (CommRingCat.of A))
  equivDesc : ∀ (A : Type) [CommRing A], IsBase A → EquivDescOver (Spec (CommRingCat.of A))
  desc : ∀ (A : Type) [CommRing A], IsBase A → DescOver (Spec (CommRingCat.of A))
  isoDesc : ∀ (A : Type) [CommRing A], IsBase A → IsoDescOver (Spec (CommRingCat.of A))
  wtBundle : ∀ (A : Type) [CommRing A] [IsLocalRing A], IsBase A → WtExistsOver (Spec (CommRingCat.of A))

structure Shared : Prop where
  biTriv_exists_field : ∀ (k : Type) [Field k], BiTrivExistsOver (Spec (CommRingCat.of k))
  biTriv_exists_thick : ∀ (A : Type) [CommRing A] [IsLocalRing A], IsNilpotent (IsLocalRing.maximalIdeal A) →
    BiTrivExistsSym (Spec (CommRingCat.of A))
  biTriv_unique : ∀ (A : Type) [CommRing A], IsBase A → BiTrivUniqueOver (Spec (CommRingCat.of A))
  biTriv_lift : ∀ (A : Type) [CommRing A] (J : Ideal A), IsBase A → IsNilpotent J → BiTrivLiftExt J
  bimul_trivial : ∀ (A : Type) [CommRing A], IsBase A → BimulTrivialOver (Spec (CommRingCat.of A))
  evenTriv_lift : ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsBase A → IsNilpotent J →
    EvenTrivLiftAlong J
  evenTriv_unique : ∀ (A : Type) [CommRing A], IsBase A → EvenTrivUniqueOver (Spec (CommRingCat.of A))
  diag_triv : ∀ (A : Type) [CommRing A], IsBase A → DiagTrivOver (Spec (CommRingCat.of A))
  desc_exists : ∀ (A : Type) [CommRing A], IsBase A → DescExistsOver (Spec (CommRingCat.of A))
  desc_unique : ∀ (A : Type) [CommRing A], IsBase A → DescUniqueOver (Spec (CommRingCat.of A))
  equivDesc_unique : ∀ (A : Type) [CommRing A], IsBase A → EquivDescUniqueOver (Spec (CommRingCat.of A))
  desc_restricts : ∀ (A : Type) [CommRing A] (J : Ideal A), IsBase A → IsNilpotent J → DescRestrictsAlong J
  desc_adj : ∀ (A : Type) [CommRing A], IsBase A → DescAdjOver (Spec (CommRingCat.of A))
  desc_diag : ∀ (A : Type) [CommRing A], IsBase A → DescDiagOver (Spec (CommRingCat.of A))
  wtBundle : ∀ (A : Type) [CommRing A] [IsLocalRing A], IsBase A → WtBundleOver (Spec (CommRingCat.of A))

structure FirstOnly : Prop where
  equivDesc : ∀ (A : Type) [CommRing A], IsBase A → EquivDescFull (Spec (CommRingCat.of A))
  lam : ∀ (A : Type) [CommRing A] [IsLocalRing A], IsBase A → LamTrivialOver (Spec (CommRingCat.of A))

structure TorusPreservingClauses : Prop where
  end_preserves : ∀ (A : Type) [CommRing A], IsBase A → EndPreservesTorusOver (Spec (CommRingCat.of A))
  even_defect : ∀ (A : Type) [CommRing A] [IsLocalRing A], IsNilpotent (IsLocalRing.maximalIdeal A) →
    EvenDefectOver (Spec (CommRingCat.of A))
  biTriv_exists_thick : ∀ (A : Type) [CommRing A] [IsLocalRing A], IsNilpotent (IsLocalRing.maximalIdeal A) →
    BiTrivExistsOver (Spec (CommRingCat.of A))

def FirstLiftWide : Prop := ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
    [IsCommMonObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left)
    (hw), IsGrpPullback G₀ G (red J) F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P (red J) F hw w →
    ∀ (i : splitTorus _ X ⟶ G) (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i → IsMonHom i₀ → TorusCompat (red J) F i₀ i →
      (Nonempty (BiTriv P₀.c i₀) → Nonempty (BiTriv P.c i)) ∧
      ((∃ σ₀ : CubTriv P₀.c i₀, σ₀.Even) → ∃ σ : CubTriv P.c i, σ.Even)

def TrivializationLiftConnected : Prop := ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J →
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G]
    (G' : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G'] [IsCommMonObj G'] [ConnectedSpace G'.left]
    (F : G'.left ⟶ G.left) (hF : IsPullback F G'.hom G.hom (red J))
    (i : splitTorus _ X ⟶ G) (i' : splitTorus _ X ⟶ G'), IsMonHom i → IsMonHom i' → TorusCompat (red J) F i' i →
    ∀ (P : CP G) (P' : CP G') (w : LB.Iso P'.L.L (P.L.L.pull F)), IsCPMap P' P (red J) F hF.w w →
    ∀ s' : BiTriv P'.c i', ∃! s : BiTriv P.c i, BiRestricts (red J) w s s'

end GlobalTheory.TrivDescentCompare
end
