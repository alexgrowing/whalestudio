import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMapsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqTopOfClosedFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsVeryAmpleH1Zero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAbelianSchemeOfCompatibleThickeningsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DescendedBundleAmpleSpecialFibreStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AlgTower

section Bundles
variable {X X' Y Y' Z : Scheme.{0}}

theorem triv_chart {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h) (t : Triv A) : Triv A' := by
  obtain ⟨t, ht⟩ := t
  exact gen_chartPull a t ht

def chartDivTriv (A : LB X) : ChartPull (LB.div A (Inh.trivLB X)) A (𝟙 X) where
  idx p := p.1
  le _ _ hy := hy.1
  g y p q hp hq := (gm_div (Inh.trivLB X) A (𝟙 X) y p q ⟨hp, hq⟩).trans
    ((congrArg (_ * ·⁻¹) (map_one _)).trans (by rw [inv_one, _root_.mul_one]))

def chartTrivDiv (A : LB X) : ChartPull A (LB.div A (Inh.trivLB X)) (𝟙 X) where
  idx i := (i, PUnit.unit)
  le _ _ hy := ⟨hy, trivial⟩
  g y i j hi hj := ((chartDivTriv A).g y (i, PUnit.unit) (j, PUnit.unit) ⟨hi, trivial⟩ ⟨hj, trivial⟩).symm

theorem triv_of_lbIso {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B) (t : Triv A) : Triv B :=
  triv_chart (chartTrivDiv B) (LBIso.trans (Inh.trivLB_isLB X) hA hB (triv_chart (chartDivTriv A) t) h)

def chartPullDiv (H P : LB X) (f : Y ⟶ X) :
    ChartPull ((LB.div H P).pull f) (LB.div (H.pull f) (P.pull f)) (𝟙 Y) where
  idx J := (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
  le J y hy := ⟨mem_pull.2 (mem_pull.1 hy).1, mem_pull.2 (mem_pull.1 hy).2⟩
  g y J J' hj hj' := by
    have a := mem_pull.1 hj
    have a' := mem_pull.1 hj'
    refine (gm_pull_g (LB.div H P) f (𝟙 Y) y J J' hj hj').trans ((gm_div P H _ y _ _ ⟨a, a'⟩).trans (Eq.symm ?_))
    refine (gm_div (P.pull f) (H.pull f) (𝟙 Y) y (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2)
      ⟨⟨mem_pull.2 a.1, mem_pull.2 a.2⟩, mem_pull.2 a'.1, mem_pull.2 a'.2⟩).trans ?_
    exact congrArg₂ (fun u v => u * v⁻¹) (gm_pull_g H f (𝟙 Y) y _ _ (mem_pull.2 a.1) (mem_pull.2 a'.1))
      (gm_pull_g P f (𝟙 Y) y _ _ (mem_pull.2 a.2) (mem_pull.2 a'.2))

theorem lbIso_factor {P H : LB X} {b : Y ⟶ X} (h : LBIso (P.pull b) (H.pull b)) (j : Z ⟶ Y) (f : Z ⟶ X)
    (e : f = j ≫ b) : LBIso (P.pull f) (H.pull f) :=
  h.chartPull (chartPullSame P _ _ _ j fun _ => e) (chartPullSame H _ _ _ j fun _ => e)

theorem triv_transfer {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {F : X' ⟶ X} (w : LBIso L' (L.pull F))
    {K : Type} [Fintype K] (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ρ : Z ⟶ Y') (h : Z ⟶ Y)
    (e : ∀ k, (ρ ≫ φ' k) ≫ F = h ≫ φ k) (t : Triv (LB.LinComb L' φ' ε)) :
    Triv ((LB.LinComb L φ ε).pull h) := by
  obtain ⟨w, hw⟩ := w
  exact triv_chart (chartPullOut L φ ε h _ e) (triv_of_lbIso (DVR.linComb_isLB _ hL' _ _) (DVR.linComb_isLB _ hL _ _)
    (iso_linComb ((isGen_iff w).1 hw) (fun k => ρ ≫ φ' k) ε)
    (triv_chart (chartPullSame L' _ φ' ε ρ fun _ => rfl) t))

end Bundles

section Points
variable {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
  {f : S' ⟶ S} {b : B'.left ⟶ B.left}

omit [IsCommMonObj B] [IsCommMonObj B'] in

theorem exists_lift (h : IsGrpPullback B' B f b) (T : Over S') (x : Over.mk (T.hom ≫ f) ⟶ B) :
    ∃ x' : T ⟶ B', pushPt h.1.w x' = x :=
  ⟨Over.homMk (h.1.lift x.left T.hom (Over.w x)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

variable {M : LB B.left} (hM : M.IsLB) (M' : CP B') (h : IsGrpPullback B' B f b) (w : LBIso M'.L.L (M.pull b))
include hM h w

theorem triv_theta (T : Over S') (U : Over.mk (T.hom ≫ f) ⟶ G3 B) : Triv ((Theta B M).pull U.left) := by
  choose x hx using fun i => exists_lift h T (U ≫ x3 B i)
  refine triv_transfer hM M'.L.isLB w (thφ B' (x3 B')) (thφ B (x3 B)) thε (lift (x 0) (lift (x 1) (x 2))).left U.left
    (fun I => ?_) ⟨M'.c.t, M'.c.isGen⟩
  have e : lift (x 0) (lift (x 1) (x 2)) ≫ psum B' (x3 B') I.down = psum B' x I.down :=
    (psum_hom (preHom _) (x3 B') I.down).trans (congrArg (fun z => psum B' z I.down) (funext fun i => by
      fin_cases i <;> simp [preHom, x3]))
  exact (congrArg (fun q => q.left ≫ b) e).trans (psum_push h x (x3 B) U hx I.down)

theorem triv_sym (T : Over S') (U : Over.mk (T.hom ≫ f) ⟶ B) :
    Triv ((LB.LinComb M (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]).pull U.left) := by
  obtain ⟨x, hx⟩ := exists_lift h T U
  refine triv_transfer hM M'.L.isLB w _ _ _ x.left U.left (fun k => ?_) ⟨M'.sym, M'.sym_gen⟩
  have e : pushPt h.1.w x⁻¹ = U⁻¹ := hx ▸ map_inv (pushHom h T) x
  fin_cases k
  · exact congrArg (fun q => q.left) e
  · exact (congrArg (· ≫ b) (Category.comp_id _)).trans
      ((congrArg (fun q => q.left) hx).trans (Category.comp_id _).symm)

end Points

section Complete
variable (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [IsAdicComplete (IsLocalRing.maximalIdeal V) V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B] [IsCommMonObj B]
  (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {M : LB B.left} (hM : M.IsLB)
  {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))}
  {b : ∀ e, (Y e).left ⟶ B.left}
include hG hB hp hM

theorem triv_theta_of_levels [∀ e, GrpObj (Y e)] [∀ e, IsCommMonObj (Y e)] (P : ∀ e, CP (Y e))
    (h : ∀ e, IsGrpPullback (Y e) B (thick V _ e) (b e)) (w : ∀ e, LBIso (P e).L.L (M.pull (b e))) :
    Triv (Theta B M) :=
  GlobalTheory.AbTriv.triv_of_forall_thick hG V (G3 B)
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB))
    (isProjBy_tensor V _ _ hp (isProjBy_tensor V _ _ hp hp)) _ (DVR.linComb_isLB _ hM _ _)
    fun e => triv_theta hM (P e) (h e) (w e) (thickObj V _ e (G3 B))
      (Over.homMk (pullback.fst (G3 B).hom (thick V _ e)) pullback.condition)

theorem triv_sym_of_levels [∀ e, GrpObj (Y e)] [∀ e, IsCommMonObj (Y e)] (P : ∀ e, CP (Y e))
    (h : ∀ e, IsGrpPullback (Y e) B (thick V _ e) (b e)) (w : ∀ e, LBIso (P e).L.L (M.pull (b e))) :
    Triv (LB.LinComb M (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]) :=
  GlobalTheory.AbTriv.triv_of_forall_thick hG V B hB hp _ (DVR.linComb_isLB _ hM _ _)
    fun e => triv_sym hM (P e) (h e) (w e) (thickObj V _ e B)
      (Over.homMk (pullback.fst B.hom (thick V _ e)) pullback.condition)

omit [IsCommMonObj B] in

theorem lbIso_of_levels {H : LB B.left} (hH : H.IsLB) (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (thick V _ e))
    (w : ∀ e, LBIso (M.pull (b e)) (H.pull (b e))) : LBIso M H :=
  GlobalTheory.AbTriv.triv_of_forall_thick hG V B hB hp (LB.div H M) (LB.isLB_div hH hM) fun e =>
    triv_chart (chartPullDiv H M _) (lbIso_factor (w e)
      ((hb e).lift (pullback.fst B.hom (thick V _ e)) (pullback.snd B.hom (thick V _ e)) pullback.condition) _
      ((hb e).lift_fst _ _ _).symm)

end Complete

theorem relAmple_of_lbIso {V : Type} [CommRing V] {B : Over (Spec (CommRingCat.of V))} {M H : LB B.left}
    (hM : M.IsLB) (hH : H.IsLB) {n d : ℕ} (hd : 1 ≤ d) {σ : Fin (n + 1) → LB.Sec H} (hva : VeryAmpleBy B.hom H σ)
    (h : LBIso (AbLaw.pw M d) H) : RelAmple B M := by
  have hP := isLB_pw hM d
  obtain ⟨w, hw⟩ : LBIso (AbLaw.pw M d) (H.pull (𝟙 _)) :=
    h.chartPull (chartPullId _) (Geo.Tor.chartPullPull H _ _ rfl)
  choose σ' hσ' using fun j => (GlobalTheory.SecPullIso.section_pull _ _ (𝟙 _) H _ w hH hP hw (σ j)).1.exists
  have hc : 𝟙 B.left ≫ B.hom = B.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id V)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]
  have hci : IsClosedImmersion (pullback.lift (𝟙 B.left) B.hom hc) := by
    have : IsIso (Spec.map (CommRingCat.ofHom (RingHom.id V))) := by
      rw [CommRingCat.ofHom_id, Spec.map_id]; infer_instance
    have : IsIso (pullback.lift (𝟙 B.left) B.hom hc ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; infer_instance
    have : IsIso (pullback.lift (𝟙 B.left) B.hom hc) := IsIso.of_isIso_comp_right _ (pullback.fst _ _)
    infer_instance
  exact (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V B M hM).2
    ⟨d, hd, n, σ', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull V _ B.hom H n σ hH hva V (RingHom.id V) _ B.hom (𝟙 _)
      hc hci _ w σ' hP hw hσ'⟩

theorem isPullback_of_grp {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B'] {f : S' ⟶ S}
    {b : B'.left ⟶ B.left} (h : IsGrpPullback B' B f b) : IsPullback b B'.hom B.hom f := h.1

theorem exists_rig {V : Type} [CommRing V] [IsLocalRing V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B]
    {M : LB B.left} (hM : M.IsLB) : ∃ L : RigLB B, L.L = M := by
  obtain ⟨r, hr⟩ := DVR.exists_gen_of_local (V := V) M hM (K := PUnit) (fun _ => eSec B) (fun _ => 1)
  exact ⟨⟨M, r, hM, hr⟩, rfl⟩

theorem lbIso_pw_pull {X Y : Scheme.{0}} {M H : LB X} {N : LB Y} (hM : M.IsLB) (hH : H.IsLB) (hN : N.IsLB)
    {b : Y ⟶ X} {d : ℤ} (h₁ : LBIso N (M.pull b)) (h₂ : LBIso (AbLaw.pw N d) (H.pull b)) :
    LBIso ((AbLaw.pw M d).pull b) (H.pull b) := by
  refine LBIso.trans (pull_isLB (isLB_pw hM d) _) (isLB_pw hN d) (pull_isLB hH _) ?_ h₂
  rw [GlobalTheory.Algebraise.pw_pull]
  exact (GlobalTheory.Algebraise.lbIso_pw h₁ d).symm

theorem exists_cp (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {M : LB B.left} (hM : M.IsLB)
    {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))}
    {b : ∀ e, (Y e).left ⟶ B.left} [∀ e, GrpObj (Y e)] [∀ e, IsCommMonObj (Y e)] (hY : ∀ e, IsAbelianScheme (Y e))
    (P : ∀ e, CP (Y e)) (h : ∀ e, IsGrpPullback (Y e) B (thick V _ e) (b e))
    (w : ∀ e, LBIso (P e).L.L (M.pull (b e))) :
    ∃ Q : CP B, Q.L.L = M ∧ ∀ e, IsCPPullback (P e) Q (thick V _ e) (b e) := by
  obtain ⟨L, rfl⟩ := exists_rig hM
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps hG _ B hB
  obtain ⟨Q, rfl⟩ := h₁ L (triv_theta_of_levels hG hB hp hM P h w) (triv_sym_of_levels hG hB hp hM P h w)
  exact ⟨Q, rfl, fun e => h₂ _ _ _ (hY e) Q (P e) _ (h e) ⟨(P e).L.rig, (P e).L.rigGen⟩ (w e)⟩

theorem exists_alg (hG : GlobalFnsSt) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
    [∀ e, GrpObj (Y e)] [hc : ∀ e, IsCommMonObj (Y e)] (hY : ∀ e, IsAbelianScheme (Y e)) (P : ∀ e, CP (Y e))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsCPPullback (P e) (P (e + 1)) (thickTrans V _ e) (β e)) (h₀ : RelAmple (Y 0) (P 0).L.L) :
    ∃ (B : Over (Spec (CommRingCat.of V))) (_ : GrpObj B) (_ : IsCommMonObj B) (M : CP B)
      (b : ∀ e, (Y e).left ⟶ B.left), IsAbelianScheme B ∧ RelAmple B M.L.L ∧
      (∀ e, IsCPPullback (P e) M (thick V _ e) (b e)) ∧ ∀ e, β e ≫ b (e + 1) = b e := by
  have hg : ∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans V _ e) (β e) := fun e => by
    obtain ⟨h, -⟩ := hβ e
    exact h
  have hv : ∀ e, ∃ v : LB.Iso (P e).L.L ((P (e + 1)).L.L.pull (β e)), v.IsGen := fun e => by
    obtain ⟨_, v, h⟩ := hβ e
    exact ⟨v, h.gen⟩
  choose v hv using hv
  have hf : ∀ e, Flat (Y e).hom := fun e => by
    have := (hY e).smooth
    infer_instance
  obtain ⟨B, M, H, b, n, d, σ, hM, hH, -, hva, hd, hb, hbβ, hiso⟩ :=
    GlobalTheory.Algebraise.algebraisation V Y β (fun e => isPullback_of_grp (hg e)) hf (fun e => (P e).L.L) v
      (fun e => ⟨(P e).L.isLB, hv e⟩) h₀
  have hp : IsProjBy B.hom := ⟨H, hH, n, σ, hva⟩
  obtain ⟨grp, comm, hB, hgb⟩ := GlobalTheory.T.isAbelianScheme_of_compatible_thickenings V Y β hg B b hY hc hp hb hbβ
  have hamp : RelAmple B M := relAmple_of_lbIso hM hH hd hva (lbIso_of_levels hG hB hp (isLB_pw hM d) hH hb
    fun e => lbIso_pw_pull hM hH (P e).L.isLB (hiso e).1 (hiso e).2)
  obtain ⟨Q, rfl, hQ⟩ := exists_cp hG hB hp hM hY P hgb fun e => (hiso e).1
  exact ⟨B, grp, comm, Q, b, hB, hamp, hQ, hbβ⟩

theorem nonempty_alg : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun s => ∀ t : Tower s, Nonempty t.Alg := by
  intro hcard hL V _ _ _ A G _ _ s t
  haveI : IsDiscreteValuationRing V := s.cdvr.1
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal V) V := s.cdvr.2.1
  obtain ⟨B, _, _, M, b, hB, ha, hb, hbβ⟩ := exists_alg hL.globalFns V (fun e => (t.l e).Q.B)
    (fun e => (t.l e).Q.isAb) (fun e => (t.l e).D.M) t.β t.β_pb (GlobalTheory.T.descended_bundle_ample_special_fibre hcard hL V A G s t)
  exact ⟨{ B := B, isAb := hB, M := M, ample := ha, b := b, b_pb := hb, b_β := hbβ }⟩

end GlobalTheory.AlgTower
