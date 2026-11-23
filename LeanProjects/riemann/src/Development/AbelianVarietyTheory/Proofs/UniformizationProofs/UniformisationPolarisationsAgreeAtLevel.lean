import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourthSide
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariantStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelComparison

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Compare

variable {B B' G E : Scheme.{0}} {M : LB B} {M' : LB B'} {L L' : LB G} {p : E ⟶ B} {p' : E ⟶ B'} {f : E ⟶ G}

def germ (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f) (M'.pull p')) (wL : LB.Iso L' (L.pull (𝟙 G)))
    {Z : Scheme.{0}} (r : Z ⟶ E) (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gw w r z jM (fun _ => jL) * gw wL (r ≫ f) z jL jL' * (gw w' r z jM' (fun _ => jL'))⁻¹

theorem germ_change {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f) (M'.pull p')}
    {wL : LB.Iso L' (L.pull (𝟙 G))} (hw : PGen w) (hw' : PGen w') (hwL : PGen wL)
    {Z : Scheme.{0}} (r : Z ⟶ E) (z : Z) (jM kM : M.ι) (jM' kM' : M'.ι) (jL kL : L.ι) (jL' kL' : L'.ι)
    (a₁ : p (r z) ∈ M.U jM) (a₂ : p' (r z) ∈ M'.U jM') (a₃ : f (r z) ∈ L.U jL)
    (a₄ : f (r z) ∈ L'.U jL') (b₁ : p (r z) ∈ M.U kM) (b₂ : p' (r z) ∈ M'.U kM')
    (b₃ : f (r z) ∈ L.U kL) (b₄ : f (r z) ∈ L'.U kL') :
    germ w w' wL r z jM jM' jL jL' =
      gm (r ≫ p) z _ (M.g jM kM) * (gm (r ≫ p') z _ (M'.g jM' kM'))⁻¹ * germ w w' wL r z kM kM' kL kL' := by
  have a := hw Z r z jM kM (fun _ => jL) (fun _ => kL) a₁ b₁ (mem_pull.2 a₃) (mem_pull.2 b₃)
  have b := hwL Z (r ≫ f) z jL kL jL' kL' a₃ b₃ a₄ b₄
  have c := hw' Z r z jM' kM' (fun _ => jL') (fun _ => kL') a₂ b₂ (mem_pull.2 a₄) (mem_pull.2 b₄)
  rw [FourthSide.gm_pull_g L f r z jL kL a₃ b₃] at a
  rw [FourthSide.gm_pull_g L' f r z jL' kL' a₄ b₄] at c
  rw [Category.comp_id] at b
  unfold germ
  rw [a, b, c]
  generalize gm (r ≫ p) z _ (M.g jM kM) = A
  generalize gm (r ≫ f) z _ (L.g jL kL) = C
  generalize gm (r ≫ p') z _ (M'.g jM' kM') = A'
  generalize gm (r ≫ f) z _ (L'.g jL' kL') = C'
  generalize gw w r z kM (fun _ => kL) = P
  generalize gw wL (r ≫ f) z kL kL' = Q
  generalize gw w' r z kM' (fun _ => kL') = R
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_unit (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f) (M'.pull p')}
    {wL : LB.Iso L' (L.pull (𝟙 G))} (hw : PGen w) (hw' : PGen w') (hwL : PGen wL) (jM : M.ι) (jM' : M'.ι) :
    ∃ s : Γ(E, (M.pull p).U (fun _ => jM) ⊓ (M'.pull p').U (fun _ => jM'))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ E) (z : Z) (jL : L.ι) (jL' : L'.ι), p (r z) ∈ M.U jM →
        p' (r z) ∈ M'.U jM' → f (r z) ∈ L.U jL → f (r z) ∈ L'.U jL' →
        gm r z _ s = germ w w' wL r z jM jM' jL jL' := by
  obtain ⟨W, hW⟩ : ∃ W : L.ι × L'.ι → E.Opens, ∀ i x, x ∈ W i ↔
      p x ∈ M.U jM ∧ p' x ∈ M'.U jM' ∧ f x ∈ L.U i.1 ∧ f x ∈ L'.U i.2 :=
    ⟨fun i => p ⁻¹ᵁ M.U jM ⊓ (p' ⁻¹ᵁ M'.U jM' ⊓ (f ⁻¹ᵁ L.U i.1 ⊓ f ⁻¹ᵁ L'.U i.2)), fun _ _ => Iff.rfl⟩
  have l₀ : ∀ i, W i ≤ (M.pull p).U (fun _ => jM) ⊓ (M'.pull p').U (fun _ => jM') := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).1, mem_pull.2 ((hW i x).1 hx).2.1⟩
  have l₁ : ∀ i, W i ≤ (M.pull p).U (fun _ => jM) ⊓ (L.pull f).U (fun _ => i.1) := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).1, mem_pull.2 ((hW i x).1 hx).2.2.1⟩
  have l₂ : ∀ i, W i ≤ f ⁻¹ᵁ ((L.pull (𝟙 G)).U (fun _ => i.1) ⊓ L'.U i.2) := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).2.2.1, ((hW i x).1 hx).2.2.2⟩
  have l₃ : ∀ i, W i ≤ (M'.pull p').U (fun _ => jM') ⊓ (L'.pull f).U (fun _ => i.2) := fun i x hx =>
    ⟨mem_pull.2 ((hW i x).1 hx).2.1, mem_pull.2 ((hW i x).1 hx).2.2.2⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(E, W i)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ E) (z : Z) (i : L.ι × L'.ι), r z ∈ W i →
      gm r z (W i) (u i) = germ w w' wL r z jM jM' i.1 i.2 :=
    ⟨fun i => res (l₁ i) (w.s (fun _ => jM, fun _ => i.1)) *
        res (l₂ i) (pullU f _ (wL.s (fun _ => i.1, i.2))) * (res (l₃ i) (w'.s (fun _ => jM', fun _ => i.2)))⁻¹,
      fun Z r z i hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        (gm_res r z (l₁ i) hz _) ((gm_res r z (l₂ i) hz _).trans (gm_pull r f z _ (l₂ i hz) _))))
        ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z (l₃ i) hz _))))⟩
  obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hL (f x)
      obtain ⟨j, hj⟩ := exists_chart hL' (f x)
      exact Opens.mem_iSup.2 ⟨(i, j), (hW (i, j) x).2 ⟨mem_pull.1 hx.1, mem_pull.1 hx.2, hi, hj⟩⟩) u
    (fun i i' x hx => by
      have h₁ := (hW i x).1 hx.1
      have h₂ := (hW i' x).1 hx.2
      have k := germ_change hw hw' hwL (𝟙 E) x jM jM jM' jM' i.1 i'.1 i.2 i'.2 h₁.1 h₁.2.1 h₁.2.2.1
        h₁.2.2.2 h₂.1 h₂.2.1 h₂.2.2.1 h₂.2.2.2
      rw [gm_self hM (𝟙 E ≫ p) x h₁.1, gm_self hM' (𝟙 E ≫ p') x h₁.2.1, inv_one, _root_.one_mul,
        _root_.one_mul] at k
      exact (hu _ (𝟙 E) x i hx.1).trans (k.trans (hu _ (𝟙 E) x i' hx.2).symm))
  refine ⟨s, fun Z r z jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  have hz := (hW (jL, jL') (r z)).2 ⟨a₁, a₂, a₃, a₄⟩
  exact (gm_res r z (l₀ (jL, jL')) hz s).symm.trans
    ((congrArg (gm r z (W (jL, jL'))) (hs (jL, jL'))).trans (hu Z r z (jL, jL') hz))

theorem exists_comparison (hM : M.IsLB) (hM' : M'.IsLB) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f) (M'.pull p')}
    {wL : LB.Iso L' (L.pull (𝟙 G))} (hw : w.IsGen) (hw' : w'.IsGen) (hwL : wL.IsGen) :
    ∃ u : LB.Iso (M'.pull p') (M.pull p), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ E) (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
        p (r z) ∈ M.U jM → p' (r z) ∈ M'.U jM' → f (r z) ∈ L.U jL → f (r z) ∈ L'.U jL' →
        gw u r z jM (fun _ => jM') * gw w' r z jM' (fun _ => jL') =
          gw w r z jM (fun _ => jL) * gw wL (r ≫ f) z jL jL' := by
  rw [isGen_iff] at hw hw' hwL
  choose s hs using exists_unit hM hM' hL hL' hw hw' hwL
  refine ⟨⟨fun q => s (q.1 PUnit.unit) (q.2 PUnit.unit)⟩, (isGen_iff _).2 ?_,
    fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  · intro Z r z j j' k k' a₁ b₁ a₂ b₂
    obtain ⟨i, hi⟩ := exists_chart hL (f (r z))
    obtain ⟨l, hl⟩ := exists_chart hL' (f (r z))
    have a₂' := mem_pull.1 a₂
    have b₂' := mem_pull.1 b₂
    have c := germ_change hw hw' hwL r z j j' _ _ i i l l a₁ a₂' hi hl b₁ b₂' hi hl
    rw [← hs j _ Z r z i l a₁ a₂' hi hl, ← hs j' _ Z r z i l b₁ b₂' hi hl,
      ← FourthSide.gm_pull_g M' p' r z _ _ a₂' b₂'] at c
    exact c
  · exact (congrArg (· * gw w' r z jM' (fun _ => jL')) (hs jM jM' Z r z jL jL' a₁ a₂ a₃ a₄)).trans
      (inv_mul_cancel_right _ _)

end Compare

section Descend

variable {X Y : Scheme.{0}} (q : X ⟶ Y) [Flat q] [Surjective q]

theorem unit_ext_of_flat {V : Y.Opens} {a b : Γ(Y, V)ˣ} (h : ∀ x, q x ∈ V → gm q x V a = gm q x V b) : a = b := by
  apply Units.ext
  apply FunDescent.app_injective q V
  have : pullU q V a = pullU q V b := unit_ext fun x hx =>
    (gm_pull (𝟙 X) q x V hx a).trans (Eq.trans (by rw [Category.id_comp]; exact h x hx)
      (gm_pull (𝟙 X) q x V hx b).symm)
  exact congrArg Units.val this

theorem exists_unit_descend [QuasiCompact q] (V : Y.Opens) (W : X.Opens) (hW : q ⁻¹ᵁ V ≤ W) (s : Γ(X, W)ˣ)
    (hs : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (z : Z), g₁ ≫ q = g₂ ≫ q → q (g₂ z) ∈ V →
      gm g₁ z W s = gm g₂ z W s) :
    ∃ t : Γ(Y, V)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), q (r z) ∈ V → gm (r ≫ q) z V t = gm r z W s := by
  obtain ⟨a, ha⟩ := FunDescent.exists_app_eq q V (res hW s).val (fun Z g₁ g₂ h₁ h₂ e => by
    have k : ∀ (g : Z ⟶ X) (h : ⊤ ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V)) (z : Z),
        gm (𝟙 Z) z ⊤ (res h (pullU g _ (res hW s))) = gm g z W s := fun g h z =>
      (gm_res (𝟙 Z) z h trivial _).trans ((gm_pull (𝟙 Z) g z _ (h trivial) _).trans (by
        rw [Category.id_comp]; exact gm_res g z hW (h trivial) s))
    have : res h₁ (pullU g₁ _ (res hW s)) = res h₂ (pullU g₂ _ (res hW s)) := unit_ext fun z _ =>
      (k g₁ h₁ z).trans ((hs Z g₁ g₂ z e (h₂ trivial)).trans (k g₂ h₂ z).symm)
    exact congrArg Units.val this)
  obtain ⟨t, rfl⟩ := FunDescent.isUnit_of_isUnit_app q V a (ha ▸ (res hW s).isUnit)
  refine ⟨t, fun Z r z hz => ?_⟩
  have : pullU q V t = res hW s := Units.ext ha
  rw [← gm_pull r q z V hz, this]
  exact gm_res r z hW hz s

theorem exists_iso_descend [QuasiCompact q] {B B' : Scheme.{0}} {M : LB B} {M' : LB B'} (a : Y ⟶ B') (b : Y ⟶ B)
    {p : X ⟶ B} {p' : X ⟶ B'} (hp : p = q ≫ b) (hp' : p' = q ≫ a) (u : LB.Iso (M'.pull p') (M.pull p))
    (hu : u.IsGen)
    (hinv : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (z : Z) (j : M.ι) (j' : M'.ι), g₁ ≫ q = g₂ ≫ q →
      p (g₂ z) ∈ M.U j → p' (g₂ z) ∈ M'.U j' → gw u g₁ z j (fun _ => j') = gw u g₂ z j (fun _ => j')) :
    ∃ v : LB.Iso (M'.pull a) (M.pull b), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (j : M.ι) (j' : M'.ι), p (r z) ∈ M.U j → p' (r z) ∈ M'.U j' →
        gw v (r ≫ q) z j (fun _ => j') = gw u r z j (fun _ => j') := by
  subst hp hp'
  rw [isGen_iff] at hu
  have key : ∀ (j : M.ι) (j' : M'.ι), ∃ t : Γ(Y, (M.pull b).U (fun _ => j) ⊓ (M'.pull a).U (fun _ => j'))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), q (r z) ∈ (M.pull b).U (fun _ => j) ⊓ (M'.pull a).U (fun _ => j') →
        gm (r ≫ q) z _ t = gw u r z j (fun _ => j') := fun j j' =>
    exists_unit_descend q ((M.pull b).U (fun _ => j) ⊓ (M'.pull a).U (fun _ => j'))
      ((M.pull (q ≫ b)).U (fun _ => j) ⊓ (M'.pull (q ≫ a)).U (fun _ => j'))
      (fun x hx => ⟨mem_pull₂.2 (mem_pull.1 hx.1), mem_pull₂.2 (mem_pull.1 hx.2)⟩)
      (u.s (fun _ => j, fun _ => j'))
      (fun Z g₁ g₂ z e hz => hinv Z g₁ g₂ z j j' e (mem_pull.1 hz.1) (mem_pull.1 hz.2))
  choose t ht using key
  refine ⟨⟨fun k => t (k.1 PUnit.unit) (k.2 PUnit.unit)⟩, ?_,
    fun Z r z j j' h h' => ht j j' Z r z ⟨mem_pull.2 h, mem_pull.2 h'⟩⟩
  rintro ⟨J, K⟩ ⟨J', K'⟩
  apply unit_ext_of_flat q
  intro x hx
  have hj := mem_pull.1 hx.1.1
  have hj' := mem_pull.1 hx.2.1
  have hk := mem_pull.1 hx.1.2
  have hk' := mem_pull.1 hx.2.2
  have c := hu _ (𝟙 X) x (J PUnit.unit) (J' PUnit.unit) (fun _ => K PUnit.unit) (fun _ => K' PUnit.unit) hj hj'
    (mem_pull₂.2 hk) (mem_pull₂.2 hk')
  have t₁ := ht (J PUnit.unit) (K PUnit.unit) X (𝟙 X) x ⟨mem_pull.2 hj, mem_pull.2 hk⟩
  have t₂ := ht (J' PUnit.unit) (K' PUnit.unit) X (𝟙 X) x ⟨mem_pull.2 hj', mem_pull.2 hk'⟩
  have g₁ := FourthSide.gm_pull_g M' (q ≫ a) (𝟙 X) x _ _ hk hk'
  have g₂ := FourthSide.gm_pull_g M' a q x _ _ hk hk'
  have g₃ := gm_div_g (L := M) (L' := M'.pull a) (F := b) q x (J PUnit.unit) (J' PUnit.unit)
    (fun _ => K PUnit.unit) (fun _ => K' PUnit.unit) hj hj' (mem_pull.2 hk) (mem_pull.2 hk')
  rw [Category.id_comp] at t₁ t₂ g₁ c
  rw [← t₁, ← t₂, g₁, ← g₂, ← g₃] at c
  exact (gm_res _ x _ hx _).trans (c.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

end Descend

end GlobalTheory.LevelComparison

namespace GlobalTheory

theorem polarisations_agree_at_level : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom → (U'.gt e).q ≫ β.hom = (U.gt e).q → ∃ v : LB.Iso (D'.toPre.P.L.pull (fstG I e D'.toPre.P.A).left) (D.toPre.P.L.pull (β.hom.left ≫ (fstG I e D.toPre.P.A).left)), v.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw v (r ≫ (U'.gt e).q.left) z jM (fun _ => jM') * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL') := by
  intro hG R _ _ _ I hI D D' A A' G _ _ hS U U' wL he hwL hrig e β hβ hq
  obtain ⟨u, hu, hu'⟩ := LevelComparison.exists_comparison D.toPre.P.isLB D'.toPre.P.isLB U.LG.isLB U'.LG.isLB
    (U.w_gen e) (U'.w_gen e) hwL
  have inv := GlobalTheory.T.genMaps_linCombIso_of_semiAbelian hG R I hI D D' A A' G hS U U' wL he hwL hrig
    (rigidified_iso_respects_cube_and_symmetry hG R I hI D D' A A' G hS U U' wL he hwL hrig) e β hβ hq u hu hu'
  haveI := (U'.gt e).q_flat
  haveI := (U'.gt e).q_surj
  haveI := (U'.gt e).q_affine
  haveI := (U.gt e).q_hom
  have hql : (U'.gt e).q.left ≫ β.hom.left = (U.gt e).q.left := congrArg (·.left) hq
  obtain ⟨v, hv, hv'⟩ := LevelComparison.exists_iso_descend (U'.gt e).q.left (fstG I e D'.toPre.P.A).left
    (β.hom.left ≫ (fstG I e D.toPre.P.A).left) (p := (U.gt e).pG.left) (p' := (U'.gt e).pG.left)
    (by rw [← Category.assoc, hql]; rfl) rfl u hu (fun Z g₁ g₂ z j j' h a b => by
      let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (g₂ ≫ (thickObj R I e G).hom)
      let k₂ : Z' ⟶ thickObj R I e G := Over.homMk g₂ rfl
      let k₁ : Z' ⟶ thickObj R I e G := Over.homMk g₁ (by
        change g₁ ≫ (thickObj R I e G).hom = g₂ ≫ (thickObj R I e G).hom
        rw [← Over.w (U'.gt e).q, reassoc_of% h])
      have e₁ : k₁ ≫ (U'.gt e).q = k₂ ≫ (U'.gt e).q := Over.OverMorphism.ext h
      have e' : k₁ ≫ (U.gt e).q = k₂ ≫ (U.gt e).q := by rw [← hq, reassoc_of% e₁]
      have w : (k₁ * k₂⁻¹) ≫ (U.gt e).q = toUnit Z' ≫ η[thickObj R I e D.toPre.P.A] := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, e', mul_inv_cancel]
        rfl
      have ht : ((U.gt e).isKernel.lift _ _ w ≫ (U.gt e).i) * k₂ = k₁ := by
        rw [(U.gt e).isKernel.lift_fst, inv_mul_cancel_right]
      have := inv Z' ((U.gt e).isKernel.lift _ _ w) k₂ z j j' a b
      rw [ht] at this
      exact this)
  refine ⟨v, hv, fun Z r z jM jM' jL jL' a₁ a₂ a₃ a₄ => ?_⟩
  rw [← hu' Z r z jM jM' jL jL' a₁ a₂ a₃ a₄]
  exact congrArg (· * _) (hv' Z r z jM jM' a₁ a₂)

end GlobalTheory
