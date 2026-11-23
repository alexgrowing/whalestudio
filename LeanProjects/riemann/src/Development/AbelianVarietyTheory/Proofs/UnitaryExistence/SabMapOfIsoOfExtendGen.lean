import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

noncomputable section

namespace GlobalTheory.Exist.CubicalExtension

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Units

variable {X X' X'' A : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem unit_ext_of_injective (d : A ⟶ X) {V : X.Opens} (hd : Function.Injective (d.app V)) {a b : Γ(X, V)ˣ}
    (h : ∀ z : A, d z ∈ V → gm d z V a = gm d z V b) : a = b := by
  have e : pullU d V a = pullU d V b := unit_ext fun z hz =>
    (gm_pull (𝟙 A) d z V hz a).trans (((congrArg (fun q => gm q z V a) (Category.id_comp d)).trans ((h z hz).trans
      (congrArg (fun q => gm q z V b) (Category.id_comp d)).symm)).trans (gm_pull (𝟙 A) d z V hz b).symm)
  exact Units.ext (hd (congrArg Units.val e))

abbrev qchart (L : LB X) (L' : LB X') (F : X' ⟶ X) (j : A ⟶ X') (a : L.ι) (i : L'.ι) : A.Opens :=
  LB.wchart (LB.div (L.pull F) L') (fun _ : PUnit => j) (fun _ => (fun _ => a, i))

theorem mem_qchart {j : A ⟶ X'} {a : L.ι} {i : L'.ι} {y : A} :
    y ∈ qchart L L' F j a i ↔ F (j y) ∈ L.U a ∧ j y ∈ L'.U i :=
  ⟨fun h => ⟨mem_pull.1 (Set.mem_iInter.1 h PUnit.unit).1, (Set.mem_iInter.1 h PUnit.unit).2⟩,
    fun h => Set.mem_iInter.2 fun _ => ⟨mem_pull.2 h.1, h.2⟩⟩

theorem isGen_quot {j : A ⟶ X'} (s : ∀ a i, Γ(A, qchart L L' F j a i)ˣ)
    (h : ∀ (y : A) a a' i i', F (j y) ∈ L.U a → F (j y) ∈ L.U a' → j y ∈ L'.U i → j y ∈ L'.U i' →
      gm (𝟙 A) y _ (s a i) = gm (j ≫ F) y _ (L.g a a') * (gm j y _ (L'.g i i'))⁻¹ * gm (𝟙 A) y _ (s a' i')) :
    LB.Gen.IsGen (L := (LB.div (L.pull F) L').pull j) ⟨fun J => s ((J PUnit.unit).1 PUnit.unit) (J PUnit.unit).2⟩ := by
  refine isGen_of_gm _ fun y J J' hJ hJ' => ?_
  have h₁ := (mem_qchart (a := (J PUnit.unit).1 PUnit.unit) (i := (J PUnit.unit).2)).1 hJ
  have h₂ := (mem_qchart (a := (J' PUnit.unit).1 PUnit.unit) (i := (J' PUnit.unit).2)).1 hJ'
  refine (h y _ _ _ _ h₁.1 h₂.1 h₁.2 h₂.2).trans (congrArg₂ (· * ·) ?_ rfl)
  rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp]
  exact (gm_div_g j y _ _ _ _ h₁.1 h₂.1 h₁.2 h₂.2).symm

theorem exists_quot_of_isos (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (w' : LB.Iso L'' (L'.pull F'))
    (w'' : LB.Iso L'' (L.pull (F' ≫ F))) (hw' : PGen w') (hw'' : PGen w'') (κ : A ⟶ X'') (j : A ⟶ X')
    (hj : κ ≫ F' = j) :
    ∃ r : LB.Gen ((LB.div (L.pull F) L').pull j), r.IsGen ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ A) (y : Y) a i k, F (j (f y)) ∈ L.U a → j (f y) ∈ L'.U i → κ (f y) ∈ L''.U k →
        gm f y (qchart L L' F j a i) (r.s (fun _ => (fun _ => a, i))) =
          gw w'' (f ≫ κ) y a k * (gw w' (f ≫ κ) y i k)⁻¹ := by
  subst hj
  have glue : ∀ a i, ∃ s : Γ(A, qchart L L' F (κ ≫ F') a i)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ A) (y : Y) k,
      F (F' (κ (f y))) ∈ L.U a → F' (κ (f y)) ∈ L'.U i → κ (f y) ∈ L''.U k →
        gm f y _ s = gw w'' (f ≫ κ) y a k * (gw w' (f ≫ κ) y i k)⁻¹ := by
    intro a i
    obtain ⟨W, hW⟩ : ∃ W : L''.ι → A.Opens, ∀ k x, x ∈ W k ↔
        F (F' (κ x)) ∈ L.U a ∧ F' (κ x) ∈ L'.U i ∧ κ x ∈ L''.U k :=
      ⟨fun k => κ ⁻¹ᵁ (F' ⁻¹ᵁ (F ⁻¹ᵁ L.U a) ⊓ (F' ⁻¹ᵁ L'.U i ⊓ L''.U k)), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ k, W k ≤ qchart L L' F (κ ≫ F') a i := fun k x hx =>
      mem_qchart.2 ⟨((hW k x).1 hx).1, ((hW k x).1 hx).2.1⟩
    have l₁ : ∀ k, W k ≤ κ ⁻¹ᵁ ((L.pull (F' ≫ F)).U (fun _ => a) ⊓ L''.U k) := fun k x hx =>
      ⟨mem_pull₂.2 ((hW k x).1 hx).1, ((hW k x).1 hx).2.2⟩
    have l₂ : ∀ k, W k ≤ κ ⁻¹ᵁ ((L'.pull F').U (fun _ => i) ⊓ L''.U k) := fun k x hx =>
      ⟨mem_pull.2 ((hW k x).1 hx).2.1, ((hW k x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(A, W k)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ A) (y : Y) k, f y ∈ W k →
        gm f y (W k) (u k) = gw w'' (f ≫ κ) y a k * (gw w' (f ≫ κ) y i k)⁻¹ :=
      ⟨fun k => res (l₁ k) (pullU κ _ (w''.s (fun _ => a, k))) * (res (l₂ k) (pullU κ _ (w'.s (fun _ => i, k))))⁻¹,
        fun Y f y k hy => (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f y (l₁ k) hy _).trans (gm_pull f κ y _ (l₁ k hy) _))
          ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f y (l₂ k) hy _).trans (gm_pull f κ y _ (l₂ k hy) _)))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨k, hk⟩ := exists_chart hL'' (κ x)
        exact Opens.mem_iSup.2 ⟨k, (hW k x).2 ⟨(mem_qchart.1 hx).1, (mem_qchart.1 hx).2, hk⟩⟩) u (fun k k' x hx => by
        have h₁ := (hW k x).1 hx.1
        have h₂ := (hW k' x).1 hx.2
        have e₁ := hw'' _ (𝟙 A ≫ κ) x a a k k' h₁.1 h₁.1 h₁.2.2 h₂.2.2
        have e₂ := hw' _ (𝟙 A ≫ κ) x i i k k' h₁.2.1 h₁.2.1 h₁.2.2 h₂.2.2
        rw [gm_self hL _ x h₁.1] at e₁
        rw [gm_self hL' _ x h₁.2.1] at e₂
        rw [hu _ (𝟙 A) x k hx.1, hu _ (𝟙 A) x k' hx.2, e₁, e₂]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Y f y k h₁ h₂ h₃ => ?_⟩
    have hy := (hW k (f y)).2 ⟨h₁, h₂, h₃⟩
    exact (gm_res f y (l₀ k) hy s).symm.trans ((congrArg (gm f y (W k)) (hs k)).trans (hu Y f y k hy))
  choose s hs using glue
  refine ⟨_, isGen_quot s fun y a a' i i' ha ha' hi hi' => ?_, fun Y f y a i k => hs a i Y f y k⟩
  obtain ⟨k, hk⟩ := exists_chart hL'' (κ y)
  have e₁ := hw'' _ (𝟙 A ≫ κ) y a a' k k ha ha' hk hk
  have e₂ := hw' _ (𝟙 A ≫ κ) y i i' k k hi hi' hk hk
  rw [hs a i _ (𝟙 A) y k ha hi hk, hs a' i' _ (𝟙 A) y k ha' hi' hk, e₁, e₂, Category.id_comp, Category.assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_quot_of_gens {Y Y' : Scheme.{0}} {e : Y ⟶ X} {e' : Y' ⟶ X'} {h : Y' ⟶ Y} (he : e' ≫ F = h ≫ e)
    (t : LB.Gen (L.pull e)) (t' : LB.Gen (L'.pull e')) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ ρ : LB.Gen ((LB.div (L.pull F) L').pull e'), ρ.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y') (y : Z) a i, F (e' (f y)) ∈ L.U a → e' (f y) ∈ L'.U i →
        gm f y (qchart L L' F e' a i) (ρ.s (fun _ => (fun _ => a, i))) =
          gm (f ≫ h) y (LB.wchart L (fun _ : PUnit => e) (fun _ => a)) (t.s (fun _ => a)) *
            (gm f y (LB.wchart L' (fun _ : PUnit => e') (fun _ => i)) (t'.s (fun _ => i)))⁻¹ := by
  have pe : ∀ y, e (h y) = F (e' y) := fun y => congrArg (fun g => g y) he.symm
  have l₁ : ∀ a i, qchart L L' F e' a i ≤ h ⁻¹ᵁ LB.wchart L (fun _ : PUnit => e) (fun _ => a) := fun a i x hx =>
    mem_pull.2 (by rw [pe]; exact (mem_qchart.1 hx).1)
  have l₂ : ∀ a i, qchart L L' F e' a i ≤ LB.wchart L' (fun _ : PUnit => e') (fun _ => i) := fun a i x hx =>
    mem_pull.2 (mem_qchart.1 hx).2
  obtain ⟨s, hs⟩ : ∃ s : ∀ a i, Γ(Y', qchart L L' F e' a i)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ Y') (y : Z) a i,
      F (e' (f y)) ∈ L.U a → e' (f y) ∈ L'.U i → gm f y (qchart L L' F e' a i) (s a i) =
          gm (f ≫ h) y (LB.wchart L (fun _ : PUnit => e) (fun _ => a)) (t.s (fun _ => a)) *
            (gm f y (LB.wchart L' (fun _ : PUnit => e') (fun _ => i)) (t'.s (fun _ => i)))⁻¹ :=
    ⟨fun a i => res (l₁ a i) (pullU h _ (t.s (fun _ => a))) * (res (l₂ a i) (t'.s (fun _ => i)))⁻¹,
      fun Z f y a i ha hi =>
        have hy : f y ∈ qchart L L' F e' a i := mem_qchart.2 ⟨ha, hi⟩
        (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res f y (l₁ a i) hy _).trans (gm_pull f h y _ (l₁ a i hy) _))
          ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res f y (l₂ a i) hy _))))⟩
  refine ⟨_, isGen_quot s fun y a a' i i' ha ha' hi hi' => ?_, hs⟩
  have e₁ := gen_trans ht (𝟙 Y' ≫ h) y (j := fun _ => a) (j' := fun _ => a') (l₁ a i (mem_qchart.2 ⟨ha, hi⟩))
    (l₁ a' i (mem_qchart.2 ⟨ha', hi⟩))
  have e₂ := gen_trans ht' (𝟙 Y') y (j := fun _ => i) (j' := fun _ => i') (mem_pull.2 hi) (mem_pull.2 hi')
  rw [trF, Fintype.prod_unique, zpow_one] at e₁ e₂
  rw [hs _ (𝟙 _) y a i ha hi, hs _ (𝟙 _) y a' i' ha' hi', e₁, e₂, Category.id_comp, Category.id_comp, he]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem pmaps_of_tri {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}
    {K : Type} [Fintype K] {Y Y' Y'' : Scheme.{0}} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {φ'' : K → (Y'' ⟶ X'')}
    {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L' φ' ε)}
    {t'' : LB.Gen (LB.LinComb L'' φ'' ε)} {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'} (T : Tri w w' w'') (hL'' : L''.IsLB)
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (hc' : ∀ k, φ'' k ≫ F' = h' ≫ φ' k) (H' : PMaps w' φ'' φ' ε t'' t' h')
    (H'' : PMaps w'' φ'' φ ε t'' t (h' ≫ h)) (l : A ⟶ Y'') (hl : ∀ V, Function.Injective ((l ≫ h').app V)) :
    PMaps w φ' φ ε t' t h := by
  intro Z r z p q hp hq
  obtain ⟨u, hu⟩ := exists_pw w φ' ε p q
  have le : LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤ h ⁻¹ᵁ LB.wchart L φ p := fun y hy =>
    Set.mem_iInter.2 fun k => by
      show φ k (h y) ∈ L.U (p k)
      rw [pt_eq hc]; exact Set.mem_iInter.1 hy.1 k
  have v₁ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
      gm r z _ (res le (pullU h _ (t.s p))) = gm (r ≫ h) z (LB.wchart L φ p) (t.s p) := fun Z r z hz =>
    (gm_res r z le hz _).trans (gm_pull r h z _ (le hz) _)
  have v₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
      gm r z _ (u * res inf_le_right (t'.s q)) = pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (t'.s q) :=
    fun Z r z hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (hu Z r z hz) (gm_res r z _ hz _))
  have e : res le (pullU h _ (t.s p)) = u * res inf_le_right (t'.s q) :=
    unit_ext_of_injective (l ≫ h') (hl _) fun y hy => by
      choose k hk using fun k => exists_chart hL'' (φ'' k (l y))
      have a₁ : ∀ k, F (F' (φ'' k (l y))) ∈ L.U (p k) := fun k => by
        rw [← pt_eq hc']; exact Set.mem_iInter.1 hy.1 k
      have a₂ : ∀ k, F' (φ'' k (l y)) ∈ L'.U (q k) := fun k => by
        rw [← pt_eq hc']; exact Set.mem_iInter.1 hy.2 k
      rw [v₁ _ _ _ hy, v₂ _ _ _ hy, Category.assoc, H'' _ l y p k a₁ hk, H' _ l y q k a₂ hk,
        T.prod hc' _ l y p q k a₁ a₂ hk, _root_.mul_assoc]
      rfl
  have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q :=
    ⟨Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩
  exact (v₁ Z r z hz).symm.trans ((congrArg (gm r z _) e).trans (v₂ Z r z hz))

end Units

section Group

variable {T K : Type} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
  [IsFractionRing T K]

omit [IsDiscreteValuationRing T] in

theorem app_injective_generic {X P : Scheme.{0}} {p : X ⟶ Sp T} [Flat p] {d : P ⟶ X} {q : P ⟶ Sp K}
    (h : IsPullback d q p (spMap (algebraMap T K))) (V : X.Opens) : Function.Injective (d.app V) := by
  have : IsDominant (spMap (algebraMap T K)) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective T K)).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  have : IsSchemeTheoreticallyDominant d := IsSchemeTheoreticallyDominant.of_isPullback h.flip
  have : QuasiCompact d := MorphismProperty.of_isPullback (P := @QuasiCompact) h.flip inferInstance
  exact d.app_injective V

theorem isPullCubical_of_generic (hE : extendGenSt.{0}) {S : Scheme.{0}} {G₀ : Over S} {G : Over (Sp T)}
    {GK : Over (Sp K)} [GrpObj G₀] [IsCommMonObj G₀] [GrpObj G] [IsCommMonObj G] [GrpObj GK] [IsCommMonObj GK]
    (hG : IsSemiAbelian G) {L₀ : RigLB G₀} {L : RigLB G} {LK : RigLB GK} (c₀ : CubicalStr G₀ L₀)
    (c : CubicalStr G L) (cK : CubicalStr GK LK) (n : CubeMap G G₀) (m : CubeMap GK G) (m' : CubeMap GK G₀)
    (hp : IsPullback m.F GK.hom G.hom (spMap (algebraMap T K))) (he : m.e = spMap (algebraMap T K))
    (h₁ : m'.F = m.F ≫ n.F) (h₂ : m'.F3 = m.F3 ≫ n.F3) (h₃ : m'.e = m.e ≫ n.e)
    (H' : m.IsPullCubical cK c) (H'' : m'.IsPullCubical cK c₀) : n.IsPullCubical c c₀ := by
  obtain ⟨F, F3, e, he', hp'⟩ := m'
  dsimp only at h₁ h₂ h₃
  subst h₁ h₂ h₃
  rw [isPullCubical_iff] at H' H'' ⊢
  obtain ⟨w', g', r', q'⟩ := H'
  obtain ⟨w'', g'', r'', q''⟩ := H''
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have a₁ : eSec G ≫ G.hom = 𝟙 _ := Over.w η[G]
  have a₂ : eSec GK ≫ GK.hom = 𝟙 _ := Over.w η[GK]
  obtain ⟨κ, κ', hκ, hκ'⟩ : ∃ (κ : genA T K G ⟶ GK.left) (κ' : GK.left ⟶ genA T K G),
      κ ≫ m.F = jA T K G ∧ κ' ≫ κ = 𝟙 _ :=
    ⟨hp.isoPullback.inv, hp.isoPullback.hom, hp.isoPullback_inv_fst, hp.isoPullback.hom_inv_id⟩
  have hj : κ' ≫ jA T K G = m.F := by rw [← hκ, ← Category.assoc, hκ', Category.id_comp]
  obtain ⟨r, hr, vr⟩ := exists_quot_of_isos L₀.isLB L.isLB LK.isLB w' w'' g' g'' κ (jA T K G) hκ
  obtain ⟨ρ, hρ, vρ⟩ := exists_quot_of_gens n.e_comm L₀.rig L.rig L₀.rigGen L.rigGen
  have heA : (eSec GK ≫ κ') ≫ jA T K G = eK T K G := by
    rw [Category.assoc, hj, m.e_comm, he]; rfl
  have heA' : (eSec GK ≫ κ') ≫ jA T K G = m.e ≫ eSec G := by
    rw [Category.assoc, hj, m.e_comm]
  have heκ : (eSec GK ≫ κ') ≫ κ = eSec GK := by rw [Category.assoc, hκ', Category.comp_id]
  obtain ⟨w, ⟨hw, hwr⟩, -⟩ := hE T K G (eSec GK ≫ κ') heA
    ⟨LB.div (L₀.L.pull n.F) L.L, ρ, LB.isLB_div (pull_isLB L₀.isLB _) L.isLB, hρ⟩ r hr (by
      intro J J' _ _ hJ
      obtain rfl : J = J' := funext fun _ => hJ PUnit.unit PUnit.unit heA
      refine unit_ext fun y hy => ?_
      refine (gm_res _ y _ hy _).trans (Eq.trans ?_ (gm_res _ y _ hy _).symm)
      refine (gm_pullGen _ _ _ r _ (𝟙 _) y J hy.1).trans (Eq.trans ?_ (gm_pullGen _ _ _ ρ _ (𝟙 _) y J hy.2).symm)
      obtain ⟨k, hk⟩ := exists_chart LK.isLB (eSec GK y)
      have hm := (mem_qchart (j := (eSec GK ≫ κ') ≫ jA T K G) (a := (J PUnit.unit).1 PUnit.unit)
        (i := (J PUnit.unit).2)).1 hy.1
      have hm' := hm
      have hm'' := hm
      rw [heA'] at hm'
      rw [Category.assoc, hj] at hm''
      have e₁ := vr _ (eSec GK ≫ κ') y _ _ k hm.1 hm.2 (by
        show ((eSec GK ≫ κ') ≫ κ) y ∈ _
        rw [heκ]; exact hk)
      have e₂ := vρ _ m.e y _ _ hm'.1 hm'.2
      have e₃ := r'' _ (𝟙 _) y (fun _ => (J PUnit.unit).1 PUnit.unit) (fun _ => k) (fun _ => hm''.1) (fun _ => hk)
      have e₄ := r' _ (𝟙 _) y (fun _ => (J PUnit.unit).2) (fun _ => k) (fun _ => hm''.2) (fun _ => hk)
      rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at e₃ e₄
      rw [heκ] at e₁
      rw [e₃, e₄, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.mul_one] at e₂
      rw [Category.id_comp, Category.id_comp]
      refine e₁.trans (e₂.symm.trans ?_)
      rw [he]
      rfl)
  have tri : Tri (L := L₀.L) (L' := L.L) (F := n.F) w w' w'' := by
    intro Y f y a i k ha hi hk
    have p₁ : jA T K G (κ' (f y)) = m.F (f y) := congrArg (fun g => g (f y)) hj
    have p₂ : κ (κ' (f y)) = f y := congrArg (fun g => g (f y)) hκ'
    have ha' : n.F (jA T K G (κ' (f y))) ∈ L₀.L.U a := by rw [p₁]; exact ha
    have hi' : jA T K G (κ' (f y)) ∈ L.L.U i := by rw [p₁]; exact hi
    have e₁ := vr _ (f ≫ κ') y a i k ha' hi' (by
      show κ (κ' (f y)) ∈ _
      rw [p₂]; exact hk)
    have hy : (f ≫ κ') y ∈ qchart L₀.L L.L n.F (jA T K G) a i := mem_qchart.2 ⟨ha', hi'⟩
    have e₂ : gm (f ≫ κ') y (qchart L₀.L L.L n.F (jA T K G) a i) (r.s (fun _ => (fun _ => a, i))) =
        gw (L := L₀.L) (L' := L.L) (F := n.F) w ((f ≫ κ') ≫ jA T K G) y a i := by
      rw [← hwr]
      exact (gm_res _ y _ hy _).trans (gm_pull (f ≫ κ') (jA T K G) y
        ((L₀.L.pull n.F).U (fun _ => a) ⊓ L.L.U i) ⟨mem_pull.2 ha', hi'⟩ _)
    rw [e₂, Category.assoc, Category.assoc, hj, hκ', Category.comp_id] at e₁
    rw [e₁, inv_mul_cancel_right]
  refine ⟨w, (isGen_iff _).1 hw, ?_, ?_⟩
  · refine pmaps_of_tri tri LK.isLB (fun _ => n.e_comm) (fun _ => m.e_comm) r' r'' (𝟙 _) ?_
    rw [Category.id_comp, he]
    exact app_injective_generic (p := 𝟙 _) (q := 𝟙 _) (IsPullback.of_vert_isIso ⟨by simp⟩)
  · have : Flat (G3 G).hom := by
      show Flat (pullback.fst G.hom (pullback.fst G.hom G.hom ≫ G.hom) ≫ G.hom)
      infer_instance
    let P : Over (Sp K) := Over.mk (pullback.snd (G3 G).hom (spMap (algebraMap T K)))
    let x : Fin 3 → (P ⟶ GK) := fun i => Over.homMk
      (hp.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
        rw [Category.assoc, Over.w]; exact pullback.condition)) (hp.lift_snd _ _ _)
    have hx : ∀ i, (x i).left ≫ m.F = pullback.fst _ _ ≫ (x3 G i).left := fun i => hp.lift_fst _ _ _
    let l : P ⟶ G3 GK := lift (x 0) (lift (x 1) (x 2))
    have hl : l.left ≫ m.F3 = pullback.fst (G3 G).hom (spMap (algebraMap T K)) := hom_ext_triple _ fun i => by
      have : l ≫ x3 GK i = x i := by fin_cases i <;> simp [l, x3]
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, this, hx]
    refine pmaps_of_tri tri LK.isLB (fun I => n.psum_comm I.down) (fun I => m.psum_comm I.down) q' q'' l.left ?_
    rw [hl]
    exact app_injective_generic (IsPullback.of_hasPullback _ _)

end Group

theorem sabMap_of_iso_of_extendGen : extendGenSt.{0} → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (t t' : SAB H (Sp T)) (tK : SAB H (Sp K)) (m : SABMap tK t (spMap (algebraMap T K))) (m' : SABMap tK t' (spMap (algebraMap T K))) (ψ : t.G ≅ t'.G), IsMonHom ψ.hom → m.φ ≫ ψ.hom.left = m'.φ → (∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a) → ∃ n : SABMap t t' (𝟙 _), n.φ = ψ.hom.left := by
  intro hE E _ _ _ H T K _ _ _ _ _ _ t t' tK m m' ψ hψ hφ hact
  have hφ' : m.cm.F ≫ ψ.hom.left = m'.cm.F := hφ
  have h3 : m'.cm.F3 = m.cm.F3 ≫ (CubeMap.ofHom ψ.hom).F3 := hom_ext_triple _ fun i => by
    rw [cubeMap_comp_proj_three, Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, cubeMap_comp_proj_three, Category.assoc, ← hφ']
    rfl
  refine ⟨⟨CubeMap.ofHom ψ.hom, isGrpPullback_of_iso ψ, rfl, fun a => congrArg (fun z => z.left) (hact a),
    isPullCubical_of_generic hE t.semi t'.cub t.cub tK.cub _ m.cm m'.cm m.cart.1 m.base hφ'.symm h3 ?_ m.lin m'.lin⟩,
    rfl⟩
  show m'.cm.e = m.cm.e ≫ 𝟙 _
  rw [Category.comp_id, m.base, m'.base]

end GlobalTheory.Exist.CubicalExtension
