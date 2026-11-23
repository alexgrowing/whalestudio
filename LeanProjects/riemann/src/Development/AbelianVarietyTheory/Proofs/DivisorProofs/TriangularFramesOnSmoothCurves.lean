import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriFrames
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnitSubOfIsSplitting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM GlobalTheory.Points GlobalTheory.GradedPieces
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

namespace GlobalTheory.TriFlag

theorem nonempty_iso_toMod {X : Scheme.{0}} {F G : X.Modules} (N : Sub F) {J : Type} {T : J → X.Opens}
    (hT : ⨆ j, T j = ⊤) (g : G ⟶ F) [Mono g]
    (hg : ∀ j (V : X.Opens), V ≤ T j → ∀ x : Γ(F, V), (∃ y, g.app V y = x) ↔ x ∈ N.sec V) :
    Nonempty (G ≅ N.toMod) := by
  have hmem (V : X.Opens) (y : Γ(G, V)) : g.app V y ∈ N.sec V := by
    refine N.mem_of_local fun x hx => ?_
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ x))
    refine ⟨V ⊓ T j, inf_le_left, ⟨hx, hj⟩, ?_⟩
    rw [← app_resM]
    exact (hg j _ inf_le_right _).1 ⟨_, rfl⟩
  let φ : G ⟶ N.toMod := N.lift g hmem
  have hφ (V : X.Opens) (y : Γ(G, V)) : N.incl.app V (φ.app V y) = g.app V y := rfl
  have hiso : IsIso φ := GlobalTheory.Twist.isIso_of_cover φ hT fun j W hW => by
    refine ⟨fun y₁ y₂ e => GlobalTheory.QCoh.injective_app_of_mono g W ?_, fun z => ?_⟩
    · rw [← hφ, ← hφ, e]
    · obtain ⟨y, hy⟩ := (hg j W hW _).2 (N.incl_app_mem z)
      exact ⟨y, N.incl_app_injective W ((hφ W y).trans hy)⟩
  exact ⟨@asIso _ _ _ _ φ hiso⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}

theorem exists_lie_iso {C : Scheme.{0}} {f : C ⟶ X} {t' : SAB H C} [QuasiSeparated t'.G.hom] (m : SABMap t' t f)
    {G : Over C} [GrpObj G] [QuasiSeparated G.hom] {i : OAct (𝓞 E) G} {φ : G.left ⟶ t.G.left}
    (h : IsActPull i t.act f φ) : ∃ e : Lie G ≅ Lie t'.G, IsEquivariant (lieAct i) (lieAct t'.act) e.hom := by
  have := t.semi
  let e : omega t'.G ≅ omega G := (asIso (omegaBase m.cart)).symm ≪≫ asIso (omegaBase h.1)
  have he : IsEquivariant (omegaAct t'.act) (omegaAct i) e.hom := fun a => by
    have h₁ := isEquivariant_omegaBase m.cart m.act a
    have h₂ := isEquivariant_omegaBase h.1 h.2 a
    simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc]
    rw [← h₂, IsIso.eq_inv_comp, ← reassoc_of% h₁, IsIso.hom_inv_id_assoc]
  exact ⟨dualIso e, he.dual⟩

theorem exists_basis {R : Type} [CommRing R] {x : Sp R ⟶ X} {N : ℕ} {u : Fin N → (Sp (DualNumber R) ⟶ t.G.left)}
    (hu : ∀ i, IsTanAtG t x (u i)) (hb : ∀ w, IsTanAtG t x w → ∃! cf : Fin N → R, IsCombAtG t x u cf w) :
    ∃ b : Module.Basis (Fin N) R (TanM x t.G), ∀ i, b i = tanOf (hu i) := by
  have key (w : TanM x t.G) : ∃! cf : Fin N → R, ∑ i, cf i • tanOf (hu i) = w :=
    (existsUnique_congr fun cf => (isComb_iff (fun i => tanOf (hu i)) cf w).trans eq_comm).1 (hb _ (isTan_tv w))
  exact ⟨.mk (v := fun i => tanOf (hu i)) (Fintype.linearIndependent_iffₛ.2 fun f g hfg =>
    congrFun ((key _).unique hfg rfl)) fun u _ => (Submodule.mem_span_range_iff_exists_fun R).2 (key u).exists,
    fun i => Module.Basis.mk_apply _ _ i⟩

theorem affPt_strHom {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] {T : C.Opens} (hT : IsAffineOpen T) :
    affPt hT ≫ strHom k C = spMap ((resG C (le_top : T ≤ ⊤)).comp (algebraMap k Γ(C, ⊤))) := by
  rw [strHom, affPt, ← Category.assoc, hT.fromSpec_toSpecΓ, ← Spec.map_comp]
  rfl

theorem natCast_residueField_eq_zero (q : ℕ) {k : Type} [Field k] [CharP k q] {C W : Scheme.{0}} [Algebra k Γ(C, ⊤)]
    (g : C ⟶ W) (x : C) : ((q : ℕ) : W.residueField (g x)) = 0 := by
  apply (g.residueFieldMap x).hom.injective
  rw [map_natCast, map_zero, ← map_natCast ((C.Γevaluation x).hom.comp (algebraMap k Γ(C, ⊤))), CharP.cast_eq_zero,
    map_zero]

set_option maxHeartbeats 1600000 in

theorem deg_of_sabMap {A : Type} [CommRing A] {s : X ⟶ Sp A} {ε : 𝓞 E →+* A} {q : ℕ} {W Y : Scheme.{0}} {b : W ⟶ X}
    {a : W ⟶ Y} {n : ℕ} {L : ℕ → LB Y} (hL : ∀ m, (L m).IsLB) (hF : TriFrames t s ε q b a n L)
    {k : Type} [Field k] [CharP k q] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C] (hC : IsProjCurve k C)
    (g : C ⟶ W) {t' : SAB H C} [QuasiSeparated t'.G.hom] (M : SABMap t' t (g ≫ b)) (β : A →+* k)
    (hβ : g ≫ b ≫ s = strHom k C ≫ spMap β) :
    (∀ n' ≤ n, ∑ m ∈ Finset.range n', degLB k ((L m).pull (g ≫ a)) ∈ subDegs k (Lie t'.G)) ∧
      deg k (lieSub t'.act (scal C (β.comp ε))) = ∑ m ∈ Finset.range n, degLB k ((L m).pull (g ≫ a)) := by
  classical
  obtain ⟨J₀, T₀, idx, vec, hcov, hle, htan, hnat, hfull, heig, htri⟩ := hF
  have := t'.semi
  have := hC.isProperCurve.isProper
  have : IsSeparated (terminal.from C) := by
    rw [← terminal.comp_from (strHom k C)]
    infer_instance
  obtain ⟨Ψ, hΨ, hΨa⟩ := GlobalTheory.LocM.LieEig.exists_tangent_equiv_act M
  obtain ⟨d, -, hd⟩ := exists_isVB_of_isSemiAbelian t'.G
  have := hd.isQuasicoherent
  let J := {p : C.Opens × J₀ // CoordOpen t' p.1 ∧ p.1 ≤ g ⁻¹ᵁ T₀ p.2}
  have hin {T : C.Opens} (hT : IsAffineOpen T) {U : W.Opens} (h : T ≤ g ⁻¹ᵁ U) : ⊤ ≤ (affPt hT ≫ g) ⁻¹ᵁ U :=
    fun z hz => h (le_preimage_affPt hT hz)
  have hc : ⨆ j : J, j.1.1 = ⊤ := top_unique fun x _ => by
    obtain ⟨j, hj⟩ := hcov (g x) (natCast_residueField_eq_zero q (k := k) g x)
    obtain ⟨T, hT, hx, hle⟩ := exists_coordOpen t' (V := g ⁻¹ᵁ T₀ j) hj
    exact Opens.mem_iSup.2 ⟨⟨(T, j), hT, hle⟩, hx⟩
  choose N e u hue hu hub using fun j : J => hfull j.1.2 _ (affPt j.2.1.1 ≫ g) (hin _ j.2.2)
  choose b₀ hb₀ using fun j : J => exists_basis (hu j) (hub j)
  obtain ⟨B, hBd⟩ : ∃ B : ∀ j : J, Fin (N j) → Γ(Lie t'.G, j.1.1),
      ∀ j c, B j c = Ψ _ j.2.1 _ (Category.assoc _ _ _).symm (b₀ j c) := ⟨_, fun _ _ => rfl⟩
  have hB (j : J) : VB.IsFrame (B j) := by
    have e : B j = ⇑((b₀ j).map (Ψ _ j.2.1 _ (Category.assoc _ _ _).symm)) :=
      funext fun a => (hBd j a).trans (Module.Basis.map_apply _ _ _).symm
    rw [e]
    exact Summand.isFrame_of_affine_basis j.2.1.1 _
  have hres (j : J) {T : C.Opens} (hT : CoordOpen t' T) (h : T ≤ j.1.1) (c : Fin n) :
      resM (Lie t'.G) h (B j (e j c)) =
      Ψ T hT _ (Category.assoc _ _ _).symm (tanOf (htan j.1.2 _ _ (hin hT.1 (h.trans j.2.2)) c)) := by
    rw [hBd, hb₀]
    refine (hΨ _ _ _ _ _ _ _ _ h _ _ ?_).symm
    rw [left_tanOf, left_tanOf, hue]
    have key : ∀ (x' : Sp Γ(C, T) ⟶ W) (hx : spMap (resG C h) ≫ affPt j.2.1.1 ≫ g = x') (h' : ⊤ ≤ x' ⁻¹ᵁ T₀ j.1.2),
        vec j.1.2 _ x' h' c = spMap (Formalism.L2.Pj.dualMap (resG C h)) ≫
          vec j.1.2 _ (affPt j.2.1.1 ≫ g) (hin j.2.1.1 j.2.2) c := by
      rintro _ rfl h'
      exact hnat _ _ _ _ _ _ _ _
    exact key _ (by rw [← Category.assoc, spMap_affPt]) _
  have hle' (c : Fin n) (j : J) : j.1.1 ≤ ((L c).pull (g ≫ a)).U fun _ => idx c j.1.2 :=
    (j.2.2.trans (g.preimage_mono (hle c j.1.2))).trans (GlobalTheory.LB.pull_U (L := L c) (g ≫ a) fun _ => idx c j.1.2).ge
  have hT : TriangularFrames.IsTriangular B Fin.val e fun c j j' => resG C (inf_le_inf (hle' c j) (hle' c j'))
      (((L c).pull (g ≫ a)).g (fun _ => idx c j.1.2) fun _ => idx c j'.1.2).val := fun j j' c => by
    have hT := j.2.1.mono (j.2.1.1.inf j'.2.1.1) inf_le_left
    have h := hin hT.1 (inf_le_left.trans j.2.2)
    have h' := hin hT.1 (inf_le_right.trans j'.2.2)
    obtain ⟨cf, h₁, h₂, h₃⟩ := htri j.1.2 j'.1.2 _ _ h h' c
    refine ⟨cf, h₁.trans (.symm ?_), fun c' hc hr => h₂ c' (lt_of_le_of_ne hr hc.symm), ?_⟩
    · refine (GlobalTheory.LB.resG_pull_g (L := L c) (g ≫ a) _ _ _).trans ((valR_affPt hT.1 _).symm.trans
        ((valR_appLE _ _ _ (le_preimage_affPt hT.1) _).trans ?_))
      rw [Category.assoc]
    · have key := (isComb_iff (fun c' => tanOf (htan j.1.2 _ _ h c')) cf (tanOf (htan j'.1.2 _ _ h' c))).1 h₃
      rw [hres j' hT, key, map_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [map_smul, hres j hT]
  have main := GlobalTheory.TriangularFrames.exists_isCohSub_deg_eq_sum k C hC (Lie t'.G) J _ hc (fun j => Fin (N j)) B hB
    (Fin n) Fin.val e (fun c => (L c).pull (g ≫ a)) (fun c => LB.isLB_pull (hL c) _)
    (fun c j _ => idx c j.1.2) hle' hT
  refine ⟨fun n' hn' => ?_, ?_⟩
  · obtain ⟨G, i, hi, hd, -⟩ := main (Finset.univ.filter fun c => c.val < n')
      (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega)
    refine ⟨G, i, hi, hd.trans ?_⟩
    refine Finset.sum_bij (fun c _ => c.val) (fun c hc => by simpa using hc)
      (fun _ _ _ _ => Fin.ext) (fun m hm => ?_) fun _ _ => rfl
    have := Finset.mem_range.1 hm
    exact ⟨⟨m, by omega⟩, by simpa using hm, rfl⟩
  · obtain ⟨G, i, hi, hd, hs⟩ := main Finset.univ (by simp)
    have := hi.mono
    have hψ {T : C.Opens} (hT : IsAffineOpen T) : (affPt hT ≫ g) ≫ b ≫ s =
        spMap (((resG C (le_top : T ≤ ⊤)).comp (algebraMap k Γ(C, ⊤))).comp β) := by
      rw [Category.assoc, hβ, ← Category.assoc, affPt_strHom, spMap_comp_spMap]
    have hB' (j : J) (c : Fin n) : B j (e j c) ∈ (eigenSub (lieAct t'.act) (scal C (β.comp ε))).sec j.1.1 := by
      refine mem_eigenSub_iff.2 fun o => ?_
      rw [(resM_self _ _).symm.trans (hres j j.2.1 le_rfl c), ← hΨa, ← map_smul]
      exact congrArg _ (tan_ext ((heig j.1.2 _ _ _ _ (hψ j.2.1.1)).1 c o))
    obtain ⟨φ⟩ := nonempty_iso_toMod (eigenSub (lieAct t'.act) (scal C (β.comp ε))) hc i fun j V h x => by
      refine (hs j V h x).trans ⟨fun hx => (Submodule.span_le.2 ?_) hx, fun hx => ?_⟩
      · rintro _ ⟨c, -, rfl⟩
        exact Sub.res_mem _ h (hB' j c)
      · refine (hT.mem_sub_iff hB (by simp) j h).1 (Sub.mem_of_local _ fun z hz => ?_)
        obtain ⟨U, hU, hzU, hUV⟩ := exists_coordOpen t' hz
        refine ⟨U, hUV, hzU, (hT.mem_sub_iff hB (by simp) j (hUV.trans h)).2 ?_⟩
        have hx' := mem_eigenSub_iff.1 (Sub.res_mem _ hUV hx)
        obtain ⟨w, hw⟩ := (Ψ U hU _ (Category.assoc _ _ _).symm).surjective (resM _ hUV x)
        rw [← hw] at hx' ⊢
        have h₀ := hin hU.1 ((hUV.trans h).trans j.2.2)
        obtain ⟨cf, hcf, -⟩ := (heig j.1.2 _ _ h₀ _ (hψ hU.1)).2 _ (isTan_tv w) fun o => by
          have := hx' o
          rw [← hΨa, ← map_smul] at this
          exact congrArg (fun z => (tv z).left) ((Ψ U hU _ _).injective this)
        rw [(isComb_iff (fun c' => tanOf (htan j.1.2 _ _ h₀ c')) cf w).1 hcf, map_sum]
        refine Submodule.sum_mem _ fun c _ => ?_
        rw [map_smul, ← hres j hU (hUV.trans h)]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, by simp, rfl⟩)
    refine (deg_congr k φ).symm.trans (hd.trans ?_)
    exact Fin.sum_univ_eq_sum_range (fun m => degLB k ((L m).pull (g ≫ a))) _

theorem deg_on_curve : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) {A : Type}
    [CommRing A] (s : X ⟶ Sp A) (ε : 𝓞 E →+* A) (q : ℕ) [Fact q.Prime] {W Y : Scheme.{0}} (b : W ⟶ X) (a : W ⟶ Y)
    (n : ℕ) (L : ℕ → LB Y), (∀ m, (L m).IsLB) → GlobalTheory.TriFlag.TriFrames t s ε q b a n L →
    ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C],
      IsSmoothProjCurve k C → ∀ (g : C ⟶ W) (G : Over C) [GrpObj G] [IsSemiAbelian G] (i : OAct (𝓞 E) G)
      (φ : G.left ⟶ t.G.left), IsActPull i t.act (g ≫ b) φ → ∀ β : A →+* k, g ≫ b ≫ s = strHom k C ≫ spMap β →
      (∀ n' ≤ n, ∑ m ∈ Finset.range n', degLB k ((L m).pull (g ≫ a)) ∈ subDegs k (Lie G)) ∧
        deg k (lieSub i (scal C (β.comp ε))) = ∑ m ∈ Finset.range n, degLB k ((L m).pull (g ≫ a)) := by
  intro E _ _ _ H X t A _ s ε q _ W Y b a n L hL hF k _ _ _ C _ _ hC g G _ _ i φ h β hβ
  have := (sabT Out.proved_CubePullSt (g ≫ b) t).semi
  have M := sabM Out.proved_CubePullSt (g ≫ b) t
  obtain ⟨e, he⟩ := exists_lie_iso M h
  obtain ⟨h₁, h₂⟩ := deg_of_sabMap hL hF hC.toIsProjCurve g M β hβ
  exact ⟨subDegs_congr (k := k) e ▸ h₁, (deg_congr k (eigenIso _ he)).trans h₂⟩

end GlobalTheory.TriFlag
