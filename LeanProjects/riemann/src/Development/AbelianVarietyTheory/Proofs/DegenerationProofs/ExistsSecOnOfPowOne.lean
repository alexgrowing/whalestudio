import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsAndLocalRegularity
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSabExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TripleOut

open GlobalTheory.CechPic GlobalTheory.TripleExt

theorem exists_secOn_of_pow_one {X : Scheme.{0}} (L : LB X) (V : X.Opens)
    {σ : ∀ j, Γ(X, V ⊓ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).U j)}
    (hσ : σ ∈ secOn (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)) V) :
    ∃ θ ∈ secOn L V, ∀ j, X.basicOpen (σ j) ≤ X.basicOpen (θ (j 0)) := by
  have h : ∀ i, L.U i ≤ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).U fun _ => i :=
    fun i x hx => Set.mem_iInter.2 fun _ => hx
  have rr : ∀ {A B C : X.Opens} (e : B ≤ A) (e' : C ≤ B) (s : Γ(X, A)),
      resG X e' (resG X e s) = resG X (e'.trans e) s := fun e e' s => by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl
  refine ⟨fun i => resG X (inf_le_inf_left V (h i)) (σ fun _ => i), fun i j => ?_, fun j => ?_⟩
  · have e := congrArg (resG X (inf_le_inf (inf_le_inf_left V (h i)) (h j))) (hσ (fun _ => i) (fun _ => j))
    rw [map_mul, rr, rr, rr] at e
    rw [rr, rr, e]
    congr 1
    simp only [LB.LinComb, Fin.prod_univ_one, zpow_one]
    exact rr _ _ _
  · obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    intro x hx
    rw [Scheme.basicOpen_res]
    exact ⟨inf_le_inf_left V (LB.wchart_le L _ _ 0) (X.basicOpen_le _ hx), hx⟩

theorem mem_basicOpen_of_valF {K : Type} [Field K] {X : Scheme.{0}} (g : Sp K ⟶ X) {U : X.Opens} (f : Γ(X, U))
    (h : valF g U f ≠ 0) (w : Sp K) : g w ∈ X.basicOpen f :=
  (GlobalTheory.Points.le_preimage_basicOpen_iff g (by_contra fun hn => h (dif_neg hn)) f).2 (isUnit_iff_ne_zero.2 h)
    (x := w) trivial

theorem exists_geomPoint {X : Scheme.{0}} (y : X) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Sp K ⟶ X), ∀ w, x w = y :=
  ⟨AlgebraicClosure (X.residueField y), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField y) _)) ≫ X.fromSpecResidueField y,
    fun w => by rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem hasTheta (Z : ZHOut ρ M U₀ EE) (h : M.HasDiv S.th) : GlobalTheory.Models.HasTheta Z.G Z.L.L := by
  intro z
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨x₀, hx₀⟩ := h z
  let W : M.Z.Opens := ⟨_, M.isOpen_setOf_div S.th x₀⟩
  obtain ⟨σ, hσ, -, hne⟩ := Z.theta W x₀ fun _ hz => hz
  obtain ⟨θ, hθ, hle⟩ := exists_secOn_of_pow_one Z.L.L _ hσ
  refine ⟨W, hx₀, θ, hθ, fun y hy => ?_⟩
  obtain ⟨K, _, _, x, hx⟩ := exists_geomPoint y
  obtain ⟨g, j, hg, hv⟩ := hne K x (by rintro _ ⟨w, rfl⟩; rw [hx]; exact hy)
  refine ⟨g (IsLocalRing.closedPoint K), j 0, ?_, hle j ?_⟩
  · exact (Scheme.Hom.comp_apply g Z.G.hom _).symm.trans (hg ▸ hx _)
  · exact mem_basicOpen_of_valF g (σ j) hv _

theorem splitFib (Z : ZHOut ρ M U₀ EE) : GlobalTheory.Models.SplitFib Z.G := by
  intro z
  refine ⟨M.Z.residueField z, inferInstance, Algebra.id _, inferInstance, inferInstance, ?_⟩
  have e : Spec.map (CommRingCat.ofHom (algebraMap (M.Z.residueField z) (M.Z.residueField z))) ≫
      M.Z.fromSpecResidueField z = M.Z.fromSpecResidueField z := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have h : ∀ f : Sp (M.Z.residueField z) ⟶ M.Z, f = M.Z.fromSpecResidueField z →
      ∃ E : SplitExt (Sp (M.Z.residueField z)), E.IsGt ((Over.pullback f).obj Z.G) := by
    rintro _ rfl
    exact Z.split z
  exact h _ e

section Cube

variable {B U X : Scheme.{0}} {A : Over B} {A' : Over U} {G : Over X} [GrpObj A] [IsCommMonObj A] [GrpObj A']
  [IsCommMonObj A'] [GrpObj G] [IsCommMonObj G]

omit [IsCommMonObj A] [IsCommMonObj A'] in
theorem pushPt_comp {u : U ⟶ B} {p : A'.left ⟶ A.left} (h : IsGrpPullback A' A u p) {a' : A' ⟶ A'} {a : A ⟶ A}
    (ha : a'.left ≫ p = p ≫ a.left) {T : Over U} (x : T ⟶ A') : pushPt h.1.w (x ≫ a') = pushPt h.1.w x ≫ a :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ha, Category.assoc])

theorem adj_pull {u : U ⟶ B} {p : A'.left ⟶ A.left} (h : IsGrpPullback A' A u p) {a' b' : A' ⟶ A'} {a b : A ⟶ A}
    (ha : a'.left ≫ p = p ≫ a.left) (hb : b'.left ≫ p = p ≫ b.left) (c : Pic A.left)
    (H : cubeCls ![fst A A ≫ a, snd A A] c = cubeCls ![fst A A, snd A A ≫ b] c) {T : Over U} (y₁ y₂ : T ⟶ A') :
    cubeCls ![y₁ ≫ a', y₂] (pull p c) = cubeCls ![y₁, y₂ ≫ b'] (pull p c) := by
  let v := lift (pushPt h.1.w y₁) (pushPt h.1.w y₂)
  refine (pull_cubeCls_push h _ _ v (fun i => ?_) c).symm.trans
    ((congrArg (pull v.left) H).trans (pull_cubeCls_push h _ _ v (fun i => ?_) c))
  · fin_cases i
    · exact (pushPt_comp h ha _).trans (by simp [v])
    · simp [v]
  · fin_cases i
    · simp [v]
    · exact (pushPt_comp h hb _).trans (by simp [v])

theorem pull_graph {u : U ⟶ B} {p : A'.left ⟶ A.left} (h : IsGrpPullback A' A u p) {a' : A' ⟶ A'} {a : A ⟶ A}
    (ha : a'.left ≫ p = p ≫ a.left) (c : Pic A.left) :
    pull p (cubeCls ![𝟙 A, a] c) = cubeCls ![𝟙 A', a'] (pull p c) := by
  have h₁ := pull_cubeCls_push h ![𝟙 A', a'] ![𝟙 A, a] (pushPt h.1.w (𝟙 A'))
    (fun i => by
      fin_cases i
      · simp
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pushPt_comp h ha _)) c
  have e : (pushPt h.1.w (𝟙 A')).left = p := Category.id_comp _
  rwa [e] at h₁

variable [IsIntegral X] [IsLocallyNoetherian X] (hX : Geo.Tor.IsNormalScheme X) [Nonempty U] {j : U ⟶ X}
  [IsOpenImmersion j] (semi : IsSemiAbelian G) {φ : A'.left ⟶ G.left} (h : IsGrpPullback A' G j φ)
include hX semi h

theorem adj_extend {a' b' : A' ⟶ A'} {a b : G ⟶ G} [IsMonHom a] [IsMonHom b]
    (ha : a'.left ≫ φ = φ ≫ a.left) (hb : b'.left ≫ φ = φ ≫ b.left) (c : Pic G.left)
    (H : ∀ {T : Over U} (y₁ y₂ : T ⟶ A'), cubeCls ![y₁ ≫ a', y₂] (pull φ c) = cubeCls ![y₁, y₂ ≫ b'] (pull φ c)) :
    cubeCls ![fst G G ≫ a, snd G G] c = cubeCls ![fst G G, snd G G ≫ b] c := by
  have := semi.smooth
  have := semi.geomConnected
  have hsm : Smooth (G ⊗ G).hom := by
    show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have hgc : GeometricallyConnected (G ⊗ G).hom := by
    show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)
    exact GeometricallyConnected.comp _ _
  let T' : Over U := Over.mk (pullback.snd (G ⊗ G).hom j)
  let u : Over.mk (T'.hom ≫ j) ⟶ G ⊗ G := Over.homMk (pullback.fst (G ⊗ G).hom j) pullback.condition
  have hy : ∀ y : G ⊗ G ⟶ G, ∃ y' : T' ⟶ A', pushPt h.1.w y' = u ≫ y := fun y =>
    ⟨Over.homMk (h.1.lift (u ≫ y).left T'.hom (Over.w (u ≫ y))) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  obtain ⟨y₁, hy₁⟩ := hy (fst G G)
  obtain ⟨y₂, hy₂⟩ := hy (snd G G)
  let e : 𝟙_ (Over X) ⟶ G ⊗ G := lift η[G] η[G]
  refine pic_ext X hX j (G ⊗ G).hom e.left u.left T'.hom hsm
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e)
    (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
  · refine (pull_cubeCls_push h _ _ u (fun i => ?_) _).trans
      ((H y₁ y₂).trans (pull_cubeCls_push h _ _ u (fun i => ?_) _).symm)
    · fin_cases i
      · simp [pushPt_comp h ha, hy₁]
      · simp [hy₂]
    · fin_cases i
      · simp [hy₁]
      · simp [pushPt_comp h hb, hy₂]
  · refine (pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (pull_cubeCls_pre e _ _).symm)
    congr 1
    funext i
    fin_cases i <;> simp [e]

theorem prim_extend {a' : A' ⟶ A'} {a : G ⟶ G} [IsMonHom a] (ha : a'.left ≫ φ = φ ≫ a.left) (c : Pic G.left)
    (hc : pull (eSec G) c = 0) (H : pull φ c = cubeCls ![𝟙 A', a'] (pull φ c)) : c = cubeCls ![𝟙 G, a] c := by
  have := semi.smooth
  have := semi.geomConnected
  refine pic_ext X hX j G.hom (eSec G) φ A'.hom inferInstance
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _
    (H.trans (pull_graph h ha c).symm) ?_
  refine hc.trans (Eq.trans ?_ (pull_cubeCls_pre η[G] _ _).symm)
  refine (cubeCls_one (n := 2) _ hc).symm.trans ?_
  congr 1
  funext i
  fin_cases i <;> simp

end Cube

theorem exists_triple : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : ZHOut ρ M U₀ EE) (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (act : OAct (NumberField.RingOfIntegers E) ρ.P.A), S.Over₀ M U₀ → (∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L) → ∃ (act' : OAct (NumberField.RingOfIntegers E) Z.G) (h₂ : _) (h₃ : _), (∀ a, ((Over.pullback Z.u₀).map (act.act a)).left ≫ Z.φ = Z.φ ≫ (act'.act a).left) ∧ (GlobalTheory.Models.AbOpen Z.G → GlobalTheory.Models.Good (SAB.mk (H := H) Z.G Z.semi act' Z.L Z.cub Z.sym h₂ h₃)) := by
  intro hD o Ω _ _ _ _ S ρ M U₀ EE Z E _ _ _ H act hO hadj hprim
  have := (inferInstance : ArithBase o Ω).ft
  have := (inferInstance : ArithBase o Ω).char
  have := M.locallyOfFiniteType_int
  have hfl := M.flat_int (M.s ≫ spMap (algebraMap ℤ o))
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian (M.s ≫ spMap (algebraMap ℤ o))
  have := ρ.P.isAb.comm
  have : Nonempty U₀.toScheme := hO.ne.to_subtype
  have hd : Dense (U₀ : Set M.Z) := U₀.isOpen.dense hO.ne
  obtain ⟨_, _⟩ := ExtUnique.dense_open U₀ hd
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian Z.G Z.semi
  let act₀ := Geo.Tor.OAct.pullback Z.u₀ ρ.P.A act
  obtain ⟨act', hact, -⟩ := ExtUnique.existsUnique_oAct_of_isGrpPullback Z.cart act₀ fun x => by
    obtain ⟨e, he, he'⟩ := grpPullback_iso Z.cart (isGrpPullback_pullback Z.G U₀.ι)
    have := act₀.hom x
    obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian_normal hD M.Z U₀ U₀.ι ⟨hO.normal, _, inferInstance, hfl⟩ inferInstance inferInstance
      inferInstance inferInstance Z.G Z.G Z.semi Z.semi (e.inv ≫ act₀.act x ≫ e.hom) inferInstance
    refine ⟨F, ?_⟩
    rw [← he', Category.assoc, ← ExtUnique.pullback_map_left_fst, hF, ← Category.assoc, ← Category.assoc,
      ← Over.comp_left, ← Over.comp_left, Iso.hom_inv_id_assoc]
  have hp := isGrpPullback_pullback ρ.P.A Z.u₀
  have ha : ∀ x, (act₀.act x).left ≫ pullback.fst ρ.P.A.hom Z.u₀ = pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act x).left :=
    fun x => ExtUnique.pullback_map_left_fst _ _
  have hc : pull Z.φ (cls Z.L.L Z.L.isLB) = pull (pullback.fst ρ.P.A.hom Z.u₀) (cls ρ.P.L ρ.P.isLB) :=
    (cls_eq_iff (pull_isLB Z.L.isLB _) (pull_isLB ρ.P.isLB _)).2 ⟨Z.w, Z.w_gen⟩
  refine ⟨act', fun b => ?_, ?_, hact, fun h => ⟨h, splitFib Z, hasTheta Z hO.div⟩⟩
  · refine (cls_eq_iff (isLB_cube _ Z.L.isLB) (isLB_cube _ Z.L.isLB)).1 ?_
    rw [cls_cube _ Z.L.isLB, cls_cube _ Z.L.isLB]
    have := act'.hom b
    have := act'.hom (H.bar b)
    have h₀ := (cls_eq_iff (isLB_cube _ ρ.P.isLB) (isLB_cube _ ρ.P.isLB)).2 (hadj b)
    rw [cls_cube _ ρ.P.isLB, cls_cube _ ρ.P.isLB] at h₀
    refine adj_extend hO.normal Z.semi Z.cart (hact b) (hact (H.bar b)) _ fun y₁ y₂ => ?_
    rw [hc]
    exact adj_pull hp (ha b) (ha (H.bar b)) _ h₀ y₁ y₂
  · refine (cls_eq_iff Z.L.isLB (isLB_cube _ Z.L.isLB)).1 ?_
    rw [cls_cube _ Z.L.isLB]
    have := act'.hom H.w0
    have h₀ := (cls_eq_iff ρ.P.isLB (isLB_cube _ ρ.P.isLB)).2 hprim
    rw [cls_cube _ ρ.P.isLB] at h₀
    refine prim_extend hO.normal Z.semi Z.cart (hact H.w0) _
      ((cls_eq_zero_iff (pull_isLB Z.L.isLB _)).2 ⟨Z.L.rig, Z.L.rigGen⟩) ?_
    rw [hc]
    exact (congrArg (pull _) h₀).trans (pull_graph hp (ha H.w0) _)

end GlobalTheory.TripleOut
