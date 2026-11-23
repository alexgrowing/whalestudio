import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfSurjectiveAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentLinearisedLineBundleGaloisCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigidifiedFaithfullyFlatDescentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescendsGaloisCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleKTrivOfFiniteEtaleCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.TripleDescent

open GlobalTheory.CechPic

theorem exists_linearisation {Ga : Type} [Group Ga] {X Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (p : Y ⟶ X)
    (e : X ⟶ Y) (he : e ≫ p = 𝟙 X) (hs : Function.Surjective p.appTop.hom) (ρ : Ga → (X ⟶ X)) (τ : Ga → (Y ⟶ Y))
    (ρm : ∀ a c, ρ (a * c) = ρ a ≫ ρ c) (τm : ∀ a c, τ (a * c) = τ a ≫ τ c) (hτ : ∀ a, e ≫ τ a = ρ a ≫ e)
    (r : (L.pull e).Gen) (hr : r.IsGen) (hiso : ∀ a, LBIso L (L.pull (τ a))) :
    ∃ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, τ a] ![1, -1]), (∀ a, (u a).IsGen) ∧
      ∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (τ a))) := by
  choose u hu hn using fun g => RigidLinearisation.exists_normalised hL p e he (ρ g) (τ g) (hτ g) r hr (hiso g)
  refine ⟨u, hu, fun g h => corr_of_val hL fun y J hJ => ?_⟩
  exact RigidLinearisation.val_eq_of_rigid hL (fun U _ k => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, τm, Category.comp_id]
      simp) e (eq_one_of_surjective_appTop_of_section p e he hs) (hu _)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (hu g) (DVR.pullGen_isGen _ _ _ _ (hu h) _)) (fun y J hJ => by
      have a₁ := hn (g * h) X (𝟙 X) y J hJ
      have a₂ := hn g X (𝟙 X) y J hJ
      have a₃ := hn h X (ρ g) y J hJ
      simp only [Category.id_comp] at a₁ a₂
      rw [val_mul hJ, val_pull hJ, hτ g, a₁, a₂, a₃, ρm]
      simp) _ _ y J hJ

section Points

variable {S S' : Scheme.{0}} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B] {j : S' ⟶ S} {φ : B.left ⟶ A.left}

abbrev fibre (T : Over S) (j : S' ⟶ S) : Over S' := Over.mk (pullback.snd T.hom j)

abbrev fibreProj (T : Over S) (j : S' ⟶ S) : Over.mk ((fibre T j).hom ≫ j) ⟶ T :=
  Over.homMk (pullback.fst T.hom j) pullback.condition

theorem exists_liftPt (h : IsGrpPullback B A j φ) {T : Over S} (p : T ⟶ A) :
    ∃ x : fibre T j ⟶ B, pushPt h.1.w x = fibreProj T j ≫ p :=
  ⟨Over.homMk (h.1.lift _ _ (Over.w (fibreProj T j ≫ p))) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem pushPt_comp (h : IsGrpPullback B A j φ) {T : Over S'} (x : T ⟶ B) {a : A ⟶ A} {a' : B ⟶ B}
    (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w (x ≫ a') = pushPt h.1.w x ≫ a :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ha, Category.assoc])

theorem one_comm (h : IsGrpPullback B A j φ) : eSec B ≫ φ = j ≫ eSec A := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ B) = η[B] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[A]).left = _
  simp [eSec]

theorem exists_oAct (hR : Out.RigiditySt) {O : Type} [CommRing O] (hA : IsAbelianScheme A) [Epi j] [Epi φ]
    (h : IsGrpPullback B A j φ) (i : OAct O B) (hi : ∀ x, ∃ f : A.left ⟶ A.left, (i.act x).left ≫ φ = φ ≫ f) :
    ∃ a : OAct O A, ∀ x, (i.act x).left ≫ φ = φ ≫ (a.act x).left := by
  choose f₀ hf₀ using hi
  let f : O → (A ⟶ A) := fun x => Over.homMk (f₀ x) (by
    rw [← cancel_epi φ, ← Category.assoc, ← hf₀, Category.assoc, h.1.w, ← Category.assoc, Over.w])
  have hf : ∀ x, (i.act x).left ≫ φ = φ ≫ (f x).left := hf₀
  have ext : ∀ {a b : A ⟶ A}, φ ≫ a.left = φ ≫ b.left → a = b := fun e =>
    Over.OverMorphism.ext ((cancel_epi φ).1 e)
  refine ⟨⟨f, fun x => hR _ _ _ hA hA _ (Over.OverMorphism.ext ?_), ext ?_, fun x y => ext ?_,
    fun x y => ext ?_⟩, hf⟩
  · have := i.hom x
    have e : eSec B ≫ (i.act x).left = eSec B := congrArg (fun q => q.left) (IsMonHom.one_hom (i.act x))
    show eSec A ≫ (f x).left = eSec A
    rw [← cancel_epi j]
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [← one_comm h, Category.assoc, ← hf, ← Category.assoc, e]
  · rw [← hf, i.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  · rw [← hf, i.mul, Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  · let φ₀ : Over.mk (B.hom ≫ j) ⟶ A := Over.homMk φ h.1.w
    have h := h.2 B (i.act x) (i.act y) (φ₀ ≫ f x) (φ₀ ≫ f y) (hf x).symm (hf y).symm
    rw [← MonObj.comp_mul] at h
    rw [← hf, i.add, ← h]
    rfl

variable [IsCommMonObj A]

def cubeCls {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) (c : Pic A.left) : Pic T.left :=
  ∑ I : Finset (Fin n), ((-1 : ℤ) ^ (n - I.card)) • pull (psum A x I).left c

theorem isLB_cube {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) {L : LB A.left} (hL : L.IsLB) : (cubeLB A x L).IsLB :=
  LB.isLB_linComb hL _ _

theorem cls_cube {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) {L : LB A.left} (hL : L.IsLB) :
    cls _ (isLB_cube x hL) = cubeCls x (cls L hL) :=
  (cls_linComb hL _ _ _).trans (Fintype.sum_equiv Equiv.ulift _ _ fun _ => rfl)

theorem pull_cubeCls [IsCommMonObj B] (h : IsGrpPullback B A j φ) {T' : Over S'} {T : Over S} {n : ℕ}
    (x' : Fin n → (T' ⟶ B)) (x : Fin n → (T ⟶ A)) (U : Over.mk (T'.hom ≫ j) ⟶ T)
    (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) (c : Pic A.left) :
    pull U.left (cubeCls x c) = cubeCls x' (pull φ c) := by
  unfold cubeCls
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← pull_comp, psum_push h x' x U hx I]

theorem pull_cubeCls_pre {T' T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) (U : T' ⟶ T) (c : Pic A.left) :
    pull U.left (cubeCls x c) = cubeCls (fun i => U ≫ x i) c := by
  unfold cubeCls
  rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← Over.comp_left]
  exact congrArg (fun q : T' ⟶ A => _ • pull q.left c) (psum_hom (preHom U) x I)

theorem cubeCls_one {T : Over S} (c : Pic A.left) : cubeCls (fun _ : Fin 3 => (1 : T ⟶ A)) c = 0 := by
  have e : ∀ I : Finset (Fin 3), psum A (fun _ : Fin 3 => (1 : T ⟶ A)) I = 1 := fun I =>
    (psum_hom (1 : (T ⟶ A) →* (T ⟶ A)) (fun _ => 1) I).symm
  unfold cubeCls
  simp only [e]
  rw [← Finset.sum_smul, show ∑ I : Finset (Fin 3), (-1 : ℤ) ^ (3 - I.card) = 0 by decide, zero_smul]

end Points

theorem eq_zero_of_pull (hG : Out.GlobalFnsSt) {S S' : Scheme.{0}} (π : S' ⟶ S) [Flat π] [Surjective π]
    [QuasiCompact π] {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) (c : Pic A.left)
    (h₀ : pull (η[A]).left c = 0) (h₁ : pull (fibreProj A π).left c = 0) : c = 0 := by
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  exact (cls_eq_zero_iff hN).2 (T.exists_gen_of_rigidified_faithfullyFlat_descent hG S S' π A N hA hN ‹_› ‹_› ‹_›
    ((cls_eq_zero_iff (pull_isLB hN _)).1 h₀) ((cls_eq_zero_iff (pull_isLB hN _)).1 h₁))

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (hG : Out.GlobalFnsSt) {X Y : Scheme.{0}}
  {π : X ⟶ Y} [Flat π] [Surjective π] [QuasiCompact π] (t : SAB H X) {A : Over Y} [GrpObj A] [IsCommMonObj A]
  (hA : IsAbelianScheme A) {φ : t.G.left ⟶ A.left} (gp : IsGrpPullback t.G A π φ) (c : Pic A.left)
  (hc : pull φ c = cls t.PP.L t.PP.isLB)

include hG hA gp hc

theorem theorem_of_cube_descends : cubeCls (x3 A) c = 0 := by
  have hA₃ := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)
  refine eq_zero_of_pull hG π hA₃ _ ?_ ?_
  · rw [pull_cubeCls_pre, ← cubeCls_one c]
    congr 1
    funext k
    fin_cases k <;> simp [x3, Hom.one_def]
  · choose x hx using fun k => exists_liftPt gp (x3 A k)
    have e : cubeCls (x3 t.G) (cls t.PP.L t.PP.isLB) = 0 :=
      (cls_cube _ _).symm.trans ((cls_eq_zero_iff _).2 ⟨t.cub.t, t.cub.isGen⟩)
    have e' := congrArg (pull (lift (x 0) (lift (x 1) (x 2))).left) e
    rw [pull_cubeCls_pre, map_zero] at e'
    rw [pull_cubeCls gp x _ _ hx, hc, ← e']
    congr 1
    funext k
    fin_cases k <;> simp [x3]

theorem cubeCls_adj (act : OAct (𝓞 E) A) (hact : ∀ x, (t.act.act x).left ≫ φ = φ ≫ (act.act x).left) (a : 𝓞 E) :
    cubeCls ![fst A A ≫ act.act a, snd A A] c = cubeCls ![fst A A, snd A A ≫ act.act (H.bar a)] c := by
  have hA₂ := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA
  have := act.hom a
  have := act.hom (H.bar a)
  refine sub_eq_zero.1 (eq_zero_of_pull hG π hA₂ _ ?_ ?_)
  · rw [map_sub, pull_cubeCls_pre, pull_cubeCls_pre, sub_eq_zero]
    have e₁ : η[A ⊗ A] ≫ fst A A = 1 := by simp [Hom.one_def]
    have e₂ : η[A ⊗ A] ≫ snd A A = 1 := by simp [Hom.one_def]
    congr 1
    funext k
    fin_cases k
    · show η[A ⊗ A] ≫ fst A A ≫ act.act a = η[A ⊗ A] ≫ fst A A
      rw [← Category.assoc, e₁, MonObj.one_comp]
    · show η[A ⊗ A] ≫ snd A A = η[A ⊗ A] ≫ snd A A ≫ act.act (H.bar a)
      rw [← Category.assoc, e₂, MonObj.one_comp]
  · obtain ⟨x, hx⟩ := exists_liftPt gp (fst A A)
    obtain ⟨y, hy⟩ := exists_liftPt gp (snd A A)
    have e : cubeCls _ (cls t.PP.L t.PP.isLB) = cubeCls _ (cls t.PP.L t.PP.isLB) :=
      (cls_cube _ _).symm.trans (((cls_eq_iff _ _).2 (t.adj a)).trans (cls_cube _ _))
    have e' := congrArg (pull (lift x y).left) e
    rw [pull_cubeCls_pre, pull_cubeCls_pre] at e'
    rw [map_sub, sub_eq_zero, pull_cubeCls gp ![x ≫ t.act.act a, y] _ _ (fun k => ?_),
      pull_cubeCls gp ![x, y ≫ t.act.act (H.bar a)] _ _ (fun k => ?_), hc]
    · refine Eq.trans ?_ (e'.trans ?_)
      · congr 1
        funext k
        fin_cases k <;> simp
      · congr 1
        funext k
        fin_cases k <;> simp
    · fin_cases k
      · exact hx
      · exact (pushPt_comp gp y (hact _)).trans (by rw [hy, Category.assoc]; rfl)
    · fin_cases k
      · exact (pushPt_comp gp x (hact a)).trans (by rw [hx, Category.assoc]; rfl)
      · exact hy

omit hG hA [Flat π] [Surjective π] [QuasiCompact π] in

theorem pull_cubeCls_prim (act : OAct (𝓞 E) A) (hact : ∀ x, (t.act.act x).left ≫ φ = φ ≫ (act.act x).left) :
    pull φ (cubeCls ![𝟙 A, act.act H.w0] c) = cls t.PP.L t.PP.isLB := by
  let U : Over.mk (t.G.hom ≫ π) ⟶ A := Over.homMk φ gp.1.w
  have e := pull_cubeCls gp ![𝟙 t.G, t.act.act H.w0] ![𝟙 A, act.act H.w0] U (fun k => by
    fin_cases k
    · exact Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm)
    · exact Over.OverMorphism.ext (hact _)) c
  rw [hc] at e
  exact e.trans ((cls_cube _ _).symm.trans ((cls_eq_iff _ _).2 t.prim).symm)

end Triple

theorem exists_sab_descent_of_galoisCover : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (t : SAB H X) (g : ℕ) (ν : ∀ a, SABMap t t (ρ a)), IsGaloisCover Ga ρ π → IsQProjOver sY → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (ν 1).φ = 𝟙 _ → (∀ a c, (ν (a * c)).φ = (ν a).φ ≫ (ν c).φ) → ∃ (t' : SAB H Y) (m : SABMap t t' π), (∀ a, (ν a).φ ≫ m.φ = m.φ) ∧ IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  intro hL _ _ E _ _ _ H K _ X Y π sY Ga _ ρ t g ν hπ hq hp _ ha hk ν₁ νm
  have hG := hL.globalFns
  have := hπ.fin
  have := hπ.etale
  have := hπ.onto
  have : IsLocallyNoetherian Y := by
    obtain ⟨N, i, hi, -, rfl⟩ := hq
    have := isProper_str K N
    exact LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str K N)
  have hB : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper _ t.semi
  obtain ⟨A, _, φ, hA, gp, hφ⟩ := T.exists_abelianScheme_descent_of_galoisCover K X Y π sY Ga ρ t.G (fun a => (ν a).φ) hπ
    (RelAmpleQProj.isQProjOver_of_relAmple K X (π ≫ sY) t.G t.PP.L
      (isQProjOver_comp_of_isFinite_noetherian K X Y π sY hπ.fin hq) t.PP.isLB ha) hB (fun a => (ν a).cart) ν₁ νm
  have := hA.comm
  have := hφ.fin
  have := hφ.etale
  have := hφ.onto
  have : Epi π := Flat.epi_of_flat_of_surjective _
  have : Epi φ := Flat.epi_of_flat_of_surjective _
  obtain ⟨act, hact⟩ := exists_oAct hL.rigidity hA gp t.act fun x => by
    obtain ⟨f, hf, -⟩ := (galoisCover_descent _ _ φ Ga _ hφ).1 _ ((t.act.act x).left ≫ φ) fun a => by
      have e : (t.act.act x).left ≫ (ν a).φ = (ν a).φ ≫ (t.act.act x).left := (ν a).act x
      rw [← Category.assoc, ← e, Category.assoc, hφ.inv a]
    exact ⟨f, hf.symm⟩
  obtain ⟨u, hu₁, hu₂⟩ := exists_linearisation t.PP.isLB t.G.hom (eSec t.G) (Over.w η[t.G]) (hG _ _ hB).2 ρ
    (fun a => (ν a).φ) hπ.mul νm (fun a => one_comm (ν a).cart) t.PP.rig t.PP.rigGen fun a => by
      obtain ⟨w, hw, -⟩ := (ν a).lin
      exact ⟨w, hw⟩
  obtain ⟨M, hM, iM⟩ := T.exists_descent_linearised_lineBundle_galoisCover _ _ φ Ga _ t.PP.L hφ t.PP.isLB u hu₁ hu₂
  have hc : pull φ (cls M hM) = cls t.PP.L t.PP.isLB := ((cls_eq_iff _ (pull_isLB hM φ)).2 iM).symm
  obtain ⟨PP, cub, sym, iso, -, prim, adj⟩ := PrimNorm.exists_primitive_normalisation hG E H Y A act M hA hM
    ((cls_eq_zero_iff (isLB_cube _ hM)).1 ((cls_cube _ hM).trans (theorem_of_cube_descends hG t hA gp _ hc)))
    fun a => (cls_eq_iff (isLB_cube _ hM) (isLB_cube _ hM)).1
      ((cls_cube _ hM).trans ((cubeCls_adj hG t hA gp _ hc act hact a).trans (cls_cube _ hM).symm))
  have iP : LBIso t.PP.L (PP.L.pull φ) := (cls_eq_iff t.PP.isLB (pull_isLB PP.isLB φ)).1
    ((pull_cubeCls_prim t gp _ hc act hact).symm.trans (congrArg (pull φ)
      ((cls_cube _ hM).symm.trans ((cls_eq_iff PP.isLB (isLB_cube _ hM)).2 iso).symm)))
  let t' : SAB H Y := ⟨A, isSemiAbelian_of_isAbelianScheme A hA, act, PP, cub, sym, adj, prim⟩
  obtain ⟨m, hm⟩ := exists_sabMap_of_isProper_of_lbIso hG E H Y X t' t π φ hA.proper gp iP hact
  obtain ⟨h₁, h₂⟩ := relAmple_kTriv_of_finite_etale_cover Y X π A t.G φ PP.L t.PP.L hπ.fin hπ.etale hπ.onto hA
    PP.isLB t.PP.isLB gp iP
  exact ⟨t', m, fun a => by rw [hm]; exact hφ.inv a, hA.proper, h₁ ha, h₂ hk⟩

end GlobalTheory.TripleDescent
