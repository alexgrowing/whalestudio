import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.KS GlobalTheory.KS.Sym

noncomputable section

namespace GlobalTheory.FibSym

def chartPullComp {X X' Y' : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (h : Y' ⟶ X') :
    ChartPull (L.pull (h ≫ F)) (L.pull F) h :=
  have hm : ∀ (y : Y') (J : PUnit → L.ι), y ∈ (L.pull (h ≫ F)).U J → h y ∈ (L.pull F).U J := fun y J hy =>
    (mem_pull (L := L) (F := F) (x := h y) (J := J)).2 ((mem_pull (L := L) (F := h ≫ F) (x := y) (J := J)).1 hy)
  { idx := fun J => J
    le := fun J y hy => hm y J hy
    g := fun y J J' hj hj' => (gm_pull_g L (h ≫ F) (𝟙 _) y J J' hj hj').trans
      (by rw [Category.id_comp]; exact (gm_pull_g L F h y J J' (hm y J hj) (hm y J' hj')).symm) }

theorem square_fibre_affine_opens_grp (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (R : Type) [CommRing R]
    (x₀ : R →+* K) (G : Over (Sp R)) [GrpObj G] [IsSeparated G.hom] (m : P₀.A.left ⟶ G.left)
    (h : IsGrpPullback P₀.A G (spMap x₀) m) :
    (∃ m₂ : (P₀.A ⊗ P₀.A).left ⟶ (G ⊗ G).left, IsSquare m m₂ ∧
      m₂ ≫ (fst G G * snd G G).left = (fst P₀.A P₀.A * snd P₀.A P₀.A).left ≫ m ∧
      m₂ ≫ (G ⊗ G).hom = (P₀.A ⊗ P₀.A).hom ≫ spMap x₀) ∧ IsSeparated P₀.A.hom ∧
    IsPullback (fst P₀.A P₀.A).left (snd P₀.A P₀.A).left P₀.A.hom P₀.A.hom ∧
    (∀ W : G.left.Opens, IsAffineOpen W → IsAffineOpen (m ⁻¹ᵁ W)) ∧
    ∀ W W' : G.left.Opens, IsAffineOpen W → IsAffineOpen W' → IsAffineOpen (W ⊓ W') := by
  have hp₀ : IsProper P₀.A.hom := P₀.isAb.proper
  refine ⟨exists_square_of_isGrpPullback _ _ _ _ h, inferInstance,
    IsPullback.of_hasPullback _ _, fun W hW => ?_, fun W W' hW hW' => ?_⟩
  · have : IsAffineHom m :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) h.1.flip inferInstance
    exact hW.preimage m
  · have : IsSeparated (terminal.from G.left) := by
      rw [← terminal.comp_from G.hom]; infer_instance
    exact hW.inf hW'

theorem exists_symm_of_ksCoc_grp (l₁ : Out.Laws) (l₂ : Out.Laws2)
    (hT : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A))
    (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)) (hv : IsLieBasis v)
    (hdd : ∀ a, IsInvDer (v a) (dd a)) (R : Type) [CommRing R] (x₀ : R →+* K) (G : Over (Sp R)) [GrpObj G]
    [IsSeparated G.hom] (m : P₀.A.left ⟶ G.left) (L : LB G.left) [Finite L.ι] (D : R → K)
    (d : L.ι → ∀ O : G.left.Opens, Γ(G.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i))
    (hpb : IsGrpPullback P₀.A G (spMap x₀) m) (hL : L.IsLB) (haff : ∀ i, IsAffineOpen (L.U i))
    (hiso : LBIso P₀.L (L.pull m)) (hks : KSCoc P₀.A.hom G.hom m D L.U dd d θ) (hφ : IsDlog m L dd φ) :
    ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ) := by
  obtain ⟨⟨m₂, hsq, sq₀, sqb⟩, hsep, hpull, hpre, hinf⟩ := square_fibre_affine_opens_grp K P₀ R x₀ G m hpb
  obtain ⟨hc, hind⟩ := (GlobalTheory.KS.DlogPol.dlog_independent K P₀ g v dd hv hdd _ m L hL hiso).2 φ hφ
  have hm : m ≫ G.hom = P₀.A.hom ≫ spMap x₀ := hpb.1.w
  have prod := fun W W' hW hW' => GlobalTheory.KS.ProdLift.main K R x₀ G P₀.A m m₂ D W W' hm hsq hW hW' _ rfl
  choose d₂ hd₂ c₁ c₂ using fun i j => (prod _ _ (haff i) (haff j)).1 (d i) (d j) (hks.der i) (hks.der j)
  choose w a₁ a₂ a₃ a₄ w₀ w₁ w₂ using fun a =>
    GlobalTheory.KS.SquareField.main K P₀.A (v a) (dd a) (hv.1 a) (hdd a) _ _ (Or.inl ⟨rfl, rfl⟩)
  choose w' b₁ b₂ b₃ b₄ w₀' w₂' w₁' using fun a =>
    GlobalTheory.KS.SquareField.main K P₀.A (v a) (dd a) (hv.1 a) (hdd a) _ _ (Or.inr ⟨rfl, rfl⟩)
  have hw : ∀ a, IsVF _ (w a) := fun a => ⟨a₁ a, a₂ a, a₃ a, a₄ a⟩
  have hw' : ∀ a, IsVF _ (w' a) := fun a => ⟨b₁ a, b₂ a, b₃ a, b₄ a⟩
  have cov : ⨆ i, m ⁻¹ᵁ L.U i = ⊤ := top_le_iff.1
    ((le_iSup_inf_preimage m L.U hL.cover ⊤).trans (iSup_mono fun _ => inf_le_right))
  obtain ⟨k, e, e', h₁, h₂, h₃, h₄, h₅⟩ := exists_square_data (θ := θ) sq₀ hsq.1 hsq.2 hL hd₂ hφ hc hw hw' w₀ w₁ w₂ w₀' w₂' w₁'
    (fun i i' j O hO f => diff_prod x₀ (hks.der i) (hks.der i') (hks.der j) (haff i) (haff i') (haff j) sqb
      (hd₂ i j) (hd₂ i' j) hsq.1 hsq.2 inf_le_left inf_le_left inf_le_right inf_le_right
      (fun x hx => by exact ⟨hx.1.1, hx.2⟩) (fun x hx => by exact ⟨hx.1.2, hx.2⟩) (c₁ i j) (c₂ i j) (c₁ i' j) (c₂ i' j)
      (prod _ _ (hinf _ _ (haff i) (haff i')) (haff j)).2 (fun a => θ a i i') (hks.diff i i' _ le_rfl) hw w₁ w₂ O hO f)
    (fun i j j' O hO f => diff_prod x₀ (hks.der j) (hks.der j') (hks.der i) (haff j) (haff j') (haff i) sqb
      (hd₂ i j) (hd₂ i j') hsq.2 hsq.1 inf_le_right inf_le_right inf_le_left inf_le_left
      (fun x hx => by exact ⟨hx.1, hx.2.1⟩) (fun x hx => by exact ⟨hx.1, hx.2.2⟩) (c₂ i j) (c₁ i j) (c₂ i j') (c₁ i j')
      (fun a b ha hb u u' => (prod _ _ (haff i) (hinf _ _ (haff j) (haff j'))).2 a b ha hb u' u)
      (fun a => θ a j j') (hks.diff j j' _ le_rfl) hw' w₂' w₁' O hO f)
    _ (fun _ => le_rfl) (fun a => GlobalTheory.KS.Primitive.cech_primitive l₁ l₂ hT K P₀ _ _ (φ a) cov (hc a))
  refine GlobalTheory.KS.exists_isSymm_of_square K _ _ P₀.A.hom _ _ L.ι _ g θ φ hsep hpull (fun i => hpre _ (haff i)) hind _ _ k e e' ?_
    h₁ h₂ h₃ h₄ h₅
  refine top_le_iff.1 fun x _ => ?_
  have pt : ∀ y : P₀.A.left, ∃ i, y ∈ m ⁻¹ᵁ L.U i := fun y =>
    TopologicalSpace.Opens.mem_iSup.1 (cov.ge trivial)
  obtain ⟨i, hi⟩ := pt ((fst P₀.A P₀.A * snd P₀.A P₀.A).left x)
  obtain ⟨j, hj⟩ := pt ((fst P₀.A P₀.A).left x)
  obtain ⟨l, hl⟩ := pt ((snd P₀.A P₀.A).left x)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j, l), ⟨hi, hj⟩, hl⟩

open GlobalTheory.LogKSBal in

theorem map_transpose_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (K : Type) [Field K] [CharZero K] (x₀ : Γ(X, U.1) →+* K) (P₀ : Out.PolAV (Sp K)) (mm : P₀.A.left ⟶ t.G.left), IsGrpPullback P₀.A t.G (spMap x₀ ≫ chart U) mm → LBIso P₀.L (t.PP.L.pull mm) → U.1 ≤ V → ∀ (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), IsKS t V U v D Θ → (Θ.map x₀)ᵀ = Θ.map x₀ := by
  intro E _ _ _ H X t V U n v hv hb K _ _ x₀ P₀ mm hpq hPL hUV D Θ hKS
  letI : GrpObj ((Over.pullback (chart U)).obj t.G) := Functor.grpObjObj
  let G := (Over.pullback (chart U)).obj t.G
  have hs := IsSemiAbelian.pullback (chart U) t.G t.semi
  have : IsSeparated G.hom := hs.separated
  have : QuasiCompact G.hom := hs.quasiCompact
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have := P₀.isAb.comm
  let io : G.left ⟶ t.G.left := pullback.fst t.G.hom (chart U)
  have hpb : IsGrpPullback G t.G (chart U) io := isGrpPullback_pullback t.G (chart U)
  have hw : mm ≫ t.G.hom = (P₀.A.hom ≫ spMap x₀) ≫ chart U := by
    rw [hpq.1.w, Category.assoc]
  let m : P₀.A.left ⟶ G.left := pullback.lift mm (P₀.A.hom ≫ spMap x₀) hw
  have hmio : m ≫ io = mm := pullback.lift_fst _ _ _
  have hmG : m ≫ G.hom = P₀.A.hom ≫ spMap x₀ := pullback.lift_snd _ _ _
  rw [← hmio] at hpq hPL
  have hm : IsGrpPullback P₀.A G (spMap x₀) m := IsGrpPullback.cancel hpb hpq hmG
  obtain ⟨b₁, b₂⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange t x₀ _ n v hv hb
  obtain ⟨u, hu, hbas, -⟩ := exists_lieBasis t hpq _ b₁ b₂
  choose dd hdd using fun a => (GlobalTheory.KS.InvField.main K P₀.A (u a) (hbas.1 a)).1
  obtain ⟨L, hfin, hL, haff, hiso, d, hd⟩ := exists_ksCoc t hUV hKS hpb.1 x₀ hpq hbas.1 hu hdd
  have hI : LBIso P₀.L (L.pull m) := LBIso.trans P₀.isLB (pull_isLB t.PP.isLB _) (pull_isLB hL _) hPL
    (hiso.chartPull (chartPullComp t.PP.L io m) (Geo.Tor.chartPullPull _ _ _ rfl))
  obtain ⟨⟨φ, hφ⟩, hφ'⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hbas hdd _ _ L hL hI
  obtain ⟨Θ', hs', hΘ'⟩ := exists_symm_of_ksCoc_grp GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.T.theorem_of_cube_polAbelianScheme K P₀ n u dd hbas hdd _ x₀ G m L _ d _ φ hm hL haff hI (hd φ hφ) hφ
  have e : Θ' = -Θ.map x₀ := by
    rw [eq_comm, ← sub_eq_zero]
    funext b
    refine (hφ' φ hφ).2 _ ?_
    rw [lc_sub]
    exact hΘ' b
  have h : Θ'ᵀ = Θ' := hs'
  rwa [e, Matrix.transpose_neg, neg_inj] at h

end GlobalTheory.FibSym

end
