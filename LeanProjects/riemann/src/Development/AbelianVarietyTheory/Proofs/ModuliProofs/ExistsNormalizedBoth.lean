import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.PrimitiveExponentPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SplitOfFactorisation

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace GlobalTheory.TripleCompare

section Cech

variable {X Y Z : Scheme.{0}}

theorem gen_refine {A B : LB Y} (n : ℤ) (σ : B.ι → A.ι) (hle : ∀ i, B.U i ≤ A.U (σ i))
    (hg : ∀ i j, B.g i j = res (inf_le_inf (hle i) (hle j)) (A.g (σ i) (σ j)) ^ n)
    (h : ∃ t : LB.Gen A, t.IsGen) : ∃ t : LB.Gen B, t.IsGen := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨fun i => res (hle i) (t.s (σ i)) ^ n⟩, fun i j => ?_⟩
  have e := congrArg (res (inf_le_inf (hle i) (hle j))) (ht (σ i) (σ j))
  rw [map_mul, DVR.res_res', DVR.res_res'] at e
  rw [hg, map_zpow, map_zpow, DVR.res_res', DVR.res_res', ← mul_zpow]
  exact congrArg (· ^ n) e

theorem div_g_res (M L : LB Y) (p q : M.ι × L.ι) {V : Y.Opens}
    (h : V ≤ (M.U p.1 ⊓ L.U p.2) ⊓ (M.U q.1 ⊓ L.U q.2)) (h₁ : V ≤ M.U p.1 ⊓ M.U q.1)
    (h₂ : V ≤ L.U p.2 ⊓ L.U q.2) :
    res h ((LB.div M L).g p q) = res h₁ (M.g p.1 q.1) * (res h₂ (L.g p.2 q.2))⁻¹ :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (DVR.res_res' _ _ _)
    ((map_inv _ _).trans (congrArg (·⁻¹) (DVR.res_res' _ _ _))))

variable {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem sum_g_res (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (j j' : K' ⊕ K → L.ι) {V : Y.Opens}
    (h : V ≤ LB.wchart L (Sum.elim φ' φ) j ⊓ LB.wchart L (Sum.elim φ' φ) j')
    (h₁ : V ≤ LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ' (j' ∘ Sum.inl))
    (h₂ : V ≤ LB.wchart L φ (j ∘ Sum.inr) ⊓ LB.wchart L φ (j' ∘ Sum.inr)) :
    res h ((LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)).g j j') =
      res h₁ ((LB.LinComb L φ' ε').g (j ∘ Sum.inl) (j' ∘ Sum.inl)) *
        (res h₂ ((LB.LinComb L φ ε).g (j ∘ Sum.inr) (j' ∘ Sum.inr)))⁻¹ := by
  rw [DVR.linComb_g_res, DVR.linComb_g_res, DVR.linComb_g_res, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Function.comp]

theorem wchart_sum (φ : K → (Y ⟶ X)) (φ' : K' → (Y ⟶ X)) (j : K' ⊕ K → L.ι) :
    LB.wchart L (Sum.elim φ' φ) j =
      LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := by
  refine le_antisymm (fun y hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k),
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩) fun y hy => ?_
  refine Set.mem_iInter.2 fun k => ?_
  rcases k with k | k
  · exact Set.mem_iInter.1 hy.1 k
  · exact Set.mem_iInter.1 hy.2 k

theorem lbIso_iff_gen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
    Geo.Tor.LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ↔
      ∃ t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)), t.IsGen := by
  constructor
  · refine gen_refine (A := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) 1
      (fun j => (j ∘ Sum.inl, j ∘ Sum.inr)) (fun j => (wchart_sum φ φ' j).le) fun j j' => ?_
    have a := (wchart_sum φ φ' j).le
    have b := (wchart_sum φ φ' j').le
    refine (DVR.res_refl' _).symm.trans ((sum_g_res φ ε φ' ε' j j' le_rfl
      (inf_le_inf (a.trans inf_le_left) (b.trans inf_le_left))
      (inf_le_inf (a.trans inf_le_right) (b.trans inf_le_right))).trans (Eq.symm ?_))
    exact (zpow_one _).trans (div_g_res (LB.LinComb L φ' ε') (LB.LinComb L φ ε) _ _ _ _ _)
  · refine gen_refine (B := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε)) 1
      (fun p => Sum.elim p.1 p.2) (fun p => (wchart_sum φ φ' (Sum.elim p.1 p.2)).ge) fun p q => ?_
    refine (DVR.res_refl' _).symm.trans ((div_g_res (LB.LinComb L φ' ε') (LB.LinComb L φ ε) p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    exact (zpow_one _).trans (sum_g_res φ ε φ' ε' (Sum.elim p.1 p.2) (Sum.elim q.1 q.2) _ _ _)

theorem wchart_id (L : LB X) (j : PUnit.{1} → L.ι) :
    LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j = L.U (j ⟨⟩) :=
  le_antisymm (fun _ hy => Set.mem_iInter.1 hy PUnit.unit) fun _ hy => Set.mem_iInter.2 fun _ => hy

theorem pull_id_g_res (L : LB X) (j j' : PUnit.{1} → L.ι) {V : X.Opens}
    (h : V ≤ LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j ⊓ LB.wchart L (fun _ : PUnit.{1} => 𝟙 X) j')
    (h' : V ≤ L.U (j ⟨⟩) ⊓ L.U (j' ⟨⟩)) :
    res h ((L.pull (𝟙 X)).g j j') = res h' (L.g (j ⟨⟩) (j' ⟨⟩)) := by
  rw [DVR.linComb_g_res, Fintype.prod_unique, zpow_one, DVR.tr_def L (ψ := 𝟙 X) h']
  exact DVR.pullU_of_eq_id _ rfl _ _ _ _ _

theorem lbIso_iff_pull_id (L M : LB X) :
    Geo.Tor.LBIso L M ↔ Geo.Tor.LBIso M (L.pull (𝟙 X)) := by
  constructor
  · refine gen_refine (A := LB.div M L) (B := LB.div (L.pull (𝟙 X)) M) (-1)
      (fun p => (p.2, p.1 ⟨⟩))
      (fun p => le_inf inf_le_right (inf_le_left.trans (wchart_id L p.1).le)) fun p q => ?_
    have a := (wchart_id L p.1).le
    have b := (wchart_id L q.1).le
    refine (DVR.res_refl' _).symm.trans ((div_g_res (L.pull (𝟙 X)) M p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    refine (zpow_neg_one _).trans ((congrArg (·⁻¹) (div_g_res M L (p.2, p.1 ⟨⟩) (q.2, q.1 ⟨⟩) _
      (inf_le_inf inf_le_right inf_le_right)
      (inf_le_inf (inf_le_left.trans a) (inf_le_left.trans b)))).trans ?_)
    refine (mul_inv_rev _ _).trans (congrArg₂ (· * ·) ((inv_inv _).trans ?_) rfl)
    exact (pull_id_g_res L p.1 q.1 _ _).symm
  · refine gen_refine (B := LB.div M L) (A := LB.div (L.pull (𝟙 X)) M) (-1)
      (fun p => (fun _ => p.2, p.1))
      (fun p => le_inf (inf_le_right.trans (wchart_id L fun _ => p.2).ge) inf_le_left) fun p q => ?_
    have a := (wchart_id L fun _ => p.2).ge
    have b := (wchart_id L fun _ => q.2).ge
    refine (DVR.res_refl' _).symm.trans ((div_g_res M L p q le_rfl
      (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_right inf_le_right)).trans (Eq.symm ?_))
    refine (zpow_neg_one _).trans ((congrArg (·⁻¹) (div_g_res (L.pull (𝟙 X)) M (fun _ => p.2, p.1)
      (fun _ => q.2, q.1) _ (inf_le_inf (inf_le_right.trans a) (inf_le_right.trans b))
      (inf_le_inf inf_le_left inf_le_left))).trans ?_)
    refine (mul_inv_rev _ _).trans (congrArg₂ (· * ·) (inv_inv _) (congrArg (·⁻¹) ?_))
    exact pull_id_g_res L (fun _ => p.2) (fun _ => q.2) _ _

theorem exists_normalized_both (hL : L.IsLB) {Z₁ Z₂ : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (z₁ : Z₁ ⟶ Y) (z₂ : Z₂ ⟶ Y) (p : Y ⟶ Z₂)
    (s : Z₁ ⟶ Z₁) (h₂ : z₂ ≫ p ≫ z₂ = z₂) (h₁ : z₁ ≫ p ≫ z₂ = s ≫ z₁)
    (h0 : DVR.fsum (fun k => z₂ ≫ φ k) ε = 0)
    (hz : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t z₁) (LB.oneGen L)) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t' z₁) (LB.oneGen L) ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t' z₂) (LB.oneGen L) := by
  have hu := DVR.mulGen_isGen_of_isGen t ht _
    (DVR.invGen_isGen_of_isGen _ (DVR.pullGen_isGen_of_isGen φ ε t ht (p ≫ z₂)))
  have h0' : DVR.fsum (fun k => (p ≫ z₂) ≫ φ k) ε = 0 := by
    have := DVR.fsum_comp (fun k => z₂ ≫ φ k) ε p
    rw [h0, Finsupp.mapDomain_zero] at this
    simpa only [Category.assoc] using this
  obtain ⟨t', ht', hc⟩ := DVR.gen_transport hL (φ' := φ) (ε' := ε) (by
    rw [DVR.sameSum_iff_fsum, DVR.fsum_sumElim, DVR.fsum_neg, h0', neg_zero, add_zero]) _ hu
  have key : ∀ {W : Scheme.{0}} (z : W ⟶ Y),
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t z) (LB.pullGen L φ ε t (z ≫ p ≫ z₂)) →
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t' z) (LB.oneGen L) := fun z h =>
    DVR.corr_trans hL (DVR.corr_pullGen (DVR.corr_symm hc) z)
      (DVR.corr_trans hL (DVR.corr_pullGen_mulGen _ _ z)
        (DVR.corr_trans hL
          (DVR.corr_mulGen (DVR.corr_refl _ (DVR.pullGen_isGen_of_isGen φ ε t ht z))
            (DVR.corr_pullGen_invGen _ z))
          (DVR.corr_ratio_one
            (DVR.corr_trans hL h (DVR.corr_symm (DVR.corr_pullGen_comp t (p ≫ z₂) z))))))
  refine ⟨t', ht', key z₁ ?_, key z₂ (DVR.corr_pullGen_of_eq t ht _ _ h₂.symm)⟩
  refine DVR.corr_trans hL hz (DVR.corr_symm ?_)
  refine DVR.corr_trans hL (DVR.corr_pullGen_of_eq t ht _ _ h₁) ?_
  refine DVR.corr_trans hL (DVR.corr_symm (DVR.corr_pullGen_comp t z₁ s)) ?_
  refine DVR.corr_trans hL (DVR.corr_pullGen hz s) (DVR.corr_one_of fun j _ => ?_)
  exact IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple.res_eq_one _ (IndefiniteRowSideFullHecke.PrimitiveExponentPullback.Triple.pullU_eq_one _ _ rfl)

end Cech

section Clauses

open GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem adjoint_iff (L : LB G.left) (hL : L.IsLB) (a b : G ⟶ G) [IsMonHom a] [IsMonHom b] :
    Geo.Tor.LBIso (cubeLB G ![fst G G ≫ a, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ b] L) ↔
      IsAdjointPair G L a b := by
  refine (lbIso_iff_gen (L := L) (lamPt G (fst G G ≫ a) (snd G G)) lamExp
    (lamPt G (fst G G) (snd G G ≫ b)) lamExp).trans ⟨?_, fun ⟨t, ht, _⟩ => ⟨t, ht⟩⟩
  rintro ⟨t, ht⟩
  have s₁ := (DVR.sameSum_iff_fsum _ _ _ _).1
    (sameSum_adj G a b (lift (pzero G G) (𝟙 G)) (Or.inl (lift_fst _ _)))
  have s₂ := (DVR.sameSum_iff_fsum _ _ _ _).1
    (sameSum_adj G a b (lift (𝟙 G) (pzero G G)) (Or.inr (lift_snd _ _)))
  rw [DVR.fsum_empty] at s₁ s₂
  obtain ⟨t₁, ht₁, h₁⟩ := DVR.exists_normalized hL (adjPt G a b) adjExp t ht (snd G G).left
    (lift (pzero G G) (𝟙 G)).left (by rw [← Over.comp_left, lift_snd, Over.id_left]) s₁
  refine exists_normalized_both hL (adjPt G a b) adjExp t₁ ht₁ (lift (pzero G G) (𝟙 G)).left
    (lift (𝟙 G) (pzero G G)).left (fst G G).left (pzero G G).left ?_ ?_ s₂ (DVR.corr_one_of h₁)
  · rw [← Over.comp_left, ← Over.comp_left, lift_fst_assoc, Category.id_comp]
  · rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, lift_fst_assoc, comp_lift, comp_lift]
    simp [pzero]

theorem primitive_iff (L : RigLB G) (w : G ⟶ G) :
    Geo.Tor.LBIso L.L (cubeLB G ![𝟙 G, w] L.L) ↔ IsPrimitiveFor G L w := by
  refine (lbIso_iff_pull_id _ _).trans ((lbIso_iff_gen (L := L.L) (lamPt G (𝟙 G) w) lamExp
    (fun _ : PUnit.{1} => 𝟙 G.left) (fun _ => 1)).trans ⟨?_, fun ⟨t, ht, _⟩ => ⟨t, ht⟩⟩)
  rintro ⟨t, ht⟩
  exact DVR.exists_normalized_to L.isLB (primPt G w) primExp t ht G.hom (eSec G)
    (Over.w η[G]) _ _ L.rig L.rigGen ((DVR.sameSum_iff_fsum _ _ _ _).1 (sameSum_prim G w))

end Clauses

section Triples

open GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback GlobalTheory.HostCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}
  {S S' : Scheme.{0}}

def toTriple (t : Geo.Tor.SAB H S) : Triple (hostEquiv H) S where
  G := t.G
  semiAbelian := t.semi
  iota := t.act
  L := t.PP
  cube := t.cub
  symm := t.sym
  adjoint := fun a => by
    have := t.act.hom a
    have := t.act.hom (IndefiniteRowSideFullHecke.HostConjugateIdeal.conjO E a)
    refine (adjoint_iff t.G t.PP.L t.PP.isLB _ _).1 ?_
    rw [← bar_eq_conjO H a]
    exact t.adj a
  primitive := by
    refine (primitive_iff t.G t.PP _).1 ?_
    rw [show (hostEquiv H).w₀ = H.w0 from hostTo_w₀ H]
    exact t.prim

def ofTriple (t : Triple (hostEquiv H) S) : Geo.Tor.SAB H S where
  G := t.G
  semi := t.semiAbelian
  act := t.iota
  PP := t.L
  cub := t.cube
  sym := t.symm
  adj := fun a => by
    have := t.iota.hom a
    have := t.iota.hom (IndefiniteRowSideFullHecke.HostConjugateIdeal.conjO E a)
    rw [bar_eq_conjO H a]
    exact (adjoint_iff t.G t.L.L t.L.isLB _ _).2 (t.adjoint a)
  prim := by
    rw [← show (hostEquiv H).w₀ = H.w0 from hostTo_w₀ H]
    exact (primitive_iff t.G t.L _).2 t.primitive

def tripleEquiv (H : Geo.Tor.Host E) (S : Scheme.{0}) :
    Geo.Tor.SAB H S ≃ Triple (hostEquiv H) S where
  toFun := toTriple
  invFun := ofTriple
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem cubeMap_ext {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m m' : CubeMap G' G) (h : m.F = m'.F) (he : m.e = m'.e) : m = m' := by
  have h3 := Triple.cubeMap_tripleProduct_unique m m' h
  cases m; cases m'
  simp only at h he h3
  subst h he h3
  rfl

def toPull {t' : Geo.Tor.SAB H S'} {t : Geo.Tor.SAB H S} {f : S' ⟶ S}
    (m : Geo.Tor.SABMap t' t f) : Triple.Pull (toTriple t') (toTriple t) f where
  φ := m.φ
  isGrpPullback := m.cart
  act_comm := m.act
  bundle := ⟨m.cm, rfl, m.base, m.lin⟩

theorem toPull_bijective (t' : Geo.Tor.SAB H S') (t : Geo.Tor.SAB H S) (f : S' ⟶ S) :
    Function.Bijective (toPull (t' := t') (t := t) (f := f)) := by
  constructor
  · intro m m' h
    have e : m.cm = m'.cm :=
      cubeMap_ext _ _ (congrArg Triple.Pull.φ h) (m.base.trans m'.base.symm)
    cases m; cases m'
    simp only at e
    subst e
    rfl
  · rintro ⟨φ, h1, h2, m, rfl, h3, h4⟩
    exact ⟨⟨m, h1, h3, h2, h4⟩, rfl⟩

def pullEquiv (t' : Geo.Tor.SAB H S') (t : Geo.Tor.SAB H S) (f : S' ⟶ S) :
    Geo.Tor.SABMap t' t f ≃ Triple.Pull (tripleEquiv H S' t') (tripleEquiv H S t) f :=
  Equiv.ofBijective toPull (toPull_bijective t' t f)

def ofPullIso {t' : Geo.Tor.SAB H S'} {t : Geo.Tor.SAB H S} {f : S' ⟶ S}
    (p : Triple.PullIso (toTriple t') (toTriple t) f) : Geo.Tor.SABMap t' t f :=
  ⟨p.m, p.isGrpPullback, p.base, p.act_comm, p.w, p.isGen, p.rig, p.cube⟩

end Triples

end GlobalTheory.TripleCompare
