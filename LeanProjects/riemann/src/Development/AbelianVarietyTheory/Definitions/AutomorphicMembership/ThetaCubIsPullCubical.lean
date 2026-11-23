import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullRigIsSymmetric
import Development.AbelianVarietyTheory.Definitions.Foundations.MemUnitaryGroupIffIsIsometry
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfUnimodular
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLeftInverse

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensorLB GlobalTheory.HomComb
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomComb

open ReciprocityTheory.ChartRestriction.G.Out

section Transport

variable {X X' W W' Y Y' Y₀ Y₀' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {Φ : W' ⟶ W}
  {J K : Type} [Fintype J] [Fintype K] {u : J → (W ⟶ X)} {u' : J → (W' ⟶ X')}

theorem mem_of_comm {f : Z ⟶ W'} {g : W' ⟶ X} {f' : Z ⟶ W} {g' : W ⟶ X} (e : f ≫ g = f' ≫ g') (z : Z) {U : X.Opens}
    (h : g (f z) ∈ U) : g' (f' z) ∈ U := by
  have : (f ≫ g) z ∈ U := h
  rw [e] at this
  exact this

def combIso (hu : ∀ i, u' i ≫ F = Φ ≫ u i) (δ : J → ℤ) (w : LB.Iso L' (L.pull F)) :
    LB.Iso (LB.LinComb L' u' δ) ((LB.LinComb L u δ).pull Φ) where
  s p := ∏ i, res (U := u' i ⁻¹ᵁ ((L.pull F).U (fun _ => p.1 ⟨⟩ i) ⊓ L'.U (p.2 i)))
    (V := ((LB.LinComb L u δ).pull Φ).U p.1 ⊓ (LB.LinComb L' u' δ).U p.2)
    (fun y hy => ⟨mem_pull.2 (mem_of_comm (hu i).symm y (Set.mem_iInter.1 (mem_pull.1 hy.1) i)),
      Set.mem_iInter.1 hy.2 i⟩) (pullU (u' i) _ (w.s (fun _ => p.1 ⟨⟩ i, p.2 i))) ^ δ i

theorem gw_combIso (hu : ∀ i, u' i ≫ F = Φ ≫ u i) (δ : J → ℤ) (w : LB.Iso L' (L.pull F)) (f : Z ⟶ W') (z : Z)
    (j : J → L.ι) (k : J → L'.ι) (hj : Φ (f z) ∈ LB.wchart L u j) (hk : f z ∈ LB.wchart L' u' k) :
    gw (L := LB.LinComb L u δ) (L' := LB.LinComb L' u' δ) (combIso hu δ w) f z j k =
      ∏ i, gw w (f ≫ u' i) z (j i) (k i) ^ δ i := by
  have hm : f z ∈ ((LB.LinComb L u δ).pull Φ).U (fun _ => j) ⊓ (LB.LinComb L' u' δ).U k := ⟨mem_pull.2 hj, hk⟩
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans (congrArg (· ^ δ i) ?_))
  exact (gm_res f z _ hm _).trans (gm_pull f (u' i) z ((L.pull F).U (fun _ => j i) ⊓ L'.U (k i))
    ⟨mem_pull.2 (mem_of_comm (hu i).symm (f z) (Set.mem_iInter.1 hj i)), Set.mem_iInter.1 hk i⟩ _)

theorem pGen_combIso (hu : ∀ i, u' i ≫ F = Φ ≫ u i) (δ : J → ℤ) {w : LB.Iso L' (L.pull F)} (hw : PGen w) :
    PGen (L := LB.LinComb L u δ) (L' := LB.LinComb L' u' δ) (combIso hu δ w) := by
  intro Z f z j j' k k' hj hj' hk hk'
  rw [gw_combIso hu δ w f z j k hj hk, gw_combIso hu δ w f z j' k' hj' hk']
  refine Eq.trans ?_ (congrArg (· * _) (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L u δ (f ≫ Φ) z j j' hj hj')
    (gm_linComb L' u' δ f z k k' hk hk'))).symm
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hw Z (f ≫ u' i) z (j i) (j' i) (k i) (k' i) (mem_of_comm (hu i).symm (f z) (Set.mem_iInter.1 hj i))
    (mem_of_comm (hu i).symm (f z) (Set.mem_iInter.1 hj' i)) (Set.mem_iInter.1 hk i) (Set.mem_iInter.1 hk' i),
    mul_zpow, mul_zpow, inv_zpow, Category.assoc, Category.assoc, hu]

theorem gm_pullAlong (L : LB X) (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K → (Y' ⟶ X'))
    (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y') (z : Z) (jj : K → PUnit → L.ι)
    (hz : r z ∈ LB.wchart (L.pull F) ψ jj) :
    gm r z (LB.wchart (L.pull F) ψ jj) ((GeneratorPullback.pullAlong L F h φ ε ψ hψ t).s jj) =
      gm (r ≫ h) z (LB.wchart L φ fun k => jj k ⟨⟩) (t.s fun k => jj k ⟨⟩) :=
  (gm_res r z _ hz _).trans (gm_pull r h z _ (GeneratorPullback.pullAlong_le L F h φ ψ hψ jj hz) _)

theorem pMaps_combIso (hu : ∀ i, u' i ≫ F = Φ ≫ u i) (δ : J → ℤ) {w : LB.Iso L' (L.pull F)} {ε : K → ℤ}
    {ψ' : K → (Y₀' ⟶ X')} {ψ : K → (Y₀ ⟶ X)} {a₀ : LB.Gen (LB.LinComb L' ψ' ε)} {t₀ : LB.Gen (LB.LinComb L ψ ε)}
    {h₀ : Y₀' ⟶ Y₀} (H : PMaps w ψ' ψ ε a₀ t₀ h₀) {φ' : K → (Y' ⟶ W')} {φ : K → (Y ⟶ W)} {h : Y' ⟶ Y}
    (hφ : ∀ k, φ' k ≫ Φ = h ≫ φ k) {ρ' : J → (Y' ⟶ Y₀')} {ρ : J → (Y ⟶ Y₀)}
    (hρ' : ∀ i k, φ' k ≫ u' i = ρ' i ≫ ψ' k) (hρ : ∀ i k, φ k ≫ u i = ρ i ≫ ψ k) (hh : ∀ i, h ≫ ρ i = ρ' i ≫ h₀) :
    PMaps (L := LB.LinComb L u δ) (L' := LB.LinComb L' u' δ) (combIso hu δ w) φ' φ ε
      (combGen L' u' δ φ' ε fun i => GeneratorPullback.pullAlong L' (u' i) (ρ' i) ψ' ε φ' (hρ' i) a₀)
      (combGen L u δ φ ε fun i => GeneratorPullback.pullAlong L (u i) (ρ i) ψ ε φ (hρ i) t₀) h := by
  intro Z r z p q hp hq
  have mp : (r ≫ h) z ∈ LB.wchart (LB.LinComb L u δ) φ p :=
    Set.mem_iInter.2 fun k => mem_of_comm (hφ k) (r z) (hp k)
  have mq : r z ∈ LB.wchart (LB.LinComb L' u' δ) φ' q := Set.mem_iInter.2 hq
  rw [gm_combGen L u δ φ ε _ (r ≫ h) z p mp, gm_combGen L' u' δ φ' ε _ r z q mq,
    Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (gw_combIso hu δ w (r ≫ φ' k) z (p k) (q k) (hp k) (hq k))]
  simp only [← Finset.prod_zpow]
  rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gm_pullAlong _ _ _ _ _ _ _ _ _ _ _ (GeneratorPullback.box_le L u φ p i mp),
    gm_pullAlong _ _ _ _ _ _ _ _ _ _ _ (GeneratorPullback.box_le L' u' φ' q i mq), Category.assoc, hh, ← Category.assoc,
    H Z (r ≫ ρ' i) z (fun k => p k i) (fun k => q k i)
      (fun k => by
        have e := mem_of_comm (hu i).symm (φ' k (r z)) (Set.mem_iInter.1 (hp k) i)
        exact mem_of_comm (hρ' i k) (r z) (U := F ⁻¹ᵁ L.U (p k i)) e)
      (fun k => mem_of_comm (hρ' i k) (r z) (Set.mem_iInter.1 (hq k) i)),
    mul_zpow, ← Finset.prod_zpow]
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  rw [← zpow_mul, ← zpow_mul, mul_comm, Category.assoc, Category.assoc, hρ']

end Transport

variable {S S' : Scheme.{0}} {G A : Over S} {G' A' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]
  [GrpObj G'] [IsCommMonObj G'] [GrpObj A'] [IsCommMonObj A'] {J : Type} [Fintype J]

theorem isPullCubical_comb (m : CubeMap G' G) (n : CubeMap A' A) (he : n.e = m.e) (u : J → (A ⟶ G))
    [∀ i, IsMonHom (u i)] (u' : J → (A' ⟶ G')) [∀ i, IsMonHom (u' i)] (δ : J → ℤ)
    (hu : ∀ i, (u' i).left ≫ m.F = n.F ≫ (u i).left) {L : RigLB G} {L' : RigLB G'} {c : CubicalStr G L}
    {c' : CubicalStr G' L'} (H : m.IsPullCubical c' c) : n.IsPullCubical (combCub u' δ c') (combCub u δ c) := by
  obtain ⟨w, hw, hr, ht⟩ := H
  refine ⟨combIso hu δ w, (isGen_iff _).2 (pGen_combIso hu δ ((isGen_iff _).1 hw)), ?_, ?_⟩
  · refine (maps_iff _ _ (fun _ => eSec A) _ _ (combRig u δ L).rig n.e _ (rigPull_le _ _ n.e_comm _) (fun _ => rfl)).2 ?_
    exact pMaps_combIso hu δ
      ((maps_iff _ _ (fun _ => eSec G) _ _ L.rig m.e _ (rigPull_le _ _ m.e_comm _) (fun _ => rfl)).1 hr)
      (fun _ => n.e_comm) (fun i _ => (CubeMap.ofHom (u' i)).e_comm) (fun i _ => (CubeMap.ofHom (u i)).e_comm)
      (fun i => (Category.comp_id _).trans (he.trans (Category.id_comp _).symm))
  · refine (maps_iff _ _ (thφ A (x3 A)) _ _ (combCub u δ c).t n.F3 _ (n.theta_le _) (fun _ => rfl)).2 ?_
    refine pMaps_combIso hu δ
      ((maps_iff _ _ (thφ G (x3 G)) _ _ c.t m.F3 _ (m.theta_le _) (fun _ => rfl)).1 ht)
      (fun I => n.psum_comm I.down) (fun i I => (CubeMap.ofHom (u' i)).psum_comm I.down)
      (fun i I => (CubeMap.ofHom (u i)).psum_comm I.down) (fun i => hom_ext_triple _ fun l => ?_)
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, cubeMap_comp_proj_three, Category.assoc, Category.assoc, cubeMap_comp_proj_three,
      ← Category.assoc (CubeMap.ofHom (u' i)).F3, cubeMap_comp_proj_three, Category.assoc]
    exact congrArg _ (hu i).symm

end GlobalTheory.HomComb

namespace GlobalTheory.HermTensor

variable {S : Scheme.{0}} {G A T T' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A]

theorem isMonHom_psum [GrpObj T] {n : ℕ} (x : Fin n → (T ⟶ G)) (hx : ∀ i, IsMonHom (x i)) (I : Finset (Fin n)) :
    IsMonHom (psum G x I) := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => exact isMonHom_one
  | cons k l ih =>
    have := hx k
    exact isMonHom_mul (x k) _

variable {O : Type} [CommRing O] [StarRing O] {M : Type} [AddCommGroup M] [Module O M]
  {a : OAct O G} {b : OAct O A} (t : IsTensor A b G a M) (P : Summand O M) (h : HermForm O M)

def gen (i : Fin P.n) : M := P.proj (Pi.single i 1)

def gram (i j : Fin P.n) : O := h (gen P j) (gen P i)

def crd (i : Fin P.n) : A ⟶ G := t.mapLeft (IsTensor.self a) (LinearMap.proj i ∘ₗ P.incl)

omit [StarRing O] in

theorem isLinearHom_crd (i : Fin P.n) : IsLinearHom b a (crd t P i) := t.isLinearHom_mapLeft _ _

instance isMonHom_crd (i : Fin P.n) : IsMonHom (crd t P i) := IsTensor.isMonHom_mapLeft _ _ _

omit [StarRing O] in

@[reassoc] theorem tmul_crd (m : M) (i : Fin P.n) : t.tmul m ≫ crd t P i = a.act (P.incl m i) := by
  simp [crd]

abbrev BIx (n : ℕ) : Type := (Fin n × Fin n) × ULift.{0} (Finset (Fin 2))

def biExp (n : ℕ) (q : BIx n) : ℤ := (-1) ^ (2 - q.2.down.card)

def biMap (x z : T ⟶ A) (q : BIx P.n) : T ⟶ G :=
  psum G ![x ≫ crd t P q.1.1, z ≫ crd t P q.1.2 ≫ a.act (gram P h q.1.1 q.1.2)] q.2.down

instance isMonHom_biMap [GrpObj T] (x z : T ⟶ A) [IsMonHom x] [IsMonHom z] (q : BIx P.n) :
    IsMonHom (biMap t P h x z q) :=
  isMonHom_psum _ (fun i => by
    have := a.hom
    fin_cases i
    · exact inferInstanceAs (IsMonHom (x ≫ crd t P q.1.1))
    · exact inferInstanceAs (IsMonHom (z ≫ crd t P q.1.2 ≫ a.act (gram P h q.1.1 q.1.2)))) _

def biLB (L : LB G.left) (x z : T ⟶ A) : LB T.left :=
  LB.LinComb L (fun q => (biMap t P h x z q).left) (biExp P.n)

theorem isLB_biLB {L : LB G.left} (hL : L.IsLB) (x z : T ⟶ A) : (biLB t P h L x z).IsLB := LB.isLB_linComb hL _ _

def bi (c : Pic G.left) (x z : T ⟶ A) : Pic T.left :=
  ∑ i, ∑ j, lam c (x ≫ crd t P i) (z ≫ crd t P j ≫ a.act (gram P h i j))

theorem cls_biLB {L : LB G.left} (hL : L.IsLB) (x z : T ⟶ A) (hb : (biLB t P h L x z).IsLB) :
    cls _ hb = bi t P h (cls L hL) x z := by
  refine (cls_linComb hL _ _ hb).trans ?_
  refine (Fintype.sum_prod_type _).trans ((Fintype.sum_prod_type _).trans ?_)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hc : (cubeLB G ![x ≫ crd t P i, z ≫ crd t P j ≫ a.act (gram P h i j)] L).IsLB := LB.isLB_linComb hL _ _
  refine Eq.trans ?_ (cls_cube_two hL _ _ hc)
  refine Eq.trans ?_ (cls_linComb hL _ _ hc).symm
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [biMap, biExp]

theorem pull_bi (c : Pic G.left) (g : T' ⟶ T) (x z : T ⟶ A) :
    pull g.left (bi t P h c x z) = bi t P h c (g ≫ x) (g ≫ z) := by
  simp only [bi, map_sum, pull_lam, Category.assoc]

theorem bi_one_left (c : Pic G.left) (z : T ⟶ A) : bi t P h c 1 z = 0 := by
  simp only [bi, MonObj.one_comp, lam_one_left, Finset.sum_const_zero]

def IsAdj (a : OAct O G) (L : LB G.left) : Prop :=
  ∀ c, LBIso (cubeLB G ![fst G G ≫ a.act c, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ a.act (star c)] L)

section Laws

variable {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ s : LB.Gen (Theta G L), s.IsGen) (hadj : IsAdj a L)

omit [IsCommMonObj G] in
include hadj in

theorem lam_act [IsCommMonObj G] (x y : T ⟶ G) (c : O) :
    lam (cls L hL) (x ≫ a.act c) y = lam (cls L hL) x (y ≫ a.act (star c)) := by
  have h₀ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (hadj c)
  have h' := congrArg (pull (lift x y).left)
    ((cls_cube_two hL _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
  simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'

include hΘ in

theorem bi_mul_left (x y z : T ⟶ A) :
    bi t P h (cls L hL) (x * y) z = bi t P h (cls L hL) x z + bi t P h (cls L hL) y z := by
  simp only [bi, MonObj.mul_comp, lam_mul_left hL hΘ, Finset.sum_add_distrib]

include hΘ in

theorem bi_mul_right (x y z : T ⟶ A) :
    bi t P h (cls L hL) x (y * z) = bi t P h (cls L hL) x y + bi t P h (cls L hL) x z := by
  have := a.hom
  simp only [bi, MonObj.mul_comp, lam_mul_right hL hΘ, Finset.sum_add_distrib]

include hadj in

theorem bi_comm (x z : T ⟶ A) : bi t P h (cls L hL) x z = bi t P h (cls L hL) z x := by
  rw [bi, bi, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [lam_comm, ← Category.assoc z, lam_act hL hadj, Category.assoc, gram, gram, h.star_apply]

include hadj in

theorem bi_act (x z : T ⟶ A) (c : O) :
    bi t P h (cls L hL) (x ≫ b.act c) z = bi t P h (cls L hL) x (z ≫ b.act (star c)) := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Category.assoc, (isLinearHom_crd t P i).comm, ← Category.assoc x, lam_act hL hadj, Category.assoc,
    Category.assoc, Category.assoc, act_comm a, ← Category.assoc (b.act _), (isLinearHom_crd t P j).comm,
    Category.assoc]

include hΘ hadj in

theorem bi_tmul (x z : T ⟶ G) (m n : M) :
    bi t P h (cls L hL) (x ≫ t.tmul m) (z ≫ t.tmul n) = lam (cls L hL) (x ≫ a.act (h m n)) z := by
  let φ : O →+ Pic T.left := AddMonoidHom.mk' (fun c => lam (cls L hL) (x ≫ a.act c) z) fun c d => by
    simp only [a.add, MonObj.comp_mul, lam_mul_left hL hΘ]
  have hφ : ∀ c d, lam (cls L hL) (x ≫ a.act c) (z ≫ a.act d) = φ (c * star d) := fun c d => by
    have := lam_act hL hadj (x ≫ a.act c) z (star d)
    rw [star_star, Category.assoc, ← a.mul] at this
    exact this.symm
  simp only [bi, Category.assoc, tmul_crd, tmul_crd_assoc, ← a.mul, hφ, ← map_sum]
  change _ = φ (h m n)
  congr 1
  rw [herm_expand (starRingEnd O) (fun m n => h m n) h.add_left h.smul_left (fun m n => (h.star_apply m n).symm) P m n]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul', gram, h.star_apply, _root_.mul_assoc]
  rfl

include hΘ hadj in

theorem lam_bi {w : O} (hw : w + star w = 1) (x z : T ⟶ A) :
    lam (bi t P h (cls L hL) (𝟙 A) (b.act w)) x z = bi t P h (cls L hL) x z := by
  have := b.hom w
  have e : bi t P h (cls L hL) x z = bi t P h (cls L hL) x (z ≫ b.act w) + bi t P h (cls L hL) z (x ≫ b.act w) := by
    rw [bi_comm t P h hL hadj z, bi_act t P h hL hadj, ← bi_mul_right t P h hL hΘ, ← MonObj.comp_mul, ← b.add, hw,
      b.one, Category.comp_id]
  rw [lam, e]
  simp only [pull_bi, Category.comp_id, MonObj.mul_comp, bi_one_left, bi_mul_left t P h hL hΘ,
    bi_mul_right t P h hL hΘ]
  abel

omit [StarRing O] in
include t in

theorem biadd_ext {V : Type 1} [AddCommGroup V] (β κ : (T ⟶ A) → (T ⟶ A) → V)
    (β₁ : ∀ x y z, β (x * y) z = β x z + β y z) (β₂ : ∀ x y z, β x (y * z) = β x y + β x z)
    (κ₁ : ∀ x y z, κ (x * y) z = κ x z + κ y z) (κ₂ : ∀ x y z, κ x (y * z) = κ x y + κ x z)
    (e : ∀ m n (x z : T ⟶ G), β (x ≫ t.tmul m) (z ≫ t.tmul n) = κ (x ≫ t.tmul m) (z ≫ t.tmul n)) (x z : T ⟶ A) :
    β x z = κ x z := by
  have o₁ : ∀ δ : (T ⟶ A) → (T ⟶ A) → V, (∀ x y z, δ (x * y) z = δ x z + δ y z) → ∀ z, δ 1 z = 0 := fun δ hδ z => by
    have := hδ 1 1 z
    rwa [_root_.mul_one, left_eq_add] at this
  have o₂ : ∀ δ : (T ⟶ A) → (T ⟶ A) → V, (∀ x y z, δ x (y * z) = δ x y + δ x z) → ∀ x, δ x 1 = 0 := fun δ hδ x => by
    have := hδ x 1 1
    rwa [_root_.mul_one, left_eq_add] at this
  refine t.induction_on (P := fun x => β x z = κ x z) x (by rw [o₁ β β₁, o₁ κ κ₁]) (fun m x => ?_)
    (fun x y hx hy => by rw [β₁, κ₁, hx, hy])
  exact t.induction_on (P := fun z => β (x ≫ t.tmul m) z = κ (x ≫ t.tmul m) z) z (by rw [o₂ β β₂, o₂ κ κ₂])
    (fun n z => e m n x z) (fun y z hy hz => by rw [β₂, κ₂, hy, hz])

include hΘ hadj in

theorem bi_mapLeft {A' : Over S} [GrpObj A'] [IsCommMonObj A'] {b' : OAct O A'} {M' : Type} [AddCommGroup M']
    [Module O M'] (t' : IsTensor A' b' G a M') (P' : Summand O M') (h' : HermForm O M') (f : M' →ₗ[O] M)
    (hf : h'.IsIsometry h f) (x z : T ⟶ A') :
    bi t' P' h' (cls L hL) x z = bi t P h (cls L hL) (x ≫ t'.mapLeft t f) (z ≫ t'.mapLeft t f) :=
  biadd_ext t' _ (fun x z => bi t P h (cls L hL) (x ≫ t'.mapLeft t f) (z ≫ t'.mapLeft t f))
    (bi_mul_left t' P' h' hL hΘ) (bi_mul_right t' P' h' hL hΘ)
    (fun x y z => by rw [MonObj.mul_comp, bi_mul_left t P h hL hΘ])
    (fun x y z => by rw [MonObj.mul_comp, bi_mul_right t P h hL hΘ])
    (fun m n x z => by
      rw [Category.assoc, Category.assoc, IsTensor.tmul_mapLeft, IsTensor.tmul_mapLeft, bi_tmul t P h hL hΘ hadj,
        bi_tmul t' P' h' hL hΘ hadj, hf]) x z

include hΘ hadj in

theorem bi_eq_sum {I : Type} [Fintype I] (l : I → (M →ₗ[O] O)) (hl : ∀ m n, h m n = ∑ i, l i m * star (l i n))
    (x z : T ⟶ A) : bi t P h (cls L hL) x z =
      ∑ i, lam (cls L hL) (x ≫ t.mapLeft (IsTensor.self a) (l i)) (z ≫ t.mapLeft (IsTensor.self a) (l i)) := by
  refine biadd_ext t _ (fun x z => ∑ i, lam (cls L hL) (x ≫ t.mapLeft (IsTensor.self a) (l i))
    (z ≫ t.mapLeft (IsTensor.self a) (l i))) (bi_mul_left t P h hL hΘ) (bi_mul_right t P h hL hΘ)
    (fun x y z => by simp only [MonObj.mul_comp, lam_mul_left hL hΘ, Finset.sum_add_distrib])
    (fun x y z => by simp only [MonObj.mul_comp, lam_mul_right hL hΘ, Finset.sum_add_distrib]) (fun m n x z => ?_) x z
  let φ : O →+ Pic T.left := AddMonoidHom.mk' (fun c => lam (cls L hL) (x ≫ a.act c) z) fun c d => by
    simp only [a.add, MonObj.comp_mul, lam_mul_left hL hΘ]
  have hφ : ∀ c d, lam (cls L hL) (x ≫ a.act c) (z ≫ a.act d) = φ (c * star d) := fun c d => by
    have := lam_act hL hadj (x ≫ a.act c) z (star d)
    rw [star_star, Category.assoc, ← a.mul] at this
    exact this.symm
  simp only [bi_tmul t P h hL hΘ hadj, Category.assoc, IsTensor.tmul_mapLeft, IsTensor.self_tmul, hφ, ← map_sum, ← hl]
  rfl

end Laws

section Rigid

variable [GrpObj T] [IsCommMonObj T] (x z : T ⟶ A) [IsMonHom x] [IsMonHom z]

def biRig (L : RigLB G) : RigLB T := combRig (biMap t P h x z) (biExp P.n) L

def biCub {L : RigLB G} (c : CubicalStr G L) : CubicalStr T (biRig t P h x z L) := combCub _ _ c

theorem biRig_isSymmetric {L : RigLB G} (c : CubicalStr G L) (hs : L.IsSymmetric) : (biRig t P h x z L).IsSymmetric :=
  combRig_isSymmetric _ _ c hs

end Rigid

def poi (L : RigLB G) : RigLB (A ⊗ A) := biRig t P h (fst A A) (snd A A) L

def theta (w : O) (L : RigLB G) : RigLB A := haveI := b.hom w; biRig t P h (𝟙 A) (b.act w) L

def thetaCub (w : O) {L : RigLB G} (c : CubicalStr G L) : CubicalStr A (theta t P h w L) :=
  haveI := b.hom w; biCub t P h (𝟙 A) (b.act w) c

theorem theta_isSymmetric (w : O) {L : RigLB G} (c : CubicalStr G L) (hs : L.IsSymmetric) :
    (theta t P h w L).IsSymmetric :=
  haveI := b.hom w; biRig_isSymmetric t P h (𝟙 A) (b.act w) c hs

theorem cls_poi (L : RigLB G) : cls _ (poi t P h L).isLB = bi t P h (cls L.L L.isLB) (fst A A) (snd A A) :=
  cls_biLB t P h L.isLB _ _ _

theorem cls_theta (w : O) (L : RigLB G) :
    cls _ (theta t P h w L).isLB = bi t P h (cls L.L L.isLB) (𝟙 A) (b.act w) :=
  cls_biLB t P h L.isLB _ _ _

theorem biLB_iso_pull (L : RigLB G) (x z : T ⟶ A) :
    LBIso (biLB t P h L.L x z) ((poi t P h L).L.pull (lift x z).left) := by
  refine (cls_eq_iff (isLB_biLB t P h L.isLB x z) (LB.isLB_linComb (poi t P h L).isLB _ _)).1 ?_
  rw [cls_biLB t P h L.isLB, cls_pull (poi t P h L).isLB, cls_poi, pull_bi, lift_fst, lift_snd]

theorem theta_iso_pull (w : O) (L : RigLB G) :
    LBIso (theta t P h w L).L ((poi t P h L).L.pull (lift (𝟙 A) (b.act w)).left) :=
  biLB_iso_pull t P h L _ _

def lamPt (c : Pic G.left) (z : T ⟶ A) : Pic (A ⊗ T).left := bi t P h c (fst A T) (snd A T ≫ z)

section ThetaLaws

variable {L : RigLB G} (c : CubicalStr G L) (hadj : IsAdj a L.L) {w : O} (hw : w + star w = 1)

include c in

theorem lamPt_mul (z z' : T ⟶ A) :
    lamPt t P h (cls L.L L.isLB) (z * z') = lamPt t P h (cls L.L L.isLB) z + lamPt t P h (cls L.L L.isLB) z' := by
  rw [lamPt, MonObj.comp_mul, bi_mul_right t P h L.isLB ⟨c.t, c.isGen⟩]; rfl

include c hadj hw

theorem lam_theta (x z : T ⟶ A) : lam (cls _ (theta t P h w L).isLB) x z = bi t P h (cls L.L L.isLB) x z := by
  rw [cls_theta, lam_bi t P h L.isLB ⟨c.t, c.isGen⟩ hadj hw]

theorem cube_theta_iso (x z : T ⟶ A) : LBIso (cubeLB A ![x, z] (theta t P h w L).L) (biLB t P h L.L x z) := by
  refine (cls_eq_iff (LB.isLB_linComb (theta t P h w L).isLB _ _) (isLB_biLB t P h L.isLB x z)).1 ?_
  exact ((cls_cube_two (theta t P h w L).isLB _ _ _).trans (lam_theta t P h c hadj hw x z)).trans
    (cls_biLB t P h L.isLB _ _ _).symm

theorem lam_theta_iso : LBIso (abelian₂ A (theta t P h w L).L) (poi t P h L).L :=
  cube_theta_iso t P h c hadj hw _ _

theorem theta_isAdj : IsAdj b (theta t P h w L).L := fun d => by
  have hN := (theta t P h w L).isLB
  refine (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hN _ _)).1 ?_
  refine (cls_cube_two hN _ _ _).trans (Eq.trans ?_ (cls_cube_two hN _ _ _).symm)
  rw [lam_theta t P h c hadj hw, lam_theta t P h c hadj hw, bi_act t P h L.isLB hadj]

theorem theta_prim : LBIso (theta t P h w L).L (cubeLB A ![𝟙 A, b.act w] (theta t P h w L).L) := by
  have hN := (theta t P h w L).isLB
  refine (cls_eq_iff hN (LB.isLB_linComb hN _ _)).1 (Eq.trans ?_ (cls_cube_two hN _ _ _).symm)
  rw [lam_theta t P h c hadj hw, cls_theta]

theorem theta_tmul (m n : M) :
    LBIso (cubeLB A ![fst G G ≫ t.tmul m, snd G G ≫ t.tmul n] (theta t P h w L).L)
      (cubeLB G ![fst G G ≫ a.act (h m n), snd G G] L.L) := by
  have hN := (theta t P h w L).isLB
  refine (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb L.isLB _ _)).1 ?_
  refine (cls_cube_two hN _ _ _).trans (Eq.trans ?_ (cls_cube_two L.isLB _ _ _).symm)
  rw [lam_theta t P h c hadj hw, bi_tmul t P h L.isLB ⟨c.t, c.isGen⟩ hadj]

theorem theta_kTriv [Module.Finite O M] [Module.Projective O M] (hu : h.Unimodular) (hK : Out.KTriv G L.L) :
    Out.KTriv A (theta t P h w L).L :=
  GlobalTheory.HermTensorKernel.kTriv_of_unimodular S G L.L O (starRingEnd O) M (fun m n => h m n) A a b t _ L.isLB (theta t P h w L).isLB
    ⟨_, (thetaCub t P h w c).isGen⟩ (theta_tmul t P h c hadj hw)
    ⟨star_star, h.add_left, h.smul_left, fun m n => (h.star_apply m n).symm⟩
    (fun l => by
      obtain ⟨n, hn⟩ := hu.exists_eq l
      exact ⟨n, fun m => (hn m).symm, fun n' hn' => hu.nondegenerate.ext_right fun m => (hn' m).symm.trans (hn m).symm⟩) hK

omit hw in

theorem theta_iso_mapLeft {A' : Over S} [GrpObj A'] [IsCommMonObj A'] {b' : OAct O A'} {M' : Type} [AddCommGroup M']
    [Module O M'] (t' : IsTensor A' b' G a M') (P' : Summand O M') (h' : HermForm O M') (f : M' →ₗ[O] M)
    (hf : h'.IsIsometry h f) : LBIso (theta t' P' h' w L).L ((theta t P h w L).L.pull (t'.mapLeft t f).left) := by
  refine (cls_eq_iff (theta t' P' h' w L).isLB (LB.isLB_linComb (theta t P h w L).isLB _ _)).1 ?_
  rw [cls_pull (theta t P h w L).isLB, cls_theta, cls_theta, pull_bi,
    bi_mapLeft t P h L.isLB ⟨c.t, c.isGen⟩ hadj t' P' h' f hf, Category.comp_id, Category.id_comp,
    (t'.isLinearHom_mapLeft t f).comm]

omit hw in

theorem theta_iso_box {k : ℕ} (l : Fin k → (M →ₗ[O] O)) (hl : ∀ m n, h m n = ∑ i, l i m * star (l i n))
    (hprim : LBIso L.L (cubeLB G ![𝟙 G, a.act w] L.L)) :
    LBIso (theta t P h w L).L (Out.boxLB L.L fun i => t.mapLeft (IsTensor.self a) (l i)) := by
  have e : cls L.L L.isLB = lam (cls L.L L.isLB) (𝟙 G) (a.act w) :=
    ((cls_eq_iff L.isLB (LB.isLB_linComb L.isLB _ _)).2 hprim).trans (cls_cube_two L.isLB _ _ _)
  refine (cls_eq_iff (theta t P h w L).isLB (LB.isLB_linComb L.isLB _ _)).1 ?_
  rw [cls_linComb L.isLB, cls_theta, bi_eq_sum t P h L.isLB ⟨c.t, c.isGen⟩ hadj l hl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_smul, Category.id_comp, (t.isLinearHom_mapLeft _ (l i)).comm]
  refine Eq.trans ?_ (congrArg (pull _) e).symm
  rw [pull_lam, Category.comp_id]

end ThetaLaws

section BaseChange

variable {S' : Scheme.{0}} {G₁ A₁ : Over S'} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj A₁] [IsCommMonObj A₁]
  {a₁ : OAct O G₁} {b₁ : OAct O A₁} (t₁ : IsTensor A₁ b₁ G₁ a₁ M) {f : S' ⟶ S} {φ : G₁.left ⟶ G.left}
  {ψ : A₁.left ⟶ A.left} (hφ : IsLinearPullback a₁ a f φ) (hψ : IsLinearPullback b₁ b f ψ)
  (hm : ∀ m, (t₁.tmul m).left ≫ ψ = φ ≫ (t.tmul m).left)
include hφ hψ hm

omit [StarRing O] in

theorem mapLeft_self_comm (l : M →ₗ[O] O) :
    (t₁.mapLeft (IsTensor.self a₁) l).left ≫ φ = ψ ≫ (t.mapLeft (IsTensor.self a) l).left := by
  have key : ∀ y : A₁ ⟶ A₁, pushHom hφ.1 A₁ (y ≫ t₁.mapLeft (IsTensor.self a₁) l) =
      pushHom hψ.1 A₁ y ≫ t.mapLeft (IsTensor.self a) l := fun y => by
    refine t₁.induction_on (P := fun y => pushHom hφ.1 A₁ (y ≫ t₁.mapLeft (IsTensor.self a₁) l) =
      pushHom hψ.1 A₁ y ≫ t.mapLeft (IsTensor.self a) l) y (by simp) (fun m x => Over.OverMorphism.ext ?_)
      (fun y z hy hz => by rw [MonObj.mul_comp, map_mul, map_mul, MonObj.mul_comp, hy, hz])
    rw [Category.assoc, IsTensor.tmul_mapLeft, IsTensor.self_tmul]
    change (x.left ≫ _) ≫ φ = ((x.left ≫ _) ≫ ψ) ≫ _
    rw [Category.assoc, Category.assoc, Category.assoc, hφ.comm, reassoc_of% hm, ← Over.comp_left,
      IsTensor.tmul_mapLeft, IsTensor.self_tmul]
  have e := congrArg (fun q => q.left) (key (𝟙 A₁))
  rw [Category.id_comp] at e
  exact e.trans (congrArg (· ≫ _) (Category.id_comp ψ))

theorem biMap_comm {T₁ : Over S'} (x₁ z₁ : T₁ ⟶ A₁) (x z : T ⟶ A) (U : Over.mk (T₁.hom ≫ f) ⟶ T)
    (hx : x₁.left ≫ ψ = U.left ≫ x.left) (hz : z₁.left ≫ ψ = U.left ≫ z.left) (q : BIx P.n) :
    (biMap t₁ P h x₁ z₁ q).left ≫ φ = U.left ≫ (biMap t P h x z q).left := by
  have hc : ∀ i, (crd t₁ P i).left ≫ φ = ψ ≫ (crd t P i).left := fun i => mapLeft_self_comm t t₁ hφ hψ hm _
  refine psum_push hφ.1 _ _ U (fun i => Over.OverMorphism.ext ?_) _
  fin_cases i
  · change (x₁.left ≫ _) ≫ φ = U.left ≫ x.left ≫ _
    rw [Category.assoc, hc, reassoc_of% hx]
  · change (z₁.left ≫ _ ≫ _) ≫ φ = U.left ≫ z.left ≫ _ ≫ _
    rw [Category.assoc, Category.assoc, hφ.comm, reassoc_of% hc, reassoc_of% hz]

theorem thetaCub_isPullCubical (w : O) (m : CubeMap G₁ G) (hF : m.F = φ) (he : m.e = f) {L : RigLB G} {L₁ : RigLB G₁}
    {c : CubicalStr G L} {c₁ : CubicalStr G₁ L₁} (H : m.IsPullCubical c₁ c) :
    (cubeMapOf hψ.1).IsPullCubical (thetaCub t₁ P h w c₁) (thetaCub t P h w c) := by
  have := b.hom w
  have := b₁.hom w
  subst hF
  refine isPullCubical_comb m (cubeMapOf hψ.1) he.symm _ _ _ (fun q => ?_) H
  exact (biMap_comm t P h t₁ hφ hψ hm (𝟙 A₁) (b₁.act w) (𝟙 A) (b.act w) (pushPt hψ.1.1.w (𝟙 A₁))
    (Category.comp_id _).symm ((hψ.comm w).trans (congrArg (· ≫ _) (Category.id_comp ψ).symm)) q).trans
    (congrArg (· ≫ _) (Category.id_comp ψ))

end BaseChange

theorem isSemiAbelian_tensor {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
    [Module.Projective O M] {a : OAct O G} {b : OAct O A} (t : IsTensor A b G a M) (hG : IsSemiAbelian G) :
    IsSemiAbelian A := by
  obtain ⟨n, ρ, -, hr⟩ := t.exists_retract
  exact GlobalTheory.SS.isSemiAbelian_of_retract S _ A (GlobalTheory.PowGrp.isSemiAbelian_pow S _ G n (Out.powIsPowGrp G n) hG)
    ⟨inferInstance, t.of_isSemiAbelian hG⟩ ρ.i ρ.r hr ρ.retract

end GlobalTheory.HermTensor
