import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section Flat

variable {Y X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)

private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ U) (u : Γ(X, U)ˣ) :
    res h1 (res h2 u) = res (h1.trans h2) u := by
  apply Units.ext
  show (X.presheaf.map (homOfLE h1).op).hom ((X.presheaf.map (homOfLE h2).op).hom (u : Γ(X, U))) =
    (X.presheaf.map ((homOfLE h2).op ≫ (homOfLE h1).op)).hom (u : Γ(X, U))
  rw [Functor.map_comp]
  rfl

lemma pull_g_res {X : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (a b : PUnit → L.ι) {V : Y.Opens}
    (h : V ≤ (L.pull f).U a ⊓ (L.pull f).U b) : res h ((L.pull f).g a b) = tr L V f (a PUnit.unit) (b PUnit.unit) := by
  have hV : V ≤ f ⁻¹ᵁ (L.U (a PUnit.unit) ⊓ L.U (b PUnit.unit)) := by
    intro x hx
    have hx' := h hx
    simp only [LB.pull, LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_mk,
      Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] at hx'
    exact ⟨hx'.1 PUnit.unit, hx'.2 PUnit.unit⟩
  unfold tr
  rw [dif_pos hV]
  dsimp only [LB.pull, LB.LinComb]
  rw [Fintype.prod_unique, zpow_one]
  exact (res_res_lemma h _ _).trans rfl

lemma flat_le {K : Type} [Fintype K] (p : (K → L₁.ι) × (K → L₂.ι)) (k : K) :
    LB.wchart L₁ (fun _ : K => f₁) p.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) p.2 ≤
      (L₂.pull f₂).U (fun _ => p.2 k) ⊓ (L₁.pull f₁).U (fun _ => p.1 k) := by
  intro x hx
  simp only [LB.pull, LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_mk,
    Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] at hx ⊢
  exact ⟨fun _ => hx.2 k, fun _ => hx.1 k⟩

def flatIso (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) {K : Type} [Fintype K] (ε : K → ℤ) :
    LB.Iso (LB.LinComb L₂ (fun _ : K => f₂) ε) (LB.LinComb L₁ (fun _ : K => f₁) ε) :=
  ⟨fun p => ∏ k, res (flat_le L₁ L₂ f₁ f₂ p k) (w.s (fun _ => p.2 k, fun _ => p.1 k)) ^ (-ε k)⟩

set_option maxHeartbeats 1000000 in
lemma w_pair (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (a a' : L₂.ι) (b b' : L₁.ι) {V : Y.Opens}
    (h : V ≤ ((L₂.pull f₂).U (fun _ => a) ⊓ (L₁.pull f₁).U (fun _ => b)) ⊓
      ((L₂.pull f₂).U (fun _ => a') ⊓ (L₁.pull f₁).U (fun _ => b'))) :
    res (h.trans inf_le_left) (w.s (fun _ => a, fun _ => b)) =
      tr L₂ V f₂ a a' * (tr L₁ V f₁ b b')⁻¹ * res (h.trans inf_le_right) (w.s (fun _ => a', fun _ => b')) := by
  have e := hw (fun _ => a, fun _ => b) (fun _ => a', fun _ => b')
  have e' : res (inf_le_left : ((L₂.pull f₂).U (fun _ => a) ⊓ (L₁.pull f₁).U (fun _ => b)) ⊓
        ((L₂.pull f₂).U (fun _ => a') ⊓ (L₁.pull f₁).U (fun _ => b')) ≤ _) (w.s (fun _ => a, fun _ => b)) =
      (res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
          ((L₂.pull f₂).g (fun _ => a) (fun _ => a')) *
        (res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
          ((L₁.pull f₁).g (fun _ => b) (fun _ => b')))⁻¹) *
      res (inf_le_right : _ ⊓ _ ≤ _) (w.s (fun _ => a', fun _ => b')) := e
  refine (res_res_lemma h inf_le_left _).symm.trans ?_
  refine (congrArg (res h) e').trans ?_
  refine ((res h).map_mul _ _).trans ?_
  refine (congrArg (fun t => t * _) ((res h).map_mul _ _)).trans ?_
  refine (congrArg (fun t => _ * t * _) ((res h).map_inv _)).trans ?_
  simp only [res_res_lemma]
  simp only [pull_g_res]
  exact congrArg (fun t => _ * t) (res_res_lemma h _ _)

lemma comm_alg {M : Type*} [CommGroup M] (a b c : M) (n : ℤ) :
    (a * b⁻¹ * c) ^ (-n) = b ^ n * (a ^ n)⁻¹ * c ^ (-n) := by
  rw [mul_zpow, mul_zpow, zpow_neg a, inv_zpow', neg_neg, mul_comm ((a ^ n)⁻¹) (b ^ n)]

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
lemma gm_pull_g' {Z : Scheme.{0}} {X : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (r : Z ⟶ Y) (z : Z) (a b : L.ι)
    (ha : f (r z) ∈ L.U a) (hb : f (r z) ∈ L.U b) :
    gm r z ((L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b)) ((L.pull f).g (fun _ => a) (fun _ => b)) =
      gm (r ≫ f) z (L.U a ⊓ L.U b) (L.g a b) := by
  exact (gm_linComb L (fun _ : PUnit => f) (fun _ => 1) r z (fun _ => a) (fun _ => b)
    (Set.mem_iInter.2 fun _ => ha) (Set.mem_iInter.2 fun _ => hb)).trans (by simp)

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
set_option maxHeartbeats 1000000 in
theorem flatIso_isGen (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) {K : Type} [Fintype K] (ε : K → ℤ) :
    (flatIso L₁ L₂ f₁ f₂ w ε).IsGen := by
  have hP := (isGen_iff w).1 hw
  intro (p : (K → L₁.ι) × (K → L₂.ι)) (q : (K → L₁.ι) × (K → L₂.ι))
  apply unit_ext
  intro y hy
  have hp : y ∈ LB.wchart L₁ (fun _ : K => f₁) p.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) p.2 := hy.1
  have hq : y ∈ LB.wchart L₁ (fun _ : K => f₁) q.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) q.2 := hy.2
  show gm (𝟙 Y) y _ (res _ (∏ k, res (flat_le L₁ L₂ f₁ f₂ p k) (w.s (fun _ => p.2 k, fun _ => p.1 k)) ^ (-ε k))) =
    gm (𝟙 Y) y _ ((res _ ((LB.LinComb L₁ (fun _ : K => f₁) ε).g p.1 q.1) *
      (res _ ((LB.LinComb L₂ (fun _ : K => f₂) ε).g p.2 q.2))⁻¹) *
      res _ (∏ k, res (flat_le L₁ L₂ f₁ f₂ q k) (w.s (fun _ => q.2 k, fun _ => q.1 k)) ^ (-ε k)))
  erw [map_mul, map_mul, map_inv, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy,
    gm_linComb L₁ _ ε (𝟙 Y) y p.1 q.1 hp.1 hq.1, gm_linComb L₂ _ ε (𝟙 Y) y p.2 q.2 hp.2 hq.2]
  erw [map_prod, map_prod]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h1 : f₁ y ∈ L₁.U (p.1 k) := Set.mem_iInter.1 hp.1 k
  have h1' : f₁ y ∈ L₁.U (q.1 k) := Set.mem_iInter.1 hq.1 k
  have h2 : f₂ y ∈ L₂.U (p.2 k) := Set.mem_iInter.1 hp.2 k
  have h2' : f₂ y ∈ L₂.U (q.2 k) := Set.mem_iInter.1 hq.2 k
  have e := hP Y (𝟙 Y) y (p.2 k) (q.2 k) (fun _ => p.1 k) (fun _ => q.1 k) (by simpa using h2) (by simpa using h2')
    (Set.mem_iInter.2 fun _ => by simpa using h1) (Set.mem_iInter.2 fun _ => by simpa using h1')
  rw [gm_pull_g' L₁ f₁ (𝟙 Y) y (p.1 k) (q.1 k) (by simpa using h1) (by simpa using h1')] at e
  rw [map_zpow, map_zpow]
  erw [gm_res _ y _ hp, gm_res _ y _ hq]
  change gw w (𝟙 Y) y (p.2 k) (fun _ => p.1 k) ^ (-ε k) = _ * _ * gw w (𝟙 Y) y (q.2 k) (fun _ => q.1 k) ^ (-ε k)
  rw [e]
  simp only [Category.id_comp]
  exact comm_alg _ _ _ _

end Flat

section NZ

variable {Y : Scheme.{0}}

lemma mem_nonzeroLocus {M : LB Y} (s : LB.Sec M) (y : Y) :
    y ∈ nonzeroLocus s ↔ ∃ j, y ∈ Y.basicOpen (s.f j) := by
  rw [nonzeroLocus, TopologicalSpace.Opens.mem_iSup]

theorem nonzeroLocus_secOfIso {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B) (hu : u.IsGen) (hA : A.IsLB)
    (hB : B.IsLB) : nonzeroLocus t ≤ nonzeroLocus (secOfIso (u := u) t hu hA hB) := by
  intro y hy
  obtain ⟨b, hb⟩ := (mem_nonzeroLocus t y).1 hy
  have hyb : y ∈ B.U b := Y.basicOpen_le _ hb
  obtain ⟨a, ha⟩ : ∃ a, y ∈ A.U a := by
    have : y ∈ (⨆ a, A.U a : Y.Opens) := by rw [hA.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  refine (mem_nonzeroLocus _ y).2 ⟨a, ?_⟩
  have e := secOfIso_spec (u := u) t hu hA hB a b
  have e2 := congrArg Y.basicOpen e
  rw [isoCand, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (Units.isUnit _), Scheme.basicOpen_res,
    Scheme.basicOpen_res] at e2
  have hmem : y ∈ (A.U a ⊓ B.U b) ⊓ ((A.U a ⊓ B.U b) ⊓ Y.basicOpen (t.f b)) := ⟨⟨ha, hyb⟩, ⟨ha, hyb⟩, hb⟩
  rw [← e2] at hmem
  exact hmem.2

lemma mem_basicOpen_chart {M : LB Y} (s : LB.Sec M) {y : Y} {d j : M.ι} (hd : y ∈ Y.basicOpen (s.f d))
    (hj : y ∈ M.U j) : y ∈ Y.basicOpen (s.f j) := by
  have hdU : y ∈ M.U d := Y.basicOpen_le _ hd
  have h1 : y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (inf_le_left : M.U d ⊓ M.U j ≤ M.U d)).op).hom (s.f d)) := by
    rw [Scheme.basicOpen_res]
    exact ⟨⟨hdU, hj⟩, hd⟩
  rw [s.compat d j, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (M.g d j).isUnit,
    Scheme.basicOpen_res] at h1
  exact h1.2.2

theorem nonzeroLocus_pullSec {X Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y) : h ⁻¹ᵁ nonzeroLocus s ≤ nonzeroLocus (pullSec L φ ε s h) := by
  intro z hz
  have hz' : h z ∈ nonzeroLocus s := hz
  rw [mem_nonzeroLocus] at hz' ⊢
  obtain ⟨j, hj⟩ := hz'
  refine ⟨j, ?_⟩
  have hw : h z ∈ (LB.LinComb L φ ε).U j := Y.basicOpen_le _ hj
  have hzw : z ∈ (LB.LinComb L (fun k => h ≫ φ k) ε).U j := by
    simp only [LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage,
      SetLike.mem_coe] at hw ⊢
    intro k
    exact hw k
  have hb : z ∈ Z.basicOpen ((h.app ((LB.LinComb L φ ε).U j)).hom (s.f j)) := by
    have e := Scheme.preimage_basicOpen h (s.f j)
    first
    | (rw [← e]; exact hj)
    | (change z ∈ Z.basicOpen (h.app _ (s.f j)); rw [← e]; exact hj)
    | exact e ▸ hj
  simp only [pullSec, rs]
  first
  | (rw [Scheme.basicOpen_res]; exact ⟨hzw, hb⟩)
  | exact ⟨hzw, hb⟩
  | (simp only [Scheme.basicOpen_res]; exact ⟨hzw, hb⟩)

theorem exists_sec_pow {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (f : Y ⟶ X) (n : ℕ) (hn : 1 ≤ n)
    (s : LB.Sec (LB.LinComb L (fun _ : Fin n => f) (fun _ => 1))) :
    ∃ s' : LB.Sec (LB.LinComb L (fun _ : Fin 1 => f) (fun _ => (n : ℤ))), nonzeroLocus s ≤ nonzeroLocus s' := by
  classical
  have hsame : LB.SameSum (fun _ : Fin n => f) (fun _ => (1 : ℤ)) (fun _ : Fin 1 => f) (fun _ => (n : ℤ)) := by
    rw [sameSum_iff_fsum]
    simp [fsum, Finset.sum_const, Finsupp.smul_single]
  obtain ⟨s', hs'⟩ := sec_transport (L := L) (φ := fun _ : Fin n => f) (ε := fun _ => 1) (φ' := fun _ : Fin 1 => f)
    (ε' := fun _ => (n : ℤ)) hL hsame s
  refine ⟨s', fun y hy => ?_⟩
  obtain ⟨d, hd⟩ := (mem_nonzeroLocus s y).1 hy
  have hyd : y ∈ LB.wchart L (fun _ : Fin n => f) d := Y.basicOpen_le _ hd
  set i := d ⟨0, hn⟩
  have hi : f y ∈ L.U i := Set.mem_iInter.1 hyd ⟨0, hn⟩
  have hj : y ∈ LB.wchart L (fun _ : Fin n => f) (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have hj' : y ∈ LB.wchart L (fun _ : Fin 1 => f) (fun _ => i) := Set.mem_iInter.2 fun _ => hi
  have hyj := mem_basicOpen_chart s hd hj
  have e := congrArg Y.basicOpen (hs' (fun _ => i) (fun _ => i) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl))
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hmem : y ∈ (LB.wchart L (fun _ : Fin n => f) (fun _ => i) ⊓ LB.wchart L (fun _ : Fin 1 => f) (fun _ => i)) ⊓
      Y.basicOpen (s.f (fun _ => i)) := ⟨⟨hj, hj'⟩, hyj⟩
  have hmem2 := e ▸ hmem
  exact (mem_nonzeroLocus s' y).2 ⟨_, hmem2.2⟩

lemma nonzeroLocus_cast {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} (ε : K → ℤ)
    (h : φ = φ') (s : LB.Sec (LB.LinComb L φ ε)) : nonzeroLocus (h ▸ s) = nonzeroLocus s := by
  subst h
  rfl

end NZ

section Main

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem genK_ample (hLaws : Laws) {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {H : Geo.Tor.Host E} {t : Geo.Tor.SAB H (Spec (CommRingCat.of V))}
    (P : Geo.Tor.PELUnif (IsLocalRing.maximalIdeal V) t) {k : ℕ} (hk : 4 ≤ k) :
    ⨆ s : P.U.SecK k, nonzeroLocus s = ⊤ := by
  classical
  obtain ⟨hgen, -⟩ := hLaws.ample (Spec (CommRingCat.of (FractionRing V))) P.A k hk
  obtain ⟨M, s, hs⟩ := hgen ⊤ (isAffineOpen_top _)
  obtain ⟨w, hw⟩ := P.U.ext
  set ι := (P.A.A.hom ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens)).ι with hι
  have hrange : Set.range P.U.gen.hom.left.base ⊆ Set.range ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    trivial
  set ψ := IsOpenImmersion.lift ι P.U.gen.hom.left hrange with hψdef
  have hψ : ψ ≫ ι = P.U.gen.hom.left := IsOpenImmersion.lift_fac _ _ _
  rw [eq_top_iff]
  intro y _
  have hy : ψ y ∈ (⨆ i, nonzeroLocus (s i)) := by rw [hs]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  let t1 := pullSec P.A.L (fun _ : Fin k => ι) (fun _ => 1) (s i) ψ
  have h1 : y ∈ nonzeroLocus t1 := nonzeroLocus_pullSec P.A.L _ _ (s i) ψ hi
  let t1' : LB.Sec (LB.LinComb P.A.L (fun _ : Fin k => P.U.gen.hom.left) (fun _ => 1)) :=
    (funext fun _ => hψ : (fun _ : Fin k => ψ ≫ ι) = fun _ => P.U.gen.hom.left) ▸ t1
  have h1' : y ∈ nonzeroLocus t1' := by rw [nonzeroLocus_cast]; exact h1
  obtain ⟨t2, ht2⟩ := exists_sec_pow P.A.L P.A.isLB P.U.gen.hom.left k (by omega) t1'
  let t3 : P.U.SecK k := secOfIso (u := flatIso P.A.L P.U.LG.L P.U.gen.hom.left (Limits.pullback.fst t.G.hom (jK V)) w
      (fun _ : Fin 1 => (k : ℤ))) t2 (flatIso_isGen _ _ _ _ w hw _) (linComb_isLB _ P.U.LG.isLB _ _)
      (linComb_isLB _ P.A.isLB _ _)
  have h3 : y ∈ nonzeroLocus t3 := nonzeroLocus_secOfIso _ _ _ _ _ (ht2 h1')
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨t3, h3⟩

end Main

end ReciprocityTheory.ChartRestriction.G.DVR
