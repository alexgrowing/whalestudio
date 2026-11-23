import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

section Germs

def gU {X : Scheme.{0}} {O : X.Opens} (x : X) (hx : x ∈ O) : Γ(X, O)ˣ →* (X.presheaf.stalk x)ˣ :=
  Units.map (X.presheaf.germ O x hx).hom

theorem unit_ext {X : Scheme.{0}} {O : X.Opens} (s t : Γ(X, O)ˣ)
    (h : ∀ x (hx : x ∈ O), gU x hx s = gU x hx t) : s = t := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext X.sheaf
  intro x hx
  first
  | exact congrArg Units.val (h x hx)
  | simpa [gU] using congrArg Units.val (h x hx)

theorem gU_res {X : Scheme.{0}} {O O' : X.Opens} (hle : O' ≤ O) (x : X) (hx : x ∈ O')
    (s : Γ(X, O)ˣ) : gU x hx (res hle s) = gU x (hle hx) s := by
  apply Units.ext
  first
  | exact congrArg (fun φ => φ.hom s.val) (X.presheaf.germ_res (homOfLE hle) x hx)
  | (simp [gU, res]; done)

theorem gU_pullU {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (y : Y) (hy : y ∈ f ⁻¹ᵁ U)
    (x : Γ(X, U)ˣ) :
    gU y hy (pullU f U x) = Units.map (f.stalkMap y).hom (gU (f.base y) hy x) := by
  apply Units.ext
  first
  | (simp [gU, pullU]; done)
  | exact (congrArg (fun φ => φ.hom x.val) (Scheme.Hom.germ_stalkMap f U y hy)).symm
  | exact congrArg (fun φ => φ.hom x.val) (Scheme.Hom.germ_stalkMap f U y hy)

theorem pullU_res' {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    pullU f V (res h x) = res (fun _ hy => h hy : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (pullU f U x) := by
  apply unit_ext
  intro y hy
  have hP : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U := fun _ hz => h hz
  rw [gU_pullU, gU_res h (f.base y) hy x]
  exact (gU_pullU f U y (hP hy) x).symm.trans (gU_res hP y hy (pullU f U x)).symm

theorem gU_pullU_congr {X Y : Scheme.{0}} {φ ψ : Y ⟶ X} (h : φ = ψ) (U : X.Opens) (x : Γ(X, U)ˣ)
    (p : Y) (hp : p ∈ φ ⁻¹ᵁ U) (hp' : p ∈ ψ ⁻¹ᵁ U) :
    gU p hp (pullU φ U x) = gU p hp' (pullU ψ U x) := by
  subst h
  rfl

theorem gU_pullU_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ)
    (y : Y) (hy : y ∈ f ⁻¹ᵁ V) (hy' : y ∈ f ⁻¹ᵁ U) :
    gU y hy (pullU f V (res h x)) = gU y hy' (pullU f U x) := by
  rw [gU_pullU, gU_res h (f.base y) hy x]
  exact (gU_pullU f U y hy' x).symm

theorem mem_wchart_pu {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (j : PUnit.{1} → L.ι) (y : Y) :
    y ∈ LB.wchart L (fun _ : PUnit.{1} => φ) j ↔ φ.base y ∈ L.U (j PUnit.unit) := by
  show y ∈ (⋂ k : PUnit.{1}, φ.base ⁻¹' (L.U (j k) : Set X)) ↔ _
  rw [Set.mem_iInter]
  exact ⟨fun h => h PUnit.unit, fun h _ => h⟩

end Germs

section Transfer

variable {X Y Z Y' : Scheme.{0}}

theorem exists_gen_transfer {L L' : LB X} (e : L'.ι → L.ι) (hU : ∀ j, L'.U j ≤ L.U (e j))
    (hg : ∀ i j (y : X) (hy : y ∈ L'.U i ⊓ L'.U j),
      gU y hy (L'.g i j) = gU y (⟨hU i hy.1, hU j hy.2⟩ : y ∈ L.U (e i) ⊓ L.U (e j)) (L.g (e i) (e j)))
    (h : ∃ t : LB.Gen L, t.IsGen) : ∃ t' : LB.Gen L', t'.IsGen := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨fun j => res (hU j) (t.s (e j))⟩, fun i j => ?_⟩
  apply unit_ext
  intro y hy
  have hm : y ∈ L.U (e i) ⊓ L.U (e j) := ⟨hU i hy.1, hU j hy.2⟩
  have key := congrArg (gU y hm) (ht (e i) (e j))
  simp only [map_mul, gU_res] at key ⊢
  rw [hg i j y hy]
  exact key

private theorem pull_le_lemma_5 (L : LB X) (a : Y ⟶ X) (i j : PUnit.{1} → L.ι) :
    (L.pull a).U i ⊓ (L.pull a).U j ≤ a ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
  fun y hy => ⟨(mem_wchart_pu L a i y).1 hy.1, (mem_wchart_pu L a j y).1 hy.2⟩

private theorem pull_g_lemma_6 (L : LB X) (a : Y ⟶ X) (i j : PUnit.{1} → L.ι) :
    (L.pull a).g i j = res (pull_le_lemma_5 L a i j) (pullU a _ (L.g (i PUnit.unit) (j PUnit.unit))) := by
  dsimp only [LB.pull, LB.LinComb]
  simp only [Fintype.prod_subsingleton _ PUnit.unit, zpow_one]
  first
  | rfl
  | skip

theorem germ_pull (L : LB X) (a : Y ⟶ X) (i j : PUnit.{1} → L.ι) (y : Y)
    (hy : y ∈ (L.pull a).U i ⊓ (L.pull a).U j)
    (hy' : y ∈ a ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))) :
    gU y hy ((L.pull a).g i j) = gU y hy' (pullU a _ (L.g (i PUnit.unit) (j PUnit.unit))) := by
  rw [pull_g_lemma_6 L a i j]
  exact gU_res _ y hy _

theorem pull_inf_le (L : LB X) (a : Y ⟶ X) (i j : PUnit.{1} → L.ι) :
    (L.pull a).U i ⊓ (L.pull a).U j ≤ a ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) := fun y hy => ⟨(mem_wchart_pu L a i y).1 hy.1, (mem_wchart_pu L a j y).1 hy.2⟩

theorem pull_g_eq (L : LB X) (a : Y ⟶ X) (i j : PUnit.{1} → L.ι) :
    (L.pull a).g i j = res (pull_inf_le L a i j) (pullU a _ (L.g (i PUnit.unit) (j PUnit.unit))) := pull_g_lemma_6 L a i j

theorem base_eq {A B B' C : Scheme.{0}} {f : A ⟶ B} {g : A ⟶ B'} {f' : B ⟶ C} {g' : B' ⟶ C}
    (h : f ≫ f' = g ≫ g') (z : A) :
    f'.base (f.base z) = g'.base (g.base z) := by
  first
  | exact congrArg (fun φ : A ⟶ C => φ.base z) h
  | simpa using congrArg (fun φ : A ⟶ C => φ.base z) h

private theorem gU_pullU_comp_lemma (b : Z ⟶ Y) (a : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) (y : Z)
    (hy : y ∈ (b ≫ a) ⁻¹ᵁ U) :
    gU y hy (pullU (b ≫ a) U x) = gU y hy (pullU b (a ⁻¹ᵁ U) (pullU a U x)) := rfl

theorem germ_pull_pull (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) (i j : PUnit.{1} → PUnit.{1} → L.ι) (y : Z)
    (hy : y ∈ ((L.pull a).pull b).U i ⊓ ((L.pull a).pull b).U j)
    (hy' : y ∈ (b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit))) :
    gU y hy (((L.pull a).pull b).g i j) =
      gU y hy' (pullU (b ≫ a) _ (L.g (i PUnit.unit PUnit.unit) (j PUnit.unit PUnit.unit))) := by
  rw [pull_g_eq (L.pull a) b i j, gU_res _ y hy, pull_g_eq L a (i PUnit.unit) (j PUnit.unit),
    gU_pullU_comp_lemma]
  exact gU_pullU_res _ _ _ _ _ _

private theorem mem_pull_pull_lemma_2 (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y)
    (j : PUnit.{1} → PUnit.{1} → L.ι) (z : Z) :
    z ∈ ((L.pull a).pull b).U j ↔ a.base (b.base z) ∈ L.U (j PUnit.unit PUnit.unit) :=
  (mem_wchart_pu (L.pull a) b j z).trans (mem_wchart_pu L a (j PUnit.unit) (b.base z))

theorem gen_pull_pull (L : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) (c : Y' ⟶ X) (d : Z ⟶ Y')
    (hbd : b ≫ a = d ≫ c) (h : ∃ t : LB.Gen ((L.pull a).pull b), t.IsGen) :
    ∃ t : LB.Gen ((L.pull c).pull d), t.IsGen := by
  have hmem : ∀ (j : PUnit.{1} → PUnit.{1} → L.ι) (z : Z),
      z ∈ ((L.pull c).pull d).U j → z ∈ ((L.pull a).pull b).U j := by
    intro j z hz
    rw [mem_pull_pull_lemma_2 L c d j z] at hz
    rw [mem_pull_pull_lemma_2 L a b j z]
    rw [base_eq hbd z]
    exact hz
  refine exists_gen_transfer (L := (L.pull a).pull b) (L' := (L.pull c).pull d) (fun j => j)
    (fun j z hz => hmem j z hz) ?_ h
  intro i j y hy
  have h1 : y ∈ (d ≫ c) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit)) :=
    ⟨(mem_pull_pull_lemma_2 L c d i y).1 hy.1, (mem_pull_pull_lemma_2 L c d j y).1 hy.2⟩
  have h2 : y ∈ (b ≫ a) ⁻¹ᵁ (L.U (i PUnit.unit PUnit.unit) ⊓ L.U (j PUnit.unit PUnit.unit)) := by
    rw [hbd]
    exact h1
  exact (germ_pull_pull L c d i j y hy h1).trans
    ((gU_pullU_congr hbd.symm _ _ y h1 h2).trans (germ_pull_pull L a b i j y _ h2).symm)

theorem germ_div (M N : LB X) (p p' : (LB.div M N).ι) (y : X)
    (hy : y ∈ (LB.div M N).U p ⊓ (LB.div M N).U p') :
    gU y hy ((LB.div M N).g p p') =
      gU y (⟨hy.1.1, hy.2.1⟩ : y ∈ M.U p.1 ⊓ M.U p'.1) (M.g p.1 p'.1) *
        (gU y (⟨hy.1.2, hy.2.2⟩ : y ∈ N.U p.2 ⊓ N.U p'.2) (N.g p.2 p'.2))⁻¹ := by
  have h1 : ((LB.div M N).U p ⊓ (LB.div M N).U p') ≤ M.U p.1 ⊓ M.U p'.1 := fun z hz => ⟨hz.1.1, hz.2.1⟩
  have h2 : ((LB.div M N).U p ⊓ (LB.div M N).U p') ≤ N.U p.2 ⊓ N.U p'.2 := fun z hz => ⟨hz.1.2, hz.2.2⟩
  have e : (LB.div M N).g p p' = res h1 (M.g p.1 p'.1) * (res h2 (N.g p.2 p'.2))⁻¹ := rfl
  exact (congrArg (gU y hy) e).trans ((map_mul (gU y hy) _ _).trans
    (congrArg₂ (· * ·) (gU_res h1 y hy _)
      ((map_inv (gU y hy) _).trans (congrArg (·⁻¹) (gU_res h2 y hy _)))))

theorem germ_pullU_div (M N : LB X) (a : Y ⟶ X) (p p' : (LB.div M N).ι) (y : Y)
    (hy : y ∈ a ⁻¹ᵁ ((LB.div M N).U p ⊓ (LB.div M N).U p'))
    (h1 : y ∈ a ⁻¹ᵁ (M.U p.1 ⊓ M.U p'.1)) (h2 : y ∈ a ⁻¹ᵁ (N.U p.2 ⊓ N.U p'.2)) :
    gU y hy (pullU a _ ((LB.div M N).g p p')) =
      gU y h1 (pullU a _ (M.g p.1 p'.1)) * (gU y h2 (pullU a _ (N.g p.2 p'.2)))⁻¹ := by
  have k1 : ((LB.div M N).U p ⊓ (LB.div M N).U p') ≤ M.U p.1 ⊓ M.U p'.1 := fun z hz => ⟨hz.1.1, hz.2.1⟩
  have k2 : ((LB.div M N).U p ⊓ (LB.div M N).U p') ≤ N.U p.2 ⊓ N.U p'.2 := fun z hz => ⟨hz.1.2, hz.2.2⟩
  have e : (LB.div M N).g p p' = res k1 (M.g p.1 p'.1) * (res k2 (N.g p.2 p'.2))⁻¹ := rfl
  exact (congrArg (fun z => gU y hy (pullU a ((LB.div M N).U p ⊓ (LB.div M N).U p') z)) e).trans
    (((congrArg (gU y hy) (map_mul (pullU a ((LB.div M N).U p ⊓ (LB.div M N).U p')) _ _)).trans (map_mul (gU y hy) _ _)).trans
      (congrArg₂ (· * ·) (gU_pullU_res a k1 (M.g p.1 p'.1) y hy h1)
        ((congrArg (gU y hy) (map_inv (pullU a ((LB.div M N).U p ⊓ (LB.div M N).U p')) _)).trans ((map_inv (gU y hy) _).trans
          (congrArg (·⁻¹) (gU_pullU_res a k2 (N.g p.2 p'.2) y hy h2))))))

theorem gen_div_pull (L : LB X) (sG : X ⟶ X) (φ₂ : Y ⟶ X) (sA : Y ⟶ Y) (h : sA ≫ φ₂ = φ₂ ≫ sG)
    (hw : ∃ t : LB.Gen ((LB.div (L.pull sG) L).pull φ₂), t.IsGen) :
    ∃ t : LB.Gen (LB.div ((L.pull φ₂).pull sA) (L.pull φ₂)), t.IsGen := by
  have hU : ∀ p : (LB.div ((L.pull φ₂).pull sA) (L.pull φ₂)).ι,
      (LB.div ((L.pull φ₂).pull sA) (L.pull φ₂)).U p ≤
        ((LB.div (L.pull sG) L).pull φ₂).U (fun _ => ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit)) := by
    intro p y hy
    have hy1 := (mem_pull_pull_lemma_2 L φ₂ sA p.1 y).1 hy.1
    have hy2 := (mem_wchart_pu L φ₂ p.2 y).1 hy.2
    refine (mem_wchart_pu (LB.div (L.pull sG) L) φ₂ (fun _ => ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit)) y).2 ⟨?_, hy2⟩
    refine (mem_wchart_pu L sG (fun _ => p.1 PUnit.unit PUnit.unit) (φ₂.base y)).2 ?_
    exact (congrArg (· ∈ L.U (p.1 PUnit.unit PUnit.unit)) (base_eq h y)).mp hy1
  refine exists_gen_transfer (L := (LB.div (L.pull sG) L).pull φ₂)
    (L' := LB.div ((L.pull φ₂).pull sA) (L.pull φ₂))
    (fun p _ => ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit)) hU ?_ hw
  intro p p' y hy
  have hA : y ∈ (sA ≫ φ₂) ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) :=
    ⟨(mem_pull_pull_lemma_2 L φ₂ sA p.1 y).1 hy.1.1, (mem_pull_pull_lemma_2 L φ₂ sA p'.1 y).1 hy.2.1⟩
  have hB : y ∈ φ₂ ⁻¹ᵁ (L.U (p.2 PUnit.unit) ⊓ L.U (p'.2 PUnit.unit)) :=
    ⟨(mem_wchart_pu L φ₂ p.2 y).1 hy.1.2, (mem_wchart_pu L φ₂ p'.2 y).1 hy.2.2⟩
  have hS : y ∈ (φ₂ ≫ sG) ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) := by
    exact (congrArg (fun φ => y ∈ φ ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit))) h).mp hA
  have hF : y ∈ φ₂ ⁻¹ᵁ (sG ⁻¹ᵁ (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit))) := hS
  have hD : y ∈ φ₂ ⁻¹ᵁ ((L.pull sG).U (fun _ => p.1 PUnit.unit PUnit.unit) ⊓
      (L.pull sG).U (fun _ => p'.1 PUnit.unit PUnit.unit)) :=
    ⟨(mem_wchart_pu L sG (fun _ => p.1 PUnit.unit PUnit.unit) (φ₂.base y)).2 hF.1,
      (mem_wchart_pu L sG (fun _ => p'.1 PUnit.unit PUnit.unit) (φ₂.base y)).2 hF.2⟩
  have hC : y ∈ φ₂ ⁻¹ᵁ ((LB.div (L.pull sG) L).U ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit) ⊓
      (LB.div (L.pull sG) L).U ((fun _ => p'.1 PUnit.unit PUnit.unit), p'.2 PUnit.unit)) :=
    ⟨⟨hD.1, hB.1⟩, ⟨hD.2, hB.2⟩⟩
  have hL := (germ_div ((L.pull φ₂).pull sA) (L.pull φ₂) p p' y hy).trans
    (congrArg₂ (· * ·) ((germ_pull_pull L φ₂ sA p.1 p'.1 y ⟨hy.1.1, hy.2.1⟩ hA).trans
      (gU_pullU_congr h (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) (L.g (p.1 PUnit.unit PUnit.unit) (p'.1 PUnit.unit PUnit.unit)) y hA hS))
      (congrArg (·⁻¹) (germ_pull L φ₂ p.2 p'.2 y ⟨hy.1.2, hy.2.2⟩ hB)))
  have hc := ((congrArg (fun z => gU y hD (pullU φ₂ ((L.pull sG).U (fun _ => p.1 PUnit.unit PUnit.unit) ⊓ (L.pull sG).U (fun _ => p'.1 PUnit.unit PUnit.unit)) z))
      (pull_g_eq L sG (fun _ => p.1 PUnit.unit PUnit.unit) (fun _ => p'.1 PUnit.unit PUnit.unit))).trans
    (gU_pullU_res φ₂ (pull_inf_le L sG (fun _ => p.1 PUnit.unit PUnit.unit) (fun _ => p'.1 PUnit.unit PUnit.unit)) (pullU sG (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) (L.g (p.1 PUnit.unit PUnit.unit) (p'.1 PUnit.unit PUnit.unit))) y hD hF)).trans (gU_pullU_comp_lemma φ₂ sG (L.U (p.1 PUnit.unit PUnit.unit) ⊓ L.U (p'.1 PUnit.unit PUnit.unit)) (L.g (p.1 PUnit.unit PUnit.unit) (p'.1 PUnit.unit PUnit.unit)) y hS).symm
  have hR := (germ_pull (LB.div (L.pull sG) L) φ₂ (fun _ => ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit)) (fun _ => ((fun _ => p'.1 PUnit.unit PUnit.unit), p'.2 PUnit.unit)) y ⟨hU p hy.1, hU p' hy.2⟩ hC).trans
    ((germ_pullU_div (L.pull sG) L φ₂ ((fun _ => p.1 PUnit.unit PUnit.unit), p.2 PUnit.unit) ((fun _ => p'.1 PUnit.unit PUnit.unit), p'.2 PUnit.unit) y hC hD hB).trans (congrArg₂ (· * ·) hc rfl))
  exact hL.trans hR.symm

private theorem germ_cocycle_lemma_3 {L : LB X} (hL : L.IsLB) (i j k : L.ι) (y : X)
    (hij : y ∈ L.U i ⊓ L.U j) (hjk : y ∈ L.U j ⊓ L.U k) (hik : y ∈ L.U i ⊓ L.U k) :
    gU y hij (L.g i j) * gU y hjk (L.g j k) = gU y hik (L.g i k) := by
  have hm : y ∈ L.U i ⊓ L.U j ⊓ L.U k := ⟨⟨hij.1, hij.2⟩, hjk.2⟩
  have key := congrArg (gU y hm) (hL.cocycle i j k)
  simp only [map_mul, gU_res] at key
  exact key

private theorem germ_self_lemma_4 {L : LB X} (hL : L.IsLB) (i : L.ι) (y : X) (h : y ∈ L.U i ⊓ L.U i) :
    gU y h (L.g i i) = 1 := by
  have hi : y ∈ L.U i := h.1
  have key := congrArg (gU y hi) (hL.g_self i)
  simp only [map_one, gU_res] at key
  exact key

private theorem alg_lemma_8 {G : Type*} [CommGroup G] (ab aa' a'b' ab' b'b bb' : G)
    (h1 : aa' * a'b' = ab') (h2 : ab' * b'b = ab) (h3 : bb' * b'b = 1) :
    ab = aa' * bb'⁻¹ * a'b' := by
  rw [← h2, ← h1, inv_eq_of_mul_eq_one_right h3]
  exact mul_right_comm _ _ _

theorem gen_refl (L : LB X) (hL : L.IsLB) : ∃ t : LB.Gen (LB.div L L), t.IsGen := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p p' => ?_⟩
  apply unit_ext
  intro y hy
  have ha : y ∈ L.U p.1 := hy.1.1
  have hb : y ∈ L.U p.2 := hy.1.2
  have ha' : y ∈ L.U p'.1 := hy.2.1
  have hb' : y ∈ L.U p'.2 := hy.2.2
  have c1 := germ_cocycle_lemma_3 hL p.1 p'.1 p'.2 y ⟨ha, ha'⟩ ⟨ha', hb'⟩ ⟨ha, hb'⟩
  have c2 := germ_cocycle_lemma_3 hL p.1 p'.2 p.2 y ⟨ha, hb'⟩ ⟨hb', hb⟩ ⟨ha, hb⟩
  have c3 := (germ_cocycle_lemma_3 hL p.2 p'.2 p.2 y ⟨hb, hb'⟩ ⟨hb', hb⟩ ⟨hb, hb⟩).trans
    (germ_self_lemma_4 hL p.2 y ⟨hb, hb⟩)
  exact (gU_res inf_le_left y hy _).trans ((alg_lemma_8 _ _ _ _ _ _ c1 c2 c3).trans
    ((congrArg₂ (· * ·) (germ_div L L p p' y hy) (gU_res inf_le_right y hy _)).symm.trans
      (map_mul (gU y hy) _ _).symm))

end Transfer

end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
