import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtension
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfPullDensePartOfPullSection
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.PIsogExt

theorem comp_pow_pt {S : Scheme.{0}} {T T' A : Over S} [GrpObj A] (f : T' ⟶ T) (g : T ⟶ A) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem pow_comp_of_isGrpPullback {Y₀ Y : Scheme.{0}} {i : Y₀ ⟶ Y} {A₀ : Over Y₀} {A : Over Y}
    [GrpObj A₀] [GrpObj A] {φ : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A i φ) (k : ℕ) (hk : 0 < k) :
    (𝟙 A₀ ^ k).left ≫ φ = φ ≫ (𝟙 A ^ k).left := by
  let φ₀ : Over.mk (A₀.hom ≫ i) ⟶ A := Over.homMk φ h.1.w
  have key : ∀ n : ℕ, (φ₀ ^ (n + 1)).left = (𝟙 A₀ ^ (n + 1)).left ≫ φ := by
    intro n
    induction n with
    | zero => rw [zero_add, pow_one, pow_one]; rfl
    | succ n ih =>
      rw [pow_succ φ₀, pow_succ (𝟙 A₀)]
      exact h.2 A₀ _ _ _ _ ih rfl
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [zero_add, ← key n]
  have : φ₀ ^ (n + 1) = φ₀ ≫ 𝟙 A ^ (n + 1) := by rw [comp_pow_pt, Category.comp_id]
  rw [this]; rfl

theorem isSquare_square_compatible_homs {Y₀ Y : Scheme.{0}} {A₀ A₀' : Over Y₀} {A A' : Over Y}
    [GrpObj A₀] [IsCommMonObj A₀] [GrpObj A₀'] [IsCommMonObj A₀'] [GrpObj A] [IsCommMonObj A]
    [GrpObj A'] [IsCommMonObj A'] {φ : A₀.left ⟶ A.left} {φ' : A₀'.left ⟶ A'.left}
    {φ₂ : (G2 A₀).left ⟶ (G2 A).left} {φ₂' : (G2 A₀').left ⟶ (G2 A').left}
    (h : IsSquare φ φ₂) (h' : IsSquare φ' φ₂') {ψ₀ : A₀ ⟶ A₀'} {ψ : A ⟶ A'}
    (e : φ ≫ ψ.left = ψ₀.left ≫ φ') : φ₂ ≫ sq2 ψ = sq2 ψ₀ ≫ φ₂' := by
  have f1 : ∀ {B B' : Over Y} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (χ : B ⟶ B'),
      sq2 χ ≫ (fst B' B').left = (fst B B).left ≫ χ.left := fun χ => by
    rw [sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  have f2 : ∀ {B B' : Over Y} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (χ : B ⟶ B'),
      sq2 χ ≫ (snd B' B').left = (snd B B).left ≫ χ.left := fun χ => by
    rw [sq2, ← Over.comp_left, lift_snd, Over.comp_left]
  have g1 : sq2 ψ₀ ≫ (fst A₀' A₀').left = (fst A₀ A₀).left ≫ ψ₀.left := by
    rw [sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  have g2 : sq2 ψ₀ ≫ (snd A₀' A₀').left = (snd A₀ A₀).left ≫ ψ₀.left := by
    rw [sq2, ← Over.comp_left, lift_snd, Over.comp_left]
  apply pullback.hom_ext
  · change _ ≫ (fst A' A').left = _ ≫ (fst A' A').left
    rw [Category.assoc, Category.assoc, f1, h'.1, ← Category.assoc, h.1, Category.assoc, e, reassoc_of% g1]
  · change _ ≫ (snd A' A').left = _ ≫ (snd A' A').left
    rw [Category.assoc, Category.assoc, f2, h'.2, ← Category.assoc, h.2, Category.assoc, e, reassoc_of% g2]

open GlobalTheory.CechPic in

theorem lbIso_extend {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {Y₀ Y : Scheme.{0}} [IsLocallyNoetherian Y] (hY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y) (i : Y₀ ⟶ Y) [IsOpenImmersion i]
    [IsDominant i] {σ₀ : Y₀ ⟶ Sp R} {σ : Y ⟶ Sp R} (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀)
    (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A) (ψ : o.A ⟶ o'.A) [IsMonHom ψ]
    (e : m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ) (c : ℕ) (h₀ : LBIso (Hecke.lbPow o₀.P c) (o₀'.P.pull (sq2 ψ₀))) :
    LBIso (Hecke.lbPow o.P c) (o'.P.pull (sq2 ψ)) := by
  haveI := GlobalTheory.IsNormalScheme.of_pred hY
  haveI := o.ab.smooth
  haveI := o.ab.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom o.A o.A
  haveI := GlobalTheory.geometricallyConnected_tensorObj_hom o.A o.A
  have hpb : IsPullback m.φ₂ (G2 o₀.A).hom (G2 o.A).hom i := GlobalTheory.SiegDesc.isPullback_of_isSquare m.cart.1 m.sq
  have hL : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
  have hM : (o'.P.pull (sq2 ψ)).IsLB := pull_isLB o'.isLB _
  have hcL : ∀ {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (h : (Hecke.lbPow L c).IsLB), cls _ h = c • cls L hL :=
    fun {X} L hL h => (cls_linComb (L := L) hL (fun _ => 𝟙 X) (fun _ => 1) h).trans (by simp [pull_id])
  let s : Y ⟶ (G2 o.A).left := (η[o.A] ≫ lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left
  have hs : s ≫ (G2 o.A).hom = 𝟙 Y := Over.w _
  have hss : s ≫ sq2 ψ = (η[o'.A] ≫ lift (1 : o'.A ⟶ o'.A) (𝟙 o'.A)).left := by
    rw [sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [Hom.one_def, IsMonHom.one_hom]
  have r0 : ∀ (A : Over Y) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (hP : P.IsLB),
      (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
      pull (η[A] ≫ lift (1 : A ⟶ A) (𝟙 A)).left (cls P hP) = 0 := by
    intro A _ _ P hP ht
    rw [Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _), (cls_eq_zero_iff _).2 ht, map_zero]
  have key := eq_zero_of_pull_densePart_of_pull_section (G2 o.A).hom i m.φ₂ (G2 o₀.A).hom i.denseRange hpb s hs
    (cls _ hM - cls _ hL) ?_ ?_
  · exact (cls_eq_iff hL hM).1 (sub_eq_zero.1 key).symm
  · have hsq := PIsogExt.isSquare_square_compatible_homs m.sq m'.sq e
    have e1 := (cls_eq_iff o₀'.isLB (pull_isLB o'.isLB _)).2 m'.pol
    have e2 := (cls_eq_iff o₀.isLB (pull_isLB o.isLB _)).2 m.pol
    have e3 : cls (Hecke.lbPow o₀.P c) (LB.isLB_linComb o₀.isLB _ _) = cls _ (pull_isLB o₀'.isLB (sq2 ψ₀)) :=
      (cls_eq_iff _ _).2 h₀
    rw [map_sub, sub_eq_zero, hcL (X := (G2 o.A).left) o.P o.isLB, map_nsmul, cls_pull o'.isLB, ← pull_comp, hsq, pull_comp,
      ← cls_pull o'.isLB _ (pull_isLB o'.isLB _), ← e1, ← cls_pull o₀'.isLB _ (pull_isLB o₀'.isLB _), ← e3]
    refine (hcL (X := (G2 o₀.A).left) o₀.P o₀.isLB _).trans ?_
    rw [e2, cls_pull o.isLB]
  · rw [map_sub, hcL (X := (G2 o.A).left) o.P o.isLB, map_nsmul, cls_pull o'.isLB, ← pull_comp, hss, r0 _ _ _ o'.rig₁, r0 _ _ _ o.rig₁,
      smul_zero, sub_zero]

theorem exists_isPIsog_extend : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ),
    3 ≤ N → N.Coprime p → ∀ (j c : ℕ), (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) →
    ∀ (Y₀ Y : Scheme.{0}) (i : Y₀ ⟶ Y) (σ₀ : Y₀ ⟶ Sp R) (σ : Y ⟶ Sp R), IsOpenImmersion i → IsDominant i →
    IsLocallyNoetherian Y → (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) →
    (∀ y : Y, IsDomain (Y.presheaf.stalk y)) →
    ∀ (o o' : Obj b N σ) (o₀ o₀' : Obj b N σ₀) (m : ObjMap o₀ o i) (m' : ObjMap o₀' o' i) (ψ₀ : o₀.A ⟶ o₀'.A),
    IsPIsog c o₀ o₀' ψ₀ → ∃ ψ : o.A ⟶ o'.A, IsPIsog c o o' ψ ∧ m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ := by
  intro p _ D R _ b N _ _ j c _ Y₀ Y i σ₀ σ _ _ _ hic hdom o o' o₀ o₀' m m' ψ₀ hψ₀
  have hY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := fun y => ⟨hdom y, hic y⟩
  haveI := GlobalTheory.IsNormalScheme.of_pred hY
  haveI : IsReduced Y := by
    haveI := hdom
    exact isReduced_of_isReduced_stalk Y
  have hcpos : 0 < c := hψ₀.pos
  obtain ⟨hk, hmon₀, hlin₀, heta₀, ⟨hP₀⟩, ψ₀', hmon₀', h₁, h₂⟩ := hψ₀
  haveI := hmon₀
  haveI := hmon₀'
  have hA := GlobalTheory.isSemiAbelian_of_isAbelianScheme o.A o.ab
  have hA' := GlobalTheory.isSemiAbelian_of_isAbelianScheme o'.A o'.ab
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.dense_openImmersion i
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian o.A hA
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian o'.A hA'
  obtain ⟨ψ, hψ⟩ := GlobalTheory.SemiAbDenseExt.exists_extension i i.denseRange o.A o'.A hA hA' o₀.A o₀'.A m.φ m'.φ
    m.cart m'.cart ψ₀ hmon₀
  obtain ⟨ψ', hψ'⟩ := GlobalTheory.SemiAbDenseExt.exists_extension i i.denseRange o'.A o.A hA' hA o₀'.A o₀.A m'.φ m.φ
    m'.cart m.cart ψ₀' hmon₀'
  haveI hψm : IsMonHom ψ := GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback m.cart m'.cart ψ₀ ψ hψ
  haveI hψm' : IsMonHom ψ' := GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback m'.cart m.cart ψ₀' ψ' hψ'
  have e : m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ := hψ.symm
  have e' : m'.φ ≫ ψ'.left = ψ₀'.left ≫ m.φ := hψ'.symm
  refine ⟨ψ, ⟨hk, hψm, fun c' => ?_, fun x => ?_, ⟨lbIso_extend hY i o o' o₀ o₀' m m' ψ₀ ψ e c hP₀⟩, ψ', hψm', ?_, ?_⟩, e⟩
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m.cart.1 ?_
    rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← m.act c', Category.assoc, e, ← Category.assoc,
      ← Over.comp_left, hlin₀ c', Over.comp_left, Category.assoc, m'.act c', ← Category.assoc, ← e, Category.assoc]
  · refine Over.OverMorphism.ext (GlobalTheory.ExtUnique.hom_ext_of_dominant o'.A.hom (by rw [Over.w, Over.w]) i ?_)
    have h1 := m'.eta x
    have h2 := m.eta x
    rw [heta₀ x, Over.comp_left, Category.assoc] at h1
    rw [← h1, ← e, Over.comp_left, ← Category.assoc, h2, Category.assoc]
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m.cart.1 ?_
    rw [Over.comp_left, ← Category.assoc, e, Category.assoc, e', ← Category.assoc, ← Over.comp_left, h₁,
      PIsogExt.pow_comp_of_isGrpPullback m.cart c hcpos]
  · refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m'.cart.1 ?_
    rw [Over.comp_left, ← Category.assoc, e', Category.assoc, e, ← Category.assoc, ← Over.comp_left, h₂,
      PIsogExt.pow_comp_of_isGrpPullback m'.cart c hcpos]

end GlobalTheory.UPel.HT.ES.PIsogExt
