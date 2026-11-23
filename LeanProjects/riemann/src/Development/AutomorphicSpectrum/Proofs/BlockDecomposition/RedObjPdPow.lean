import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedFil

theorem exists_lift {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    {δ : DividedPowers J} {δ' : DividedPowers J'} {f : B →+* B'} (hf : IsDPMorphism δ δ' f)
    (hJ : J' = J.map f) (hs : Function.Surjective f) (l : List (ℕ × B')) (hl : ∀ q ∈ l, q.2 ∈ J') :
    ∃ l' : List (ℕ × B), (∀ q ∈ l', q.2 ∈ J) ∧ l'.map Prod.fst = l.map Prod.fst ∧
      (l.map fun q => δ'.dpow q.1 q.2).prod = f (l'.map fun q => δ.dpow q.1 q.2).prod := by
  induction l with
  | nil => exact ⟨[], by simp, rfl, by simp⟩
  | cons q l ih =>
    obtain ⟨l', h1, h2, h3⟩ := ih fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have hq := hl q List.mem_cons_self
    rw [hJ] at hq
    obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective f hs).1 hq
    refine ⟨(q.1, y) :: l', ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      exacts [hy, h1 p hp]
    · simp [h2]
    · simp only [List.map_cons, List.prod_cons, map_mul, h3, ← e]
      rw [hf.2 y hy]

theorem dividedPowerFiltration_le_map {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    {δ : DividedPowers J} {δ' : DividedPowers J'} {f : B →+* B'} (hf : IsDPMorphism δ δ' f)
    (hJ : J' = J.map f) (hs : Function.Surjective f) (r : ℕ) : pdP δ' r ≤ (pdP δ r).map f := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hr, rfl⟩
  obtain ⟨l', h1, h2, h3⟩ := exists_lift hf hJ hs l hl
  rw [h3]
  exact Ideal.mem_map_of_mem f (Ideal.subset_span ⟨l', h1, by rwa [h2], rfl⟩)

section
variable {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ]
  {I : Ideal A} {γ : DividedPowers I} {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  (d : RedIn δ κ γ l n) {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {s : ℕ}

theorem redObj_pdPow (T : Thick (nlFun γ 0 X q (κA O I))) (h : TF l s T) (r : ℕ) :
    (redObj T d h).pdPow r ≤ (T.pdPow r).map (Ideal.Quotient.mk (lnT T l n)) :=
  dividedPowerFiltration_le_map (redδ_dp T h n) rfl Ideal.Quotient.mk_surjective r
end

def toSomeP {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : ℤ) (c : b.R) (j : ℕ) :
    HM Q none c j →ₗ[b.R] HM Q (some r) c j :=
  (sqLe (a := IdF.top _) (a' := IdF.top _) (b := stdI Q none c) (b' := stdI Q (some r) c)
    (fun _ => le_rfl) (fun T => sup_le_sup_right (bot_le : (⊥ : Ideal _) ≤ _) _)).pull j

end GlobalTheory.CompanionTheory.RedFil

namespace GlobalTheory.CompanionTheory.RedFil

section
variable {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ]
  {I : Ideal A} {γ : DividedPowers I} {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  (d : RedIn δ κ γ l n) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ)
  (𝒱 : Set X.Opens) (c : Λ →+* R) (lam : Λ →+* A)
  (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))

theorem val_zero (r : ℕ) (T : (TS γ q l s 𝒱).FullSubcategory) (v : ((redG q s d 𝒱).obj T).B)
    (hv : v ∈ ((redG q s d 𝒱).obj T).pdPow r) :
    (sqLe (a := IdF.top _) (a' := IdF.top _) (b := stdI (TS γ q l s 𝒱) none ((l : A) ^ n))
      (b' := stdI (TS γ q l s 𝒱) (some (r : ℤ)) ((l : A) ^ n)) (fun _ => le_rfl)
      (fun T => sup_le_sup_right (bot_le : (⊥ : Ideal _) ≤ _) _)).τ T
      ((redMor q s d 𝒱 c lam hc none).τ T v) = 0 := by
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
    (redObj_pdPow d T.obj T.property.1 r hv)
  refine Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left ?_))
  change y ∈ T.obj.pdPow (r : ℤ).toNat
  simpa using hy

theorem red_kills (r j : ℕ) : ∀ x ∈ (B.pdS (nlFun δ l X q κ) c r).img j,
    toSomeP (TS γ q l s 𝒱) (r : ℤ) ((l : A) ^ n) j ((redMor q s d 𝒱 c lam hc none).pull j x) = 0 := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 y
  let S := B.pdS (nlFun δ l X q κ) c r
  let m := redMor q s d 𝒱 c lam hc none
  let t := sqLe (a := IdF.top _) (a' := IdF.top _) (b := stdI (TS γ q l s 𝒱) none ((l : A) ^ n))
      (b' := stdI (TS γ q l s 𝒱) (some (r : ℤ)) ((l : A) ^ n)) (fun _ => le_rfl)
      (fun T => sup_le_sup_right (bot_le : (⊥ : Ideal _) ≤ _) _)
  have h1 : CH.d _ j (S.inc.pullC j a) = 0 := by
    rw [S.inc.d_pullC]
    exact (congrArg _ ha).trans (map_zero _)
  have h2 : CH.d _ j (m.pullC j (S.inc.pullC j a)) = 0 := by
    rw [m.d_pullC, h1, map_zero]
  have h3 : CH.d _ j (t.pullC j (m.pullC j (S.inc.pullC j a))) = 0 := by
    rw [t.d_pullC, h2, map_zero]
  have e1 : S.inc.pull j ((CH.cx _).cls a ha) = (CH.cx _).cls (S.inc.pullC j a) h1 :=
    CrystallineSemistableComparison.P.mapH_cls S.inc.hom j a ha h1
  have e2 : m.pull j ((CH.cx _).cls (S.inc.pullC j a) h1) = (CH.cx _).cls (m.pullC j (S.inc.pullC j a)) h2 :=
    CrystallineSemistableComparison.P.mapH_cls m.hom j _ h1 h2
  have e3 : t.pull j ((CH.cx _).cls (m.pullC j (S.inc.pullC j a)) h2) =
      (CH.cx _).cls (t.pullC j (m.pullC j (S.inc.pullC j a))) h3 :=
    CrystallineSemistableComparison.P.mapH_cls t.hom j _ h2 h3
  have e4 : t.pullC j (m.pullC j (S.inc.pullC j a)) = 0 := by
    funext σ
    exact val_zero d q s 𝒱 c lam hc r _ _ (a (((σ ⋙ t.G) ⋙ m.G) ⋙ S.inc.G)).2
  change t.pull j (m.pull j (S.inc.pull j _)) = 0
  rw [e1, e2, e3]
  exact ((CrystallineSemistableComparison.P.cls_surj _ j).2.1 _ h3).2 (by rw [e4]; exact Submodule.zero_mem _)
end

end GlobalTheory.CompanionTheory.RedFil
