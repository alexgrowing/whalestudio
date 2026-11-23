import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFinitePresentationOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeOfIsHeckeWit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.ValExt

open GlobalTheory.DrinLev.HT.HeckePt GlobalTheory.CechPic in

theorem isPIsog_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N c : ℕ) (S S' : Scheme.{0}) (σ : S ⟶ Sp R) (σ' : S' ⟶ Sp R) (f : S' ⟶ S) (o o' : Obj b N σ) (o₁ o₁' : Obj b N σ') (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsPIsog c o₁ o₁' ψ₁ ∧ m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ := by
  intro p _ D R _ b N c S S' σ σ' f o o' o₁ o₁' m m' ψ hψ
  obtain ⟨hk, hmon, hlin, heta, ⟨hP⟩, ψ', hmon', h₁, h₂⟩ := hψ
  haveI := hmon
  haveI := hmon'
  have e : m.φ ≫ ψ.left = (pullMor m.cart m'.cart ψ).left ≫ m'.φ := (pullMor_left m.cart m'.cart ψ).symm
  refine ⟨pullMor m.cart m'.cart ψ, ⟨hk, isMonHom_pullMor _ _ _, fun a => ?_, fun y => ?_, ⟨?_⟩,
    pullMor m'.cart m.cart ψ', isMonHom_pullMor _ _ _, pullMor_comp_eq_pow m.cart m'.cart ψ ψ' c h₁,
    pullMor_comp_eq_pow m'.cart m.cart ψ' ψ c h₂⟩, e⟩
  · apply ext_of_left m'.cart
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← e, ← Category.assoc, m.act, Category.assoc,
      ← Over.comp_left, hlin a, Over.comp_left, Category.assoc, m'.act, ← Category.assoc, ← Category.assoc, e]
  · apply ext_of_left m'.cart
    rw [Over.comp_left, Category.assoc, ← e, ← Category.assoc, m.eta, m'.eta, Category.assoc, ← Over.comp_left,
      ← heta y]
  · have hsq := PIsogExt.isSquare_square_compatible_homs m.sq m'.sq e
    have hcL : ∀ {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (h : (Hecke.lbPow L c).IsLB), cls _ h = c • cls L hL :=
      fun {X} L hL h => (cls_linComb (L := L) hL (fun _ => 𝟙 X) (fun _ => 1) h).trans (by simp [pull_id])
    have e1 := (cls_eq_iff o₁'.isLB (pull_isLB o'.isLB _)).2 m'.pol
    have e2 := (cls_eq_iff o₁.isLB (pull_isLB o.isLB _)).2 m.pol
    have e3 : cls (Hecke.lbPow o.P c) (LB.isLB_linComb o.isLB _ _) = cls (o'.P.pull (sq2 ψ)) (pull_isLB o'.isLB _) :=
      (cls_eq_iff _ _).2 hP
    refine (cls_eq_iff (LB.isLB_linComb o₁.isLB _ _) (pull_isLB o₁'.isLB _)).1 ?_
    refine (hcL o₁.P o₁.isLB _).trans ?_
    rw [e2, cls_pull o.isLB, ← map_nsmul, ← hcL o.P o.isLB (LB.isLB_linComb o.isLB _ _), e3,
      cls_pull o'.isLB, ← pull_comp, hsq, pull_comp, ← cls_pull o'.isLB _ (pull_isLB o'.isLB _), ← e1,
      ← cls_pull o₁'.isLB]

theorem of_ext (hext : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (v : Sp V ⟶ Sp R) (o : Obj b N v) (o₀ o₀' : Obj b N (spMap (algebraMap V (FractionRing V)) ≫ v)) (m : ObjMap o₀ o (spMap (algebraMap V (FractionRing V)))) (ψ₀ : o₀.A ⟶ o₀'.A), IsPIsog c o₀ o₀' ψ₀ → ∃ (o' : Obj b N v) (m' : ObjMap o₀' o' (spMap (algebraMap V (FractionRing V)))) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ m.φ ≫ ψ.left = ψ₀.left ≫ m'.φ) : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ s₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ := by
  intro p _ D R _ _ _ _ b N hN hNp _ r w j c _ _ _ _ _ M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst _ _ _ _ _ _ hψ _ V K _ _ _ _ _ _ y x hxy
  let eK : K →+* FractionRing V := (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).toRingEquiv.toRingHom
  have heK : eK.comp (algebraMap V K) = algebraMap V (FractionRing V) := by
    ext a; exact (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).commutes a
  let kF : Sp (FractionRing V) ⟶ Sp V := spMap (algebraMap V (FractionRing V))
  let x' : Sp (FractionRing V) ⟶ Y₀ := spMap eK ≫ x
  have hk : kF = spMap eK ≫ spMap (algebraMap V K) := by
    simp only [kF, spMap, ← heK, CommRingCat.ofHom_comp, Spec.map_comp]
  have hxy' : kF ≫ y = x' ≫ s₀ := by rw [hk, Category.assoc, hxy]; rfl
  obtain ⟨o, ⟨my⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp V) M.s y M.univ
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp (FractionRing V)) (y ≫ M.s) kF o
  have m1 : ObjMap oK M.univ (x' ≫ s₀) := hxy' ▸ GlobalTheory.UPel.HT.ObjMap.comp mK my
  obtain ⟨n₀, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m1 ms₀
  have key : ∀ σ : Sp (FractionRing V) ⟶ Sp R, x' ≫ (s₀ ≫ M.s) = σ → ∃ o' : Obj b N σ, Nonempty (ObjMap o' o₀' x') := by
    rintro σ rfl
    exact GlobalTheory.HTPull.exists_objMap_pull p D R b N Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) x' o₀'
  obtain ⟨oK', ⟨n₀'⟩⟩ := key (kF ≫ (y ≫ M.s)) (by rw [← Category.assoc, ← hxy', Category.assoc])
  obtain ⟨ψK, hψK, -⟩ := isPIsog_pull p D R b N c Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) (kF ≫ (y ≫ M.s)) x' o₀ o₀' oK oK' n₀ n₀' ψ₀ hψ
  obtain ⟨o', m', -, -, -⟩ := hext p D R b N hN hNp c V (y ≫ M.s) o oK oK' mK ψK hψK
  obtain ⟨z, ⟨hz, ⟨mz⟩⟩, -⟩ := M.rep (Sp V) (y ≫ M.s) o'
  refine ⟨z, ?_⟩
  obtain ⟨f, -, huniq⟩ := M.rep (Sp (FractionRing V)) (kF ≫ (y ≫ M.s)) oK'
  have e1 := huniq (kF ≫ z) ⟨by rw [Category.assoc, hz], ⟨GlobalTheory.UPel.HT.ObjMap.comp m' mz⟩⟩
  have e2 := huniq (x' ≫ t₀) ⟨by rw [Category.assoc, ← hst, ← Category.assoc, ← hxy', Category.assoc],
    ⟨GlobalTheory.UPel.HT.ObjMap.comp n₀' mt₀⟩⟩
  have e3 : spMap eK ≫ (spMap (algebraMap V K) ≫ z) = spMap eK ≫ (x ≫ t₀) := by
    rw [← Category.assoc, ← hk, e1, ← e2, Category.assoc]
  haveI : IsIso (spMap eK) := by
    let e := (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).toRingEquiv
    have h1 : IsIso (CommRingCat.ofHom eK) := (RingEquiv.toCommRingCatIso e).isIso_hom
    exact inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom eK)))
  exact (cancel_epi (spMap eK)).1 e3

end GlobalTheory.UPel.HT.ES.ValExt
