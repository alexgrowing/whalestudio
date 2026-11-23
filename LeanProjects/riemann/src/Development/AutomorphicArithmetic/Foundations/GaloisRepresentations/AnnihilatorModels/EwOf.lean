import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.ew_of :
    WModEx → RankN → LineC → SecEquiv → KerRead → RedPts → CountIn → PulledEx → CaseE → CaseW → EW := by
  intro hW hRank hLine hSec hKR hRed hCI hPull hE hCW
  intro p _ D O _ _ _ _ f b N r w _ hS M T V _ _ _ _ _ hp x hcl hord φ hφ
  obtain ⟨W⟩ := hW p D O b N M.X M.s M.univ w (Over.mk x)
  obtain ⟨hfin, hrank⟩ := hRank p D O f b N r w hS M V hp x W
  obtain ⟨C, hC1, hC⟩ := hLine p D O f b N r w hS M V hp x hord W
  have hsec := fun j : Fin (D.n + 1) =>
    hSec p D O f b N r w hS M j (Nat.lt_succ_iff.mp j.2) (T j) V hp x W
  choose e he using hsec
  haveI : CharP (IsLocalRing.ResidueField V) p := hord.1
  obtain ⟨β, hβ⟩ : ∃ β : O →+* IsLocalRing.ResidueField V, (resPt V ≫ x) ≫ M.s = spMap β :=
    ⟨(Spec.preimage ((resPt V ≫ x) ≫ M.s)).hom, (Spec.map_preimage _).symm⟩
  have hker : ∀ a ∈ IsLocalRing.maximalIdeal O, β a = 0 := by
    intro a ha
    have h1 : (spMap β) (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint O := by
      rw [← hβ]
      have : (resPt V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) = IsLocalRing.closedPoint V :=
        IsLocalRing.comap_closedPoint (IsLocalRing.residue V)
      change M.s (x ((resPt V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)))) = _
      rw [this, hcl]
    have h2 : a ∈ ((spMap β) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))).asIdeal := by
      rw [h1]; exact ha
    have h3 : β a ∈ IsLocalRing.maximalIdeal (IsLocalRing.ResidueField V) := h2
    simpa [IsLocalRing.maximalIdeal_eq_bot] using h3
  obtain ⟨o₁, ⟨m₁⟩⟩ : ∃ o₁ : Obj b N (spMap β), Nonempty (ObjMap o₁ M.univ (resPt V ≫ x)) := by
    rw [← hβ]
    exact GlobalTheory.T.exists_harrisTaylorObject_pullback p D O b N M.X (Sp (IsLocalRing.ResidueField V)) M.s (resPt V ≫ x) M.univ
  have hinj : ∀ a a' : 𝟙_ (Over (Sp (IsLocalRing.ResidueField V))) ⟶ o₁.A,
      a.left ≫ m₁.φ = a'.left ≫ m₁.φ → a = a' := by
    intro a a' h
    apply Over.OverMorphism.ext
    apply m₁.cart.1.hom_ext h
    rw [Over.w a, Over.w a']
  have hlift : ∀ q : Sp (IsLocalRing.ResidueField V) ⟶ M.univ.A.left, q ≫ M.univ.A.hom = resPt V ≫ x →
      ∃ a : 𝟙_ (Over (Sp (IsLocalRing.ResidueField V))) ⟶ o₁.A, a.left ≫ m₁.φ = q := by
    intro q hq
    refine ⟨Over.homMk (m₁.cart.1.lift q (𝟙 _) (by simpa using hq)) ?_, ?_⟩
    · simp
    · simp
  let ρ : W.H → (Sp (IsLocalRing.ResidueField V) ⟶ M.univ.A.left) := fun h => resPt V ≫ (W.pt h).left
  have hρ : ∀ a a', ρ a = ρ a' ↔ a - a' ∈ C := hC
  have key : ∀ (j : ℕ) (Tj : TjD M r w j (p ^ (f * j))) (z : Sp V ⟶ Tj.Y) (_ : z ≫ Tj.s = x)
      (Dd : Submodule (𝓞 D.F ⧸ w) W.H) (_ : ∀ h, h ∈ Dd ↔ KerAt Tj z (W.pt h).left)
      (P : Pulled Tj m₁ (resPt V ≫ z)), RepAlg o₁.A (UKer r o₁ P.ψ) ((p ^ f) ^ j) ∧
        ∀ a : 𝟙_ (Over (Sp (IsLocalRing.ResidueField V))) ⟶ o₁.A,
          UKer r o₁ P.ψ _ a ↔ a.left ≫ m₁.φ ∈ ρ '' (Dd : Set W.H) := by
    intro j Tj z hz Dd hD P
    obtain ⟨h1, h2⟩ := hKR p D O f b N r w hS M j Tj V hp x z hz (spMap β) o₁ m₁ P
    refine ⟨h1, fun a => (h2 a).trans ⟨?_, ?_⟩⟩
    · rintro ⟨g, hg, hk, ha⟩
      obtain ⟨h, rfl⟩ := (W.range g).2 hg
      exact ⟨h, (hD h).2 hk, ha.symm⟩
    · rintro ⟨h, hh, ha⟩
      exact ⟨W.pt h, (W.range _).1 ⟨h, rfl⟩, (hD h).1 hh, ha.symm⟩
  have hcard : ∀ (Dd : Submodule (𝓞 D.F ⧸ w) W.H)
      (U : (𝟙_ (Over (Sp (IsLocalRing.ResidueField V))) ⟶ o₁.A) → Prop),
      (∀ a, U a ↔ a.left ≫ m₁.φ ∈ ρ '' (Dd : Set W.H)) →
      Nat.card {a // U a} = Nat.card (ρ '' (Dd : Set W.H)) := by
    intro Dd U hU
    refine Nat.card_eq_of_bijective
      (fun a : {a // U a} => (⟨a.1.left ≫ m₁.φ, (hU _).1 a.2⟩ : ρ '' (Dd : Set W.H))) ⟨?_, ?_⟩
    · intro a a' h
      exact Subtype.ext (hinj _ _ (congrArg Subtype.val h))
    · rintro ⟨q, h, hh, rfl⟩
      obtain ⟨a, ha⟩ := hlift (ρ h) (by
        have := Over.w (W.pt h)
        simp only [ρ, Category.assoc]
        rw [this]
        rfl)
      exact ⟨⟨a, (hU a).2 (ha ▸ ⟨h, hh, rfl⟩)⟩, Subtype.ext ha⟩
  have hk : Nat.card (𝓞 D.F ⧸ w) = p ^ f := by
    rw [← hS.norm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.F ⧸ w) :=
    Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hcnt : ∀ (j : ℕ) (Dd : Submodule (𝓞 D.F ⧸ w) W.H), Module.finrank (𝓞 D.F ⧸ w) Dd = j → ¬ C ≤ Dd →
      Nat.card (ρ '' (Dd : Set W.H)) = (p ^ f) ^ j := by
    intro j Dd hj hn
    rw [(hRed _ _ _ C ρ hρ Dd).1, hk, ← (hCI _ _ C hC1).2.2 Dd hn, hj]
  have hiff : ∀ (Dd Dd' : Submodule (𝓞 D.F ⧸ w) W.H)
      (U U' : (𝟙_ (Over (Sp (IsLocalRing.ResidueField V))) ⟶ o₁.A) → Prop),
      (∀ a, U a ↔ a.left ≫ m₁.φ ∈ ρ '' (Dd : Set W.H)) →
      (∀ a, U' a ↔ a.left ≫ m₁.φ ∈ ρ '' (Dd' : Set W.H)) → Dd.map C.mkQ = Dd'.map C.mkQ →
      ∀ a, U a ↔ U' a := by
    intro Dd Dd' U U' hU hU' hm a
    rw [hU, hU', (hRed _ _ _ C ρ hρ Dd).2 Dd' hm]
  have hy : ∀ (j : Fin (D.n + 1)) (z : {z : Sp V ⟶ (T j).Y // z ≫ (T j).s = x}),
      (resPt V ≫ z.1) ≫ (T j).s = resPt V ≫ x := by
    intro j z
    rw [Category.assoc, z.2]
  have hP : ∀ (j : Fin (D.n + 1)) (z : {z : Sp V ⟶ (T j).Y // z ≫ (T j).s = x}),
      Nonempty (Pulled (T j) m₁ (resPt V ≫ z.1)) := fun j z =>
    hPull p D O b N hS.three hS.cop M r w j _ (T j) _ (resPt V ≫ x) (spMap β) hβ o₁ m₁ _ (hy j z)
  refine ⟨W.H, inferInstance, inferInstance, hfin, C, e, hrank, hC1, ?_, ?_⟩
  · intro j z z' hn hn' hm
    obtain ⟨P⟩ := hP j z
    obtain ⟨P'⟩ := hP j z'
    obtain ⟨hr, hi⟩ := key j (T j) z.1 z.2 (e j z).1 (he j z) P
    obtain ⟨hr', hi'⟩ := key j (T j) z'.1 z'.2 (e j z').1 (he j z') P'
    have := hE p D O f b N r w hS M j _ (T j) _ (resPt V ≫ x) (spMap β) hβ o₁ m₁ _ _ (hy j z) (hy j z')
      P P' _ hr hr' ((hcard _ _ hi).trans (hcnt j _ (e j z).2 hn)) (hiff _ _ _ _ hi hi' hm)
    exact ⟨by simpa only [Category.assoc] using this.1, this.2⟩
  · intro j j' z z' hjj hin hn' hm
    obtain ⟨P⟩ := hP j z
    obtain ⟨P'⟩ := hP j' z'
    obtain ⟨hr, hi⟩ := key j (T j) z.1 z.2 (e j z).1 (he j z) P
    obtain ⟨hr', hi'⟩ := key j' (T j') z'.1 z'.2 (e j' z').1 (he j' z') P'
    have := hCW p D O f b N r w hS M j' j hjj (T j) (T j') _ φ hφ (resPt V ≫ x) β hβ hker o₁ m₁ _ _
      (hy j z) (hy j' z') P P' hr hr' ((hcard _ _ hi').trans (hcnt j' _ (e j' z').2 hn'))
      (hiff _ _ _ _ hi hi' hm)
    exact ⟨by simpa only [Category.assoc] using this.1, this.2⟩
