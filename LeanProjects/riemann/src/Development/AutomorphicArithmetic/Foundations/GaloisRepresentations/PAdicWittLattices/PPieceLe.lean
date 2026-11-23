import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem unit_sp (l : ℕ) (Ω : Type) [Field Ω] (h : (l : Ω) ≠ 0) : IsUnit (l : Γ(sp Ω, ⊤)) := by
  have hu : IsUnit ((l : Ω)) := h.isUnit
  have := hu.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  simpa using this

private theorem bc_apply {R : Type} [CommRing R] (L : Type) [CommRing L] [Algebra R L] {M N P : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (y : L ⊗[R] M) :
    (g ∘ₗ f).baseChange L y = g.baseChange L (f.baseChange L y) := by
  rw [LinearMap.baseChange_comp]; rfl

private theorem fEt_iso {Y Z : Scheme.{0}} (f : Y ⟶ Z) [IsIso f] : FEt f 1 := by
  refine ⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨x ≫ inv f, by simp⟩⟩⟩
  rw [← cancel_mono f, a.2, b.2]

theorem UpperTheory.Gal.G3.pPieceLe :
    EtGood → BcGood.{1} → ExtGood.{1} → (∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{1} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L)) → HopSpec → CoverInv.{1} → PieceLe := by
  intro hEt hBc hExt hExtTr hHop hCov l _ k L O _ _ _ _ _ hl H θ C hC Ω _ _
  have hlΩ : ((l : ℕ) : Ω) ≠ 0 := by
    intro h0
    apply hl
    have : algebraMap k Ω (l : k) = 0 := by simpa using h0
    exact (algebraMap k Ω).injective (by simpa using this)
  have hT0 : (etG l k Ω).Good := hBc _ _ (hEt l _ (unit_sp l Ω hlΩ))
  have hT : ((etG l k Ω).ext L).Good := hExt _ L hT0
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[l] L).injective
  obtain ⟨hinj, hsurj⟩ := hCov C hC ((etG l k Ω).ext L) hT
  refine ⟨hinj, fun y hy => hsurj y ?_⟩
  intro g hiso hθ
  haveI := hiso
  obtain ⟨tr0, htr0⟩ := hT0.tr H.q (H.s g ≫ H.q) (H.s g) rfl
  refine ⟨tr0.baseChange L, hExtTr _ L H.q (H.s g ≫ H.q) (H.s g) tr0 htr0, ?_⟩
  have hop_eq := (hHop l hl H Ω g 1 (fEt_iso (H.s g))).2 tr0 htr0
  have hy' : y ∈ Module.End.eigenspace ((hop l H Ω g).baseChange L) (θ g) :=
    (Submodule.mem_iInf _).1 hy g
  rw [Module.End.mem_eigenspace_iff, hθ, one_smul, hop_eq] at hy'
  change tr0.baseChange L (((etG l k Ω).pull (H.t g) _).baseChange L y) = y
  exact (bc_apply L _ _ y).symm.trans hy'
