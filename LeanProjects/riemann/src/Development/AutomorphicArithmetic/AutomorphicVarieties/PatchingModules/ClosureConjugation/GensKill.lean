import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PhiFg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.PairMf
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.StarBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.PairKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GKillsTr

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.gens_kill :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ z ∈ P.gens, u.D.Kills z ∧ G.frame.star O B n z ∈ P.gens := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P z hz
  haveI := IsCoef.complete (l := l) (O := O)
  haveI := IsCoef.finite (l := l) (O := O)
  haveI := IsCoef.char (l := l) (O := O)
  have hn : 1 ≤ n := x.a_pos.trans x.a_le
  have hPhi : PhiCond G.frame.G₀ l := phi_fg G.frame P.fg
  obtain ⟨-, hks, -, hoEl, hIp⟩ := pair_kills r u hPhi hn
  obtain ⟨hfin, -, e, χ, hχ, hmf⟩ := pair_mf u hPhi
  haveI := hfin
  haveI := IsCO.complete (O := O) (R := B)
  haveI : CompactSpace G.frame.G₀ := by
    haveI := G.frame.cpt
    show CompactSpace G.frame.η.ker
    exact isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ G.frame.η_open).isCompact
  obtain ⟨hss, -, -, -, h1, hsub, -⟩ := star_basic G.frame n O B
  have htr : ∀ y, u.D.Kills y ↔ ∀ g, u.D.tr (MonoidAlgebra.single g 1 * y) = 0 :=
    g_kills_tr u.D χ u.cont hχ hmf hn
  unfold OoPt.gens pairGens qGens at hz ⊢
  simp only [Set.mem_union, Set.mem_setOf_eq] at hz ⊢
  rcases hz with ((⟨v, g, rfl | rfl⟩ | ⟨w, g, hg, rfl | rfl⟩) | (⟨j, rfl | rfl⟩ | ⟨j, i, rfl | rfl⟩))
  · exact ⟨hoEl v g, Or.inl (Or.inl ⟨v, g, Or.inr rfl⟩)⟩
  · refine ⟨hks _ (hoEl v g), Or.inl (Or.inl ⟨v, g, Or.inl ?_⟩)⟩
    rw [hss]
  · exact ⟨hIp w g hg, Or.inl (Or.inr ⟨w, g, hg, Or.inr (by rw [hsub, h1])⟩)⟩
  · have hk := hks _ (hIp w g hg)
    rw [hsub, h1] at hk
    refine ⟨hk, Or.inl (Or.inr ⟨w, g, hg, Or.inl ?_⟩)⟩
    rw [hsub, hss, h1]
  · have hk := (htr _).2 (P.q1 j)
    exact ⟨hk, Or.inr (Or.inl ⟨j, Or.inr rfl⟩)⟩
  · have hk := hks _ ((htr _).2 (P.q1 j))
    refine ⟨hk, Or.inr (Or.inl ⟨j, Or.inl ?_⟩)⟩
    rw [hss]
  · have hk := (htr _).2 (P.q2 j i)
    exact ⟨hk, Or.inr (Or.inr ⟨j, i, Or.inr rfl⟩)⟩
  · have hk := hks _ ((htr _).2 (P.q2 j i))
    refine ⟨hk, Or.inr (Or.inr ⟨j, i, Or.inl ?_⟩)⟩
    rw [hss]
