import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtMulTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionRegularFunctionsGoodPrimes
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
open GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.WholeFlag
open IsDedekindDomain GlobalTheory.WholeFlag.Glue GlobalTheory.WholeFlag.GlueProof
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WholeFlag.GlueProof.Covering

theorem main : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ) (V : Cover Y) (W : Y.X.Opens) {ι : Type} (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn) (L : Fin g → LB V.X) (m : ℕ) (r : ∀ i, ((L i).pull V.j).ι → V.G.functionFieldˣ), Hyp A p V W U H J d T L m r → ∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ q : Idx ι L, x ∈ chartOpen V U H L m r q := by
  intro F _ _ Y C g A p V W ι U H J d T L m r hyp x hx
  obtain ⟨hp, hg, -, hW, hm, hUc, hLc, hT, hGd, hr, hnorm, hreg, htest⟩ := hyp
  obtain ⟨a, ha⟩ := hUc x hx
  choose jj hjj using fun i => hLc i x hx
  let O : V.X.Opens := ⟨(U a : Set V.X) ∩ ⋂ i, ((L i).U (jj i) : Set V.X),
    (U a).isOpen.inter (isOpen_iInter_of_finite fun i => ((L i).U _).isOpen)⟩
  have hOU : O ≤ U a := fun y hy => hy.1
  have hOL : ∀ i, O ≤ (L i).U (jj i) := fun i y hy => Set.mem_iInter.1 hy.2 i
  have hxO : x ∈ O := ⟨ha, Set.mem_iInter.2 hjj⟩
  have hmem : ∀ (z : V.G), V.j z ∈ O → ∀ i, z ∈ ((L i).pull V.j).U (fun _ => jj i) := by
    intro z hz i
    have := hOL i hz
    simpa [LB.pull, LB.LinComb, LB.wchart] using this
  have key : ∀ (k : ℕ) (hk : k ≤ g), ∃ σ : Fin k → Fin (g + g),
      UnitAt x ((toG V).symm (nmin V (H a) (frames r jj) m k hk σ)) := by
    intro k hk
    refine GlobalTheory.Mean4O.Cover.MaxUnit.main F Y V p hp W hW O
      (fun σ : Fin k → Fin (g + g) => (toG V).symm (nmin V (H a) (frames r jj) m k hk σ)) ?_ ?_ x hxO hx
    · intro σ z hz
      refine (regAt_symm V).2 (unitAt_minor_of_nmin V (H a) (frames r jj) m hm k hk σ (T (V.π z)) (d (V.π z))
        (fun i => genAt (A i).D (V.π z)) (hT _).1 (hT _).2 (hreg a z (hOU hz)) (fun i => V.unitAt_φ (hGd i _))
        (fun i => hr i _ z (hmem z hz i))).1
    · intro v hv e y hy z yt hzy hc hO
      obtain ⟨ν, hν, hlg, hall⟩ := htest v hv e y hy z yt hzy hc
      have hUa : ⊤ ≤ yt ⁻¹ᵁ U a := fun q hq => hOU (hO hq)
      obtain ⟨hle, hex, -, -⟩ := hall a hUa
      have hν0 : ν 0 = 1 := by
        obtain ⟨σ, hσ⟩ := hex 0 (Nat.zero_le g)
        rw [← hσ]
        simp [minorAt]
      have hb : below y.1 = V.π (below z) := by rw [← hzy]; rfl
      have hzO : V.j (below z) ∈ O := by
        have h1 : below (z ≫ V.j) ∈ O := by
          rw [← hc]
          exact hO (x := spMap e.O.subtype _) trivial
        exact h1
      have hw : ∀ σ : Fin k → Fin (g + g),
          e.w (valAt (z ≫ V.j) ((toG V).symm (nmin V (H a) (frames r jj) m k hk σ))) =
            (e.w (minorAt (valMat V (H a) (T (below y.1)) z) k hk σ) / ν k) ^ m := by
        intro σ
        rw [valAt_symm, div_pow]
        refine w_nmin V e z (H a) (frames r jj) m k hk σ (T (below y.1)) (d (below y.1))
          (fun i => genAt (A i).D (below y.1)) (hT _).1 (hT _).2 ?_ ?_ ?_ ν hν hν0 (fun i => (A i).lg v e y) ?_ ?_
        · rw [hb]; exact hreg a _ (hOU hzO)
        · intro i; rw [hb]; exact hGd i _
        · intro i; rw [hb]; exact hr i _ _ (hmem _ hzO i)
        · intro i
          exact hnorm i v hv e y z yt (fun _ => jj i) hzy hc (fun q hq => hOL i (hO hq))
        · intro i; rw [hzy]; exact hlg i
      refine ⟨fun σ => ?_, ?_⟩
      · rw [hw]
        exact pow_le_one₀ (div_nonneg (e.w.nonneg _) (hν k hk).le) ((div_le_one (hν k hk)).2 (hle k hk σ))
      · obtain ⟨σ, hσ⟩ := hex k hk
        exact ⟨σ, by rw [hw, hσ, div_self (hν k hk).ne', one_pow]⟩
  choose σ hσ using key
  refine ⟨(a, fun k => if hk : k ≤ g then σ k hk else fun _ => ⟨0, by omega⟩, jj), ha, hjj, fun k hk => ?_⟩
  simp only [dif_pos hk]
  exact hσ k hk

end GlobalTheory.WholeFlag.GlueProof.Covering
