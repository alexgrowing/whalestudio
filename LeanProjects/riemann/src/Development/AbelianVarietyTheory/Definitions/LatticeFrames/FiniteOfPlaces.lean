import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfinitelyManySplitPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatEqMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIncAMulMemIntAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPl.PlacesTest

variable {D : D7}

theorem exists_one_place (D : D7) (Z : Finset (Pl D)) : ∃ (v : Pl D) (p : SplitPt D (Fv D.host.F v)),
    v ∉ Z ∧ Places (fun _ : Unit => p) [()] (· = v) := by
  have h := ((GlobalTheory.FinPl.AlmostAll.latA_eq_latV D).and ((GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0).and
    (GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D D.host.xi0⁻¹))).and Z.eventually_cofinite_notMem
  obtain ⟨v, ⟨e, ε, he, hε, hs⟩, ⟨h1, h2, h3⟩, hZ⟩ :=
    ((Set.infinite_iff_frequently_cofinite.1 (infinite_splitIdem_places D)).and_eventually h).exists
  obtain ⟨p, -, hp⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v e ε he hε hs
  refine ⟨v, p, hZ, by simp, by simp, fun _ _ _ => rfl, fun x => by simp [hp], fun _ => ?_⟩
  unfold SplitPt.UnitAA
  rw [hp]
  exact ⟨fun a ha => ⟨h2 a ha, h3 a ha⟩, h1⟩

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

theorem finite_of_places {p : ι → SplitPt D k} {I : List ι} {P : Pl D → Prop} (h : Places p I P) : {x | P x}.Finite := by
  have : Finite ι := Set.finite_univ_iff.1 ((List.finite_toSet I).subset fun i _ => h.all i)
  exact (Set.finite_range fun i => (p i).v).subset fun x hx => by
    obtain ⟨i, rfl⟩ := (h.mem x).1 hx
    exact ⟨i, rfl⟩

theorem not_places_of_eq {p : ι → SplitPt D k} {I : List ι} {P : Pl D → Prop} {i j : ι} (hij : i ≠ j) (hv : (p i).v = (p j).v) :
    ¬ Places p I P := fun h => hij (h.inj hv)

theorem places_empty (p : Empty → SplitPt D k) : Places p [] fun _ => False :=
  ⟨List.nodup_nil, fun i => i.elim, fun i => i.elim, fun _ => ⟨False.elim, fun ⟨i, _⟩ => i.elim⟩, fun i => i.elim⟩

variable {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S} {LT : Lat T}

theorem reps_nil (Ψ : ι → Matrix n n' k → ℂ) (P : Pl D → Prop) : Reps ψ α β LS LT Ψ [] P (Finsupp.single 0 1) :=
  ⟨OffTest.combAt_single_zero P 1, fun f _ => OffTest.comb_single_zero ψ S T f⟩

theorem vac_zero (P : Pl D → Prop) : Vac ψ S T LS LT P 0 := by
  have h : ∀ u, heisO ψ S T u 0 = 0 := fun u => by funext w; simp [heisO]
  exact ⟨⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun u _ _ => h u⟩, continuous_const, fun _ _ _ _ _ => contDiff_const⟩,
    fun u _ => h _, fun _ _ u _ _ => h u⟩

theorem sb_of_reps {Ψ : ι → Matrix n n' k → ℂ} {i : ι} {I : List ι} {P : Pl D → Prop} {c : WO S T →₀ ℂ}
    (h : Reps ψ α β LS LT Ψ (i :: I) P c) : Ψ i ∈ SB (Matrix n n' k) ∧ IsSelfDualC S LS ∧ IsSelfDualC T LT := by
  obtain ⟨g, -, h1, h2, -, h3, -⟩ := h.2 0 (vac_zero P)
  exact ⟨h3, h1, h2⟩

end

theorem symplOH_kap {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (S : HSp D) (x y : WO S L'') :
    symplOH L S (kap τ S x) (kap τ S y) = symplOH S L'' x y := by
  have := GlobalTheory.LinkKappa.symplO_ofAdj L L'' S τ (-1) (by simpa using hτ) x y
  simp only [symplOH, kap, this]
  simp

theorem kap_add {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (x y : WO S L'') :
    kap τ S (x + y) = kap τ S x + kap τ S y := by
  simp only [kap, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj, Matrix.mul_add, adj_add, Matrix.add_mul, smul_add]

theorem lastBi_heis (ψ : AddChar (AF D.host.F) ℂ) {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram) (a : WO A S) (x : WO S X) (Ξ Φ₂) (u v) :
    heisO ψ A S a (fun u' => heisO ψ S X x (lastBi o o'' τ Ξ Φ₂ u') v) u =
      lastBi o o'' τ (heisO ψ V₀ S ((o.resS S).symm (a, kap τ S (o''.resT S x).2)) Ξ) (heisO ψ S T (o''.resT S x).1 Φ₂) u v := by
  simp only [heisO, lastBi, OrthDec.boxT, map_add, Prod.fst_add, Prod.snd_add, kap_add]
  rw [o.symplOH_resS, o''.symplOH_resT, ← map_add (o.resS S).symm]
  simp only [AddEquiv.apply_symm_apply, symplOH_kap τ hτ, AddChar.map_add_eq_mul, Prod.mk_add_mk]
  ring

theorem smallPair_zero {V₀ A L S T : HSp D} (o : OrthDec V₀ A L) (om₁ : Om V₀ S) (omT : Om S T) (vA : Vol A) (vS : Vol S)
    (vT : Vol T) (Ξ Φ₂ F) : smallPair o om₁ omT vA vS vT 0 Ξ Φ₂ F = 0 := by
  simp [smallPair, liftA]

theorem smallPair_eq_Q {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {B : BesLev D 0} (t : Last ψ T B) (o : OrthDec B.V B.A B.L)
    (ho : ∀ a, o.emb (a, 1) = embA B.d B.o a) (φ Φ₁ Φ₂ F) :
    smallPair o t.s.om t.om B.vA t.s.vW t.vT φ Φ₁ Φ₂ F = t.Q φ Φ₁ Φ₂ F := by
  have h0 : (o.resS t.J.W).symm (0, 0) = 0 := map_zero (o.resS t.J.W).symm
  simp only [smallPair, liftA, Last.Q, ho, h0]

end GlobalTheory.FinPl.PlacesTest

end
