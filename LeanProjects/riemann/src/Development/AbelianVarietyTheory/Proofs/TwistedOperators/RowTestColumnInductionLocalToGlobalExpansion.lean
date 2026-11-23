import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDoubleCosetPointsChainPlaceByPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsetPlaceVectorsAndStepsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPassPlaceModelsLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCombinationOperatorColumnProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnCombinationsComposeLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFiniteDatumLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnAtReadsPlacePartLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumEqSumSinglePlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumPlacesUniqueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumDatumTrivialCombinationLargeDepthStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

set_option maxHeartbeats 1000000 in

theorem columnInduction : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (ζ : locPl ch.G t → ℂ), (∀ w : locPl ch.G t, GlobalTheory.LocAsm.PlaceCl ch s t w (β w) (ζ w)) → ∀ (M : Vol ch.G) (hM : M.Is t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∀ (I : locPl ch.G t → Type) (S : ∀ w, Finset (I w)) (x : ∀ w, I w → ℂ) (d : ∀ w, I w → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : ∀ w, I w → Combs ch.G), (∀ w, ∀ i ∈ S w, ∀ j : Fin D.R.m, (d w i j).e = eL w ∧ IsCombOf ch.W (d w i j) ((c w i).1 j)) → (∀ w (y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))), (∀ j, IsHalf (eL w) (y j)) → ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 y) 0) → ∃ (J : Type) (SJ : Finset J) (xJ : J → ℂ) (dJ : J → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (cJ : J → ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), (∀ a ∈ SJ, ∀ j : Fin D.R.m, (dJ a j).e = e ∧ IsCombOf ch.W (dJ a j) (cJ a j)) ∧ (∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf e (u j)) → ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn (u j) = ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 u) 0) ∧ ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ u : ColPt ch.G, evT (conAt ch.W hM (fockD ch.W t fd P) (p * b)) 1 u 0 = (∏ w, ζ w) * ∑ a ∈ SJ, xJ a * evT (combC ch.W (cJ a, 0) (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
  refine big_mono (fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch h => ?_)
    (((GlobalTheory.T.rowTest_doubleCosetPoints_chain_place_by_place.and GlobalTheory.T.subset_place_vectors_and_steps).and (GlobalTheory.T.fockVectors_pass_placeModels_largeDepth.and GlobalTheory.T.exists_combinationOperator_columnProduct)).and ((GlobalTheory.T.columnCombinations_compose_largeDepth.and GlobalTheory.T.productFiniteDatum_largeDepth).and (GlobalTheory.T.columnAt_reads_placePart_largeDepth.and GlobalTheory.T.vacuumDatum_trivialCombination_largeDepth)))
  obtain ⟨⟨⟨hA, hB⟩, hC, hD⟩, ⟨hE, hF⟩, hG, hZ⟩ := h
  intro s t β ζ hζ M hM b b₀ hb hb₀ e he φ hφ fd hfd eL heL I S x d c hdc hexp
  obtain ⟨he_sum, hsub, hmul⟩ := GlobalTheory.T.isIdemSum_eq_sum_singlePlaces D e (locPl ch.G t) he eL heL
  obtain ⟨V, hV0, hVu, hVth, hVst⟩ := hB t e he φ hφ fd hfd eL heL
  have hpts := fun (p : Pts ch.G) (hp : IsRealPt p) => hA s t β b b₀ hb hb₀ eL heL p hp
  choose q hq0 hqu hqst using hpts
  choose Tc hTc using hD
  obtain ⟨fl, hfl⟩ : ∃ fl : locPl ch.G t → (∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) → ℂ,
      ∀ w y, fl w y = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1)
        (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w))
          ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 y) 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hexp' : ∀ w y, (∀ j, IsHalf (eL w) (y j)) → ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (y j) = fl w y :=
    fun w y hy => (hexp w y hy).trans (hfl w y).symm
  have hflG : ∀ (w' : locPl ch.G t) (e' : AE D), e' * eL w' = eL w' → ∀ u, fl w' (fun j => e' • u j) = fl w' u := by
    intro w' e' he' u
    rw [hfl, hfl, hG t w' (eL w') e' (heL w') he' u]

  have hcomb1 : ∀ (S' T' : HSp D) (f : WO S' T' → ℂ), comb ch.W.ψ S' T' (Finsupp.single 0 1) f = f := by
    intro S' T' f
    rw [GlobalTheory.DisjComb.comb_single]
    funext y
    simp [heisO, symplOH, symplO, hO]
  have hcombC1 : ∀ C : BiFam ch.G, combC ch.W ((fun _ => Finsupp.single 0 1), 0) C = C := by
    intro C
    funext j y z
    simp only [combC, biComb, hcomb1]

  have hidem : ∀ (S' : Finset (locPl ch.G t)), (∑ w ∈ S', eL w) * (∑ w ∈ S', eL w) = ∑ w ∈ S', eL w := by
    intro S'
    rw [hmul, Finset.inter_self]
  have hidem1 : ∀ w : locPl ch.G t, eL w * eL w = eL w := by
    intro w
    have h := hmul {w} {w}
    rw [Finset.inter_self, Finset.sum_singleton] at h
    exact h
  have hsubmul : ∀ (S' : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∈ S' → (∑ w ∈ S', eL w) * eL w = eL w := by
    intro S' w hw
    have h := hmul S' {w}
    rw [Finset.inter_singleton_of_mem hw, Finset.sum_singleton] at h
    exact h
  have hhalf : ∀ (a : AE D), a * a = a → ∀ {m n : ℕ} (y : Mx D m n), IsHalf a (a • y) := by
    intro a ha m n y i j
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ha]
  have key : ∀ S' : Finset (locPl ch.G t), ∃ (J : Type) (SJ : Finset J) (xJ : J → ℂ)
      (dJ : J → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j))
      (cJ : J → ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ),
      (∀ a ∈ SJ, ∀ j : Fin D.R.m, (dJ a j).P = S'.map (Function.Embedding.subtype _) ∧
        (dJ a j).e = ∑ w ∈ S', eL w ∧ IsCombOf ch.W (dJ a j) (cJ a j)) ∧
      (∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf (∑ w ∈ S', eL w) (u j)) →
        ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn (u j) = ∏ w ∈ S', fl w u) ∧
      ∀ (P : PolDown ch.G) (p : Pts ch.G) (hp : IsRealPt p) (u : ColPt ch.G),
        evT (conAt ch.W hM (fockD ch.W t (V S') P) (q p hp S')) 1 u 0 = (∏ w ∈ S', ζ w) * ∑ a ∈ SJ, xJ a *
          evT (combC ch.W (cJ a, 0) (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
    intro S'
    induction S' using Finset.induction_on with
    | empty =>
      refine ⟨Unit, {()}, fun _ => 1, fun _ j => FinDatum.vacuum ch.G t (.top t j), fun _ _ => Finsupp.single 0 1, ?_, ?_, ?_⟩
      · intro a _ j
        refine ⟨?_, ?_, hZ t j⟩
        · rw [Finset.map_empty]; rfl
        · rw [Finset.sum_empty]; rfl
      · intro u hu
        have h0 : ∀ j, u j = 0 := by
          intro j
          ext a b'
          have := hu j a b'
          rw [Finset.sum_empty, zero_mul] at this
          exact this.symm
        simp only [Finset.sum_singleton, Finset.prod_empty, one_mul]
        refine Finset.prod_eq_one fun j _ => ?_
        rw [h0 j]
        show halfInd (0 : AE D) _ 0 = 1
        unfold halfInd
        rw [if_pos ⟨zero_mem _, fun a b' => by simp⟩]
      · intro P p hp u
        simp only [hV0, hq0 p hp, Finset.prod_empty, Finset.sum_singleton, one_mul, hcombC1]
    | insert w S₀ hw ih =>
      obtain ⟨J, SJ, xJ, dJ, cJ, h1, h2, h3⟩ := ih
      have hPw : ∀ i ∈ S w, ∀ j : Fin D.R.m, (d w i j).P = {w.1} := by
        intro i hi j
        have h := (d w i j).e_is
        rw [(hdc w i hi j).1] at h
        exact GlobalTheory.T.isIdemSum_places_unique D _ _ _ h (heL w)
      have hsum : ∑ w' ∈ insert w S₀, eL w' = eL w + ∑ w' ∈ S₀, eL w' := Finset.sum_insert hw
      have hmap : (insert w S₀).map (Function.Embedding.subtype (· ∈ locPl ch.G t)) =
          {w.1} ∪ S₀.map (Function.Embedding.subtype (· ∈ locPl ch.G t)) := by
        rw [Finset.map_insert, Finset.insert_eq]; rfl
      have hs : IsIdemSum (eL w + ∑ w' ∈ S₀, eL w') ({w.1} ∪ S₀.map (Function.Embedding.subtype _)) := by
        have := hsub (insert w S₀)
        rwa [hsum, hmap] at this
      have hF' : ∀ (k : I w × J) (j : Fin D.R.m),
          ∃ (dd : FinDatum ch.G t (.top t j)) (cc : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), k.1 ∈ S w → k.2 ∈ SJ →
            dd.P = (d w k.1 j).P ∪ (dJ k.2 j).P ∧ dd.e = (d w k.1 j).e + (dJ k.2 j).e ∧ IsCombOf ch.W dd cc ∧
            (∀ y, IsHalf dd.e y → dd.fn y = (d w k.1 j).fn ((d w k.1 j).e • y) * (dJ k.2 j).fn ((dJ k.2 j).e • y)) ∧
            ∀ f, comb ch.W.ψ _ _ cc f = comb ch.W.ψ _ _ ((c w k.1).1 j) (comb ch.W.ψ _ _ (cJ k.2 j) f) := by
        intro k j
        by_cases hk : k.1 ∈ S w ∧ k.2 ∈ SJ
        · have hId : IsIdemSum ((d w k.1 j).e + (dJ k.2 j).e) ((d w k.1 j).P ∪ (dJ k.2 j).P) := by
            rw [(hdc w k.1 hk.1 j).1, (h1 k.2 hk.2 j).2.1, hPw k.1 hk.1 j, (h1 k.2 hk.2 j).1]
            exact hs
          obtain ⟨dd, cc, hh⟩ := hF t j (d w k.1 j) (dJ k.2 j) ((c w k.1).1 j) (cJ k.2 j) hId
            (hdc w k.1 hk.1 j).2 (h1 k.2 hk.2 j).2.2
          exact ⟨dd, cc, fun _ _ => hh⟩
        · exact ⟨FinDatum.vacuum ch.G t (.top t j), 0, fun h1' h2' => absurd ⟨h1', h2'⟩ hk⟩
      choose dF cF hdF using hF'
      refine ⟨I w × J, S w ×ˢ SJ, fun k => x w k.1 * xJ k.2, dF,
        fun k j => if h : j < D.R.m then cF k ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
      · intro k hk j
        obtain ⟨hk1, hk2⟩ := Finset.mem_product.1 hk
        obtain ⟨hP, he', hc, -, -⟩ := hdF k j hk1 hk2
        refine ⟨?_, ?_, ?_⟩
        · rw [hP, hPw k.1 hk1 j, (h1 k.2 hk2 j).1, hmap]
        · rw [he', (hdc w k.1 hk1 j).1, (h1 k.2 hk2 j).2.1, hsum]
        · dsimp only
          rw [dif_pos j.2]
          exact hc
      · intro u hu
        have hu' : ∀ j, IsHalf (eL w + ∑ w' ∈ S₀, eL w') (u j) := fun j => by rw [← hsum]; exact hu j
        have hfn : ∀ k ∈ S w ×ˢ SJ, ∀ j, (dF k j).fn (u j) =
            (d w k.1 j).fn (eL w • u j) * (dJ k.2 j).fn ((∑ w' ∈ S₀, eL w') • u j) := by
          intro k hk j
          obtain ⟨hk1, hk2⟩ := Finset.mem_product.1 hk
          obtain ⟨-, he', -, hfn', -⟩ := hdF k j hk1 hk2
          rw [hfn' (u j) (by rw [he', (hdc w k.1 hk1 j).1, (h1 k.2 hk2 j).2.1]; exact hu' j), (hdc w k.1 hk1 j).1,
            (h1 k.2 hk2 j).2.1]
        have hA' : ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (eL w • u j) = fl w u :=
          (hexp' w _ fun j => hhalf _ (hidem1 w) (u j)).trans (hflG w (eL w) (hidem1 w) u)
        have hB' : ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn ((∑ w' ∈ S₀, eL w') • u j) = ∏ w' ∈ S₀, fl w' u :=
          (h2 _ fun j => hhalf _ (hidem S₀) (u j)).trans
            (Finset.prod_congr rfl fun w' hw' => hflG w' _ (hsubmul S₀ w' hw') u)
        rw [Finset.sum_congr rfl fun k hk => by rw [Finset.prod_congr rfl fun j _ => hfn k hk j],
          Finset.sum_product, Finset.prod_insert hw, ← hA', ← hB', Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
      · intro P p hp u
        obtain ⟨r, r₀, h, hr, hr₀, htl, hhr, hhr₀⟩ := hqst p hp S₀ w hw
        have hloc := fun j => hC t (eL w) (V S₀) (V (insert w S₀)) P j _ (hVth S₀ j) (hVst S₀ w hw j)
        have hPC := hζ w (eL w) (heL w) M hM r r₀ h hr hr₀ htl (GlobalTheory.LocAsm.exOne (φ w)) (fun _ _ _ => rfl)
          (fockD ch.W t (V S₀) P) (fockD ch.W t (V (insert w S₀)) P) (fun j => (hloc j).1) (fun j => (hloc j).2)
          (I w) (S w) (x w) (d w) (c w) (hdc w) (hexp w) u
        rw [← hhr, hPC, hhr₀]
        have hIH : (fun u => evT (conAt ch.W hM (fockD ch.W t (V S₀) P) (q p hp S₀)) 1 u 0) =
            (∏ w' ∈ S₀, ζ w') • ∑ a ∈ SJ, xJ a • (fun u => evT (combC ch.W (cJ a, 0)
              (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0) := by
          funext u'
          rw [h3 P p hp u']
          simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
        have hstep : ∀ i ∈ S w, evT (combC ch.W (c w i) (conAt ch.W hM (fockD ch.W t (V S₀) P) (q p hp S₀))) 1 u 0 =
            (∏ w' ∈ S₀, ζ w') * ∑ a ∈ SJ, xJ a * evT (combC ch.W ((fun j => if h : j < D.R.m then cF (i, a) ⟨j, h⟩ else 0), 0)
              (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
          intro i hi
          rw [congrFun (hTc (c w i) _) u, hIH, map_smul, map_sum]
          simp only [map_smul, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
          congr 1
          refine Finset.sum_congr rfl fun a ha => ?_
          congr 1
          rw [← congrFun (hTc (c w i) _) u]
          refine hE (c w i) (cJ a) _ ?_ _ u
          intro j hj f
          rw [dif_pos hj]
          exact (hdF (i, a) ⟨j, hj⟩ hi ha).2.2.2.2 f
        rw [Finset.prod_insert hw, Finset.sum_product, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hstep i hi]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
  obtain ⟨J, SJ, xJ, dJ, cJ, h1, h2, h3⟩ := key Finset.univ
  refine ⟨J, SJ, xJ, dJ, cJ, fun a ha j => ⟨(h1 a ha j).2.1.trans he_sum.symm, (h1 a ha j).2.2⟩, fun u hu => ?_,
    fun P p hp u => ?_⟩
  · rw [h2 u (fun j => by rw [← he_sum]; exact hu j)]
    exact Finset.prod_congr rfl fun w _ => hfl w u
  · have := h3 P p hp u
    rwa [hVu, hqu p hp] at this

end GlobalTheory.LocAsm

end
