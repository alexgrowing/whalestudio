import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlOrbitIntegralDepthDatumMemSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridGivenPathTensorMemSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilTraceAddCharAtPlaceMemSubfieldOfRootsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedAbsComplexPowHalfMemSubfieldOfSqrtNormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TflipField

section Generic

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

omit [MeasurableSpace k] [BorelSpace k] in

theorem apow_nat_half_mem (F : Subfield ℂ) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F) (x : kˣ) (n : ℕ) :
    apow x ((n : ℂ) / 2) ∈ F := by
  have : apow x ((n : ℂ) / 2) = apow x (1 / 2) ^ n := by
    rw [apow, apow, ← Complex.cpow_nat_mul]; congr 1; ring
  rw [this]; exact F.pow_mem (habs x) n

omit [MeasurableSpace k] [BorelSpace k] in

theorem fourierSum_mem {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (F : Subfield ℂ) (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F)
    {Φ : Matrix A D k → ℂ} (hΦ : ∀ X, Φ X ∈ F) (Y : Matrix A D k) : fourierSum ψ ϖ e P Φ Y ∈ F := by
  classical
  rw [fourierSum_apply]
  split_ifs with h
  · refine F.mul_mem (F.inv_mem (F.pow_mem (natCast_mem F _) _)) (F.sum_mem fun T _ => F.mul_mem (hΦ _) (hψ _ ?_))
    rw [← Valuation.mem_integer_iff]
    change _ ∈ 𝒪[k]
    rw [pairCols, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Finset.mul_sum]
    refine Subring.sum_mem _ fun j _ => ?_
    rw [mul_left_comm]
    exact Subring.mul_mem _ (liftRes_mem T i j) (h i j j.2)
  · exact F.zero_mem

omit [MeasurableSpace k] [BorelSpace k] in

theorem invFourierSum_inv_mem {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (F : Subfield ℂ) (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F)
    {Φ : Matrix A D k → ℂ} (hΦ : ∀ X, Φ X ∈ F) (T : Matrix A D k) : invFourierSum ψ⁻¹ ϖ e P Φ T ∈ F := by
  classical
  rw [invFourierSum_inv_apply]
  split_ifs with h
  · refine F.sum_mem fun S _ => F.mul_mem (hΦ _) (hψ _ ?_)
    rw [← Valuation.mem_integer_iff]
    change _ ∈ 𝒪[k]
    have e1 : ((ϖ ^ e : kˣ) : k) * pairCols P T ((ϖ ^ e)⁻¹ • liftRes S) = ∑ i, ∑ j : P, liftRes S i j * T i j := by
      rw [pairCols, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, Units.smul_def, smul_eq_mul, ← mul_assoc, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mul]
    rw [e1]
    exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (liftRes_mem S i j) (h i j j.2)
  · exact F.zero_mem

theorem smallF_mem {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (F : Subfield ℂ) {J : Subgroup (GL A' k)} (hJo : IsOpen (J : Set (GL A' k))) (hJK : J ≤ KO k A')
    (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (he : 1 ≤ e) (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν)
    (hνF : ∀ u, (ν u : ℂ) ∈ F) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F) (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}
    (hΨ : HasDepth ϖ e (diagLat c) Ψ) (hΨF : ∀ X, Ψ X ∈ F) (h : GL D k) :
    smallF (haarVol J) ν Ψ (Y0 k σ * h.val) ∈ F :=
  GlobalTheory.T.glOrbitIntegral_depthDatum_mem_subfield F hJo hJK σ ν hϖ he hν hram hνF habs c hΨ hΨF h

theorem phiA_mem {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (F : Subfield ℂ) {J : Subgroup (GL A' k)} (hJo : IsOpen (J : Set (GL A' k))) (hJK : J ≤ KO k A')
    (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (he : 1 ≤ e) (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν)
    (hνF : ∀ u, (ν u : ℂ) ∈ F) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F) (c : D → kˣ) (Λ' : Submodule 𝒪[k] (D → k))
    {Ψ : Matrix A' D k → ℂ} (hΨ : HasDepth ϖ e (diagLat c) Ψ) (hΨF : ∀ X, Ψ X ∈ F) (X : Matrix A D k) :
    phiA (haarVol J) σ ν ϖ e Λ' Ψ X ∈ F := by
  classical
  unfold phiA
  split_ifs
  · unfold fFun
    split_ifs with hX
    · exact F.mul_mem (F.mul_mem (hνF _) (apow_nat_half_mem F habs _ _))
        (smallF_mem F hJo hJK σ ν hϖ he hν hram hνF habs c hΨ hΨF _)
    · exact F.zero_mem
  · exact F.zero_mem

theorem flipTensor_mem {G : Grid k} (F : Subfield ℂ) {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ)
    (hψc : HasConductor ψ 1) (he : 1 ≤ e) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F)
    (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F) {i j : ℕ}
    (hν : CondLE ϖ e (G.nu i j)) (hram : ¬ IsUnram (G.nu i j)) (hνF : ∀ u, (G.nu i j u : ℂ) ∈ F) {J : G.Level}
    (hJ : IsOpen (J (i, j) : Set (GL (Fin (G.rank (i, j))) k))) (hK : J (i, j) ≤ KO k _) {γ : List Edge}
    (h1 : Edge.theta i j ∈ γ) (h2 : Edge.ex i j ∈ γ) {T : G.Args → ℂ} (hT : G.IsTensor ϖ e γ T) (hTF : ∀ x, T x ∈ F)
    (x : G.Args) : G.flipTensor .one ψ ϖ e i j J T x ∈ F := by
  have hJ' := isOpen_map_invT hJ hK
  unfold Grid.flipTensor squareFlip
  exact invFourierSum_inv_mem F ψ ϖ e _ hψ (fun X => phiA_mem F hJ'.1 hJ'.2 _ _ hϖ he hν hram hνF habs
    (blockUnits ϖ e _) _ ((FourierDepth.fourier_exchange k _ _ ψ ϖ e _ hϖ hψc).1 _ (isNatDatum_sliceB hT h1 h2 x))
    (fun Y => fourierSum_mem F ψ ϖ e _ hψ (fun Z => hTF _) Y) X) _

theorem flips_mem {G : Grid k} (F : Subfield ℂ) {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ)
    (hψc : HasConductor ψ 1) (he : 1 ≤ e) (habs : ∀ u : kˣ, apow u (1 / 2) ∈ F)
    (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ F) :
    ∀ (l : List (ℕ × ℕ)) (S : G.PiLocalization₂),
      (∀ x ∈ l, CondLE ϖ e (G.nu x.1 x.2) ∧ ¬ IsUnram (G.nu x.1 x.2) ∧ ∀ u, (G.nu x.1 x.2 u : ℂ) ∈ F) →
      CanFlip S.path l → (∀ X, IsOpen (S.level X : Set (GL (Fin (G.rank X)) k)) ∧ S.level X ≤ KO k _) →
      G.IsTensor ϖ e S.path S.tensor → (∀ z, S.tensor z ∈ F) → ∀ z, (S.flips .one ψ ϖ e l).tensor z ∈ F := by
  intro l
  induction l with
  | nil => intro S _ _ _ _ hF; exact hF
  | cons x l ih =>
    intro S hν hc hJ hT hF
    obtain _ | ⟨hp, hc'⟩ := hc
    have hsub := hp.subset
    have hx := hν x List.mem_cons_self
    refine ih (S.flip .one ψ ϖ e x) (fun y hy => hν y (List.mem_cons_of_mem _ hy)) hc' (fun X => ?_)
      (isTensor_flipTensor hϖ hψc he hx.1 (hJ _).1 (hJ _).2 (hsub (by simp)) (hsub (by simp)) hT)
      (flipTensor_mem F hϖ hψc he habs hψ hx.1 hx.2.1 hx.2.2 (hJ _).1 (hJ _).2 (hsub (by simp)) (hsub (by simp)) hT hF)
    change IsOpen (G.flipLevel x.1 x.2 S.level X : Set (GL (Fin (G.rank X)) k)) ∧ G.flipLevel x.1 x.2 S.level X ≤ _
    by_cases hX : X = (x.1 + 1, x.2 + 1)
    · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
    · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X

end Generic

end GlobalTheory.TflipField

namespace GlobalTheory.TflipField

section Concrete

open ValuativeRel Formalism.L2.Host

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem givenStage_mem (F : Subfield ℂ) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E)
    (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) (hxi : ∀ x, ((L.xiH t).loc w x : ℂ) ∈ F)
    (z : (locGrid G t w).Args) : (givenStage t w B Φ).tensor z ∈ F :=
  GlobalTheory.T.gridGivenPathTensor_mem_subfield F B t Φ w hmu hxi z

theorem nu_mem (F : Subfield ℂ) (t : T) (w : Pl D.host.E) (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F)
    (hxi : ∀ x, ((L.xiH t).loc w x : ℂ) ∈ F) (hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, ((G.ch.chiH i).loc w x : ℂ) ∈ F)
    {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) (u : (Kw w)ˣ) : ((locGrid G t w).nu i j u : ℂ) ∈ F := by
  have e1 : (((locGrid G t w).nu i j u : ℂˣ) : ℂ) =
      ((L.C.mu0 ⟨j, hj⟩).loc w u : ℂ) * ((L.xiH t).loc w u : ℂ) * (((G.ch.chiH (D.R.m - i)).loc w u : ℂ))⁻¹ := by
    simp only [Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Units.val_div_eq_div_val, div_eq_mul_inv]
    simp [HChar.loc]
  rw [e1]
  exact F.mul_mem (F.mul_mem (hmu _ _) (hxi _)) (F.inv_mem (hchi _ (by omega) (by omega) _))

theorem psiAt_mem (F : Subfield ℂ) {W : G.Weil} {w : Pl D.host.E}
    (hroots : ∀ z : ℂ, z ^ (Ideal.absNorm w.asIdeal ^ depthAt G w) = 1 → z ∈ F) (hcond : HasConductor (psiAt W w) 1)
    (x : Kw w) (hx : valuation (Kw w) ((((unifAt w) ^ depthAt G w : (Kw w)ˣ) : Kw w) * x) ≤ 1) :
    (psiAt W w x : ℂ) ∈ F :=
  GlobalTheory.T.weilTraceAddCharAtPlace_mem_subfield_of_roots F hroots hcond x hx

theorem apow_half_mem (F : Subfield ℂ) (w : Pl D.host.E)
    (hsq : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ F) (u : (Kw w)ˣ) : apow u (1 / 2) ∈ F :=
  GlobalTheory.T.normalisedAbsComplexPow_half_mem_subfield_of_sqrt_norm F w hsq u

end Concrete

end GlobalTheory.TflipField

namespace GlobalTheory.RowTest

theorem Tflip_mem_range : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D)
    (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum),
    ch.S.SumOK t Φ → ∀ w ∈ locPl ch.G t, ∀ z, Tflip ch.W ch.S.B t Φ w z ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS hch _ hF t Φ _ w hw z
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B t Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  let K : Subfield ℂ := D.what₂.embLL.fieldRange
  have hK : ∀ y, y ∈ Set.range D.what₂.embLL → y ∈ K := fun y hy => RingHom.mem_fieldRange.2 hy
  have hmu : ∀ j x, ((R.toLevCh.C.mu0 j).loc w x : ℂ) ∈ K := fun j x => hK _ (hF.chars.mu0 j w x)
  have hxi : ∀ x, ((R.toLevCh.xiH t).loc w x : ℂ) ∈ K := fun x => hK _ (hF.chars.xi t w x)
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x, ((ch.G.ch.chiH i).loc w x : ℂ) ∈ K :=
    fun i a b x => hK _ (hF.chars.chi i a b w x)
  have habs : ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ K :=
    GlobalTheory.TflipField.apow_half_mem K w (hK _ (hF.sqrt w (.inr ⟨t, hw⟩)))
  have hψ := GlobalTheory.TflipField.psiAt_mem (W := ch.W) K (fun z hz => hK _ (hF.roots t w hw z hz)) h00.cond
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G t w).nu x.1 x.2) ∧
      ¬ IsUnram ((locGrid ch.G t w).nu x.1 x.2) ∧ ∀ u, ((locGrid ch.G t w).nu x.1 x.2 u : ℂ) ∈ K := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    have hs := hg.square i hi j hj
    have e := (locGrid ch.G t w).alpha_div_beta i j
    refine ⟨by rw [← e]; exact hs.condν, by rw [← e]; exact hs.ram, GlobalTheory.TflipField.nu_mem K t w hmu hxi hchi hi hj⟩
  have key := GlobalTheory.TflipField.flips_mem K h00.unif h00.cond h00.one_le habs hψ (flipOrder D.R.m)
    (givenStage t w ch.S.B Φ) hν (canFlip_flipOrder _).1 (fun X => GivenAdm.givenLevel_open hL hw X) hadm.tensor
    (GlobalTheory.TflipField.givenStage_mem K ch.S.B t Φ w hmu hxi) z
  exact RingHom.mem_fieldRange.1 key

end GlobalTheory.RowTest
