import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardinalityOfBand

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def VolSigIndep (D : D7) : Prop :=
  ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) →
    (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank →
    ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)) (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram))
      (μ₀ : Measure (HA (AF D.host.F) D.sp.cm.sig W₀.gram))
      (𝓕₀ : Set (HA (AF D.host.F) D.sp.cm.sig W₀.gram)),
      IsVolMeas D W P Q μ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
      IsVolMeas D W₀ P₀ Q₀ μ₀ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₀.gram) 𝓕₀ μ₀ →
      μ 𝓕 = μ₀ 𝓕₀

def UnitSplit (D : D7) : Prop :=
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∃ x : W.V, W.hT x x = (if s then 1 else -1) ∧
      ∃ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
        HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧ W'.SigOK ∧
        (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1)))

theorem volTie_toReal (D : D7) (hT : VolTie D) (W : HSpace D.host.E) (P Q : ℕ) (hW : W.SigOK)
    (hs : ∀ τ, W.sig τ = (P, Q)) (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) (hμ : IsVolMeas D W P Q μ)
    (h𝓕 : IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ) :
    (μ 𝓕).toReal = D.vol W := by
  obtain ⟨-, hall⟩ := hT W P Q hW hs
  obtain ⟨-, hF⟩ := hall μ hμ
  rw [hF 𝓕 h𝓕, ENNReal.toReal_ofReal (D.vol_pos W).le]

theorem vol_eq_of_indep (D : D7) (hT : VolTie D) (hI : VolSigIndep D) (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ)
    (hW : W.SigOK) (hW₀ : W₀.SigOK) (hs : ∀ τ, W.sig τ = (P, Q)) (hs₀ : ∀ τ, W₀.sig τ = (P₀, Q₀))
    (hr : W.rank = W₀.rank) : D.vol W = D.vol W₀ := by
  obtain ⟨⟨μ, hμ⟩, hall⟩ := hT W P Q hW hs
  obtain ⟨⟨𝓕, h𝓕⟩, hF⟩ := hall μ hμ
  obtain ⟨⟨μ₀, hμ₀⟩, hall₀⟩ := hT W₀ P₀ Q₀ hW₀ hs₀
  obtain ⟨⟨𝓕₀, h𝓕₀⟩, hF₀⟩ := hall₀ μ₀ hμ₀
  have e := hI W W₀ P Q P₀ Q₀ hW hW₀ hs hs₀ hr μ 𝓕 μ₀ 𝓕₀ hμ h𝓕 hμ₀ h𝓕₀
  rw [hF 𝓕 h𝓕, hF₀ 𝓕₀ h𝓕₀] at e
  exact (ENNReal.ofReal_eq_ofReal_iff (D.vol_pos W).le (D.vol_pos W₀).le).1 e

def stdPos (D : D7) (n : ℕ) : HSpace D.host.E :=
  Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) (fun x hx => Formalism.BasicNotions.Examples₂.star_isIntegral x hx) n

theorem stdPos_sigOK (D : D7) (n : ℕ) : (stdPos D n).SigOK :=
  Formalism.BasicNotions.Examples₂.posSpace_sigOK (E := D.host.E) (fun x hx => Formalism.BasicNotions.Examples₂.star_isIntegral x hx) n

theorem stdPos_rank (D : D7) (n : ℕ) : (stdPos D n).rank = n := rfl

theorem stdPos_sig (D : D7) (n : ℕ) (τ : D.host.E →+* ℂ) : (stdPos D n).sig τ = (n, 0) := rfl

theorem vol_eq_mass_of_indep (D : D7) (n : ℕ) (hT : VolTie D) (hI : VolSigIndep D) (hC : ClassItemsAt D n)
    (W : HSpace D.host.E) (P Q : ℕ) (hW : W.SigOK) (hs : ∀ τ, W.sig τ = (P, Q)) (hrk : W.rank = n) :
    D.vol W = massI D n := by
  rw [vol_eq_of_indep D hT hI W (stdPos D n) P Q n 0 hW (stdPos_sigOK D n) hs (stdPos_sig D n)
    (by rw [hrk, stdPos_rank])]
  exact volume_mass_of_class_data D n hT hC.1 hC.2.1 hC.2.2 (stdPos D n) (stdPos_sigOK D n)
    (fun τ => by rw [stdPos_sig, stdPos_rank]) (stdPos_rank D n)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem volRatioTrue_of_indep (D : D7) (hT : VolTie D) (hI : VolSigIndep D)
    (hC : ∀ n, 2 ≤ n → ClassItemsAt D n) (hU : UnitSplit D) : VolRatioTrue D := by
  intro W P Q hW hs hM s hsP
  obtain ⟨x, hx, W', ι, h1, h2, hW', hs'⟩ := hU W P Q hW hs hM s hsP
  refine ⟨x, hx, W', ι, h1, h2, hW', hs', ?_⟩
  intro μ 𝓕 μ' 𝓕' hμ h𝓕 hμ' h𝓕'
  have hrk : W.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    rw [hs D.host.φ₀] at this
    omega
  have hs'' : ∀ τ, W'.sig τ = (if s then P - 1 else P, if s then Q else Q - 1) := by
    intro τ; rw [hs' τ]; cases s <;> simp
  have hrk' : W'.rank = W.rank - 1 := by
    have := Formalism.BasicNotions.sig_sum W' hW' D.host.φ₀
    rw [hs'' D.host.φ₀] at this
    cases s <;> simp at this hsP <;> omega
  rw [volTie_toReal D hT W P Q hW hs μ 𝓕 hμ h𝓕,
    volTie_toReal D hT W' _ _ hW' hs'' μ' 𝓕' hμ' h𝓕',
    vol_eq_mass_of_indep D W.rank hT hI (hC _ (by omega)) W P Q hW hs rfl,
    vol_eq_mass_of_indep D (W.rank - 1) hT hI (hC _ (by omega)) W' _ _ hW' hs'' hrk']
  exact standardLattice_aux2b D W.rank hM

def LandherrSig (D : D7) : Prop :=
  ∀ W₁ W₂ : HSpace D.host.E, W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank → (∀ τ, W₁.sig τ = W₂.sig τ) →
    ∃ φ : W₁.V ≃ₗ[D.host.E] W₂.V, ∀ x y, W₂.hT (φ x) (φ y) = W₁.hT x y

def band (m a b : ℕ) : Fin m → Bool := fun i => decide (a ≤ (i : ℕ) ∧ (i : ℕ) < b)

theorem card_band (m a b : ℕ) (hb : b ≤ m) :
    (Finset.univ.filter (fun i : Fin m => band m a b i = true)).card = b - a := by
  first | exact UpperTheory.Reformulated.B.CardinalityOfBand.card_band .. | (apply UpperTheory.Reformulated.B.CardinalityOfBand.card_band <;> assumption) | (intros; apply UpperTheory.Reformulated.B.CardinalityOfBand.card_band <;> assumption) | (apply @UpperTheory.Reformulated.B.CardinalityOfBand.card_band <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.CardinalityOfBand.card_band <;> assumption) | (apply @UpperTheory.Reformulated.B.CardinalityOfBand.card_band <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.CardinalityOfBand.card_band m a b hb | exact @UpperTheory.Reformulated.B.CardinalityOfBand.card_band m a b | exact @UpperTheory.Reformulated.B.CardinalityOfBand.card_band m a | exact @UpperTheory.Reformulated.B.CardinalityOfBand.card_band m

theorem hasSig_diag_sgn {N : ℕ} (d : Fin N → Bool) (q : ℕ)
    (hq : (Finset.univ.filter (fun i => d i = true)).card = q) :
    Formalism.UG.HasSignature (Matrix.diagonal fun i : Fin N => (Formalism.BasicNotions.Examples₂.sgn (d i) : ℂ)) (N - q) q := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (p := fun i => d i = true)
  rw [hq, Finset.card_univ, Fintype.card_fin] at hsum
  have hp : Fintype.card {i // d i = false} = N - q := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter (fun i : Fin N => d i = false)) =
        (Finset.univ.filter (fun i : Fin N => ¬ d i = true)) := by
      ext i; simp
    rw [this]; omega
  have hq' : Fintype.card {i // ¬ d i = false} = q := by
    rw [Fintype.card_subtype, ← hq]
    congr 1; ext i; simp
  let e1 : {i // d i = false} ≃ Fin (N - q) := Fintype.equivFinOfCardEq hp
  let e2 : {i // ¬ d i = false} ≃ Fin q := Fintype.equivFinOfCardEq hq'
  let e : Fin N ≃ Fin (N - q) ⊕ Fin q :=
    (Equiv.sumCompl (fun i => d i = false)).symm.trans (Equiv.sumCongr e1 e2)
  have hl : ∀ a, e.symm (Sum.inl a) = (e1.symm a).1 := fun a => rfl
  have hr : ∀ a, e.symm (Sum.inr a) = (e2.symm a).1 := fun a => rfl
  refine ⟨e, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, hl, hl, Matrix.diagonal_apply]
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
    by_cases h : a = b
    · subst h; simp [(e1.symm a).2, Formalism.BasicNotions.Examples₂.sgn]
    · have h' : (e1.symm a).1 ≠ (e1.symm b).1 := fun h' => h (e1.symm.injective (Subtype.val_injective h'))
      simp [h, h']
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, hl, hr, Matrix.diagonal_apply]
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    have h' : (e1.symm a).1 ≠ (e2.symm b).1 := fun h => (e2.symm b).2 (h ▸ (e1.symm a).2)
    simp [h']
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, hr, hl, Matrix.diagonal_apply]
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    have h' : (e2.symm a).1 ≠ (e1.symm b).1 := fun h => (e2.symm a).2 (h ▸ (e1.symm b).2)
    simp [h']
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, hr, hr, Matrix.diagonal_apply]
    simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply]
    have hd : d (e2.symm a).1 = true := by simpa using (e2.symm a).2
    by_cases h : a = b
    · subst h; simp [hd, Formalism.BasicNotions.Examples₂.sgn]
    · have h' : (e2.symm a).1 ≠ (e2.symm b).1 := fun h' => h (e2.symm.injective (Subtype.val_injective h'))
      simp [h, h']

def bandSpace (D : D7) (m a b : ℕ) : HSpace D.host.E :=
  Formalism.BasicNotions.Examples₂.stdSpace (E := D.host.E) (fun x hx => Formalism.BasicNotions.Examples₂.star_isIntegral x hx) m (band m a b)
    (m - (b - a)) (b - a)

theorem bandSpace_sigOK (D : D7) (m a b : ℕ) (hb : b ≤ m) : (bandSpace D m a b).SigOK := by
  intro τ
  have hg : (bandSpace D m a b).gram.map τ =
      Matrix.diagonal fun i : Fin m => (Formalism.BasicNotions.Examples₂.sgn (band m a b i) : ℂ) := by
    ext i j
    rw [Matrix.map_apply]
    refine (congrArg τ (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E)
      (fun x hx => Formalism.BasicNotions.Examples₂.star_isIntegral x hx) m (band m a b) (m - (b - a)) (b - a) i j)).trans ?_
    change τ (if i = j then (Formalism.BasicNotions.Examples₂.sgn (band m a b i) : D.host.E) else 0) =
      if i = j then (Formalism.BasicNotions.Examples₂.sgn (band m a b i) : ℂ) else 0
    by_cases h : i = j <;> simp [h, Formalism.BasicNotions.Examples₂.map_sgn]
  rw [hg]
  exact hasSig_diag_sgn (band m a b) (b - a) (card_band m a b hb)

theorem selfDualLattice_projection_mem_of_unit_length (D : D7) (hL : LandherrSig D) (W : HSpace D.host.E) (P Q : ℕ) (hW : W.SigOK)
    (hs : ∀ τ, W.sig τ = (P, Q)) (n a b b' : ℕ) (hn : W.rank = n + 1) (hb : b ≤ n + 1) (hQ : b - a = Q)
    (hP : n + 1 - Q = P) (hb' : b' ≤ n) (hbb : ∀ i : Fin n, band n a b' i = band (n + 1) a b (Fin.castSucc i)) :
    ∃ x : W.V, W.hT x x = Formalism.BasicNotions.Examples₂.sgn (band (n + 1) a b (Fin.last n)) ∧
      ∃ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
        HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧ W'.SigOK ∧
        (∀ τ, W'.sig τ = (n - (b' - a), b' - a)) := by
  have h1 : (bandSpace D (n + 1) a b).SigOK := bandSpace_sigOK D (n + 1) a b hb
  obtain ⟨φ, hφ⟩ := hL (bandSpace D (n + 1) a b) W h1 hW hn.symm (fun τ => by
    rw [hs τ]; show (n + 1 - (b - a), b - a) = (P, Q); rw [hQ, hP])
  obtain ⟨φ', hφ'⟩ : ∃ φ' : (Fin (n + 1) → D.host.E) ≃ₗ[D.host.E] W.V, ∀ x y : Fin (n + 1) → D.host.E,
      W.hT (φ' x) (φ' y) = Formalism.BasicNotions.Examples₂.diagForm (n + 1) (band (n + 1) a b) x y := ⟨φ, hφ⟩
  have key : ∀ u : Fin (n + 1) → D.host.E, W.hT (φ' (Pi.single (Fin.last n) (1 : D.host.E))) (φ' u) =
      Formalism.BasicNotions.Examples₂.sgn (band (n + 1) a b (Fin.last n)) * u (Fin.last n) := by
    intro u
    rw [hφ', Formalism.BasicNotions.Examples₂.diagForm_single_left]
    simp
  refine ⟨φ' (Pi.single (Fin.last n) (1 : D.host.E)), ?_, bandSpace D n a b',
    φ'.toLinearMap ∘ₗ Formalism.BasicNotions.Examples₂.extZero n, ?_, ?_, bandSpace_sigOK D n a b' hb', fun τ => rfl⟩
  · rw [key]
    simp
  · exact fun y z => (hφ' _ _).trans
      (Formalism.BasicNotions.Examples₂.extZero_isom n (band n a b') (band (n + 1) a b) (fun i => (hbb i).symm) y z)
  · ext v
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨y, rfl⟩
      exact (key _).trans (mul_eq_zero_of_right _ (Formalism.BasicNotions.Examples₂.extZero_last n y))
    · intro hv
      have hv' := key (φ'.symm v)
      rw [LinearEquiv.apply_symm_apply, hv] at hv'
      have hz : φ'.symm v (Fin.last n) = 0 := by
        rcases mul_eq_zero.1 hv'.symm with h | h
        · exact absurd h (Formalism.BasicNotions.Examples₂.sgn_ne_zero _)
        · exact h
      have hE : Formalism.BasicNotions.Examples₂.extZero n (fun i => φ'.symm v (Fin.castSucc i)) = φ'.symm v := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [Formalism.BasicNotions.Examples₂.extZero_last, hz]
        · rw [Formalism.BasicNotions.Examples₂.extZero_castSucc]
      exact ⟨fun i => φ'.symm v (Fin.castSucc i), (congrArg φ' hE).trans (φ'.apply_symm_apply v)⟩

theorem unitSplit_of_landherr (D : D7) (hL : LandherrSig D) : UnitSplit D := by
  intro W P Q hW hs hM s hsP
  have hrk : W.rank = P + Q := by
    have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    rw [hs D.host.φ₀] at this
    omega
  obtain ⟨n, hn⟩ : ∃ n, W.rank = n + 1 := ⟨W.rank - 1, by omega⟩
  cases s with
  | true =>
    have hP1 : 1 ≤ P := by simpa using hsP
    obtain ⟨x, hx, W', ι, h1, h2, h3, h4⟩ :=
      selfDualLattice_projection_mem_of_unit_length D hL W P Q hW hs n (P - 1) n n hn (by omega) (by omega) (by omega) le_rfl
        (fun i => by simp only [band, Fin.val_castSucc])
    refine ⟨x, ?_, W', ι, h1, h2, h3, fun τ => ?_⟩
    · rw [hx]; simp [band, Formalism.BasicNotions.Examples₂.sgn]
    · rw [h4 τ]; simp only [if_true, Prod.mk.injEq]; constructor <;> omega
  | false =>
    have hQ1 : 1 ≤ Q := by simpa using hsP
    obtain ⟨x, hx, W', ι, h1, h2, h3, h4⟩ :=
      selfDualLattice_projection_mem_of_unit_length D hL W P Q hW hs n P (n + 1) n hn le_rfl (by omega) (by omega) le_rfl
        (fun i => by
          have := i.isLt
          simp only [band, Fin.val_castSucc, decide_eq_decide]
          omega)
    refine ⟨x, ?_, W', ι, h1, h2, h3, fun τ => ?_⟩
    · rw [hx]
      have hb : band (n + 1) P (n + 1) (Fin.last n) = true := by
        simp only [band, Fin.val_last, decide_eq_true_eq]; omega
      rw [hb]; simp [Formalism.BasicNotions.Examples₂.sgn]
    · rw [h4 τ]; simp only [Bool.false_eq_true, if_false, Prod.mk.injEq]; constructor <;> omega

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem volRatioTrue_of_named (D : D7) (hT : VolTie D) (hI : VolSigIndep D) (hL : LandherrSig D)
    (hC : ∀ n, 2 ≤ n → ClassItemsAt D n) : VolRatioTrue D :=
  volRatioTrue_of_indep D hT hI hC (unitSplit_of_landherr D hL)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem theorem_two_of_landherr (D : D7) (hT : VolTie D) (hI : VolSigIndep D) (hL : LandherrSig D)
    (hC : ∀ n, 2 ≤ n → ClassItemsAt D n) : Conclusion2 D :=
  theorem_two_of_volume_ratio D (volRatioTrue_of_named D hT hI hL hC) hT

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
