import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodAtOfFixRed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperLeftBlockEqOneIffOfFullRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjLevelConjCharacterSymmetricLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFixedBasisReductionMapConjStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem mem_baseLevel_iff_finiteGroup_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) :
    κ ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P) ↔ g0 ∈ P.H := by
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = g0 := hl.2.2
  show κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P) ∧
    rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) ∈ P.H) ↔ _
  rw [e]
  exact ⟨fun hk => hk.2.2, fun hg => ⟨hl.1, hl.2.1, hg⟩⟩

theorem baseLevelCharacter_eq_blockCharacter_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) (hg : g0 ∈ P.H) :
    levChi (Yc D 0) (R.βY 0) (R.dat0 P) κ = ((P.chi ⟨g0, hg⟩ : ℂˣ) : ℂ) := by
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = g0 := hl.2.2
  have e2 : levFn (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = ext1 P.H P.chi (rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ)) := by
    show ext1 P.H P.chi _ * (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ = _
    simp
  unfold levChi
  rw [e2, e, extendOne_of_mem _ hg]

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_flag_triv (R : RealDat D A Ks) (κ : GA D (Yc D 0)) :
    levChi (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) κ = 1 := by
  unfold levChi
  show ((ext1 (⊤ : Subgroup (G0 R.Pg D.R.r)) (⇑(1 : (⊤ : Subgroup (G0 R.Pg D.R.r)) →* ℂˣ)) _ *
    (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
  unfold ext1
  split_ifs <;> simp

theorem hasType_flag1 (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (F : GA D (Yc D 0) → ℂ)
    (hF : ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P), ∀ g, F (g * k) = levChi (Yc D 0) (R.βY 0) (R.dat0 P) k * F g) :
    HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) F := by
  intro κ hκ g
  have h1 : κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) ∧
      rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) κ) ∈ (⊥ : Subgroup (G0 R.Pg D.R.r))) := hκ
  have e : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = 1 := Subgroup.mem_bot.1 h1.2.2
  have hJ : κ ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P) := by
    show κ ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) κ ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P) ∧
      rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) ∈ P.H)
    rw [e]
    exact ⟨h1.1, h1.2.1, P.H.one_mem⟩
  have c1 : levChi (Yc D 0) (R.βY 0) (R.dat0 P) κ = 1 := by
    unfold levChi
    show ((ext1 P.H P.chi (rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ)) *
      (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
    rw [e]
    have h2 : ext1 P.H (⇑P.chi) (1 : G0 R.Pg D.R.r) = 1 := blockDiagonalExtendByOnePrimeField_one P.H P.chi
    erw [h2]
    simp
  have c2 : levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv)) κ = 1 := by
    unfold levChi
    show ((ext1 (⊥ : Subgroup (G0 R.Pg D.R.r)) (⇑(1 : (⊥ : Subgroup (G0 R.Pg D.R.r)) →* ℂˣ)) _ *
      (∏ PP ∈ R.Pg, ∏ c ∈ Finset.range 0, _) * ∏ PP ∈ (∅ : Finset (Pl D.host.E)), _ : ℂˣ) : ℂ) = 1
    unfold ext1
    split_ifs <;> simp
  rw [hF κ hJ g, c1, c2]

theorem mult_act_of_lift (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) {g0 : G0 R.Pg D.R.r} {κ : GA D (Yc D 0)}
    (hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) :
    ∀ T ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 P)) (levChi (Yc D 0) (R.βY 0) (R.dat0 P)),
      ∀ (v : (MP R).Vec) (g : GA D (Yc D 0)),
        (T : MMap (MP R)) v (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 ((T : MMap (MP R)) v) g := by
  intro T hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    intro v g
    have hF := hasType_flag1 R P (T v) (fun k hk g' => hT.lev v k hk g')
    have := level_action_spec hF ⟨κ, hl⟩ κ hl g
    show T v (g * κ) = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (T v) g
    rw [this, levChi_flag_triv, inv_one, one_mul]
  | zero =>
    intro v g
    show (0 : GA D (Yc D 0) → ℂ) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (0 : GA D (Yc D 0) → ℂ) g
    rw [map_zero]
    rfl
  | add T₁ T₂ _ _ h₁ h₂ =>
    intro v g
    show (T₁ v + T₂ v) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (T₁ v + T₂ v) g
    rw [map_add, Pi.add_apply, Pi.add_apply, h₁ v g, h₂ v g]
  | smul a T _ hT =>
    intro v g
    show (a • T v) (g * κ) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 (a • T v) g
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, hT v g]

end GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.SRe

theorem isRedHom_conj {D : D7} {X : HidaSetting D} {red : X.B.I.Gf → G0g D.nd}
    {b' : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E} (c : G0g D.nd) (hred : IsRedHom X red)
    (hf : FixRed X (fun k => c⁻¹ * red k * c) b') : IsRedHom X (fun k => c⁻¹ * red k * c) := by
  refine ⟨goodAt_of_fixRed hf, fun k hk k' hk' => ?_, fun γ => ?_, fun k hk => ?_⟩
  · simp only [hred.2.1 k hk k' hk', mul_assoc, mul_inv_cancel_left]
  · obtain ⟨k, hk, e⟩ := hred.2.2.1 (c * γ * c⁻¹)
    exact ⟨k, hk, by simp only [e]; group⟩
  · rw [← hred.2.2.2 k hk]
    show c⁻¹ * red k * c = 1 ↔ red k = 1
    constructor
    · intro e
      calc red k = c * (c⁻¹ * red k * c) * c⁻¹ := by group
        _ = 1 := by rw [e]; group
    · intro e; rw [e]; group

theorem seeAt_exists : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → R.grp_levels F → GrpPin R → IdempotentRealFixed D → ∃ t, SeeAt R F X h t := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h hι hL hlev hpin hE
  obtain ⟨eR, plg, iso, hpl, he, hdiv, heG⟩ := hpin
  obtain ⟨ψ0, hgen, -, π, hπ, hmem, hchi⟩ := hlev
  have hgw : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := by
    intro kv
    have := D.naut.plGw_over kv.1 kv.2
    simp [placesOver] at this
    exact this
  obtain ⟨t₀, ht₀, red, b, hred, hfix, hlift, hcover⟩ := GlobalTheory.Mem.SRe.TrPt.exists_trans D G' Pl0 T A Ks R X h eR plg iso hι hL hpl hdiv heG
  obtain ⟨c, hc⟩ := GlobalTheory.T.conj_level_conjCharacter_symmetricLevel D G' Pl0 T A Ks R X h eR plg iso hι hL hpl hdiv heG ψ0 hgen π hπ red b hred hfix hgw
  obtain ⟨b', hfix'⟩ := GlobalTheory.T.isFixedBasisReductionMap_conj D X red b c hgw hfix
  obtain ⟨kc, hkc, hkcv⟩ := hred.2.2.1 c
  have hK : ∀ x, x ∈ X.B.I.Kset ↔ x ∈ GlobalTheory.RowLev.Inhab.Ksub X.B.I := fun x => Iff.rfl
  have hmul := hred.2.1
  have red_one : red 1 = 1 := by
    have e := hmul 1 ((hK 1).2 (Subgroup.one_mem _)) 1 ((hK 1).2 (Subgroup.one_mem _))
    rw [mul_one] at e
    exact left_eq_mul.mp e
  have red_inv : ∀ x ∈ X.B.I.Kset, red x⁻¹ = (red x)⁻¹ := by
    intro x hx
    have hx' : x⁻¹ ∈ X.B.I.Kset := (hK _).2 (Subgroup.inv_mem _ ((hK x).1 hx))
    have e := hmul x⁻¹ hx' x hx
    rw [inv_mul_cancel, red_one] at e
    exact eq_inv_of_mul_eq_one_left e.symm
  have memK : ∀ k ∈ X.B.I.Kset, kc⁻¹ * k * kc ∈ X.B.I.Kset := fun k hk =>
    (hK _).2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ((hK _).1 hkc)) ((hK _).1 hk)) ((hK _).1 hkc))
  have red_conj : ∀ k ∈ X.B.I.Kset, red (kc⁻¹ * k * kc) = c⁻¹ * red k * c := by
    intro k hk
    have hkc' : kc⁻¹ ∈ X.B.I.Kset := (hK _).2 (Subgroup.inv_mem _ ((hK _).1 hkc))
    have h1 : kc⁻¹ * k ∈ X.B.I.Kset := (hK _).2 (Subgroup.mul_mem _ ((hK _).1 hkc') ((hK _).1 hk))
    rw [hmul _ h1 _ hkc, hmul _ hkc' _ hk, red_inv _ hkc, hkcv]
  obtain ⟨t, ht⟩ : ∃ t : GA D (D.sp.Y 0), t = (iotaX X h).symm (1, kc) * t₀ := ⟨_, rfl⟩
  have hkap : ∀ k, kap X h t k = kap X h t₀ (kc⁻¹ * k * kc) := by
    intro k
    have e : ((1 : X.B.I.Ginf), kc⁻¹ * k * kc) = ((1, kc) : X.B.I.GA)⁻¹ * (1, k) * (1, kc) := by
      ext <;> simp
    show (t⁻¹ * (iotaX X h).symm (1, k) * t : GA D (D.sp.Y 0)) =
      t₀⁻¹ * (iotaX X h).symm (1, kc⁻¹ * k * kc) * t₀
    rw [e, map_mul, map_mul, map_inv, ht]
    group
  set red' : X.B.I.Gf → G0g D.nd := fun k => c⁻¹ * red k * c with hred'def
  have hred' : IsRedHom X red' := isRedHom_conj c hred hfix'
  have hliftT : ∀ k ∈ X.B.I.Kset, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (eR.symm (red' k))) (kap X h t k) := by
    intro k hk
    rw [hkap, hred'def]
    simp only
    rw [← red_conj k hk]
    exact hlift _ (memK k hk)
  have key : ∀ k ∈ X.B.I.Kset, (kap X h t k ∈ JR R F ↔ k ∈ X.K2) ∧
      ∀ hJ : kap X h t k ∈ JR R F, chiR R F (kap X h t k) = star (X.chi2 k) := by
    intro k hk
    have hl := hliftT k hk
    have hiff := mem_baseLevel_iff_finiteGroup_lift R (R.levR F true) hl
    have hc1 := (hc k hk).1
    refine ⟨?_, fun hJ => ?_⟩
    · rw [show kap X h t k ∈ JR R F ↔ _ from hiff, hmem, hc1]
    · have hg : R.eG (eR.symm (red' k)) ∈ (R.levR F true).H := hiff.1 hJ
      have hg' : reord π (R.eG (eR.symm (red' k))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H := (hmem _).1 hg
      show levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) (kap X h t k) = _
      rw [baseLevelCharacter_eq_blockCharacter_lift R (R.levR F true) hl hg, hchi _ hg hg']
      exact (hc k hk).2 hg'
  have hio : ∀ k, iotaX X h ((iotaX X h).symm (1, k)) = (1, k) := fun k => (iotaX X h).apply_symm_apply _
  have hconjEq : ∀ k, (t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹ = (iotaX X h).symm (1, k) := by
    intro k
    group
  have hK2K : ∀ k ∈ X.K2, k ∈ X.B.I.Kset := fun k hk => hk.1
  refine ⟨t, ⟨?_, ?_, eR.symm, red', ?_, ⟨hred', ?_⟩, ?_⟩⟩
  · have e : t = t₀ * (t₀⁻¹ * (iotaX X h).symm (1, kc) * t₀) := by rw [ht]; group
    rw [e]
    exact Subgroup.mul_mem _ ht₀ (hlift kc hkc).1
  · intro y
    have hJ' : ∀ k, (t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹ ∈ iotaX X h ⁻¹' concreteLevelAdelicSubset X ↔ k ∈ X.K2 := by
      intro k
      rw [hconjEq, Set.mem_preimage, hio]
      exact ⟨fun hh => hh.2, fun hh => ⟨rfl, hh⟩⟩
    have hy : y ∈ JR R F ∨ (t⁻¹)⁻¹ * y * t⁻¹ ∈ iotaX X h ⁻¹' concreteLevelAdelicSubset X → ∃ k ∈ X.B.I.Kset, y = kap X h t k := by
      rintro (hy | hy)
      · have hyF : y ∈ levG (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) := ⟨hy.1, hy.2.1, Subgroup.mem_top _⟩
        obtain ⟨k', hk', e⟩ := hcover y hyF
        refine ⟨kc * k' * kc⁻¹, (hK _).2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ ((hK _).1 hkc) ((hK _).1 hk'))
          (Subgroup.inv_mem _ ((hK _).1 hkc))), ?_⟩
        rw [hkap, e]
        congr 1
        group
      · have h2 : (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).1 = 1 ∧ (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2 ∈ X.K2 := hy
        refine ⟨(iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2, h2.2.1, ?_⟩
        have e : (iotaX X h).symm (1, (iotaX X h ((t⁻¹)⁻¹ * y * t⁻¹)).2) = (t⁻¹)⁻¹ * y * t⁻¹ := by
          rw [← h2.1]
          exact (iotaX X h).symm_apply_apply _
        show y = (t⁻¹ * (iotaX X h).symm (1, _) * t : GA D (D.sp.Y 0))
        rw [e]
        group
    refine ⟨⟨fun h1 => ?_, fun h1 => ?_⟩, fun h1 => ?_⟩
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inl h1)
      exact (hJ' k).2 ((key k hk).1.1 h1)
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inr h1)
      exact (key k hk).1.2 ((hJ' k).1 h1)
    · obtain ⟨k, hk, rfl⟩ := hy (Or.inl h1)
      rw [(key k hk).2 h1]
      show adelicCharacterOfHidaSetting X (iotaX X h ((t⁻¹)⁻¹ * (t⁻¹ * (iotaX X h).symm (1, k) * t) * t⁻¹)) = _
      rw [hconjEq, hio]
      rfl
  · intro k hk
    have hkK := hK2K k hk
    have hJ := (key k hkK).1.2 hk
    exact ⟨hJ, (key k hkK).2 hJ⟩
  · intro k hk T hT v g
    exact mult_act_of_lift R (R.levR F true) (hliftT k hk) T hT v g
  · intro γ
    show star (D.ntypes.e0.coeff γ) = D.what₂.embLL ((idemOf A.X).coeff (eR.symm γ))
    rw [he, MulEquiv.apply_symm_apply, hE γ]

end GlobalTheory.Mem.SRe
