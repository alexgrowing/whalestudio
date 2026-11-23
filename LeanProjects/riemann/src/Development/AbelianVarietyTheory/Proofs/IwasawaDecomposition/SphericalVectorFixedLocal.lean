import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfNodupAlg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutRepIsotypicSplitPlaceLocalComponentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceFixedVectorSumSphericalImagesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceHeckeOperatorEigenvalueConjSphericalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteHeckeDoubleCosetCosetsAtSplitPlaceStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeckeFrob

theorem conjSplit_w (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host) (h : IsConjPl D.host w s.w) :
    (conjSplit s).w = w := by
  have hc : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun x => by
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact Formalism.HC.HostAx.conjE_apply _ _ _
  apply HeightOneSpectrum.ext
  ext x
  have hy : ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [hc]; rfl
  rw [h x _ hy]
  exact Iff.rfl

theorem heckeD_add (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (f f' : GAf L n → W) :
    NG.heckeD J Dset (f + f') = NG.heckeD J Dset f + NG.heckeD J Dset f' := by
  classical
  funext g
  have hsub : ∀ F : GAf L n → W,
      Function.support (fun cc : GAf L n ⧸ J =>
        if hc : ∃ x ∈ Dset, (x : GAf L n ⧸ J) = cc then F (g * hc.choose) else 0) ⊆
        (hfin.toFinset : Set (GAf L n ⧸ J)) := by
    intro F cc hcc
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    apply hcc
    dsimp only
    rw [dif_neg]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  rw [Pi.add_apply]
  simp only [NG.heckeD]
  rw [finsum_eq_sum_of_support_subset _ (hsub _), finsum_eq_sum_of_support_subset _ (hsub _),
    finsum_eq_sum_of_support_subset _ (hsub _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun cc _ => ?_
  split_ifs <;> simp

theorem heckeD_zero (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (Dset : Set (GAf L n)) :
    NG.heckeD J Dset (0 : GAf L n → W) = 0 := by
  funext g
  simp [NG.heckeD]

theorem tN_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' tSet L n s ϖ k).Finite) {m : ℕ} (F : Fin m → GAf L n → W) :
    NG.tN J s ϖ k (∑ j, F j) = ∑ j, NG.tN J s ϖ k (F j) := by
  classical
  have key : ∀ t : Finset (Fin m), NG.tN J s ϖ k (∑ j ∈ t, F j) = ∑ j ∈ t, NG.tN J s ϖ k (F j) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp [NG.tN, heckeD_zero]
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      simp only [NG.tN]
      rw [heckeD_add L n J _ hfin, smul_add]
  exact key Finset.univ

theorem prod_eq_vieta (n : ℕ) (β : Multiset ℂ) (hn : Multiset.card β = n) :
    (β.map fun a => X - C a).prod = X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * β.esymm k) * X ^ (n - k) := by
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, hn, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [pow_zero, Multiset.esymm, Multiset.powersetCard_zero_left, Multiset.map_singleton,
    Multiset.prod_zero, Multiset.sum_singleton, map_one, one_mul, Nat.sub_zero]
  congr 1
  refine Finset.sum_congr (by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega) fun k _ => ?_
  rw [map_mul, map_pow, map_neg, map_one, mul_assoc]

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem cls_heq {E : Type} [Field E] [NumberField E] {n : ℕ} {a b : HeightOneSpectrum (𝓞 E)} (h : a = b)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (a.adicCompletion E))) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (b.adicCompletion E)))
    (he : HEq σ.cl τ.cl) : HEq (GlobalTheory.LocLanglands.cls σ) (GlobalTheory.LocLanglands.cls τ) := by
  subst h
  exact heq_of_eq (congrArg (Sigma.mk n) (eq_of_heq he))

theorem galSide (hL : GlobalTheory.Published.LocalLanglandsGL) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {n : ℕ}
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E))) (α : Fin n → ℂˣ) (hα : GlobalTheory.SmGL.HasSatake σ.ρ α) :
    ((GlobalTheory.CuspRep.ParLaws.locRec hL h (GlobalTheory.LocLanglands.cls σ)).lpTw ((1 - (n : ℝ)) / 2)).unr ∧
    ((GlobalTheory.CuspRep.ParLaws.locRec hL h (GlobalTheory.LocLanglands.cls σ)).lpTw ((1 - (n : ℝ)) / 2)).frobEig = twEig w α := by
  rw [GlobalTheory.CuspRep.ParLaws.rec_eq_diag (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL h) hα]
  have hu : (GlobalTheory.WeilDeligne.WD.mk (GlobalTheory.WeilDeligne.WDRep.diag h fun i => (α i)⁻¹)).unr :=
    (GlobalTheory.WeilDeligne.WD.unr_mk _).2 (GlobalTheory.WeilDeligne.WDRep.unr_diag _)
  refine ⟨(GlobalTheory.WeilDeligne.WD.unr_tw _ _).2 hu, ?_⟩
  rw [GlobalTheory.WeilDeligne.WD.frobEig_tw _ _ hu, GlobalTheory.WeilDeligne.WD.frobEig_diag]
  simp [twEig]

theorem heckeSide (hL : GlobalTheory.Published.LocalLanglandsGL) {L : Type} [Field L] [NumberField L] [IsCMField L] {Ω : Type}
    [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω} {n : ℕ} (π : NG.AutRep L n) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (hu : IsUnif L s.v ϖ) (J : Subgroup (GAf L n))
    (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) (f : GAf L n → π.W) (hf : f ∈ π.S) (hf0 : f ≠ 0)
    (hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) (c : ℕ → ℂ)
    (hc : ∀ k, 1 ≤ k → k ≤ n → NG.tN J s ϖ k f = c k • f) (hp : IsPlaceOver A (conjSplit s).w)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((conjSplit s).w.adicCompletion L))) (hσ : IsLocS π.S (conjSplit s) σ) :
    ∃ α, GlobalTheory.SmGL.HasSatake σ.ρ α ∧ ∀ k, 1 ≤ k → k ≤ n →
      ((normV (conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k = (twEig (conjSplit s).w α).esymm k := by
  obtain ⟨i, T, hic, hcomp, hinj, hmem, heq⟩ := hσ
  have hf' := GlobalTheory.T.autRep_isotypic_splitPlace_localComponent L n π (conjSplit s) σ i T hinj hmem heq f hf
  obtain ⟨m, Tj, ej, hTj, hej, hsum⟩ := GlobalTheory.T.splitPlace_fixed_vector_sum_spherical_images L n π (conjSplit s) σ i hic hcomp f hf' hfix
  have hne : ∃ j, ej j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf0
    rw [hsum]
    simp [h]
  have hsph : GlobalTheory.SmGL.IsSpherical σ.ρ := by
    obtain ⟨j, hj⟩ := hne
    exact (Submodule.ne_bot_iff _).2 ⟨ej j, hej j, hj⟩
  have hR := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL hp
  obtain ⟨α, hα⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake_of_unr hR ((GlobalTheory.CuspRep.ParLaws.unr_iff hR σ).2 hsph)
  refine ⟨α, hα, fun k hk1 hk2 => ?_⟩
  have hfin := GlobalTheory.T.finite_heckeDoubleCoset_cosets_at_splitPlace L n s ϖ hu J hJ k
  have key : ((normV (conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) • NG.tN J s ϖ k f =
      (twEig (conjSplit s).w α).esymm k • f := by
    conv_lhs => rw [hsum]
    rw [tN_sum J s ϖ k hfin, Finset.smul_sum, hsum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ =>
      GlobalTheory.T.split_place_hecke_operator_eigenvalue_conj_spherical L n s ϖ hu J hJ σ α hα i hic hcomp (Tj j) (hTj j) (ej j) (hej j) k hk1 hk2
  rw [hc k hk1 hk2, smul_smul] at key
  exact smul_left_injective ℂ hf0 key

theorem locPol_eq : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E)
    (w : PlE D.host) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
    IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → ∀ J : Subgroup (GAf D.host.E D.R.nV),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV)) → ∀ f ∈ π.S, f ≠ 0 →
    (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) → ∀ c : ℕ → ℂ,
    (∀ k, 1 ≤ k → k ≤ D.R.nV → NG.tN J s ϖ k f = c k • f) → ∀ x, GlobalTheory.AutQuot.LocAt π w x →
    ((GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) x).lpTw ((1 - (D.R.nV : ℝ)) / 2)).unr ∧
    X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        Polynomial.C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      (Multiset.map (fun α => X - Polynomial.C α)
        ((GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) x).lpTw ((1 - (D.R.nV : ℝ)) / 2)).frobEig).prod := by
  intro hL D π s w ϖ hcw hu J hJ f hf hf0 hfix c hc x hx
  have hw := conjSplit_w D s w hcw
  subst hw
  obtain ⟨σc, hσc, huniq⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV π (conjSplit s)
  obtain ⟨s', σ', h', hσ', hxe⟩ := hx
  have hh := huniq π s' h' σ' (NG.AutRep.iso_equivalence.refl π) hσ'
  have hxc : x = GlobalTheory.LocLanglands.cls σc := eq_of_heq (hxe.symm.trans (cls_heq h' σ' σc hh))
  subst hxc
  obtain ⟨α, hα, heig⟩ := heckeSide hL π s ϖ hu J hJ f hf hf0 hfix c hc (D.nd.plOm.2 _) σc hσc
  obtain ⟨hun, hfe⟩ := galSide hL (D.nd.plOm.2 _) σc α hα
  refine ⟨hun, ?_⟩
  rw [hfe, prod_eq_vieta D.R.nV _ (by simp [twEig])]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
  rw [mul_assoc, heig k hk1 hk2]

end

end GlobalTheory.HeckeFrob

end
