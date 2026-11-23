import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CplxOfFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjAGphiEqSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaReadingLinearInjectiveAtOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxTranslateExponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenMapTranspose
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.SplitClass

open GlobalTheory.SplitScalar

section Adelic

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem exists_rat_sub_mem {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {Λ : AddSubgroup (WO S T)}
    (hΛ : ∃ U : Set (WO S T), IsOpen U ∧ ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ u ∈ U))
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    ∃ γ, (LatVac.finTens 1 γ : WO S T) ∈ (latO S T LS LT fun _ => True) ∧ u - LatVac.finTens 1 γ ∈ Λ := by
  obtain ⟨U, hU, hUΛ⟩ := hΛ
  have hfin : ∀ (α : Af D.host.F) (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E),
      (LatVac.finTens α M : WO S T).map (infPart D) = 0 := fun α M =>
    Matrix.ext fun i j => LatVac.infPart_pair _ _
  refine LatVac.latO_induction (p := fun u => ∃ γ,
    (LatVac.finTens 1 γ : WO S T) ∈ (latO S T LS LT fun _ => True) ∧ u - LatVac.finTens 1 γ ∈ Λ) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    let φ : Af D.host.F →+ WO S T := AddMonoidHom.mk' (fun β => LatVac.finTens β M)
      fun a b => LatVac.finTens_add_left a b M
    let C : AddSubgroup (Af D.host.F) :=
      { carrier := {β | ∃ γ, (LatVac.finTens 1 γ : WO S T) ∈ (latO S T LS LT fun _ => True) ∧
          φ β - LatVac.finTens 1 γ ∈ Λ}
        zero_mem' := ⟨0, by rw [LatVac.finTens_zero]; exact zero_mem _,
          by rw [LatVac.finTens_zero, map_zero, sub_self]; exact zero_mem _⟩
        add_mem' := by
          rintro a b ⟨γ, h1, h2⟩ ⟨γ', h1', h2'⟩
          refine ⟨γ + γ', by rw [LatVac.finTens_add]; exact add_mem h1 h1', ?_⟩
          rw [LatVac.finTens_add, map_add, add_sub_add_comm]
          exact add_mem h2 h2'
        neg_mem' := by
          rintro a ⟨γ, h1, h2⟩
          refine ⟨-γ, by rw [LatVac.finTens_neg]; exact neg_mem h1, ?_⟩
          rw [LatVac.finTens_neg, map_neg, neg_sub_neg, ← neg_sub]
          exact neg_mem h2 }
    have hc := VacSign.continuous_finTens (D := D) M
    have hop : IsOpen (C : Set (Af D.host.F)) := by
      refine C.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset
        ((hU.preimage hc).mem_nhds ?_) fun β hβ => ⟨0, ?_, ?_⟩)
      · refine (hUΛ _ (hfin _ _)).1 ?_
        rw [LatVac.finTens_zero_left]
        exact zero_mem _
      · rw [LatVac.finTens_zero]; exact zero_mem _
      · rw [LatVac.finTens_zero, sub_zero]
        exact (hUΛ _ (hfin _ _)).2 hβ
    refine IntDense.mem_of_isClosed D.host.F (C := (C : Set (Af D.host.F))) (C.isClosed_of_isOpen hop)
      (fun a => ?_) α hα
    have hm : LatVac.finTens (algebraMap D.host.F (Af D.host.F) (a : D.host.F)) M ∈
        latO S T LS LT fun _ => True :=
      LatVac.finTens_mem_latO (fun v => by
        rw [AlgHom.commutes]; exact v.coe_algebraMap_mem (𝓞 D.host.F) D.host.F a) hM
    rw [VacSign.finTens_algebraMap] at hm
    refine ⟨_, hm, ?_⟩
    rw [← VacSign.finTens_algebraMap]
    change LatVac.finTens _ M - LatVac.finTens _ M ∈ Λ
    rw [sub_self]
    exact zero_mem _
  · exact ⟨0, by rw [LatVac.finTens_zero]; exact zero_mem _,
      by rw [LatVac.finTens_zero, sub_self]; exact zero_mem _⟩
  · rintro a b ⟨γ, h1, h2⟩ ⟨γ', h1', h2'⟩
    refine ⟨γ + γ', by rw [LatVac.finTens_add]; exact add_mem h1 h1', ?_⟩
    rw [LatVac.finTens_add, add_sub_add_comm]
    exact add_mem h2 h2'
  · rintro a ⟨γ, h1, h2⟩
    refine ⟨-γ, by rw [LatVac.finTens_neg]; exact neg_mem h1, ?_⟩
    rw [LatVac.finTens_neg, neg_sub_neg, ← neg_sub]
    exact neg_mem h2

theorem exists_reps {G ι : Type} [AddCommGroup G] (Λ : AddSubgroup G) (P : G → Prop) (s : Finset ι) (a : ι → G)
    (h : ∀ u, P u → ∃ i ∈ s, u - a i ∈ Λ) :
    ∃ R : Finset G, (∀ u ∈ R, P u) ∧ ∀ u, P u → ∃! v, v ∈ R ∧ u - v ∈ Λ := by
  have hfin : (QuotientAddGroup.mk '' {u | P u} : Set (G ⧸ Λ)).Finite := by
    refine ((s.finite_toSet).image fun i => (QuotientAddGroup.mk (a i) : G ⧸ Λ)).subset ?_
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨i, hi, h⟩ := h u hu
    exact ⟨i, hi, (QuotientAddGroup.eq_iff_sub_mem.2 h).symm⟩
  obtain ⟨t, ht, hb⟩ := Set.exists_subset_bijOn {u | P u} (QuotientAddGroup.mk : G → G ⧸ Λ)
  have htf : t.Finite := Set.Finite.of_finite_image (hb.image_eq ▸ hfin) hb.injOn
  refine ⟨htf.toFinset, fun u hu => ht (htf.mem_toFinset.1 hu), fun u hu => ?_⟩
  obtain ⟨v, hv, h⟩ := hb.surjOn ⟨u, hu, rfl⟩
  refine ⟨v, ⟨htf.mem_toFinset.2 hv, QuotientAddGroup.eq_iff_sub_mem.1 h.symm⟩, fun v' hv' => ?_⟩
  exact hb.injOn (htf.mem_toFinset.1 hv'.1) hv ((QuotientAddGroup.eq_iff_sub_mem.2 hv'.2).symm.trans h.symm)

set_option maxHeartbeats 800000 in

theorem om_eq_smul_sum {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (hS : S.SigOK) (hT : T.SigOK) {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hsS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ))
    (hsT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS ΛS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛS' : IsSelfDualC S ΛS') (hΛT : IsSelfDualC T ΛT) {e : AE D} (he : IsSplitIdem D e)
    {h : GA D S} (hh : SuppAt e S h) {y : (AE D)ˣ} (hy : IsDetAt e S h y) {Λ Λ' : AddSubgroup (WO S T)}
    (hΛ : Λ = latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (hΛ' : Λ' = latO S T (ΛS' : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (hmove : ∀ u : WO S T, u ∈ Λ' ↔ ∃ u₀ ∈ Λ, u = actO S T h 1 u₀) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS ΛT f) {ι : Type} (s : Finset ι) (a : ι → WO S T) (c : ι → ℂ)
    (ha : ∀ i ∈ s, a i ∈ Λ') (hc : ∀ i ∈ s, ‖c i‖ = 1) (hex : ∀ u ∈ Λ', ∃ i ∈ s, u - a i ∈ Λ)
    (hun : ∀ i ∈ s, ∀ j ∈ s, a i - a j ∈ Λ → i = j)
    (hsg : ∀ F, IsThetaFunO ψ S T F → IsLatVac (heisO ψ S T) Λ' F → ∀ i ∈ s, c i • heisO ψ S T (a i) F = F)
    (hG : IsLatVac (heisO ψ S T) Λ' (∑ i ∈ s, c i • heisO ψ S T (a i) f)) :
    om (h, 1) f = (((χT y : Circle) : ℂ)⁻¹ * ((Real.sqrt (s.card : ℝ) : ℝ) : ℂ)⁻¹) •
      ∑ i ∈ s, c i • heisO ψ S T (a i) f := by
  have he' := isSplitIdem_conj he
  have hψ := hW.std
  have hm1 : Formalism.L2.Theta.mt T (1 : GA D T) = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one]
  have h1 : SuppAt e T 1 := fun i j => by rw [hm1, sub_self, Matrix.zero_apply, mul_zero]
  have h1' : IsDetAt e T 1 1 := by
    unfold IsDetAt
    rw [hm1, Matrix.det_one, mul_one, add_sub_cancel, Units.val_one]
  obtain ⟨R, hR, hRu⟩ := exists_reps Λ (fun u => u ∈ Λ' ∧ IsHalf e u) s a fun u hu => hex u hu.1
  obtain ⟨R', hR', hRu'⟩ := exists_reps Λ (fun u => u ∈ Λ' ∧ IsHalf (cA D e) u) s a fun u hu => hex u hu.1
  have hmain := om_vacuum_eq_splitFac_smul_sum D ψ θ S T χS χT om hW hθ hS hT sS sT hsS hsT ΛS ΛS' ΛT ΛT hΛS hΛS'
    hΛT hΛT e he h 1 hh h1 y 1 hy h1' (hΛ ▸ hΛ' ▸ hmove) R R' (hΛ' ▸ hR)
    (hΛ ▸ hΛ' ▸ fun u hu hue => hRu u ⟨hu, hue⟩) (hΛ' ▸ hR') (hΛ ▸ hΛ' ▸ fun u hu hue => hRu' u ⟨hu, hue⟩) f hf
  obtain ⟨hd, -, hsign⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hΛS hΛT
  obtain ⟨hd', -, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS' ΛT hψ hΛS' hΛT
  obtain ⟨-, hom⟩ := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ h 1
    (fun τ => by rw [compAt_mt he hh, mul_one, one_mul]) (fun τ => by rw [compAt_mt he h1, mul_one, one_mul])
    (hΛ ▸ hΛ' ▸ hmove) f hf
  have hfin' := @latO_fin D S T ΛS' ΛT
  obtain ⟨-, hf⟩ := hf
  rw [← hΛ] at hd hsign hf
  rw [← hΛ'] at hd' hom hfin'
  have hdd : ∀ u ∈ Λ', ∀ u' ∈ Λ', ψ (symplO S T u u') = 1 := fun u hu => (hd' u (hfin' hu)).1 hu
  obtain ⟨G, hGdef⟩ : ∃ G, G = ∑ i ∈ s, c i • heisO ψ S T (a i) f := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℂ, k = (splitFacO χS χT y 1 : ℂ) * ((Real.sqrt ((R.card : ℝ) * R'.card) : ℝ) : ℂ)⁻¹ :=
    ⟨_, rfl⟩
  have key : (s.card : ℂ) • om (h, 1) f = (k * ((R.card : ℂ) * R'.card)) • G := by
    have e1 : (s.card : ℂ) • om (h, 1) f = ∑ i ∈ s, c i • heisO ψ S T (a i) (om (h, 1) f) := by
      rw [Finset.sum_congr rfl (hsg _ hom.theta hom.lat), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    have e2 : ∑ u ∈ R, ∑ u' ∈ R', heisO ψ S T u (heisO ψ S T u' G) = ((R.card : ℂ) * R'.card) • G := by
      rw [← hGdef] at hG
      rw [Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' hu' => by
        rw [hG.2 _ he' u' (hR' u' hu').1 (hR' u' hu').2, hG.2 _ he u (hR u hu).1 (hR u hu).2],
        Finset.sum_const, Finset.sum_const, mul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rw [e1, mul_smul, ← e2, hmain, ← hk, hGdef]
    simp only [heisO_smul, heisO_sum, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u' hu' => Finset.sum_congr rfl fun i hi => ?_
    rw [heisO_comm ψ S T (a i), hdd _ (ha i hi) _ (hR u hu).1, one_smul, heisO_comm ψ S T (a i),
      hdd _ (ha i hi) _ (hR' u' hu').1, one_smul, smul_comm]
  obtain ⟨p, hp⟩ := hf.norm.1
  have hn : nrm2 p.1 p.2 G = s.card := by
    rw [hGdef]
    refine GlobalTheory.HeisOrtho.thetaNormSq_sum_heisenbergTranslates_distinctChars D ψ S T hψ.1 p.1 p.2 hp f hf.theta (hf.norm.2 p hp) _ _ _ _ hc
      fun i hi j hj hne => ?_
    have hnot : a i - a j ∉ Λ := fun hm => hne (hun i hi j hj hm)
    rw [hd _ (hfin' (sub_mem (ha i hi) (ha j hj)))] at hnot
    push Not at hnot
    obtain ⟨l, hl, hne'⟩ := hnot
    obtain ⟨ε, hε, hεf⟩ := hsign f hf.lat l hl
    exact ⟨l, ε, by rcases hε with rfl | rfl <;> simp, hεf f hf.lat, hne'⟩
  obtain ⟨i₀, hi₀, -⟩ := hex 0 (zero_mem _)
  have hs0 : (0 : ℝ) < s.card := Nat.cast_pos.2 (Finset.card_pos.2 ⟨i₀, hi₀⟩)
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (s.card : ℝ)⁻¹ * ((Real.sqrt ((R.card : ℝ) * R'.card))⁻¹ * (R.card * R'.card)) :=
    ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hχ : ‖((χT y : Circle) : ℂ)⁻¹‖ = 1 := by rw [norm_inv, Circle.norm_coe, inv_one]
  have e3 : om (h, 1) f = ((χT y : Circle) : ℂ)⁻¹ • (t : ℂ) • G := by
    have hs0' : (s.card : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    rw [← inv_smul_smul₀ hs0' (om (h, 1) f), key, hk, splitFacO, map_one, mul_one, smul_smul, smul_smul, ht,
      Circle.coe_inv]
    congr 1
    push_cast
    ring
  have e4 : t ^ 2 * s.card = 1 := by
    have := hom.norm.2 p hp
    rw [← hn, ← pairNorm_smul, ← this, e3]
    unfold nrm2
    simp only [Pi.smul_apply (((χT y : Circle) : ℂ)⁻¹), norm_smul, hχ, one_mul]
  have e5 : t = (Real.sqrt (s.card : ℝ))⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_sq ht0, eq_inv_of_mul_eq_one_left e4]
  rw [e3, ← hGdef, smul_smul, e5, Complex.ofReal_inv]

end Adelic

section Reading

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {r g : ℕ} {hr : W.rank = r}
  {X : Data D.host.E r} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {x : Frame X.Ψ r}

def rowsC {E : Type} {m n : ℕ} (hr : m = r) (y : Matrix (Fin n) (Fin r) E) : Matrix (Fin m) (Fin n) E :=
  fun a b => y b (Fin.cast hr a)

theorem colsR_rowsC {E : Type} {m n : ℕ} (hr : m = r) (y : Matrix (Fin n) (Fin r) E) :
    colsR hr (rowsC hr y) = y := by
  subst hr
  rfl

theorem colsR_sub {E : Type} [AddCommGroup E] {m n : ℕ} (hr : m = r) (γ γ' : Matrix (Fin m) (Fin n) E) :
    colsR hr (γ - γ') = colsR hr γ - colsR hr γ' := rfl

theorem finTens_sub {m n : ℕ} (M N : Matrix (Fin m) (Fin n) D.host.E) :
    LatVac.finTens (D := D) 1 (M - N) = LatVac.finTens 1 M - LatVac.finTens 1 N := by
  rw [sub_eq_add_neg, LatVac.finTens_add, LatVac.finTens_neg, sub_eq_add_neg]

theorem epsW_neg {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (X : Data E r) (w : E)
    (y : Matrix (Fin n) (Fin r) E) : epsW X w (-y) = epsW X w y := by
  simp only [epsW, TensLat.EF_eq_bilin]
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (-y) k = -y k from rfl, smul_neg, map_neg, map_neg, LinearMap.neg_apply, neg_neg]

theorem norm_epsW {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (X : Data E r) (w : E)
    (y : Matrix (Fin n) (Fin r) E) : ‖epsW X w y‖ = 1 := by
  have := congrArg norm (TensVac.epsW_mul_conj (X := X) w y)
  rw [norm_mul, Complex.norm_conj, norm_one] at this
  exact (mul_self_eq_one_iff.1 this).resolve_right fun h => by linarith [norm_nonneg (epsW X w y)]

theorem reads_smul
    (hl : ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x →
      Reads θ V W hr X bas idx f' φ' x → ∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x)
    {f : WO V W → ℂ} {φ : TF V.rank g} (h : Reads θ V W hr X bas idx f φ x) (a : ℂ) :
    Reads θ V W hr X bas idx (a • f) (a • φ) x := by
  have := hl f f φ φ h h a 0
  rwa [zero_smul, zero_smul, add_zero, add_zero] at this

theorem reads_sum
    (hl : ∀ (f f' : WO V W → ℂ) (φ φ' : TF V.rank g), Reads θ V W hr X bas idx f φ x →
      Reads θ V W hr X bas idx f' φ' x → ∀ a b : ℂ, Reads θ V W hr X bas idx (a • f + b • f') (a • φ + b • φ') x)
    {f₀ : WO V W → ℂ} {φ₀ : TF V.rank g} (h₀ : Reads θ V W hr X bas idx f₀ φ₀ x) {ι : Type} (s : Finset ι)
    (c : ι → ℂ) {f : ι → WO V W → ℂ} {φ : ι → TF V.rank g} (h : ∀ i, Reads θ V W hr X bas idx (f i) (φ i) x) :
    Reads θ V W hr X bas idx (∑ i ∈ s, c i • f i) (∑ i ∈ s, c i • φ i) x := by
  induction s using Finset.induction_on with
  | empty =>
    have := reads_smul hl h₀ 0
    rwa [zero_smul, zero_smul] at this
  | insert i s hi ih =>
    have := hl _ _ _ _ (h i) ih (c i) 1
    rwa [one_smul, one_smul, ← Finset.sum_insert (f := fun i => c i • f i) hi,
      ← Finset.sum_insert (f := fun i => c i • φ i) hi] at this

end Reading

set_option maxHeartbeats 800000 in

theorem reads_om_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (ΛV₁ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' Λ₁ : Lt D.host.E V.rank) (L : Lt D.host.E r), IsSelfDualC V ΛV → IsSelfDualC V ΛV₁ → IsSelfDualC W ΛW → (∀ v : Fin V.rank → D.host.E, v ∈ Λ' ↔ (fun j => star (v j)) ∈ ΛV) → (∀ v : Fin V.rank → D.host.E, v ∈ Λ₁ ↔ (fun j => star (v j)) ∈ ΛV₁) → (∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L₀ = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ ΛW, w = a • v} → L = latR hr L₀) → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ φ : TF V.rank g, Reads θ V W hr X bas idx f φ x → ∀ (e : AE D) (h : GA D V) (y : (AE D)ˣ), IsSplitIdem D e → SuppAt e V h → IsDetAt e V h y → (∀ u : WO V W, u ∈ (latO V W (ΛV₁ : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), u = actO V W h 1 u₀) → Reads θ V W hr X bas idx (om (h, 1) f) ((((χW y : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ₁ ⊓ Λ').toAddSubgroup.addSubgroupOf Λ₁.toAddSubgroup).index : ℝ) ^ r) : ℂ)) • projA X bas (H.w0 : D.host.E) (tens Λ₁ L) φ) x := by
  intro D ψ θ V W χV χW om hP r g hr X bas idx hX hs H hH ΛV ΛW ΛV₁ Λ' Λ₁ L hΛV hΛV₁ hΛW hΛ' hΛ₁ hL x s hx hxs f hf
    φ hφ e h y he hh hy hmove
  have hψ := hP.weil.std
  have hn := hP.even
  have hw0 : (H.w0 : D.host.E) + cc (H.w0 : D.host.E) = 1 := by
    have h1 : 2 * (H.w0 : D.host.E) = 1 + D.host.sqrtMinusD := by
      rw [← hH]; exact congrArg Subtype.val H.two_weight_eq_one_add_root
    have h2 := congrArg star h1
    rw [star_mul', star_add, star_one, star_ofNat, SplitIdem.star_eq_conj D D.host.sqrtMinusD,
      D.host.conj_sqrtMinusD] at h2
    change (H.w0 : D.host.E) + star (H.w0 : D.host.E) = 1
    linear_combination (1 / 2 : D.host.E) * h1 + (1 / 2 : D.host.E) * h2
  have hwi : IsIntegral ℤ (H.w0 : D.host.E) := H.w0.isIntegral_coe
  obtain ⟨cW, cV, -⟩ := FrameCplx.cplx_of_frame D ψ θ V W r g hr X bas idx hψ hP.inf hP.std hn hX hs x s hx hxs
  obtain ⟨l0, hSD, u0, f0⟩ :=
    LatOf.isLatOf_tens D ψ θ V W r g hr X bas idx hψ hP.inf hP.std hn hX hs ΛV ΛW Λ' L hΛV hΛW hΛ' hL
  obtain ⟨l1, -, u1, f1⟩ :=
    LatOf.isLatOf_tens D ψ θ V W r g hr X bas idx hψ hP.inf hP.std hn hX hs ΛV₁ ΛW Λ₁ L hΛV₁ hΛW hΛ₁ hL
  have lin := reads_linear_injective D ψ θ V W r g hr X bas idx hψ hP.inf hP.std hn hX hs x hx
  have hl := fun f f' φ φ' h h' => (lin f f' φ φ' h h').1
  have Heisenberg₂ := reads_heisO_finOf D ψ θ V W r g hr X bas idx hψ hP.inf hP.std hn hX hs x hx
  have eps0 := VacSign.isLatVac_iff_epsW D ψ θ V W r g hr X bas idx hψ hP.inf hP.std hn hX hs H hH ΛV ΛW hΛV hΛW
  have eps1 := VacSign.isLatVac_iff_epsW D ψ θ V W r g hr X bas idx hψ hP.inf hP.std hn hX hs H hH ΛV₁ ΛW hΛV₁ hΛW
  obtain ⟨a1, a2, a3, -⟩ := TensLat.tens_selfDual_semichar_index _ r X g bas idx _ hs hn _ hwi hw0 L hSD 1 _
    (VacProj.mem_vset ⟨Λ'⟩ u0 f0)
  obtain ⟨b1, b2, b3, -⟩ := TensLat.tens_selfDual_semichar_index _ r X g bas idx _ hs hn _ hwi hw0 L hSD 1 _
    (VacProj.mem_vset ⟨Λ₁⟩ u1 f1)
  have g0 : TensVac.Good X (H.w0 : D.host.E) (tens Λ' L) := ⟨a1, a2, a3⟩
  have g1 : TensVac.Good X (H.w0 : D.host.E) (tens Λ₁ L) := ⟨b1, b2, b3⟩
  obtain ⟨v, hv, hvu⟩ := g0.vac hs
  obtain ⟨v₁, hv₁, -⟩ := g1.vac hs
  have hfin : ∀ z, IsFinOf V W (rowsC hr (-z)) (LatVac.finTens 1 (rowsC hr (-z))) := fun z =>
    (VacSign.isFinOf_iff _ _).2 rfl
  have hrd : ∀ F φ', IsThetaFunO ψ V W F → Reads θ V W hr X bas idx F φ' x → ∀ z,
      Reads θ V W hr X bas idx (heisO ψ V W (LatVac.finTens 1 (rowsC hr (-z))) F) (heisG X bas z φ') x := by
    intro F φ' hF hr' z
    have := Heisenberg₂ F φ' hF hr' _ _ (hfin z)
    rwa [colsR_rowsC, neg_neg] at this
  obtain ⟨κ, rfl⟩ : ∃ κ : ℂ, φ = κ • v := by
    refine hvu φ hφ.1 fun z hz => ?_
    have h1 := (eps0 f hf.2.theta).1 hf.2.lat _ _ (hfin z)
      ((l0.rat _ _ (hfin z)).2 (by rw [colsR_rowsC]; exact neg_mem hz))
    rw [colsR_rowsC, epsW_neg] at h1
    rw [(lin _ _ _ _ (hrd f φ hf.2.theta hφ z) (reads_smul hl hφ _)).2.1 h1, smul_smul, ← sq, (a3 z hz).1, one_smul]
  have hidx : (tens Λ' L).relIndex (tens Λ₁ L) ≠ 0 := by
    intro h0
    have := g1.overlap idx hs hn g0 hv₁ hv
    rw [h0, Nat.cast_zero, zero_mul] at this
    exact zero_ne_one this
  haveI : ((tens Λ' L).addSubgroupOf (tens Λ₁ L)).FiniteIndex := ⟨hidx⟩
  haveI := Fintype.ofFinite (tens Λ₁ L ⧸ (tens Λ' L).addSubgroupOf (tens Λ₁ L))
  obtain ⟨R, hR, hRu⟩ := exists_reps (tens Λ' L) (fun z => z ∈ tens Λ₁ L) Finset.univ
    (fun q : tens Λ₁ L ⧸ (tens Λ' L).addSubgroupOf (tens Λ₁ L) => (q.out : Matrix (Fin V.rank) (Fin r) D.host.E))
    fun z hz => ⟨QuotientAddGroup.mk ⟨z, hz⟩, Finset.mem_univ _,
      AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq_iff_sub_mem.1 (QuotientAddGroup.out_eq'
        (QuotientAddGroup.mk ⟨z, hz⟩ : tens Λ₁ L ⧸ (tens Λ' L).addSubgroupOf (tens Λ₁ L))).symm)⟩
  obtain ⟨c1, c2, c3, -⟩ := VacProj.projA_gphi_eq_sum _ r g _ X bas idx hs hn _ hwi hw0 L hSD ⟨Λ'⟩ ⟨Λ₁⟩ u0 u1 f0 f1
    v hv R hR hRu
  dsimp only at c1 c2 c3
  obtain ⟨z₀, ⟨hz₀, -⟩, -⟩ := hRu 0 (zero_mem _)
  have hc0 : (0 : ℝ) < R.card := Nat.cast_pos.2 (Finset.card_pos.2 ⟨z₀, hz₀⟩)
  have hc0' : (R.card : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hsq : (Real.sqrt (R.card : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hc0).ne'
  have hproj : projA X bas (H.w0 : D.host.E) (tens Λ₁ L) (κ • v) =
      κ • projA X bas (H.w0 : D.host.E) (tens Λ₁ L) v := by
    rw [(g1.proj idx hs hn hφ.1 hv₁).2, (g1.proj idx hs hn hv.1 hv₁).2, TensVac.ip_smul_left κ hv.1 hv₁.1, mul_smul]
  have hG := reads_sum hl hφ R (epsW X (H.w0 : D.host.E)) (hrd f _ hf.2.theta hφ)
  have hsum : ∑ z ∈ R, epsW X (H.w0 : D.host.E) z • heisG X bas z (κ • v) =
      (κ * (Real.sqrt (R.card : ℝ) : ℂ)) • (Real.sqrt (R.card : ℝ) : ℂ) •
        projA X bas (H.w0 : D.host.E) (tens Λ₁ L) v := by
    rw [c2, smul_smul, smul_smul, mul_assoc κ, ← Complex.ofReal_mul, Real.mul_self_sqrt hc0.le,
      Complex.ofReal_natCast, mul_inv_cancel_right₀ hc0', Finset.smul_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [TensVac.heisG_smul, smul_comm]
  rw [hsum] at hG
  have hGth := FinTranslate.isTheta_sum_heisO_fin D ψ V W hψ.1 f hf.2.theta _ R
    (fun z => LatVac.finTens 1 (rowsC hr (-z))) (epsW X (H.w0 : D.host.E)) fun z _ => (hfin z).1
  have hmem : ∀ z ∈ R, (LatVac.finTens 1 (rowsC hr (-z)) : WO V W) ∈ latO V W (ΛV₁ : Set (Fin V.rank → D.host.E))
      (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True := fun z hz =>
    (l1.rat _ _ (hfin z)).2 (by rw [colsR_rowsC]; exact neg_mem (hR z hz))
  have hdiff : ∀ γ z, (LatVac.finTens 1 γ - LatVac.finTens 1 (rowsC hr (-z)) : WO V W) ∈
      (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔
        -colsR hr γ - z ∈ tens Λ' L := by
    intro γ z
    rw [← finTens_sub, l0.rat _ _ ((VacSign.isFinOf_iff _ _).2 rfl), colsR_sub, colsR_rowsC, ← neg_mem_iff]
    congr! 1
    abel
  have hom := om_eq_smul_sum hP.weil hP.inf hP.sigV hP.sigW cV cW hΛV hΛV₁ hΛW he hh hy rfl rfl hmove hf R
    (fun z => LatVac.finTens 1 (rowsC hr (-z))) (epsW X (H.w0 : D.host.E)) hmem (fun z _ => norm_epsW X _ z)
    (fun u hu => by
      obtain ⟨γ, h1, h2⟩ := exists_rat_sub_mem l0.opn hu
      obtain ⟨z, ⟨hz, h3⟩, -⟩ := hRu _ (neg_mem ((l1.rat _ _ ((VacSign.isFinOf_iff _ _).2 rfl)).1 h1))
      refine ⟨z, hz, ?_⟩
      rw [← sub_add_sub_cancel]
      exact add_mem h2 ((hdiff γ z).2 h3))
    (fun z hz z' hz' hm => by
      rw [hdiff, colsR_rowsC, neg_neg] at hm
      exact (hRu z (hR z hz)).unique ⟨hz, by rw [sub_self]; exact zero_mem _⟩ ⟨hz', hm⟩)
    (fun F hF hFl z hz => by
      rw [(eps1 F hF).1 hFl _ _ (hfin z) (hmem z hz), colsR_rowsC, epsW_neg, smul_smul, ← sq, (b3 z (hR z hz)).1,
        one_smul])
    ((eps1 _ hGth).2 fun γ u hu hm => by
      have hz := neg_mem ((l1.rat _ _ hu).1 hm)
      have hth := FinTranslate.isTheta_sum_heisO_fin D ψ V W hψ.1 _ hGth Unit {()} (fun _ => u) (fun _ => 1)
        fun _ _ => hu.1
      rw [Finset.sum_singleton, one_smul] at hth
      have hth' := FinTranslate.isTheta_sum_heisO_fin D ψ V W hψ.1 _ hGth Unit {()} (fun _ => 0)
        (fun _ => epsW X (H.w0 : D.host.E) (colsR hr γ)) fun _ _ => Matrix.ext fun _ _ => (infPart D).map_zero
      rw [Finset.sum_singleton, heisO_zero] at hth'
      refine (lin _ _ _ _ (Heisenberg₂ _ _ hGth hG γ u hu) (reads_smul hl hG _)).2.2 hth hth' ?_
      rw [TensVac.heisG_smul, smul_comm (epsW X _ _), ← epsW_neg]
      congr 1
      conv_rhs => rw [← c3.2.2 _ hz]
      rw [smul_smul, ← sq, (b3 _ hz).1, one_smul])
  have := reads_smul hl hG (((χW y : Circle) : ℂ)⁻¹ * ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ)⁻¹)
  rw [← hom, smul_smul, smul_smul] at this
  rw [hproj, smul_smul, ← Nat.cast_pow, ← c1]
  convert this using 2
  field_simp

end GlobalTheory.AdTh.SplitClass

end
