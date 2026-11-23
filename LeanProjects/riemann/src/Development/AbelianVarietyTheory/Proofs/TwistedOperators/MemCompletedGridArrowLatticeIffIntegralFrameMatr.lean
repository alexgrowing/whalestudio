import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.RowLatChi
open Matrix ValuativeRel
open scoped TensorProduct

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem smul_mem_latRat (hS : IsSelfDualC S ΛS) {a : D.host.E} (ha : a ∈ D.host.AA)
    {x : Matrix (Fin T.rank) (Fin S.rank) D.host.E} (hx : x ∈ homLat ΛS ΛT) :
    a • x ∈ GlobalTheory.LatVac.latRat S T (ΛS : Set _) (ΛT : Set _) := by
  obtain ⟨m, s, s', hs, hs', hdual⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hS
  have e : a • x = ∑ l, GlobalTheory.LatVac.genMap S T a (s' l) (x *ᵥ s l) := by
    ext p q
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, GlobalTheory.LatVac.genMap, Matrix.of_apply, Matrix.mulVec,
      dotProduct]
    have h2 : ∀ l, a * (∑ r, x p r * s l r) * (∑ k, star (s' l k) * HSpace.gram S k q) =
        ∑ r, a * x p r * (s l r * ∑ k, star (s' l k) * HSpace.gram S k q) := fun l => by
      rw [mul_comm a, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [Finset.sum_congr rfl fun l _ => h2 l, Finset.sum_comm]
    simp only [← Finset.mul_sum, hdual]
    simp
  rw [e]
  exact sum_mem fun l _ => AddSubgroup.subset_closure ⟨a, ha, s' l, hs' l, x *ᵥ s l, hx _ (hs l), rfl⟩

theorem fr_neg {A : Type} [CommRing A] {m n : ℕ} (β' : GL (Fin m) A) (β : GL (Fin n) A) (x : Matrix (Fin m) (Fin n) A) :
    Comparison₂.fr β' β (-x) = -Comparison₂.fr β' β x := by rw [Comparison₂.fr, Comparison₂.fr, Matrix.mul_neg, Matrix.neg_mul]

theorem genMap_one_mem_homLat (hS : IsSelfDualC S ΛS) {s : Fin S.rank → D.host.E} (hs : s ∈ ΛS)
    {t : Fin T.rank → D.host.E} (ht : t ∈ ΛT) : GlobalTheory.LatVac.genMap S T 1 s t ∈ homLat ΛS ΛT := by
  intro y hy
  obtain ⟨b, hb⟩ := (hS.2 y).1 hy s hs
  have e : GlobalTheory.LatVac.genMap S T 1 s t *ᵥ y = (b : D.host.E) • t := by
    funext i
    simp only [GlobalTheory.LatVac.genMap, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, hb,
      Finset.sum_mul, Finset.mul_sum, one_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact ΛT.smul_mem b ht

theorem tmul_eq (α : Af D.host.F) (c y : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * y) = (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) * incA D c) * incA D y := by
  change _ = (_ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] c)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y)
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul]

set_option maxHeartbeats 1000000 in

theorem int_of_mem_latO (hS : IsSelfDualC S ΛS) {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT) (w : Pl D.host.E)
    (hw : ∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) (a : Fin T.rank) (b : Fin S.rank) :
    Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (u.map (toEAf D)) a b)) ≤ 1 := by
  let p : WO S T → Prop := fun u => ∀ a b, Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (u.map (toEAf D)) a b)) ≤ 1
  have hadd : ∀ x y, p x → p y → p (x + y) := fun x y hx hy a b => by
    rw [Matrix.map_add _ (toEAf D).map_add, Comparison₂.fr_add, Matrix.add_apply, RingHom.map_add]
    exact Valuation.map_add_le _ (hx a b) (hy a b)
  have hneg : ∀ x, p x → p (-x) := fun x hx a b => by
    rw [Matrix.map_neg _ (toEAf D).map_neg, fr_neg, Matrix.neg_apply, RingHom.map_neg, Valuation.map_neg]
    exact hx a b
  have hzero : p 0 := fun a b => by
    rw [Matrix.map_zero _ (toEAf D).map_zero, show Comparison₂.fr βT βS (0 : Matrix (Fin T.rank) (Fin S.rank) (EAf D)) = 0 by
      rw [Comparison₂.fr, Matrix.mul_zero, Matrix.zero_mul]]
    simp
  refine GlobalTheory.LatVac.latO_induction (p := p) (fun α hα M hM => ?_) hzero hadd hneg hu a b
  induction hM using AddSubgroup.closure_induction with
  | mem M hM =>
    obtain ⟨c, hc, s, hs, t, ht, rfl⟩ := hM
    set Y := GlobalTheory.LatVac.genMap S T 1 s t
    have hY : Y ∈ homLat ΛS ΛT := genMap_one_mem_homLat hS hs ht
    have e1 : (GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T c s t) : WO S T).map (toEAf D) =
        toEAf D ((pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D c) • Y.map (eToEAf D) := by
      ext i j
      simp only [GlobalTheory.LatVac.finTens, Y, GlobalTheory.LatVac.genMap, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
        smul_eq_mul]
      rw [show c * t i * ∑ k, star (s k) * HSpace.gram S k j = c * (1 * t i * ∑ k, star (s k) * HSpace.gram S k j) by ring,
        tmul_eq, RingHom.map_mul]
      rfl
    intro a b
    rw [e1, Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, RingHom.map_mul, Valuation.map_mul,
      RingHom.map_mul, Valuation.map_mul]
    have h1 : Valued.v (cpt (D := D) w (toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)))) ≤ 1 := by
      have hi : finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩
      exact ((comp_toAd D).int (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E))).1 hi w
    have h2 : Valued.v (cpt (D := D) w (toEAf D (incA D c))) ≤ 1 := by
      rw [show cpt (D := D) w (toEAf D (incA D c)) = algebraMap D.host.E (Kw w) c from Comparison₂.cpt_tmul w c]
      exact hw c hc
    have h3 : Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (Y.map (eToEAf D)) a b)) ≤ 1 := by
      obtain ⟨s', -, hs'⟩ := Comparison₂.fr_mem_idS hβS hβT (𝔪 := ⊤) (by rw [Submodule.top_smul]; exact hY) a b
      have h4 := (mem_OA_iff _).1 s'.2 w
      rw [hs'] at h4
      exact h4
    exact mul_le_one' (mul_le_one' h1 h2) h3
  | zero => rw [GlobalTheory.LatVac.finTens_zero]; exact hzero
  | add x y _ _ hx hy => rw [GlobalTheory.LatVac.finTens_add]; exact hadd _ _ hx hy
  | neg x _ hx => rw [GlobalTheory.LatVac.finTens_neg]; exact hneg _ hx

theorem mem_hatMx_of_int {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT) {e₁ : AE D} {P₁ : Finset (Pl D.host.E)} (he : IsIdemSum e₁ P₁)
    {u : WO S T} (hu : IsHalf e₁ u)
    (h : ∀ w ∈ P₁, ∀ a b, Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (u.map (toEAf D)) a b)) ≤ 1) :
    u ∈ hatMx (homLat ΛS ΛT) := by
  obtain ⟨e0, -, e2⟩ := Comparison₂.cpt_idemSum he
  have hfr : ∀ a b, Comparison₂.fr βT βS (u.map (toEAf D)) a b = toEAf D e₁ * Comparison₂.fr βT βS (u.map (toEAf D)) a b := by
    intro a b
    have hm : u.map (toEAf D) = toEAf D e₁ • u.map (toEAf D) := Matrix.ext fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, ← RingHom.map_mul, hu i j]
    conv_lhs => rw [hm, Comparison₂.fr_smul]
    rfl
  rw [← Submodule.top_smul (homLat ΛS ΛT), HatFrame.mem_hatMx_homLat_iff D ΛS ΛT βS βT hβS hβT ⊤ u]
  refine ⟨fun a b => by rw [← hu a b, RingHom.map_mul, e0, zero_mul], fun a b => ?_⟩
  refine ⟨⟨Comparison₂.fr βT βS (u.map (toEAf D)) a b, (mem_OA_iff _).2 fun Q => ?_⟩, ?_, rfl⟩
  · by_cases hQ : Q ∈ P₁
    · exact h Q hQ a b
    · rw [hfr, RingHom.map_mul, e2 Q hQ, zero_mul]; exact zero_mem _
  · unfold idS; rw [Ideal.map_top]; exact Submodule.mem_top

theorem smul_mem_latO_of_mem_hatMx (hS : IsSelfDualC S ΛS) {a : D.host.E} (ha : a ∈ D.host.AA) {u : WO S T}
    (hm : u ∈ hatMx (homLat ΛS ΛT)) : incA D a • u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True := by
  induction hm using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hv
    have e : incA D a • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] x i j : WO S T) =
        GlobalTheory.LatVac.finTens α (a • x) := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.of_apply, GlobalTheory.LatVac.finTens, Matrix.map_apply, smul_eq_mul]
      change ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] x i j) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e]
    exact GlobalTheory.LatVac.finTens_mem_latO hα (smul_mem_latRat hS ha hx)
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

set_option maxHeartbeats 1000000 in

theorem mem_latO_of_mem_hatMx (hS : IsSelfDualC S ΛS) {e₁ : AE D} {P₁ : Finset (Pl D.host.E)} (he : IsIdemSum e₁ P₁)
    (hAA : ∀ w ∈ P₁, ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) {u : WO S T} (hu : IsHalf e₁ u)
    (hm : u ∈ hatMx (homLat ΛS ΛT)) : u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hxe : (∑ PP ∈ P₁, es PP) • u = u := Matrix.ext fun i j => hu i j
  rw [← hxe, Finset.sum_smul]
  refine sum_mem fun w hw => ?_
  obtain ⟨a, ha, hv⟩ := hAA w hw
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, Valuation.map_zero] at hv
    exact zero_ne_one hv
  have hc : finPart D (es w * incA D a⁻¹) ∈ intAE D := by
    refine ((comp_toAd D).int (es w * incA D a⁻¹)).2 fun Q => ?_
    show Valued.v (cpt (D := D) Q (toEAf D (es w * incA D a⁻¹))) ≤ 1
    obtain ⟨h1, h2⟩ := cpt_of_isIdemAt (hes w hw)
    rw [RingHom.map_mul, RingHom.map_mul,
      show cpt (D := D) Q (toEAf D (incA D a⁻¹)) = algebraMap D.host.E (Kw Q) a⁻¹ from Comparison₂.cpt_tmul Q a⁻¹]
    rcases eq_or_ne Q w with rfl | hQ
    · rw [h1, one_mul, map_inv₀, map_inv₀, hv, inv_one]
    · rw [h2 Q hQ, zero_mul, Valuation.map_zero]
      exact zero_le
  have e : es w • u = (es w * incA D a⁻¹) • (incA D a • u) := by
    rw [smul_smul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ ha0, RingHom.map_one, mul_one]
  rw [e]
  exact GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hc _ (smul_mem_latO_of_mem_hatMx hS ha hm)

theorem intM_iff (w : Pl D.host.E) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (Kw w)) :
    GlobalTheory.StepData.IntM M ↔ ∀ a b, Valued.v (M a b) ≤ 1 := by
  refine forall₂_congr fun a b => ?_
  rw [Valuation.mem_integer_iff, ← map_one (valuation (Kw w))]
  rw [(Comparison₂.vEq w) (M a b) 1, map_one]

end GlobalTheory.RowLatChi

open GlobalTheory.RowLatChi in

theorem GlobalTheory.RowLatChi.mem_latO_iff_intM : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) {e₁ : AE D} {P₁ : Finset (Pl D.host.E)}, IsIdemSum e₁ P₁ → (∀ w ∈ P₁, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ (i : Fin D.R.m) (z : WO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0))), IsHalf e₁ z → (z ∈ (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _) (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) ↔ ∀ w ∈ P₁, GlobalTheory.StepData.IntM (B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0)) ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (z.map (cpt (D := D) w ∘ toEAf D)))) := by
  intro D T L sc G μ₀ hL B t e₁ P₁ hI hAA i z hz
  have hi : (i : ℕ) < D.R.m := i.2
  have hSD := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  have hβS := B.isFrame_β hL (i := (i : ℕ) + 1) hi (Nat.zero_le _)
  have hβT := B.isFrame_β hL (i := (i : ℕ)) hi.le (Nat.zero_le _)
  have key : ∀ w, (GlobalTheory.StepData.IntM (B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0)) ⟨i.2.le, Nat.zero_le _⟩
      ⟨i.2, Nat.zero_le _⟩ (z.map (cpt (D := D) w ∘ toEAf D))) ↔
      ∀ a b, Valued.v (cpt (D := D) w (Comparison₂.fr (B.β i 0) (B.β (i + 1) 0) (z.map (toEAf D)) a b)) ≤ 1) := by
    intro w
    rw [intM_iff, ← Matrix.map_map, Comparison₂.coord_map]
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
    exact ⟨fun H a b => by
      simpa using H (b.cast (rank_vertex G t w (X := ((i : ℕ) + 1, 0)) ⟨hi, Nat.zero_le _⟩).symm)
        (a.cast (rank_vertex G t w (X := ((i : ℕ), 0)) ⟨hi.le, Nat.zero_le _⟩).symm), fun H a b => H _ _⟩
  simp only [key]
  constructor
  · intro h w hw a b
    exact int_of_mem_latO hSD.1 hβS hβT w (hAA w hw).1 h a b
  · intro h
    exact mem_latO_of_mem_hatMx hSD.1 hI (fun w hw => (hAA w hw).2) hz (mem_hatMx_of_int hβS hβT hI hz h)
