import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParabolicAtStandardWeylElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GapHypOfNodes
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DiscreteSeriesUniqueLargeGap

noncomputable section

namespace GlobalTheory.HeckeField.Gap

open Matrix Formalism.MainNotions.S GlobalTheory.Published.HermitianUnique

theorem herm_of_equiv {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {J P P' : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (hP' : IsUnit P') (hJ : Pᴴ * Formalism.REAL.Jm ε * P = J) (hJ' : P'ᴴ * Formalism.REAL.Jm ε * P' = J)
    {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (hσ : IsDS ε lam σ)
    (U : H' ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ v, U (σ' g v) = σ g (U v)) :
    ∃ U : H' ≃ₗᵢ[ℂ] H, ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, U (σ' (P' * g * P'⁻¹) w) = σ (P * g * P⁻¹) (U w) := by
  obtain ⟨-, -, ⟨⟨h1, hmul⟩, hiso, -⟩, -⟩ := hσ
  have e : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have e2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have e' : P'⁻¹ * P' = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP')
  have one : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.QuantumDeterminants.UH J := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * J * 1 = J
    simp
  have ha : P * 1 * P'⁻¹ ∈ UJset ε := frame_mem hP' hJ hJ' one
  have hb : P' * 1 * P⁻¹ ∈ UJset ε := frame_mem hP hJ' hJ one
  rw [Matrix.mul_one] at ha hb
  have hsurj : Function.Surjective
      (⟨(σ (P * P'⁻¹) : H →ₗ[ℂ] H), hiso _ ha⟩ : H →ₗᵢ[ℂ] H) := by
    intro v
    refine ⟨σ (P' * P⁻¹) v, ?_⟩
    have e3 : P * P'⁻¹ * (P' * P⁻¹) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc P'⁻¹, e', Matrix.one_mul, e2]
    have := hmul _ ha _ hb
    rw [e3, h1] at this
    exact (congrArg (fun T : H →L[ℂ] H => T v) this).symm
  refine ⟨U.trans (LinearIsometryEquiv.ofSurjective _ hsurj), fun g hg w => ?_⟩
  show σ (P * P'⁻¹) (U (σ' (P' * g * P'⁻¹) w)) = σ (P * g * P⁻¹) (σ (P * P'⁻¹) (U w))
  have hg' := frame_mem hP' hJ' hJ' hg
  have hg1 := frame_mem hP hJ hJ hg
  have k1 := congrArg (fun T : H →L[ℂ] H => T (U w)) (hmul _ ha _ hg')
  have k2 := congrArg (fun T : H →L[ℂ] H => T (U w)) (hmul _ hg1 _ ha)
  have k3 : P * P'⁻¹ * (P' * g * P'⁻¹) = P * g * P⁻¹ * (P * P'⁻¹) := by
    calc P * P'⁻¹ * (P' * g * P'⁻¹) = P * (P'⁻¹ * P') * g * P'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P * g * (P⁻¹ * P) * P'⁻¹ := by rw [e, e', Matrix.mul_one, Matrix.mul_one]
      _ = P * g * P⁻¹ * (P * P'⁻¹) := by simp only [Matrix.mul_assoc]
  rw [hU _ hg']
  rw [k3] at k1
  exact k1.symm.trans k2

theorem npq_lt {n : ℕ} (ε : Fin n → Bool) (hn : 1 ≤ n) :
    (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) + 1 < 16 * (n : ℝ) ^ 19 := by
  have hp : ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ n := by
    unfold ReciprocityTheory.ChartRestriction.DS.pOf
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hq : ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ n := by
    unfold ReciprocityTheory.ChartRestriction.DS.qOf
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp' : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ n := by exact_mod_cast hp
  have hq' : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ n := by exact_mod_cast hq
  have h3 : (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ (n : ℝ) ^ 3 := by
    have := mul_le_mul (mul_le_mul_of_nonneg_left hp' (by positivity)) hq' (by positivity) (by positivity)
    nlinarith
  have h19 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 19 := pow_le_pow_right₀ hn' (by norm_num)
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 19 := one_le_pow₀ hn'
  linarith

end GlobalTheory.HeckeField.Gap

namespace GlobalTheory.HeckeField.Gap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.HeightCounting.RatSide
  GlobalTheory.HeckeField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Gapped (S : SPar) (h : ℚ) : Prop := ∀ x ∈ S, ∀ y ∈ S, x.2 ≠ y.2 → h ≤ |x.1 - y.1|

theorem Gapped.dual {S : SPar} {h : ℚ} (hS : Gapped S h) : Gapped (dualPar S) h := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
  have := hS a ha b hb hxy
  show h ≤ |-a.1 - -b.1|
  rwa [show -a.1 - -b.1 = -(a.1 - b.1) by ring, abs_neg]

theorem gapped_holPar {R : Ranks} (hc : HCParam R) (i : Fin R.m) {p q : ℕ} (hp : p = R.k + i) (hq : q = R.m - (i + 1)) {h : ℚ}
    (hg : ∀ hj : i.1 + 1 < R.m, h ≤ hc.b ⟨i.1 + 1, hj⟩ - hc.b i) :
    Gapped (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW hc p q)) h := by
  have hk := R.m_add_three_le_k
  have hi := i.2
  have hr : p + q = R.r := by unfold Ranks.r; omega
  have ho : Odd (p + q) := by rw [hr]; exact Formalism.L2.NTheta.odd_r R
  have key : ∀ (a : Fin p) (c : Fin q), h ≤ Formalism.L2.NTheta.lamAt hc a - Formalism.L2.NTheta.lamAt hc (p + c) := by
    intro a c
    have ha := a.2
    have hc' := c.2
    have hj : i.1 + 1 < R.m := by omega
    have h1 := Formalism.L2.NTheta.lamAt_add_add_le hc (p - 1 - a) a (by omega)
    have h2 := Formalism.L2.NTheta.lamAt_add_add_le hc c p (by omega)
    rw [show a.1 + (p - 1 - a) = p - 1 by omega] at h1
    have e1 : Formalism.L2.NTheta.lamAt hc (p - 1) = -hc.b i := by
      unfold Formalism.L2.NTheta.lamAt
      rw [dif_neg (by omega), dif_pos (by omega)]
      congr 2
      exact Fin.ext (by simp only; omega)
    have e2 : Formalism.L2.NTheta.lamAt hc p = -hc.b ⟨i.1 + 1, hj⟩ := by
      unfold Formalism.L2.NTheta.lamAt
      rw [dif_neg (by omega), dif_pos (by omega)]
      congr 2
      exact Fin.ext (by simp only; omega)
    have h3 := hg hj
    have h4 : (0 : ℚ) ≤ ((p - 1 - a : ℕ) : ℚ) := Nat.cast_nonneg _
    have h5 : (0 : ℚ) ≤ ((c : ℕ) : ℚ) := Nat.cast_nonneg _
    linarith
  intro x hx y hy hxy
  simp only [Formalism.L2.NTheta.holPar, Formalism.L2.NTheta.holEnt_kapW hc _ _ ho] at hx hy
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hy
  rcases a with a | a <;> rcases b with b | b
  · exact absurd rfl hxy
  · exact (key a b).trans (le_abs_self _)
  · rw [abs_sub_comm]; exact (key b a).trans (le_abs_self _)
  · exact absurd rfl hxy

variable {D : D7}

theorem gapped_parAt (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    Gapped (parAt (Wc D i) σ ρ) (16 * (D.R.r : ℚ) ^ 19) := by
  have hs : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have h0 : Gapped (Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) σ ρ)) (16 * (D.R.r : ℚ) ^ 19) :=
    gapped_holPar (D.hc (lab σ ρ)) i (by rw [hs]; simp [Ranks.sigW]) (by rw [hs]; rfl) (hG.2 _ i)
  unfold parAt
  split_ifs
  exacts [h0, h0.dual]

theorem exists_intertwiner {V : HSp D} {S : D.what₂.Tau → SPar} (h1 : 1 ≤ V.rank)
    (hS : ∀ τ, Gapped (S τ) (16 * (V.rank : ℚ) ^ 19)) (M M' : DSModel V S) :
    ∃ U : ∀ τ, M'.H τ ≃ₗᵢ[ℂ] M.H τ,
      ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, U τ (M'.rep τ g w) = M.rep τ g (U τ w) := by
  have key : ∀ τ, ∃ U : M'.H τ ≃ₗᵢ[ℂ] M.H τ,
      ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, U (M'.rep τ g w) = M.rep τ g (U w) := by
    intro τ
    obtain ⟨hl, he⟩ := GlobalTheory.SignedParTest.isEnum_unique (M.enum τ) (M'.enum τ)
    have hd' : Formalism.MainNotions.S.IsDS (M.ε τ) (M.lam τ) (M'.σ τ) := hl ▸ he ▸ M'.ds τ
    haveI : CompleteSpace (M.H τ) := (M.ds τ).1
    haveI : CompleteSpace (M'.H τ) := (M'.ds τ).1
    have hgap : Formalism.QuantumDeterminants.GapAtLeast (M.ε τ) (M.lam τ) (16 * (V.rank : ℝ) ^ 19) := by
      obtain ⟨-, f, hf, e⟩ := M.enum τ
      intro a b hab
      have := hS τ (f a, M.ε τ a) (e ▸ Finset.mem_image_of_mem _ (Finset.mem_univ a)) (f b, M.ε τ b)
        (e ▸ Finset.mem_image_of_mem _ (Finset.mem_univ b)) hab
      rw [hf, hf]
      exact_mod_cast this
    obtain ⟨U, hU⟩ := ReciprocityTheory.ChartRestriction.DS.final_deg_DSUniqG _ (M.ε τ) (M.lam τ) _ _ (M'.σ τ) (M.σ τ)
      (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M.enum τ).1 (M.ds τ)) hd' (M.ds τ) _ hgap (npq_lt _ h1)
    exact herm_of_equiv (M.fr_unit τ) (M'.fr_unit τ) (M.fr_gram τ) (he ▸ M'.fr_gram τ) (M.ds τ) U hU
  choose U hU using key
  exact ⟨U, hU⟩

theorem occ_model {V : HSp D} {S : D.what₂.Tau → SPar} (h1 : 1 ≤ V.rank) (hS : ∀ τ, Gapped (S τ) (16 * (V.rank : ℚ) ^ 19))
    {J : Set (GA D V)} {I : Finset (GA D V) → ℂ → Prop} (h : Occ V S J I)
    (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (M' : DSModel V S) :
    ∃ U ∈ Mult θ M' J fun _ => 1, U ≠ 0 ∧ ∀ Rr a, I Rr a → heckeOn M' Rr U = a • U := by
  obtain ⟨θ', hθ', M, U, hM, h0, he⟩ := h
  obtain rfl := GlobalTheory.VolHeckeCompare.infFam_unique hθ hθ'
  obtain ⟨N, c, hc⟩ := GlobalTheory.ConjDS.exists_conjModel M
  obtain ⟨u, hu⟩ := exists_intertwiner h1 hS M M'
  obtain ⟨U1, m1, n1, e1⟩ := eig_conj θ M N c hc J hM h0
  obtain ⟨U2, m2, n2, e2⟩ := eig_conj θ N M' (fun τ => (u τ).trans (c τ).symm) (fun τ g hg w => (c τ).injective (by
    show c τ ((c τ).symm (u τ _)) = c τ (N.rep τ g ((c τ).symm (u τ w)))
    rw [(c τ).apply_symm_apply, hc τ g hg, (c τ).apply_symm_apply, hu τ g hg])) J m1 n1
  exact ⟨U2, m2, n2, fun Rr a ha => by simpa only [star_star] using e2 Rr _ (e1 Rr a (he Rr a ha))⟩

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_boundAt (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) (R : RealDat3 D A3 Ks) (hL : R.toLevCh.Is A3.A.μ0)
    (hθ : IsInfFam R.θ) (hW : R.toRealDat.models_HW) (hu : R.toRealDat.LUnif) (i : Fin D.R.m) (hK : (R.FW i).IsKsForm)
    (h : ℕ → PlE D.host → Module.End D.what₂.LL (Fin (R.nW i) → D.what₂.LL))
    (hs : ∀ k P x, x ∈ (R.FW i).WK → h k P x ∈ (R.FW i).WK)
    (hr : ∀ k P α Rr, HkDat R (SbD D) i k P α Rr → ∀ x, (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) (h k P x)) =
      hkNorm R i k P • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) x))) :
    ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ BoundAt R.C i S := by
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  obtain ⟨n, b, hb, -, hsp, -, hsp'⟩ := hK
  haveI : FiniteDimensional Ks (R.FW i).WK := by
    rw [← hsp]
    exact FiniteDimensional.span_of_finite Ks (Set.finite_range b)
  let ι : (R.FW i).WK →ₛₗ[(sg0 D A3.A).comp (algebraMap Ks D.what₂.LL)] MMap (R.MW i (sg0 D A3.A)) :=
    { toFun := fun x => (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) x)
      map_add' := fun x y => by rw [Submodule.coe_add, map_add, map_add]
      map_smul' := fun a x => by rw [Submodule.coe_smul, ← algebraMap_smul D.what₂.LL a, map_smulₛₗ, map_smul]; rfl }
  let κ := {t : ℕ × PlE D.host × GA D (Wc D i) × Finset (GA D (Wc D i)) // HkAt R.C i t.1 t.2.1 t.2.2.1 t.2.2.2}
  obtain ⟨S, h1, h2⟩ := exists_finset_eig _ ι
    (fun t : κ => ((h t.1.1 t.1.2.1).restrictScalars Ks).restrict (hs t.1.1 t.1.2.1))
    (fun t : κ => hkNorm R i t.1.1 t.1.2.1 • heckeOn (R.MW i (sg0 D A3.A)) t.1.2.2.2)
    (fun t x => (hr _ _ _ _ ((hkDat_iff hL).2 t.2) x).symm)
  refine ⟨S, h1, fun L hS c hc k P α Rr hd => ?_⟩
  unfold EigSys at hc
  rw [← parabolic_at_standard_weyl_element (A3 := A3) R.toRealDat] at hc
  obtain ⟨U, hM, h0, he⟩ := occ_model (by have := hG.1; omega) (fun τ => by rw [hrk]; exact gapped_parAt hG i _ τ) hc
    R.θ hθ (R.MW i (sg0 D A3.A))
  refine h2 L hS U ?_ h0 (fun t => nrm R.C i t.1.1 t.1.2.1 * c t.1.1 t.1.2.1) (fun t => ?_) ⟨(k, P, α, Rr), hd⟩
  · have hM' : U ∈ R.Wall i (sg0 D A3.A) := by
      refine mult_mono _ _ (fun k hk => ?_) hM
      have := GlobalTheory.HeckeParts.triv_le (V := Wc D i) (β := R.βW i) R.triv k hk
      exact ⟨by rw [← levTriv_eq hL i]; exact hk, this.2.symm⟩
    rw [← (hW i _).2.1] at hM'
    obtain ⟨y, rfl⟩ := hM'
    have hy : y ∈ Submodule.span ℂ (Set.range ((R.FW i).j (sg0 D A3.A))) := (hu i _).2.1 ▸ Submodule.mem_top
    refine Submodule.span_le (p := (Submodule.span ℂ (Set.range ι)).comap (R.HW i (sg0 D A3.A)).e).2 ?_ hy
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ Submodule.span D.what₂.LL (Set.range b) := hsp' ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    show (R.HW i (sg0 D A3.A)).e _ ∈ Submodule.span ℂ (Set.range ι)
    rw [map_sum, map_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [map_smulₛₗ, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨b l, hb l⟩, rfl⟩)
  · show hkNorm R i t.1.1 t.1.2.1 • heckeOn (R.MW i (sg0 D A3.A)) t.1.2.2.2 U = _
    rw [he _ _ ⟨_, _, _, t.2, rfl⟩, smul_smul]
    rfl

end GlobalTheory.HeckeField.Gap

namespace GlobalTheory.HeckeField.Gap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide GlobalTheory.HeckeField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

theorem exists_bound {D : D7} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (hL : R.toLevCh.Is A3.A.μ0)
    (hθ : IsInfFam R.θ) (hW : R.toRealDat.models_HW) (hu : R.toRealDat.LUnif) (hK : ∀ i, (R.FW i).IsKsForm)
    (h : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j)) (hs : StabC (ratDatR R cG kKs hk) h)
    (hr : HeckeRd R cG kKs hk (SbD D) h) : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ i, BoundAt R.C i S := by
  classical
  have key : ∀ i : Fin D.R.m, ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ BoundAt R.C i S := fun i => by
    have h1 : 1 ≤ i.1 + 1 := Nat.le_add_left _ _
    have := exists_boundAt hG R hL hθ hW hu (idxOf D (i.1 + 1)) (hK _) (h (i.1 + 1)) (hs _ h1 i.2)
      (fun k P α Rr hd => hr _ k P α Rr h1 i.2 hd)
    rwa [NX.idxOf_succ] at this
  choose S h1 h2 using key
  refine ⟨Finset.univ.biUnion S, fun z hz => ?_, fun i L hS => h2 i L fun z hz => hS z ?_⟩
  · obtain ⟨i, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact h1 i z hz
  · exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hz⟩

theorem rowEig_mem_fixedField : StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), ∀ hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j), StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∀ (i : Fin (Dof x).R.m) (σ : (Dof x).what₂.FT) (k : ℕ) (Pl : PlE (Dof x).host) α Rr, HkDat x.m.z.R (SbD (Dof x)) i k Pl α Rr → (Dof x).what₂.isot (i.1 + 1) σ ≠ ⊥ → ∃ c : ↥(Dof x).LL0, (Dof x).what₂.embLL (c : (Dof x).what₂.LL) = hkNorm x.m.z.R i k Pl * GlobalTheory.EigRows.rowEig x.r.Y i σ Pl (GlobalTheory.EigRows.diagLab (Dof x).R.r k) := by
  refine (evG_of_ev GlobalTheory.Mem.Top.NodeGap.ev_gapHyp).imp fun K _ _ _ _ hgap =>
    ⟨fun Q f _ => gens Q f, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun Q f _ => gens_alg Q f, by simp, fun B f T hO hH _ _ _ _ _ w _ P x hL' hs hr i σ k Pl α Rr hd h0 => ?_⟩
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp (Dof x) := hgap (w.st x.o.Z) hO
  have hC : x.m.z.R.C = Fr.at (w.st x.o.Z) f := x.m.z.lev.C.trans (congrArg (Fr.at (w.st x.o.Z)) w.C_eq)
  have hb := x.m.z.pins.char.base
  obtain ⟨S, h1, h2⟩ := exists_bound hG x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) hb.lev hb.models.inf hb.models.HW
    x.m.intersectionNumber_baseChange.prim.unif x.m.z.geo.fw.ks hL' hs hr
  rw [hC] at h2
  have h3 := boundAt_gens (w.st x.o.Z) f h1 h2 i
  rw [← hC] at h3
  obtain ⟨c, hc, e⟩ := B.mem_LL0C.1
    (h3 B.fixedCoefficientFieldInComplex hH.1 _ (eigSys_row x.r.Y hb.lev hb.models.inf h0) k Pl α Rr ((hkDat_iff hb.lev).1 hd))
  exact ⟨⟨c, hc⟩, e⟩

end GlobalTheory.HeckeField.Gap
