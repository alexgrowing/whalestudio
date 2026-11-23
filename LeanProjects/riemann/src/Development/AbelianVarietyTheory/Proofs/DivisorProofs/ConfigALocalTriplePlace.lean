import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfTensEqOfNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPairEigenUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalInvarianceFirstOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMovesYByIotaAndX
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
open scoped Classical

namespace GlobalTheory.ThK.ShiftUnip

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem symp_vecMulVec_eq_zero {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) (AE F E))
    (x : Fin n → E) (hx : form σ J x x = 0) (p q : Fin d → AE F E) :
    symp (cA σ) (-1) (incM F J) JB (Matrix.vecMulVec (incV F x) p) (Matrix.vecMulVec (incV F x) q) = 0 := by
  have hc : ∀ k, cA σ (inclR (F := F) (AF F) (x k)) = inclR (F := F) (AF F) (σ (x k)) := fun k => by
    simp [cA, inclR, Algebra.TensorProduct.map_tmul]
  have h0 : ∑ i, ∑ k, incV F x i * incM F J i k * cA σ (incV F x k) = 0 := by
    have : ∑ i, ∑ k, incV F x i * incM F J i k * cA σ (incV F x k) = inclR (F := F) (AF F) (form σ J x x) := by
      simp only [form, dotProduct, Matrix.mulVec, incV, incM, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [hc k]; ring
    rw [this, hx, map_zero]
  have hT : hTens (cA σ) (incM F J) JB (Matrix.vecMulVec (incV F x) p) (Matrix.vecMulVec (incV F x) q) = 0 := by
    unfold hTens
    have : ∀ i, ∑ j, ∑ k, ∑ l, Matrix.vecMulVec (incV F x) p i j * incM F J i k * JB j l *
        cA σ (Matrix.vecMulVec (incV F x) q k l) =
        ∑ k, (incV F x i * incM F J i k * cA σ (incV F x k)) * ∑ j, ∑ l, p j * JB j l * cA σ (q l) := fun i => by
      simp only [Matrix.vecMulVec_apply, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    simp only [this, ← Finset.sum_mul, h0, zero_mul]
  unfold symp
  rw [hT, mul_zero, map_zero]

theorem partFin_vecMulVec {n d : ℕ} (v : Pl F) (x : Fin n → AE F E) (p : Fin d → AE F E) :
    partFin v (Matrix.vecMulVec x p) = Matrix.vecMulVec x (partFin v p) := by
  ext i j
  simp [partFin, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, mul_smul_comm]

theorem vecMulVec_mul_transpose' {R : Type} [CommRing R] {n d : ℕ} (y : Fin n → R) (x : Fin d → R)
    (N : Matrix (Fin d) (Fin d) R) : Matrix.vecMulVec y x * Nᵀ = Matrix.vecMulVec y (N *ᵥ x) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem exists_SB_zero_eq_one {κ : Type} [Fintype κ] (v : Pl F) :
    ∃ h ∈ SB (κ → Fv F v), h 0 = 1 := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : κ → Fv F v)
  obtain ⟨U, hU, h0, hUK⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := κ → Fv F v)).mem_nhds_iff.1 hK0
  have hU' : IsClopen U := hU
  have hc : IsCompact U := hK.of_isClosed_subset hU'.isClosed hUK
  refine ⟨U.indicator 1, ⟨(IsLocallyConstant.iff_exists_open _).2 fun g => ?_,
    .intro hc fun x hx => Set.indicator_of_notMem hx _⟩, by simp [h0]⟩
  by_cases hg : g ∈ U
  · exact ⟨U, hU'.isOpen, hg, fun x hx => by simp [hx, hg]⟩
  · exact ⟨Uᶜ, hU'.isClosed.isOpen_compl, hg, fun x hx => by
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hg]⟩

theorem exists_point {κ : Type} (v : Pl F) (ξ : κ → mixedEmbedding.mixedSpace F) (y : κ → Fv F v) :
    ∃ x : κ → AF F, (fun i => evI F (x i)) = ξ ∧ (fun i => evFin F v (x i)) = y ∧
      ∀ u, u ≠ v → (fun i => evFin F u (x i)) = 0 := by
  refine ⟨fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (ξ i), singleFin v (y i)), ?_, ?_, fun u hu => ?_⟩
  · funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (ξ i)
  · funext i
    exact evalV_singleFin_self v (y i)
  · funext i
    exact evalV_singleFin_ne hu (y i)

theorem loc_transfer {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁}
    {W₁ : Spc F E d₁} {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hψ : Continuous B.ψ) (hM : M.IsGood B.ψ)
    {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
    {ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)}
    {ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ}
    (hloc : GlobalTheory.ThK.LemF.IsLocPart M M₁ e ei ev) (v : Pl F) (w w' : Matrix (Fin n) (Fin d) (AE F E))
    (h : ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (partFin v w) Φ) = e (M.co.rho B.ψ (partFin v w') Φ))
    {φ : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) :
    ev v (locOp v (M.co.rho B.ψ (partFin v w)) φ) = ev v (locOp v (M.co.rho B.ψ (partFin v w')) φ) := by
  obtain ⟨hei, hevv, hpure⟩ := hloc
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ei f ξ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  have hupd : ∀ φ₀ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ, (∀ u, φ₀ u ∈ SB _) →
      ∀ ψ ∈ SB (Fin n × Fin d → Fv F v), ∀ u, Function.update φ₀ v ψ u ∈ SB _ := by
    intro φ₀ h₀ ψ hψ' u
    by_cases hu : u = v
    · subst hu
      rw [Function.update_self]
      exact hψ'
    · rw [Function.update_of_ne hu]
      exact h₀ u
  have hcof : ∀ φ₀ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ, (∀ᶠ u in cofinite, φ₀ u = M.vac u) →
      ∀ ψ : (Fin n × Fin d → Fv F v) → ℂ, ∀ᶠ u in cofinite, Function.update φ₀ v ψ u = M.vac u := by
    intro φ₀ h₀ ψ
    filter_upwards [Filter.eventually_cofinite_ne v, h₀] with u hu hu'
    rw [Function.update_of_ne hu, hu']

  have hfin : {u | M₁.vac u 0 ≠ 1}.Finite := by
    by_contra hinf
    obtain ⟨r, -, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f M.vac hM.std
    obtain ⟨x, hxi, hxv, hxu⟩ := exists_point v ξ 0
    have h0 : tens (evFin F v) (0 : (Fin n × Fin d → Fv F v) → ℂ) r = 0 := by
      funext x
      simp [tens]
    have h1 := hpure f _ (hupd M.vac (fun u => (hM.vac u).1) 0 (zero_mem _))
      (hcof M.vac (Filter.Eventually.of_forall fun _ => rfl) 0)
    rw [← hrt, h0, map_zero] at h1
    have h2 := congrFun h1 x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.zero_apply] at h2
    rw [hxi, finprod_of_infinite_mulSupport, mul_one] at h2
    · exact hξ h2.symm
    · refine Set.Infinite.mono (fun u hu => ?_) (Set.Infinite.diff hinf (Set.finite_singleton v))
      have huv : u ≠ v := hu.2
      rw [Function.mem_mulSupport, Function.update_of_ne huv, (hevv u).1, hxu u huv]
      exact hu.1
  have hg : ∀ u : Pl F, ∃ g ∈ SB (Fin n × Fin d → Fv F u), ev u g 0 = 1 := fun u => by
    obtain ⟨h, hh, h0⟩ := exists_SB_zero_eq_one (κ := Fin n₁ × Fin d₁) u
    rw [← (hevv u).2] at hh
    obtain ⟨g, hg, rfl⟩ := hh
    exact ⟨g, hg, h0⟩
  choose g hgS hg1 using hg
  let φ₀ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ := fun u => if M₁.vac u 0 = 1 then M.vac u else g u
  have hφ₀S : ∀ u, φ₀ u ∈ SB _ := fun u => by
    simp only [φ₀]
    split_ifs
    · exact (hM.vac u).1
    · exact hgS u
  have hφ₀c : ∀ᶠ u in cofinite, φ₀ u = M.vac u := by
    filter_upwards [hfin.compl_mem_cofinite] with u hu
    exact if_pos (not_not.1 hu)
  have hφ₀1 : ∀ u, ev u (φ₀ u) 0 = 1 := fun u => by
    simp only [φ₀]
    split_ifs with hu
    · rw [(hevv u).1, hu]
    · exact hg1 u
  have hφ₀std := (hφ₀c.and hM.std).mono fun u hu => hu.1.trans hu.2
  obtain ⟨r₀, hr₀, hr₀t⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ₀ hφ₀std
  have hRest : ∀ ψ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) ψ r₀ := fun ψ hψ' =>
    ⟨hr₀, by
      rw [hr₀t ψ]
      exact GlobalTheory.TensUniq.pure_mem_schA f _ (hupd φ₀ hφ₀S ψ hψ') (GlobalTheory.PureFactor.update_eventually _ v ψ hφ₀std)⟩
  funext y
  obtain ⟨x, hxi, hxv, hxu⟩ := exists_point v ξ y
  have hev_pure : ∀ ψ ∈ SB (Fin n × Fin d → Fv F v),
      e (tens (evFin F v) ψ r₀) x = ei f ξ * ev v ψ y := by
    intro ψ hψ'
    rw [hr₀t ψ, hpure f _ (hupd φ₀ hφ₀S ψ hψ') (hcof φ₀ hφ₀c ψ)]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [hxi, finprod_eq_single _ v, Function.update_self, hxv]
    intro u hu
    rw [Function.update_of_ne hu, hxu u hu, hφ₀1]
  have h1 := locOp_rho M.co hψ v w hφ
  have h2 := locOp_rho M.co hψ v w' hφ
  apply mul_left_cancel₀ hξ
  rw [← hev_pure _ (locOp_mem v _ φ), ← hev_pure _ (locOp_mem v _ φ), ← h1.1 r₀ (hRest φ hφ),
    ← h2.1 r₀ (hRest φ hφ), h _ (hRest φ hφ).2]

theorem shiftUnip : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, GlobalTheory.ThK.LemF.IsLocPart G.M G₁.M e ei ev →
    ∀ X om om', IsTriple B G X om om' → ∀ v : Pl F, ∀ u ∈ unip σ G.W H', ∀ l : (AE F E)ˣ,
    ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l * (mat u)ᵀ))) φ) =
        ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l))) φ) := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' cfg e hev ei ev hloc X om om' T v u hu l φ hφ
  obtain ⟨z, c, huy⟩ := GlobalTheory.IsoMove.unip_mulVec_y F E σ B _ _ G.W G₁.W H' _ _ _ _ T.base.cm T.geo.hW cfg.hH' u hu
  have hS : shiftA H H' l = Matrix.vecMulVec (incV F H.x) (l.1 • incV F H'.y) := by
    ext i j
    simp [shiftA, Matrix.vecMulVec_apply, mul_left_comm]
  have hSu : shiftA H H' l * (mat u)ᵀ = Matrix.vecMulVec (incV F H.x) (l.1 • incV F H'.y) +
      (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ (l.1 • z)) +
        Matrix.vecMulVec (incV F H.x) ((l.1 * c) • incV F H'.x)) := by
    rw [hS, vecMulVec_mul_transpose', Matrix.mulVec_smul, huy, Matrix.mulVec_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hP : ∀ p q r : Fin (b + 2 + a') → AE F E, partFin v (Matrix.vecMulVec (incV F H.x) p +
      (Matrix.vecMulVec (incV F H.x) q + Matrix.vecMulVec (incV F H.x) r)) =
      Matrix.vecMulVec (incV F H.x) (partFin v q) + Matrix.vecMulVec (incV F H.x) (partFin v r) +
        Matrix.vecMulVec (incV F H.x) (partFin v p) := by
    intro p q r
    rw [partFin, smul_add, smul_add, ← partFin, ← partFin, ← partFin, partFin_vecMulVec, partFin_vecMulVec,
      partFin_vecMulVec]
    abel
  have hsy : ∀ p q : Fin (b + 2 + a') → AE F E,
      symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (Matrix.vecMulVec (incV F H.x) p) (Matrix.vecMulVec (incV F H.x) q) = 0 :=
    fun p q => symp_vecMulVec_eq_zero G.V.J _ H.x cfg.hH.xx p q
  have hstd := T.base.std
  refine loc_transfer hstd.1 T.geo.hM hloc v _ _ (fun Φ hΦ => ?_) hφ
  rw [hSu, hP, hS, partFin_vecMulVec]
  set A := Matrix.vecMulVec (incV F H.x) (partFin v (l.1 • incV F H'.y))
  set D₁ := Matrix.vecMulVec (incV F H.x) (partFin v (incM F H'.ι *ᵥ (l.1 • z)))
  set D₂ := Matrix.vecMulVec (incV F H.x) (partFin v ((l.1 * c) • incV F H'.x))
  have hD₁ : D₁ ∈ isoA H H' := by
    refine Or.inr ⟨partFin v (l.1 • z), ?_⟩
    simp only [D₁, partFin, Matrix.mulVec_smul]
  have hD₂ : D₂ ∈ isoA H H' := by
    refine Or.inl ⟨partFin v (l.1 * c) • incV F H.x, ?_⟩
    ext i j
    simp only [D₂, partFin, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc]
    congr 1
    ring
  have hΨ : G.M.co.rho B.ψ A Φ ∈ schA F _ := GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd _ _ hΦ
  have hΨ₂ : G.M.co.rho B.ψ D₂ (G.M.co.rho B.ψ A Φ) ∈ schA F _ := GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd _ _ hΨ
  rw [GlobalTheory.UnipEvLaw.rho_add G.M B.ψ _ _ (by simp only [D₁, D₂, A, ← Matrix.vecMulVec_add]; exact hsy _ _),
    GlobalTheory.UnipEvLaw.rho_add G.M B.ψ _ _ (hsy _ _), hev.inv _ hD₁ _ hΨ₂, hev.inv _ hD₂ _ hΨ]

end GlobalTheory.ThK.ShiftUnip
