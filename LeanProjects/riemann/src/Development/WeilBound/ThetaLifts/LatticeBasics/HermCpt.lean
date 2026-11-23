import Development.WeilBound.ThetaLifts.LatticeBasics.HermRank
import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsMaximalCompactInfinite
import Development.WeilBound.ThetaLifts.FrameEstimates.LatArch
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopology

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.CMAdele Dense PositivityTheory.ThKF
open PositivityTheory.ThK (kc_ring adele_t2Space kc_smul kc_closedU kc_cont_mat isCompact_of_units)
open GlobalTheory.CompanionTheory.SW.Core (Oh)

attribute [local instance] kc_ring adele_t2Space kc_smul

namespace Herm

theorem map_star_mul' {a b c : Type} [Fintype b] (x : Matrix a b ℂ) (y : Matrix b c ℂ) :
    (x * y).map star = x.map star * y.map star := Matrix.map_mul (f := starRingEnd ℂ)

theorem cpt_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (h0 : min r s = 0) :
    ∃ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C ∧ ∀ g, gᵀ * M * g.map star = M → g ∈ C := by
  obtain ⟨hn, A, hA⟩ := h
  obtain ⟨ε, e1, e2⟩ : ∃ ε : ℂ, ε * ε = 1 ∧ Aᵀ * M * A.map star = ε • 1 := by
    rcases Nat.min_eq_zero_iff.1 h0 with rfl | rfl
    · refine ⟨-1, by simp, hA.trans ?_⟩
      ext (i | i) (j | j) <;> first | exact i.elim0 | exact j.elim0 | (simp only [Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, neg_smul, one_smul, Matrix.one_apply, Sum.inr.injEq])
    · refine ⟨1, by simp, hA.trans ?_⟩
      ext (i | i) (j | j) <;> first | exact i.elim0 | exact j.elim0 | simp [Matrix.one_apply]
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ, Aᵀ * N = (1 : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) := ⟨ε • (M * A.map star), by rw [Matrix.mul_smul, ← Matrix.mul_assoc, e2, smul_smul, e1, one_smul]⟩
  have hN' : N * Aᵀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hn])).1 hN
  have h1 : A * Nᵀ = 1 := by simpa using congrArg Matrix.transpose hN'
  have h2 : A.map star * Nᵀ.map star = 1 := by rw [← map_star_mul', h1]; simp
  refine ⟨(fun u : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ => A * u * Nᵀ) '' Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall 0 1,
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _).image
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const), fun g hg =>
    ⟨Nᵀ * g * A, fun k _ i _ => ?_, by
      simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]; rw [Matrix.mul_assoc, h1, Matrix.mul_one]⟩⟩
  have e3 : N * Nᵀ.map star = ε • M := by
    have : N * (Aᵀ * M * A.map star) * Nᵀ.map star = M := by
      simp only [← Matrix.mul_assoc, hN', Matrix.one_mul]; rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [← this, e2, Matrix.mul_smul, Matrix.smul_mul, smul_smul, e1, one_smul, Matrix.mul_one]
  have e4 : (Nᵀ * g * A)ᵀ * (Nᵀ * g * A).map star = 1 := by
    calc _ = Aᵀ * (gᵀ * (N * Nᵀ.map star) * g.map star) * A.map star := by
          simp only [map_star_mul', Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = 1 := by rw [e3, Matrix.mul_smul, Matrix.smul_mul, hg, Matrix.mul_smul, Matrix.smul_mul, e2, smul_smul, e1, one_smul]
  generalize Nᵀ * g * A = u at e4
  have e5 : ∑ l, ‖u l i‖ ^ 2 = 1 := by
    have := congrFun (congrFun e4 i) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq, Complex.star_def,
      Complex.mul_conj'] at this
    exact_mod_cast this
  rw [mem_closedBall_zero_iff, ← sq_le_one_iff₀ (norm_nonneg _), ← e5]
  exact Finset.single_le_sum (f := fun l => ‖u l i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

variable (F) in

def fA : Af F →+ AF F := AddMonoidHom.inr (Ainf F) (Af F)

theorem fA_mul (x : Af F) (a : AF F) : fA F x * a = fA F (x * a.2) := Prod.ext (zero_mul _) rfl

theorem cont_realAd : Continuous (realAd F) := by
  refine Continuous.prodMk (Continuous.comp (g := (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm) (continuous_pi fun v => ?_)
    (continuous_algebraMap ℝ _)) continuous_const
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem exists_arch_section (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ T : (InfinitePlace F → ℂ) → AE F E, Continuous T ∧ ∀ a, a = T (fun w => piInf (τ w) a) + fA F 1 • a := by
  choose x x1 x2 using GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ
  have sm : ∀ w (t : AF F) (a : AE F E), piInf (τ w) (t • a) =
      InfinitePlace.Completion.extensionEmbedding w (evInf F w t) * piInf (τ w) a := fun w t a => by
    rw [Algebra.smul_def, map_mul, PositivityTheory.ThKEst.LatArchPf.piInf_alg]
  refine ⟨fun z => ∑ w, (realAd F (z w).re • x (Pi.single w 1) + realAd F (z w).im • x (Pi.single w Complex.I)),
    continuous_finsetSum _ fun w _ =>
      by have := cont_realAd (F := F); fun_prop, fun a => ?_⟩
  rw [← sub_eq_iff_eq_add, ← sub_eq_zero]
  refine eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_
  · have h1 : c.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hc
    have h2 : c * fA F 1 = c := Prod.ext ((mul_zero _).trans h1.symm) (mul_one _)
    have h3 : ∀ t z, c • realAd F t • x z = 0 := fun t z => by rw [smul_comm, x1 _ c hc, smul_zero]
    rw [smul_sub, smul_sub, smul_smul c, h2]
    simp only [sub_self, Finset.smul_sum, smul_add, h3, add_zero, Finset.sum_const_zero]
  · simp only [map_sub, map_sum, map_add, sm, x2, PositivityTheory.ThKEst.LatArchPf.emb_realAd h.1]
    rw [show evInf F w (fA F 1) = 0 from rfl, Finset.sum_eq_single w (fun v _ hv => by simp [Pi.single_eq_of_ne hv.symm])
      (by simp)]
    simp

variable (F E) in

def lamF : AddSubgroup (AE F E) where
  carrier := (fun x : Ix E → Af F => ∑ i, fA F (x i) • bA F i) '' Set.univ.pi fun _ => Oh F
  zero_mem' := ⟨0, fun _ _ v => zero_mem _, Finset.sum_eq_zero fun _ _ => by simp⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    refine ⟨x + y, fun i _ v => add_mem (hx i trivial v) (hy i trivial v), ?_⟩
    simp [Finset.sum_add_distrib, add_smul]
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨-x, fun i _ v => neg_mem (hx i trivial v), ?_⟩
    simp

theorem lamF_mul {a b : AE F E} (ha : a ∈ lamF F E) (hb : b ∈ lamF F E) : a * b ∈ lamF F E := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  rw [Finset.sum_mul_sum]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  obtain ⟨c, hc⟩ := bA_mul (F := F) i j
  rw [smul_mul_smul_comm, hc, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  rw [smul_comm]
  refine zsmul_mem (⟨Pi.single k (x i * y j), fun l _ v => ?_, ?_⟩ : _ ∈ lamF F E) _
  · by_cases h : l = k
    · subst h; rw [Pi.single_eq_same]; exact mul_mem (hx i trivial v) (hy j trivial v)
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  · refine (Finset.sum_eq_single k (fun l _ h => by simp [Pi.single_eq_of_ne h]) (by simp)).trans ?_
    rw [Pi.single_eq_same, fA_mul]
    rfl

theorem lamF_cpt : IsCompact (lamF F E : Set (AE F E)) :=
  (isCompact_univ_pi fun _ => GlobalTheory.CompanionTheory.SW.Core.AfTop.isCompact_Oh F).image (continuous_finsetSum _ fun i _ =>
    Continuous.fun_smul (f := fun x : Ix E → Af F => fA F (x i)) (continuous_const.prodMk (continuous_apply i))
      continuous_const)

theorem lamF_nhds : ∀ᶠ a in 𝓝 (0 : AE F E), fA F 1 • a ∈ lamF F E := by
  obtain ⟨S, hS⟩ := exists_sectionC (F := F) (E := E)
  have hSc : Continuous S := IsModuleTopology.continuous_of_linearMap S
  have : ∀ᶠ a in 𝓝 (0 : AE F E), ∀ i, (S a i).2 ∈ Oh F := eventually_all.2 fun i =>
    (continuous_snd.comp ((continuous_apply i).comp hSc)).continuousAt.eventually_mem
      ((GlobalTheory.CompanionTheory.SW.Core.AfTop.isOpen_Oh F).mem_nhds (show (S 0 i).2 ∈ Oh F by rw [map_zero]; exact fun v => zero_mem _))
  refine this.mono fun a ha => ⟨fun i => (S a i).2, fun i _ => ha i, ?_⟩
  conv_rhs => rw [← hS a, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [smul_smul, fA_mul, one_mul]

def kInt (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) : Subgroup (UA σ J) where
  carrier := {g | ∀ i j, fA F 1 • (mat g - 1) i j ∈ lamF F E ∧
    fA F 1 • (mat g⁻¹ - 1) i j ∈ lamF F E}
  one_mem' := fun i j => by simp [mat_one']
  mul_mem' := fun {g h} hg hh => by
    have key : ∀ A B : Matrix (Fin n) (Fin n) (AE F E), (∀ i j, fA F 1 • (A - 1) i j ∈ lamF F E) →
        (∀ i j, fA F 1 • (B - 1) i j ∈ lamF F E) →
        ∀ i j, fA F 1 • (A * B - 1) i j ∈ lamF F E := fun A B hA hB i j => by
      have e : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
      have e2 : fA F 1 * fA F 1 = fA F 1 := Prod.ext (mul_zero _) (mul_one _)
      rw [e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply, smul_add, smul_add, Finset.smul_sum]
      refine add_mem (add_mem (sum_mem fun k _ => ?_) (hA i j)) (hB i j)
      rw [← e2, ← smul_mul_smul_comm]
      exact lamF_mul (hA i k) (hB k j)
    refine fun i j => ⟨key _ _ (fun i j => (hg i j).1) (fun i j => (hh i j).1) i j, ?_⟩
    rw [mul_inv_rev]
    exact key _ _ (fun i j => (hh i j).2) (fun i j => (hg i j).2) i j
  inv_mem' := fun {g} hg i j => ⟨(hg i j).2, by rw [inv_inv]; exact (hg i j).1⟩

theorem kInt_open (J : Matrix (Fin n) (Fin n) E) : IsOpen (kInt σ J : Set (UA σ J)) := by
  have hm := kc_cont_mat (σ := σ) J
  refine (kInt σ J).isOpen_of_mem_nhds (g := 1) (show ∀ᶠ g in 𝓝 1, ∀ i j, _ from
    eventually_all.2 fun i => eventually_all.2 fun j => Eventually.and ?_ ?_)
  · exact (((hm.sub continuous_const).matrix_elem i j).tendsto' 1 0 (by simp [mat_one'])).eventually lamF_nhds
  · exact ((((hm.comp continuous_inv).sub continuous_const).matrix_elem i j).tendsto' 1 0 (by simp [mat_one'])).eventually lamF_nhds

end Herm

open Herm in
theorem cptOpen : CptOpen := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0
  refine ⟨kInt σ Y.J, kInt_open _, ?_⟩
  have : ∀ w, ∃ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C ∧ ∀ g : UA σ Y.J, (mat g).map (piInf (B.emb w)) ∈ C := fun w => by
    have e : ∀ g : UA σ Y.J, ((mat g).map (piInf (B.emb w)))ᵀ * Y.J.map (B.emb w).1 * ((mat g).map (piInf (B.emb w))).map star =
        Y.J.map (B.emb w).1 := fun g => by
      have := congrArg (·.map (piInf (B.emb w))) (show (mat g)ᵀ * incM F Y.J * (mat g).map (cA σ) = incM F Y.J from g.2)
      simp only [Matrix.map_mul, map_incM, Matrix.transpose_map] at this
      convert this using 2
      ext i j
      exact (piInf_cA hB.cm _ _).symm
    rcases hY with h | h
    · exact (cpt_sig (h.sig w) h0).imp fun C hC => ⟨hC.1, fun g => hC.2 _ (e g)⟩
    · exact (cpt_sig (h.sig w) h0).imp fun C hC => ⟨hC.1, fun g => hC.2 _ (by rw [Matrix.mul_smul, Matrix.smul_mul, e])⟩
  choose C h1 h2 using this
  obtain ⟨T, t1, t2⟩ := exists_arch_section hB.cm B.emb
  let f : (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) × Matrix (Fin n) (Fin n) (AE F E) → Matrix (Fin n) (Fin n) (AE F E) :=
    fun p i j => T (fun w => p.1 w i j) + (p.2 i j + fA F 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) i j)
  have cf : Continuous f := continuous_matrix fun i j =>
    (t1.comp (continuous_pi fun w => ((continuous_apply w).comp continuous_fst).matrix_elem i j)).add
      ((continuous_snd.matrix_elem i j).add continuous_const)
  have key : ∀ g ∈ kInt σ Y.J, mat g ∈ f '' (Set.univ.pi C ×ˢ Set.univ.pi fun _ => Set.univ.pi fun _ => (lamF F E : Set _)) :=
    fun g hg => ⟨(fun w => (mat g).map (piInf (B.emb w)), fun i j => fA F 1 • (mat g - 1) i j),
      ⟨fun w _ => h2 w g, fun i _ j _ => (hg i j).1⟩, by
        ext i j
        simp only [f, Matrix.sub_apply, ← smul_add, sub_add_cancel, Matrix.map_apply]
        exact (t2 _).symm⟩
  exact isCompact_of_units _ (kc_closedU Y.J) _ ((kInt σ Y.J).isClosed_of_isOpen (kInt_open _)) _
    (((isCompact_univ_pi h1).prod (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => lamF_cpt)).image cf)
    fun k hk => ⟨key k hk, key k⁻¹ (inv_mem hk)⟩

theorem hermLine_of' (hC : CptAll) (hS : PairsStable) (hJ : PairsIrr) (hF : Factor) (hN : NonZeroAn)
    (hW : WeilConv) (hB : ThetaBasic) (hI : PositivityTheory.ThKF.ICont) (hM : MatchEx) : HermLine :=
  hermLine_of hC cptOpen polRank hS hJ hF hN hW hB hI hM

end GlobalTheory.ThK.Dbl

end
