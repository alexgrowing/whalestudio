import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParDec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIsCompactStab
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EisensteinMaximalParabolicIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMajorantFrameCompactSubgroupLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneWittIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneIsotropicBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalOrderFiniteAdelesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleOrderBezoutStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeAdelicStatement
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.IwLineGen

open Formalism.UG (cT UJ hform stabGL)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_nat_smul_mem {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {R : Subring A}
    (hc : IsCompact (R : Set A)) (hN : ∀ a : A, ∃ N : ℕ, N ≠ 0 ∧ (N : A) * a ∈ R) {n : ℕ} {L : Submodule R (Fin n → A)}
    (hL : IsOpen (L : Set (Fin n → A))) (v : Fin n → A) : ∃ N : ℕ, N ≠ 0 ∧ (N : A) • v ∈ L := by
  choose N hN0 hNv using fun i => hN (v i)
  let K : AddSubgroup (Fin n → A) := AddSubgroup.pi Set.univ fun _ => R.toAddSubgroup
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_univ_pi fun _ => hc)
  have hv : ((∏ i, N i : ℕ) : A) • v ∈ K := fun i _ => by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Pi.smul_apply, smul_eq_mul, Nat.cast_mul, mul_assoc]
    exact mul_mem (natCast_mem R _) (hNv i)
  let U := L.toAddSubgroup.addSubgroupOf K
  haveI : Finite (K ⧸ U) := AddSubgroup.quotient_finite_of_isOpen U (hL.preimage continuous_subtype_val)
  refine ⟨U.index * ∏ i, N i, mul_ne_zero AddSubgroup.index_ne_zero_of_finite (Finset.prod_ne_zero_iff.2 fun i _ => hN0 i), ?_⟩
  rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
  exact U.nsmul_index_mem ⟨_, hv⟩

omit [NumberField F] [NumberField E] in
theorem hform_map (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hform (sigR R σ) (JR R J) (fun i => inclR R (x i)) (fun i => inclR R (y i)) =
      inclR (F := F) R (hform (σ : E →+* E) J x y) := by
  simp [hform, JR, map_sum, sigR, inclR]

theorem fin_iwasawa (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {x y : Fin n → E}
    (hxx : hform (σ : E →+* E) J x x = 0) (hxy : hform (σ : E →+* E) J x y = 1) :
    ∃ K : Subgroup (GFin σ J), IsOpen (K : Set (GFin σ J)) ∧ IsCompact (K : Set (GFin σ J)) ∧ ∀ g : GFin σ J, ∃ k ∈ K,
      ∃ t : Af F ⊗[F] E, (matHom _ σ J (g * k⁻¹)).1 *ᵥ (fun i => inclR (Af F) (x i)) = t • fun i => inclR (Af F) (x i) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Af F)
  haveI : T2Space (Af F ⊗[F] E) := e.isEmbedding.t2Space
  obtain ⟨R, ι, hι, hc, ho, hR, hN⟩ := GlobalTheory.T.exists_maximal_order_finite_adeles F E σ
  have hm : ∀ a, ι.symm a ∈ R ↔ a ∈ {a : FiniteAdeleRing (𝓞 E) E | ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (a P) ≤ 1} :=
    fun a => by rw [hι, ι.apply_symm_apply]; rfl
  obtain ⟨hB, hQ, hS⟩ := GlobalTheory.T.finite_adele_order_bezout E _ (fun _ => Iff.rfl)
  have hσ' : ∀ a, sigR (Af F) σ (sigR (Af F) σ a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR, hσ]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hu : ∀ N : ℕ, N ≠ 0 → IsUnit (N : Af F ⊗[F] E) := fun N h => by
    simpa using (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 h : (N : E) ≠ 0)).map (inclR (F := F) (Af F))
  have hJ' : ∀ i j, sigR (Af F) σ (JR (F := F) (Af F) J j i) = JR (F := F) (Af F) J i j := fun i j => by
    simp [sigR, JR, inclR, hJ.1]
  obtain ⟨L, hfg, hLo, hLc, hL, hE, hmax⟩ := GlobalTheory.T.exists_self_dual_lattice_adelic _ (sigR (Af F) σ) hσ' R hc ho hR hN hu n (JR (Af F) J) hJ' (by
    rw [show JR (F := F) (Af F) J = (inclR (F := F) (Af F)).mapMatrix J from rfl, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 hJ.2).map _)
  have hfull : ∀ v, ∃ c : (Af F ⊗[F] E)ˣ, c.1 • v ∈ L := fun v => by
    obtain ⟨N, hN0, h⟩ := exists_nat_smul_mem hc hN hLo v
    exact ⟨(hu N hN0).unit, h⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.EvenLatIwasawa.isOpen_isCompact_stab (J := JR (Af F) J)
    (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Af F) σ) hfg hfull hLo hLc
  refine ⟨(stabGL L).subgroupOf _, h1, h2, fun g => ?_⟩
  refine (GlobalTheory.EvenLatIwasawa.iwasawa_line (x := fun i => inclR (Af F) (x i)) (y := fun i => inclR (Af F) (y i))
    hσ' hJ' hR (fun a b => ?_) (fun p hp q hq => ?_) (fun c hc => ?_) hL hE hfg hfull hmax
    (by rw [hform_map, hxx, map_zero]) (by rw [hform_map, hxy, map_one]) g.2).elim
    fun k ⟨hk, t, ht⟩ => ⟨⟨k, hk.1⟩, hk.2, t, ht⟩
  · obtain ⟨u, hu, v, hv, r, hr, r', hr', e1, e2⟩ := hB (ι a) (ι b)
    exact ⟨_, (hm u).2 hu, _, (hm v).2 hv, _, (hm r).2 hr, _, (hm r').2 hr', ι.injective (by simpa using e1),
      ι.injective (by simpa using e2)⟩
  · obtain ⟨u, hu, v, hv, r, hr, r', hr', e1, e2⟩ := hQ (ι p) ((hι p).1 hp) (ι q) ((hι q).1 hq)
    exact ⟨_, (hm u).2 hu, _, (hm v).2 hv, _, (hm r).2 hr, _, (hm r').2 hr', ι.injective (by simpa using e1),
      ι.injective (by simpa using e2)⟩
  · obtain ⟨u, hu, v, hv, e1, e2, h⟩ := hS (ι c) ((hι c).1 hc)
    refine ⟨_, (hm u).2 hu, _, (hm v).2 hv, ι.injective (by simpa using e1), ι.injective (by simpa using e2),
      fun m hm1 m' hm' e3 a ha => ?_⟩
    obtain ⟨d, hd, e4⟩ := h _ ((hι m).1 hm1) _ ((hι m').1 hm') (by rw [← map_mul, e3, map_one]) _ ((hι a).1 ha)
    exact ⟨_, (hm d).2 hd, ι.injective (by simpa using e4)⟩

theorem adelic_iwasawa (hcm : IsCMExt F E σ) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {x y : Fin n → E} (hxx : hform (σ : E →+* E) J x x = 0) (hxy : hform (σ : E →+* E) J x y = 1)
    {c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)}
    (hc : ∀ w, ∃ ε : Fin n → Bool, cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
      Matrix.diagonal fun i => if ε i then 1 else -1) :
    ∃ Kf : Subgroup (GAd σ J), IsCompact (Kf : Set (GAd σ J)) ∧ Kf ≤ finPts σ J ∧
      (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ U ⊓ finPts σ J ≤ Kf) ∧
      ∀ g : GAd σ J, ∃ (p : GAd σ J) (t : (AE F E)ˣ), (matHom (AF F) σ J p).1 *ᵥ incV F x = t.1 • incV F x ∧
        ∃ k ∈ GlobalTheory.UAut.majCpt σ J c, ∃ k₂ ∈ Kf, g = p * (k * k₂) := by
  obtain ⟨K, hKo, hKc, hK⟩ := fin_iwasawa hσ hJ hxx hxy
  refine ⟨K.map (ofFin σ J), by rw [Subgroup.coe_map]; exact hKc.image (continuous_ofFin σ J), ?_,
    ⟨K.comap (projFin σ J), hKo.preimage (continuous_projFin σ J), fun g hg => ⟨_, hg.1, ?_⟩⟩, fun g => ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact mem_finPts.2 (by simp)
  · exact ext_inf_fin σ J (by simp [mem_finPts.1 hg.2]) (by simp)
  let C : Matrix (Fin n) (Fin 1) E := Matrix.of fun i _ => x i
  let D : Matrix (Fin 1) (Fin n) E := Matrix.of fun _ j => ∑ i, σ (y i) * J i j
  have hD : D * C = 1 := by
    have := GlobalTheory.EvenLatIwasawa.hform_swap (σ := (σ : E →+* E)) hσ hJ.1 x y
    rw [hxy, map_one, hform, Finset.sum_comm] at this
    ext i j
    rw [Subsingleton.elim i j, Matrix.one_apply_eq, ← this]
    simp [D, C, Matrix.mul_apply, Finset.sum_mul]
  have hCC : cT (σ : E →+* E) C * J * C = 0 := by
    ext i j
    rw [Matrix.zero_apply, ← hxx, hform, Finset.sum_comm]
    simp [C, cT, Matrix.mul_apply, Finset.sum_mul]
  have hloc : ∀ w : InfinitePlace F, ∃ k ∈ stabArch σ J w (c w),
      GlobalTheory.EisMaxCompare.Keeps w.Completion C (projArch σ J w g * k⁻¹) := fun w => by
    obtain ⟨ε, hε⟩ := hc w
    have h0 : cT (sigR w.Completion σ) (C.map (inclR (F := F) w.Completion)) * JR (F := F) w.Completion J *
        C.map (inclR (F := F) w.Completion) = 0 := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map (σ : E →+* E) _ _ (fun x => by simp [sigR, inclR]), JR,
        ← Matrix.map_mul, ← Matrix.map_mul, hCC, Matrix.map_zero _ (map_zero _)]
    obtain ⟨k, hk, hk', β, hβ⟩ := GlobalTheory.Core.Rk.IwIso.local_at_arch hcm J w _ ε hε _ h0
      (matHom w.Completion σ J (projArch σ J w g)) (projArch σ J w g).2
    exact ⟨⟨k, hk⟩, GlobalTheory.Core.Rk.IwIso.mem_stabArch_of σ J w _ ⟨k, hk⟩ hk', β, hβ⟩
  choose kk hkk hβ using hloc
  obtain ⟨k₂, hk₂, s, hs⟩ := hK (projFin σ J g)
  let k := ofInf σ J (embArchPi σ J kk)
  have hp : g * (k * ofFin σ J k₂)⁻¹ ∈ GlobalTheory.UAut.parFlag σ J C fun _ => 0 := by
    refine GlobalTheory.EisMaxCompare.mem_parFlag_of_local hD _ (fun w => ?_) fun v => ?_
    · simpa [k] using hβ w
    · have e : proj σ J v (g * (k * ofFin σ J k₂)⁻¹) = projFinLoc σ J v (projFin σ J g * k₂⁻¹) := by simp [k]
      rw [e]
      let φ : Af F ⊗[F] E →+* Fv F v ⊗[F] E := (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)).toRingHom
      have hφ : ∀ a, φ (inclR (Af F) a) = inclR _ a := fun a => by simp [φ, inclR]
      refine ⟨Matrix.of fun _ _ => φ s, ?_⟩
      ext i j
      have := congrArg φ (congrFun hs i)
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hφ, Pi.smul_apply, smul_eq_mul] at this
      simp only [Matrix.mul_apply, Matrix.map_apply, C, Matrix.of_apply, Fin.sum_univ_one]
      rw [mul_comm _ (φ s), ← this]
      rfl
  obtain ⟨B, hB⟩ := (GlobalTheory.IndefiniteRowSideFullHecke.DeterminantHeightFlags.mem_parFlag_iff σ J hD _).1 hp
  refine ⟨_, Matrix.GeneralLinearGroup.det B, ?_, k, GlobalTheory.UAut.mem_majCpt.2 ⟨mem_infPts.2 (by simp [k]), fun w => by
    simpa [k] using hkk w⟩, _, ⟨k₂, hk₂, rfl⟩, (inv_mul_cancel_right _ _).symm⟩
  funext i
  have := congrFun (congrFun hB i) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_one] at this
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one, Pi.smul_apply, smul_eq_mul, mul_comm]
  exact this

theorem iwasawa : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ χ : Chr F E, (∀ t : Eˣ, χ (Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom t) = 1) → Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) →
      ∀ K₁ : Subgroup (GAd σ (c₀ • W₁.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W₁.J.map σ) K₁ →
      ∀ ψ : GAd σ (c₀ • W₁.J.map σ) → ℂ, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ ψ →
      ∃ K' : Subgroup (GAd σ (c₀ • W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K' ∧ (∀ y ∈ K₁, GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M y ∈ K') ∧
      (∀ (t : (AE F E)ˣ) (y : GAd σ (c₀ • W₁.J.map σ)) (g : GAd σ (c₀ • W.J.map σ)), GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t y g → g ∈ K' → y ∈ K₁) ∧
      ∃ Kf : Subgroup (GAd σ (c₀ • W.J.map σ)), IsCompact (Kf : Set (GAd σ (c₀ • W.J.map σ))) ∧ Kf ≤ finPts σ (c₀ • W.J.map σ) ∧
      (∃ U : Subgroup (GAd σ (c₀ • W.J.map σ)), IsOpen (U : Set (GAd σ (c₀ • W.J.map σ))) ∧ U ⊓ finPts σ (c₀ • W.J.map σ) ≤ Kf) ∧
      ∀ g : GAd σ (c₀ • W.J.map σ), ∃ (t : (AE F E)ˣ) (y : GAd σ (c₀ • W₁.J.map σ)) (p : GAd σ (c₀ • W.J.map σ)), GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t y p ∧ ∃ k ∈ K', ∃ k₂ ∈ Kf, g = p * (k * k₂) := by
  intro F E _ _ _ _ _ σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hJ₁ hJ M hM hML _ r Xf Yf _ X' Y' hW hX _ _ _ _ _ _
    K₁ hK₁ _ _
  obtain ⟨K, hKi, hKc, hKe⟩ := GlobalTheory.T.hyperbolic_plane_isotropic_basis F E σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hJ₁ hJ M hM hML K₁
    hK₁.1.1 hK₁.1.2
  obtain ⟨c, hc, hKle⟩ := GlobalTheory.CptMajorant.exists_frame_le_majCpt F E σ hcm n _ hJ K hKi hKc
  have hmax := GlobalTheory.UAut.isMaxCpt_majCpt hcm hc
  have key : ∀ Z : Matrix (Fin n) (Fin (r + 1)) E, hform (σ : E →+* E) (c₀ • W.J.map σ) H.x (fun k => Z k 0) =
      (cT (σ : E →+* E) X' * (c₀ • W.J.map σ) * Z) 0 0 := fun Z => by
    rw [hform, Finset.sum_comm]
    simp only [cT, Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply, hX]
  obtain ⟨Kf, h1, h2, h3, h4⟩ := adelic_iwasawa hcm hσ hJ (x := H.x) (y := fun k => Y' k 0)
    (by have := key X'; rw [hW.1, funext hX] at this; exact this) (by rw [key, hW.3, Matrix.one_apply_eq]) hc
  refine ⟨_, hmax, fun y hy => hKle (hKe y hy), GlobalTheory.T.hyperbolic_plane_complement_decomposition F E σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hJ₁ hJ
    M hM hML r X' Y' hW hX K₁ hK₁ _ hmax.1.1 hmax.1.2 fun y hy => hKle (hKe y hy), Kf, h1, h2, h3, fun g => ?_⟩
  obtain ⟨p, t, ht, h⟩ := h4 g
  obtain ⟨y, hy⟩ := GlobalTheory.T.hyperbolic_plane_witt_index F E σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hJ₁ hJ M hM hML r X' Y' hW hX p t ht
  exact ⟨t, y, p, hy, h⟩

end GlobalTheory.IwLineGen

end
