import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.ArchSlice
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.DictHaar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open GlobalTheory.Doubling

theorem eps_fst : (realAd F 1).1 = 1 := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ 1) = 1
  rw [map_one, map_one]

theorem eps_snd : (realAd F 1).2 = 0 := rfl

theorem evI_eq_zero {u : AF F} : evI F u = 0 ↔ u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff

theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] {z : M} : At (evI F) z ↔ realAd F 1 • z = z := by
  constructor
  · intro h
    have := h (1 - realAd F 1) (evI_eq_zero.2 (by
      change (1 : Ainf F) - (realAd F 1).1 = 0
      rw [eps_fst, sub_self]))
    rw [sub_smul, one_smul] at this
    exact (sub_eq_zero.1 this).symm
  · intro h u hu
    rw [← h, smul_smul]
    have : u * realAd F 1 = 0 := Prod.ext (by
      change u.1 * (realAd F 1).1 = 0
      rw [evI_eq_zero.1 hu, zero_mul]) (mul_zero u.2)
    rw [this, zero_smul]

theorem compInf_eps (w : InfinitePlace F) (x : AE F E) : compInf F E w (realAd F 1 • x) = compInf F E w x := by
  rw [Algebra.smul_def, map_mul]
  have : compInf F E w (algebraMap (AF F) (AE F E) (realAd F 1)) = 1 := by
    change ((realAd F 1).1 w) ⊗ₜ[F] (1 : E) = 1
    rw [eps_fst]; rfl
  rw [this, one_mul]

theorem compFin_eps (v : Pl F) (x : AE F E) : compFin F E v (realAd F 1 • x) = 0 := by
  rw [Algebra.smul_def, map_mul]
  have : compFin F E v (algebraMap (AF F) (AE F E) (realAd F 1)) = 0 := by
    change evFin F v (realAd F 1) ⊗ₜ[F] (1 : E) = 0
    rw [show evFin F v (realAd F 1) = 0 from map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v), TensorProduct.zero_tmul]
  rw [this, zero_mul]

instance topRingAF : IsTopologicalRing (AF F) := inferInstanceAs (IsTopologicalRing (Ainf F × Af F))

theorem at_of_fin {x : AE F E} (h : ∀ v, compFin F E v x = 0) : At (evI F) x :=
  at_iff.2 (adele_ext (fun w => compInf_eps w x) fun v => by rw [compFin_eps, h])

theorem fin_of_at {x : AE F E} (h : At (evI F) x) (v : Pl F) : compFin F E v x = 0 := by
  rw [← at_iff.1 h, compFin_eps]

theorem ext_at (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {x y : AE F E}
    (hf : ∀ v, compFin F E v x = compFin F E v y) (e : ∀ w, piInf (τ w) x = piInf (τ w) y) : x = y :=
  adele_ext (fun w => (infEmb_bijective h (τ w)).1 (e w)) hf

def lft (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (c : InfinitePlace F → ℂ) : AE F E :=
  ∑ w, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (inInf w) (inInf_mul w) ((RingEquiv.ofBijective _ (infEmb_bijective h (τ w))).symm (c w))

theorem fin_lft (h : IsCMExt F E σ) (τ) (c) (v : Pl F) : compFin F E v (lft h τ c) = 0 := by
  rw [lft, map_sum]
  exact Finset.sum_eq_zero fun w _ => GlobalTheory.AutFunCompare.map_tensNU_zero (evFin F v) _ _ (fun _ => map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)) _

theorem pi_lft (h : IsCMExt F E σ) (τ) (c) (w : InfinitePlace F) : piInf (τ w) (lft h τ c) = c w := by
  classical
  rw [lft, map_sum, Finset.sum_eq_single w]
  · have := GlobalTheory.AutFunCompare.map_tensNU_self (E := E) (evInf F w) (inInf w) (inInf_mul w) (fun a => Pi.single_eq_same w a)
      ((RingEquiv.ofBijective _ (infEmb_bijective h (τ w))).symm (c w))
    exact (congrArg (infEmb (τ w)) this).trans ((RingEquiv.ofBijective _ (infEmb_bijective h (τ w))).apply_symm_apply _)
  · intro u _ hu
    have := GlobalTheory.AutFunCompare.map_tensNU_zero (E := E) (evInf F w) (inInf u) (inInf_mul u) (fun a => Pi.single_eq_of_ne hu.symm a)
      ((RingEquiv.ofBijective _ (infEmb_bijective h (τ u))).symm (c u))
    exact (congrArg (infEmb (τ w)) this).trans (map_zero _)
  · simp

theorem cont_lft (h : IsCMExt F E σ) (τ) : Continuous (lft h τ) := by
  haveI := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  classical
  refine continuous_finset_sum _ fun w _ => ?_
  have hc : Continuous (inInf (F := F) w) := (continuous_single w).prodMk continuous_const
  exact (GlobalTheory.AutFunCompare.continuous_tensNU (R' := AF F) (inInf w) (inInf_mul w) hc).comp
    ((GlobalTheory.AdelicU.Frames.continuous_infEmb_symm h (τ w)).comp (continuous_apply w))

theorem cont_pi {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf (F := F) (E := E) τ) :=
  (GlobalTheory.Orb.continuous_infEmb τ).comp (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evInf F w).toLinearMap (map_mul (evInf F w))
    ((continuous_apply w).comp continuous_fst))

theorem pi_eps {w : InfinitePlace F} (τ : EmbOver E w) (x : AE F E) : piInf τ (realAd F 1 • x) = piInf τ x :=
  congrArg (infEmb τ) (compInf_eps w x)

theorem pi_tmul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (x : E) :
    piInf τ (a ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 x := rfl

theorem emb_real (h : IsCMExt F E σ) (w : InfinitePlace F) (a : w.Completion) :
    starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w a) = InfinitePlace.Completion.extensionEmbedding w a := by
  have := h.1
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) a, Complex.conj_ofReal]

theorem pi_conj (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (a : AE F E) :
    piInf τ (cA σ a) = starRingEnd ℂ (piInf τ a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x =>
    change piInf τ (c ⊗ₜ[F] σ x) = _
    rw [pi_tmul, pi_tmul, map_mul, emb_real h, h.2.2.2]; rfl

theorem trace_E (h : IsCMExt F E σ) (x : E) : algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  let s := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hs : (1 : E ≃ₐ[F] E) ≠ s := fun e => by
    have := h.2.1
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y =>
        (h.2.2.2 τ y).symm.trans (congrArg τ (AlgEquiv.congr_fun e y).symm))))
  have hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} :=
    (Finset.eq_univ_of_card _ (by
      rw [Finset.card_pair hs, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h.2.2.1])).symm
  rw [trace_eq_sum_automorphisms, hu, Finset.sum_pair hs]
  rfl

theorem trace_tmul (a : AF F) (x : E) :
    Algebra.trace (AF F) (AE F E) (a ⊗ₜ[F] x) = a * algebraMap F (AF F) (Algebra.trace F E x) := by
  have e : (a ⊗ₜ[F] x : AE F E) = a • ((1 : AF F) ⊗ₜ[F] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e, map_smul, smul_eq_mul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem emb_trace (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (a : AE F E) :
    InfinitePlace.Completion.extensionEmbedding w ((Algebra.trace (AF F) (AE F E) a).1 w) = ((2 * (piInf τ a).re : ℝ) : ℂ) := by
  rw [← Complex.add_conj, ← pi_conj h]
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]; exact map_zero _
  | add x y hx hy =>
    rw [map_add (piInf τ), map_add (cA σ), map_add (piInf τ), add_add_add_comm, ← hx, ← hy, ← map_add,
      map_add (Algebra.trace (AF F) (AE F E))]; rfl
  | tmul c x =>
    change _ = _ + piInf τ (c ⊗ₜ[F] σ x)
    rw [← map_add, ← TensorProduct.tmul_add, ← trace_E h, trace_tmul, Algebra.algebraMap_eq_smul_one (A := E),
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', pi_tmul, map_one, mul_one, Algebra.smul_def, mul_comm]

theorem trace_pi_real {ι : Type} [Fintype ι] (y : ι → ℝ) : Algebra.trace ℝ (ι → ℝ) y = ∑ i, y i := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun ℝ ι)]
  simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul]

open Classical in
theorem trace_mixed (h : IsCMExt F E σ) (t : AF F) (r : InfinitePlace F → ℝ)
    (hr : ∀ w, InfinitePlace.Completion.extensionEmbedding w (t.1 w) = r w) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F t) = ∑ w, r w := by
  have := h.1
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
  rw [Algebra.trace_prod_apply, Subsingleton.elim (evI F t).2 0, map_zero, add_zero, trace_pi_real,
    ← (Equiv.subtypeUnivEquiv fun w : InfinitePlace F => IsTotallyReal.isReal w).sum_comp]
  refine Finset.sum_congr rfl fun w _ => ?_
  have := (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2 (t.1 w)).trans (hr w)
  exact_mod_cast this

theorem at_unit_iff {l : (AE F E)ˣ} : At (evI F) ((l : AE F E) - 1) ↔ ∀ v, unitFin F E v l = 1 :=
  ⟨fun h v => Units.ext (by
    have := fin_of_at h v
    rw [map_sub, map_one] at this
    exact sub_eq_zero.1 this), fun h => at_of_fin fun v => by
    rw [map_sub, map_one]
    exact sub_eq_zero.2 (congrArg Units.val (h v))⟩

theorem mem_idAt {l : (AE F E)ˣ} : l ∈ idAt E (evI F) ↔ At (evI F) ((l : AE F E) - 1) := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  have : idAt E (evI F) ≤ ⨅ v, (unitFin F E v).ker :=
    (Subgroup.closure_le _).2 fun l hl => Subgroup.mem_iInf.2 (at_unit_iff.1 hl)
  exact at_unit_iff.2 (Subgroup.mem_iInf.1 (this h))

def uv (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (c : InfinitePlace F → ℂ) : AE F E :=
  1 + lft h τ (c - 1)

theorem fin_uv (h : IsCMExt F E σ) (τ) (c) (v : Pl F) : compFin F E v (uv h τ c) = 1 := by
  rw [uv, map_add, map_one, fin_lft, add_zero]

theorem pi_uv (h : IsCMExt F E σ) (τ) (c) (w : InfinitePlace F) : piInf (τ w) (uv h τ c) = c w := by
  rw [uv, map_add, map_one, pi_lft]; simp

theorem uv_mul (h : IsCMExt F E σ) (τ) {c c' : InfinitePlace F → ℂ} (e : ∀ w, c w * c' w = 1) : uv h τ c * uv h τ c' = 1 :=
  ext_at h τ (fun v => by rw [map_mul, fin_uv, fin_uv, one_mul, map_one]) fun w => by rw [map_mul, pi_uv, pi_uv, e, map_one]

def un (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (c : {c : InfinitePlace F → ℂ // ∀ w, c w ≠ 0}) :
    idAt E (evI F) :=
  ⟨⟨uv h τ c.1, uv h τ fun w => (c.1 w)⁻¹, uv_mul h τ fun w => mul_inv_cancel₀ (c.2 w), uv_mul h τ fun w => inv_mul_cancel₀ (c.2 w)⟩,
    mem_idAt.2 (at_unit_iff.2 fun v => Units.ext (fin_uv h τ _ v))⟩

theorem cont_un (h : IsCMExt F E σ) (τ) : Continuous (un h τ) := by
  haveI := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have hu : Continuous (uv h τ) := continuous_const.add ((cont_lft h τ).comp (continuous_id.sub continuous_const))
  have h2 : Continuous fun c : {c : InfinitePlace F → ℂ // ∀ w, c w ≠ 0} => uv h τ fun w => (c.1 w)⁻¹ :=
    hu.comp (continuous_pi fun w => ((continuous_apply w).comp continuous_subtype_val).inv₀ fun c => c.2 w)
  have h3 : Continuous fun c => (un h τ c).1 := Units.continuous_iff.2 ⟨hu.comp continuous_subtype_val, h2⟩
  exact h3.subtype_mk _

theorem pi_ne {w : InfinitePlace F} (τ : EmbOver E w) (l : (AE F E)ˣ) : piInf τ (l : AE F E) ≠ 0 := (l.isUnit.map _).ne_zero

theorem openEmb (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    IsOpenEmbedding (fun (l : idAt E (evI F)) w => piInf (τ w) (l.1 : AE F E)) ∧
      Set.range (fun (l : idAt E (evI F)) w => piInf (τ w) (l.1 : AE F E)) = {c | ∀ w, c w ≠ 0} := by
  let e : idAt E (evI F) ≃ₜ {c : InfinitePlace F → ℂ // ∀ w, c w ≠ 0} :=
    { toFun := fun l => ⟨fun w => piInf (τ w) (l.1 : AE F E), fun w => pi_ne _ _⟩
      invFun := un h τ
      left_inv := fun l => Subtype.ext (Units.ext (ext_at h τ
        (fun v => (fin_uv h τ _ v).trans (congrArg Units.val (at_unit_iff.1 (mem_idAt.1 l.2) v)).symm) fun w => pi_uv h τ _ w))
      right_inv := fun c => Subtype.ext (funext fun w => pi_uv h τ _ w)
      continuous_toFun := Continuous.subtype_mk (continuous_pi fun w =>
        (cont_pi (τ w)).comp (Units.continuous_val.comp continuous_subtype_val)) _
      continuous_invFun := cont_un h τ }
  have ho : IsOpen {c : InfinitePlace F → ℂ | ∀ w, c w ≠ 0} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (continuous_apply w) continuous_const
  refine ⟨ho.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding, Set.ext fun c => ⟨?_, fun hc => ⟨un h τ ⟨c, hc⟩, ?_⟩⟩⟩
  · rintro ⟨l, rfl⟩ w; exact pi_ne _ _
  · exact funext fun w => pi_uv h τ _ w

theorem isLift_lft (B : Base F E) (hB : B.IsGood σ) : IsLift σ B (lft hB.cm B.emb) where
  supp c := at_of_fin (fin_lft _ _ c)
  pi := pi_lft _ _
  inv a ha := ext_at hB.cm B.emb (fun v => by rw [fin_lft, fin_of_at ha]) (pi_lft _ _ _)
  part a := ⟨at_of_fin fun v => compFin_eps v a, fun w => pi_eps _ a⟩
  conj a w := pi_conj hB.cm _ a
  incl x w := by
    change piInf (B.emb w) ((1 : AF F) ⊗ₜ[F] x) = _
    rw [pi_tmul]
    exact (congrArg (· * _) (map_one _)).trans (one_mul _)
  cont w := cont_pi _
  psi a ha := by
    rw [hB.std.2.2 _ fun u hu => by rw [← map_smul, ha u hu, map_zero],
      trace_mixed hB.cm _ _ fun w => emb_trace hB.cm (B.emb w) a]
  abs l hl := by
    rw [absE_apply, finprod_eq_one_of_forall_eq_one fun v => by rw [at_unit_iff.1 hl v, map_one], mul_one]
    push_cast
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [absEw_eq_sq hB.cm (B.emb w)]; rfl
  idAt l := mem_idAt
  unit c hc := ⟨(un hB.cm B.emb ⟨c, hc⟩).1, mem_idAt.1 (un hB.cm B.emb ⟨c, hc⟩).2, pi_uv _ _ _⟩
  haar x hx := by
    haveI := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
    letI : MeasurableSpace (Loc.idAt E (evI F)) := borel _
    haveI : BorelSpace (Loc.idAt E (evI F)) := ⟨rfl⟩
    exact haar_units _ (openEmb hB.cm B.emb).1 (openEmb hB.cm B.emb).2 (fun a b => funext fun w => map_mul (piInf (B.emb w)) _ _) x

theorem archDict_of : ArchDict := fun _ _ _ _ _ _ _ _ B hB => ⟨_, isLift_lft B hB⟩

end PositivityTheory.ThKG.Loc.Bump

end
