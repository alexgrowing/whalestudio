import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.ContinuousExpG
import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Grp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open Classical in

def ind (S : Finset (Pl F)) : Af F :=
  ⟨fun u => if u ∈ S then 1 else 0, Eventually.of_forall fun u => by
    by_cases h : u ∈ S
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

open Classical in
theorem ev_ind (S : Finset (Pl F)) (u : Pl F) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (ind S) = if u ∈ S then 1 else 0 := rfl

theorem fin_ext {a b : Af F} (h : ∀ u, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u a = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u b) : a = b :=
  Subtype.ext (funext h)

theorem tendsto_ind_mul (α : Af F) : Tendsto (fun S : Finset (Pl F) => ind S * α) atTop (𝓝 α) := by
  classical
  let T : Set (Pl F) := {u | α u ∈ (u.adicCompletionIntegers F : Set (u.adicCompletion F))}
  have hT : cofinite ≤ 𝓟 T := le_principal_iff.2 α.2
  let f : Finset (Pl F) → RestrictedProduct (fun u : Pl F => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 T) :=
    fun S => ⟨fun u => if u ∈ S then α u else 0, fun u hu => by
      by_cases h : u ∈ S
      · simp only [Set.mem_setOf_eq, h, if_true]; exact hu
      · simp only [Set.mem_setOf_eq, h, if_false]; exact zero_mem _⟩
  let a : RestrictedProduct (fun u : Pl F => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 T) := ⟨fun u => α u, fun u hu => hu⟩
  have hf : Tendsto f atTop (𝓝 a) := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro u
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({u} : Finset _)] with S hS
    exact (if_pos (hS (Finset.mem_singleton_self u))).symm
  have h2 := ((RestrictedProduct.continuous_inclusion hT).tendsto a).comp hf
  refine Tendsto.congr (fun S => fin_ext fun u => ?_) h2
  rw [map_mul, ev_ind]
  change (if u ∈ S then α u else 0) = _
  split_ifs
  · exact (one_mul _).symm
  · exact (zero_mul _).symm

def eps (S : Finset (Pl F)) : AF F := ((1, ind S) : Ainf F × Af F)

def idm (v : Pl F) : AF F := ((0, ind {v}) : Ainf F × Af F)

theorem ind_sq (S : Finset (Pl F)) : ind S * ind S = ind S := fin_ext fun u => by rw [map_mul, ev_ind]; split_ifs <;> simp

theorem eps_sq (S : Finset (Pl F)) : eps S * eps S = eps S := Prod.ext (one_mul _) (ind_sq S)

theorem idm_sq (v : Pl F) : idm v * idm v = idm v := Prod.ext (mul_zero _) (ind_sq _)

theorem eps_cons (S : Finset (Pl F)) (v : Pl F) (hv : v ∉ S) : eps (S.cons v hv) = eps S + idm v ∧ eps S * idm v = 0 := by
  refine ⟨Prod.ext (add_zero _).symm (fin_ext fun u => ?_), Prod.ext (mul_zero _) (fin_ext fun u => ?_)⟩
  · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (ind _) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (ind S + ind {v})
    rw [map_add, ev_ind, ev_ind, ev_ind]
    by_cases h : u = v
    · simp [h, hv]
    · have hm : u ∈ S.cons v hv ↔ u ∈ S := Finset.mem_cons.trans (or_iff_right h)
      by_cases h' : u ∈ S
      · rw [if_pos (hm.2 h'), if_pos h', if_neg (by simpa using h), add_zero]
      · rw [if_neg (fun x => h' (hm.1 x)), if_neg h', if_neg (by simpa using h), add_zero]
  · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u (ind S * ind {v}) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u 0
    rw [map_mul, ev_ind, ev_ind, map_zero]
    by_cases h : u = v
    · simp [h, hv]
    · simp [h]

theorem tendsto_eps (x : AE F E) : Tendsto (fun S : Finset (Pl F) => eps S • x) atTop (𝓝 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simpa only [smul_zero] using tendsto_const_nhds
  | tmul a e =>
    have h0 : Tendsto (fun S : Finset (Pl F) => eps S * a) atTop (𝓝 a) :=
      Tendsto.congr (f₁ := fun S => ((a.1, ind S * a.2) : Ainf F × Af F)) (fun S => Prod.ext (one_mul _).symm rfl)
        ((tendsto_const_nhds (x := a.1)).prodMk_nhds (tendsto_ind_mul a.2))
    have h := h0.smul_const ((1 : AF F) ⊗ₜ[F] e)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  | add x y hx hy => simpa only [smul_add] using hx.add hy

variable {d : ℕ} {J : Matrix (Fin d) (Fin d) E}

theorem mix_mul {a : AF F} (ha : a * a = a) (x y : Matrix (Fin d) (Fin d) (AE F E)) :
    (1 + a • (x - 1)) * (1 + a • (y - 1)) = 1 + a • (x * y - 1) := by
  rw [show x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) by noncomm_ring, add_mul, mul_add, mul_add, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, ha, smul_add, smul_add, one_mul, one_mul, mul_one]
  abel

def piece (a : AF F) (ha : a * a = a) (g : UA σ J) : UA σ J :=
  ⟨⟨1 + a • (mat g - 1), 1 + a • (mat g⁻¹ - 1), by rw [mix_mul ha, mat_mul_inv, sub_self, smul_zero, add_zero],
    by rw [mix_mul ha, mat_inv_mul, sub_self, smul_zero, add_zero]⟩, by
    change (1 + a • (mat g - 1))ᵀ * incM F J * (cA σ).mapMatrix (1 + a • (mat g - 1)) = incM F J
    have h := mat_unit g
    rw [map_add, map_smul, map_sub, map_one, AlgHom.mapMatrix_apply, Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_sub, Matrix.transpose_one]
    generalize (mat g).map (cA σ) = y at h ⊢
    generalize (mat g)ᵀ = x at h ⊢
    generalize incM F J = K at h ⊢
    have e : (x - 1) * K + K * (y - 1) + (x - 1) * K * (y - 1) = 0 := by
      rw [show (x - 1) * K + K * (y - 1) + (x - 1) * K * (y - 1) = x * K * y - K by noncomm_ring, h, sub_self]
    have e2 := congrArg (a • ·) e
    simp only [smul_add, smul_zero] at e2
    rw [add_mul, add_mul, mul_add, mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      smul_smul, ha, one_mul, mul_one, mul_one, add_assoc, ← add_assoc (a • _), add_comm (a • (K * _)), e2, add_zero]⟩

theorem mat_piece {a : AF F} (ha : a * a = a) (g : UA σ J) : mat (piece a ha g) = 1 + a • (mat g - 1) := rfl

theorem piece_add {a b c : AF F} (ha : a * a = a) (hb : b * b = b) (hc : c * c = c) (e : c = a + b) (o : a * b = 0) (g : UA σ J) :
    piece c hc g = piece a ha g * piece b hb g := mat_inj (by
  rw [mat_mul, mat_piece, mat_piece, mat_piece, e, add_mul, mul_add, mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_smul, smul_smul, o, zero_smul, add_smul, one_mul, one_mul, mul_one]
  abel)

theorem tendsto_piece (g : UA σ J) : Tendsto (fun S : Finset (Pl F) => piece (eps S) (eps_sq S) g) atTop (𝓝 g) := by
  have h : ∀ M : Matrix (Fin d) (Fin d) (AE F E), Tendsto (fun S : Finset (Pl F) => 1 + eps S • (M - 1)) atTop (𝓝 M) := fun M => by
    have : Tendsto (fun S : Finset (Pl F) => eps S • (M - 1)) atTop (𝓝 (M - 1)) :=
      tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => tendsto_eps _
    simpa using this.const_add 1
  refine (IsEmbedding.subtypeVal.tendsto_nhds_iff).2 ((Units.isEmbedding_embedProduct.tendsto_nhds_iff).2 ?_)
  exact (h _).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (h (mat g⁻¹)))

theorem piInf_piece (S : Finset (Pl F)) (g : UA σ J) {w : InfinitePlace F} (τ : EmbOver E w) :
    (mat (piece (eps S) (eps_sq S) g)).map (piInf τ) = (mat g).map (piInf τ) := by
  have h : ∀ z : AE F E, compInf F E w (eps S • z) = compInf F E w z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero]
    | tmul a x =>
      exact congrArg (fun b => GlobalTheory.AutFunCompare.evW w b ⊗ₜ[F] x) (one_mul a.1)
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  ext i j
  change piInf τ ((1 : Matrix _ _ _) i j + eps S • (mat g i j - (1 : Matrix _ _ _) i j)) = piInf τ (mat g i j)
  rw [map_add, piInf, RingHom.comp_apply, RingHom.comp_apply, h, ← map_add, ← map_add, add_sub_cancel, RingHom.comp_apply]

theorem piece_prod {W : Spc F E d} (g : UA σ W.J) (S : Finset (Pl F)) : ∃ l : List (UA σ W.J),
    (∀ h ∈ l, ∃ v, h ∈ UAt σ W (evFin F v)) ∧ piece (eps S) (eps_sq S) g = piece (eps ∅) (eps_sq ∅) g * l.prod := by
  induction S using Finset.cons_induction with
  | empty => exact ⟨[], by simp, by simp⟩
  | cons v S hv ih =>
    obtain ⟨l, h1, h2⟩ := ih
    refine ⟨l ++ [piece (idm v) (idm_sq v) g], fun h hh => ?_, ?_⟩
    · rcases List.mem_append.1 hh with k | k
      · exact h1 h k
      · refine ⟨v, fun u hu => ?_⟩
        have : u * idm v = 0 := Prod.ext (mul_zero u.1) (fin_ext fun x => by
          change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F x (u.2 * ind {v}) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F x 0
          rw [map_mul, ev_ind, map_zero]
          split_ifs with e
          · rw [Finset.mem_singleton.1 e, mul_one]; exact hu
          · exact mul_zero _)
        rw [List.mem_singleton.1 k, mat_piece, add_sub_cancel_left, smul_smul, this, zero_smul]
    · rw [piece_add (eps_sq S) (idm_sq v) _ (eps_cons S v hv).1 (eps_cons S v hv).2, h2, List.prod_append, List.prod_singleton,
        mul_assoc]

theorem piece_inf {W : Spc F E d} (g : UA σ W.J) : piece (eps ∅) (eps_sq ∅) g ∈ UAt σ W (evI F) := fun u hu => by
  have : u * eps ∅ = 0 := Prod.ext ((mul_one u.1).trans ((map_eq_zero_iff _ (RingEquiv.injective _)).1 hu)) (fin_ext fun x => by
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F x (u.2 * ind ∅) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F x 0
    rw [map_mul, ev_ind, map_zero, if_neg (Finset.notMem_empty x), mul_zero])
  rw [mat_piece, add_sub_cancel_left, smul_smul, this, zero_smul]

theorem level_sch (hL : PositivityTheory.ThKEst.Level) {n : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW om r s r' s'}
    (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) :
    ∀ᶠ u in 𝓝 (1 : UA σ W.J), (∀ w, (mat u).map (piInf (B.emb w)) = 1) → om (1, u) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨U, hU, h⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp g hg
    exact mem_of_superset hU fun u hu k => h u hu k f
  | zero => exact Eventually.of_forall fun _ _ => map_zero _
  | add x y _ _ hx hy => filter_upwards [hx, hy] with u h1 h2 k using by rw [map_add, h1 k, h2 k]
  | smul a x _ hx => filter_upwards [hx] with u h1 k using by rw [map_smul, h1 k]

theorem decomp_of (hL : PositivityTheory.ThKEst.Level) : Decomp := by
  intro F E _ _ _ _ _ σ B a a' G X om om' t k hk Φ hΦ Φ' hΦ'
  have h1 : Tendsto (fun S : Finset (Pl F) => (piece (eps S) (eps_sq S) k)⁻¹ * k) atTop (𝓝 1) := by
    rw [← inv_mul_cancel k]
    exact (tendsto_piece k).inv.mul_const k
  obtain ⟨S, h2, h3⟩ := (h1.eventually ((level_sch hL (PositivityTheory.ThKG.pairV t) hΦ).and (level_sch hL (PositivityTheory.ThKG.pairV' t) hΦ'))).exists
  have h4 : ∀ w, (mat ((piece (eps S) (eps_sq S) k)⁻¹ * k)).map (piInf (B.emb w)) = 1 := fun w => by
    rw [mat_mul, Matrix.map_mul, ← piInf_piece S k, ← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨l, l1, l2⟩ := piece_prod k S
  exact ⟨_, ⟨piece_inf k, fun w => (piInf_piece ∅ k _).symm ▸ hk w⟩, l, _, l1, by rw [← l2, mul_inv_cancel_left], h2 h4, h3 h4⟩

theorem exists_ins {ι : Type} [DecidableEq ι] {Y : ι → Type} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] (T : Finset ι) (v : ι)
    (s : ∀ i, Y i) (Op : Module.End ℂ (Y v)) :
    ∃ e : (PiTensorProduct ℂ fun u : T => Y u) →ₗ[ℂ] PiTensorProduct ℂ fun u : (insert v T : Finset ι) => Y u,
      ∀ y : ∀ i, Y i, (∀ i ∉ T, y i = s i) → e (PiTensorProduct.tprod ℂ fun u : T => y u) =
        PiTensorProduct.tprod ℂ fun u : (insert v T : Finset ι) => Function.update y v (Op (y v)) u := by
  have hT := Finset.subset_insert v T
  let ext : (∀ u : T, Y u) → ∀ u : (insert v T : Finset ι), Y u := fun w u => if h : (u : ι) ∈ T then w ⟨u, h⟩ else s u
  have hupd : ∀ (inst : DecidableEq T) (w : ∀ u : T, Y u) (i : T) (z : Y i),
      ext (@Function.update _ _ inst w i z) = Function.update (ext w) ⟨i.1, hT i.2⟩ z := by
    intro inst w i z
    funext u
    by_cases hv : u = ⟨i.1, hT i.2⟩
    · subst hv
      simp [ext]
    · rw [Function.update_of_ne hv]
      by_cases h : (u : ι) ∈ T
      · have hne : (⟨u, h⟩ : T) ≠ i := fun e => hv (Subtype.ext (show (u : ι) = i.1 by rw [← e]))
        simp only [ext, dif_pos h]
        rw [Function.update_of_ne hne]
      · simp only [ext, dif_neg h]
  let m : MultilinearMap ℂ (fun u : T => Y u) (PiTensorProduct ℂ fun u : (insert v T : Finset ι) => Y u) :=
    { toFun := fun w => PiTensorProduct.tprod ℂ (ext w)
      map_update_add' := fun {inst} w i x y => by
        simp only [hupd inst]
        exact (PiTensorProduct.tprod ℂ).map_update_add _ _ _ _
      map_update_smul' := fun {inst} w i c x => by
        simp only [hupd inst]
        exact (PiTensorProduct.tprod ℂ).map_update_smul _ _ _ _ }
  refine ⟨PiTensorProduct.map (Function.update (fun j : (insert v T : Finset ι) => (LinearMap.id : Y j →ₗ[ℂ] Y j))
    ⟨v, Finset.mem_insert_self v T⟩ Op) ∘ₗ PiTensorProduct.lift m, fun y hy => ?_⟩
  have e : ext (fun u : T => y u) = fun u : (insert v T : Finset ι) => y u := funext fun u => by
    by_cases h : (u : ι) ∈ T
    · simp [ext, h]
    · simp [ext, h, hy _ h]
  rw [LinearMap.comp_apply, PiTensorProduct.lift.tprod]
  change PiTensorProduct.map _ (PiTensorProduct.tprod ℂ (ext fun u : T => y u)) = _
  rw [e, PiTensorProduct.map_tprod]
  congr 1
  funext u
  by_cases h : u = ⟨v, Finset.mem_insert_self v T⟩
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne (show (u : ι) ≠ v from fun e => h (Subtype.ext e))]; rfl

theorem common_op {V V' P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup P] [Module ℂ P]
    {S : Submodule ℂ V} {S' : Submodule ℂ V'} {p : V →ₗ[ℂ] P} {p' : V' →ₗ[ℂ] P} (h : S.map p = ⊤) (A : V →ₗ[ℂ] V)
    (A' : V' →ₗ[ℂ] V') (e : ∀ x ∈ S, ∀ x' ∈ S', p x = p' x' → p (A x) = p' (A' x')) :
    ∃ Op : Module.End ℂ P, (∀ x ∈ S, Op (p x) = p (A x)) ∧ ∀ x' ∈ S', Op (p' x') = p' (A' x') := by
  have hq : Function.Surjective (p.domRestrict S) := fun u => by
    obtain ⟨x, h1, h2⟩ : u ∈ S.map p := h ▸ Submodule.mem_top
    exact ⟨⟨x, h1⟩, h2⟩
  obtain ⟨s, hs⟩ := (p.domRestrict S).exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)
  have hs' : ∀ y, p (s y) = y := LinearMap.congr_fun hs
  refine ⟨p ∘ₗ A ∘ₗ S.subtype ∘ₗ s, fun x hx => ?_, fun x' hx' => e _ (s _).2 _ hx' (hs' _)⟩
  have := e (s (p x) - x) (sub_mem (s _).2 hx) 0 (zero_mem _) (by rw [map_sub, hs', sub_self, map_zero])
  rw [map_sub, map_sub, map_zero, map_zero, sub_eq_zero] at this
  exact this

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'}
  {Rf : FinMaps F a a'}

theorem match_inf (hA : PositivityTheory.ThKF.ArchOp) (hm : IsMatched B G X om om' R Rf) {k : UA σ G.W.J} (hk : k ∈ KInf σ G.W B.emb) {Φ Φ'}
    (H : PolMatch B G X R Rf Φ Φ') : PolMatch B G X R Rf (om (1, k) Φ) (om' (1, k) Φ') := by
  have t := hm.triple
  have one : ∀ {n : ℕ} (Y : Spc F E n), (1 : UA σ Y.J) ∈ KInf σ Y B.emb := fun Y =>
    ⟨fun u _ => by rw [mat_one, sub_self, smul_zero], fun w => by
      rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _⟩
  obtain ⟨A, a1, a2⟩ := hA F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (PositivityTheory.ThKG.pairV t) 1 (one _).1 k hk.1
  obtain ⟨A', b1, b2⟩ := hA F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (PositivityTheory.ThKG.pairV' t) 1 (one _).1 k hk.1
  obtain ⟨Op, o1, o2⟩ := common_op (S' := G.M'.Pol B.ψ B.emb) hm.real.quot.onto (A : _ →ₗ[ℂ] _) (A' : _ →ₗ[ℂ] _) fun x hx x' hx' e =>
    hm.real.cpt k hk _ hx _ hx' _ _ (a1.2 _) (b1.2 _) e
  obtain ⟨T, hT, m, m', f, φ, f', φ', h1, h2, rfl, rfl, e⟩ := H
  have cof : ∀ {P : Pl F → Prop}, (∀ v ∉ T, P v) → ∀ᶠ v in cofinite, P v := fun h => T.eventually_cofinite_notMem.mono h
  refine ⟨T, hT, m, m', fun i => A (f i), φ, fun i => A' (f' i), φ', fun i => ⟨a2 (one _) hk _ (h1 i).1, (h1 i).2⟩,
    fun i => ⟨b2 (one _) hk _ (h2 i).1, (h2 i).2⟩, ?_, ?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA t.geo.hM (φ i) (h1 i).2.1 (cof (h1 i).2.2)
    rw [e, e, a1.1 _ g hg]
  · rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA t.geo.hM' (φ' i) (h2 i).2.1 (cof (h2 i).2.2)
    rw [e, e, b1.1 _ g hg]
  · have := congrArg (Op.rTensor _) e
    simp only [map_sum, LinearMap.rTensor_tmul, o1 _ (h1 _).1, o2 _ (h2 _).1] at this
    exact this

theorem match_fin (hP : PositivityTheory.ThKF.PureAct) (hm : IsMatched B G X om om' R Rf) {v : Pl F} {h : UA σ G.W.J}
    (hh : h ∈ UAt σ G.W (evFin F v)) {Φ Φ'} (H : PolMatch B G X R Rf Φ Φ') : PolMatch B G X R Rf (om (1, h) Φ) (om' (1, h) Φ') := by
  classical
  have t := hm.triple
  obtain ⟨ω, ρ, L⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ G.M om ⟨t.base, ⟨_, _, t.geo.hV⟩, ⟨_, _, t.geo.hW⟩, t.geo.hM, _, _, t.weil⟩ v
  obtain ⟨ω', ρ', L'⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ G.M' om'
    ⟨t.base, ⟨_, _, t.geo.hV'⟩, ⟨_, _, t.geo.hW⟩, t.geo.hM', _, _, t.weil'⟩ v
  have o := PositivityTheory.ThKH.Locrep.one_mem_UAt (σ := σ) G.V v
  have o' := PositivityTheory.ThKH.Locrep.one_mem_UAt (σ := σ) G.V' v
  obtain ⟨Op, o1, o2⟩ := common_op (S' := SB _) (hm.fin.onto v) (ω (1, h)) (ω' (1, h)) fun x hx x' hx' e =>
    hm.fin.equiv v h hh _ hx _ hx' _ (L.pres 1 o h hh _ hx) _ (L'.pres 1 o' h hh _ hx') ((L.acts 1 o h hh _ hx _).2 rfl)
      ((L'.acts 1 o' h hh _ hx' _).2 rfl) e
  obtain ⟨T, hT, m, m', f, φ, f', φ', h1, h2, rfl, rfl, e⟩ := H
  have cof : ∀ {P : Pl F → Prop}, (∀ v ∉ T, P v) → ∀ᶠ v in cofinite, P v := fun h => T.eventually_cofinite_notMem.mono h
  have upd : ∀ {Y : Pl F → Type} (P : ∀ u, Y u → Prop) (y : ∀ u, Y u) (z : Y v), (∀ u, P u (y u)) → P v z →
      ∀ u, P u (Function.update y v z u) := fun P y z h1 h2 u => by
    by_cases e : u = v
    · subst e; rwa [Function.update_self]
    · rw [Function.update_of_ne e]; exact h1 u
  have off : ∀ {Y : Pl F → Type} (y w : ∀ u, Y u) (z : Y v), (∀ u ∉ T, y u = w u) → ∀ u ∉ insert v T, Function.update y v z u = w u :=
    fun y w z h1 u hu => by
      rw [Finset.mem_insert, not_or] at hu
      rw [Function.update_of_ne hu.1, h1 u hu.2]
  obtain ⟨Ω, hΩ⟩ := exists_ins (Y := Rf.Pi) T v (fun u => Rf.p u (G.M.vac u)) Op
  refine ⟨insert v T, hT.trans (Finset.subset_insert v T), m, m', f, fun i => Function.update (φ i) v (ω (1, h) (φ i v)), f',
    fun i => Function.update (φ' i) v (ω' (1, h) (φ' i v)),
    fun i => ⟨(h1 i).1, upd (fun _ x => x ∈ SB _) _ _ (h1 i).2.1 (L.pres 1 o h hh _ ((h1 i).2.1 v)), off _ _ _ (h1 i).2.2⟩,
    fun i => ⟨(h2 i).1, upd (fun _ x => x ∈ SB _) _ _ (h2 i).2.1 (L'.pres 1 o' h hh _ ((h2 i).2.1 v)), off _ _ _ (h2 i).2.2⟩, ?_, ?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    convert (hP F _ v (om (1, h)) (f i) (φ i) (h1 i).2.1 (((cof (h1 i).2.2).and t.geo.hM.std).mono fun _ k => k.1.trans k.2)).2.2 _
      ((L.acts 1 o h hh _ ((h1 i).2.1 v) _).2 rfl)
  · rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    convert (hP F _ v (om' (1, h)) (f' i) (φ' i) (h2 i).2.1 (((cof (h2 i).2.2).and t.geo.hM'.std).mono fun _ k => k.1.trans k.2)).2.2 _
      ((L'.acts 1 o' h hh _ ((h2 i).2.1 v) _).2 rfl)
  · have := congrArg (Ω.lTensor _) e
    simp only [map_sum, LinearMap.lTensor_tmul] at this
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (this.trans (Finset.sum_congr rfl fun i _ => ?_))
    · rw [hΩ (fun u => Rf.p u (φ i u)) fun u hu => by rw [(h1 i).2.2 u hu], o1 _ ((h1 i).2.1 v)]
      congr 2
      funext u
      exact Function.apply_update (fun u => Rf.p u) _ _ _ _
    · rw [hΩ (fun u => Rf.p' u (φ' i u)) fun u hu => by rw [(h2 i).2.2 u hu, (hm.fin.sph u fun k => hu (hT k)).1],
        o2 _ ((h2 i).2.1 v)]
      congr 2
      funext u
      exact (Function.apply_update (fun u => Rf.p' u) _ _ _ _).symm

theorem matchStab_of (hA : PositivityTheory.ThKF.ArchOp) (hPA : PositivityTheory.ThKF.PureAct) (hL : PositivityTheory.ThKEst.Level) (hS : PositivityTheory.ThKCT.SoStab) : MatchStab := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm k hk Φ Φ' hΦ' hP
  have t := hm.triple
  refine ⟨hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (PositivityTheory.ThKG.pairV' t) _ _ hΦ', ?_⟩
  obtain ⟨p1, p2⟩ := PositivityTheory.ThKG.polMatch_mem hP
  obtain ⟨k₀, h0, l, r, h1, rfl, h2, h3⟩ := decomp_of hL F E σ B a a' G X om om' t k hk Φ (PositivityTheory.ThKG.polData_le t.geo.hM p1) Φ'
    (PositivityTheory.ThKG.polData_le t.geo.hM' p2)
  have m : ∀ {n : ℕ} {Y : Spc F E n} (o : Rep σ Y G.W) x y Ψ, o (1, x * y) Ψ = o (1, x) (o (1, y) Ψ) := fun o x y Ψ => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  rw [m, m, m, m, h2, h3]
  refine match_inf hA hm h0 ?_
  clear hk h2 h3
  induction l with
  | nil => simpa only [List.prod_nil, ← Prod.one_eq_mk, map_one, Module.End.one_apply] using hP
  | cons x l ih =>
    obtain ⟨v, hv⟩ := h1 x List.mem_cons_self
    rw [List.prod_cons, m, m]
    exact match_fin hPA hm hv (ih fun h hh => h1 h (List.mem_cons_of_mem _ hh))

end PositivityTheory.ThKEnd.Grp

end
