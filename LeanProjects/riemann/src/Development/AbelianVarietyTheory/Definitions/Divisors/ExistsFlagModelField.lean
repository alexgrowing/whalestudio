import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRingHomOfIsLieComb
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankEqOfExistsUniqueComb
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEigenProjectorRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsOpenImmersionOfSurj

noncomputable section

namespace GlobalTheory.FlagMod.LowRank

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

section Alg

theorem idem_low {R L : Type} [CommRing R] [Field L] (φ : R →+* L) (hφ : Function.Injective φ) {n m : ℕ} (hm : m ≤ 1)
    (e : Matrix (Fin n) (Fin n) R) (he : e * e = e) (N : Submodule L (Fin n → L))
    (hN : ∀ v, v ∈ N ↔ (e.map φ).mulVec v = v) (hr : Module.finrank L N = m) :
    (∑ ix : Fin m → Fin n, ∏ i, e (ix i) (ix i) = 1) ∧
      ∀ ix : Fin m → Fin n, (∏ i, e (ix i) (ix i)) • e = e.submatrix id ix * e.submatrix ix id := by
  have hcol : ∀ k, (fun i => φ (e i k)) ∈ N := fun k => (hN _).2 (by
    funext i
    have := congrArg φ (congrFun (congrFun he i) k)
    rw [Matrix.mul_apply, map_sum] at this
    simpa [Matrix.mulVec, dotProduct] using this)
  obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
  · have hb : N = ⊥ := Submodule.finrank_eq_zero.1 hr
    refine ⟨by simp, fun ix => ?_⟩
    ext i k
    have := hcol k
    rw [hb, Submodule.mem_bot] at this
    have h0 : e i k = 0 := hφ (by rw [map_zero]; exact congrFun this i)
    simp [Matrix.mul_apply, h0]
  · obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 hr
    choose a ha using fun k => hv ⟨_, hcol k⟩
    have hE : ∀ i k, φ (e i k) = a k * v.1 i := fun i k => (congrFun (congrArg Subtype.val (ha k)) i).symm
    constructor
    · apply hφ
      obtain ⟨i, hi⟩ : ∃ i, v.1 i ≠ 0 := by
        by_contra h
        push Not at h
        exact hv0 (Subtype.ext (funext h))
      have h1 := congrFun ((hN _).1 v.2) i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hE] at h1
      rw [map_sum, map_one, ← (Equiv.funUnique (Fin 1) (Fin n)).symm.sum_comp]
      simp only [Fin.prod_univ_one, Equiv.funUnique_symm_apply, uniqueElim_const, hE]
      apply mul_right_cancel₀ hi
      rw [_root_.one_mul, Finset.sum_mul]
      refine Eq.trans (Finset.sum_congr rfl fun j _ => by ring) h1
    · intro ix
      ext i k
      apply hφ
      simp only [Fin.prod_univ_one, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_one,
        Matrix.submatrix_apply, id, map_mul, hE]
      ring

theorem initSpan_low {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {m : ℕ} (hm : m ≤ 1) {v v' : Fin m → N}
    (h : initSpan R v m = initSpan R v' m) (i : ℕ) : initSpan R v i = initSpan R v' i := by
  rcases i with _ | i
  · simp [initSpan]
  · have e : {j : Fin m | (j : ℕ) < i + 1} = {j : Fin m | (j : ℕ) < m} := by
      ext j; have := j.2; simp only [Set.mem_ofPred_eq]; omega
    unfold initSpan at h ⊢
    rw [e, h]

end Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Red

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem initSpan_frVec_top {S : Type} [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) (M : MChart Y)
    (h : ⊤ ≤ (frX P ≫ Y.j) ⁻¹ᵁ M.U) (σ : E →+* ℂ) :
    initSpan S (frVec Y P rfl σ) (Dw.mult σ) = eigLie c (frX P ≫ Y.j) σ := by
  obtain ⟨Λ₀⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev _ M.U h) (frX P) (frX_snd P)
    (spMap_ev _ M.hU h).symm
  let Λ : M.Lift (ev _ M.U h) P.x := frX_fst P ▸ Λ₀
  have eΛ : Λ.xF = frX P := eq_frX P Λ.xF_fst Λ.xF_snd
  have hv : ∀ j, Λ.Vec ((vec M _ h).symm (frVec Y P rfl σ j)) (P.u σ j) := fun j =>
    (vec_iff_toModel h Λ eΛ (frX_fst P) rfl _ (P.tan σ j)).2 (LinearEquiv.apply_symm_apply _ _).symm
  have heig := GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c O β Y M S _ P.x Λ σ
  obtain ⟨hex, htan, hco⟩ := GlobalTheory.Reg.vec_bijective E H Dw l Xo c O β Y M S _ P.x Λ
  refine le_antisymm (Submodule.span_le.2 ?_) fun v hv' => ?_
  · rintro _ ⟨j, -, rfl⟩
    rw [← (vec M _ h).apply_symm_apply (frVec Y P rfl σ j)]
    exact (vec_mem_eigLie M _ h σ _).2 ((heig _ _ (hv j)).1 (P.eig σ j))
  · obtain ⟨cv, rfl⟩ := (vec M _ h).surjective v
    obtain ⟨w, hw⟩ := (hex cv).exists
    obtain ⟨a, ha⟩ := (P.basis σ w (htan cv w hw) ((heig cv w hw).2 ((vec_mem_eigLie M _ h σ _).1 hv'))).exists
    have h4 := (VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M S _ P.x Λ _ _ (P.u σ) a w hv).1 ha
    refine mem_initSpan.2 ⟨a, fun j hj => absurd j.2 (not_lt.2 hj), ?_⟩
    rw [← (hco w (htan cv w hw)).unique h4 hw, map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]

def ofFrames (hm : ∀ σ, Dw.mult σ ≤ 1) (F : Frames Y (𝟙 Y.X)) (hF : F.TopEigen) : FlagModel Y where
  YY := Y.X
  π := 𝟙 _
  proper := inferInstance
  normal := Y.normal
  flat := by rw [Category.id_comp]; exact Y.flat
  F := F
  dense := by
    have : IsIso (genMap (Y := Y) (𝟙 Y.X)) :=
      ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [Category.id_comp, pullback.condition]),
        by apply pullback.hom_ext <;> simp only [genMap, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          Category.comp_id, Category.id_comp],
        by apply pullback.hom_ext <;> simp only [genMap, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          Category.comp_id, Category.id_comp]⟩
    exact Y.jQ_dense.preimage (genMap (Y := Y) (𝟙 Y.X)).homeomorph.isOpenMap
  top := hF
  rep S _ _ P := by
    refine ⟨frX P ≫ Y.j, ⟨Category.comp_id _, fun S' _ _ ψ P' hP k z' ez hz hx σ i => ?_⟩,
      fun z hz => (Category.comp_id _).symm.trans hz.1⟩
    refine initSpan_low (hm σ) ?_ i
    rw [hF S' _ (frX_snd P') z' hx k hz σ]
    exact initSpan_frVec_top P' _ (F.inM hz hx) σ
  fin K _ _ z := (Set.finite_singleton z).subset fun z' ⟨hx, _⟩ => by simpa using hx

end Red

section Frames

variable {O : Type} [CommRing O] {β : O →+* c.F}

structure Proj (β : O →+* c.F) where
  m : (E →+* ℂ) → ℕ
  a : ∀ σ, Fin (m σ) → 𝓞 E
  κ : ∀ σ, Fin (m σ) → O
  spec : ∀ σ (R : Type) [CommRing R] [Algebra c.F R] (n : ℕ) (ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) R),
    (∀ b : 𝓞 E, ρ b * (∑ k, algebraMap c.F R (β (κ σ k)) • ρ (a σ k)) =
      algebraMap c.F R (embK c σ b) • ∑ k, algebraMap c.F R (β (κ σ k)) • ρ (a σ k)) ∧
    ∀ x : Fin n → R, (∀ b : 𝓞 E, (ρ b).mulVec x = algebraMap c.F R (embK c σ b) • x) →
      (∑ k, algebraMap c.F R (β (κ σ k)) • ρ (a σ k)).mulVec x = x

theorem nonempty_proj_id : Nonempty (Proj (RingHom.id c.F)) := by
  have hemb : Function.Injective (embF (E := E) c) := fun τ τ' h =>
    RingHom.ext fun a => congrArg Subtype.val (RingHom.congr_fun h a)
  choose m a κ h using GlobalTheory.exists_eigen_projector_ringOfIntegers E c.F (embF c) hemb
  exact ⟨⟨m, a, κ, h⟩⟩

theorem nonempty_proj_of_mem (p : Proj (RingHom.id c.F)) (h : ∀ σ k, p.κ σ k ∈ β.range) : Nonempty (Proj β) := by
  choose κ hκ using h
  exact ⟨⟨p.m, p.a, κ, fun σ => by simp only [hκ]; exact p.spec σ⟩⟩

variable {Y : Model Xo c β} {S : Type} [CommRing S]

def str (x : Sp S ⟶ Y.X) : O →+* S := (ev (x ≫ Y.s) ⊤ le_top).comp (toΓ O)

theorem str_eq {x : Sp S ⟶ Y.X} {g : O →+* S} (h : x ≫ Y.s = spMap g) : str x = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((spMap_ev_top _).trans h))

theorem ev_str (M : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (o : O) :
    ev x M.U h (str (tau M.hU) o) = str x o := by
  have : str x = (ev x M.U h).comp (str (tau M.hU)) := str_eq (by
    rw [← spMap_comp', str, spMap_ev_top, ← Category.assoc]
    exact congrArg (· ≫ Y.s) (spMap_ev x M.hU h).symm)
  rw [this]; rfl

theorem str_gen [Algebra c.F S] {y : Sp S ⟶ Xo.XF c} (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (o : O) :
    str (y ≫ Y.j) o = algebraMap c.F S (β o) := by
  rw [str_eq (g := (algebraMap c.F S).comp β) (by
    rw [Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
      ← Category.assoc, hy, spMap_comp'])]
  rfl

variable (p : Proj β)

def pm (M : MChart Y) (σ : E →+* ℂ) : Matrix (Fin M.n) (Fin M.n) Γ(Y.X, M.U) :=
  ∑ k, str (tau M.hU) (p.κ σ k) • M.ρ (p.a σ k)

theorem pm_map (M : MChart Y) (σ : E →+* ℂ) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) :
    (pm p M σ).map (ev x M.U h) = ∑ k, str x (p.κ σ k) • (M.ρ (p.a σ k)).map (ev x M.U h) := by
  ext i j
  simp only [pm, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, ev_str]

theorem vec_pm (M : MChart Y) (σ : E →+* ℂ) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (cv : Fin M.n → S) :
    vec M x h (((pm p M σ).map (ev x M.U h)).mulVec cv) =
      ∑ k, str x (p.κ σ k) • actR Y.t.act (p.a σ k) (vec M x h cv) := by
  rw [pm_map, Matrix.sum_mulVec, map_sum]
  simp only [Matrix.smul_mulVec, map_smul, actR_vec]

theorem pm_gen [Algebra c.F S] (M : MChart Y) (σ : E →+* ℂ) {y : Sp S ⟶ Xo.XF c}
    (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (h : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ M.U) :
    (∀ cv, M.Eig (ev _ M.U h) σ cv ↔ ((pm p M σ).map (ev _ M.U h)).mulVec cv = cv) ∧
      (pm p M σ).map (ev _ M.U h) * (pm p M σ).map (ev _ M.U h) = (pm p M σ).map (ev _ M.U h) := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.Reg.MChart.exists_ringHom_rho E H Dw l Xo c O _ Y M
  obtain ⟨h1, h2⟩ := p.spec σ S M.n ((ev _ M.U h).mapMatrix.comp ρ)
  simp only [RingHom.comp_apply, RingHom.mapMatrix_apply, hρ, ← str_gen (Y := Y) hy, ← pm_map] at h1 h2
  refine ⟨fun cv => ⟨h2 cv, fun hx b => ?_⟩, ?_⟩
  · have := congrArg (fun A => Matrix.mulVec A cv) (h1 b)
    simpa only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, hx] using this
  · ext i j
    have := h2 (fun k => (pm p M σ).map (ev _ M.U h) k j) (fun b => by
      funext k
      exact congrFun (congrFun (h1 b) k) j)
    exact congrFun this i

def GenIn (Y : Model Xo c β) : Prop :=
  ∀ M : MChart Y, ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L) (y : Sp L ⟶ Xo.XF c)
    (h : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ M.U), y ≫ pullback.snd _ _ = spMap (algebraMap c.F L) ∧
      Function.Injective (ev (y ≫ Y.j) M.U h)

theorem pm_low (hm : ∀ σ, Dw.mult σ ≤ 1) (hg : GenIn Y) (M : MChart Y) (σ : E →+* ℂ) :
    pm p M σ * pm p M σ = pm p M σ ∧
    (∑ ix : Fin (Dw.mult σ) → Fin M.n, ∏ i, pm p M σ (ix i) (ix i) = 1) ∧
      ∀ ix : Fin (Dw.mult σ) → Fin M.n, (∏ i, pm p M σ (ix i) (ix i)) • pm p M σ =
        (pm p M σ).submatrix id ix * (pm p M σ).submatrix ix id := by
  obtain ⟨L, _, _, y, h, hy, hi⟩ := hg M
  obtain ⟨h1, h2⟩ := pm_gen p M σ hy h
  have he : pm p M σ * pm p M σ = pm p M σ := Matrix.map_injective hi (Matrix.map_mul.trans h2)
  obtain ⟨Λ⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M L (ev _ M.U h) y hy (spMap_ev _ M.hU h).symm
  let N : Submodule L (Fin M.n → L) := Module.End.eigenspace ((pm p M σ).map (ev _ M.U h)).mulVecLin 1
  have hN : ∀ v, v ∈ N ↔ ((pm p M σ).map (ev _ M.U h)).mulVec v = v := fun v =>
    Module.End.mem_eigenspace_iff.trans (by rw [one_smul]; rfl)
  exact ⟨he, idem_low _ hi (hm σ) _ he N hN
    (finrank_chart_eig E H Dw l Xo c O β Y M L _ _ Λ σ N fun v => (hN v).trans (h1 v).symm)⟩

variable (Y) in

structure ECh where
  M : GChart Y
  V : Y.X.Opens
  le : V ≤ M.U
  u : ∀ σ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult σ)) Γ(Y.X, V)
  w : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin M.n) Γ(Y.X, V)
  wu : ∀ σ, w σ * u σ = 1
  uw : ∀ σ, u σ * w σ = (pm p M.toMChart σ).map (resG Y.X le)

theorem exists_eCh (hm : ∀ σ, Dw.mult σ ≤ 1) (hg : GenIn Y) (M : GChart Y) (x : Y.X) (hx : x ∈ M.U) :
    ∃ k : ECh Y p, x ∈ k.V := by
  classical
  have ex : ∀ σ, ∃ ix : Fin (Dw.mult σ) → Fin M.n,
      Y.X.evaluation M.U x hx (∏ i, pm p M.toMChart σ (ix i) (ix i)) ≠ 0 := fun σ => by
    by_contra h
    push Not at h
    have := congrArg (Y.X.evaluation M.U x hx) (pm_low p hm hg M.toMChart σ).2.1
    rw [map_sum, map_one, Finset.sum_eq_zero fun ix _ => h ix] at this
    exact zero_ne_one this
  choose ix hix using ex
  let d := fun σ => ∏ i, pm p M.toMChart σ (ix σ i) (ix σ i)
  let r := resG Y.X (Y.X.basicOpen_le (∏ σ, d σ))
  have hu : ∀ σ, IsUnit (r (d σ)) := fun σ =>
    isUnit_of_dvd_unit (map_dvd r (Finset.dvd_prod_of_mem d (Finset.mem_univ σ)))
      (RingedSpace.isUnit_res_basicOpen Y.X.toRingedSpace _)
  refine ⟨⟨M, Y.X.basicOpen (∏ σ, d σ), Y.X.basicOpen_le _,
    fun σ => ((pm p M.toMChart σ).submatrix id (ix σ)).map r,
    fun σ => (hu σ).unit⁻¹.val • ((pm p M.toMChart σ).submatrix (ix σ) id).map r, fun σ => ?_, fun σ => ?_⟩, ?_⟩
  · rw [Matrix.smul_mul, ← Matrix.map_mul, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      (pm_low p hm hg M.toMChart σ).1]
    have : Subsingleton (Fin (Dw.mult σ)) := Fin.subsingleton_iff_le_one.2 (hm σ)
    ext i j
    obtain rfl := Subsingleton.elim i j
    have hd : d σ = pm p M.toMChart σ (ix σ i) (ix σ i) := Fintype.prod_subsingleton _ i
    rw [Matrix.one_apply_eq, Matrix.smul_apply, Matrix.map_apply, Matrix.submatrix_apply, ← hd]
    exact (hu σ).val_inv_mul
  · rw [Matrix.mul_smul, ← Matrix.map_mul, ← (pm_low p hm hg M.toMChart σ).2.2]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    rw [← _root_.mul_assoc, (hu σ).val_inv_mul, _root_.one_mul]
  · refine (Y.X.evaluation_ne_zero_iff_mem_basicOpen x hx _).1 ?_
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun σ _ => hix σ

variable {p}

theorem ECh.fix_iff (k : ECh Y p) (σ : E →+* ℂ) (z : Sp S ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ k.V) (h : ⊤ ≤ z ⁻¹ᵁ k.M.U)
    (cv : Fin k.M.n → S) : ((pm p k.M.toMChart σ).map (ev z _ h)).mulVec cv = cv ↔
      ∃ a, ((k.u σ).map (ev z _ hz)).mulVec a = cv := by
  have e : (pm p k.M.toMChart σ).map (ev z _ h) = (k.u σ).map (ev z _ hz) * (k.w σ).map (ev z _ hz) := by
    rw [← Matrix.map_mul, k.uw]
    ext i j
    exact (ev_res z _ hz h _).symm
  rw [e, ← Matrix.mulVec_mulVec]
  refine ⟨fun h => ⟨_, h⟩, ?_⟩
  rintro ⟨a, rfl⟩
  rw [Matrix.mulVec_mulVec (M := (k.w σ).map _), ← Matrix.map_mul, k.wu, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.one_mulVec]

variable (p) in

def eigFrames (hm : ∀ σ, Dw.mult σ ≤ 1) (hc : ∀ x : Y.X, ∃ k : ECh Y p, x ∈ k.V) : Frames Y (𝟙 Y.X) where
  J := ECh Y p
  U k := k.V
  cover := eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (hc x)
  M k := k.M
  le k := k.le
  u k := k.u
  split k σ := ⟨k.w σ, k.wu σ⟩
  tri k k' σ := by
    have : Subsingleton (Fin (Dw.mult σ)) := Fin.subsingleton_iff_le_one.2 (hm σ)
    let Cm : Matrix (Fin k.M.n) (Fin k'.M.n) Γ(Y.X, k.V ⊓ k'.V) := (chg k.M.toMChart k'.M.toMChart).map
      (Scheme.Hom.appLE (𝟙 Y.X) (k.M.U ⊓ k'.M.U) (k.V ⊓ k'.V) (inf_le_inf k.le k'.le)).hom
    let Um : Matrix (Fin k'.M.n) (Fin (Dw.mult σ)) Γ(Y.X, k.V ⊓ k'.V) := (k'.u σ).map (resG Y.X inf_le_right)
    let Wm : Matrix (Fin (Dw.mult σ)) (Fin k.M.n) Γ(Y.X, k.V ⊓ k'.V) := (k.w σ).map (resG Y.X inf_le_left)
    let Vm : Matrix (Fin k.M.n) (Fin (Dw.mult σ)) Γ(Y.X, k.V ⊓ k'.V) := (k.u σ).map (resG Y.X inf_le_left)
    refine ⟨Wm * (Cm * Um), fun i j h => absurd (Subsingleton.elim _ _) h.ne, ?_⟩
    show Cm * Um = Vm * (Wm * (Cm * Um))
    have euw : Vm * Wm = ((pm p k.M.toMChart σ).map (resG Y.X k.le)).map (resG Y.X inf_le_left) := by
      rw [← k.uw]; exact Matrix.map_mul.symm
    rw [← Matrix.mul_assoc, euw]
    ext i j
    refine ext_ev fun S _ z hz => ?_
    have a := le_preimage_mono inf_le_left hz
    have b := le_preimage_mono inf_le_right hz
    have a' := le_preimage_mono k.le a
    have b' := le_preimage_mono k'.le b
    have ab := le_preimage_inf a' b'
    have h1 := (k'.fix_iff σ z b b' _).2 ⟨Pi.single j 1, rfl⟩
    have h2 := congrArg (vec k'.M.toMChart z b') h1
    rw [vec_pm, ← vec_chg k.M.toMChart k'.M.toMChart z a' b' ab, ← vec_pm] at h2
    have h3 := congrFun ((vec _ _ _).injective h2) i
    have e1 : ∀ s t, ev z _ hz ((Scheme.Hom.appLE (𝟙 Y.X) (k.M.U ⊓ k'.M.U) (k.V ⊓ k'.V)
        (inf_le_inf k.le k'.le)).hom (chg k.M.toMChart k'.M.toMChart s t)) =
        ev z _ ab (chg k.M.toMChart k'.M.toMChart s t) := fun s t =>
      (ev_appLE z (𝟙 Y.X) _ hz (by rw [Category.comp_id]; exact ab) _).trans
        (by rw [ev_congr (Category.comp_id z) _ _ ab])
    rw [Matrix.mulVec_single_one] at h3
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.col_apply] at h3
    simp only [Cm, Um, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, e1, ev_res z _ hz a, ev_res z _ hz b,
      ev_res z _ a a']
    exact h3.symm

theorem eigFrames_top (hm : ∀ σ, Dw.mult σ ≤ 1) (hc : ∀ x : Y.X, ∃ k : ECh Y p, x ∈ k.V) :
    (eigFrames p hm hc).TopEigen := by
  intro S _ _ y hy z hx k hz σ
  obtain rfl : z = y ≫ Y.j := (Category.comp_id _).symm.trans hx
  change ECh Y p at k
  have h : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ k.M.U := (eigFrames p hm hc).inM hz hx
  ext v
  obtain ⟨cv, rfl⟩ := (vec k.M.toMChart _ h).surjective v
  refine Iff.trans ?_ ((vec_mem_eigLie _ _ h σ cv).trans (((pm_gen p k.M.toMChart σ hy h).1 cv).trans
    (k.fix_iff σ _ hz h cv))).symm
  rw [mem_initSpan]
  exact ⟨fun ⟨a, _, e⟩ => ⟨a, (vec k.M.toMChart _ h).injective
      (((eigFrames p hm hc).sum_vecAt k _ hz hx σ a).symm.trans e)⟩,
    fun ⟨a, e⟩ => ⟨a, fun j hj => absurd j.2 (not_lt.2 hj),
      ((eigFrames p hm hc).sum_vecAt k _ hz hx σ a).trans (congrArg (vec k.M.toMChart _ h) e)⟩⟩

theorem exists_flagModel [IsNoetherianRing O] (p : Proj β) (hp : Dw.p ≤ 1) (hq : Dw.q ≤ 1) (hg : GenIn Y)
    (hP : PushInvertible Y.t.G Y.t.PP.L) : ∃ X : FlagModel Y, X.YY = Y.X := by
  have hm : ∀ σ, Dw.mult σ ≤ 1 := fun σ => by unfold Datum.mult; split_ifs <;> assumption
  have hc : ∀ x : Y.X, ∃ k : ECh Y p, x ∈ k.V := fun x =>
    (exists_gChart hP x).elim fun M hM => exists_eCh p hm hg M x hM
  exact ⟨ofFrames hm _ (eigFrames_top hm hc), rfl⟩

end Frames

section Gen

theorem exists_field (A : Type) [CommRing A] [IsDomain A] :
    ∃ (L : Type) (_ : Field L) (f : A →+* L), Function.Injective f :=
  ⟨FractionRing A, inferInstance, algebraMap _ _, IsFractionRing.injective _ _⟩

theorem genIn_of {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    (h : ∀ (M : MChart Y) (L : Type) [Field L] (f : Γ(Y.X, M.U) →+* L), Function.Injective f →
      ∃ (_ : Algebra c.F L) (y : Sp L ⟶ Xo.XF c),
      y ≫ pullback.snd _ _ = spMap (algebraMap c.F L) ∧ y ≫ Y.j = spMap f ≫ tau M.hU) :
    GenIn Y := fun M => by
  have := M.dom
  obtain ⟨L, _, f, hf⟩ := exists_field Γ(Y.X, M.U)
  obtain ⟨A, y, h1, h2⟩ := h M L f hf
  have hU : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ M.U := h2 ▸ le_preimage_comp _ (tau_le M.hU le_rfl)
  refine ⟨L, inferInstance, A, y, hU, h1, ?_⟩
  rw [ev_congr h2 _ _ (h2 ▸ hU), ev_spMap_tau]
  exact hf

theorem genIn_dvr {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F]
    [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)) : GenIn Y := genIn_of fun M L _ f hi => by
  obtain ⟨α, es, -, -, hinj, ⟨e, he⟩, hes, hop, -⟩ := GlobalTheory.Reg.ChartOpens.moduli_basicOpens E H Dw l Xo c O Y M
  have hi' : Function.Injective (f.comp α) := hi.comp hinj
  let A : Algebra c.F L := (IsFractionRing.lift hi').toAlgebra
  obtain ⟨y, h1, h2⟩ := (hop e he L f (RingHom.ext fun o => (IsFractionRing.lift_algebraMap hi' o).symm)
    (IsUnit.mk0 _ ((map_ne_zero_iff _ hi).2 (hes e he)))).1
  exact ⟨A, y, h1, h2⟩

theorem spec_generic {A L : Type} [CommRing A] [Field L] (f : A →+* L) (hf : Function.Injective f)
    (q : PrimeSpectrum L) (t : PrimeSpectrum A) : PrimeSpectrum.comap f q ⤳ t := by
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  obtain rfl : q = ⊥ := Subsingleton.elim _ _
  show Ideal.comap f ⊥ ≤ _
  rw [Ideal.comap_bot_of_injective _ hf]
  exact bot_le

theorem genIn_id (Y : Model Xo c (RingHom.id c.F)) : GenIn Y := genIn_of fun M L _ f hi => by
  have := M.dom
  have := Y.jQ_open
  have : IsIso (spMap (RingHom.id c.F)) := by
    rw [show spMap (RingHom.id c.F) = 𝟙 _ from Spec.map_id _]; infer_instance
  have : IsOpenImmersion Y.j := by unfold Model.j; infer_instance
  have hd : Dense (Set.range Y.j) := by
    have := (pullback.fst Y.s (spMap (RingHom.id c.F))).homeomorph.surjective.denseRange.comp Y.jQ_dense
      (pullback.fst Y.s (spMap (RingHom.id c.F))).homeomorph.continuous
    refine this.mono ?_
    rintro _ ⟨t, rfl⟩
    exact ⟨t, Scheme.Hom.comp_apply _ _ _⟩
  let z : Sp L ⟶ Y.X := spMap f ≫ tau M.hU
  have hr : Set.range z ⊆ Set.range Y.j := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hd.inter_open_nonempty (Set.range (tau M.hU))
      M.hU.fromSpec.isOpenEmbedding.isOpen_range ⟨_, (⊥ : PrimeSpectrum Γ(Y.X, M.U)), rfl⟩
    have hs : spMap f q ⤳ t := spec_generic f hi q t
    rw [Scheme.Hom.comp_apply]
    exact (hs.map (tau M.hU).continuous).mem_open Y.j.isOpenEmbedding.isOpen_range ht
  let A : Algebra c.F L := (str z).toAlgebra
  refine ⟨A, IsOpenImmersion.lift Y.j z hr, ?_, IsOpenImmersion.lift_fac _ _ _⟩
  have e : Y.j ≫ Y.s = pullback.snd _ _ := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over,
      show spMap (RingHom.id c.F) = 𝟙 _ from Spec.map_id _, Category.comp_id]
  rw [← e, ← Category.assoc, IsOpenImmersion.lift_fac]
  exact (spMap_ev_top _).symm

theorem exists_flagModel_field (Y : Model Xo c (RingHom.id c.F)) (hp : Dw.p ≤ 1) (hq : Dw.q ≤ 1)
    (hP : PushInvertible Y.t.G Y.t.PP.L) : ∃ X : FlagModel Y, X.YY = Y.X :=
  nonempty_proj_id.elim fun p => exists_flagModel p hp hq (genIn_id Y) hP

theorem exists_flagModel_dvr {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F]
    [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)) (p : Proj (RingHom.id c.F))
    (hint : ∀ σ k, p.κ σ k ∈ (algebraMap O c.F).range) (hp : Dw.p ≤ 1) (hq : Dw.q ≤ 1)
    (hP : PushInvertible Y.t.G Y.t.PP.L) : ∃ X : FlagModel Y, X.YY = Y.X :=
  (nonempty_proj_of_mem p hint).elim fun p => exists_flagModel p hp hq (genIn_dvr Y) hP

theorem nonempty_of_frPt {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (X : FlagCover Y) {K : Type}
    [Field K] [Algebra c.F K] (P : FrPt Xo c K) : Nonempty X.YY := ⟨X.ptY P (⊥ : PrimeSpectrum K)⟩

end Gen

end GlobalTheory.FlagMod.LowRank
