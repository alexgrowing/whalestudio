import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder

noncomputable section

open NumberField IsDedekindDomain Topology Matrix
open GlobalTheory.CuspRep
open scoped ContDiff

namespace GlobalTheory.IsoPull

section Ring

variable {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] {a : ℕ}

theorem map_map_comm (p : R →+* S) (p' : R' →+* S') (c : R →+* R') (c' : S →+* S') (h : ∀ x, p' (c x) = c' (p x))
    (g : GL (Fin a) R) :
    GeneralLinearGroup.map p' (GeneralLinearGroup.map c g) =
      GeneralLinearGroup.map c' (GeneralLinearGroup.map p g) := by
  ext i j
  exact h _

theorem continuous_mapGL [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S]
    (c : R →+* S) (h : Continuous c) : Continuous (GeneralLinearGroup.map (n := Fin a) c) :=
  Continuous.units_map _ (continuous_matrix fun i j => h.comp (continuous_id.matrix_elem i j))

theorem map_unip {r : ℕ} (c : R →+* S) (x : BlockIx a r → R) :
    GeneralLinearGroup.map c (unip x) = unip fun p => c (x p) := by
  ext i j
  change c ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) =
    (1 + nilM fun p => c (x p) : Matrix (Fin a) (Fin a) S) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add]
  split_ifs <;> simp

end Ring

section Sat

open Formalism.UG GlobalTheory.LFun GlobalTheory.PRep

theorem Tj_map {F F' : Type} [Field F] [Field F'] {n : ℕ} (c : F ≃+* F') {O : Subring F} {O' : Subring F'}
    (hK : ∀ g, g ∈ GLint (Fin n) O ↔ Units.mapEquiv c.mapMatrix.toMulEquiv g ∈ GLint (Fin n) O') (ϖ : Fˣ) (j : ℕ)
    (g : GL (Fin n) F) : Tj ℂ n O' (c ϖ) j (Units.mapEquiv c.mapMatrix.toMulEquiv g) = Tj ℂ n O ϖ j g := by
  classical
  set G : GL (Fin n) F ≃* GL (Fin n) F' := Units.mapEquiv c.mapMatrix.toMulEquiv with hG
  have hGv : ∀ g i j, (G g).1 i j = c (g.1 i j) := fun _ _ _ => rfl
  have e : G (ConjPlace.dGL n ϖ j) = ConjPlace.dGL n (Units.map (c : F →* F') ϖ) j :=
    Units.ext (Matrix.ext fun a b => by
      rw [hGv]
      simp only [ConjPlace.dGL, diagJ, Matrix.diagonal_apply]
      split_ifs <;> simp)
  refine (ConjPlace.Tj_apply O' (Units.map (c : F →* F') ϖ) j _).trans ?_
  rw [ConjPlace.Tj_apply, ← e]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨a, ha, b, hb, H⟩
    obtain ⟨a, rfl⟩ := G.surjective a
    obtain ⟨b, rfl⟩ := G.surjective b
    rw [← map_mul, ← map_mul, G.apply_eq_iff_eq] at H
    exact ⟨a, (hK a).2 ha, b, (hK b).2 hb, H⟩
  · rintro ⟨a, ha, b, hb, H⟩
    exact ⟨_, (hK a).1 ha, _, (hK b).1 hb, by rw [H, map_mul, map_mul]⟩

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hasSatGL_of_ringEquiv (c : v.adicCompletion K ≃+* w.adicCompletion M) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (hq : qV M w = qV K v) {ρ : Representation ℂ (GL (Fin n) (v.adicCompletion K)) V}
    {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion M)) W} (T : V ≃ₗ[ℂ] W)
    (hT : ∀ g x, ρ' (GeneralLinearGroup.map c.toRingHom g) (T x) = T (ρ g x)) {B : Multiset ℂˣ}
    (h : HasSatGL v ρ B) : HasSatGL w ρ' B := by
  let G : GL (Fin n) (v.adicCompletion K) ≃* GL (Fin n) (w.adicCompletion M) := Units.mapEquiv c.mapMatrix.toMulEquiv
  have hG : ∀ g, G g = GeneralLinearGroup.map c.toRingHom g := fun g => Units.ext rfl
  have hGv : ∀ g i j, (G g).1 i j = c (g.1 i j) := fun _ _ _ => rfl
  have hO : ∀ x, c x ∈ Ov M w ↔ x ∈ Ov K v := fun x => by
    change Valued.v (c x) ≤ 1 ↔ Valued.v x ≤ 1
    rw [hc]
  have hK : ∀ g, g ∈ KGL v n ↔ G g ∈ KGL w n := fun g => by
    simp only [KGL, GlobalTheory.AdelicU.mem_GLint_iff, ← map_inv, hGv, hO]
  have hf : ∀ g y, T.toLinearMap ((ρ.comp G.symm.toMonoidHom) g y) = ρ' g (T.toLinearMap y) := fun g y => by
    change T (ρ (G.symm g) y) = ρ' g (T y)
    rw [← hT, ← hG, MulEquiv.apply_symm_apply]
  have hTj := Tj_map (n := n) c hK
  have key0 : ∀ x, IsSatVecGL v ρ x B → IsSatVecGL w (ρ.comp G.symm.toMonoidHom) x B := by
    rintro x ⟨h0, hx, hB, hH⟩
    refine ⟨h0, (mem_fixed_comp_symm _ hK).2 hx, hB, fun ϖ' hϖ' j hj => ?_⟩
    obtain ⟨p, rfl⟩ := c.surjective ϖ'
    have hp : IsUnifV K v p := (hc p).symm.trans hϖ'
    obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (v.adicCompletion K)ˣ, ϖ = p :=
      ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
    rw [heckeVec_comp_symm _ hK (Tj_mem_hecke hϖ' j).1 hx, hq, ← hH _ hp j hj]
    exact congrArg (fun t => heckeVec ρ _ t x) (funext (hTj ϖ j))
  have key : ∀ x, IsSatVecGL v ρ x B → IsSatVecGL w ρ' (T x) B := fun x hx =>
    (key0 x hx).map T.toLinearMap hf ((map_ne_zero_iff T T.injective).2 hx.1)
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)
    rwa [hG, hT] at this

end Sat

variable {K M : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M]
  {a : ℕ} (e : K ≃+* M)

def mapL : Lie K a →L[ℝ] Lie M a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => cInf e (X i j)
      map_add' := fun X Y => by funext i j; simp
      map_smul' := fun t X => by funext i j; exact cInf_smul e t _ }

def mapK (k : Kinf K a) : Kinf M a :=
  ⟨k.1.map (cInf e), Matrix.mem_unitaryGroup_iff.2 (by
    have h : star (k.1.map (cInf e)) = (star k.1).map (cInf e) := by
      ext i j : 1
      exact (cInf_star e _).symm
    rw [h, ← Matrix.map_mul, Matrix.mem_unitaryGroup_iff.1 k.2]
    exact Matrix.map_one _ (map_zero _) (map_one _))⟩

def mapOp : Op K a → Op M a
  | .fin k => .fin (GeneralLinearGroup.map (cFin e) k)
  | .cpt k => .cpt (mapK e k)
  | .lie X => .lie (mapL e X)

theorem mapOp_symm (o : Op K a) : mapOp e.symm (mapOp e o) = o := by
  cases o with
  | fin k => exact congrArg Op.fin (Units.ext (Matrix.ext fun i j => cFin_symm e _))
  | cpt k => exact congrArg Op.cpt (Subtype.ext (Matrix.ext fun i j => cInf_symm e _))
  | lie X => exact congrArg Op.lie (funext₂ fun i j => cInf_symm e _)

variable (a) in

def mapA : GA K a →* GA M a := GeneralLinearGroup.map (cAd e)

theorem mapA_symm (g : GA K a) : mapA a e.symm (mapA a e g) = g := by
  ext i j : 2
  exact cAd_symm e _

theorem mapA_infGL (y : GL (Fin a) (Cinf K)) :
    mapA a e (infGL K a y) = infGL M a (GeneralLinearGroup.map (cInf e) y) :=
  ga_ext (by rw [mapA, map_map_comm _ _ _ _ (pInf_cAd e), pInf_infGL, pInf_infGL])
    (by rw [mapA, map_map_comm _ _ _ _ (pFin_cAd e), pFin_infGL, pFin_infGL, map_one])

theorem mapA_finGL (k : GL (Fin a) (Af K)) : mapA a e (finGL K a k) = finGL M a (GeneralLinearGroup.map (cFin e) k) :=
  ga_ext (by rw [mapA, map_map_comm _ _ _ _ (pInf_cAd e), pInf_finGL, pInf_finGL, map_one])
    (by rw [mapA, map_map_comm _ _ _ _ (pFin_cAd e), pFin_finGL, pFin_finGL])

theorem mapA_ratGL (γ : GL (Fin a) K) :
    mapA a e (ratGL K a γ) = ratGL M a (GeneralLinearGroup.map e.toRingHom γ) :=
  Units.ext (Matrix.ext fun _ _ => cAd_algebraMap e _)

theorem chart_map (φ : GA M a → ℂ) (g : GA K a) {x : Lie K a} (hx : x ∈ invSet K a) :
    chart (fun g => φ (mapA a e g)) g x = chart φ (mapA a e g) (mapL e x) ∧ mapL e x ∈ invSet M a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [show mapL e (toL u.val) = toL (GeneralLinearGroup.map (cInf e) u).val from rfl,
    chart_val, chart_val, map_mul, mapA_infGL]
  exact ⟨rfl, val_mem_invSet _⟩

theorem map_mem_Sm {φ : GA M a → ℂ} (hφ : φ ∈ Sm M a) : (fun g => φ (mapA a e g)) ∈ Sm K a := fun g =>
  ((hφ (mapA a e g)).comp (mapL (a := a) e).contDiff.contDiffOn
    fun _ hx => (chart_map e φ g hx).2).congr fun _ hx => (chart_map e φ g hx).1

variable (a) in

def pull : Sm M a ≃ₗ[ℂ] Sm K a where
  toFun φ := ⟨fun g => φ.1 (mapA a e g), map_mem_Sm e φ.2⟩
  invFun φ := ⟨fun g => φ.1 (mapA a e.symm g), map_mem_Sm e.symm φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (mapA_symm e.symm g)
  right_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (mapA_symm e g)

theorem pull_apply (φ : Sm M a) (g : GA K a) : (pull a e φ).1 g = φ.1 (mapA a e g) := rfl

theorem rt_pull (h : GA K a) (φ : Sm M a) : rt K a h (pull a e φ) = pull a e (rt M a (mapA a e h) φ) :=
  Subtype.ext <| funext fun g => congrArg φ.1 (map_mul (mapA a e) g h)

theorem lie_pull (X : Lie K a) (φ : Sm M a) : lie K a X (pull a e φ) = pull a e (lie M a (mapL e X) φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have e1 : chart (pull a e φ).1 g =ᶠ[𝓝 (oneL K a)] chart φ.1 (mapA a e g) ∘ mapL e :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (chart_map e φ.1 g hx).1
  have h1 : mapL e (oneL K a) = oneL M a := by
    funext i j
    change cInf e ((1 : Matrix (Fin a) (Fin a) (Cinf K)) i j) = (1 : Matrix (Fin a) (Fin a) (Cinf M)) i j
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h2 := HasFDerivAt.comp (oneL K a) (f := mapL e)
    (by rw [h1]; exact (differentiableAt_chart φ.2 (mapA a e g)).hasFDerivAt) (mapL e).hasFDerivAt
  change fderiv ℝ _ _ X = fderiv ℝ _ _ _
  rw [e1.fderiv_eq, h2.fderiv]
  rfl

theorem act_pull (o : Op K a) (φ : Sm M a) : act o (pull a e φ) = pull a e (act (mapOp e o) φ) := by
  cases o with
  | fin k => exact (rt_pull e _ φ).trans (by rw [mapA_finGL]; rfl)
  | cpt k =>
    have e1 : GeneralLinearGroup.map (cInf e) (Unitary.toUnits k) = Unitary.toUnits (mapK e k) :=
      Units.ext rfl
    exact (rt_pull e (infGL K a (Unitary.toUnits k)) φ).trans (by rw [mapA_infGL, e1]; rfl)
  | lie X => exact lie_pull e X φ

theorem pull_act (o : Op M a) (φ : Sm M a) : pull a e (act o φ) = act (mapOp e.symm o) (pull a e φ) := by
  rw [act_pull]
  exact congrArg (fun o => pull a e (act o φ)) (mapOp_symm e.symm o).symm

theorem Eop_pull (τ : M →+* ℂ) (i j : Fin a) (φ : Sm M a) :
    Eop (τ.comp e.toRingHom) i j (pull a e φ) = pull a e (Eop τ i j φ) := by
  have h2 : ∀ z, lieS K a i j (atEmb (τ.comp e.toRingHom) z) (pull a e φ) =
      pull a e (lieS M a i j (atEmb τ z) φ) := fun z => by
    have e' : ∀ x, mapL e (toL (Matrix.single i j x)) = toL (Matrix.single i j (cInf e x)) := fun x => by
      funext k l
      change cInf e (Matrix.single i j x k l) = Matrix.single i j (cInf e x) k l
      rw [Matrix.single_apply, Matrix.single_apply]
      split_ifs <;> simp
    rw [lieS_apply, lie_pull, e', cInf_atEmb, lieS_apply]
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, h2, map_smul, map_sub]

theorem cap_pull (τ : M →+* ℂ) (u : ℂ) (φ : Sm M a) :
    cap (τ.comp e.toRingHom) u (pull a e φ) = pull a e (cap τ u φ) := by
  have h := map_qdet ((pull a e).conjAlgEquiv ℂ).toAlgHom (Eop τ) (u + ((a : ℂ) - 1) / 2)
  have e1 : (fun i j => ((pull a e).conjAlgEquiv ℂ).toAlgHom (Eop τ i j)) = Eop (τ.comp e.toRingHom) := by
    funext i j
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨ψ, rfl⟩ := (pull a e).surjective ψ
    rw [Eop_pull]
    change pull a e (Eop τ i j ((pull a e).symm (pull a e ψ))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [e1] at h
  rw [cap, ← h, cap]
  generalize Formalism.REAL.qdet (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2) = z
  change pull a e (z ((pull a e).symm (pull a e φ))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem cap_pull' (σ : K →+* ℂ) (u : ℂ) (φ : Sm M a) :
    cap σ u (pull a e φ) = pull a e (cap (σ.comp e.symm.toRingHom) u φ) := by
  rw [← cap_pull]
  congr 2
  ext x
  simp

theorem Zalg_pull {z : Module.End ℂ (Sm K a)} (hz : z ∈ Zalg K a) :
    ∃ z' ∈ Zalg M a, ∀ φ, z (pull a e φ) = pull a e (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨_, Algebra.subset_adjoin ⟨_, _, rfl⟩, cap_pull' e τ u⟩
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩

omit [IsTotallyComplex K] [IsTotallyComplex M] in

theorem height_map_le (y : GL (Fin a) (Cinf K)) : height (GeneralLinearGroup.map (cInf e) y) ≤ height y := by
  have h1 : ∀ y : GL (Fin a) (Cinf K), ‖toL (GeneralLinearGroup.map (cInf e) y).val‖ ≤ ‖toL y.val‖ := fun y =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j =>
      (norm_cInf_le e _).trans ((norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i))
  unfold height
  rw [← map_inv]
  linarith [h1 y, h1 y⁻¹]

theorem height_map (y : GL (Fin a) (Cinf K)) : height (GeneralLinearGroup.map (cInf e) y) = height y := by
  refine le_antisymm (height_map_le e y) (le_of_eq_of_le ?_ (height_map_le e.symm _))
  exact congrArg height (Units.ext (Matrix.ext fun i j => (cInf_symm e _).symm))

theorem isAutForm_pull {φ : Sm M a} (h : IsAutForm φ) : IsAutForm (pull a e φ) where
  left γ g := by rw [pull_apply, map_mul, mapA_ratGL, h.left, pull_apply]
  level := by
    convert h.level.preimage (continuous_mapGL (cFin e) (continuous_cFin e)) using 1
    ext k
    exact (Eq.congr_left (act_pull e (.fin k) φ)).trans (pull a e).injective.eq_iff
  kfin := by
    have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep M a k φ)).map
      (pull a e).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_pull e (.cpt k) φ).symm⟩
  zfin := by
    have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm M a) => z φ) ''
      Zalg M a)).map (pull a e).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := Zalg_pull e hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth (mapA a e g)
    refine ⟨C, N, fun y => ?_⟩
    rw [pull_apply, map_mul, mapA_infGL, ← height_map e]
    exact h1 _

theorem map_mem_ratN {r : ℕ} {x : BlockIx a r → Ad K} (hx : x ∈ ratN K a r) :
    (fun p => cAd e (x p)) ∈ ratN M a r := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨fun p => e (y p), funext fun p => (cAd_algebraMap e (y p)).symm⟩

open MeasureTheory in

theorem isCuspidal_pull {φ : GA M a → ℂ} (hφ : IsCuspidal φ) : IsCuspidal fun g => φ (mapA a e g) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  borelize (BlockIx a r → Ad M)
  let β : (BlockIx a r → Ad K) ≃ₜ+ (BlockIx a r → Ad M) :=
    { toFun := fun x p => cAd e (x p)
      invFun := fun x p => cAd e.symm (x p)
      left_inv := fun x => funext fun p => cAd_symm e _
      right_inv := fun x => funext fun p => cAd_symm e.symm _
      map_add' := fun x y => funext fun p => map_add (cAd e) _ _
      continuous_toFun := continuous_pi fun p => (continuous_cAd e).comp (continuous_apply p)
      continuous_invFun := continuous_pi fun p => (continuous_cAd e.symm).comp (continuous_apply p) }
  let q : ratN M a r ≃ ratN K a r :=
    { toFun := fun y => ⟨β.symm y, map_mem_ratN e.symm y.2⟩
      invFun := fun x => ⟨β x, map_mem_ratN e x.2⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hφ r h0 h1 (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving q fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add, β.apply_symm_apply]) (mapA a e g)
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  beta_reduce
  rw [map_mul, mapA, map_unip]
  rfl

def pullSub (π : CuspSub M a) : CuspSub K a where
  V := π.V.map (pull a e).toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact ⟨isAutForm_pull e (π.cusp φ hφ).1, isCuspidal_pull e (π.cusp φ hφ).2⟩
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable _ φ hφ, (act_pull e o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := pull a e)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap (pull a e).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (pull a e).injective h2]) fun o φ hφ => by
      change pull a e (act o φ) ∈ W
      rw [pull_act]
      exact hs _ _ hφ
    have e1 := Submodule.map_comap_eq_of_surjective (f := (pull a e).toLinearMap) (pull a e).surjective W
    exact h.imp (fun h => by rw [← e1, h, Submodule.map_bot]) fun h => by rw [← e1, h]

theorem hasInfChar_pullSub {π : CuspSub M a} {σ : K →+* ℂ} {m : Multiset ℂ}
    (h : π.HasInfChar (σ.comp e.symm.toRingHom) m) : (pullSub e π).HasInfChar σ m := by
  refine ⟨h.1, ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap σ u (pull a e φ) = _ • pull a e φ
  rw [cap_pull', h.2 u φ hφ, map_smul]

theorem hasSat_pullSub {π : CuspSub M a} {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (hw : Over e v w) {B : Multiset ℂˣ} (h : (CG.mk π).HasSat w B) : (CG.mk (pullSub e π)).HasSat v B := by
  rw [CG.hasSat_mk] at h ⊢
  refine hasSatGL_of_ringEquiv (locEquiv hw.symm) (valued_cLoc hw.symm) (qV_eq hw.symm)
    ((pull a e).submoduleMap π.V) (fun g x => Subtype.ext ?_) h
  refine Eq.trans ?_ (pull_act e (.fin (locGL M a w g)) x.1).symm
  change _ = act (.fin (GeneralLinearGroup.map (cFin e.symm) (locGL M a w g))) (pull a e x.1)
  rw [cFin_locGL hw.symm]
  rfl

theorem exists_transport : ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] (e : K ≃+* M) (a : ℕ) (π : CuspSub K a), ∃ π' : CuspSub M a, (∀ (τ : M →+* ℂ) (m : Multiset ℂ), π.HasInfChar (τ.comp e.toRingHom) m → π'.HasInfChar τ m) ∧ ∀ (v : HeightOneSpectrum (𝓞 K)) (B : Multiset ℂˣ), (CG.mk π).HasSat v B → (CG.mk π').HasSat (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) v) B :=
  fun _ _ _ _ _ _ _ _ e _ π => ⟨pullSub e.symm π, fun _ _ h => hasInfChar_pullSub e.symm h,
    fun _ _ h => hasSat_pullSub e.symm (fun _ => Iff.rfl) h⟩

end GlobalTheory.IsoPull

end
