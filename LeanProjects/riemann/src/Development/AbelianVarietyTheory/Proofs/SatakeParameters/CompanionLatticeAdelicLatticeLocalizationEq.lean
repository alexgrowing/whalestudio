import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicLatticeCompletionLocalGlobal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeBidual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanLatAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem dualL_fg {n : ℕ} (τ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det)
    (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsLattice E M) : (dualL τ J M).FG := by
  classical
  obtain ⟨S, hS⟩ := hM.fg
  have hSE : Submodule.span E ((S : Set (Fin n → E))) = ⊤ := by
    rw [← Submodule.span_span_of_tower (𝓞 E) E, hS]
    exact hM.span_eq_top
  let Θ : (Fin n → E) →ₗ[𝓞 E] (S → E) :=
    { toFun := fun y s => hform τ J s.1 y
      map_add' := fun y y' => by
        funext s
        simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r y => by
        funext s
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [show r • y = (r : E) • y from (algebraMap_smul E r y).symm, GlobalTheory.LevelHecke.DualConj.hform_smul_right,
          Algebra.smul_def] }
  have hΘ : Function.Injective Θ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∀ x ∈ Submodule.span E (S : Set (Fin n → E)), hform τ J x y = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact congrFun hy ⟨x, hx⟩
      | zero => simp [hform]
      | add x x' _ _ hx hx' =>
        have e : hform τ J (x + x') y = hform τ J x y + hform τ J x' y := by
          simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
        rw [e, hx, hx', add_zero]
      | smul c x _ hx => rw [GlobalTheory.LevelHecke.DualConj.hform_smul_left, hx, mul_zero]
    have hJy : J *ᵥ y = 0 := by
      funext i
      have := h0 (Pi.single i 1) (by rw [hSE]; trivial)
      show (J *ᵥ y) i = 0
      rw [← this]
      simp [hform, Pi.single_apply, Matrix.mulVec, dotProduct]
    have : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
    rw [this, hJy, Matrix.mulVec_zero]
  let P : Submodule (𝓞 E) (S → E) := LinearMap.range
    (LinearMap.pi fun s : S => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj s) : (S → 𝓞 E) →ₗ[𝓞 E] (S → E))
  have hP : P.FG := by
    show (LinearMap.range _).FG
    rw [← Submodule.map_top]
    exact Module.Finite.fg_top.map _
  haveI := isNoetherian_of_fg_of_noetherian _ hP
  refine Submodule.fg_of_fg_map_injective Θ hΘ (Submodule.FG.of_le_of_isNoetherian (T := P) ?_)
  rintro _ ⟨y, hy, rfl⟩
  have hy' := (GlobalTheory.LevelHecke.DualConj.mem_dualL τ J M y).1 hy
  choose f hf using fun s : S => hy' s.1 (hS ▸ Submodule.subset_span s.2)
  refine ⟨f, ?_⟩
  funext s
  exact hf s

end GlobalTheory.CompanLatAd

namespace GlobalTheory.CompanLatAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_latS_sup_smul_iff (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (M N : Submodule (𝓞 E) (Fin n → E)) (a : 𝓞 E)
    (z : Fin n → E ⊗[F] v.adicCompletion F) :
    z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (M ⊔ Ideal.span {a} • N) ↔
      ∃ m ∈ latS (F := F) (v.adicCompletion F) (intV E v) M, ∃ w ∈ latS (F := F) (v.adicCompletion F) (intV E v) N,
        z = m + inclE (F := F) (v.adicCompletion F) (a : E) • w := by
  set c := inclE (F := F) (v.adicCompletion F) (a : E) with hc
  have hincl : ∀ y y' : Fin n → E, (fun i => inclE (F := F) (v.adicCompletion F) ((y + y') i)) =
      (fun i => inclE (F := F) (v.adicCompletion F) (y i)) + fun i => inclE (F := F) (v.adicCompletion F) (y' i) := by
    intro y y'; funext i; simp
  have hsm : ∀ y : Fin n → E, (fun i => inclE (F := F) (v.adicCompletion F) ((a • y) i)) =
      c • fun i => inclE (F := F) (v.adicCompletion F) (y i) := by
    intro y; funext i
    simp only [Pi.smul_apply, smul_eq_mul, hc, ← map_mul]
    rw [Algebra.smul_def]
  have hcw : ∀ w ∈ latS (F := F) (v.adicCompletion F) (intV E v) N,
      c • w ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Ideal.span {a} • N) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      rw [← hsm]
      exact Submodule.subset_span ⟨a • y, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hy, rfl⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add w w' _ _ hw hw' => rw [smul_add]; exact add_mem hw hw'
    | smul s w _ hw =>
      rw [Subring.smul_def, smul_comm]
      exact Submodule.smul_mem _ s hw
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hy
      rw [Submodule.ideal_span_singleton_smul] at hq
      obtain ⟨q', hq', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hq
      exact ⟨_, Submodule.subset_span ⟨p, hp, rfl⟩, _, Submodule.subset_span ⟨q', hq', rfl⟩, by
        show (fun i => inclE (F := F) (v.adicCompletion F) ((p + a • q') i)) = _
        rw [hincl, hsm]⟩
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add z z' _ _ hz hz' =>
      obtain ⟨m, hm, w, hw, rfl⟩ := hz
      obtain ⟨m', hm', w', hw', rfl⟩ := hz'
      exact ⟨m + m', add_mem hm hm', w + w', add_mem hw hw', by rw [smul_add]; abel⟩
    | smul s z _ hz =>
      obtain ⟨m, hm, w, hw, rfl⟩ := hz
      refine ⟨s • m, Submodule.smul_mem _ s hm, s • w, Submodule.smul_mem _ s hw, ?_⟩
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      ring
  · rintro ⟨m, hm, w, hw, rfl⟩
    have h1 : (M : Set (Fin n → E)) ⊆ ((M ⊔ Ideal.span {a} • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) :=
      SetLike.coe_subset_coe.2 le_sup_left
    have h2 : ((Ideal.span {a} • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ⊆
        ((M ⊔ Ideal.span {a} • N : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) :=
      SetLike.coe_subset_coe.2 le_sup_right
    exact add_mem (Submodule.span_mono (Set.image_mono h1) hm) (Submodule.span_mono (Set.image_mono h2) (hcw w hw))

end GlobalTheory.CompanLatAd

namespace GlobalTheory.CompanLatAd

theorem isLattice_compan {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (a : 𝓞 E)
    (M : Submodule (𝓞 E) (Fin N → E)) (hM : Submodule.IsLattice E M) :
    Submodule.IsLattice E (compan (sp := sp) J a M) := by
  refine ⟨?_, ?_⟩
  · exact hM.fg.sup ((Submodule.FG.smul (IsNoetherian.noetherian (Ideal.span {a})) (dualL_fg (sp.cm.sig : E →+* E) J hJ M hM)))
  · rw [eq_top_iff, ← hM.span_eq_top]
    exact Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left)

theorem compan_latAd_eq {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (σ : E →ₐ[F] E) (hσ : (σ : E →+* E) = sp.cm.sig) (J : Matrix (Fin N) (Fin N) E)
    (hJ : IsUnit J.det) (a : 𝓞 E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hx : x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) (hfg : Lb.FG)
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) :
    compan (sp := sp) J a (latAd x Lb) = latAd x (compan (sp := sp) J a Lb) := by
  have hcomp : ∀ M : Submodule (𝓞 E) (Fin N → E),
      compan (sp := sp) J a M = M ⊔ Ideal.span {a} • dualL (σ : E →+* E) J M := by
    intro M
    unfold compan dualL
    rw [hσ]
  have hLb : Submodule.IsLattice E Lb := ⟨hfg, hspan⟩
  have hfin : Module.Finite (𝓞 E) Lb := Module.Finite.iff_fg.mpr hfg
  have hlatAd : ∀ M : Submodule (𝓞 E) (Fin N → E), Submodule.IsLattice E M → Submodule.IsLattice E (latAd x M) := by
    intro M hM
    have e : latAd x M = Formalism.UG.CS.globLat x M := Submodule.span_eq (Formalism.UG.CS.globLat x M)
    rw [e]
    exact Formalism.UG.P.csGlob_lattice M (Module.Finite.iff_fg.mpr hM.fg) hM.span_eq_top x
  have hΛ := hlatAd Lb hLb
  have hcL := isLattice_compan sp J hJ a Lb hLb
  have hcΛ := isLattice_compan sp J hJ a (latAd x Lb) hΛ
  have hRHS := hlatAd _ hcL
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fin N → E ⊗[F] v.adicCompletion F),
      z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (compan (sp := sp) J a (latAd x Lb)) ↔
        z ∈ latS (F := F) (v.adicCompletion F) (intV E v) (latAd x (compan (sp := sp) J a Lb)) := by
    intro v z
    set g := bc (prV (E := E) v) x with hg
    have hgU : g ∈ UPts σ J (v.adicCompletion F) := GlobalTheory.MemDual.bc_prV_mem_UPts σ J v hx
    have hcar1 := GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v
    have hcar2 := GlobalTheory.LocCarry.mem_latS_latAd_iff x (compan (sp := sp) J a Lb)
      (Module.Finite.iff_fg.mpr hcL.fg) hcL.span_eq_top v
    have hdm := GlobalTheory.DualCompletion.dual_move F E σ N J v (latAd x Lb) Lb g hJ hΛ hLb hgU hcar1
    have hgg : ∀ w : Fin N → E ⊗[F] v.adicCompletion F, ((g⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ
        ((g : Matrix (Fin N) (Fin N) _) *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hgg' : ∀ w : Fin N → E ⊗[F] v.adicCompletion F, (g : Matrix (Fin N) (Fin N) _) *ᵥ
        (((g⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [hcar2, hcomp, hcomp, mem_latS_sup_smul_iff, mem_latS_sup_smul_iff]
    constructor
    · rintro ⟨m, hm, w, hw, rfl⟩
      exact ⟨_, (hcar1 m).1 hm, _, (hdm w).1 hw, by rw [Matrix.mulVec_add, Matrix.mulVec_smul]⟩
    · rintro ⟨m, hm, w, hw, he⟩
      refine ⟨(g : Matrix (Fin N) (Fin N) _) *ᵥ m, (hcar1 _).2 (by rw [hgg]; exact hm),
        (g : Matrix (Fin N) (Fin N) _) *ᵥ w, (hdm _).2 (by rw [hgg]; exact hw), ?_⟩
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← he, hgg']
  apply le_antisymm
  · intro w hw
    refine GlobalTheory.LatLocGlob.mem_of_forall_locLat (F := F) _ (Module.Finite.iff_fg.mpr hRHS.fg) hRHS.span_eq_top w fun v => ?_
    exact (key v _).1 (Submodule.subset_span ⟨w, hw, rfl⟩)
  · intro w hw
    refine GlobalTheory.LatLocGlob.mem_of_forall_locLat (F := F) _ (Module.Finite.iff_fg.mpr hcΛ.fg) hcΛ.span_eq_top w fun v => ?_
    exact (key v _).2 (Submodule.subset_span ⟨w, hw, rfl⟩)

theorem locP_companion_latAd : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (σ : E →ₐ[F] E), (σ : E →+* E) = sp.cm.sig → ∀ (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (a : 𝓞 E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) → ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (P : HeightOneSpectrum (𝓞 E)), Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (compan (sp := sp) J a (latAd x Lb)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd x (compan (sp := sp) J a Lb)) := by
  intro R F E _ _ _ _ _ _ sp N σ hσ J hJ a x hx Lb hfg hspan P
  rw [compan_latAd_eq sp σ hσ J hJ a x hx Lb hfg hspan]

end GlobalTheory.CompanLatAd
