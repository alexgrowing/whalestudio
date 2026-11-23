import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.Top.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word}

theorem unit_transfer {A B m n : Type} [CommRing A] [CommRing B] [Fintype m] [Fintype n] (e : m ≃ n) (s : A →+* B) (σ : A →+* A)
    (τ : B →+* B) (hs : ∀ x, s (σ x) = τ (s x)) (J : Matrix n n A) (J' : Matrix m m B) (hJ : ∀ a b, J' a b = s (J (e a) (e b)))
    (y : Matrix n n A) (g : Matrix m m B) (hg : ∀ a b, g a b = s (y (e a) (e b))) (hy : Formalism.UG.cT σ y * J * y = J) :
    Formalism.UG.cT τ g * J' * g = J' := by
  ext i j
  have := congrArg s (congrFun (congrFun hy (e i)) (e j))
  rw [hJ, ← this]
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hg, hJ, hs]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← e.sum_comp]

theorem swap_inj : Function.Injective (Lev.swapAE D) :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective

theorem hasMat_mat {h : GA D D.sp.X'} {y y'} (h1 : HasMat h y) (h2 : HasMat h y') : y = y' := by
  apply Units.ext
  ext i j
  have a := h1.2 ((finCongr (rankP D)).symm i) ((finCongr (rankP D)).symm j)
  have b := h2.2 ((finCongr (rankP D)).symm i) ((finCongr (rankP D)).symm j)
  simp only [Equiv.apply_symm_apply] at a b
  rw [← a, ← b]

theorem hasMat_pt {h h' : GA D D.sp.X'} {y} (h1 : HasMat h y) (h2 : HasMat h' y) : h = h' := by
  refine GlobalTheory.UnitarySplit.ga_ext _ ?_ ?_
  · have a : infHom D.sp.X' h = 1 := h1.1
    have b : infHom D.sp.X' h' = 1 := h2.1
    rw [a, b]
  · apply Units.ext
    ext i j
    apply swap_inj
    exact (h1.2 i j).trans (h2.2 i j).symm

set_option maxHeartbeats 1000000 in

theorem hasMat_exists (y : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ h : GA D D.sp.X', HasMat h y.1 := by
  let e := finCongr (rankP D)
  let s := (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm
  let r := (Matrix.reindexAlgEquiv D.host.F (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) e.symm)
  let g := Formalism.UG.bc s.toRingEquiv.toRingHom (Units.map r.toRingEquiv.toRingHom.toMonoidHom y.1)
  have hg : ∀ i j, g.1 i j = s (y.1.1 (e i) (e j)) := fun i j => rfl
  have hm : g ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig D.sp.X'.gram := by
    have hs : ∀ x, s (Formalism.UG.sigR (sigD D) _ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig (s x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    have hy : Formalism.UG.cT (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) y.1.1 *
        (gramP D).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * y.1.1 =
        (gramP D).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := y.2
    have hJ : ∀ a b, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.X'.gram a b =
        s.toRingEquiv.toRingHom (((gramP D).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) (e a) (e b)) :=
      fun a b => rfl
    have key := unit_transfer e s.toRingEquiv.toRingHom (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) hs _ _ hJ y.1.1 g.1 hg hy
    exact key
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue D.sp.X' 1 g (one_mem _) hm
  refine ⟨k, k1, fun i j => ?_⟩
  rw [k2]
  exact s.symm_apply_apply _

theorem hasMat_one : HasMat (1 : GA D D.sp.X') 1 := by
  refine ⟨one_mem _, fun i j => ?_⟩
  rw [map_one, map_one]
  simp [Matrix.one_apply, Fin.ext_iff]

open Classical in

theorem topLev_exists (K : ClsPTied u) : ∃ J χ, TopLev K J χ ∧ 1 ∈ J ∧ χ 1 = 1 ∧ ∀ κ : K.lev.U, ∃ h ∈ J, HasMat h κ.1 := by
  let χ : GA D D.sp.X' → ℂ := fun h => if hh : ∃ κ : K.lev.U, HasMat h κ.1 then star ((K.lev.chi hh.choose : ℂˣ) : ℂ) else 0
  have hχ : ∀ h (κ : K.lev.U), HasMat h κ.1 → χ h = star ((K.lev.chi κ : ℂˣ) : ℂ) := by
    intro h κ hk
    have hh : ∃ κ : K.lev.U, HasMat h κ.1 := ⟨κ, hk⟩
    simp only [χ, dif_pos hh]
    rw [show hh.choose = κ from Subtype.ext (hasMat_mat hh.choose_spec hk)]
  refine ⟨{h | ∃ κ : K.lev.U, HasMat h κ.1}, χ, ⟨fun _ => Iff.rfl, hχ⟩, ⟨1, hasMat_one⟩, ?_, fun κ => ?_⟩
  · rw [hχ 1 1 hasMat_one]; simp
  · obtain ⟨h, hh⟩ := hasMat_exists ⟨κ.1, ((K.lev.U_eq _).1 κ.2).1⟩
    exact ⟨h, ⟨κ, hh⟩, hh⟩

theorem isJ_smul {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S} {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} (h : IsJ u M j) {a : ℂ} (ha : a ≠ 0) :
    IsJ u M (a • j) := by
  refine ⟨fun x y hxy => h.inj (smul_right_injective _ ha hxy), ?_, fun τ g hg v w hw y y' hy => ?_⟩
  · rw [LinearMap.range_smul _ _ ha, h.range]
  · simp only [LinearMap.smul_apply, Pi.smul_apply]
    rw [h.eqv τ g hg v w hw y y' hy]

theorem multT_bot {V : HSp D} {S : D.what₂.Tau → SPar} (θ) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (hχ : ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∃ k ∈ U, k ∈ GfC V ∧ k ∈ J ∧ χ k ≠ 1) :
    MultT θ M J χ = ⊥ := by
  have : Mult θ M J χ = ⊥ := by
    unfold Mult
    rw [Submodule.span_eq_bot]
    intro T hT
    ext v g
    obtain ⟨U, hU, hl⟩ := (hT.aut v).level
    obtain ⟨k, k1, k2, k3, k4⟩ := hχ U hU
    have e1 := hl k k1 k2 g
    rw [hT.lev v k k3 g] at e1
    have : (χ k - 1) * T v g = 0 := by rw [sub_mul, e1]; ring
    simpa [sub_eq_zero, k4] using this
  unfold MultT
  rw [this, Submodule.map_bot]

theorem period_zero {K : ClsPTied u} (V : ValPTied u K) {S : D.what₂.Tau → SPar} (θ) (M : DSModel D.sp.X' S)
    (j : SmT M →ₗ[ℂ] (FrP D → ℂ)) (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ)
    (hχ : ∀ U : Subgroup (GA D D.sp.X'), IsOpen (U : Set (GA D D.sp.X')) → ∃ k ∈ U, k ∈ GfC D.sp.X' ∧ k ∈ J ∧ χ k ≠ 1)
    (eT : (D.mem u).P.Mt → MultT θ M J χ) (hf : TopFormula V M j fun F => (eT F).1) (F c v) :
    (D.mem u).P.period (V.eW.symm (by classical exact Pi.single c (j v))) F = 0 := by
  obtain ⟨h, hh⟩ := hasMat_exists (K.y c)
  have e := hf F c v h hh
  have z : (eT F).1 = 0 := by
    exact (Submodule.eq_bot_iff _).1 (multT_bot θ M J χ hχ) _ (eT F).2
  simp only [z, LinearMap.zero_apply, Pi.zero_apply] at e
  have hc : (Nat.card ((D.fm u).stabilizer₂ c) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := (D.fm u).stabilizer₂ c)).ne'
  exact (mul_eq_zero.1 e.symm).resolve_left hc

theorem valC_ne_bot {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) : ValC G lam ≠ ⊥ := by
  intro h
  have hm : fnOf G (shiftOf lam) 1 (ten fun τ => extremal ℂ n (lam τ)) ∈ ValC G lam :=
    ⟨_, Submodule.subset_span ⟨_, fun τ => Submodule.subset_span ⟨[], rfl⟩, rfl⟩, rfl⟩
  rw [h, Submodule.mem_bot] at hm
  have := congrFun hm ⟨fun _ => 1, fun _ => by simp⟩
  simp [fnOf, ten, extremal, Formalism.GradedWeylDivisibility.hw, Formalism.GradedWeylDivisibility.lpMinor, MvPolynomial.eval_rename, RingHom.map_det] at this
  have e : ∀ (x : ι) (s : ℕ) (h1 h2 : s ≤ n), ((Matrix.of fun p q : Fin s => (MvPolynomial.X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin n × Fin n) ℂ)).map
      ⇑(MvPolynomial.eval ((fun x : ι × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) x.2.1 x.2.2) ∘ Prod.mk x))) = 1 := by
    intro x s h1 h2
    ext p q
    simp [Matrix.one_apply]
  simp only [e, Matrix.det_one, one_pow, Finset.prod_const_one] at this
  exact one_ne_zero this

theorem not_isJ_zero {S : D.what₂.Tau → SPar} (M : DSModel D.sp.X' S) : ¬ IsJ u M 0 := fun h =>
  valC_ne_bot _ _ (h.range.symm.trans LinearMap.range_zero)

end GlobalTheory.Core.Rk.Top.Model

end
