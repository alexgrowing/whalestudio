import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDefiniteUnitaryDoubleCosets

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.UnitaryBC.ClassTransport
open scoped TensorProduct

namespace GlobalTheory.FormDict.Model

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation "F₀" => maximalRealSubfield L

def kappa : AL L ≃+* FiniteAdeleRing (𝓞 L) L :=
  (Algebra.TensorProduct.comm F₀ L (FiniteAdeleRing (𝓞 F₀) F₀)).toRingEquiv.trans (GlobalTheory.LFun.finAdEquiv F₀ L)

theorem kappa_tmul (x : L) (a : FiniteAdeleRing (𝓞 F₀) F₀) :
    kappa L (x ⊗ₜ a) = GlobalTheory.AdeleBaseChange.adMap F₀ L a * algebraMap L _ x :=
  GlobalTheory.LFun.toFinAd_tmul a x

theorem kappa_conj (y : AL L) :
    kappa L (conjAL L y) = conjFin (IsCMField.complexConj L).toRingEquiv (kappa L y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul x a =>
    change kappa L ((IsCMField.complexConj L x) ⊗ₜ a) = _
    rw [kappa_tmul, kappa_tmul, map_mul, conjFin_adMap, conjFin_algebraMap]
    rfl
  | add y z hy hz => rw [map_add, map_add, map_add, hy, hz, map_add]

def psi0 : GAf L n →* GL (Fin n) (FiniteAdeleRing (𝓞 L) L) :=
  (Matrix.GeneralLinearGroup.map (kappa L).toRingHom).comp (ReciprocityTheory.Aut.GA L n).subtype

theorem map_conjT (M : Matrix (Fin n) (Fin n) (AL L)) :
    (conjT (conjAL L) M).map (kappa L).toRingHom =
      Formalism.UG.cT (conjFin (IsCMField.complexConj L).toRingEquiv) (M.map (kappa L).toRingHom) :=
  Matrix.ext fun _ _ => kappa_conj L _

theorem unitaryFinitePointsToGLFiniteAdeles_isUnitary (x : GAf L n) :
    Formalism.UG.cT (conjFin (IsCMField.complexConj L).toRingEquiv) (psi0 L n x).val * (psi0 L n x).val = 1 := by
  have hx : x.1.val * conjT (conjAL L) x.1.val = 1 := x.2
  rw [mul_eq_one_comm] at hx
  change Formalism.UG.cT _ (x.1.val.map (kappa L).toRingHom) * x.1.val.map (kappa L).toRingHom = 1
  rw [← map_conjT, ← Matrix.map_mul, hx, Matrix.map_one _ (map_zero _) (map_one _)]

def j0 : GAf L n →* UA L n :=
  ((finGL L n).comp (psi0 L n)).codRestrict (UA L n) fun x => finGL_mem_UA _ (unitaryFinitePointsToGLFiniteAdeles_isUnitary L n x)

def finIso : FinIso L n where
  κ := kappa L
  left x := by rw [kappa_tmul, map_one, one_mul]
  right w v h := by
    have h' : w.under (𝓞 F₀) = v := HeightOneSpectrum.ext h
    subst h'
    refine ⟨GlobalTheory.LFun.complMap (rfl : w.under (𝓞 F₀) = _), GlobalTheory.LFun.InertChart.continuous_complMap _, fun a => ?_⟩
    rw [kappa_tmul, map_one, mul_one]
    rfl
  j := j0 L n
  fin x := MonoidHom.mem_ker.2 (pInf_finGL (psi0 L n x))
  loc x w s t := by
    have h : Matrix.GeneralLinearGroup.map (pFin L) (j0 L n x).1 = psi0 L n x := pFin_finGL _
    have h2 := congrArg (fun g : GL (Fin n) (Af L) => pLoc L w (g.val s t)) h
    exact h2
  onto g hgf := by
    have hg := g.2
    change Formalism.UG.cT (conjAd L) g.1.val * 1 * g.1.val = 1 at hg
    rw [Matrix.mul_one] at hg
    have hf : Formalism.UG.cT (conjFin (IsCMField.complexConj L).toRingEquiv)
        (Matrix.GeneralLinearGroup.map (pFin L) g.1).val * (Matrix.GeneralLinearGroup.map (pFin L) g.1).val = 1 := by
      have h := congrArg (fun M => M.map (pFin L)) hg
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
      exact h
    let u := Matrix.GeneralLinearGroup.map (kappa L).symm.toRingHom (Matrix.GeneralLinearGroup.map (pFin L) g.1)
    have hU : u.val.map (kappa L).toRingHom = (Matrix.GeneralLinearGroup.map (pFin L) g.1).val :=
      Matrix.ext fun i j => (kappa L).apply_symm_apply _
    have hmem : u ∈ ReciprocityTheory.Aut.GA L n := by
      change u.val * conjT (conjAL L) u.val = 1
      rw [mul_eq_one_comm]
      refine Matrix.map_injective (kappa L).injective ?_
      change Matrix.map _ (kappa L).toRingHom = Matrix.map 1 (kappa L).toRingHom
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), map_conjT, hU]
      exact hf
    refine ⟨⟨u, hmem⟩, Subtype.ext (ga_ext ?_ ?_)⟩
    · exact (pInf_finGL _).trans (MonoidHom.mem_ker.1 hgf).symm
    · exact (pFin_finGL _).trans (Units.ext hU)

instance : Nonempty (FinIso L n) := ⟨finIso L n⟩

variable {L n}

theorem kappa_eq (F G : FinIso L n) : F.κ = G.κ := by
  refine RingEquiv.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y z hy hz => rw [map_add, map_add, hy, hz]
  | tmul x a =>
    have e : x ⊗ₜ[F₀] a = (x ⊗ₜ[F₀] (1 : AFplus L)) * ((1 : L) ⊗ₜ[F₀] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, F.left, G.left]
    congr 1
    refine FiniteAdeleRing.ext _ fun w => ?_
    obtain ⟨i, hi, h1⟩ := F.right w (w.under (𝓞 F₀)) rfl
    obtain ⟨i', hi', h2⟩ := G.right w (w.under (𝓞 F₀)) rfl
    have key : ∀ k : F₀, (1 : L) ⊗ₜ[F₀] (algebraMap F₀ (AFplus L) k) = (k : L) ⊗ₜ[F₀] (1 : AFplus L) := fun k => by
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      rfl
    have : (i : _ → _) = i' := (HeightOneSpectrum.denseRange_algebraMap F₀ (w.under (𝓞 F₀))).equalizer hi hi'
      (funext fun k => by
        have a1 := h1 (algebraMap F₀ _ k)
        have a2 := h2 (algebraMap F₀ _ k)
        rw [key, F.left] at a1
        rw [key, G.left] at a2
        exact a1.symm.trans a2)
    change F.κ (1 ⊗ₜ a) w = G.κ (1 ⊗ₜ a) w
    rw [h1, h2, this]

theorem j_eq (F G : FinIso L n) : F.j = G.j := by
  refine MonoidHom.ext fun x => Subtype.ext (ga_ext ?_ ?_)
  · exact (MonoidHom.mem_ker.1 (F.fin x)).trans (MonoidHom.mem_ker.1 (G.fin x)).symm
  · refine Units.ext (Matrix.ext fun s t => FiniteAdeleRing.ext _ fun w => ?_)
    have a := F.loc x w s t
    rw [kappa_eq F G] at a
    exact a.trans (G.loc x w s t).symm

theorem j_injective (F : FinIso L n) : Function.Injective F.j := fun x y h => by
  refine Subtype.ext (Units.ext (Matrix.ext fun s t => F.κ.injective (FiniteAdeleRing.ext _ fun w => ?_)))
  have a := F.loc x w s t
  rw [h] at a
  exact a.symm.trans (F.loc y w s t)

variable (L n) in

def trivRep : NG.AutRep L n where
  W := ℂ
  ρ := Representation.trivial ℂ (GQ L n) ℂ
  alg := ⟨inferInstance, Unit, inferInstance, inferInstance, Module.Basis.singleton Unit ℂ, fun _ _ => 1, fun γ γ₀ _ => by
    ext i j
    simp [LinearMap.toMatrix_apply]⟩
  irr := by
    have hb : (⊥ : Subrepresentation (Representation.trivial ℂ (GQ L n) ℂ)) ≠ ⊤ := fun h => by
      have := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top (α := Submodule ℂ ℂ) this
    haveI : Nontrivial (Subrepresentation (Representation.trivial ℂ (GQ L n) ℂ)) := ⟨_, _, hb⟩
    refine ⟨fun a => ?_⟩
    rcases eq_bot_or_eq_top a.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  S := Submodule.span ℂ {(fun _ => 1 : GAf L n → ℂ)}
  irrS := by
    have h0 : (fun _ => 1 : GAf L n → ℂ) ≠ 0 := fun h => one_ne_zero (congrFun h 1)
    refine ⟨⟨fun φ hφ => ?_, fun h φ hφ => ?_⟩, by simpa using h0,
      fun W _ hW => (nonzero_span_atom _ h0).le_iff.1 hW⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
      exact ⟨fun _ _ => rfl, 1, one_pos, fun _ _ _ => rfl⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
      exact hφ

theorem dict_triv (F : FinIso L n) : Dict F (trivRep L n) (Submodule.span ℂ {(fun _ => 1 : UA L n → ℂ)}) := by
  refine ⟨isAutRepU_const, ?_⟩
  rw [Submodule.map_span, Set.image_singleton]
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
  · rintro _ rfl
    exact ⟨fun _ => (1 : ℂ), Submodule.mem_span_singleton_self (R := ℂ) (fun _ => 1 : GAf L n → ℂ), (LinearMap.id : ℂ →ₗ[ℂ] ℂ), rfl⟩
  · rintro _ ⟨f, hf, lam, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_singleton (R := ℂ) (M := GAf L n → ℂ)).1 hf
    exact Submodule.mem_span_singleton.2 ⟨lam (c • (1 : ℂ)), funext fun x => mul_one _⟩

theorem not_dict_bot (F : FinIso L n) (π : NG.AutRep L n) : ¬ Dict F π ⊥ := fun h => h.1.ne_bot rfl

theorem restrict_translate (F : FinIso L n) (φ : UA L n → ℂ) (h : GAf L n) :
    LinearMap.funLeft ℂ ℂ F.j (RU L n (F.j h) φ) = NG.rt L n h (LinearMap.funLeft ℂ ℂ F.j φ) := by
  funext g
  change φ (F.j g * F.j h) = φ (F.j (g * h))
  rw [map_mul]

end GlobalTheory.FormDict.Model

end
